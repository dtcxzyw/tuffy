//! Arena-based memory model with four-state AbstractByte tracking.
//!
//! Each allocation has:
//! - A unique `AllocId`
//! - A byte array of `AbstractByte` values
//! - Liveness tracking (freed allocations cannot be accessed)
//! - Size tracking for bounds checking

use std::collections::HashMap;

use crate::value::{AbstractByte, AllocId, Pointer};

/// Metadata for a single allocation.
#[derive(Debug)]
struct Allocation {
    /// The actual bytes.
    bytes: Vec<AbstractByte>,
    /// Whether this allocation is still live.
    live: bool,
    /// Human-readable name for debugging.
    #[allow(
        dead_code,
        reason = "Allocation names are kept for diagnostics even when a given build does not print them."
    )]
    name: String,
}

/// UB categories detected by the memory model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoryError {
    /// Access to a freed allocation.
    UseAfterFree(AllocId),
    /// Access outside allocation bounds.
    OutOfBounds {
        /// Allocation being accessed.
        alloc_id: AllocId,
        /// Byte offset of the attempted access.
        offset: i64,
        /// Access size in bytes.
        size: usize,
        /// Allocation size in bytes.
        alloc_size: usize,
    },
    /// Invalid (null/dangling) pointer.
    InvalidPointer,
    /// Double free.
    DoubleFree(AllocId),
    /// Unknown allocation ID.
    UnknownAllocation(AllocId),
}

impl std::fmt::Display for MemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryError::UseAfterFree(id) => {
                write!(f, "use-after-free: alloc{}", id.0)
            }
            MemoryError::OutOfBounds {
                alloc_id,
                offset,
                size,
                alloc_size,
            } => {
                write!(
                    f,
                    "out-of-bounds: alloc{} offset={offset} size={size} alloc_size={alloc_size}",
                    alloc_id.0
                )
            }
            MemoryError::InvalidPointer => write!(f, "invalid pointer dereference"),
            MemoryError::DoubleFree(id) => write!(f, "double-free: alloc{}", id.0),
            MemoryError::UnknownAllocation(id) => {
                write!(f, "unknown allocation: alloc{}", id.0)
            }
        }
    }
}

/// The memory subsystem.
#[derive(Debug)]
pub struct Memory {
    /// Live and freed allocations keyed by allocation id.
    allocations: HashMap<AllocId, Allocation>,
    /// Next allocation id to hand out.
    next_alloc_id: u64,
}

impl Memory {
    /// Create an empty memory state.
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            // Start at 1; 0 is reserved as "null" sentinel.
            next_alloc_id: 1,
        }
    }

    /// Allocate `size` bytes of uninitialized memory.
    pub fn allocate(&mut self, size: usize, name: impl Into<String>) -> AllocId {
        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;
        self.allocations.insert(
            id,
            Allocation {
                bytes: vec![AbstractByte::Uninit; size],
                live: true,
                name: name.into(),
            },
        );
        id
    }

    /// Allocate with initial data (for static data).
    pub fn allocate_with_data(&mut self, data: &[u8], name: impl Into<String>) -> AllocId {
        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;
        self.allocations.insert(
            id,
            Allocation {
                bytes: data.iter().map(|&b| AbstractByte::Bits(b)).collect(),
                live: true,
                name: name.into(),
            },
        );
        id
    }

    /// Free an allocation.
    ///
    /// # Errors
    ///
    /// Returns an error if the allocation is unknown or already freed.
    pub fn deallocate(&mut self, id: AllocId) -> Result<(), MemoryError> {
        let alloc = self
            .allocations
            .get_mut(&id)
            .ok_or(MemoryError::UnknownAllocation(id))?;
        if !alloc.live {
            return Err(MemoryError::DoubleFree(id));
        }
        alloc.live = false;
        Ok(())
    }

    /// Get the size of an allocation.
    ///
    /// # Errors
    ///
    /// Returns an error if the allocation is unknown or has been freed.
    pub fn alloc_size(&self, id: AllocId) -> Result<usize, MemoryError> {
        let alloc = self
            .allocations
            .get(&id)
            .ok_or(MemoryError::UnknownAllocation(id))?;
        if !alloc.live {
            return Err(MemoryError::UseAfterFree(id));
        }
        Ok(alloc.bytes.len())
    }

    /// Validate that an access at `ptr` of `size` bytes is in-bounds.
    fn validate_access(&self, ptr: &Pointer, size: usize) -> Result<(), MemoryError> {
        let alloc = self
            .allocations
            .get(&ptr.alloc_id)
            .ok_or(MemoryError::UnknownAllocation(ptr.alloc_id))?;
        if !alloc.live {
            return Err(MemoryError::UseAfterFree(ptr.alloc_id));
        }
        let offset = ptr.offset;
        if offset < 0 || (offset as usize) + size > alloc.bytes.len() {
            return Err(MemoryError::OutOfBounds {
                alloc_id: ptr.alloc_id,
                offset,
                size,
                alloc_size: alloc.bytes.len(),
            });
        }
        Ok(())
    }

    /// Read `size` bytes from memory at `ptr`.
    ///
    /// # Errors
    ///
    /// Returns an error if the access is invalid or out of bounds.
    pub fn read(&self, ptr: &Pointer, size: usize) -> Result<Vec<AbstractByte>, MemoryError> {
        // Zero-size reads are always valid (even to freed memory).
        if size == 0 {
            return Ok(vec![]);
        }
        self.validate_access(ptr, size)?;
        let alloc = &self.allocations[&ptr.alloc_id];
        let start = ptr.offset as usize;
        Ok(alloc.bytes[start..start + size].to_vec())
    }

    /// Write bytes to memory at `ptr`.
    ///
    /// # Errors
    ///
    /// Returns an error if the access is invalid or out of bounds.
    ///
    /// # Panics
    ///
    /// Panics if the allocation disappears after `validate_access` succeeds.
    pub fn write(&mut self, ptr: &Pointer, bytes: &[AbstractByte]) -> Result<(), MemoryError> {
        if bytes.is_empty() {
            return Ok(());
        }
        self.validate_access(ptr, bytes.len())?;
        let alloc = self.allocations.get_mut(&ptr.alloc_id).unwrap();
        let start = ptr.offset as usize;
        alloc.bytes[start..start + bytes.len()].clone_from_slice(bytes);
        Ok(())
    }

    /// Memory copy (non-overlapping).
    ///
    /// # Errors
    ///
    /// Returns an error if either access is invalid or out of bounds.
    pub fn memcpy(
        &mut self,
        dst: &Pointer,
        src: &Pointer,
        count: usize,
    ) -> Result<(), MemoryError> {
        if count == 0 {
            return Ok(());
        }
        let data = self.read(src, count)?;
        self.write(dst, &data)
    }

    /// Memory move (may overlap).
    ///
    /// # Errors
    ///
    /// Returns an error if either access is invalid or out of bounds.
    pub fn memmove(
        &mut self,
        dst: &Pointer,
        src: &Pointer,
        count: usize,
    ) -> Result<(), MemoryError> {
        // Same as memcpy since we read first then write.
        self.memcpy(dst, src, count)
    }

    /// Memory set.
    ///
    /// # Errors
    ///
    /// Returns an error if the access is invalid or out of bounds.
    ///
    /// # Panics
    ///
    /// Panics if the allocation disappears after `validate_access` succeeds.
    pub fn memset(&mut self, dst: &Pointer, val: u8, count: usize) -> Result<(), MemoryError> {
        if count == 0 {
            return Ok(());
        }
        self.validate_access(dst, count)?;
        let alloc = self.allocations.get_mut(&dst.alloc_id).unwrap();
        let start = dst.offset as usize;
        for i in 0..count {
            alloc.bytes[start + i] = AbstractByte::Bits(val);
        }
        Ok(())
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}
