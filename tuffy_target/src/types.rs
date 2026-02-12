//! Common types shared between target backends and the codegen layer.

use crate::reloc::Relocation;

/// A compiled function ready for object file emission.
pub struct CompiledFunction {
    pub name: String,
    pub code: Vec<u8>,
    pub relocations: Vec<Relocation>,
}

/// A static data blob to be placed in a read-only section.
pub struct StaticData {
    pub name: String,
    pub data: Vec<u8>,
    /// Relocations within the data (e.g. function pointers in vtables).
    pub relocations: Vec<Relocation>,
}
