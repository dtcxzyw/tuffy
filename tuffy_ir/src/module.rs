//! Module-level IR container with interned symbol table.
//!
//! `Module` is the top-level IR structure that owns all functions, static data,
//! and a shared symbol table. It replaces the ad-hoc `TranslationResult`
//! aggregation in the codegen layer.

use std::collections::HashMap;
use std::fmt;

use crate::function::Function;

/// Interned symbol identifier. Indexes into a module-level symbol table.
///
/// Used for function names, static data labels, and external references.
/// Mirrors `TuffyLean.IR.SymbolId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

/// Interned symbol table mapping names to `SymbolId`s.
///
/// Avoids repeated String allocation and enables O(1) equality comparison.
#[derive(Debug, Clone)]
pub struct SymbolTable {
    /// Interned symbol strings indexed by [`SymbolId`].
    names: Vec<String>,
    /// Reverse map from symbol string to its interned identifier.
    lookup: HashMap<String, SymbolId>,
}

impl SymbolTable {
    /// Create an empty symbol table.
    pub fn new() -> Self {
        Self {
            names: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    /// Intern a symbol name, returning its `SymbolId`.
    ///
    /// If the name already exists, returns the existing id.
    pub fn intern(&mut self, name: &str) -> SymbolId {
        if let Some(&id) = self.lookup.get(name) {
            return id;
        }
        let id = SymbolId(self.names.len() as u32);
        self.names.push(name.to_string());
        self.lookup.insert(name.to_string(), id);
        id
    }

    /// Resolve a `SymbolId` back to its name.
    pub fn resolve(&self, id: SymbolId) -> &str {
        &self.names[id.0 as usize]
    }

    /// Number of interned symbols.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

/// A static data blob (emitted in .rodata or similar section).
#[derive(Debug, Clone)]
pub struct StaticData {
    /// Symbol naming this static-data blob.
    pub name: SymbolId,
    /// Raw bytes emitted for the blob.
    pub data: Vec<u8>,
    /// Relocations: at `offset`, write the address of `symbol`.
    pub relocations: Vec<StaticRelocation>,
}

/// A relocation inside static data: the 8 bytes at `offset` should be
/// patched with the address of `symbol`.
#[derive(Debug, Clone)]
pub struct StaticRelocation {
    /// Byte offset within the static-data blob.
    pub offset: usize,
    /// Symbol whose address should be written at `offset`.
    pub symbol: SymbolId,
}

/// Top-level IR container.
///
/// Owns the symbol table, all functions, and static data.
pub struct Module {
    /// Human-readable module name.
    pub name: String,
    /// Interned symbol table shared by the module.
    pub symbols: SymbolTable,
    /// Functions defined in the module.
    pub functions: Vec<Function>,
    /// Static-data blobs owned by the module.
    pub static_data: Vec<StaticData>,
}

impl Module {
    /// Create a new empty module.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            symbols: SymbolTable::new(),
            functions: Vec::new(),
            static_data: Vec::new(),
        }
    }

    /// Intern a symbol name in this module's symbol table.
    pub fn intern(&mut self, name: &str) -> SymbolId {
        self.symbols.intern(name)
    }

    /// Resolve a symbol id to its name.
    pub fn resolve(&self, id: SymbolId) -> &str {
        self.symbols.resolve(id)
    }

    /// Add a function to the module.
    pub fn add_function(&mut self, func: Function) {
        self.functions.push(func);
    }

    /// Add static data to the module.
    pub fn add_static_data(&mut self, name: SymbolId, data: Vec<u8>) {
        self.static_data.push(StaticData {
            name,
            data,
            relocations: Vec::new(),
        });
    }

    /// Add static data with relocations to the module.
    pub fn add_static_data_with_relocs(
        &mut self,
        name: SymbolId,
        data: Vec<u8>,
        relocations: Vec<StaticRelocation>,
    ) {
        self.static_data.push(StaticData {
            name,
            data,
            relocations,
        });
    }
}

impl fmt::Debug for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Module")
            .field("name", &self.name)
            .field("symbols", &self.symbols)
            .field(
                "functions",
                &format!("[{} functions]", self.functions.len()),
            )
            .field(
                "static_data",
                &format!("[{} entries]", self.static_data.len()),
            )
            .finish()
    }
}
