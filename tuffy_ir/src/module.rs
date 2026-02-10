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
    names: Vec<String>,
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
    pub name: SymbolId,
    pub data: Vec<u8>,
}

/// Top-level IR container.
///
/// Owns the symbol table, all functions, and static data.
pub struct Module {
    pub name: String,
    pub symbols: SymbolTable,
    pub functions: Vec<Function>,
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
        self.static_data.push(StaticData { name, data });
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
