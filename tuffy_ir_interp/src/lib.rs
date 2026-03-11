//! tuffy_ir_interp: Miri-like IR interpreter with UB detection.
//!
//! Provides an interpreter for `tuffy_ir` programs that executes IR directly
//! with full poison propagation and undefined behavior detection.
//!
//! # Key features
//! - Infinite-precision integer arithmetic (via `num_bigint::BigInt`)
//! - Four-state abstract byte memory model (Bits, PtrFragment, Uninit, Poison)
//! - Pointer provenance tracking with allocation IDs
//! - Poison propagation through computations
//! - UB detection at observation points (branches, returns, memory access)
//! - Hierarchical CFG walking (Function/Loop/Plain regions)
//! - Function calls via call stack with depth limiting

pub mod exec;
pub mod interp;
pub mod memory;
pub mod value;

pub use interp::{ExecMode, InterpResult, Interpreter};
pub use value::{AbstractByte, AllocId, Pointer, Value};
