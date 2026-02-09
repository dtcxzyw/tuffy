//! tuffy_codegen: Re-exports from target-specific backends.
//!
//! The actual implementations live in their respective target crates
//! (e.g. `tuffy_target_x86`). This crate provides a unified interface.

pub mod emit;
pub mod encode;
pub mod isel;
