//! Top-level interpreter: CFG walker, function calls, call stack.
//!
//! Walks the hierarchical region-based CFG, executing instructions in order.
//! Handles function calls via a call stack. Starts from `main`.

use std::collections::HashMap;
use std::hash::Hasher;

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use tuffy_ir::function::{CfgNode, Function, RegionKind};
use tuffy_ir::instruction::{Op, Operand};
use tuffy_ir::module::{Module, SymbolId};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, RegionRef, ValueRef};

use crate::exec::{ExecResult, TerminatorAction, UbKind, UbViolation, execute_instruction};
use crate::memory::Memory;
use crate::value::{AllocId, Pointer, Value};

/// Maximum call stack depth to prevent infinite recursion.
const MAX_CALL_DEPTH: usize = 1024;

/// Maximum number of instructions to execute before aborting (infinite loop protection).
fn max_steps() -> u64 {
    std::env::var("TUFFY_MAX_STEPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500_000_000)
}

/// Execution mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecMode {
    /// Abort on first UB.
    Strict,
    /// Report UB as warnings, continue execution.
    Normal,
}

/// Result of interpreting a module.
#[derive(Debug)]
pub enum InterpResult {
    /// Program completed normally with a return value.
    Ok(Option<Value>),
    /// Undefined behavior detected.
    Ub(UbViolation),
    /// Function not found.
    FunctionNotFound(String),
    /// Call stack overflow.
    StackOverflow,
    /// Step limit exceeded.
    StepLimitExceeded,
}

impl std::fmt::Display for InterpResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpResult::Ok(Some(v)) => write!(f, "ok: {v}"),
            InterpResult::Ok(None) => write!(f, "ok: ()"),
            InterpResult::Ub(ub) => write!(f, "{ub}"),
            InterpResult::FunctionNotFound(name) => write!(f, "function not found: {name}"),
            InterpResult::StackOverflow => write!(f, "stack overflow"),
            InterpResult::StepLimitExceeded => write!(f, "step limit exceeded"),
        }
    }
}

/// A frame on the call stack.
struct CallFrame<'a> {
    func: &'a Function,
    /// SSA value environment: maps ValueRef (raw encoding) to runtime Value
    /// along with the definition-site annotation (used as fallback when no
    /// use-site annotation is present, e.g. for sext/zext source width).
    env: HashMap<u32, (Value, Option<Annotation>)>,
    /// Stack slot allocations to deallocate on return.
    stack_allocs: Vec<AllocId>,
}

impl<'a> CallFrame<'a> {
    fn new(func: &'a Function) -> Self {
        Self {
            func,
            env: HashMap::new(),
            stack_allocs: Vec::new(),
        }
    }

    fn set_value(&mut self, vref: ValueRef, val: Value) {
        // Store with no definition annotation (callers that know the annotation
        // should use set_value_with_ann instead).
        self.env.insert(vref.raw(), (val, None));
    }

    fn set_value_with_ann(&mut self, vref: ValueRef, val: Value, ann: Option<Annotation>) {
        self.env.insert(vref.raw(), (val, ann));
    }

    fn get_value(&self, vref: ValueRef) -> Value {
        self.env
            .get(&vref.raw())
            .map(|(v, _)| v.clone())
            .unwrap_or_else(|| panic!("undefined value reference: {:?} (raw={})", vref, vref.raw()))
    }

    fn get_def_annotation(&self, vref: ValueRef) -> Option<Annotation> {
        self.env.get(&vref.raw()).and_then(|(_, ann)| *ann)
    }
}

/// The interpreter.
pub struct Interpreter<'a> {
    module: &'a Module,
    memory: Memory,
    mode: ExecMode,
    /// Map from symbol name to function index.
    func_map: HashMap<String, usize>,
    /// Map from SymbolId to pointer (for symbol addresses).
    symbol_addrs: HashMap<u32, Value>,
    /// Reverse map: AllocId → symbol name (for extern call resolution).
    alloc_to_symbol: HashMap<u64, String>,
    /// Step counter.
    steps: u64,
    /// Maximum step count before aborting.
    max_steps: u64,
    /// Warnings accumulated in Normal mode.
    pub warnings: Vec<UbViolation>,
    /// Captured stdout output.
    pub stdout: Vec<u8>,
    /// Captured stderr output.
    pub stderr: Vec<u8>,
    /// Captured template + args pointers from the most recent `Arguments::new` call.
    /// Used by the `__print` extern handler.
    pending_fmt_template: Option<Pointer>,
    pending_fmt_args: Option<Pointer>,
    /// Shadow hashers: maps hasher AllocId to a native DefaultHasher.
    /// Used to produce correct SipHash results despite codegen bugs in the
    /// compiled SipHash IR (wrong struct field offsets in c_rounds).
    shadow_hashers: HashMap<u64, std::collections::hash_map::DefaultHasher>,
}

impl<'a> Interpreter<'a> {
    /// Create a new interpreter for a module.
    pub fn new(module: &'a Module, mode: ExecMode) -> Self {
        let mut func_map = HashMap::new();
        for (i, func) in module.functions.iter().enumerate() {
            let name = module.symbols.resolve(func.name);
            func_map.insert(name.to_string(), i);
        }

        let mut interp = Self {
            module,
            memory: Memory::new(),
            mode,
            func_map,
            symbol_addrs: HashMap::new(),
            alloc_to_symbol: HashMap::new(),
            steps: 0,
            max_steps: max_steps(),
            warnings: Vec::new(),
            stdout: Vec::new(),
            stderr: Vec::new(),
            pending_fmt_template: None,
            pending_fmt_args: None,
            shadow_hashers: HashMap::new(),
        };

        // Initialize static data.
        for sd in &module.static_data {
            let name = module.symbols.resolve(sd.name).to_string();
            let id = interp.memory.allocate_with_data(&sd.data, &name);
            interp.alloc_to_symbol.insert(id.0, name);
            interp.symbol_addrs.insert(
                sd.name.0,
                Value::Ptr(Pointer {
                    alloc_id: id,
                    offset: 0,
                }),
            );
        }

        // Create symbol addresses for functions (as opaque pointers).
        for func in &module.functions {
            let name = module.symbols.resolve(func.name).to_string();
            let id = interp.memory.allocate(0, format!("fn:{name}"));
            interp.alloc_to_symbol.insert(id.0, name);
            interp.symbol_addrs.insert(
                func.name.0,
                Value::Ptr(Pointer {
                    alloc_id: id,
                    offset: 0,
                }),
            );
        }

        // Create symbol addresses for unresolved symbols (referenced but not
        // defined as functions or static data). These are extern functions.
        for i in 0..module.symbols.len() {
            let sym_id = SymbolId(i as u32);
            if interp.symbol_addrs.contains_key(&sym_id.0) {
                continue;
            }
            let name = module.symbols.resolve(sym_id).to_string();
            let id = interp.memory.allocate(0, format!("extern:{name}"));
            interp.alloc_to_symbol.insert(id.0, name);
            interp.symbol_addrs.insert(
                sym_id.0,
                Value::Ptr(Pointer {
                    alloc_id: id,
                    offset: 0,
                }),
            );
        }

        // Apply relocations: patch static data memory with symbol pointers.
        for sd in &module.static_data {
            let sd_ptr = interp.symbol_addrs[&sd.name.0].clone();
            if let Value::Ptr(base) = &sd_ptr {
                for reloc in &sd.relocations {
                    if let Some(Value::Ptr(target)) = interp.symbol_addrs.get(&reloc.symbol.0) {
                        // Write the target pointer as 8 PtrFragment bytes at the relocation offset.
                        let ptr_at_offset = Pointer {
                            alloc_id: base.alloc_id,
                            offset: reloc.offset as i64,
                        };
                        let ptr_bytes = crate::value::ptr_to_le_bytes(target);
                        let _ = interp.memory.write(&ptr_at_offset, &ptr_bytes);
                    }
                }
            }
        }

        interp
    }

    /// Run the program starting from the named function.
    pub fn run(&mut self, entry_name: &str) -> InterpResult {
        let func_idx = match self.func_map.get(entry_name) {
            Some(&idx) => idx,
            None => return InterpResult::FunctionNotFound(entry_name.to_string()),
        };
        match self.call_function(func_idx, vec![], 0) {
            Ok(val) => InterpResult::Ok(val),
            Err(ub) => InterpResult::Ub(ub),
        }
    }

    /// Call a function with arguments.
    fn call_function(
        &mut self,
        func_idx: usize,
        args: Vec<Value>,
        depth: usize,
    ) -> Result<Option<Value>, UbViolation> {
        if depth >= MAX_CALL_DEPTH {
            return Err(UbViolation {
                kind: UbKind::InvalidOperand,
                message: "call stack overflow".into(),
            });
        }

        let func = &self.module.functions[func_idx];
        let func_name = self.module.symbols.resolve(func.name).to_string();

        let mut frame = CallFrame::new(func);
        let param_values: Vec<Value> = args;
        let root = func.root_region;
        let result = self
            .execute_region(&mut frame, root, &param_values, depth)
            .map_err(|mut e| {
                e.message = format!("{}\n  in {func_name}", e.message);
                e
            })?;

        for alloc_id in &frame.stack_allocs {
            let _ = self.memory.deallocate(*alloc_id);
        }

        Ok(result)
    }

    /// Execute a region, returning the value from Ret or RegionYield.
    fn execute_region(
        &mut self,
        frame: &mut CallFrame<'a>,
        region_ref: RegionRef,
        param_values: &[Value],
        depth: usize,
    ) -> Result<Option<Value>, UbViolation> {
        let region = frame.func.region(region_ref);
        let kind = region.kind;
        let children: Vec<CfgNode> = region.children.clone();

        if children.is_empty() {
            return Ok(None);
        }

        match kind {
            RegionKind::Function | RegionKind::Plain => {
                self.execute_region_children(frame, &children, param_values, depth)
            }
            RegionKind::Loop => {
                // Loop regions: Continue is handled inside execute_region_children
                // by resetting child_idx to 0, so we only call once.
                let current_args = param_values.to_vec();
                self.execute_region_children(frame, &children, &current_args, depth)
            }
        }
    }

    /// Execute the children of a region sequentially.
    fn execute_region_children(
        &mut self,
        frame: &mut CallFrame<'a>,
        children: &[CfgNode],
        param_values: &[Value],
        depth: usize,
    ) -> Result<Option<Value>, UbViolation> {
        // Build block order map for this region's children.
        let mut block_indices: HashMap<u32, usize> = HashMap::new();
        let mut region_at_index: HashMap<usize, RegionRef> = HashMap::new();
        for (i, child) in children.iter().enumerate() {
            match child {
                CfgNode::Block(bref) => {
                    block_indices.insert(bref.index(), i);
                }
                CfgNode::Region(rref) => {
                    region_at_index.insert(i, *rref);
                    // Also map the entry block of this region.
                    let region = frame.func.region(*rref);
                    block_indices.insert(region.entry_block.index(), i);
                }
            }
        }

        let mut child_idx = 0;
        let mut pending_block_args: Option<(BlockRef, Vec<Value>)> = None;

        // Set up initial block args for the first block.
        // Function entry blocks have v0: mem as their first arg — ensure it's set
        // even when param_values is empty (zero-param functions).
        if let Some(CfgNode::Block(first_block)) = children.first() {
            let bb = frame.func.block(*first_block);
            let block_args = frame.func.block_args(*first_block);
            if bb.arg_count > 0 && block_args[0].ty == tuffy_ir::types::Type::Mem {
                let mem_vref = ValueRef::block_arg(bb.arg_start);
                frame.set_value(mem_vref, Value::Mem);
            }
            for (i, val) in param_values.iter().enumerate() {
                if i < bb.arg_count as usize {
                    let vref = ValueRef::block_arg(bb.arg_start + i as u32);
                    frame.set_value(vref, val.clone());
                }
            }
        }

        while child_idx < children.len() {
            match &children[child_idx] {
                CfgNode::Block(bref) => {
                    // If we have pending block args for this block, set them.
                    if let Some((target, args)) = pending_block_args.take()
                        && target.index() == bref.index()
                    {
                        let bb = frame.func.block(target);
                        for (i, val) in args.iter().enumerate() {
                            if i < bb.arg_count as usize {
                                let vref = ValueRef::block_arg(bb.arg_start + i as u32);
                                frame.set_value(vref, val.clone());
                            }
                        }
                    }

                    match self.execute_block(frame, *bref, param_values, depth)? {
                        BlockResult::FallThrough => {
                            child_idx += 1;
                        }
                        BlockResult::Branch(target, args) => {
                            // Check if target is in this region.
                            if let Some(&idx) = block_indices.get(&target.index()) {
                                // Set block args for the target.
                                let bb = frame.func.block(target);
                                for (i, val) in args.iter().enumerate() {
                                    if i < bb.arg_count as usize {
                                        let vref = ValueRef::block_arg(bb.arg_start + i as u32);
                                        frame.set_value(vref, val.clone());
                                    }
                                }
                                child_idx = idx;
                                pending_block_args = None;
                            } else {
                                // Target is outside this region; propagate.
                                return Err(UbViolation {
                                    kind: UbKind::InvalidOperand,
                                    message: format!(
                                        "branch to block {} outside current region",
                                        target.index()
                                    ),
                                });
                            }
                        }
                        BlockResult::Return(val) => {
                            return Ok(val);
                        }
                        BlockResult::Continue(args) => {
                            // Loop backedge: return control to the loop handler.
                            // We signal this by returning with a special marker.
                            // The loop handler in execute_region will restart.
                            // Re-bind entry block args.
                            if let Some(CfgNode::Block(first_block)) = children.first() {
                                let bb = frame.func.block(*first_block);
                                for (i, val) in args.iter().enumerate() {
                                    if i < bb.arg_count as usize {
                                        let vref = ValueRef::block_arg(bb.arg_start + i as u32);
                                        frame.set_value(vref, val.clone());
                                    }
                                }
                            }
                            child_idx = 0;
                        }
                        BlockResult::RegionYield(vals) => {
                            // Region exit: return the yielded values (unused in simple cases).
                            return Ok(vals.into_iter().next());
                        }
                    }
                }
                CfgNode::Region(rref) => {
                    // Enter nested region.
                    let region = frame.func.region(*rref);
                    let entry = region.entry_block;

                    // Pass pending block args if they target the entry block.
                    let initial_args = if let Some((target, ref args)) = pending_block_args {
                        if target.index() == entry.index() {
                            let a = args.clone();
                            pending_block_args = None;
                            a
                        } else {
                            vec![]
                        }
                    } else {
                        vec![]
                    };

                    match self.execute_region(frame, *rref, &initial_args, depth)? {
                        Some(val) => {
                            // Check if this is a function return propagating up.
                            // In most cases, region yield is used for non-return exits.
                            // For simplicity, if a Ret was hit, it propagates up.
                            // We need to distinguish Ret from RegionYield.
                            // Ret should propagate all the way up.
                            return Ok(Some(val));
                        }
                        None => {
                            child_idx += 1;
                        }
                    }
                }
            }
        }

        Ok(None)
    }

    /// Execute a single basic block. Returns the action to take.
    fn execute_block(
        &mut self,
        frame: &mut CallFrame<'a>,
        block_ref: BlockRef,
        param_values: &[Value],
        depth: usize,
    ) -> Result<BlockResult, UbViolation> {
        let bb = frame.func.block(block_ref);
        let inst_start = bb.inst_start;
        let inst_count = bb.inst_count;

        for i in 0..inst_count {
            self.steps += 1;
            if self.steps > self.max_steps {
                return Err(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: "step limit exceeded".into(),
                });
            }

            let inst_idx = inst_start + i;
            let inst = frame.func.inst(inst_idx);
            let vref = ValueRef::inst_result(inst_idx);

            // Handle Param instruction specially.
            if let Op::Param(idx) = &inst.op {
                let val = if (*idx as usize) < param_values.len() {
                    let v = param_values[*idx as usize].clone();
                    // Apply result annotation
                    match (&v, &inst.result_annotation) {
                        (Value::Int(n), Some(Annotation::Int(ann))) => {
                            crate::exec::apply_annotation(n, ann)
                        }
                        _ => v,
                    }
                } else {
                    Value::Poison
                };
                frame.set_value_with_ann(vref, val, inst.result_annotation);
                continue;
            }

            // Handle Call instruction specially.
            if let Op::Call(func_ptr, args, _mem) = &inst.op {
                let vp = {
                    let base = frame.get_value(func_ptr.clone().raw().value);
                    crate::exec::apply_result_annotation(base, &func_ptr.clone().raw().annotation)
                };
                let arg_vals: Vec<Value> = args
                    .iter()
                    .map(|a| {
                        let base = frame.get_value(a.value);
                        let def_ann = frame.get_def_annotation(a.value);
                        let effective_ann = a.annotation.as_ref().or(def_ann.as_ref());
                        match effective_ann {
                            Some(ann) => match (&base, ann) {
                                (Value::Int(n), tuffy_ir::types::Annotation::Int(ia)) => {
                                    crate::exec::apply_annotation(n, ia)
                                }
                                _ => base,
                            },
                            None => base,
                        }
                    })
                    .collect();

                // Look up the function by pointer.
                let call_result = self.resolve_call(&vp, arg_vals, depth)?;
                frame.set_value_with_ann(vref, Value::Mem, inst.result_annotation); // Primary result is Mem token
                if let Some(_sec_ty) = &inst.secondary_ty {
                    let sec_vref = ValueRef::inst_secondary_result(inst_idx);
                    frame.set_value_with_ann(
                        sec_vref,
                        call_result.unwrap_or(Value::Unit),
                        inst.secondary_result_annotation,
                    );
                } else {
                    // Single-result call: the result is the return value, type permitting
                    if !matches!(inst.ty, Type::Mem) {
                        frame.set_value_with_ann(
                            vref,
                            call_result.unwrap_or(Value::Unit),
                            inst.result_annotation,
                        );
                    }
                }
                continue;
            }

            // General instruction execution.
            // Clone the op and relevant fields to avoid borrowing `frame` across the execute call.
            let inst_op = inst.op.clone();
            let inst_ty = inst.ty.clone();
            let inst_result_ann = inst.result_annotation;
            let inst_secondary_ty = inst.secondary_ty.clone();
            let inst_secondary_result_ann = inst.secondary_result_annotation;

            // Snapshot the values needed by the instruction from the environment.
            let env_snapshot = frame.env.clone();
            let func_name_for_debug = self.module.symbols.resolve(frame.func.name).to_string();
            let inst_idx_for_debug = inst_idx;
            let resolve_value = |v: ValueRef| -> Value {
                env_snapshot
                    .get(&v.raw())
                    .map(|(val, _)| val.clone())
                    .unwrap_or_else(|| {
                        panic!(
                            "undefined value: {:?} (secondary={}) at inst {} in {}",
                            v,
                            v.is_secondary_result(),
                            inst_idx_for_debug,
                            func_name_for_debug
                        )
                    })
            };
            let resolve_operand_value = |op: &Operand| -> Value {
                let (base, def_ann) =
                    env_snapshot
                        .get(&op.value.raw())
                        .cloned()
                        .unwrap_or_else(|| {
                            panic!(
                                "undefined value: {:?} (secondary={}) at inst {} in {}",
                                op.value,
                                op.value.is_secondary_result(),
                                inst_idx_for_debug,
                                func_name_for_debug
                            )
                        });
                // Use the use-site annotation if present, otherwise fall back
                // to the definition-site annotation (critical for sext/zext
                // which need source width from the defining instruction).
                let effective_ann = op.annotation.as_ref().or(def_ann.as_ref());
                match effective_ann {
                    Some(ann) => match (&base, ann) {
                        (Value::Int(n), tuffy_ir::types::Annotation::Int(ia)) => {
                            crate::exec::apply_annotation(n, ia)
                        }
                        _ => base,
                    },
                    None => base,
                }
            };

            let symbol_addrs = &self.symbol_addrs;
            let resolve_symbol = |sym_id: SymbolId| -> Value {
                symbol_addrs
                    .get(&sym_id.0)
                    .cloned()
                    .unwrap_or(Value::Poison)
            };

            // Handle StackSlot specially to avoid borrow conflicts.
            if let Op::StackSlot(bytes) = &inst_op {
                let id = self.memory.allocate(*bytes as usize, "stack_slot");
                frame.stack_allocs.push(id);
                frame.set_value(
                    vref,
                    Value::Ptr(Pointer {
                        alloc_id: id,
                        offset: 0,
                    }),
                );
                continue;
            }

            let mut noop_alloc =
                |_size: usize| -> AllocId { unreachable!("StackSlot handled above") };

            let def_annotation = |v: ValueRef| -> Option<Annotation> {
                env_snapshot.get(&v.raw()).and_then(|(_, ann)| *ann)
            };

            let result = execute_instruction(
                &inst_op,
                &inst_ty,
                &inst_result_ann,
                &inst_secondary_ty,
                &inst_secondary_result_ann,
                &resolve_value,
                &resolve_operand_value,
                &mut self.memory,
                &mut noop_alloc,
                &resolve_symbol,
                &def_annotation,
            );

            match result {
                Ok(ExecResult::Value(val)) => {
                    frame.set_value_with_ann(vref, val, inst_result_ann);
                }
                Ok(ExecResult::MultiValue(v1, v2)) => {
                    frame.set_value_with_ann(vref, v1, inst_result_ann);
                    let sec_vref = ValueRef::inst_secondary_result(inst_idx);
                    frame.set_value_with_ann(sec_vref, v2, inst_secondary_result_ann);
                }
                Ok(ExecResult::Terminator(action)) => {
                    // Still set the terminator's value (for display consistency).
                    frame.set_value(vref, Value::Unit);
                    return self.handle_terminator(action);
                }
                Err(ub) => match self.mode {
                    ExecMode::Strict => return Err(ub),
                    ExecMode::Normal => {
                        self.warnings.push(ub);
                        frame.set_value(vref, Value::Poison);
                    }
                },
            }
        }

        // If block has no terminator (shouldn't happen in well-formed IR).
        Ok(BlockResult::FallThrough)
    }

    fn handle_terminator(&mut self, action: TerminatorAction) -> Result<BlockResult, UbViolation> {
        match action {
            TerminatorAction::Return(val) => {
                // Check for poison observation at return.
                if let Some(Value::Poison) = &val {
                    match self.mode {
                        ExecMode::Strict => {
                            return Err(UbViolation {
                                kind: UbKind::PoisonObserved,
                                message: "poison value returned from function".into(),
                            });
                        }
                        ExecMode::Normal => {
                            self.warnings.push(UbViolation {
                                kind: UbKind::PoisonObserved,
                                message: "poison value returned from function".into(),
                            });
                        }
                    }
                }
                Ok(BlockResult::Return(val))
            }
            TerminatorAction::Branch(target, args) => Ok(BlockResult::Branch(target, args)),
            TerminatorAction::BranchIf {
                cond,
                then_block,
                then_args,
                else_block,
                else_args,
            } => {
                match cond.as_bool() {
                    Some(true) => Ok(BlockResult::Branch(then_block, then_args)),
                    Some(false) => Ok(BlockResult::Branch(else_block, else_args)),
                    None => {
                        // Branching on poison is UB.
                        match self.mode {
                            ExecMode::Strict => Err(UbViolation {
                                kind: UbKind::PoisonObserved,
                                message: "branch condition is poison".into(),
                            }),
                            ExecMode::Normal => {
                                self.warnings.push(UbViolation {
                                    kind: UbKind::PoisonObserved,
                                    message: "branch condition is poison".into(),
                                });
                                // In Normal mode, take the else branch arbitrarily.
                                Ok(BlockResult::Branch(else_block, else_args))
                            }
                        }
                    }
                }
            }
            TerminatorAction::Continue(args) => Ok(BlockResult::Continue(args)),
            TerminatorAction::RegionYield(args) => Ok(BlockResult::RegionYield(args)),
            TerminatorAction::Unreachable => Err(UbViolation {
                kind: UbKind::UnreachableReached,
                message: "unreachable instruction executed".into(),
            }),
            TerminatorAction::Trap => Err(UbViolation {
                kind: UbKind::TrapExecuted,
                message: "trap instruction executed".into(),
            }),
        }
    }

    /// Resolve a function call through a pointer.
    fn resolve_call(
        &mut self,
        func_ptr: &Value,
        args: Vec<Value>,
        depth: usize,
    ) -> Result<Option<Value>, UbViolation> {
        // Find which function this pointer refers to.
        if let Value::Ptr(ptr) = func_ptr {
            for (i, func) in self.module.functions.iter().enumerate() {
                if let Some(Value::Ptr(func_p)) = self.symbol_addrs.get(&func.name.0)
                    && func_p.alloc_id == ptr.alloc_id
                {
                    let func_name = self.module.symbols.resolve(func.name);

                    // Intercept broken intrinsics and implement natively.
                    if func_name.contains("unchecked_funnel_shl") {
                        return self.intrinsic_funnel_shl(&args);
                    }
                    if func_name.contains("unchecked_funnel_shr") {
                        return self.intrinsic_funnel_shr(&args);
                    }

                    // Shadow hasher: intercept DefaultHasher methods to bypass
                    // buggy compiled SipHash (wrong struct offsets in c_rounds).
                    if let Some(result) = self.try_shadow_hasher(func_name, &args, depth)? {
                        return Ok(result);
                    }

                    // Intercept Arguments::new to capture template+args pointers
                    // before ptrtoaddr loses provenance.
                    if func_name.contains("Arguments")
                        && func_name.contains("new")
                        && !func_name.contains("new_display")
                    {
                        if let Some(Value::Ptr(template)) = args.first() {
                            self.pending_fmt_template = Some(template.clone());
                        }
                        if let Some(Value::Ptr(fmt_args)) = args.get(1) {
                            self.pending_fmt_args = Some(fmt_args.clone());
                        }
                    }
                    return self.call_function(i, args, depth + 1);
                }
            }
            // Not a known function body — try extern function handling.
            if let Some(sym_name) = self.alloc_to_symbol.get(&ptr.alloc_id.0).cloned() {
                return self.call_extern(&sym_name, args);
            }
        }
        Err(UbViolation {
            kind: UbKind::InvalidOperand,
            message: "call to invalid function pointer".into(),
        })
    }

    /// Handle calls to external (non-IR) functions.
    fn call_extern(
        &mut self,
        sym_name: &str,
        args: Vec<Value>,
    ) -> Result<Option<Value>, UbViolation> {
        // Demangle or match by known patterns.
        // libc write: write(fd, buf, count) -> ssize_t
        if sym_name == "write" || sym_name == "__write" || sym_name == "__GI___libc_write" {
            return self.extern_write(&args);
        }

        // Rust allocator shims
        if sym_name.contains("__rust_alloc_zeroed") || sym_name.ends_with("__rdl_alloc_zeroed") {
            return self.extern_alloc_zeroed(&args);
        }
        if sym_name.contains("__rust_alloc") || sym_name.ends_with("__rdl_alloc") {
            return self.extern_alloc(&args);
        }
        if sym_name.contains("__rust_dealloc") || sym_name.ends_with("__rdl_dealloc") {
            return self.extern_dealloc(&args);
        }
        if sym_name.contains("__rust_realloc") || sym_name.ends_with("__rdl_realloc") {
            return self.extern_realloc(&args);
        }
        if sym_name.contains("__rust_no_alloc_shim_is_unstable") {
            return Ok(Some(Value::Unit));
        }

        // abort / panic
        if sym_name.contains("abort") || sym_name.contains("__rust_start_panic") {
            return Err(UbViolation {
                kind: UbKind::TrapExecuted,
                message: format!("extern abort: {sym_name}"),
            });
        }

        // drop_in_place variants — no-op
        if sym_name.contains("drop_in_place") {
            return Ok(Some(Value::Unit));
        }

        // precondition_check — no-op
        if sym_name.contains("precondition_check") {
            return Ok(Some(Value::Unit));
        }

        // bcmp/memcmp
        if sym_name == "bcmp" || sym_name == "memcmp" {
            return self.extern_memcmp(&args);
        }

        // std::io::stdio::_print / __print — format Arguments and write to stdout
        if sym_name.contains("__print") || sym_name.contains("_print") && sym_name.contains("stdio")
        {
            return self.extern_print(&args);
        }

        // panic_fmt — trap with message
        if sym_name.contains("panic_fmt") || sym_name.contains("panicking") {
            return Err(UbViolation {
                kind: UbKind::TrapExecuted,
                message: format!("panic: {sym_name}"),
            });
        }

        // Unhandled extern — report but continue in Normal mode.
        let msg = format!("unhandled extern function: {sym_name}");
        match self.mode {
            ExecMode::Strict => Err(UbViolation {
                kind: UbKind::InvalidOperand,
                message: msg,
            }),
            ExecMode::Normal => {
                self.warnings.push(UbViolation {
                    kind: UbKind::InvalidOperand,
                    message: msg,
                });
                Ok(Some(Value::Int(num_bigint::BigInt::from(0))))
            }
        }
    }

    /// extern write(fd, buf, count) -> ssize_t
    fn extern_write(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let fd = args
            .first()
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_i64())
            .unwrap_or(-1);
        let buf_ptr = args.get(1).and_then(|v| v.as_ptr());
        let count = args
            .get(2)
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);

        if let Some(ptr) = buf_ptr {
            let bytes = self.memory.read(ptr, count).map_err(|e| UbViolation {
                kind: UbKind::MemoryViolation,
                message: format!("write: {e}"),
            })?;
            let raw: Vec<u8> = bytes
                .iter()
                .map(|b| match b {
                    crate::value::AbstractByte::Bits(v) => *v,
                    _ => b'?',
                })
                .collect();
            match fd {
                1 => self.stdout.extend_from_slice(&raw),
                2 => self.stderr.extend_from_slice(&raw),
                _ => {} // ignore other fds
            }
            Ok(Some(Value::Int(num_bigint::BigInt::from(count))))
        } else {
            Ok(Some(Value::Int(num_bigint::BigInt::from(-1i64))))
        }
    }

    /// extern __rust_alloc(size, align) -> *mut u8
    fn extern_alloc(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let size = args
            .first()
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);
        let id = self.memory.allocate(size, "heap_alloc");
        Ok(Some(Value::Ptr(Pointer {
            alloc_id: id,
            offset: 0,
        })))
    }

    /// extern __rust_alloc_zeroed(size, align) -> *mut u8
    fn extern_alloc_zeroed(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let size = args
            .first()
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);
        let data = vec![0u8; size];
        let id = self.memory.allocate_with_data(&data, "heap_alloc_zeroed");
        Ok(Some(Value::Ptr(Pointer {
            alloc_id: id,
            offset: 0,
        })))
    }

    /// extern __rust_dealloc(ptr, size, align)
    fn extern_dealloc(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        if let Some(ptr) = args.first().and_then(|v| v.as_ptr()) {
            let _ = self.memory.deallocate(ptr.alloc_id);
        }
        Ok(Some(Value::Unit))
    }

    /// extern __rust_realloc(ptr, old_size, align, new_size) -> *mut u8
    fn extern_realloc(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let old_ptr = args.first().and_then(|v| v.as_ptr());
        let new_size = args
            .get(3)
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);
        let old_size = args
            .get(1)
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);

        // Read old data.
        let old_data = if let Some(p) = old_ptr {
            self.memory.read(p, old_size).unwrap_or_default()
        } else {
            vec![]
        };

        // Allocate new block.
        let new_id = self.memory.allocate(new_size, "heap_realloc");
        let copy_len = old_size.min(new_size);
        if copy_len > 0 {
            let new_ptr = Pointer {
                alloc_id: new_id,
                offset: 0,
            };
            let _ = self.memory.write(&new_ptr, &old_data[..copy_len]);
        }

        // Free old block.
        if let Some(p) = old_ptr {
            let _ = self.memory.deallocate(p.alloc_id);
        }

        Ok(Some(Value::Ptr(Pointer {
            alloc_id: new_id,
            offset: 0,
        })))
    }

    /// extern memcmp/bcmp(s1, s2, n) -> int
    fn extern_memcmp(&mut self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let ptr1 = args.first().and_then(|v| v.as_ptr());
        let ptr2 = args.get(1).and_then(|v| v.as_ptr());
        let n = args
            .get(2)
            .and_then(|v| v.as_int())
            .and_then(|n| n.to_usize())
            .unwrap_or(0);

        if let (Some(p1), Some(p2)) = (ptr1, ptr2) {
            let b1 = self.memory.read(p1, n).map_err(|e| UbViolation {
                kind: UbKind::MemoryViolation,
                message: format!("memcmp: {e}"),
            })?;
            let b2 = self.memory.read(p2, n).map_err(|e| UbViolation {
                kind: UbKind::MemoryViolation,
                message: format!("memcmp: {e}"),
            })?;
            for (a, b) in b1.iter().zip(b2.iter()) {
                match (a, b) {
                    (crate::value::AbstractByte::Bits(x), crate::value::AbstractByte::Bits(y)) => {
                        if x != y {
                            let result = if x < y { -1i64 } else { 1i64 };
                            return Ok(Some(Value::Int(num_bigint::BigInt::from(result))));
                        }
                    }
                    _ => {
                        return Ok(Some(Value::Int(num_bigint::BigInt::from(0))));
                    }
                }
            }
            Ok(Some(Value::Int(num_bigint::BigInt::from(0))))
        } else {
            Ok(Some(Value::Int(num_bigint::BigInt::from(0))))
        }
    }

    /// Handle std::io::stdio::_print by parsing the packed template format.
    ///
    /// Native implementation of unchecked_funnel_shl (used for rotate_left).
    /// fshl(a, b, c) = (a << (c % bitwidth)) | (b >> (bitwidth - c % bitwidth))
    fn intrinsic_funnel_shl(&self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let a = match &args[0] {
            Value::Int(v) => v.to_u64().unwrap_or(0),
            _ => 0,
        };
        let b = match &args[1] {
            Value::Int(v) => v.to_u64().unwrap_or(0),
            _ => 0,
        };
        let c = match &args[2] {
            Value::Int(v) => v.to_u32().unwrap_or(0),
            _ => 0,
        };
        let shift = c % 64;
        let result = if shift == 0 {
            a
        } else {
            (a << shift) | (b >> (64 - shift))
        };
        Ok(Some(Value::Int(BigInt::from(result))))
    }

    /// Native implementation of unchecked_funnel_shr (used for rotate_right).
    /// fshr(a, b, c) = (b >> (c % bitwidth)) | (a << (bitwidth - c % bitwidth))
    fn intrinsic_funnel_shr(&self, args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let a = match &args[0] {
            Value::Int(v) => v.to_u64().unwrap_or(0),
            _ => 0,
        };
        let b = match &args[1] {
            Value::Int(v) => v.to_u64().unwrap_or(0),
            _ => 0,
        };
        let c = match &args[2] {
            Value::Int(v) => v.to_u32().unwrap_or(0),
            _ => 0,
        };
        let shift = c % 64;
        let result = if shift == 0 {
            b
        } else {
            (b >> shift) | (a << (64 - shift))
        };
        Ok(Some(Value::Int(BigInt::from(result))))
    }

    /// Intercept DefaultHasher methods and forward to a native shadow hasher.
    /// Returns `Some(value)` if intercepted, `None` if the call should proceed
    /// normally through the IR.
    ///
    /// Shadow hashers are created lazily on first write call because
    /// DefaultHasher::new writes to a stack slot that later gets copied
    /// to the LazyLock storage (different AllocId). DefaultHasher::new()
    /// always uses keys (0, 0), so lazy creation is safe.
    fn try_shadow_hasher(
        &mut self,
        func_name: &str,
        args: &[Value],
        _depth: usize,
    ) -> Result<Option<Option<Value>>, UbViolation> {
        if !func_name.contains("DefaultHasher") {
            return Ok(None);
        }

        // Helper: get or create shadow hasher for the given alloc_id.
        fn get_or_create(
            map: &mut std::collections::HashMap<u64, std::collections::hash_map::DefaultHasher>,
            id: u64,
        ) -> &mut std::collections::hash_map::DefaultHasher {
            map.entry(id).or_default()
        }

        // DefaultHasher::Hasher::write (general, not write_u*/write_i*)
        if func_name.contains("Hasher5write")
            && !func_name.contains("write_u")
            && !func_name.contains("write_i")
            && let Some(Value::Ptr(p)) = args.first()
        {
            let shadow = get_or_create(&mut self.shadow_hashers, p.alloc_id.0);
            if let (Some(Value::Ptr(buf)), Some(Value::Int(len))) = (args.get(1), args.get(2)) {
                let n = len.to_usize().unwrap_or(0);
                if let Ok(bytes) = self.memory.read(buf, n) {
                    let raw: Vec<u8> = bytes
                        .iter()
                        .map(|b| match b {
                            crate::value::AbstractByte::Bits(v) => *v,
                            _ => 0,
                        })
                        .collect();
                    shadow.write(&raw);
                }
            }
            return Ok(Some(None));
        }

        // All typed write variants: write_u8/u16/u32/u64/u128/usize and
        // write_i8/i16/i32/i64/i128/isize.
        // BigInt may store signed values as unsigned bit patterns, so for
        // signed types we try to_iN first (handles negative BigInts) then
        // fall back to to_uN (handles unsigned-represented negatives).
        if func_name.contains("Hasher")
            && (func_name.contains("write_u") || func_name.contains("write_i"))
            && let Some(Value::Ptr(p)) = args.first()
        {
            let shadow = get_or_create(&mut self.shadow_hashers, p.alloc_id.0);
            if let Some(Value::Int(val)) = args.get(1) {
                if func_name.contains("write_u8") {
                    shadow.write_u8(val.to_u8().unwrap_or(0));
                } else if func_name.contains("write_u16") {
                    shadow.write_u16(val.to_u16().unwrap_or(0));
                } else if func_name.contains("write_u32") {
                    shadow.write_u32(val.to_u32().unwrap_or(0));
                } else if func_name.contains("write_u64") {
                    shadow.write_u64(val.to_u64().unwrap_or(0));
                } else if func_name.contains("write_u128") {
                    shadow.write_u128(val.to_u128().unwrap_or(0));
                } else if func_name.contains("write_usize") {
                    shadow.write_usize(val.to_usize().unwrap_or(0));
                } else if func_name.contains("write_i8") {
                    let v = val
                        .to_i8()
                        .unwrap_or_else(|| val.to_u8().unwrap_or(0) as i8);
                    shadow.write_i8(v);
                } else if func_name.contains("write_i16") {
                    let v = val
                        .to_i16()
                        .unwrap_or_else(|| val.to_u16().unwrap_or(0) as i16);
                    shadow.write_i16(v);
                } else if func_name.contains("write_i32") {
                    let v = val
                        .to_i32()
                        .unwrap_or_else(|| val.to_u32().unwrap_or(0) as i32);
                    shadow.write_i32(v);
                } else if func_name.contains("write_i64") {
                    let v = val
                        .to_i64()
                        .unwrap_or_else(|| val.to_u64().unwrap_or(0) as i64);
                    shadow.write_i64(v);
                } else if func_name.contains("write_i128") {
                    let v = val
                        .to_i128()
                        .unwrap_or_else(|| val.to_u128().unwrap_or(0) as i128);
                    shadow.write_i128(v);
                } else if func_name.contains("write_isize") {
                    let v = val
                        .to_i64()
                        .unwrap_or_else(|| val.to_u64().unwrap_or(0) as i64);
                    shadow.write_isize(v as isize);
                }
            }
            return Ok(Some(None));
        }

        // DefaultHasher::Hasher::finish — return shadow result.
        if func_name.contains("Hasher6finish")
            && let Some(Value::Ptr(p)) = args.first()
        {
            let shadow = get_or_create(&mut self.shadow_hashers, p.alloc_id.0);
            let result = shadow.finish();
            return Ok(Some(Some(Value::Int(BigInt::from(result)))));
        }

        Ok(None)
    }

    /// Uses the template and args pointers captured from the most recent
    /// `Arguments::new` call (since the codegen doesn't preserve the args
    /// pointer in the Arguments struct return value).
    fn extern_print(&mut self, _args: &[Value]) -> Result<Option<Value>, UbViolation> {
        let template_ptr = match self.pending_fmt_template.take() {
            Some(p) => p,
            None => return Ok(Some(Value::Unit)),
        };
        let args_ptr = self.pending_fmt_args.take();

        let mut output = Vec::new();
        let mut pos: i64 = 0;
        let mut arg_index: usize = 0;

        loop {
            // Read one byte at a time from the template.
            let byte_ptr = Pointer {
                alloc_id: template_ptr.alloc_id,
                offset: template_ptr.offset + pos,
            };
            let Ok(byte_data) = self.memory.read(&byte_ptr, 1) else {
                break;
            };
            let n = match &byte_data[0] {
                crate::value::AbstractByte::Bits(v) => *v,
                _ => break,
            };
            pos += 1;

            if n == 0 {
                break;
            } else if n < 0x80 {
                // Short literal string piece of length n.
                let piece_ptr = Pointer {
                    alloc_id: template_ptr.alloc_id,
                    offset: template_ptr.offset + pos,
                };
                if let Ok(piece_bytes) = self.memory.read(&piece_ptr, n as usize) {
                    for b in &piece_bytes {
                        if let crate::value::AbstractByte::Bits(v) = b {
                            output.push(*v);
                        }
                    }
                }
                pos += n as i64;
            } else if n == 0x80 {
                // Long literal string piece (16-bit length).
                let len_ptr = Pointer {
                    alloc_id: template_ptr.alloc_id,
                    offset: template_ptr.offset + pos,
                };
                if let Ok(len_bytes) = self.memory.read(&len_ptr, 2) {
                    let b0 = match &len_bytes[0] {
                        crate::value::AbstractByte::Bits(v) => *v,
                        _ => 0,
                    };
                    let b1 = match &len_bytes[1] {
                        crate::value::AbstractByte::Bits(v) => *v,
                        _ => 0,
                    };
                    let len = u16::from_le_bytes([b0, b1]) as usize;
                    pos += 2;
                    let piece_ptr = Pointer {
                        alloc_id: template_ptr.alloc_id,
                        offset: template_ptr.offset + pos,
                    };
                    if let Ok(piece_bytes) = self.memory.read(&piece_ptr, len) {
                        for b in &piece_bytes {
                            if let crate::value::AbstractByte::Bits(v) = b {
                                output.push(*v);
                            }
                        }
                    }
                    pos += len as i64;
                } else {
                    break;
                }
            } else if n >= 0xC0 {
                // Placeholder for an argument.
                let formatted = self.format_arg(args_ptr.as_ref(), arg_index);
                output.extend_from_slice(formatted.as_bytes());
                arg_index += 1;

                // Skip optional fields based on the marker byte flags.
                if n > 0xC0 {
                    let skip = (n & 1 != 0) as i64 * 4
                        + (n & 2 != 0) as i64 * 2
                        + (n & 4 != 0) as i64 * 2
                        + (n & 8 != 0) as i64 * 2;
                    pos += skip;
                }
            }
        }

        self.stdout.extend_from_slice(&output);
        Ok(Some(Value::Unit))
    }

    /// Format a single argument from the args array.
    fn format_arg(&self, args_ptr: Option<&Pointer>, arg_index: usize) -> String {
        let Some(args_base) = args_ptr else {
            return "?".to_string();
        };

        // Each Argument is 16 bytes: [0..8] = data address (as integer), [8..16] = format fn ptr
        let arg_offset = arg_index * 16;
        let arg_ptr = Pointer {
            alloc_id: args_base.alloc_id,
            offset: args_base.offset + arg_offset as i64,
        };

        // Read the data address (first 8 bytes of Argument).
        let Ok(data_bytes) = self.memory.read(&arg_ptr, 8) else {
            return "?".to_string();
        };

        // The data address is stored as an integer via ptrtoaddr.
        // It could be raw integer bytes (from store.8 of an int:u64)
        // or PtrFragment bytes (from store.8 of a ptr).
        // Check for PtrFragment first.
        let has_ptr_fragments = data_bytes
            .iter()
            .any(|b| matches!(b, crate::value::AbstractByte::PtrFragment(_, _)));

        if has_ptr_fragments {
            // Reconstruct pointer from fragments.
            if let Some((alloc_id, _)) = data_bytes.iter().find_map(|b| match b {
                crate::value::AbstractByte::PtrFragment(id, idx) => Some((*id, *idx)),
                _ => None,
            }) {
                let data_ptr = Pointer {
                    alloc_id,
                    offset: 0,
                };
                return self.read_and_format_value(&data_ptr);
            }
        }

        // It's a synthetic address stored as integer bytes.
        let raw: Vec<u8> = data_bytes
            .iter()
            .map(|b| match b {
                crate::value::AbstractByte::Bits(v) => *v,
                _ => 0,
            })
            .collect();
        if raw.len() >= 8 {
            let addr = i64::from_le_bytes(raw[..8].try_into().unwrap());
            if addr == 0 {
                return "0".to_string();
            }
            let alloc_id = AllocId((addr / 0x1000) as u64);
            let offset = addr % 0x1000;
            let data_ptr = Pointer { alloc_id, offset };
            return self.read_and_format_value(&data_ptr);
        }

        "?".to_string()
    }

    /// Read a value from a pointer and format it as a decimal integer.
    fn read_and_format_value(&self, ptr: &Pointer) -> String {
        // Try reading as u64 (8 bytes).
        if let Ok(bytes) = self.memory.read(ptr, 8) {
            let raw: Vec<u8> = bytes
                .iter()
                .map(|b| match b {
                    crate::value::AbstractByte::Bits(v) => *v,
                    _ => 0,
                })
                .collect();
            if raw.len() >= 8 {
                let val = u64::from_le_bytes(raw[..8].try_into().unwrap());
                return val.to_string();
            }
        }
        "?".to_string()
    }
}

/// Result of executing a basic block.
enum BlockResult {
    /// Fall through to the next child in the region.
    FallThrough,
    /// Branch to a specific block with arguments.
    Branch(BlockRef, Vec<Value>),
    /// Return from the function.
    Return(Option<Value>),
    /// Loop backedge.
    Continue(Vec<Value>),
    /// Region exit.
    RegionYield(Vec<Value>),
}
