//! Top-level interpreter: CFG walker, function calls, call stack.
//!
//! Walks the hierarchical region-based CFG, executing instructions in order.
//! Handles function calls via a call stack. Starts from `main`.

use std::collections::HashMap;

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
const MAX_STEPS: u64 = 10_000_000;

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
    /// SSA value environment: maps ValueRef (raw encoding) to runtime Value.
    env: HashMap<u32, Value>,
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
        self.env.insert(vref.raw(), val);
    }

    fn get_value(&self, vref: ValueRef) -> Value {
        self.env
            .get(&vref.raw())
            .cloned()
            .unwrap_or_else(|| panic!("undefined value reference: {:?} (raw={})", vref, vref.raw()))
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
    /// Step counter.
    steps: u64,
    /// Warnings accumulated in Normal mode.
    pub warnings: Vec<UbViolation>,
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
            steps: 0,
            warnings: Vec::new(),
        };

        // Initialize static data.
        for sd in &module.static_data {
            let id = interp
                .memory
                .allocate_with_data(&sd.data, module.symbols.resolve(sd.name));
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
            let id = interp
                .memory
                .allocate(0, format!("fn:{}", module.symbols.resolve(func.name)));
            interp.symbol_addrs.insert(
                func.name.0,
                Value::Ptr(Pointer {
                    alloc_id: id,
                    offset: 0,
                }),
            );
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
        let mut frame = CallFrame::new(func);

        // Bind parameters as initial values.
        // We'll set them when we encounter Param instructions.

        // Set up the parameter values for Param instructions to reference.
        // Store args so Param(idx) can retrieve them.
        let param_values: Vec<Value> = args;

        // Execute the function body starting from the root region.
        let root = func.root_region;
        let result = self.execute_region(&mut frame, root, &param_values, depth)?;

        // Deallocate stack slots.
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

        // Set up initial block args for the first block if param_values provided.
        if !param_values.is_empty()
            && let Some(CfgNode::Block(first_block)) = children.first()
        {
            let bb = frame.func.block(*first_block);
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
            if self.steps > MAX_STEPS {
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
                frame.set_value(vref, val);
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
                        match &a.annotation {
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
                frame.set_value(vref, Value::Mem); // Primary result is Mem token
                if let Some(_sec_ty) = &inst.secondary_ty {
                    let sec_vref = ValueRef::inst_secondary_result(inst_idx);
                    frame.set_value(sec_vref, call_result.unwrap_or(Value::Unit));
                } else {
                    // Single-result call: the result is the return value, type permitting
                    if !matches!(inst.ty, Type::Mem) {
                        frame.set_value(vref, call_result.unwrap_or(Value::Unit));
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
            let resolve_value = |v: ValueRef| -> Value {
                env_snapshot
                    .get(&v.raw())
                    .cloned()
                    .unwrap_or_else(|| panic!("undefined value: {:?}", v))
            };
            let resolve_operand_value = |op: &Operand| -> Value {
                let base = env_snapshot
                    .get(&op.value.raw())
                    .cloned()
                    .unwrap_or_else(|| panic!("undefined value: {:?}", op.value));
                match &op.annotation {
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
            );

            match result {
                Ok(ExecResult::Value(val)) => {
                    frame.set_value(vref, val);
                }
                Ok(ExecResult::MultiValue(v1, v2)) => {
                    frame.set_value(vref, v1);
                    let sec_vref = ValueRef::inst_secondary_result(inst_idx);
                    frame.set_value(sec_vref, v2);
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
                    return self.call_function(i, args, depth + 1);
                }
            }
        }
        Err(UbViolation {
            kind: UbKind::InvalidOperand,
            message: "call to invalid function pointer".into(),
        })
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
