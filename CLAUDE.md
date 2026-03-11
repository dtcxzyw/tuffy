# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Maintaining CLAUDE.md

When the user provides a common instruction or policy that applies broadly to future work in this repository, update this file to capture it. This ensures future sessions inherit the instruction without the user needing to repeat it.

## Context Management

**CRITICAL:** When the conversation context is compacted (compressed due to length), you MUST restore essential context by re-reading key documents.

### After Context Compaction

Immediately after context compaction occurs, you MUST:

1. **Re-read CLAUDE.md:**
   - Always re-read `/tuffy/CLAUDE.md` to restore project policies and conventions
   - This file contains critical instructions that must never be lost

2. **Re-read Component README files:**
   - When modifying code in any component/module, read that component's `README.md`
   - Example: When working on `rustc_codegen_tuffy`, read `rustc_codegen_tuffy/README.md`
   - Example: When working on Lean code, read `lean/TuffyLean/README.md`

3. **Re-read Previously Referenced Documentation:**
   - Re-read all documents from `docs/` that were referenced earlier in the conversation
   - This includes task documents, RFCs, and any other documentation that informed your work
   - Maintain a mental note of which docs files have been consulted during the session

### Working with Components

Before modifying any component:
- Read the component's `README.md` to understand its architecture and conventions
- Follow the component-specific rules defined in its documentation
- Do not proceed with changes until you have verified the component's requirements

## Problem Solving Policy

**IMPORTANT:** You have sufficient time to thoroughly analyze and debug problems. Do not choose temporary workarounds or give up due to perceived time constraints. When encountering bugs or issues:

- Investigate root causes systematically rather than documenting problems and moving on
- Persist through complex debugging sessions even if they take multiple attempts
- Avoid shortcuts or partial solutions when complete fixes are achievable
- Only escalate or defer issues when genuinely blocked by external factors

## First Principles Thinking

**IMPORTANT:** When approaching any problem, design decision, or implementation task, you MUST apply first principles thinking. Break down complex problems into fundamental truths and rebuild solutions from the ground up.

### Core Process

1. **Deconstruct the Problem:**
   - Identify the core components and fundamental truths that cannot be further simplified
   - Distinguish between what is undeniably true (physical laws, mathematical constraints, fundamental requirements) and what is assumed

2. **Challenge Assumptions:**
   - Question every assumption, including industry conventions, common practices, and perceived constraints
   - For each assumption, ask: "Why must this be true?" and "What if it weren't true?"
   - Ignore existing solutions and conventional wisdom during this phase

3. **Reconstruct from Fundamentals:**
   - Build solutions based ONLY on the fundamental truths identified
   - Do not reference existing implementations, competitors, or standard approaches
   - Generate novel approaches that directly address the core requirements

4. **Reason Step-by-Step:**
   - Present clear, logical reasoning at each stage
   - Explain why each decision follows from fundamental principles
   - Verify that no unjustified assumptions have crept back in

### SMT Solver Thinking

Apply SMT (Satisfiability Modulo Theories) solver methodology to expose logical inconsistencies and hidden assumptions:

1. **Logical Inversion:**
   - Take any claim or requirement and invert it logically
   - Test whether the negation leads to contradictions or reveals unstated constraints
   - Example: If "this optimization is always beneficial," test scenarios where it might not be

2. **Identify Axiom Systems:**
   - When facing disagreements or design conflicts, identify the underlying axiom systems
   - Distinguish between conflicts arising from different foundational assumptions versus genuine incompatibilities
   - Make implicit axioms explicit before proceeding

3. **Establish Formal Constraints:**
   - Define precise success criteria and significance thresholds before implementation
   - Expose vague statements (e.g., "good enough performance") by demanding concrete bounds
   - Reject solutions that cannot be formally verified against stated requirements

4. **Proof by Contradiction:**
   - When uncertain about correctness, assume the opposite and derive consequences
   - If contradictions emerge, the original approach is validated
   - If no contradictions arise, reconsider the assumptions

### Application Guidelines

- When designing new components, start from the fundamental requirements rather than copying existing patterns
- When debugging, trace issues to their root cause in the fundamental behavior of the system
- When evaluating trade-offs, ground decisions in first principles rather than conventional wisdom
- When someone suggests "this is how it's usually done," ask whether that approach is necessary given the fundamentals
- Before implementing, invert key assumptions to test their necessity
- When requirements seem vague, establish formal constraints to expose ambiguities

This approach ensures that Tuffy's architecture emerges from sound reasoning rather than inherited assumptions, leading to more elegant and correct solutions.

## Quality Standards and Anti-Slop Policy

**CRITICAL:** You must never take shortcuts, use workarounds, or produce low-quality "slop" output. Every solution must be thorough, correct, and properly reasoned.

### Prohibited Behaviors

- **No Placeholder Solutions:** Never use TODO comments, stub implementations, or "this will be implemented later" patterns unless explicitly requested
- **No Superficial Fixes:** Do not apply band-aid solutions that mask symptoms without addressing root causes
- **No Assumption Skipping:** Do not proceed with unstated assumptions; make all assumptions explicit and verify them
- **No Generic Responses:** Avoid vague, general advice when specific, actionable solutions are required
- **No Premature Conclusions:** Do not jump to solutions before thoroughly understanding the problem

### Mandatory Practices

1. **Verify Before Acting:**
   - Read relevant code before proposing changes
   - Understand existing architecture before adding new components
   - Check test results before claiming success

2. **Reason Explicitly:**
   - Show your reasoning step-by-step
   - Explain why each decision follows from requirements
   - Identify what you know, what you assume, and what you need to verify

3. **Demand Precision:**
   - When requirements are vague, ask clarifying questions
   - Establish concrete success criteria before implementation
   - Define measurable outcomes rather than accepting "good enough"

4. **Self-Critique:**
   - After proposing a solution, identify its potential weaknesses
   - Consider edge cases and failure modes
   - Ask: "What could go wrong with this approach?"

5. **Iterate Toward Correctness:**
   - Treat initial solutions as drafts requiring validation
   - Test assumptions through implementation
   - Refine based on actual results, not wishful thinking

### Quality Checklist

Before completing any task, verify:
- [ ] Have I understood the root cause, not just symptoms?
- [ ] Does this solution address fundamental requirements?
- [ ] Have I tested this works, not just assumed it will?
- [ ] Are there hidden assumptions I haven't validated?
- [ ] Would this solution survive adversarial review?

## Language Policy

**IMPORTANT:** When interacting with the user, you MUST match the language they are using. If the user writes in Chinese, respond in Chinese. If the user writes in English, respond in English.

Always use English when editing files (code, comments, documentation). All content committed to git must be in English — this includes code, comments, documentation, commit messages, and task/RFC documents.

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

Short-term goals and milestones belong in `docs/tasks/`, not in `README.md`. `README.md` should only contain long-term vision and project-level information.

## Development Environment

Development uses VS Code dev containers built on `mcr.microsoft.com/devcontainers/rust:latest`. The container includes cmake, ninja-build, gdb/gdbserver, and mounts the workspace at `/tuffy`. Cargo cache is persisted via a Docker volume.

To open the dev container, use the VS Code "Reopen in Container" command.

## Branching Strategy

All development happens on the `main` branch. Keep a linear history (no merge commits). Use `git rebase` instead of `git merge` when needed.

## Commit Convention

Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Common types: `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`, `ci`, `chore`. Append `!` before the colon for breaking changes.

Commit messages must include a body explaining what was changed and why. Do not write title-only commits.

Before committing, ensure `cargo test` and `cargo clippy` pass without errors. `rustc_codegen_tuffy/tests/run-ui-tests.sh` is only run in CI — do not run it before committing.

Before running UI tests (`run-ui-tests.sh`), always update the Rust nightly toolchain (`rustup update nightly`) and rebuild the codegen backend. The UI test suite is pulled from upstream rust-lang/rust and may use features only available in the latest nightly.

Changes to different components must be committed separately. Each individual commit must pass all existing tests (`cargo test`, `cargo clippy`, `rustc_codegen_tuffy/tests/run-ui-tests.sh`). Do not bundle unrelated component changes into a single commit.

Automatically decide when to commit based on logical units of work. Do not ask the user for permission to commit — just commit when a coherent change is complete.

Never amend previous commits (`git commit --amend`). Always create new commits to keep a linear, auditable history.

## Binary Files and Build Artifacts

Place binary outputs in `/tmp` or `scratch/` directory. Do not generate build artifacts in the working directory unless they follow established conventions.

For conventional build directories (e.g., Rust `target/`, Python `.venv/`, Lean `.lake/`), ensure they are listed in `.gitignore`.

**Never commit binary files to git unless explicitly authorized by the user.** This includes compiled executables, libraries (.so, .rlib, .a), object files, and other build artifacts.

## Build Commands

```
cargo build              # Debug build
cargo build --release    # Release build
cargo run                # Run debug build
cargo test               # Run all tests
cargo test <test_name>   # Run a single test
cargo clippy             # Lint
cargo fmt                # Format code
```

### rustc_codegen_tuffy (codegen backend)

`rustc_codegen_tuffy/` is **not** part of the Cargo workspace. It has its own `Cargo.toml` (crate-type `dylib`) and its own `target/` directory. Build it separately:

```
cargo build --manifest-path rustc_codegen_tuffy/Cargo.toml
```

The resulting `.so` is at `rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so`. Use it with rustc:

```
rustc +nightly -Z codegen-backend=rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so \
    -C llvm-args=dump-ir -o out input.rs
```

`cargo build` / `cargo test` / `cargo clippy` at the workspace root do **not** touch this crate.

### Lean 4 (formal verification)

```
cd lean && lake build    # Build Lean project
cd lean && lake clean    # Clean build artifacts
```

Lean 4 is managed via elan (toolchain manager). The Lean project is under `lean/` with Mathlib dependency.

`lean/TuffyLean/README.md` defines module-level conventions for the Lean codebase (directory roles and isel export conventions). Treat it as the canonical guide when modifying files under `lean/TuffyLean/`.

## Documentation

- `docs/tasks/` — task tracking documents
- `docs/RFCs/` — design proposals and RFCs

Documents are archived by year-month under their respective directories, written in Markdown. Each document must include: current status, created time, and completed time. Example path: `docs/tasks/202602/init.md`.

Task documents must additionally include: title, task description, and affected modules (modules expected to be modified).

When starting work on a task, update its status to `In Progress`. When the task is completed, update its status to `Completed` and fill in the completed date.

Templates are available for reference:
- `docs/tasks/template.md` — task document template
- `docs/RFCs/template.md` — RFC document template (based on Rust RFC format)

To list incomplete tasks, run `docs/tasks/list.py`. It displays all tasks not marked as Completed/Cancelled/Abandoned, sorted by creation date.

When the user provides reference documents, categorize and add them to `docs/references.md`. Download a local copy to `scratch/` when possible. Each reference entry should include a brief summary of key conclusions and their relevance to tuffy.

## Code Review Mode

When the user is reviewing code and providing feedback, record each piece of feedback as a task document in `docs/tasks/`. Do not modify code directly and do not enter plan mode during code review.

## Standard Operating Procedures

Before starting a task, check `docs/SOPs/` for a matching SOP. If one exists, follow the procedure defined in it.

## Tool Output Policy

When outputting content using tools, output in multiple smaller segments rather than one large block. Avoid writing excessively large amounts of content in a single tool call.

## Coding Rules

Do not use `static` global variables for mutable state (including `AtomicU64`, `Mutex`, etc.). Counters and other session state must live on a context struct, not at module scope. This ensures deterministic behavior and avoids cross-compilation-unit interference.

**Generated Files:** When encountering a file with "DO NOT EDIT" in its header comment, identify which command or tool generates it before making any changes. Never directly modify generated files — instead, modify the source or generator. For example, `tuffy_target_x86/src/isel_gen.rs` is generated and must not be edited manually.

**Component Conventions:** When modifying code in any component, you MUST follow the conventions and requirements defined in that component's `README.md`. Do not use workarounds or insert special-case logic in inappropriate components. Each component has its own architectural rules — respect them and implement changes in the correct location according to the component's design.

## Testing Policy

**IMPORTANT:** Do not delete or skip existing tests in the repository unless explicitly authorized by the user. All existing tests must continue to pass. This policy ensures test coverage is maintained and prevents regression.

**Regression Tests:** After fixing a bug, you must add a corresponding regression test. For example, when fixing a MIR-to-IR bug in `rustc_codegen_tuffy`, add a new regression test to `rustc_codegen_tuffy/tests/codegen` and use `rustc_codegen_tuffy/tests/update-codegen-test.sh` to generate check lines.

## Architecture

The IR definition in Lean 4 (`lean/TuffyLean/IR/`) is the **source of truth**. The Rust implementation (`tuffy_ir/`) and the spec (`docs/spec/`) must conform to the Lean definitions. When there is a conflict, the Lean code takes precedence.

`docs/initial.md` is frozen — it records early design decisions and must not be modified. New design discussions belong in `docs/RFCs/`.

Source code architecture overviews are documented in the `README.md` within each component's directory. For example, when modifying `rustc_codegen_tuffy`, you must follow the requirements defined in `rustc_codegen_tuffy/README.md`.

**CRITICAL: Do Not Assume LLVM Semantics**

Tuffy is NOT LLVM. Do not infer Tuffy's design, IR semantics, or behavior based on your knowledge of LLVM or other compiler infrastructures. Tuffy has its own unique design principles and semantics that may differ significantly from conventional compilers.

Before taking any action:
1. **Read the relevant documentation** — consult `docs/spec/`, component READMEs, Lean definitions, and RFCs
2. **Explore the codebase structure** — use Glob/Grep to understand how components are organized and how they interact
3. **Verify your understanding** — base decisions on what you've actually read, not on assumptions from other compilers

Never fabricate or guess at semantics, instruction behavior, or design decisions. If documentation is unclear or missing, ask the user for clarification rather than proceeding with assumptions.
