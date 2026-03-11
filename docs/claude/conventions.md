# Project Conventions

## Commit Convention

Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Common types: `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`, `ci`, `chore`. Append `!` before the colon for breaking changes.

Commit messages must include a body explaining what was changed and why. Do not write title-only commits.

## Documentation

- `docs/tasks/` — task tracking documents
- `docs/RFCs/` — design proposals and RFCs

Documents are archived by year-month under their respective directories, written in Markdown. Each document must include: current status, created time, and completed time. Example path: `docs/tasks/202602/init.md`.

Task documents must additionally include: title, task description, and affected modules (modules expected to be modified).

When starting work on a task, update its status to `In Progress`. When the task is completed, update its status to `Completed` and fill in the completed date.

Templates:
- `docs/tasks/template.md` — task document template
- `docs/RFCs/template.md` — RFC document template (based on Rust RFC format)

To list incomplete tasks, run `docs/tasks/list.py`.

When the user provides reference documents, categorize and add them to `docs/references.md`. Download a local copy to `scratch/` when possible. Each reference entry should include a brief summary of key conclusions and their relevance to tuffy.

## Documentation Maintenance

When code changes affect behavior, update related documentation in the same commit:

- **Inline documentation (doc comments):** Update when function signatures, behavior, or semantics change
- **Component READMEs:** Update when architecture, conventions, or major workflows change
- **`docs/spec/`:** Update when IR semantics or formal specifications change
- **Lean definitions:** Update when fundamental semantics or type definitions change (these are the source of truth)

## Dependency Management

Before adding a new Cargo dependency, verify:
- The functionality cannot be reasonably implemented using existing dependencies or the standard library
- The crate is actively maintained (recent commits, responsive to issues)
- The license is compatible (prefer MIT/Apache-2.0)
- The dependency tree is reasonable (avoid heavy transitive dependencies)

Prefer standard library solutions over external crates when feasible. Document in the commit message why the dependency is necessary and what alternatives were considered.

## Binary Files and Build Artifacts

Place binary outputs in `/tmp` or `scratch/` directory. Do not generate build artifacts in the working directory unless they follow established conventions.

For conventional build directories (e.g., Rust `target/`, Python `.venv/`, Lean `.lake/`), ensure they are listed in `.gitignore`.

**Never commit binary files to git unless explicitly authorized by the user.** This includes compiled executables, libraries (.so, .rlib, .a), object files, and other build artifacts.

## Code Review Mode

When the user is reviewing code and providing feedback, record each piece of feedback as a task document in `docs/tasks/`. Do not modify code directly and do not enter plan mode during code review.

## Standard Operating Procedures

Before starting a task, check `docs/SOPs/` for a matching SOP. If one exists, follow the procedure defined in it.

Current SOPs:
- `docs/SOPs/add-codegen-test.md` — Adding codegen tests
- `docs/SOPs/ir-change.md` — Modifying the Tuffy IR
- `docs/SOPs/docs-update.md` — Updating documentation
