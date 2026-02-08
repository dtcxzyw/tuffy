# Summary

[Introduction](introduction.md)

# Reference

- [IR Language Reference](spec.md)
- [Initial Design](initial.md)
- [References](references.md)

# RFCs

- [IR Design](RFCs/202602/ir-design.md)
- [Pipeline Design](RFCs/202602/pipeline-design.md)
- [Interpreter](RFCs/202602/interpreter.md)
- [Rewrite Trace](RFCs/202602/rewrite-trace.md)
- [Verification](RFCs/202602/verification.md)

# Development Tasks

- [Project Initialization](tasks/202602/init.md)
  - [Workspace Setup](tasks/202602/01-workspace-setup.md)
  - [Tuffy IR](tasks/202602/02-tuffy-ir.md)
  - [Tuffy IR Interpreter](tasks/202602/03-tuffy-ir-interp.md)
  - [Tuffy Target](tasks/202602/04-tuffy-target.md)
  - [Tuffy Optimizer](tasks/202602/05-tuffy-opt.md)
  - [Tuffy Trace](tasks/202602/06-tuffy-trace.md)
  - [Tuffy TV](tasks/202602/07-tuffy-tv.md)
  - [Tuffy Codegen](tasks/202602/08-tuffy-codegen.md)
  - [rustc Codegen Tuffy](tasks/202602/09-rustc-codegen-tuffy.md)
- [E2E Pipeline](tasks/202602/e2e-pipeline.md)
  - [E2E: IR Minimal](tasks/202602/e2e-01-ir-minimal.md)
  - [E2E: Codegen Backend](tasks/202602/e2e-02-codegen-backend.md)
  - [E2E: MIR to IR](tasks/202602/e2e-03-mir-to-ir.md)
  - [E2E: ISel](tasks/202602/e2e-04-isel.md)
  - [E2E: Emit](tasks/202602/e2e-05-emit.md)
  - [E2E: Test](tasks/202602/e2e-06-test.md)
- [UI Tests](tasks/202602/ui-tests.md)
  - [UI: Constant Operands](tasks/202602/ui-01-constant-operands.md)
  - [UI: ABI Registers](tasks/202602/ui-02-abi-registers.md)
  - [UI: Undefined Locals](tasks/202602/ui-03-undefined-locals.md)
  - [UI: Test Harness](tasks/202602/ui-04-test-harness.md)
- [Hello World](tasks/202602/hello-world.md)
  - [Control Flow](tasks/202602/hw-01-control-flow.md)
  - [Function Calls](tasks/202602/hw-02-function-calls.md)
  - [Memory](tasks/202602/hw-03-memory.md)
  - [Types](tasks/202602/hw-04-types.md)
  - [Linking](tasks/202602/hw-05-linking.md)
  - [Std](tasks/202602/hw-06-std.md)
- [Doctest Support](tasks/202602/doctest.md)
