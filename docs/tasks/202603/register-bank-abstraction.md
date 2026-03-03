# Add Register Bank Abstraction to tuffy_target

- Status: Pending
- Created: 2026-03-03
- Completed: N/A
- Parent: N/A

## Description

Currently, tuffy_target does not provide an abstraction for register banks, which is needed to properly support x86's vector register hierarchy (xmm/ymm/zmm). These registers have overlapping physical storage:
- xmm0-xmm15: 128-bit SSE registers
- ymm0-ymm15: 256-bit AVX registers (lower 128 bits alias xmm)
- zmm0-zmm31: 512-bit AVX-512 registers (lower 256 bits alias ymm, lower 128 bits alias xmm)

The register allocator needs to understand these aliasing relationships to avoid conflicts when allocating registers from different banks that share physical storage.

### Requirements

1. Define a register bank abstraction in tuffy_target that can represent:
   - Multiple register classes (e.g., GPR, XMM, YMM, ZMM)
   - Aliasing relationships between registers
   - Register constraints and availability

2. Integrate the register bank abstraction with the existing register allocation infrastructure

3. Implement x86-specific register banks in tuffy_target_x86:
   - GPR bank (rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8-r15)
   - XMM bank (xmm0-xmm15)
   - YMM bank (ymm0-ymm15, aliases XMM)
   - ZMM bank (zmm0-zmm31, aliases YMM and XMM)

4. Update register allocation to respect bank constraints and aliasing

### Affected Modules

- `tuffy_target/` — core register bank abstraction
- `tuffy_target_x86/` — x86-specific register bank implementation
- Register allocator (if exists) — integration with bank abstraction

### Notes

This is a prerequisite for proper SIMD support in the x86 backend. The abstraction should be general enough to support other architectures with similar register aliasing (e.g., ARM NEON).
