# ADR 0001: Zero-Mathlib Lean 4.35.0 Kernel + 7-Engine Polyglot Verification

- **Status:** Accepted (2026-11-26)
- **Context:** Large proof libraries depending on Mathlib often suffer version churn, slow replay across external kernels, and opaque axiom footprints. Meanwhile, floating-point scripts alone cannot certify exact combinatorics, cyclotomic inner products, or polytope extremes.
- **Decision:** Formalize all core theorems of Pillars I, II, and III in **zero-Mathlib pure Lean 4.35.0** using `module` syntax so every theorem replays across all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) in minutes with axioms strictly inside `[propext, Classical.choice, Quot.sound]`. Pair the formal proofs with 7 independent polyglot engines (NASM x86-64, ISO C11 + Moonlab/QGTL, C++20 $\mathbb{Z}[\zeta_p]$, Zig 0.17.0 `comptime`, Rust 1.94.1, Eshkol AD, Python 3.12 exact oracle) cross-checked differentially.
- **Consequences:** Completely self-contained, zero external Lean package risk, sub-minute local builds, and maximal independent verifiability.
