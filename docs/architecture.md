# Architecture Overview

`quantum-phasespace-rigidity` (`0TH-2026-020`) pairs a **zero-Mathlib Lean 4.35.0 formal proof kernel** with a **7-engine polyglot independent computational verification stack** and an **AMS-LaTeX manuscript + interactive GitHub Pages Observatory**.

```
                   ┌──────────────────────────────────────────────┐
                   │   Weyl–Heisenberg Phase-Space Rigidity       │
                   │   (Z_d Rings · F_q Fields · Lambda_n Duals)  │
                   └────────────────────┬─────────────────────────┘
          ┌─────────────────────────────┼─────────────────────────────┐
          ▼                             ▼                             ▼
  Pillar I: AMEGraph          Pillar II: ResolvableQLS      Pillar III: MagicGeometry
  • Radical-CRT (T1a)         • Trace-Spanning (T2a)        • Odd-p AWP ⊆ ASEP (T3a)
  • Unimodular K2,K3,C5,      • 3-RQLS(11), 4-RQLS(13),     • 2-Qubit Entangled ASTAB
    Prism, W5 (T1b)             3-RQLS(16), 2-RQLS(9) (T2b)   & Sep Non-ASTAB (T3a)
  • Pless Bound (T1c)         • Direct-Product Lift (T2c)   • Exact ASTAB Circumradii
  • Rains Shadow (T1d)        • Exhaustive F_8 Obs. (T2d)     2-Qubit & 1-Qutrit (T3b)
  • All Cyclic Z_{2l} (T1e)                                 • Symplectic Marginal 15/7x
  • Z_4 vs F_4 Split (T1e)                                    + Deg-2 RLT Barrier (T3c)
          │                             │                             │
          └─────────────────────────────┼─────────────────────────────┘
                                        ▼
  ┌─────────────────────────────────────────────────────────────────────────┐
  │ Layer 1: Zero-Mathlib Lean 4.35.0 (6 independent kernels, --paranoid)   │
  │ Layer 2: Polyglot Native & Exact Verifiers                              │
  │   • x86-64 NASM ASM (AVX2/POPCNT Pauli weight & symplectic kernel)      │
  │   • ISO C11 (-Werror) + Moonlab (SHA3/CTR_DRBG/QRNG) + QGTL Metric/Berry│
  │   • C++20 Exact Cyclotomic Ring Z[zeta_p] t-RQLS Verifier               │
  │   • Zig 0.17.0 comptime F_q Generator & Exhaustive F_7/F_8 Prover       │
  │   • Rust 1.94.1 (#![forbid(unsafe_code)]) 22,320-vertex Lambda_2 Auditor│
  │   • Eshkol Dual-Number Forward-Mode AD (ASTAB KKT & QGTL Trajectories)  │
  │   • Python 3.12 Exact Fraction/Decimal Oracle + Differential + Mutation │
  │ Layer 3: AMS-LaTeX Paper + Vector PDFs + GitHub Pages Observatory       │
  │ Layer 4: SLSA Provenance + RFC 3161 (.tsr) + OpenTimestamps (.ots)      │
  └─────────────────────────────────────────────────────────────────────────┘
```
