# Roadmap

## v1.0.0 (Current Release — November 2026)
- Zero-Mathlib Lean 4.35.0 6-kernel-verified proof suite covering Pillars I, II, and III (`T1a`–`T1e`, `T2a`–`T2d`, `T3a`–`T3d`).
- 7-engine polyglot verification stack (NASM x86-64, ISO C11 + Moonlab/QRNG/QGTL, C++20 $\mathbb{Z}[\zeta_p]$, Zig 0.17.0 `comptime`, Rust 1.94.1 `#![forbid(unsafe_code)]`, Eshkol forward-mode AD, Python 3.12 exact oracle).
- AMS-LaTeX white paper (`dist/Donahue_2026_quantum_phasespace_rigidity.pdf`), standalone clean-room `dist/arxiv_submission.tar.gz`, interactive GitHub Pages Observatory & Lean Blueprint.
- 3 full cycles of 1,000-check systematic hardening (`HARDENING_LOG.md`), RFC 3161 + OpenTimestamps cryptographic anchoring, and `0thernes-research-archive` registration (`0TH-2026-020`).

## Future Research Directions (Explicitly Open)
- Resolve Zurel–Davis Conjecture 1 (CNC sufficiency for $n \ge 3$ qubits) and Conjecture 2 ($\max_{X \in \Lambda_n} \operatorname{Tr}(X^2) = 2$ for $n \ge 3$ qubits) using degree-$\ge 3$ algebraic / tropical certificates bypassing our degree-2 RLT+SOS barrier (`T3d`).
- Determine existence of maximal-cardinality $1$-$\mathrm{RQLS}(v)$ for the 17 open orders $v \in \{10,14,18,22,26,30,34,38,42,46,54,58,62,66,74,82,94\}$ left open by Zhang & Cao (`arXiv:2608.29201v2`) beyond Frobenius-field permutation ansätze.
- Extend exact cyclic-ring $\mathbb{Z}_d$ stabilizer classification (`T1e`) to odd composite dimensions $d = 3\ell$ for $N \in \{8, 10, 12, 14, 16\}$ between known MDS constructions and our pure-integer Pless threshold ($N \ge 2p^2$).
