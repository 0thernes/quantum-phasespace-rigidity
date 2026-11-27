# AGENTS.md — Operational Guide for Coding & Research Agents

This repository (`quantum-phasespace-rigidity`, archive ID `0TH-2026-020`, author Alexander Stephen Donahue, ORCID `0009-0006-8168-9648`) follows **Build Standard for LLMs v1.2.0** and **Defensible Independent AI Research Playbook v1.3**.

## Hard Rules (Non-Negotiable)
1. **Direct-to-`main` workflow (R1–R3):** Commit and push directly to `main`. No branch protection, no required PRs, no commit/tag signing, no blocking git hooks. CI is strictly informational.
2. **Epistemic & Proof Integrity (R6):**
   - Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom` declarations in `lean/`.
   - All verified Lean theorems must stay strictly within `[propext, Classical.choice, Quot.sound]`.
   - Every Lean file uses `module` syntax (`leanprover/lean4:v4.35.0`, zero Mathlib).
   - Never fabricate citations, DOIs, test runs, or peer-review status.
   - Author affiliation is strictly `Independent Researcher, Spokane, WA, USA` (never a corporate LLC affiliation).
3. **Ten Finding Classes (R7):** Log every hardening/audit finding in `HARDENING_LOG.md` under one of: `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`.

## Architecture Map
- `lean/` — Zero-Mathlib Lean 4.35.0 formal proofs (`QPRigidity/{AMEGraph,ResolvableQLS,MagicGeometry,NonVacuity,AdversarialTests}.lean`, `PalomarChallenge.lean`, `PalomarSolution.lean`, `VerifyAxioms.lean`, `comparator.json`).
- `asm/` — x86-64 NASM AVX2/POPCNT symplectic inner-product & Pauli weight-enumerator kernel (dual Win64 / System V AMD64 ABI).
- `c/` — Strict ISO C11 (`-Werror`) AME minor verifier, QGTL Fubini-Study / Berry curvature engine, and vendored MIT Moonlab (`SHA3-256`, `CTR_DRBG`, SP 800-90B QRNG health tests).
- `cpp/` — Strict C++20 exact cyclotomic-integer $\mathbb{Z}[\zeta_p]$ $t$-RQLS Gram/cardinality verifier.
- `zig/` — Zig 0.17.0 `comptime` $\mathbb{F}_q$ Megyesi $t$-RQLS generator and exhaustive $\mathbb{F}_7/\mathbb{F}_8$ orthomorphism prover.
- `rust/` — `#![forbid(unsafe_code)]`, zero-dependency Rust exact $\Lambda_2$ 22,320-vertex auditor ($C_2 = 2$) & Rains shadow engine.
- `eshkol/` — Dual-number forward-mode AD modules (`*.esk` + exact runner) for `ASTAB` KKT optimization & QGTL curvature trajectories.
- `src/qp_rigidity/` & `reference/` — Python 3.12 exact `Fraction`/`Decimal` oracle & differential harness.
- `paper/` & `dist/` — AMS-LaTeX manuscript, vector PDF figures, frozen PDF, and clean-room `arxiv_submission.tar.gz`.
- `docs/site/` — Interactive Web Observatory and searchable Lean Blueprint DAG.

## Quick Verification Commands
```bash
cd lean && lake build && lake build PalomarChallenge && lake env lean VerifyAxioms.lean
cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all
cd zig && zig test src/main.zig
cd cpp && make test
cd c && make test
PYTHONPATH=src:. pytest -v tests/test_all.py
python scripts/check_readme_axioms.py
python scripts/check_citations.py
```
