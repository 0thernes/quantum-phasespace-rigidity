# Replication & Independent Verification Guide

Every theorem, table, figure, and numerical certificate in `quantum-phasespace-rigidity` (`0TH-2026-020`) is independently reproducible offline without API keys or external services.

## 1. Pinned Toolchains
- **Lean 4:** `leanprover/lean4:v4.35.0` (zero Mathlib)
- **Rust:** `rustc 1.94.1` (`cargo`, `clippy`)
- **Zig:** `zig 0.17.0`
- **C / C++ / ASM:** `gcc` / `g++` (C11 / C++20) + `nasm 2.16.03`
- **Python:** `Python 3.12` (`requirements.lock.txt`)
- **LaTeX:** `Tectonic` (`tectonic -X compile`)

## 2. Step-by-Step Verification

### A. Machine-Checked Lean 4.35.0 Proofs (6 Independent Kernels)
```bash
cd lean
lake build
lake build PalomarChallenge
lake env lean VerifyAxioms.lean > ../results/ci_lean_axioms.txt
diff -u ../results/lean_axioms.txt ../results/ci_lean_axioms.txt
lake env leanchecker --fresh PalomarSolution
lake env leanchecker-paranoid --fresh PalomarSolution
# On Linux with bubblewrap installed (all 6 independent proof kernels):
lake check --paranoid
lake comparator --config comparator.json --paranoid
```

### B. Polyglot Computational Verification (7 Engines)
```bash
# 1. Rust (forbid unsafe, zero external crates — 22,320-vertex Lambda_2 audit + Rains shadows)
cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all

# 2. Zig 0.17.0 (comptime F_q Megyesi t-RQLS + exhaustive F_7/F_8 obstruction)
cd zig && zig test src/main.zig && zig build-exe -OReleaseSafe src/main.zig -femit-bin=zig-out/qpr_zig && ./zig-out/qpr_zig --verify-all

# 3. C++20 (exact cyclotomic-integer Z[zeta_p] t-RQLS Gram & cardinality verification)
cd cpp && make test && ./build/qpr_cpp --verify-all

# 4. ISO C11 + x86-64 NASM Assembly + Vendored Moonlab/QRNG + QGTL Metric/Curvature
cd c && make test && ./build/qpr_c --verify-all

# 5. Eshkol Forward-Mode Dual-Number AD (ASTAB KKT + QGTL trajectory)
python3 eshkol/run_eshkol_ad.py --verify-all

# 6. Python 3.12 Exact Oracle, Differential Tests, Property Tests & Mutation Tests
PYTHONPATH=src:. pytest -v tests/test_all.py
python3 scripts/mutate.py
python3 scripts/check_readme_axioms.py
python3 scripts/check_citations.py
```

### C. Manuscript, Figures & Clean-Room arXiv Tarball
```bash
python3 scripts/generate_figures.py
mkdir -p paper/build
tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
mkdir -p /tmp/arxiv_cleanroom/out
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_cleanroom
tectonic -X compile /tmp/arxiv_cleanroom/main.tex --outdir /tmp/arxiv_cleanroom/out
```

### D. Cryptographic Integrity Check
```bash
sha256sum -c MANIFEST.sha256
sha256sum -c SHA256SUMS
```

## 3. Independent Replication Log

| Date | Environment | Scope Verified | Outcome |
| :--- | :--- | :--- | :--- |
| 2026-11-26 | Windows 11 x86-64 (ReFS Dev Drive) — Lean 4.35.0, Rust 1.94.1, Zig 0.17.0, GCC/G++ 15, NASM 2.16, Python 3.12, Tectonic | Full 7-engine build, 23 Lean declarations (`leanchecker-paranoid`), 100k NASM fuzz, 6/6 mutants, 0-overfull PDF + clean-room arXiv tarball | **PASS** |
| 2026-11-26 | GitHub Actions Linux (`ubuntu-latest`) + macOS + Windows CI matrix (run [`45947314711`](https://github.com/0thernes/quantum-phasespace-rigidity/actions/runs/45947314711)) | All 8 jobs: 6-kernel Lean 4.35.0 Palomar Comparator in bubblewrap (`11m 54s`), 3-OS Rust, Zig `master`, C++20/C11/NASM ASan+UBSan+100k fuzz, Python/Eshkol/100% mutation, Tectonic clean-room arXiv + Build Standard v1.2.0 | **PASS (8/8)** |
| 2026-11-27 | Windows 11 x86-64 (ReFS Dev Drive, `v2.0.0`) — Lean 4.35.0 (`warningAsError=true`), Rust 1.94.1, Zig 0.17.0, GCC/G++ 15, NASM 2.16, Python 3.12, Tectonic | 311-decl `SweepAllAxioms.lean` + `leanchecker-paranoid`, Rust (1,770 pairs / 240 CNC / 336 $n=3$ subspaces), `REQUIRE_ALL_ENGINES=1` pytest (12/12 + Draft 2020-12 schema + README exec), 12/12 mutants, 25/25 live citations, 0-overfull PDF (`509,489` B), 1,000/1,000 zero-padding audit, 69/69 Build Standard v1.2.0 | **PASS** |
