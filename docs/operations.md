# Operations & CI Runbook

## Local Development Workflow (Build Standard R1–R4)
- Work directly on `main`.
- Run `just verify-all` (or individual engine commands from `REPLICATION.md`) before pushing.
- Push directly to `origin main`. Monitor GitHub Actions workflows (informational; any failure is triaged and fixed via a direct follow-up commit to `main`).

## CI Workflows
1. `.github/workflows/ci.yml`:
   - `lean-6kernel`: Ubuntu + bubblewrap + Lean 4.35.0 (`lake build`, `VerifyAxioms.lean` diff, negative axiom test, `leanchecker`, `leanchecker-paranoid`, `lake check --paranoid`, `lake comparator --paranoid`).
   - `rust-matrix`: Ubuntu / macOS / Windows (`cargo clippy --all-targets -- -D warnings`, `cargo test --release`, `--verify-all`).
   - `zig-matrix`: Ubuntu / Windows (`zig test`, `ReleaseSafe` build + `--verify-all`).
   - `cpp-c-asm-sanitizers`: Ubuntu (`nasm` + `gcc -Werror` + `g++ -std=c++20 -Werror` + ASan/UBSan + 100k fuzz + Moonlab QRNG health tests + QGTL checks).
   - `python-eshkol-differential`: Ubuntu / macOS / Windows (`pytest`, Hypothesis, `eshkol/run_eshkol_ad.py`, cross-language differential checks, `mutate.py`, `check_readme_axioms.py`, `check_citations.py`).
   - `latex-and-provenance`: Tectonic compile (0 overfulls/warnings), clean-room `dist/arxiv_submission.tar.gz` compile, SHA-256 verification, SLSA build provenance attestation.
   - `lint-audit-security`: Ruff, mypy, `scripts/audit-repo.sh`, secret/placeholder scan.
2. `.github/workflows/pages.yml`:
   - Deploys `docs/site/` (Interactive Observatory + Lean Blueprint DAG) to GitHub Pages.
3. `.github/workflows/release.yml`:
   - Triggered on `v*` tags: verifies `SHA256SUMS` & `MANIFEST.sha256`, emits SLSA build provenance (`actions/attest-build-provenance@v2`), and publishes release artifacts.

## Offsite Backup, Archival Mirror & Bundle Protocol
- **Master Research Archive Mirror:** Pinned commit submodule and frozen PDF mirrored in `https://github.com/0thernes/0thernes-research-archive` under `0TH-2026-020`.
- **Software Heritage Preservation:** Public origin snapshot archived via Software Heritage Save Code Now for permanent SWHID retrieval.
- **Offline Git Bundle Backup:** Generate a self-contained verifiable archive bundle via:
  ```bash
  git bundle create quantum-phasespace-rigidity-v1.0.0.bundle --all
  git bundle verify quantum-phasespace-rigidity-v1.0.0.bundle
  ```
