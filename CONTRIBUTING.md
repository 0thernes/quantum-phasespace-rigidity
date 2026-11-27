# Contributing

Contributions, independent proof audits, adversarial counterexample attempts, and replication reports are welcome.

## Standards
1. **Direct & Lightweight:** Issues, patches, and formalization improvements should follow `AGENTS.md` and `repo.yaml` (Build Standard v1.2.0).
2. **Formal Proof Additions (`lean/`):**
   - Must compile under pinned `leanprover/lean4:v4.35.0` with zero Mathlib.
   - Zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms.
   - All axioms must remain strictly within `[propext, Classical.choice, Quot.sound]`, verified by `VerifyAxioms.lean` and `lake comparator --config comparator.json --paranoid`.
3. **Native & Polyglot Engines:**
   - Rust: `cargo clippy --all-targets -- -D warnings && cargo test --release`.
   - Zig: `zig test src/main.zig`.
   - C11/C++20/NASM: `-Wall -Wextra -Werror` clean + ASan/UBSan clean.
   - Python: `pytest`, `ruff check`, `mypy`, and `scripts/mutate.py` 100% kill rate.
4. **Licensing:** Code contributions are licensed under Apache-2.0; documentation and manuscript edits under CC-BY-4.0.
