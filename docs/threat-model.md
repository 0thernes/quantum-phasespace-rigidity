# Threat & Soundness Model

## Scope
Because this is an offline formal-verification and scientific-computing repository, the primary threat model is **epistemic and verification soundness**, alongside standard native-code memory safety and artifact integrity.

| Threat Vector | Mitigation Implemented |
| --- | --- |
| Unintended axioms / `sorry` / `native_decide` in Lean proofs | `VerifyAxioms.lean` asserts exact `#print axioms` strictly inside `[propext, Classical.choice, Quot.sound]`; negative CI test injects a bogus axiom and verifies audit failure; `lake comparator --paranoid` replays every theorem across 6 independent kernels in bubblewrap. |
| Statement-fidelity drift (weakened or vacuous formal statements) | Explicit `PalomarChallenge.lean` contract, `NonVacuity.lean` witness instantiations, `AdversarialTests.lean` false-variant rejections, and human-auditable `docs/statement-fidelity.md` table. |
| Documentation / README axiom drift | `scripts/check_readme_axioms.py` enforces byte-for-byte match between README verbatim `#print axioms` block and live `results/lean_axioms.txt`. |
| Memory safety / UB in C11 / C++20 / NASM / Zig | `-Wall -Wextra -Werror`, ASan + UBSan CI job, 100k-iteration fuzzer (`fuzz_qpr`), Zig `ReleaseSafe`, Rust `#![forbid(unsafe_code)]`, dual Win64/SysV ABI verification. |
| Hallucinated or retracted citations | `scripts/check_citations.py` verifies every BibTeX entry against arXiv / Crossref metadata (title, author, year, DOI, retraction status). |
| Weak tests / surviving mutants | `scripts/mutate.py` executes surgical code mutations against `src/qp_rigidity/` verifying 100% mutant kill rate, plus cross-language differential oracle tests across all 7 engines. |
| Post-publication tampering or backdating | `MANIFEST.sha256`, `SHA256SUMS`, GitHub SLSA build provenance attestation, RFC 3161 DigiCert `.tsr`, and Bitcoin OpenTimestamps `.ots`. |
