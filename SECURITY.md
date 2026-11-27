# Security Policy

## Scope
`quantum-phasespace-rigidity` is an offline mathematical verification, formal proof, and scientific computing repository. It performs no network listening, stores no user credentials, and requires no runtime secrets.

## Reporting a Vulnerability or Proof-Soundness Defect
If you discover a memory-safety issue in the C11/C++20/NASM engines, a build-supply-chain issue, or a mathematical/formalization soundness defect (e.g., an unintended axiom, vacuous hypothesis, or misformalized definition):
- Email: `0_0@0thernes.art` (Alexander Stephen Donahue)
- Or open a public GitHub issue using the `Math Correction` or `Bug Report` template.

## Security Measures
- Rust engine enforces `#![forbid(unsafe_code)]` with zero external crates.
- ISO C11 and C++20 engines compile under `-Wall -Wextra -Werror`, AddressSanitizer + UndefinedBehaviorSanitizer in CI, and randomized fuzzing (`fuzz_qpr`).
- Vendored Moonlab cryptographic primitives (`c/third_party/moonlab/`) are pinned by exact commit SHA (`cd3b2347e3739327548708073d7e4ac710cc6a6c`) and audited with NIST SP 800-90B RCT/APT health tests.
- Release artifacts carry SHA-256 manifests (`MANIFEST.sha256`, `SHA256SUMS`), GitHub SLSA build provenance attestations, RFC 3161 DigiCert timestamps, and Bitcoin OpenTimestamps proofs.
