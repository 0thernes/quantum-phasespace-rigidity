<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Environment & Configuration Reference (`docs/configuration.md`)

All engines and scripts in `0thernes/quantum-phasespace-rigidity` run deterministically with zero secrets and zero mandatory environment variables. Optional runtime toggles are documented below and mirrored in [`.env.example`](../.env.example).

| Variable | Default | Scope | Purpose |
| :--- | :--- | :--- | :--- |
| `REQUIRE_ALL_ENGINES` | `0` (unset) | `tests/test_all.py` | When set to `1`, cross-language differential tests **fail** if any compiled native binary (`qpr-rust`, `qpr_zig`, `qpr_cpp`, `qpr_c`) is missing instead of skipping. Enabled unconditionally in GitHub Actions unified differential CI. |
| `PYTHONPATH` | `src:.` | Python scripts & tests | Adds `src/qp_rigidity` and `reference/` to module resolution without requiring editable installation. |
| `QPR_NO_ASM` | unset | `c/Makefile` (`-DQPR_NO_ASM`) | Compiles portable ISO C11 fallback kernels in `c/src/qpr_core.c` instead of linking x86-64 NASM assembly (`asm/pauli_popcnt.asm`) on non-x86 architectures (e.g., ARM64). |
| `FUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION` | unset | `c/tests/fuzz_qpr.c` | Enables `LLVMFuzzerTestOneInput` for Clang `-fsanitize=fuzzer,address,undefined` runs. |
