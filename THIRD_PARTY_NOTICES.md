# Third-Party Notices & Upstream Attributions

This repository (`quantum-phasespace-rigidity`, Copyright 2026 Alexander Stephen Donahue) is dual-licensed under **Apache-2.0** (code) and **CC-BY-4.0** (manuscripts, figures, and documentation). All vendored or referenced upstream open-source projects are attributed below with pinned commit SHAs and preserved licenses.

## 1. Vendored Third-Party Source Code (`c/third_party/moonlab/`)

- **Upstream Repository:** `https://github.com/tsotchke/moonlab`
- **Pinned Commit SHA:** `cd3b2347e3739327548708073d7e4ac710cc6a6c`
- **License:** MIT License (preserved verbatim at [`c/third_party/moonlab/LICENSE-MOONLAB`](c/third_party/moonlab/LICENSE-MOONLAB) with pinned SHA in [`c/third_party/moonlab/UPSTREAM_COMMIT.txt`](c/third_party/moonlab/UPSTREAM_COMMIT.txt))
- **Role in `quantum-phasespace-rigidity`:** Provides FIPS 202 SHA3-256 (`crypto/sha3/`), NIST SP 800-90A CTR_DRBG (`crypto/drbg/`), and NIST SP 800-90B RCT/APT entropy health testing (`applications/health_tests.{h,c}`) used in our C11 engine to drive cryptographically audited stochastic Frank-Wolfe exploration of $\Lambda_3$ and reproducible certificate digests. Zero upstream MIT headers were altered or removed.

## 2. Referenced & Adapted Open-Source Ecosystem (`tsotchke`)

| Repository | Pinned Commit SHA | License | Usage in This Project |
| --- | --- | --- | --- |
| `tsotchke/quantum_geometric_tensor` | `770994aa8ddd858e6bb16eebb25250a7b9f67c96` | MIT | Mathematical formulation for `c/src/qgtl_metric.c` computing exact Fubini-Study metric $g_{\mu\nu}$ and Berry curvature $\Omega_{\mu\nu}$ along entangled-`ASTAB` two-qubit orbits and $t$-RQLS unitary manifolds |
| `tsotchke/eshkol` | `eb224260b4814baf3ad260744c8dcdd05fb84898` | MIT | Target Lisp/Scheme dialect for `eshkol/astab_kkt_ad.esk` and `eshkol/qgtl_trajectory_ad.esk` dual-number forward-mode AD optimization modules |
| `tsotchke/quantum_rng` | `1a77e77f803c63883349b658361c06401cd8ceb7` | MIT | SP 800-90B RCT/APT entropy pipeline reference paired with Moonlab's `health_tests.c` |

## 3. Research Preprints & Literature

No third-party arXiv LaTeX, PDF, or HTML source files are redistributed in this repository. All cited papers (`arXiv:2603.18193v3`, `arXiv:2603.13442v2`, `arXiv:2608.29201v2`, `arXiv:2607.12933v2`, `arXiv:2602.22336v2`, `arXiv:2512.16777v2`, `arXiv:2508.04777`, Gurvits & Barnum PRA 66, 062311, 2002, etc.) are cited strictly via bibliographic references in `paper/references.bib` and verified via `scripts/check_citations.py`.

## 4. Standards & Tooling

- Build Standard for LLMs v1.2.0 audit scripts (`scripts/audit-repo.sh`, `scripts/Audit-Repo.ps1`, `scripts/audit-checks.tsv`, `repo-standard.schema.json`).
- Lean 4.35.0 standard core (`Init`) — zero Mathlib dependency.
