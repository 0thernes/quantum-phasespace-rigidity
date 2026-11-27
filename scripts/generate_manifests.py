# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate deterministic cryptographic SHA-256 manifests (MANIFEST.sha256 and SHA256SUMS)."""
from __future__ import annotations

import hashlib
import pathlib

REPO = pathlib.Path(__file__).resolve().parent.parent

CANONICAL_FILES = [
    "dist/Donahue_2026_quantum_phasespace_rigidity.pdf",
    "dist/arxiv_submission.tar.gz",
    "data/certificates.json",
    "results/lean_axioms.txt",
    "paper/main.tex",
    "paper/references.bib",
    "paper/figures/fig1_ame_phase_diagram.pdf",
    "paper/figures/fig2_rqls_frontier.pdf",
    "paper/figures/fig3_astab_magic_geometry.pdf",
    "paper/figures/fig4_qgtl_and_architecture.pdf",
    "lean/PalomarChallenge.lean",
    "lean/PalomarSolution.lean",
    "lean/QPRigidity/AMEGraph.lean",
    "lean/QPRigidity/ResolvableQLS.lean",
    "lean/QPRigidity/MagicGeometry.lean",
    "lean/QPRigidity/NonVacuity.lean",
    "lean/QPRigidity/AdversarialTests.lean",
    "lean/VerifyAxioms.lean",
    "rust/src/main.rs",
    "zig/src/main.zig",
    "cpp/src/qpr_cyclotomic.cpp",
    "c/src/main.c",
    "c/src/qpr_core.c",
    "c/src/qgtl_metric.c",
    "c/src/qrng_fw.c",
    "asm/pauli_popcnt.asm",
    "eshkol/astab_kkt_ad.esk",
    "eshkol/qgtl_trajectory_ad.esk",
    "src/qp_rigidity/oracle.py",
]


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    lines: list[str] = []
    for rel in CANONICAL_FILES:
        p = REPO / rel
        if not p.exists():
            raise FileNotFoundError(f"Missing canonical artifact: {rel}")
        lines.append(f"{sha256_file(p)}  {rel}")
    body = "\n".join(lines) + "\n"
    (REPO / "MANIFEST.sha256").write_text(body, encoding="utf-8")

    dist_lines = [ln for ln in lines if ln.split("  ", 1)[1].startswith(("dist/", "data/", "results/"))]
    (REPO / "SHA256SUMS").write_text("\n".join(dist_lines) + "\n", encoding="utf-8")
    print(f"[MANIFEST] Wrote MANIFEST.sha256 ({len(lines)} files) and SHA256SUMS ({len(dist_lines)} files).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
