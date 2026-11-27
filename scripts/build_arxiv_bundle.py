# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Compile paper/main.tex, audit 0 overfull hboxes / 0 LaTeX warnings, export frozen PDF
to dist/, build standalone dist/arxiv_submission.tar.gz, and clean-room compile it."""
from __future__ import annotations

import hashlib
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

REPO = pathlib.Path(__file__).resolve().parent.parent
PAPER = REPO / "paper"
BUILD = PAPER / "build"
DIST = REPO / "dist"


def find_tectonic() -> str:
    cand = shutil.which("tectonic")
    if cand:
        return cand
    win_local = pathlib.Path.home() / ".local" / "bin" / "tectonic.exe"
    if win_local.exists():
        return str(win_local)
    raise FileNotFoundError("tectonic executable not found on PATH or ~/.local/bin")


def main() -> int:
    check_only = "--check-only" in sys.argv
    tectonic = find_tectonic()
    BUILD.mkdir(parents=True, exist_ok=True)
    DIST.mkdir(parents=True, exist_ok=True)

    # 1. Compile main.tex with logs
    res = subprocess.run(
        [tectonic, "-X", "compile", "main.tex", "--outdir", "build", "--keep-logs", "--keep-intermediates"],
        cwd=str(PAPER),
        capture_output=True,
        text=True,
    )
    print(res.stdout, flush=True)
    if res.stderr:
        print(res.stderr, file=sys.stderr, flush=True)
    if res.returncode != 0:
        raise RuntimeError(f"Tectonic build failed ({res.returncode})")

    # 2. Audit log for overfull hboxes and LaTeX/BibTeX warnings
    log_txt = (BUILD / "main.log").read_text(encoding="utf-8", errors="ignore")
    overfull = re.findall(r"Overfull \\hbox.*", log_txt)
    warnings = [
        ln for ln in log_txt.splitlines()
        if ("LaTeX Warning:" in ln or "Package hyperref Warning:" in ln or "Citation `" in ln)
    ]
    print(f"[TEX AUDIT] Overfull hboxes: {len(overfull)} | LaTeX warnings: {len(warnings)}")
    for o in overfull:
        print("  OVERFULL:", o)
    for w in warnings:
        print("  WARNING:", w)
    if overfull or warnings:
        raise RuntimeError("Typography/warning gate failed! Fix all overfull hboxes and warnings.")

    # 3. Copy frozen PDF to dist/ (unless --check-only in CI, preserving committed hashes)
    pdf_src = BUILD / "main.pdf"
    pdf_dst = DIST / "Donahue_2026_quantum_phasespace_rigidity.pdf"
    tar_path = DIST / "arxiv_submission.tar.gz"
    if not check_only:
        shutil.copy2(pdf_src, pdf_dst)
        pdf_sha = hashlib.sha256(pdf_dst.read_bytes()).hexdigest()
        print(f"[DIST] Frozen PDF: {pdf_dst.name} ({pdf_dst.stat().st_size} bytes, SHA-256: {pdf_sha})")

        # 4. Build standalone arXiv submission tarball (main.tex, references.bib, main.bbl, figures/*.pdf)
        files_to_pack: list[tuple[pathlib.Path, str]] = [
            (PAPER / "main.tex", "main.tex"),
            (PAPER / "references.bib", "references.bib"),
        ]
        bbl = BUILD / "main.bbl"
        if bbl.exists():
            files_to_pack.append((bbl, "main.bbl"))
        for fig in sorted((PAPER / "figures").glob("*.pdf")):
            files_to_pack.append((fig, f"figures/{fig.name}"))

        with tarfile.open(tar_path, "w:gz") as tf:
            for src, arcname in files_to_pack:
                tf.add(src, arcname=arcname)
        tar_sha = hashlib.sha256(tar_path.read_bytes()).hexdigest()
        print(f"[ARXIV] Tarball: {tar_path.name} ({len(files_to_pack)} files, SHA-256: {tar_sha})")
    else:
        print(
            f"[CHECK-ONLY] Compiled main.pdf ({pdf_src.stat().st_size} bytes); "
            f"verifying committed {tar_path.name}"
        )

    # 5. Clean-room compile verification inside an isolated temp directory
    with tempfile.TemporaryDirectory(prefix="qpr_arxiv_cleanroom_") as tmp:
        tmp_path = pathlib.Path(tmp)
        with tarfile.open(tar_path, "r:gz") as tf:
            tf.extractall(tmp_path, filter="data")
        cr = subprocess.run(
            [tectonic, "-X", "compile", "main.tex"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
        )
        if cr.returncode != 0 or not (tmp_path / "main.pdf").exists():
            print(cr.stdout, flush=True)
            print(cr.stderr, file=sys.stderr, flush=True)
            raise RuntimeError("Clean-room arXiv tarball compile FAILED!")
        pdf_sz = (tmp_path / "main.pdf").stat().st_size
        print(f"[CLEAN-ROOM] arXiv tarball compiled cleanly ({pdf_sz} bytes)!")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
