# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Guard script ensuring README.md contains the verbatim Lean 4 `#print axioms` output
from `results/lean_axioms.txt` and strictly zero unauthorized axioms or `0thernes LLC` strings."""
from __future__ import annotations

import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    axioms_path = REPO / "results" / "lean_axioms.txt"
    readme_path = REPO / "README.md"
    if not axioms_path.exists():
        print(f"[FAIL] Missing {axioms_path}", file=sys.stderr)
        return 1
    if not readme_path.exists():
        print(f"[FAIL] Missing {readme_path}", file=sys.stderr)
        return 1

    raw = axioms_path.read_text(encoding="utf-8").strip()
    lines = [ln.strip() for ln in raw.splitlines() if ln.strip()]
    assert len(lines) == 23, f"Expected 23 audited declarations, got {len(lines)}"

    for ln in lines:
        if "does not depend on any axioms" in ln:
            continue
        assert "depends on axioms: [" in ln and ln.endswith("]"), f"Malformed axiom line: {ln}"
        inner = ln.split("depends on axioms: [", 1)[1][:-1]
        used = {tok.strip() for tok in inner.split(",") if tok.strip()}
        disallowed = used - ALLOWED
        assert not disallowed, f"Disallowed axiom(s) {disallowed} in: {ln}"

    readme = readme_path.read_text(encoding="utf-8")
    for ln in lines:
        if ln not in readme:
            print(f"[FAIL] README.md missing verbatim axiom line:\n  {ln}", file=sys.stderr)
            return 1

    # Also enforce zero legacy affiliation leaks across tracked markdown/tex/yaml/json/source
    skip_dirs = (
        ".git/", ".venv/", ".lake/", "target/", "build/",
        "third_party/", "zig-out/", "zig-cache/",
    )
    text_exts = {
        ".md", ".tex", ".bib", ".cff", ".yaml", ".yml", ".json", ".py",
        ".rs", ".zig", ".c", ".h", ".cpp", ".lean", ".esk", ".html", ".txt",
    }
    bad_hits = []
    for p in REPO.rglob("*"):
        if not p.is_file():
            continue
        rel = str(p.relative_to(REPO)).replace("\\", "/")
        if any(seg in rel for seg in skip_dirs):
            continue
        if p.suffix.lower() in text_exts:
            txt = p.read_text(encoding="utf-8", errors="ignore")
            if "0thernes LLC" in txt and p.name not in {"check_readme_axioms.py", "hardening_audit.py"}:
                bad_hits.append(rel)
    if bad_hits:
        print(f"[FAIL] Found forbidden legacy affiliation string in: {bad_hits}", file=sys.stderr)
        return 1

    print(
        f"[OK] Verified all {len(lines)} Lean 4 axiom lines verbatim in README.md "
        "and zero forbidden affiliation strings."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
