# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Surgical mutation testing harness verifying 100% mutant kill rate on src/qp_rigidity/oracle.py."""
from __future__ import annotations

import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
TARGET = REPO / "src" / "qp_rigidity" / "oracle.py"

MUTANTS = [
    ("M1_ame_dichotomy_add_n4", "return n in (2, 3, 5, 6)", "return n in (2, 3, 4, 5, 6)"),
    ("M2_krawtchouk_sign", "((-1) ** j)", "((1) ** j)"),
    ("M3_astab_2q_denom", "/ Decimal(484)", "/ Decimal(485)"),
    ("M4_astab_1qt_coeff", "Decimal(3) * s5", "Decimal(2) * s5"),
    ("M5_smd_inball_ratio", "Fraction(15, 7 * (2**n)", "Fraction(14, 7 * (2**n)"),
    ("M6_megyesi_quad_res", "pow(g, 2 * k, p)", "pow(g, 3 * k, p)"),
]


def main() -> int:
    original = TARGET.read_text(encoding="utf-8")
    killed = 0
    try:
        for name, old, new in MUTANTS:
            assert old in original, f"Mutant anchor missing: {name}"
            TARGET.write_text(original.replace(old, new, 1), encoding="utf-8")
            env = dict(__import__("os").environ)
            env["PYTHONPATH"] = f"{REPO / 'src'}{__import__('os').pathsep}{REPO}"
            res = subprocess.run(
                [sys.executable, "-m", "pytest", "-q", "tests/test_all.py"],
                cwd=str(REPO),
                env=env,
                capture_output=True,
                text=True,
            )
            status = "KILLED" if res.returncode != 0 else "SURVIVED"
            print(f"[MUTATE] {name}: {status}")
            if res.returncode != 0:
                killed += 1
    finally:
        TARGET.write_text(original, encoding="utf-8")
    print(f"[MUTATE] Summary: {killed}/{len(MUTANTS)} mutants killed (100% required).")
    return 0 if killed == len(MUTANTS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
