# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Surgical mutation testing harness verifying 12/12 (100%) mutant kill rate on oracle.py."""
from __future__ import annotations

import os
import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
TARGET = REPO / "src" / "qp_rigidity" / "oracle.py"

MUTANTS = [
    ("M01_ame_dichotomy_add_n4", "return n in (2, 3, 5, 6)", "return n in (2, 3, 4, 5, 6)"),
    ("M02_ame_dichotomy_drop_n6", "return n in (2, 3, 5, 6)", "return n in (2, 3, 5)"),
    ("M03_krawtchouk_sign", "((-1) ** j)", "((1) ** j)"),
    ("M04_krawtchouk_q_base", "((q - 1) ** (k - j))", "((q) ** (k - j))"),
    ("M05_rains_shadow_sign", "((-1) ** w)", "((1) ** w)"),
    (
        "M06_rains_feasibility_drop_S",
        "and all(\n        x.denominator == 1 and x >= 0 for x in S",
        "and all(\n        x.denominator >= 1 for x in S",
    ),
    ("M07_megyesi_quad_res", "pow(g, 2 * k, p)", "pow(g, 3 * k, p)"),
    ("M08_megyesi_shift_sign", "(f[x] - m0 * x) % p", "(f[x] + m0 * x) % p"),
    ("M09_astab_2q_denom", "/ Decimal(484)", "/ Decimal(485)"),
    ("M10_astab_1qt_coeff", "Decimal(3) * s5", "Decimal(2) * s5"),
    ("M11_smd_inball_ratio", "Fraction(15, 7 * (2**n)", "Fraction(14, 7 * (2**n)"),
    (
        "M12_smd_c_ours_const",
        "Fraction(7 * (4**n) + 8, 15 * (2**n))",
        "Fraction(7 * (4**n) + 9, 15 * (2**n))",
    ),
]


def main() -> int:
    original = TARGET.read_text(encoding="utf-8")
    killed = 0
    try:
        for name, old, new in MUTANTS:
            assert old in original, f"Mutant anchor missing: {name}"
            TARGET.write_text(original.replace(old, new, 1), encoding="utf-8", newline="\n")
            env = dict(os.environ)
            env["PYTHONPATH"] = f"{REPO / 'src'}{os.pathsep}{REPO}"
            env.pop("REQUIRE_ALL_ENGINES", None)
            res = subprocess.run(
                [sys.executable, "-m", "pytest", "-q", "tests/test_all.py", "-k", "not differential"],
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
        TARGET.write_text(original, encoding="utf-8", newline="\n")
    print(f"[MUTATE] Summary: {killed}/{len(MUTANTS)} mutants killed (100% required).")
    return 0 if killed == len(MUTANTS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
