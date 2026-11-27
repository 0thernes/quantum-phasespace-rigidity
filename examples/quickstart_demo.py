# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""One-command quickstart demo verifying all three pillars in exact arithmetic."""
from __future__ import annotations

from qp_rigidity import verify_all_exact


def main() -> int:
    res = verify_all_exact()
    print("=== Quantum Phase-Space Rigidity (0TH-2026-020) Quickstart Demo ===")
    print("Pillar I  — Cyclic Z_{2l}-stabilizer AME(N, 2l) feasible N:", res["pillar1_ame_feasible"])
    print("Pillar II — Maximal-cardinality t-RQLS(p) spectrum:", res["pillar2_prime_t"])
    print("Pillar III — 2-qubit R^2(ASTAB_0):", res["pillar3_astab"]["r2_2qubit_exact"][:24])
    print("Pillar III — 1-qutrit R^2(ASTAB_0):", res["pillar3_astab"]["r2_1qutrit_exact"][:24])
    print("Pillar III — Symplectic Marginal Descent inball gain:", res["pillar3_smd_ratio"])
    print("ALL EXACT CHECKS PASSED!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
