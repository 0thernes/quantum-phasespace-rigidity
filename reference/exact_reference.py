# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Independent reference implementation cross-checking src/qp_rigidity/oracle.py."""
from __future__ import annotations

from fractions import Fraction


def pless_a_k_plus_2_even(k: int, p: int) -> int:
    """Closed-form A_{k+2} = C(2k, k+2) * (p^2 - 1) * (p^2 - 1 - k) from Theorem T1c."""
    from math import comb
    return comb(2 * k, k + 2) * (p * p - 1) * (p * p - 1 - k)


def pless_a_k_plus_2_odd(k: int, p: int) -> int:
    """Closed-form A_{k+2} = C(2k+1, k+2) * (p - 1) * (p^2 + p - 1 - k) from Theorem T1c."""
    from math import comb
    return comb(2 * k + 1, k + 2) * (p - 1) * (p * p + p - 1 - k)


def gurvits_barnum_delta_norm_sq(d: int, purity: Fraction) -> Fraction:
    """Exact ||(d-1)*rho - I_d||_2^2 = (d-1)^2 * Tr(rho^2) - 2(d-1) + d."""
    return Fraction((d - 1) ** 2) * purity - 2 * (d - 1) + d
