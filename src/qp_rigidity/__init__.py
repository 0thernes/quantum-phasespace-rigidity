# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Quantum Phase-Space Rigidity (0TH-2026-020) — Exact Rational & Arbitrary-Precision Oracle."""
from .oracle import (
    exact_astab_circumradii,
    exact_cyclic_ame_dichotomy,
    exact_megyesi_rqls_prime,
    exact_rains_shadow_qubit,
    exact_symplectic_marginal_bound,
    verify_all_exact,
)

__all__ = [
    "exact_astab_circumradii",
    "exact_cyclic_ame_dichotomy",
    "exact_megyesi_rqls_prime",
    "exact_rains_shadow_qubit",
    "exact_symplectic_marginal_bound",
    "verify_all_exact",
]
__version__ = "1.0.0"
