# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Comprehensive pytest, Hypothesis property, schema, README, and 7-engine differential test suite."""
from __future__ import annotations

import json
import os
import pathlib
import platform
import re
import subprocess
import sys
from decimal import Decimal, localcontext
from fractions import Fraction

import jsonschema
import pytest
import yaml
from hypothesis import given, settings
from hypothesis import strategies as st

from qp_rigidity import (
    exact_astab_circumradii,
    exact_cyclic_ame_dichotomy,
    exact_megyesi_rqls_prime,
    exact_rains_shadow_qubit,
    exact_symplectic_marginal_bound,
    verify_all_exact,
)
from reference.exact_reference import (
    gurvits_barnum_delta_norm_sq,
    pless_a_k_plus_2_even,
    pless_a_k_plus_2_odd,
)

REPO = pathlib.Path(__file__).resolve().parent.parent
EXE = ".exe" if platform.system() == "Windows" else ""
REQUIRE_ALL_ENGINES = os.environ.get("REQUIRE_ALL_ENGINES", "0") == "1"


def test_pillar1_rains_and_pless_exact():
    feasible = [n for n in range(2, 15) if exact_rains_shadow_qubit(n)["feasible"]]
    assert feasible == [2, 3, 5, 6]
    assert exact_rains_shadow_qubit(4)["S"][0] == Fraction(-1, 2)
    assert exact_rains_shadow_qubit(7)["S"][1] == Fraction(7, 4)
    assert exact_rains_shadow_qubit(9)["S"][1] == Fraction(-9, 4)
    assert exact_rains_shadow_qubit(11)["S"][3] == Fraction(-165, 8)
    for n in range(2, 20):
        assert exact_cyclic_ame_dichotomy(n, 4) == (n in (2, 3, 5, 6))
        assert exact_cyclic_ame_dichotomy(n, 12) == (n in (2, 3, 5, 6))


@given(p=st.sampled_from([2, 3, 5, 7]), delta=st.integers(min_value=0, max_value=8))
@settings(max_examples=40)
def test_pillar1_pless_obstruction_property(p: int, delta: int):
    k_even = p * p + delta
    assert pless_a_k_plus_2_even(k_even, p) < 0
    k_odd = p * p + p + delta
    assert pless_a_k_plus_2_odd(k_odd, p) < 0


def test_pillar2_megyesi_rqls_primes():
    for p in (7, 11, 13, 17, 19, 23):
        r = exact_megyesi_rqls_prime(p)
        assert r["t"] == (p - 5) // 2
        assert r["cardinality"] == p * p
        assert r["maximal_cardinality"] is True


def test_pillar3_astab_circumradii_and_witnesses():
    res = exact_astab_circumradii(80)
    assert res["r2_2qubit_gt_gb"] is True
    assert res["r2_1qutrit_between_inball_and_awp"] is True
    with localcontext() as ctx:
        ctx.prec = 80
        r2_2q = Decimal(res["r2_2qubit_exact"])
        r2_1qt = Decimal(res["r2_1qutrit_exact"])
        # Exact minimal polynomials: (484*R^2 - 39)^2 = 432 and (6*R^2 - 7)^2 = 45
        assert abs((Decimal(484) * r2_2q - Decimal(39)) ** 2 - Decimal(432)) < Decimal("1e-70")
        assert abs((Decimal(6) * r2_1qt - Decimal(7)) ** 2 - Decimal(45)) < Decimal("1e-70")
    assert res["rho_ent_in_astab"] is True
    assert res["rho_ent_entangled_va"] == Fraction(1, 10)
    assert res["rho_sep_in_asep"] is True
    assert res["rho_sep_outside_astab"] is True


@given(d=st.integers(min_value=2, max_value=40))
@settings(max_examples=40)
def test_pillar3_gurvits_barnum_cor3_property(d: int):
    # At exact Zurel-Davis AWP_0 circumradius purity P = 1/(D-1), ||Delta||_2^2 == 1 identically!
    assert gurvits_barnum_delta_norm_sq(d, Fraction(1, d - 1)) == Fraction(1)
    assert gurvits_barnum_delta_norm_sq(d, Fraction(1, d)) < Fraction(1)


@given(n=st.integers(min_value=2, max_value=20))
@settings(max_examples=25)
def test_pillar3_symplectic_marginal_descent_property(n: int):
    b = exact_symplectic_marginal_bound(n)
    assert b["inball_ratio"] == Fraction(15, 7)
    assert b["c_ours"] == Fraction(7 * (4**n) + 8, 15 * (2**n))
    assert b["c_ours"] <= Fraction(2 ** (n - 1))
    assert b["c_ours"] < b["c_liu"]


def test_verify_all_exact_summary():
    out = verify_all_exact()
    assert out["pillar1_ame_feasible"] == [2, 3, 5, 6]
    assert out["pillar2_prime_t"][11] == 3
    assert out["pillar3_smd_ratio"] == "15/7"


def test_repo_yaml_matches_build_standard_v120_schema():
    """Validate repo.yaml against the official Build Standard v1.2.0 Draft 2020-12 JSON Schema."""
    schema_path = REPO / "scripts" / "repo-standard.schema.json"
    repo_yaml_path = REPO / "repo.yaml"
    assert schema_path.exists(), "Missing scripts/repo-standard.schema.json"
    assert repo_yaml_path.exists(), "Missing repo.yaml"
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    data = yaml.safe_load(repo_yaml_path.read_text(encoding="utf-8"))
    jsonschema.Draft202012Validator(schema).validate(data)
    assert data["standard"] == "1.2.0"
    assert data["project_type"] == "research"
    assert data["flags"]["formal"] is True
    assert data["flags"]["visual"] is True


def test_readme_quickstart_python_snippet():
    """Extract and execute the Python Quickstart snippet from README.md to prevent doc drift."""
    readme = (REPO / "README.md").read_text(encoding="utf-8")
    blocks = re.findall(r"```python\n(.*?)```", readme, flags=re.DOTALL)
    assert blocks, "No ```python code block found in README.md"
    snippet = blocks[0]
    assert "exact_symplectic_marginal_bound" in snippet
    ns: dict[str, object] = {}
    exec(compile(snippet, "README.md:quickstart", "exec"), ns, ns)


def test_lean_axioms_artifact_strictly_classical():
    """Verify results/lean_axioms.txt depends strictly on [propext, Classical.choice, Quot.sound]."""
    ax_file = REPO / "results" / "lean_axioms.txt"
    assert ax_file.exists(), "Missing results/lean_axioms.txt"
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    lines = [ln.strip() for ln in ax_file.read_text(encoding="utf-8").splitlines() if ln.strip()]
    assert len(lines) >= 20, f"Unexpectedly few axiom lines: {len(lines)}"
    for ln in lines:
        assert "sorryAx" not in ln and "_native" not in ln, f"Forbidden axiom in {ln}"
        m = re.search(r"depends on axioms:\s*\[([^\]]+)\]", ln)
        if m:
            used = {tok.strip() for tok in m.group(1).split(",") if tok.strip()}
            assert used <= allowed, f"Unauthorized axioms {used - allowed} in {ln}"


def test_differential_rust_cpp_c_zig_eshkol():
    """Cross-language differential verification across Rust, Zig, C++20, C11+NASM, and Eshkol AD."""
    # 1. Eshkol AD (always runnable)
    e_out = subprocess.check_output(
        [sys.executable, str(REPO / "eshkol" / "run_eshkol_ad.py"), "--json"], text=True
    )
    ej = json.loads(e_out)
    assert ej["all_ok"] is True
    assert ej["precision_class"] == "numerical_approximation"
    astab = exact_astab_circumradii(50)
    assert abs(ej["astab_2q"]["val"] - float(astab["r2_2qubit_exact"])) < 1e-13
    assert abs(ej["astab_1qt"]["val"] - float(astab["r2_1qutrit_exact"])) < 1e-13

    # 2. Rust binary
    rust_bin = REPO / "rust" / "target" / "release" / f"qpr-rust{EXE}"
    if REQUIRE_ALL_ENGINES:
        assert rust_bin.exists(), f"REQUIRE_ALL_ENGINES=1 but missing {rust_bin}"
    if rust_bin.exists():
        r_out = subprocess.check_output([str(rust_bin), "--json"], text=True)
        rj = json.loads(r_out)
        assert rj["all_ok"] is True
        assert rj["precision_class"] == "exact_integer_rational"
        assert rj["qubit_ame_feasible_n"] == [2, 3, 5, 6]
        assert rj["lambda2_facet_pairs_checked"] == 1770
        assert rj["lambda2_min_facet_overlap"] == -1
        assert rj["lambda2_cnc_m1_vertex_count"] == 240
        assert rj["lambda2_c2_exact"] == "2/1"
        assert rj["n3_symplectic_4d_subspaces"] == 336
        assert rj["n3_pauli_uniform_cover"] == 80
        assert rj["symplectic_inball_gain"] == "15/7"

    # 3. C++20 cyclotomic binary
    cpp_bin = REPO / "cpp" / "build" / f"qpr_cpp{EXE}"
    if REQUIRE_ALL_ENGINES:
        assert cpp_bin.exists(), f"REQUIRE_ALL_ENGINES=1 but missing {cpp_bin}"
    if cpp_bin.exists():
        p_out = subprocess.check_output([str(cpp_bin), "--json"], text=True)
        pj = json.loads(p_out)
        assert pj["all_ok"] is True
        by_name = {c["name"]: c for c in pj["certificates"]}
        assert by_name["3-RQLS(11)"]["pairs"] == 14641
        assert by_name["3-RQLS(11)"]["collinear_offdiag"] == 0
        assert by_name["3-RQLS(16)"]["pairs"] == 65536

    # 4. C11 + NASM + Moonlab + QGTL binary
    c_bin = REPO / "c" / "build" / f"qpr_c{EXE}"
    if REQUIRE_ALL_ENGINES:
        assert c_bin.exists(), f"REQUIRE_ALL_ENGINES=1 but missing {c_bin}"
    if c_bin.exists():
        c_out = subprocess.check_output([str(c_bin), "--json"], text=True)
        cj = json.loads(c_out)
        assert cj["all_ok"] is True
        assert cj["n4_f2_ame_count"] == 0
        assert cj["prism6_unimodular"] is True
        assert cj["wheel5_unimodular"] is True
        assert cj["qgtl_entangled_astab"]["precision_class"] == "numerical_approximation"
        assert abs(cj["qgtl_entangled_astab"]["g_pp"] - ej["qgtl_gpp"]["val"]) < 1e-8

    # 5. Zig comptime + exhaustive F_8 engine
    zig_bin = REPO / "zig" / "zig-out" / f"qpr_zig{EXE}"
    if REQUIRE_ALL_ENGINES:
        assert zig_bin.exists(), f"REQUIRE_ALL_ENGINES=1 but missing {zig_bin}"
    if zig_bin.exists():
        z_out = subprocess.check_output(
            [str(zig_bin), "--verify-all"], stderr=subprocess.STDOUT, text=True
        )
        assert "nonlin_t>=1=0" in z_out
        assert "F7_nonlin_mc=84" in z_out
        assert "F11:t=3" in z_out
        assert "F16:t=3" in z_out


def test_input_validation_errors():
    with pytest.raises(ValueError):
        exact_rains_shadow_qubit(1)
    with pytest.raises(ValueError):
        exact_megyesi_rqls_prime(8)
    with pytest.raises(ValueError):
        exact_symplectic_marginal_bound(1)
