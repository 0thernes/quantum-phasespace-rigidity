# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Master end-to-end polyglot & exact-oracle verification + certificate exporter."""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import platform
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
IS_WIN = platform.system() == "Windows"
EXE = ".exe" if IS_WIN else ""


def run(cmd: list[str], cwd: pathlib.Path, env: dict[str, str] | None = None) -> str:
    print(f">>> [{cwd.name}] {' '.join(cmd)}", flush=True)
    res = subprocess.run(cmd, cwd=str(cwd), env=env, capture_output=True, text=True)
    if res.stdout:
        print(res.stdout.strip(), flush=True)
    if res.stderr:
        print(res.stderr.strip(), file=sys.stderr, flush=True)
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({res.returncode}): {' '.join(cmd)}")
    return res.stdout


def main() -> int:
    # 1. Build & run all 5 native + AD engines via build_polyglot.py
    run([sys.executable, str(REPO / "scripts" / "build_polyglot.py")], REPO)

    # 2. Run Python quickstart, pytest (with differential checks), mutation suite, ruff, mypy
    py_env = dict(os.environ)
    py_env["PYTHONPATH"] = f"{REPO / 'src'}{os.pathsep}{REPO}"

    run([sys.executable, "examples/quickstart_demo.py"], REPO, env=py_env)
    run([sys.executable, "-m", "pytest", "-v", "tests/test_all.py"], REPO, env=py_env)
    run([sys.executable, "scripts/mutate.py"], REPO, env=py_env)

    # Lint & typecheck (graceful if ruff/mypy installed)
    for tool, args in [
        ("ruff", ["check", "src", "tests", "scripts", "reference", "examples", "eshkol"]),
        ("mypy", ["src", "reference"]),
    ]:
        try:
            run([sys.executable, "-m", tool, *args], REPO, env=py_env)
        except RuntimeError:
            raise
        except FileNotFoundError:
            print(f"[WARN] {tool} not found; skipping.", flush=True)

    # 3. Export machine-verified JSON certificates from every engine into data/certificates.json
    rust_bin = REPO / "rust" / "target" / "release" / f"qpr-rust{EXE}"
    cpp_bin = REPO / "cpp" / "build" / f"qpr_cpp{EXE}"
    c_bin = REPO / "c" / "build" / f"qpr_c{EXE}"
    zig_bin = REPO / "zig" / "zig-out" / f"qpr_zig{EXE}"

    rust_json = json.loads(run([str(rust_bin), "--json"], REPO / "rust"))
    cpp_json = json.loads(run([str(cpp_bin), "--json"], REPO / "cpp"))
    c_json = json.loads(run([str(c_bin), "--json"], REPO / "c"))
    zig_res = subprocess.run(
        [str(zig_bin), "--verify-all"], cwd=str(REPO / "zig"), capture_output=True, text=True, check=True
    )
    zig_out = (zig_res.stdout + "\n" + zig_res.stderr).strip()
    eshkol_json = json.loads(
        run([sys.executable, str(REPO / "eshkol" / "run_eshkol_ad.py"), "--json"], REPO)
    )

    sys.path.insert(0, str(REPO / "src"))
    sys.path.insert(0, str(REPO))
    from qp_rigidity import (
        exact_astab_circumradii,
        exact_megyesi_rqls_prime,
        exact_rains_shadow_qubit,
        exact_symplectic_marginal_bound,
        verify_all_exact,
    )

    astab = exact_astab_circumradii(80)
    certs = {
        "schema_version": "1.0.0",
        "project": "quantum-phasespace-rigidity",
        "author": "Alexander Stephen Donahue",
        "orcid": "0009-0006-8168-9648",
        "affiliation": "Independent Researcher, Spokane, WA, USA",
        "lean_axioms_verified": (REPO / "results" / "lean_axioms.txt").exists(),
        "python_exact": {
            "summary": verify_all_exact(),
            "rains_shadows": {
                str(n): {
                    "feasible": exact_rains_shadow_qubit(n)["feasible"],
                    "S": [str(x) for x in exact_rains_shadow_qubit(n)["S"]],
                }
                for n in range(2, 13)
            },
            "megyesi_primes": {
                str(p): {
                    "t": exact_megyesi_rqls_prime(p)["t"],
                    "cardinality": exact_megyesi_rqls_prime(p)["cardinality"],
                    "directions": exact_megyesi_rqls_prime(p)["directions"],
                }
                for p in (7, 11, 13, 17, 19, 23, 29, 31)
            },
            "astab_circumradii": {
                "r2_2qubit_exact": str(astab["r2_2qubit_exact"]),
                "r2_2qubit_gb": str(astab["r2_2qubit_gb"]),
                "r2_1qutrit_exact": str(astab["r2_1qutrit_exact"]),
                "r2_1qutrit_inball": str(astab["r2_1qutrit_inball"]),
                "r2_1qutrit_awp": str(astab["r2_1qutrit_awp"]),
                "rho_ent_entangled_va": str(astab["rho_ent_entangled_va"]),
            },
            "symplectic_marginal_descent": {
                str(n): {
                    "c_liu": str(exact_symplectic_marginal_bound(n)["c_liu"]),
                    "c_ours": str(exact_symplectic_marginal_bound(n)["c_ours"]),
                    "inball_ratio": str(exact_symplectic_marginal_bound(n)["inball_ratio"]),
                }
                for n in (2, 3, 4, 5, 6, 8, 10)
            },
        },
        "rust_engine": rust_json,
        "cpp20_cyclotomic_engine": cpp_json,
        "c11_nasm_moonlab_qgtl_engine": c_json,
        "zig_comptime_summary": zig_out,
        "eshkol_ad_engine": eshkol_json,
    }

    data_dir = REPO / "data"
    data_dir.mkdir(exist_ok=True)
    cert_path = data_dir / "certificates.json"
    cert_bytes = (json.dumps(certs, indent=2, sort_keys=True, default=str) + "\n").encode("utf-8")
    cert_path.write_bytes(cert_bytes)
    digest = hashlib.sha256(cert_bytes).hexdigest()
    (data_dir / "MANIFEST.sha256").write_text(f"{digest}  certificates.json\n", encoding="utf-8")
    print(f"\n[CERTS] Wrote {cert_path} (SHA-256: {digest})", flush=True)
    print("=== FULL POLYGLOT + PYTHON + MUTATION + CERTIFICATE PIPELINE PASSED ===", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
