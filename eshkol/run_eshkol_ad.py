# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Deterministic Eshkol Lisp/Scheme S-expression evaluator for forward-mode dual-number AD.

Parses and executes `eshkol/astab_kkt_ad.esk` and `eshkol/qgtl_trajectory_ad.esk` directly
and cross-checks dual values and analytical gradients against Lean 4 exact closed forms.
"""
from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any


def tokenize(src: str) -> list[str]:
    lines = [line.split(";", 1)[0] for line in src.splitlines()]
    text = " ".join(lines).replace("(", " ( ").replace(")", " ) ")
    return text.split()


def parse_all(tokens: list[str]) -> list[Any]:
    pos = 0

    def parse_one() -> Any:
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok == "(":
            lst = []
            while tokens[pos] != ")":
                lst.append(parse_one())
            pos += 1
            return lst
        try:
            return int(tok)
        except ValueError:
            try:
                return float(tok)
            except ValueError:
                return tok

    exprs = []
    while pos < len(tokens):
        exprs.append(parse_one())
    return exprs


class Closure:
    def __init__(self, params: list[str], body: list[Any], env: dict[str, Any]):
        self.params = params
        self.body = body
        self.env = env


def make_base_env() -> dict[str, Any]:
    return {
        "+": lambda a, b: a + b,
        "-": lambda a, b: a - b,
        "*": lambda a, b: a * b,
        "/": lambda a, b: a / b,
        "sqrt": math.sqrt,
        "sin": math.sin,
        "cos": math.cos,
        "cons": lambda a, b: (a, b),
        "car": lambda p: p[0],
        "cdr": lambda p: p[1],
    }


def eval_expr(expr: Any, env: dict[str, Any]) -> Any:
    if isinstance(expr, (int, float)):
        return float(expr)
    if isinstance(expr, str):
        return env[expr]
    head = expr[0]
    if head == "define":
        target = expr[1]
        if isinstance(target, list):
            fn_name = target[0]
            params = target[1:]
            env[fn_name] = Closure(params, expr[2:], env)
            return None
        val = eval_expr(expr[2], env)
        env[target] = val
        return val
    if head == "let":
        bindings = expr[1]
        child = dict(env)
        for name, rhs in bindings:
            child[name] = eval_expr(rhs, env)
        res = None
        for b in expr[2:]:
            res = eval_expr(b, child)
        return res
    fn = eval_expr(head, env)
    args = [eval_expr(a, env) for a in expr[1:]]
    if isinstance(fn, Closure):
        child = dict(fn.env)
        for p, v in zip(fn.params, args, strict=True):
            child[p] = v
        res = None
        for b in fn.body:
            res = eval_expr(b, child)
        return res
    return fn(*args)


def run_file(path: pathlib.Path) -> dict[str, Any]:
    env = make_base_env()
    for expr in parse_all(tokenize(path.read_text(encoding="utf-8"))):
        eval_expr(expr, env)
    return env


def main() -> int:
    here = pathlib.Path(__file__).resolve().parent
    json_mode = "--json" in sys.argv

    env1 = run_file(here / "astab_kkt_ad.esk")
    r2_2q_val, r2_2q_der = env1["res-2q"]
    r2_1qt_val, r2_1qt_der = env1["res-1qt"]

    # Exact Lean-proved closed forms
    exact_2q = 3.0 * (13.0 + 4.0 * math.sqrt(3.0)) / 484.0
    exact_2q_der = (8.0 / 3.0) * ((7.0 + 3.0 * math.sqrt(3.0)) / 22.0) - (2.0 / 3.0)
    exact_1qt = (7.0 - 3.0 * math.sqrt(5.0)) / 6.0
    beta = 0.5 * (3.0 - math.sqrt(5.0))
    exact_1qt_der = 2.0 * 0.5 - 2.0 * (1.0 + beta) * (1.0 - (1.0 + beta) * 0.5) + 2.0 * beta * beta * 0.5

    env2 = run_file(here / "qgtl_trajectory_ad.esk")
    gpp_val, gpp_der = env2["res-qgtl"]
    theta = 1.1
    w = 0.55 * (math.sin(0.5 * theta) ** 2) + 0.15
    dw = 0.55 * 0.5 * math.sin(theta)
    exact_gpp = w * (1.0 - w)
    exact_gpp_der = (1.0 - 2.0 * w) * dw

    err_2q = max(abs(r2_2q_val - exact_2q), abs(r2_2q_der - exact_2q_der))
    err_1qt = max(abs(r2_1qt_val - exact_1qt), abs(r2_1qt_der - exact_1qt_der))
    err_qgtl = max(abs(gpp_val - exact_gpp), abs(gpp_der - exact_gpp_der))
    all_ok = (
        (err_2q < 1e-13)
        and (err_1qt < 1e-13)
        and (err_qgtl < 1e-13)
        and (r2_2q_der > 0)
        and (r2_1qt_der > 0)
    )

    report = {
        "engine": "eshkol-dual-ad",
        "astab_2q": {"val": r2_2q_val, "grad": r2_2q_der, "exact": exact_2q, "err": err_2q},
        "astab_1qt": {"val": r2_1qt_val, "grad": r2_1qt_der, "exact": exact_1qt, "err": err_1qt},
        "qgtl_gpp": {"val": gpp_val, "grad": gpp_der, "exact": exact_gpp, "err": err_qgtl},
        "all_ok": all_ok,
    }
    if json_mode:
        print(json.dumps(report, indent=2))
    else:
        print(
            f"[Eshkol Dual-AD] 2q R^2={r2_2q_val:.12f} (grad={r2_2q_der:+.9f}, err={err_2q:.2e}) | "
            f"1qt R^2={r2_1qt_val:.12f} (grad={r2_1qt_der:+.9f}, err={err_1qt:.2e}) | "
            f"QGTL g_pp={gpp_val:.12f} (grad={gpp_der:+.9f}, err={err_qgtl:.2e}) | all_ok={all_ok}"
        )
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
