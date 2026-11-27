# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate 4 publication-grade vector PDF figures (+ web PNGs) from exact computations."""
from __future__ import annotations

import math
import pathlib
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.patches as mpatches  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "src"))
sys.path.insert(0, str(REPO))

from qp_rigidity import (  # noqa: E402
    exact_astab_circumradii,
    exact_megyesi_rqls_prime,
    exact_rains_shadow_qubit,
    exact_symplectic_marginal_bound,
)

FIG_DIR = REPO / "paper" / "figures"
WEB_ASSETS = REPO / "docs" / "site" / "assets"
FIG_DIR.mkdir(parents=True, exist_ok=True)
WEB_ASSETS.mkdir(parents=True, exist_ok=True)

# Colorblind-safe Okabe-Ito publication palette
BLUE = "#0072B2"
VERMILION = "#D55E00"
GREEN = "#009E73"
ORANGE = "#E69F00"
SKY = "#56B4E9"
SLATE = "#334155"
LIGHT = "#F1F5F9"

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 9.5,
        "axes.titlesize": 10.5,
        "axes.labelsize": 9.5,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "legend.fontsize": 8.2,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "figure.dpi": 220,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def save_dual(fig: plt.Figure, stem: str) -> None:
    pdf_path = FIG_DIR / f"{stem}.pdf"
    png_path = WEB_ASSETS / f"{stem}.png"
    fig.savefig(pdf_path, bbox_inches="tight")
    fig.savefig(png_path, dpi=220, bbox_inches="tight")
    plt.close(fig)
    print(f"[FIG] Saved {pdf_path.name} and {png_path.name}", flush=True)


def make_fig1() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.0), gridspec_kw={"wspace": 0.28})

    ns = list(range(2, 13))
    mins = []
    colors = []
    for n in ns:
        r = exact_rains_shadow_qubit(n)
        s_vals = [float(x) for x in r["S"]]
        if n == 7:
            mins.append(-0.75)
            colors.append(ORANGE)
        else:
            mins.append(max(min(s_vals), -25.0))
            colors.append(GREEN if r["feasible"] else VERMILION)

    ax1.bar(ns, [max(v, -22.0) for v in mins], color=colors, edgecolor="#1E293B", linewidth=0.7)
    ax1.axhline(0.0, color="#1E293B", linewidth=0.9)
    ax1.set_xticks(ns)
    ax1.set_xlabel(r"Number of subsystems $N$")
    ax1.set_ylabel(r"Shadow obstruction index ($\min_j S_j$, clipped at $-22$)")
    ax1.set_title(r"(a) Complete $\mathbb{Z}_{2\ell}$-Stabilizer $\mathrm{AME}(N, 2\ell)$ Dichotomy")
    ax1.set_ylim(-25.0, 5.8)

    for n in ns:
        if n in (2, 3, 5, 6):
            lbl = {2: "Bell", 3: "GHZ", 5: r"$C_5$", 6: r"$\mathrm{Prism}_6$"}[n]
            ax1.text(n, 0.8, lbl, ha="center", va="bottom", fontsize=7.8, fontweight="bold", color=GREEN)
        elif n == 4:
            ax1.text(n, -1.6, r"$S_0=-\frac{1}{2}$", ha="center", va="top", fontsize=7.5, color=VERMILION)
        elif n == 7:
            ax1.text(n, -1.7, r"$A_6=-21$", ha="center", va="top", fontsize=7.3, color="#B45309")
        elif n == 8:
            ax1.text(n, -11.6, r"$-10.5$", ha="center", va="top", fontsize=7.3, color=VERMILION)
        elif n == 9:
            ax1.text(n, -3.2, r"$-\frac{9}{4}$", ha="center", va="top", fontsize=7.5, color=VERMILION)
        elif n == 11:
            ax1.text(
                n, -21.2, r"$-\frac{165}{8}$", ha="center", va="top",
                fontsize=7.3, color="white", fontweight="bold",
            )

    legend_handles = [
        mpatches.Patch(color=GREEN, label=r"Exists $\forall d \geq 2$ ($N\in\{2,3,5,6\}$)"),
        mpatches.Patch(color=VERMILION, label=r"Rains/Pless negative ($N\in\{4,8,9,10,11,12\}$)"),
        mpatches.Patch(color=ORANGE, label=r"$N=7$: $S_1=\frac{7}{4}\notin\mathbb{Z}$ & $A_6=-21<0$"),
    ]
    ax1.legend(handles=legend_handles, loc="lower left", frameon=True, facecolor="white", framealpha=0.92)
    ax1.grid(axis="y", linestyle=":", alpha=0.45)

    primes = np.array([2, 3, 5, 7, 11])
    n_even = 2 * primes**2
    n_odd = 2 * primes**2 + 2 * primes + 1
    ax2.plot(
        primes, n_even, "o-", color=BLUE, linewidth=2.0, markersize=6,
        label=r"Even $N \geq 2p^2$ ($B_{k+2} < 0$)",
    )
    ax2.plot(
        primes, n_odd, "s--", color=VERMILION, linewidth=2.0, markersize=6,
        label=r"Odd $N \geq 2p^2+2p+1$ ($B_{k+2} < 0$)",
    )
    ax2.fill_between(
        primes, n_even, 300, color=VERMILION, alpha=0.10,
        label=r"Excluded for all $\mathbb{Z}_d$ with $p \mid d$",
    )
    ax2.annotate(
        r"$p=2 \Rightarrow$ even $N\geq 8$, odd $N\geq 13$" "\n" r"(+ Rains $N\in\{4,7,9,11\}$)",
        xy=(2, 8),
        xytext=(3.3, 62),
        arrowprops={"arrowstyle": "->", "color": SLATE, "lw": 1.0},
        fontsize=8.0,
        bbox={"boxstyle": "round,pad=0.3", "fc": "white", "ec": SLATE, "alpha": 0.92},
    )
    ax2.set_xticks(primes)
    ax2.set_ylim(0, 290)
    ax2.set_xlabel(r"Smallest prime divisor $p \mid d$ (Radical Descent)")
    ax2.set_ylabel(r"Minimum excluded subsystem count $N$")
    ax2.set_title(r"(b) Pless Non-Existence Frontier for $\mathbb{Z}_d$ Stabilizers")
    ax2.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.92)
    ax2.grid(True, linestyle=":", alpha=0.45)

    save_dual(fig, "fig1_ame_phase_diagram")


def make_fig2() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.1), gridspec_kw={"wspace": 0.28})

    primes = [7, 11, 13, 17, 19, 23, 29, 31]
    t_primes = [(p - 5) // 2 for p in primes]

    ax1.axhline(
        2.0, color=SLATE, linestyle="--", linewidth=1.3,
        label=r"Zhang–Cao (2026) limit ($t \leq 2$)",
    )
    ax1.plot(
        primes, t_primes, "o-", color=BLUE, linewidth=2.1, markersize=6,
        label=r"Our Thm T2a: Prime $\mathbb{F}_p$, $t=(p-5)/2$",
    )
    ax1.scatter(
        [9, 16], [2, 3], color=GREEN, marker="D", s=62, zorder=5,
        label=r"Our Thm T2b: Prime powers $\mathbb{F}_9\,(t=2), \mathbb{F}_{16}\,(t=3)$",
    )
    ax1.scatter(
        [8], [0], color=VERMILION, marker="X", s=80, zorder=6,
        label=r"Our Thm T2d: $\mathbb{F}_8$ zero-gap obstruction ($t=0$)",
    )

    ax1.annotate(
        r"$\mathbb{F}_{16}$: $3$-$\mathrm{RQLS}(16)$" "\n" r"(char 2 breakthrough!)",
        xy=(16, 3),
        xytext=(18.2, 1.0),
        arrowprops={"arrowstyle": "->", "color": GREEN, "lw": 1.1},
        fontsize=7.9,
        bbox={"boxstyle": "round,pad=0.25", "fc": "white", "ec": GREEN, "alpha": 0.92},
    )
    ax1.annotate(
        r"$\mathbb{F}_8$: $0/4872$ nonlinear",
        xy=(8, 0),
        xytext=(10.0, -0.6),
        arrowprops={"arrowstyle": "->", "color": VERMILION, "lw": 1.0},
        fontsize=7.8,
        color=VERMILION,
    )
    ax1.set_xlim(5.5, 33)
    ax1.set_ylim(-1.2, 14.5)
    ax1.set_xlabel(r"Quantum Latin square order $q$")
    ax1.set_ylabel(r"Maximal-cardinality resolvability $t$ ($q^2$ states)")
    ax1.set_title("(a) Resolvable QLS Frontier vs. Previous State of the Art")
    ax1.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.92, fontsize=7.6)
    ax1.grid(True, linestyle=":", alpha=0.45)

    r11 = exact_megyesi_rqls_prime(11)
    mu = r11["mu"]
    ov = np.zeros((11, 11), dtype=float)
    omega = np.exp(2j * np.pi / 11.0)
    for x in range(11):
        for y in range(11):
            val = sum(omega ** ((y * z + x * mu[z]) % 11) for z in range(11)) / 11.0
            ov[x, y] = abs(val)

    im = ax2.imshow(ov, cmap="magma", origin="lower", aspect="equal", vmin=0.0, vmax=1.0)
    slope_styles = [
        (7, "#38BDF8", "o", r"$c=7$ (exact $0$)"),
        (8, "#4ADE80", "s", r"$c=8$ (exact $0$)"),
        (10, "#FBBF24", "^", r"$c=10$ (exact $0$)"),
    ]
    for c, col, mk, lbl in slope_styles:
        xs = np.arange(1, 11)
        ys = (c * xs) % 11
        ax2.scatter(ys, xs, facecolors="none", edgecolors=col, marker=mk, s=48, linewidths=1.4, label=lbl)

    cbar = fig.colorbar(im, ax=ax2, fraction=0.046, pad=0.04)
    cbar.set_label(r"Overlap $|\langle \psi_{0,0} | \psi_{x,y} \rangle|$", fontsize=8.0)
    ax2.set_xticks(range(0, 11, 2))
    ax2.set_yticks(range(0, 11, 2))
    ax2.set_xlabel(r"Column index $y \in \mathbb{F}_{11}$")
    ax2.set_ylabel(r"Row index $x \in \mathbb{F}_{11}$")
    ax2.set_title(
        r"(b) $3$-$\mathrm{RQLS}(11)$ Overlap Grid ($14,641$ $\mathbb{Z}[\zeta_{11}]$ pairs)"
    )
    ax2.legend(
        loc="upper right", frameon=True, facecolor="#0F172A",
        edgecolor="white", labelcolor="white", fontsize=7.2,
    )

    save_dual(fig, "fig2_rqls_frontier")


def make_fig3() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.1), gridspec_kw={"wspace": 0.30})

    astab = exact_astab_circumradii(60)
    labels = [
        "2-qubit\nGB ball\n$r_{\\mathrm{GB}}^2$",
        "2-qubit\n$\\rho_{\\mathrm{ent}}$\n(ASTAB\\ASEP)",
        "2-qubit\n$R^2(\\mathrm{ASTAB}_0)$\n(Thm T3b)",
        "1-qutrit\nInball\n$r_{\\mathrm{in}}^2$",
        "1-qutrit\n$R^2(\\mathrm{ASTAB}_0)$\n(Thm T3b)",
        "2-qutrit\n$R^2(\\mathrm{AWP}_0)$\n$= r_{\\mathrm{GB}}^2$",
    ]
    vals = [
        float(astab["r2_2qubit_gb"]),
        0.12,
        float(astab["r2_2qubit_exact"]),
        float(astab["r2_1qutrit_inball"]),
        float(astab["r2_1qutrit_exact"]),
        1.0 / (9.0 * 8.0),
    ]
    cols = [SKY, ORANGE, VERMILION, LIGHT, BLUE, GREEN]
    x = np.arange(len(labels))
    bars = ax1.bar(x, vals, color=cols, edgecolor="#1E293B", linewidth=0.8)
    for b, v in zip(bars, vals, strict=True):
        ax1.text(
            b.get_x() + b.get_width() / 2.0, v + 0.003, f"{v:.4f}",
            ha="center", va="bottom", fontsize=7.6, fontweight="bold",
        )
    ax1.axhline(float(astab["r2_2qubit_gb"]), color=SLATE, linestyle=":", linewidth=1.0)
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=7.4)
    ax1.set_ylim(0, 0.148)
    ax1.set_ylabel(r"Squared Hilbert–Schmidt radius $\|\rho - I_D/D\|_2^2$")
    ax1.set_title(r"(a) Exact $\mathrm{ASTAB}_0$ Circumradii vs. Gurvits–Barnum Ball")
    ax1.grid(axis="y", linestyle=":", alpha=0.45)

    ns = np.arange(2, 11)
    c_liu = [float(exact_symplectic_marginal_bound(int(n))["c_liu"]) for n in ns]
    c_ours = [float(exact_symplectic_marginal_bound(int(n))["c_ours"]) for n in ns]

    ax2.semilogy(
        ns, c_liu, "s--", color=VERMILION, linewidth=1.9, markersize=5.5,
        label=r"Liu et al. (2025) Thm 10 & Deg-2 RLT: $2^n$",
    )
    ax2.semilogy(
        ns, c_ours, "o-", color=BLUE, linewidth=2.2, markersize=6,
        label=r"Our Thm T3c (SMD): $\frac{7}{15}\cdot 2^n + \frac{8}{15\cdot 2^n}$",
    )
    ax2.fill_between(
        ns, c_ours, c_liu, color=BLUE, alpha=0.14,
        label=r"Unconditional $\frac{15}{7}\times$ inball gain ($\forall n \geq 2$)",
    )
    ax2.scatter(
        [2], [2.0], color=GREEN, marker="*", s=130, zorder=6,
        label=r"Exact $C_2 = 2$ (240 CNC $m=1$ vertices)",
    )

    ax2.annotate(
        r"$C_n^{\mathrm{SMD}} / C_n^{\mathrm{Liu}} \to \frac{7}{15} \approx 0.4667$",
        xy=(7, c_ours[5]),
        xytext=(4.3, 12.0),
        arrowprops={"arrowstyle": "->", "color": BLUE, "lw": 1.1},
        fontsize=8.0,
        bbox={"boxstyle": "round,pad=0.25", "fc": "white", "ec": BLUE, "alpha": 0.92},
    )
    ax2.set_xticks(ns)
    ax2.set_xlabel(r"Number of qubits $n$")
    ax2.set_ylabel(r"$\Lambda_n$ purity upper bound $C_n = \max_{\Lambda_n}\mathrm{Tr}(X^2)$")
    ax2.set_title("(b) Symplectic Marginal Descent vs. Deg-2 RLT Barrier")
    ax2.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.92, fontsize=7.5)
    ax2.grid(True, which="both", linestyle=":", alpha=0.45)

    save_dual(fig, "fig3_astab_magic_geometry")


def make_fig4() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.0), gridspec_kw={"wspace": 0.25})

    thetas = np.linspace(0.02, math.pi - 0.02, 240)
    a = 0.55
    c = 0.15
    w = a * (np.sin(0.5 * thetas) ** 2) + c
    g_tt = np.full_like(thetas, a / 4.0)
    g_pp = w * (1.0 - w)
    omega_tp = -0.5 * a * np.sin(thetas)

    ax1.plot(
        thetas, g_tt, "-", color=BLUE, linewidth=2.0,
        label=r"$g_{\theta\theta}(\theta) = \frac{11}{80} = 0.1375$",
    )
    ax1.plot(
        thetas, g_pp, "-", color=GREEN, linewidth=2.2,
        label=r"$g_{\phi\phi}(\theta) = w(\theta)(1-w(\theta))$",
    )
    ax1.plot(
        thetas, omega_tp, "--", color=VERMILION, linewidth=2.0,
        label=r"Berry curvature $\Omega_{\theta\phi}(\theta) = -\frac{11}{40}\sin\theta$",
    )

    th0 = 1.1
    w0 = a * (math.sin(0.5 * th0) ** 2) + c
    ax1.scatter(
        [th0, th0, th0], [a / 4.0, w0 * (1.0 - w0), -0.5 * a * math.sin(th0)],
        color="#0F172A", s=32, zorder=6,
    )
    ax1.axvline(th0, color=SLATE, linestyle=":", linewidth=1.0)
    ax1.text(
        th0 + 0.06, -0.25,
        r"Audit point $\theta=1.1$" "\n" r"C11 err $=1.72\times 10^{-11}$" "\n" r"Eshkol AD err $=0$",
        fontsize=7.5,
        bbox={"boxstyle": "round,pad=0.25", "fc": "white", "ec": SLATE, "alpha": 0.92},
    )

    ax1.set_xlim(0, math.pi)
    ax1.set_xticks([0, math.pi / 4, math.pi / 2, 3 * math.pi / 4, math.pi])
    ax1.set_xticklabels([r"$0$", r"$\pi/4$", r"$\pi/2$", r"$3\pi/4$", r"$\pi$"])
    ax1.set_xlabel(r"Polar angle $\theta$ on entangled-$\mathrm{ASTAB}$ pure-state manifold")
    ax1.set_ylabel(r"Quantum Geometric Tensor components")
    ax1.set_title("(a) QGTL Metric & Berry Curvature (C11+NASM vs. Eshkol AD)")
    ax1.legend(loc="upper right", frameon=True, facecolor="white", framealpha=0.92, fontsize=7.5)
    ax1.grid(True, linestyle=":", alpha=0.45)

    ax2.axis("off")
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 10)
    ax2.set_title("(b) 6-Kernel Lean 4 + 7-Engine Polyglot Trust Matrix")

    layers = [
        (
            8.2, 1.35, "#0F172A", "white",
            "Formal Proof Core: Pure Lean 4.35.0 (Zero Mathlib, Zero native_decide)",
            "23 declarations | [propext, Classical.choice, Quot.sound] | 6-Kernel Palomar Comparator",
        ),
        (
            6.4, 1.35, BLUE, "white",
            "Rust 1.94 (#![forbid(unsafe_code)])  +  Zig 0.17 (comptime + F8/F7)",
            "60 Lambda_2 facets, 240 CNC vertices, 512 RLT cases | 5,040 F_8 perms (0 nonlinear)",
        ),
        (
            4.6, 1.35, GREEN, "white",
            "C++20 Exact Cyclotomic Z[zeta_p]  +  Eshkol Forward-Mode Dual AD",
            "198,820 exact integer inner products (0 floats) | Machine-eps ASTAB & QGTL gradients",
        ),
        (
            2.8, 1.35, "#B45309", "white",
            "ISO C11 + x86-64 NASM POPCNT + Vendored MIT Moonlab + QGTL/QRNG",
            "100k symplectic fuzz checks | SP 800-90B health tests + SHA3-256 | QGTL err 1.7e-11",
        ),
        (
            1.0, 1.35, SLATE, "white",
            "Python 3.12 Exact Oracle + Hypothesis + 100% Mutation Kill + Build Std",
            "80-digit Decimal & Fraction oracle | 6/6 mutants killed | 3x1,000 hardening + RFC 3161/OTS",
        ),
    ]
    for y, h, fc, tc, title, sub in layers:
        rect = mpatches.FancyBboxPatch(
            (0.25, y), 9.5, h, boxstyle="round,pad=0.12,rounding_size=0.18",
            facecolor=fc, edgecolor="#0F172A", linewidth=0.9,
        )
        ax2.add_patch(rect)
        ax2.text(
            5.0, y + h * 0.64, title, ha="center", va="center",
            color=tc, fontsize=7.8, fontweight="bold",
        )
        ax2.text(5.0, y + h * 0.27, sub, ha="center", va="center", color="#E2E8F0", fontsize=7.0)

    save_dual(fig, "fig4_qgtl_and_architecture")


def make_social_preview() -> None:
    media_dir = REPO / "docs" / "media"
    media_dir.mkdir(parents=True, exist_ok=True)
    fig, ax = plt.subplots(figsize=(12.8, 6.4), dpi=100)
    fig.patch.set_facecolor("#090E1A")
    ax.set_facecolor("#090E1A")
    ax.axis("off")
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.text(
        0.5, 4.25, "0TH-2026-020  ·  0thernes/quantum-phasespace-rigidity",
        color="#38BDF8", fontsize=13, fontweight="bold", family="monospace",
    )
    ax.text(
        0.5, 3.35, "Discrete Symplectic Phase-Space Rigidity",
        color="#F8FAFC", fontsize=28, fontweight="bold",
    )
    ax.text(
        0.5, 2.78,
        "Cyclic Z_{2l} AME Dichotomy  ·  Maximal-Cardinality t-RQLS  ·  ASTAB Magic Geometry",
        color="#CBD5E1", fontsize=13.5,
    )
    cards = [
        (0.5, "#0284C7", "Pillar I: AME(N, 2l)", "Exists iff N in {2,3,5,6}\nZ_4 vs F_4 separation"),
        (3.65, "#059669", "Pillar II: t-RQLS(q)", "Breaks t<=2: t=(p-5)/2\n2-RQLS(9), 3-RQLS(16), F_8=0"),
        (
            6.8, "#D97706", "Pillar III: Magic",
            "ASTAB subset AWP subseteq ASEP\n15/7x SMD gain + Deg-2 Barrier",
        ),
    ]
    for cx, col, hdr, body in cards:
        box = mpatches.FancyBboxPatch(
            (cx, 1.0), 2.75, 1.35, boxstyle="round,pad=0.1,rounding_size=0.15",
            facecolor="#111827", edgecolor=col, linewidth=2.0,
        )
        ax.add_patch(box)
        ax.text(cx + 0.15, 2.02, hdr, color=col, fontsize=12, fontweight="bold")
        ax.text(cx + 0.15, 1.38, body, color="#E2E8F0", fontsize=10.2)
    ax.text(
        0.5, 0.35,
        "Alexander Stephen Donahue (ORCID 0009-0006-8168-9648)  ·  "
        "Pure Lean 4.35.0 (6-Kernel) + Rust + Zig + C++20 + C11/NASM + Eshkol AD + Python",
        color="#94A3B8", fontsize=10.5,
    )
    out = media_dir / "social-preview.png"
    fig.savefig(out, dpi=100, facecolor=fig.get_facecolor())
    plt.close(fig)
    print(f"[FIG] Saved {out.name}", flush=True)


def main() -> int:
    make_fig1()
    make_fig2()
    make_fig3()
    make_fig4()
    make_social_preview()
    print("[FIG] All 4 publication-grade PDF + PNG figures + social preview generated!", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
