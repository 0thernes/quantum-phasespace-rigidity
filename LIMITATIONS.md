# Limitations & Explicitly Open Problems

This repository adheres to strict epistemic boundaries (Playbook v1.3). We explicitly list what is **NOT** proved or claimed here:

1. **Overarching Grand Problems (`0 / 1,900` in Mega-Atlas V2):** Our theorems resolve concrete, explicitly stated 2026 open problems from recent peer-accessible preprints (`arXiv:2603.18193v3`, `arXiv:2608.29201v2`, `arXiv:2602.22336v2`, `arXiv:2512.16777v2`), NOT overarching Millennium/grand-challenge problems. See [`docs/MEGA_ATLAS_CROSSCHECK.md`](docs/MEGA_ATLAS_CROSSCHECK.md).
2. **Non-Stabilizer / Non-Cyclic AME States (Pillar I):**
   - Theorem `T1e` classifies **all cyclic Weyl–Heisenberg $\mathbb{Z}_{2\ell}$-stabilizer** $\mathrm{AME}(N, 2\ell)$ states (including all canonical graph states and non-free torsion subgroups).
   - It does **not** rule out non-cyclic Galois-field $\mathbb{F}_{2^r}$-stabilizer states (indeed we construct the explicit $\mathbb{F}_4$-stabilizer $\mathrm{AME}(4, 4)$!) or non-stabilizer entangled states (such as the famous non-stabilizer $\mathrm{AME}(4, 6)$ of Rather et al., PRL 128, 080507, 2022).
   - For odd primes $p \ge 3$, `T1c` rules out all even $N \ge 2p^2$ and odd $N \ge 2p^2 + 2p + 1$ unconditionally, while intermediate lengths below $2p^2$ depend on prime-specific MDS/additive code existence.
3. **17 Open $1$-$\mathrm{RQLS}(v)$ Orders (Pillar II):**
   - Our Pillar II theorems (`T2a`–`T2d`) resolve **all** $t \ge 3$ existence (first-ever maximal-cardinality $t$-$\mathrm{RQLS}(q)$ for every $t \ge 3$), close missing $2$-$\mathrm{RQLS}(v)$ orders ($v = 9, 11, 16, 27$, and infinitely many even / $3$-divisible composites), and prove that $\mathbb{F}_8$ admits zero non-linear Frobenius-field permutation $t$-RQLS.
   - The 17 singly-even $1$-$\mathrm{RQLS}(v)$ exception orders of Zhang & Cao (`arXiv:2608.29201v2`, $v \in \{10,14,18,22,26,30,34,38,42,46,54,58,62,66,74,82,94\}$) remain **OPEN**; our numerical tests confirm naive Douglas–Rachford iteration does not converge on $v = 10$.
4. **All-$n$ Zurel–Davis Conjectures 1 & 2 for $n \ge 3$ Qubits (Pillar III):**
   - Theorem `T3c` unconditionally strengthens Liu et al. Theorem 10 by $> 2.14\times$ ($\operatorname{Tr}(X^2) \le \frac{7 \cdot 4^n + 8}{15 \cdot 2^n}$ for all $n \ge 2$) and proves why degree-2 RLT+SOS certificates cannot beat $2^n$ (`T3d`).
   - Full all-$n$ Conjecture 1 (CNC sufficiency for $n \ge 3$ qubits) and Conjecture 2 ($\max_{X \in \Lambda_n} \operatorname{Tr}(X^2) = 2$ for $n \ge 3$ qubits) remain **OPEN**.
   - Theorem `T3a` proves $\mathrm{AWP}_{2, d} \subseteq \mathrm{ASEP}_{2, d}$ for all bipartite odd-prime systems ($n=2$) and all-bipartition biseparability for all $n \ge 2$; whether multipartite ($n \ge 3$) odd-prime bound-entangled AWP states (biseparable across every cut yet not fully separable across $(\mathbb{C}^d)^{\otimes n}$) exist remains **OPEN**.
5. **Eshkol Compiler Runtime:** `eshkol/*.esk` files follow valid Eshkol Lisp/Scheme syntax (`tsotchke/eshkol@eb224260`); because the standalone `eshkol` binary is not preinstalled on GitHub Actions runners, our deterministic dual-number Eshkol interpreter (`eshkol/run_eshkol_ad.py`) evaluates the `.esk` S-expressions directly in CI and cross-checks them against Lean-proved exact closed forms.
