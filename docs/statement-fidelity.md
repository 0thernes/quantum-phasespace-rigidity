<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Lean 4 Statement-Fidelity Audit

This document audits the exact semantic correspondence between every mathematical theorem stated in [`paper/main.tex`](../paper/main.tex) and its machine-checked type in [`lean/PalomarChallenge.lean`](../lean/PalomarChallenge.lean) / [`lean/PalomarSolution.lean`](../lean/PalomarSolution.lean).

## Anti-Gaming & Non-Vacuity Controls

1. **Zero `sorry` / `admit` / `native_decide` / custom axioms** in `PalomarSolution.lean` and all imported modules (enforced by `lake env lean VerifyAxioms.lean`, `lake env leanchecker-paranoid --fresh PalomarSolution`, and 6-kernel `lake comparator --paranoid`).
2. **Non-Vacuity Witnesses (`lean/QPRigidity/NonVacuity.lean`):**
   - `nonvacuity_pillar1_ame`: Inhabits `IsAMEGraph 12 graphPrism6`, `IsAMEGraph 6 graphC5`, `PlessEvenSpec 3 2` ($A = [1,0,0,0,45,0,18]$), and `PlessOddSpec 2 2` ($A = [1,0,0,10,15,6]$).
   - `nonvacuity_pillar2_rqls55`: Instantiates `ResolvableQLSSpec 11 3` from `mu11` and `ClassicalMOLSRes 5 3` over $\mathbb{F}_5$, lifted by `direct_product_rqls_lifting` to `ResolvableQLSSpec 55 3`.
   - `nonvacuity_pillar3_magic`: Inhabits `gurvits_barnum_cor3_identity` ($D=9, P=1/8$), `symplectic_marginal_descent_all_n` ($n=3$), and `clifford_reynolds_deg2_rlt_barrier` ($n=2, M=15$).
3. **Adversarial Boundary Refutations (`lean/QPRigidity/AdversarialTests.lean`):**
   - `refute_path5_ame`: Proves path graph $P_5$ is NOT `IsAMEGraph 2` (ruling out degenerate graph predicates).
   - `refute_pless_even_n8_p2` & `refute_pless_odd_n13_p2`: Confirms Pless inequalities fail immediately at the exact threshold $N=8$ (even) and $N=13$ (odd).
   - `refute_f8_swap67_direction`: Refutes a concrete nonlinear transposition on $\mathbb{F}_8$.
   - `refute_deg2_rlt_conjecture2_n2`: Proves degree-2 RLT cannot certify $M = 14 < 15$ at $n=2$.
   - `refute_2qubit_astab_in_gb_ball`: Axiom-free proof (`does not depend on any axioms`) that $R^2(\mathrm{ASTAB}_{2,2}) > 1/12$.

## Line-by-Line Theorem Fidelity Map

| Paper Theorem | Lean Declaration | Formally Certified Inside Kernel | Explicit Paper / Polyglot Bridge |
| :--- | :--- | :--- | :--- |
| **T1a** | `prove_t1a` | `radical_divisor_descent`, `prime_power_kuniform_ascent`, `crt_coprime_kuniform_lift`, `universal_unimodular_graphs_all_d` (all 20 $3\times 3$ minors of `Prism_6` & `W_5` in $\{\pm 1\}$) | Standard Helwig (2013) equivalence between graph-state $k$-uniformity and right-invertibility of cross-adjacency blocks $\Gamma_{A,B} \bmod d$. |
| **T1b** | `prove_t1b` | `pless_even_obstruction` ($N=2k \ge 2p^2$), `pless_odd_obstruction` ($N=2k+1 \ge 2p^2+2p+1$) | Quantum MacWilliams / Pless power-moment equations for $\mathbb{F}_p$-stabilizer codes. |
| **T1c** | `prove_t1c` | `f2_commuting_weight_additive`, `rains_shadow_no_ame{4,7,9,11}`, `no_canonical_graph_ame4_f2` (0/64) | Exact Rains (1999) shadow enumerator integrality & non-negativity for qubit stabilizer codes; cross-checked in Rust, C11+NASM, Python. |
| **T1d** | `prove_t1d` | `torsion_rank_lower_and_free`, `additive_mds_n7_impossible` ($A_6 = -21 < 0$), `additive_mds_odd_ge9_impossible` ($B_{k+2} < 0$) | Finite abelian $2$-Sylow invariant-factor structure forcing $\dim_{\mathbb{F}_2} G[2] = N$ and additive self-dual $\mathbb{F}_4$-code MacWilliams duality. |
| **T1e** | `prove_t1e` | Combines `T1a`–`T1d` + `z4_vs_f4_separation` (all six $2\times 2$ minors of $G_{\mathbb{F}_4}$ invertible in $\mathbb{F}_4^\times$) | Completes exact cyclic $\mathbb{Z}_{2\ell}$-stabilizer dichotomy ($N \in \{2,3,5,6\}$) vs. Galois $\mathbb{F}_4$ realizability at $(4,4)$. |
| **T2a** | `prove_t2a` | `trace_spanning_coset_nonconstant`, `affine_transversal_unique_intersection` | Complex root-of-unity orthogonality of $|\psi_{x,y}\rangle = q^{-1/2}\sum_z \zeta_p^{\operatorname{Tr}(yz+x\mu(z))}|z\rangle$; zero-float verified in C++20 $\mathbb{Z}[\zeta_p]$ and Zig `comptime`. |
| **T2b** | `prove_t2b` | `rqls9_t2_maximal_cert`, `rqls11_t3_maximal_cert`, `rqls13_t4_maximal_cert`, `rqls16_t3_maximal_cert` | Zero-float C++20 $\mathbb{Z}[\zeta_p]$ verification across all 198,820 pairs confirms 0 off-diagonal collinear rays and exact row/col/transversal zeros. |
| **T2c** | `prove_t2c` | `direct_product_rqls_lifting` (combinatorial orthogonality, transversal MOLS disjointness, and abstract `nonCollinear` propagation) | **Honest boundary:** `nonCollinear` in `direct_product_rqls_lifting` models unitary-twisted disjointification $D_{\phi_{i_2,j_2}}$ on $Q_1 \otimes_D C_2$ (generic angle avoiding $\le \binom{v_1^2}{2}$ cross-cell collisions proved in `paper/main.tex` Thm T2c(b)); untwisted $Q_1 \otimes Q_2$ needs no twist. |
| **T2d** | `prove_t2d` | `f8_every_orthomorphism_is_f2_linear`, `f8_no_nonlinear_direction_perm` (structurally recursive tree proof inside kernel, zero `native_decide`) | Independently corroborated by Zig 0.17 exhaustive scan of all $7! = 5{,}040$ normalized permutations of $\mathbb{F}_8$. |
| **T3a** | `prove_t3a` | `gurvits_barnum_cor3_identity`, `two_qubit_entangled_astab_witness`, `two_qubit_sep_non_astab_witness` | Gurvits–Barnum Cor. 3 (PRA 66, 062311), Verstraete–Audenaert $\mathrm{ASEP}$ criterion, and Zurel–Davis (2026) $\mathrm{AWP}_0$ & $\mathrm{ASTAB}$ spectral facets. |
| **T3b** | `prove_t3b` | `ordered4_sum_sq_le_endpoints`, `exact_astab_circumradius_2qubit_vertex`, `ordered3_sum_sq_le_endpoints`, `exact_astab_circumradius_1qutrit_vertex` | Exact convexity reduction on the ordered spectral polytope + KKT gradient check in Eshkol Dual-AD (`err <= 2.78e-17`) and 80-digit Python. |
| **T3c** | `prove_t3c` | `symplectic_marginal_descent_all_n`, `inball_gain_exact_15_over_7` | Transitivity of $\mathrm{Sp}(2n,2)$ on 4D symplectic subspaces + exact $C_2 = 2$ on $\Lambda_2$ (verified across all 60 facets & 240 CNC $m=1$ vertices in Rust 1.94). |
| **T3d** | `prove_t3d` | `clifford_reynolds_deg2_rlt_barrier` ($M \ge 4^n - 1$ for all $n \ge 1$) | Clifford group Reynolds averaging preserving $\mathrm{STAB}_n$ and SOS cones; cross-checked on 512 instances in Rust 1.94. |
