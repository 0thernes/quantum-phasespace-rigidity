<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Epistemic Claims Ledger (`0TH-2026-020`, v2.0.0)

**Author:** Alexander Stephen Donahue (`ORCID 0009-0006-8168-9648`, Independent Researcher, Spokane, WA, USA)
**Repository:** `0thernes/quantum-phasespace-rigidity`

Every mathematical, computational, and empirical claim in this repository is strictly classified into one of four verification tiers:

- **`[LEAN-6K]`**: Formally proved in pure zero-Mathlib Lean 4.35.0 (`lean/PalomarSolution.lean`), strictly within `[propext, Classical.choice, Quot.sound]`, zero `sorry`/`admit`/`native_decide`, `warningAsError = true`, audited by `leanchecker-paranoid`, whole-module `Lean.collectAxioms` sweep (`SweepAllAxioms.lean`), and 6 independent proof kernels via Palomar Comparator.
- **`[EXACT-COMP]`**: Independently verified in zero-float exact arithmetic across compiled native engines (`Rust 1.94`, `Zig 0.17`, `C++20`, `ISO C11 + x86-64 NASM`, `Python 3.12 Fraction/80-digit Decimal`), plus clearly tagged `numerical_approximation` checks in C11 QGTL & Eshkol forward-mode dual-number AD.
- **`[PAPER-PROOF]`**: Proved completely in `paper/main.tex` (with full self-contained `\begin{proof}...\end{proof}` blocks for all 13 theorems `T1a`–`T3d`).
- **`[OPEN]`**: Explicitly NOT claimed to be solved here.

---

## Verified Claims (1-to-1 Aligned with `lean/Challenge.lean`)

| Claim ID | Statement | Primary Proof Artifact | Cross-Check Engines | Tier |
| :--- | :--- | :--- | :--- | :--- |
| **T1a** | Radical-CRT equivalence: divisor descent ($d \to m \mid d$), prime-power Hensel ascent ($p \to p^e$), and coprime CRT lifting ($a,b \to ab$) for $k$-uniform canonical graph states | `lean/QPRigidity/AMEGraph.lean` (`prove_t1a`) | Python, `paper/main.tex` | `[LEAN-6K]` `[PAPER-PROOF]` |
| **T1b** | Universal unimodular canonical graph states $K_2, K_3, C_5, \mathrm{Prism}_6 = K_3 \mathbin{\square} K_2, W_5$ are $\mathrm{AME}(N, d)$ for **every** integer $d \ge 2$ (all 20 $3\times 3$ minors of $\mathrm{Prism}_6$ & $W_5$ in $\{\pm 1\}$) | `lean/QPRigidity/AMEGraph.lean` (`prove_t1b`) | C11+NASM (`all 20 minors in {±1}`), Python | `[LEAN-6K]` `[EXACT-COMP]` |
| **T1c** | Universal Pless power-moment obstruction for all $p \ge 2$: no $\mathbb{F}_p$-stabilizer $\mathrm{AME}(N, p)$ for even $N = 2k \ge 2p^2$ ($k \ge p^2$) or odd $N = 2k+1 \ge 2p^2+2p+1$ ($k \ge p^2+p$) | `lean/QPRigidity/AMEGraph.lean` (`prove_t1c`) | Python Hypothesis, Rust | `[LEAN-6K]` `[EXACT-COMP]` |
| **T1d** | Binary commuting-weight homomorphism + exact Rains shadow obstructions ($S_0(4)=-1/2$, $S_1(7)=7/4 \notin \mathbb{Z}$, $S_1(9)=-9/4$, $S_3(11)=-165/8$) + exhaustive 0/64 binary $N=4$ graph search (132/1,024 at $N=5$) | `lean/QPRigidity/AMEGraph.lean` (`prove_t1d`) | Rust, C11+NASM, Python | `[LEAN-6K]` `[EXACT-COMP]` |
| **T1e** | Torsion Singleton $p$-rank forcing ($\dim_{\mathbb{F}_2} G[2] = N$), additive $\mathbb{F}_4$-MDS impossibility ($N=7$ $A_6 = -21 < 0$ & odd $N \ge 9$ $B_{k+2} < 0$), complete cyclic $\mathbb{Z}_{2\ell}$-stabilizer $\mathrm{AME}(N, 2\ell)$ dichotomy ($N \in \{2,3,5,6\}$), and Ring-vs-Field separation at $(4,4)$ ($\mathbb{Z}_4$ impossible vs. $\mathbb{F}_4$ CSS pair $(G_X, G_Z)$) | `lean/QPRigidity/AMEGraph.lean` (`prove_t1e`) | Rust, C11+NASM, Python, `paper/main.tex` | `[LEAN-6K]` `[EXACT-COMP]` `[PAPER-PROOF]` |
| **T2a** | General Trace-Spanning Maximal-Cardinality Theorem over any finite field + Megyesi prime-field family giving maximal-cardinality $\frac{p-5}{2}$-$\mathrm{RQLS}(p)$ for all odd primes $p \ge 7$ (breaks $t \le 2$ ceiling of Zhang & Cao 2026) | `lean/QPRigidity/ResolvableQLS.lean` (`prove_t2a`) | C++20 $\mathbb{Z}[\zeta_p]$, Zig `comptime`, Python | `[LEAN-6K]` `[EXACT-COMP]` `[PAPER-PROOF]` |
| **T2b** | Kernel-checked maximal-cardinality $2$-$\mathrm{RQLS}(9)$, $3$-$\mathrm{RQLS}(11)$, $4$-$\mathrm{RQLS}(13)$, and char-2 $3$-$\mathrm{RQLS}(16)$ (plus $6$-$\mathrm{RQLS}(17)$ in C++20/Zig) | `lean/QPRigidity/ResolvableQLS.lean` (`prove_t2b`) | C++20 (`198,820` exact $\mathbb{Z}[\zeta_p]$ pairs, `0` off-diag collinear), Zig `comptime` | `[LEAN-6K]` `[EXACT-COMP]` |
| **T2c** | Direct-product composite lifting: **both** untwisted quantum–quantum $Q_1 \otimes Q_2$ ($3$-$\mathrm{RQLS}(143)$) and unitary-twisted quantum–classical $Q_1 \otimes_D C_2$ ($3$-$\mathrm{RQLS}(55)$ with explicit `twistSep` hypothesis) | `lean/QPRigidity/ResolvableQLS.lean` (`prove_t2c`), `NonVacuity.lean` | `paper/main.tex` (collision-avoidance proof) | `[LEAN-6K]` `[PAPER-PROOF]` |
| **T2d** | Zero-gap $\mathbb{F}_8$ obstruction: every orthomorphism of $\mathbb{F}_8$ fixing $0$ is $\mathbb{F}_2$-linear (`0/4,872` nonlinear permutations vs. `84` on $\mathbb{F}_7$) | `lean/QPRigidity/ResolvableQLS.lean` (`prove_t2d`) | Zig 0.17 exhaustive 5,040-perm runtime scan | `[LEAN-6K]` `[EXACT-COMP]` |
| **T3a** | Exact Gurvits–Barnum Cor. 3 identity ($\mathrm{ASTAB}_{2,d} \subset \mathrm{AWP}_{2,d} \subseteq \mathrm{ASEP}_{2,d}$ for all odd primes $d \ge 3$, all-bipartition biseparability $\forall n \ge 2$) + 2-qubit strict incomparability witnesses $\rho_{\mathrm{ent}} = (11,3,3,3)/20$, $\rho_{\mathrm{sep}} = (8,7,4,1)/20$ | `lean/QPRigidity/MagicGeometry.lean` (`prove_t3a`) | Rust, Python 80-digit Decimal, `paper/main.tex` | `[LEAN-6K]` `[EXACT-COMP]` `[PAPER-PROOF]` |
| **T3b** | Universal global polytope optimality in $\mathbb{Z}[\sqrt{3}]$ & $\mathbb{Z}[\sqrt{5}]$ for exact closed-form circumradii $R^2(\mathrm{ASTAB}_{2,2}) = \frac{3(13+4\sqrt{3})}{484} > \frac{1}{12}$ and $R^2(\mathrm{ASTAB}_{1,3}) = \frac{7-3\sqrt{5}}{6} \in (\frac{1}{24}, \frac{1}{6})$ | `lean/QPRigidity/MagicGeometry.lean` (`prove_t3b`) | Eshkol Dual-AD (`err <= 2.78e-17`), Python 80-digit | `[LEAN-6K]` `[EXACT-COMP]` `[PAPER-PROOF]` |
| **T3c** | Finite uniform-covering double-counting theorem + Symplectic Marginal Descent: $C_n = \max_{\Lambda_n}\operatorname{Tr}(X^2) \le \frac{7\cdot 4^n + 8}{15\cdot 2^n}$ yielding an exact unconditional $15/7\times$ squared-inball-radius strengthening of Liu et al. Thm 10 for all $n \ge 2$ | `lean/QPRigidity/MagicGeometry.lean` (`prove_t3c`) | Rust (60 facets, all 240 CNC $m=1$ vertices, all 336 $n=3$ 4D subspaces with $r=80$), Python Hypothesis | `[LEAN-6K]` `[EXACT-COMP]` `[PAPER-PROOF]` |
| **T3d** | First-principles multivariate polynomial Clifford–Reynolds Degree-2 RLT+SOS Barrier: no degree-2 RLT+SOS polynomial certificate over $\Lambda_n$ (for any stabilizer facet system with pairwise overlaps $\ge -1$) beats $M = 4^n - 1$ ($\operatorname{Tr}(X^2) \le 2^n$) | `lean/QPRigidity/MagicGeometry.lean` (`prove_t3d`) | Rust (all 1,770 $\Lambda_2$ facet pairs min overlap $-1$, 512-case sweep) | `[LEAN-6K]` `[EXACT-COMP]` |
| **QGTL** | Fubini–Study metric & Berry curvature on 2-qubit Entangled-$\mathrm{ASTAB}$ manifold and $3$-$\mathrm{RQLS}(11)$ phase torus; Moonlab SP 800-90B + SHA3-256 audited QRNG $\Lambda_2$ sampling (`numerical_approximation` tagged) | `c/src/qgtl_metric.c`, `c/src/qrng_fw.c`, `eshkol/qgtl_trajectory_ad.esk` | C11+NASM (`err 1.72e-11`, `5.90e-10`), Eshkol AD (`err 0.00`) | `[EXACT-COMP]` `[PAPER-PROOF]` |

---

## Falsification Criteria (What Would Prove Us Wrong)

Any single independently reproducible artifact below would immediately falsify the corresponding theorem and trigger a public entry in `ERRATA.md`:

1. **Pillar I (`T1a`–`T1e`):**
   - Exhibiting a cyclic Weyl–Heisenberg isotropic subgroup $G \le \mathbb{Z}_{2\ell}^{2N}$ of order $(2\ell)^N$ with minimum symplectic Hamming weight $\ge \lfloor N/2 \rfloor + 1$ for any even $d = 2\ell \ge 2$ and any $N \notin \{2, 3, 5, 6\}$ (e.g., $(N, d) = (4, 4)$ or $(7, 2)$).
   - Exhibiting a $3 \times 3$ cross-bipartition minor of $\mathrm{Prism}_6$ or $W_5$ with determinant $\notin \{\pm 1\}$.
2. **Pillar II (`T2a`–`T2d`):**
   - Exhibiting two distinct cells $(x, y) \ne (x', y')$ in our $2$-$\mathrm{RQLS}(9)$, $3$-$\mathrm{RQLS}(11)$, $4$-$\mathrm{RQLS}(13)$, $3$-$\mathrm{RQLS}(16)$, or $6$-$\mathrm{RQLS}(17)$ arrays with $|\langle \psi_{x,y} | \psi_{x',y'} \rangle| = 1$, or a non-zero inner product along any declared row, column, or transversal slope.
   - Exhibiting a non-$\mathbb{F}_2$-linear bijection $\theta : \mathbb{F}_8 \to \mathbb{F}_8$ with $\theta(0) = 0$ such that $x \mapsto \theta(x) \oplus x$ is also bijective.
3. **Pillar III (`T3a`–`T3d`):**
   - Exhibiting an entangled bipartite odd-prime ($d \ge 3$) state $\rho \in \mathrm{AWP}_{2,d}$ with $\operatorname{Tr}(\rho^2) \le 1/(d^2 - 1)$ (which would also refute Gurvits & Barnum Corollary 3).
   - Exhibiting any $X \in \Lambda_n$ ($n \ge 2$) with $\operatorname{Tr}(X^2) > \frac{7 \cdot 4^n + 8}{15 \cdot 2^n}$, or a valid degree-2 RLT+SOS polynomial certificate over $\Lambda_n$ achieving $M < 4^n - 1$.

---

## Explicitly Open Problems (`[OPEN]` — Not Solved Here)

1. **0thernes Mega-Atlas V2 (`0/1,900`):** Zero Millennium/Erdős/grand classical problems are claimed solved.
2. **Non-stabilizer even-$d$ $\mathrm{AME}(N, d)$ existence** (e.g., $\mathrm{AME}(4, 6)$ of Rather et al. 2022) and odd-$d$ stabilizer classification below $2p^2$.
3. **Zhang & Cao's 17 sporadic missing orders for $1$-$\mathrm{RQLS}(v)$** beginning at $v = 10$ (where $2 \mid v$ prevents odd prime-power lifting).
4. **Zurel & Davis Conjectures 1 and 2 for $n \ge 3$ qubits**, and whether odd-prime multipartite ($n \ge 3$) $\mathrm{AWP}_{n,d}$ contains bound-entangled states beyond all-bipartition biseparability.
