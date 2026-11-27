module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import QPRigidity.AMEGraph
public import QPRigidity.ResolvableQLS
public import QPRigidity.MagicGeometry

/-!
# Formal Statement Contract (`Challenge.lean`)

Exports all 14 headline theorem statements (`T1a`–`T1e`, `T2a`–`T2d`, `T3a`–`T3d`, plus `AllRigidityTheorems`)
for Palomar Comparator 6-kernel replay (`PalomarChallenge.lean` vs. `PalomarSolution.lean`).
-/

namespace Challenge

open QPRigidity.AMEGraph
open QPRigidity.ResolvableQLS
open QPRigidity.MagicGeometry

/-- T1a: Exact Radical-CRT equivalence (divisor descent, prime-power ascent, coprime CRT lift). -/
public abbrev T1aStmt : Prop :=
  (∀ {N k d p : Nat} (Γ : GraphAdj N), d ≥ 2 → p ≥ 2 → p ∣ d → IsKUniformGraph d Γ k → IsKUniformGraph p Γ k) ∧
  (∀ {N k p : Nat} (Γ : GraphAdj N), p ≥ 2 → IsKUniformGraph p Γ k → ∀ e, e ≥ 1 → IsKUniformGraph (p ^ e) Γ k) ∧
  (∀ {N k a b : Nat}, a ≥ 2 → b ≥ 2 → Nat.gcd a b = 1 →
    (∃ Γ₁ : GraphAdj N, IsKUniformGraph a Γ₁ k) →
    (∃ Γ₂ : GraphAdj N, IsKUniformGraph b Γ₂ k) →
    ∃ Γ : GraphAdj N, IsKUniformGraph (a * b) Γ k)

/-- T1b: Universal unimodular canonical graph states `K_2, K_3, C_5, K_3 □ K_2, W_5` are `AME(N, d)` for ALL `d ≥ 2`. -/
public abbrev T1bStmt : Prop :=
  ∀ d : Nat, d ≥ 2 →
    IsAMEGraph d graphK2 ∧ IsAMEGraph d graphK3 ∧ IsAMEGraph d graphC5 ∧
    IsAMEGraph d graphPrism6 ∧ IsAMEGraph d graphWheel5

/-- T1c: Pure-integer Pless power-moment obstruction for ALL `p ≥ 2` (even `k < p²`, odd `k < p² + p`). -/
public abbrev T1cStmt : Prop :=
  (∀ {k p : Nat} {A : Nat → Nat}, p ≥ 2 → k ≥ 2 → PlessEvenSpec k p A → k < p ^ 2) ∧
  (∀ {k p : Nat} {A : Nat → Nat}, p ≥ 2 → k ≥ 2 → PlessOddSpec k p A → k < p ^ 2 + p)

/-- T1d: Binary commuting-weight homomorphism + Rains shadow contradictions for `N ∈ {4, 7, 9, 11}`
plus direct exhaustive `N = 4` binary graph obstruction. -/
public abbrev T1dStmt : Prop :=
  (∀ {N : Nat} (u v : Fin N → Bool × Bool),
    sympF2 u v = false → pauliWeightF2 (xorF2 u v) % 2 = (pauliWeightF2 u + pauliWeightF2 v) % 2) ∧
  (∀ {A S : Fin 5 → Nat}, RainsShadowQubitAME 4 A S → False) ∧
  (∀ {A S : Fin 8 → Nat}, RainsShadowQubitAME 7 A S → False) ∧
  (∀ {A S : Fin 10 → Nat}, RainsShadowQubitAME 9 A S → False) ∧
  (∀ {A S : Fin 12 → Nat}, RainsShadowQubitAME 11 A S → False) ∧
  (∀ Γ : GraphAdj 4, ¬ IsAMEGraph 2 Γ)

/-- T1e: Cyclic torsion-rank Singleton forcing, additive `F_4`-MDS odd-`N` obstruction (`N = 7` & `N ≥ 9`),
even-`d` `AME(4, 2ℓ)` impossibility, and Ring-vs-Field Separation at `(4, 4)` (`Z_4` impossible vs `F_4` explicit). -/
public abbrev T1eStmt : Prop :=
  (∀ {m e N : Nat} (a : Fin m → Nat), e ≥ 1 → (∀ i, a i ≤ e) → sumFin m a = e * N →
    m ≥ N ∧ (m = N → ∀ i, a i = e)) ∧
  (∀ {k : Nat} {B : Nat → Nat}, k ≥ 4 → AdditiveMDSOdd4 k B → False) ∧
  (∀ {B : Fin 8 → Nat} {A6 : Nat},
    B ⟨0, by decide⟩ = 1 → B ⟨1, by decide⟩ = 0 → B ⟨2, by decide⟩ = 0 → B ⟨3, by decide⟩ = 0 →
    choose 7 3 + B ⟨4, by decide⟩ = choose 7 3 * 4 →
    choose 7 2 + B ⟨4, by decide⟩ * 3 + B ⟨5, by decide⟩ = choose 7 2 * 16 →
    choose 7 1 + B ⟨4, by decide⟩ * 3 + B ⟨5, by decide⟩ * 2 + B ⟨6, by decide⟩ = choose 7 1 * 64 →
    1 + B ⟨4, by decide⟩ + B ⟨5, by decide⟩ + B ⟨6, by decide⟩ + B ⟨7, by decide⟩ = 256 →
    sumFinInt 8 (fun w => (B w : Int) * krawtchouk4 6 w.val 7) = 256 * (A6 : Int) → False) ∧
  (∀ {d : Nat}, d ≥ 2 → 2 ∣ d → ∀ Γ : GraphAdj 4, ¬ IsAMEGraph d Γ) ∧
  ((∀ Γ : GraphAdj 4, ¬ IsAMEGraph 4 Γ) ∧
   (∀ a b c e a' b' c' e' : Fin 4,
     f4Symp4 (f4AME4_X a b) (f4AME4_Z c e) (f4AME4_X a' b') (f4AME4_Z c' e') = false) ∧
   (∀ a b c e : Fin 4, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0) →
     f4PauliWeight4 (f4AME4_X a b) (f4AME4_Z c e) ≥ 3))

/-- T2a: General Trace-Spanning Maximal-Cardinality Theorem over ANY finite field `(F, +, *, tr)`. -/
public abbrev T2aStmt : Prop :=
  ∀ {F B : Type} (K : TraceFieldSpec F B) (H : F → Prop),
    IsTraceSpanning K H →
    ∀ (u α β : F), u ≠ K.zero → α ≠ β →
    ∀ (f : F → F), f K.zero = K.zero →
    (∀ x, H x → f x = K.mul α x) →
    (∀ x, H x → f (K.mul u x) = K.mul β (K.mul u x)) →
    ∀ a b : F, (a ≠ K.zero ∨ b ≠ K.zero) →
      ∃ z : F, K.tr (K.add (K.mul a (f z)) (K.mul b z)) ≠ K.b0

/-- T2b: Explicit kernel-verified maximal-cardinality `2-RQLS(9)`, `3-RQLS(11)`, `4-RQLS(13)`, `3-RQLS(16)`. -/
public abbrev T2bStmt : Prop :=
  (isBijectiveFin mu9 = true ∧
   isBijectiveFin (fun x : Fin 9 => gf9Add (mu9 x) (gf9Mul ⟨1, by decide⟩ x)) = true ∧
   isBijectiveFin (fun x : Fin 9 => gf9Add (mu9 x) (gf9Mul ⟨2, by decide⟩ x)) = true ∧
   (∀ a b : Fin 9, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 9, gf9Trace (gf9Add (gf9Mul a (mu9 z)) (gf9Mul b z)) ≠ 0)) ∧
  (isBijectiveFin mu11 = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨(mu11 x + 7 * x.val) % 11, Nat.mod_lt _ (by decide)⟩) = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨(mu11 x + 8 * x.val) % 11, Nat.mod_lt _ (by decide)⟩) = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨(mu11 x + 10 * x.val) % 11, Nat.mod_lt _ (by decide)⟩) = true ∧
   (∀ a b : Fin 11, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 11, (a.val * (mu11 z).val + b.val * z.val) % 11 ≠ 0)) ∧
  (isBijectiveFin mu13 = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨(mu13 x + 7 * x.val) % 13, Nat.mod_lt _ (by decide)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨(mu13 x + 9 * x.val) % 13, Nat.mod_lt _ (by decide)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨(mu13 x + 10 * x.val) % 13, Nat.mod_lt _ (by decide)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨(mu13 x + 11 * x.val) % 13, Nat.mod_lt _ (by decide)⟩) = true ∧
   (∀ a b : Fin 13, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 13, (a.val * (mu13 z).val + b.val * z.val) % 13 ≠ 0)) ∧
  (isBijectiveFin mu16 = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul ⟨3, by decide⟩ x)) = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul ⟨9, by decide⟩ x)) = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul ⟨10, by decide⟩ x)) = true ∧
   (∀ a b : Fin 16, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 16, gf16Trace (gf16Add (gf16Mul a (mu16 z)) (gf16Mul b z)) = true))

/-- T2c: Universal `t`-resolvable direct-product lifting: BOTH untwisted quantum-quantum `Q₁ ⊗ Q₂`
and unitary-twisted quantum-classical `Q₁ ⊗_D C₂` (with explicit twist-separation witness). -/
public abbrev T2cStmt : Prop :=
  (∀ {v1 v2 t : Nat}, v2 > 0 → ResolvableQLSSpec v1 t → ResolvableQLSSpec v2 t →
    Nonempty (ResolvableQLSSpec (v1 * v2) t)) ∧
  (∀ {v1 v2 t : Nat}, v2 > 0 → ResolvableQLSSpec v1 t → (C2 : ClassicalMOLSRes v2 t) →
    (twistSep : Fin v2 → Fin v2 → Fin v2 → Fin v2 → Prop) →
    (∀ i2 j2 i2' j2', (i2 ≠ i2' ∨ j2 ≠ j2') → C2.sym i2 j2 = C2.sym i2' j2' → twistSep i2 j2 i2' j2') →
    Nonempty (ResolvableQLSSpec (v1 * v2) t))

/-- T2d: Exhaustive `F_8` non-linear orthomorphism & direction obstruction. -/
public abbrev T2dStmt : Prop :=
  ∀ (μ : Fin 8 → Fin 8) (c : Fin 8), μ 0 = 0 → c ≠ 0 →
    (∀ x y : Fin 8, μ x = μ y → x = y) →
    (∀ x y : Fin 8, gf8Add (μ x) (gf8Mul c x) = gf8Add (μ y) (gf8Mul c y) → x = y) →
    ∀ x y : Fin 8, μ (gf8Add x y) = gf8Add (μ x) (μ y)

/-- T3a: Bipartite odd-prime `AWP ⊆ ASEP` Gurvits-Barnum Cor 3 identity + 2-qubit strict incomparability witnesses. -/
public abbrev T3aStmt : Prop :=
  (∀ D P_num P_den : Int, D ≥ 2 → P_den > 0 → (D - 1) * P_num ≤ P_den →
    (D - 1) * (D - 1) * P_num - 2 * (D - 1) * P_den + D * P_den ≤ P_den) ∧
  (quadPos 3 (11 + 3) (3 - 11) ∧ quadPos 5 20 (6 - 14) ∧ (((11 : Int) - 3) * (11 - 3) > 4 * 3 * 3)) ∧
  ((((8 : Int) - 4) * (8 - 4) < 4 * 7 * 1) ∧ quadPos 3 (-(8 + 1)) (8 - 1))

/-- T3b: Universal global polytope optimality of 2-qubit (`Z[√3]`) & 1-qutrit (`Z[√5]`) `ASTAB_0`
circumradii + exact extremal vertex bounds. -/
public abbrev T3bStmt : Prop :=
  (∀ l1 l2 l3 l4 M : Int, M > 0 → l1 + l2 + l3 + l4 = M → l1 ≥ l2 → l2 ≥ l3 → l3 ≥ l4 → l4 ≥ 0 →
    quadNonneg 3 (l1 + l4) (l4 - l1) →
    quadNonneg 3 (40 * (M * M) - 121 * (l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4)) (3 * (M * M))) ∧
  (∀ l1 l2 l3 M : Int, M > 0 → l1 + l2 + l3 = M → l1 ≥ l2 → l2 ≥ l3 → l3 ≥ 0 →
    2 * l1 ≤ M → quadNonneg 5 (2 * l3 - 3 * l1) l1 →
    quadNonneg 5 (3 * (M * M) - 2 * (l1 * l1 + l2 * l2 + l3 * l3)) (-(M * M))) ∧
  (quadPos 3 (36 * 13 - 484) (36 * 4)) ∧
  (quadPos 5 27 (-12) ∧ quadPos 5 (-6) 3)

/-- T3c: General finite uniform-covering double-counting theorem + unconditional Symplectic Marginal
Descent bound & exact `15/7` squared-inball gain for ALL `n ≥ 2`. -/
public abbrev T3cStmt : Prop :=
  (∀ {P K m r B : Nat} (inSub : Fin K → Fin P → Bool) (f : Fin P → Nat),
    r > 0 →
    (∀ k : Fin K, countFin P (fun p => inSub k p) = m) →
    (∀ p : Fin P, countFin K (fun k => inSub k p) = r) →
    (∀ k : Fin K, sumFin P (fun p => if inSub k p then f p else 0) ≤ B) →
    m * sumFin P f ≤ B * P) ∧
  (∀ n S Q : Nat, n ≥ 2 → Q > 0 → 15 * S ≤ 7 * (4 ^ n - 1) * Q →
    15 * (Q + S) ≤ (7 * 4 ^ n + 8) * Q ∧ (7 * 4 ^ n + 8) * Q < 15 * 4 ^ n * Q) ∧
  (∀ n : Nat, n ≥ 1 → 15 * ((7 * 4 ^ n + 8) - 15) = 7 * (15 * (4 ^ n - 1)))

/-- T3d: First-principles multivariate polynomial Degree-2 RLT+SOS Barrier (`M ≥ 4ⁿ - 1` for ALL `n ≥ 1`
and ANY finite stabilizer facet system `s` with pairwise overlaps `≥ -1`). -/
public abbrev T3dStmt : Prop :=
  ∀ (n K R : Nat), n ≥ 1 →
  ∀ (s : Fin K → Fin (4 ^ n - 1) → Int)
    (lam : Fin K → Fin K → Int)
    (mu : Fin K → Int)
    (c : Fin R → Int)
    (v : Fin R → Fin (4 ^ n - 1) → Int)
    (M : Int),
    (∀ k l, lam k l ≥ 0) →
    (∀ k, mu k ≥ 0) →
    (∀ k l, sumFinInt (4 ^ n - 1) (fun p => s k p * s l p) ≥ -1) →
    (∀ x : Fin (4 ^ n - 1) → Int,
      M - sumFinInt (4 ^ n - 1) (fun p => x p * x p) = polyRltSos s lam mu c v x) →
    M ≥ ((4 ^ n - 1 : Nat) : Int)

/-- Master conjunction of all 13 headline theorems across Pillars I, II, and III. -/
public abbrev AllRigidityTheoremsStmt : Prop :=
  T1aStmt ∧ T1bStmt ∧ T1cStmt ∧ T1dStmt ∧ T1eStmt ∧
  T2aStmt ∧ T2bStmt ∧ T2cStmt ∧ T2dStmt ∧
  T3aStmt ∧ T3bStmt ∧ T3cStmt ∧ T3dStmt

end Challenge
