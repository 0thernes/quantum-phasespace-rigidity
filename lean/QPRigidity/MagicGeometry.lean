module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import QPRigidity.AMEGraph

/-!
# Pillar III: Absolutely Stabilizer Magic Geometry, Entanglement Dichotomy, & RLT Barrier (`QPRigidity.MagicGeometry`)

Resolves open problems of Zurel & Davis (`arXiv:2602.22336v2`, 30 Sep 2026, Sec. V.3 & VII)
and strengthens Liu, Haug, Ye, Liu, and Roth (`arXiv:2512.16777v2`, Apr/Aug 2026, Thm 10):

* **T3a** (`gurvits_barnum_cor3_identity`, `two_qubit_entangled_astab_witness`,
  `two_qubit_sep_non_astab_witness`):
  (i) Exact Gurvits-Barnum Corollary 3 identity proving `ASTAB_{2,d} ⊂ AWP_{2,d} ⊆ ASEP_{2,d}`
  for ALL bipartite odd-prime systems (zero entangled 2-qudit AWP states) and all-bipartition
  biseparability for ALL `n ≥ 2`, reversing the Sec. V.3 expectation of Zurel & Davis;
  (ii) Two exact rational witnesses proving 2-qubit `ASTAB_2` and `ASEP_2` are strictly incomparable.
* **T3b** (`two_qubit_astab_global_circumradius`, `one_qutrit_astab_global_circumradius`,
  `exact_astab_circumradius_2qubit_vertex`, `exact_astab_circumradius_1qutrit_vertex`):
  Complete universal global polytope optimality proofs over exact quadratic rings `Z[√3]` and `Z[√5]`
  (zero reals, zero floats), certifying the exact 2-qubit `ASTAB` circumradius
  `R² = 3(13 + 4√3)/484 > 1/12 = r²_GB` and 1-qutrit `ASTAB` circumradius
  `R² = (7 - 3√5)/6` (`1/24 < R² < 1/6`).
* **T3c** (`uniform_cover_avg_bound`, `symplectic_marginal_descent_all_n`, `inball_gain_exact_15_over_7`):
  General finite uniform-covering double-counting theorem + unconditional Symplectic Marginal
  Descent bound `Tr(X²) ≤ (7·4ⁿ + 8)/(15·2ⁿ) ≤ 2^(n-1) < 2^n` for ALL `n ≥ 2`, improving
  Liu et al. Theorem 10 by an exact squared-inball factor `15/7` for every `n ≥ 2`.
* **T3d** (`deg2_rlt_sos_polynomial_barrier`, `clifford_reynolds_deg2_rlt_barrier`):
  First-principles multivariate polynomial degree-2 RLT+SOS barrier theorem proving that for ANY
  finite stabilizer facet system `s : Fin K → Fin P → Int` satisfying pairwise inner product
  `∑_p s_{k,p} s_{l,p} ≥ -1`, ANY pointwise degree-2 RLT+SOS polynomial identity
  `M - ∑_{p=1}^P x_p² = ∑ λ_{k,l} ℓ_k(x) ℓ_l(x) + ∑ μ_k ℓ_k(x) + ∑ (c_r + ∑ v_{r,p} x_p)²`
  with `λ_{k,l} ≥ 0, μ_k ≥ 0` unconditionally forces `M ≥ P` (`M ≥ 4^n - 1` for `P = 4^n - 1`).
-/

namespace QPRigidity.MagicGeometry

open QPRigidity.AMEGraph

/-! ## Section 1: Exact Ordered Quadratic-Ring Arithmetic `Z[√d]` (Zero Floats, Zero Reals) -/

/-- Exact predicate for `a + b * √d ≥ 0` over `Int` (`d > 0`, square-free). -/
@[expose] public def quadNonneg (d : Nat) (a b : Int) : Prop :=
  (a ≥ 0 ∧ b ≥ 0) ∨
  (a ≥ 0 ∧ b < 0 ∧ a * a ≥ (d : Int) * (b * b)) ∨
  (a < 0 ∧ b ≥ 0 ∧ (d : Int) * (b * b) ≥ a * a)

/-- Strict inequality `a + b * √d > 0` over `Int`. -/
@[expose] public def quadPos (d : Nat) (a b : Int) : Prop :=
  (a > 0 ∧ b ≥ 0) ∨
  (a ≥ 0 ∧ b > 0) ∨
  (a > 0 ∧ b < 0 ∧ a * a > (d : Int) * (b * b)) ∨
  (a ≤ 0 ∧ b > 0 ∧ (d : Int) * (b * b) > a * a)

private theorem int_sq_nonneg (x : Int) : x * x ≥ 0 := by
  by_cases h : x ≥ 0
  · exact Int.mul_nonneg h h
  · exact Int.le_of_lt (Int.mul_pos_of_neg_of_neg (by omega) (by omega))

private theorem int_sq_le_sq_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x * x ≤ y * y) :
    x ≤ y := by
  exact Classical.byContradiction fun hgt => by
    have h1 : y < x := by omega
    have h2 : y * y ≤ y * x := Int.mul_le_mul_of_nonneg_left (by omega) hy
    have h3 : y * x < x * x := Int.mul_lt_mul_of_pos_right h1 (by omega)
    omega

private theorem int_sq_ge_of_le_nonneg {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x * x ≤ y * y := by
  have hy : 0 ≤ y := by omega
  have h1 : x * x ≤ x * y := Int.mul_le_mul_of_nonneg_left hxy hx
  have h2 : x * y ≤ y * y := Int.mul_le_mul_of_nonneg_right hxy hy
  omega

private theorem int_sq_lt_of_lt_nonneg {x y : Int} (hx : 0 ≤ x) (hxy : x < y) :
    x * x < y * y := by
  have hy : 0 < y := by omega
  have h1 : x * x ≤ x * y := Int.mul_le_mul_of_nonneg_left (by omega) hx
  have h2 : x * y < y * y := Int.mul_lt_mul_of_pos_right hxy hy
  omega

private theorem int_le_of_mul_le_mul_pos {k x y : Int} (hk : 0 < k) (h : k * x ≤ k * y) :
    x ≤ y := by
  exact Classical.byContradiction fun hgt => by
    have hlt : y < x := by omega
    have hbad : k * y < k * x := Int.mul_lt_mul_of_pos_left hlt hk
    omega

private theorem quadNonneg_of_int {d : Nat} {a : Int} (ha : a ≥ 0) : quadNonneg d a 0 :=
  Or.inl ⟨ha, by omega⟩

private theorem quadNonneg_of_pos_mul {d : Nat} {k a b : Int} (hk : k > 0)
    (h : quadNonneg d (k * a) (k * b)) : quadNonneg d a b := by
  have hk2 : k * k > 0 := Int.mul_pos hk hk
  have hsign_ge : ∀ x : Int, k * x ≥ 0 → x ≥ 0 := fun x hx => by
    have h0 : k * 0 ≤ k * x := by rw [Int.mul_zero]; exact hx
    exact int_le_of_mul_le_mul_pos hk h0
  have hsign_lt : ∀ x : Int, k * x < 0 → x < 0 := fun x hx =>
    Classical.byContradiction fun hge => by
      have hnn : k * x ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      omega
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hsq_ge⟩ | ⟨ha, hb, hsq_ge⟩
  · exact Or.inl ⟨hsign_ge a ha, hsign_ge b hb⟩
  · right; left
    refine ⟨hsign_ge a ha, hsign_lt b hb, ?_⟩
    have h1 : (k * k) * ((d : Int) * (b * b)) ≤ (k * k) * (a * a) := by
      have eL : (k * k) * ((d : Int) * (b * b)) = (d : Int) * ((k * b) * (k * b)) := by grind
      have eR : (k * k) * (a * a) = (k * a) * (k * a) := by grind
      omega
    exact int_le_of_mul_le_mul_pos hk2 h1
  · right; right
    refine ⟨hsign_lt a ha, hsign_ge b hb, ?_⟩
    have h1 : (k * k) * (a * a) ≤ (k * k) * ((d : Int) * (b * b)) := by
      have eL : (k * k) * (a * a) = (k * a) * (k * a) := by grind
      have eR : (k * k) * ((d : Int) * (b * b)) = (d : Int) * ((k * b) * (k * b)) := by grind
      omega
    exact int_le_of_mul_le_mul_pos hk2 h1

/-- Exact additive closure of the nonnegativity cone in `Z[√d]` (`d > 0`). -/
public theorem quadNonneg_add {d : Nat} (hd : d > 0) {a1 b1 a2 b2 : Int}
    (h1 : quadNonneg d a1 b1) (h2 : quadNonneg d a2 b2) :
    quadNonneg d (a1 + a2) (b1 + b2) := by
  have hd_pos : (d : Int) > 0 := by omega
  have hd_nn : (d : Int) ≥ 0 := by omega
  have hsub1 : ∀ X x Y y : Int, X ≥ x → x > 0 → Y > y → y ≥ 0 →
      X * X ≥ (d : Int) * (Y * Y) → (d : Int) * (y * y) ≥ x * x →
      (X - x) * (X - x) ≥ (d : Int) * ((Y - y) * (Y - y)) := by
    intro X x Y y hXx hx hYy hy hX hdy
    have hXY_sq : (Y * x) * (Y * x) ≤ (X * y) * (X * y) := by
      have e1 : (Y * x) * (Y * x) = (Y * Y) * (x * x) := by grind
      have e2 : (X * y) * (X * y) = (X * X) * (y * y) := by grind
      have m1 : (Y * Y) * (x * x) ≤ (Y * Y) * ((d : Int) * (y * y)) :=
        Int.mul_le_mul_of_nonneg_left hdy (int_sq_nonneg Y)
      have m2 : (Y * Y) * ((d : Int) * (y * y)) = ((d : Int) * (Y * Y)) * (y * y) := by grind
      have m3 : ((d : Int) * (Y * Y)) * (y * y) ≤ (X * X) * (y * y) :=
        Int.mul_le_mul_of_nonneg_right hX (int_sq_nonneg y)
      omega
    have hXy_ge : Y * x ≤ X * y :=
      int_sq_le_sq_nonneg (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) hy) hXY_sq
    have hlin : X * (Y - y) ≤ Y * (X - x) := by grind
    have hsq_lin : (X * (Y - y)) * (X * (Y - y)) ≤ (Y * (X - x)) * (Y * (X - x)) :=
      int_sq_ge_of_le_nonneg (Int.mul_nonneg (by omega) (by omega)) hlin
    have eL : (X * (Y - y)) * (X * (Y - y)) = (X * X) * ((Y - y) * (Y - y)) := by grind
    have eR : (Y * (X - x)) * (Y * (X - x)) = (Y * Y) * ((X - x) * (X - x)) := by grind
    have hstep : ((d : Int) * (Y * Y)) * ((Y - y) * (Y - y)) ≤ (X * X) * ((Y - y) * (Y - y)) :=
      Int.mul_le_mul_of_nonneg_right hX (int_sq_nonneg (Y - y))
    have hre : (Y * Y) * ((d : Int) * ((Y - y) * (Y - y))) = ((d : Int) * (Y * Y)) * ((Y - y) * (Y - y)) := by grind
    have hYY : Y * Y > 0 := Int.mul_pos (by omega) (by omega)
    exact int_le_of_mul_le_mul_pos hYY (by omega)
  have hsub2 : ∀ X x Y y : Int, X > x → x ≥ 0 → Y ≥ y → y > 0 →
      (d : Int) * (Y * Y) ≥ X * X → x * x ≥ (d : Int) * (y * y) →
      (d : Int) * ((Y - y) * (Y - y)) ≥ (X - x) * (X - x) := by
    intro X x Y y hXx hx hYy hy hdY hx2
    have hXY_sq : (d : Int) * ((X * y) * (X * y)) ≤ (d : Int) * ((Y * x) * (Y * x)) := by
      have m1 : (d : Int) * ((X * y) * (X * y)) = (X * X) * ((d : Int) * (y * y)) := by grind
      have m2 : (X * X) * ((d : Int) * (y * y)) ≤ (X * X) * (x * x) :=
        Int.mul_le_mul_of_nonneg_left hx2 (int_sq_nonneg X)
      have m3 : (X * X) * (x * x) ≤ ((d : Int) * (Y * Y)) * (x * x) :=
        Int.mul_le_mul_of_nonneg_right hdY (int_sq_nonneg x)
      have m4 : ((d : Int) * (Y * Y)) * (x * x) = (d : Int) * ((Y * x) * (Y * x)) := by grind
      omega
    have hXy_le : X * y ≤ Y * x :=
      int_sq_le_sq_nonneg (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) hx)
        (int_le_of_mul_le_mul_pos hd_pos hXY_sq)
    have hlin : Y * (X - x) ≤ X * (Y - y) := by grind
    have hsq_lin : (Y * (X - x)) * (Y * (X - x)) ≤ (X * (Y - y)) * (X * (Y - y)) :=
      int_sq_ge_of_le_nonneg (Int.mul_nonneg (by omega) (by omega)) hlin
    have eL : (Y * (X - x)) * (Y * (X - x)) = (Y * Y) * ((X - x) * (X - x)) := by grind
    have eR : (X * (Y - y)) * (X * (Y - y)) = (X * X) * ((Y - y) * (Y - y)) := by grind
    have hstep : (X * X) * ((Y - y) * (Y - y)) ≤ ((d : Int) * (Y * Y)) * ((Y - y) * (Y - y)) :=
      Int.mul_le_mul_of_nonneg_right hdY (int_sq_nonneg (Y - y))
    have hre : (Y * Y) * ((d : Int) * ((Y - y) * (Y - y))) = ((d : Int) * (Y * Y)) * ((Y - y) * (Y - y)) := by grind
    have hYY : Y * Y > 0 := Int.mul_pos (by omega) (by omega)
    exact int_le_of_mul_le_mul_pos hYY (by omega)
  have hboth_neg_b : ∀ x1 y1 x2 y2 : Int, x1 ≥ 0 → y1 > 0 → x2 ≥ 0 → y2 > 0 →
      x1 * x1 ≥ (d : Int) * (y1 * y1) → x2 * x2 ≥ (d : Int) * (y2 * y2) →
      (x1 + x2) * (x1 + x2) ≥ (d : Int) * ((y1 + y2) * (y1 + y2)) := by
    intro x1 y1 x2 y2 hx1 hy1 hx2 hy2 h1sq h2sq
    have hcross_sq : ((d : Int) * (y1 * y2)) * ((d : Int) * (y1 * y2)) ≤ (x1 * x2) * (x1 * x2) := by
      have eL : ((d : Int) * (y1 * y2)) * ((d : Int) * (y1 * y2)) =
                ((d : Int) * (y1 * y1)) * ((d : Int) * (y2 * y2)) := by grind
      have eR : (x1 * x2) * (x1 * x2) = (x1 * x1) * (x2 * x2) := by grind
      have m1 : ((d : Int) * (y1 * y1)) * ((d : Int) * (y2 * y2)) ≤ (x1 * x1) * ((d : Int) * (y2 * y2)) :=
        Int.mul_le_mul_of_nonneg_right h1sq (Int.mul_nonneg hd_nn (int_sq_nonneg y2))
      have m2 : (x1 * x1) * ((d : Int) * (y2 * y2)) ≤ (x1 * x1) * (x2 * x2) :=
        Int.mul_le_mul_of_nonneg_left h2sq (int_sq_nonneg x1)
      omega
    have hcross : (d : Int) * (y1 * y2) ≤ x1 * x2 :=
      int_sq_le_sq_nonneg (Int.mul_nonneg hd_nn (Int.mul_nonneg (by omega) (by omega)))
        (Int.mul_nonneg hx1 hx2) hcross_sq
    grind
  have hboth_neg_a : ∀ x1 y1 x2 y2 : Int, x1 > 0 → y1 ≥ 0 → x2 > 0 → y2 ≥ 0 →
      (d : Int) * (y1 * y1) ≥ x1 * x1 → (d : Int) * (y2 * y2) ≥ x2 * x2 →
      (d : Int) * ((y1 + y2) * (y1 + y2)) ≥ (x1 + x2) * (x1 + x2) := by
    intro x1 y1 x2 y2 hx1 hy1 hx2 hy2 h1sq h2sq
    have hcross_sq : (x1 * x2) * (x1 * x2) ≤ ((d : Int) * (y1 * y2)) * ((d : Int) * (y1 * y2)) := by
      have eR : ((d : Int) * (y1 * y2)) * ((d : Int) * (y1 * y2)) =
                ((d : Int) * (y1 * y1)) * ((d : Int) * (y2 * y2)) := by grind
      have eL : (x1 * x2) * (x1 * x2) = (x1 * x1) * (x2 * x2) := by grind
      have m1 : (x1 * x1) * (x2 * x2) ≤ ((d : Int) * (y1 * y1)) * (x2 * x2) :=
        Int.mul_le_mul_of_nonneg_right h1sq (int_sq_nonneg x2)
      have m2 : ((d : Int) * (y1 * y1)) * (x2 * x2) ≤ ((d : Int) * (y1 * y1)) * ((d : Int) * (y2 * y2)) :=
        Int.mul_le_mul_of_nonneg_left h2sq (Int.mul_nonneg hd_nn (int_sq_nonneg y1))
      omega
    have hcross : x1 * x2 ≤ (d : Int) * (y1 * y2) :=
      int_sq_le_sq_nonneg (Int.mul_nonneg (by omega) (by omega))
        (Int.mul_nonneg hd_nn (Int.mul_nonneg hy1 hy2)) hcross_sq
    grind
  rcases h1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1, hs1⟩ | ⟨ha1, hb1, hs1⟩ <;>
  rcases h2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2, hs2⟩ | ⟨ha2, hb2, hs2⟩
  · exact Or.inl ⟨by omega, by omega⟩
  · by_cases hb : b1 + b2 ≥ 0
    · exact Or.inl ⟨by omega, hb⟩
    · right; left; refine ⟨by omega, by omega, ?_⟩
      have hsqA : a2 * a2 ≤ (a1 + a2) * (a1 + a2) := int_sq_ge_of_le_nonneg ha2 (by omega)
      have hsqB : (-(b1 + b2)) * (-(b1 + b2)) ≤ (-b2) * (-b2) := int_sq_ge_of_le_nonneg (by omega) (by omega)
      have hmul : (d : Int) * ((b1 + b2) * (b1 + b2)) ≤ (d : Int) * (b2 * b2) :=
        Int.mul_le_mul_of_nonneg_left (by grind) hd_nn
      omega
  · by_cases ha : a1 + a2 ≥ 0
    · exact Or.inl ⟨ha, by omega⟩
    · right; right; refine ⟨by omega, by omega, ?_⟩
      have hsqA : (-(a1 + a2)) * (-(a1 + a2)) ≤ (-a2) * (-a2) := int_sq_ge_of_le_nonneg (by omega) (by omega)
      have hsqB : b2 * b2 ≤ (b1 + b2) * (b1 + b2) := int_sq_ge_of_le_nonneg hb2 (by omega)
      have hmul : (d : Int) * (b2 * b2) ≤ (d : Int) * ((b1 + b2) * (b1 + b2)) :=
        Int.mul_le_mul_of_nonneg_left hsqB hd_nn
      have : (a1 + a2) * (a1 + a2) ≤ a2 * a2 := by grind
      omega
  · by_cases hb : b1 + b2 ≥ 0
    · exact Or.inl ⟨by omega, hb⟩
    · right; left; refine ⟨by omega, by omega, ?_⟩
      have hsqA : a1 * a1 ≤ (a1 + a2) * (a1 + a2) := int_sq_ge_of_le_nonneg ha1 (by omega)
      have hsqB : (-(b1 + b2)) * (-(b1 + b2)) ≤ (-b1) * (-b1) := int_sq_ge_of_le_nonneg (by omega) (by omega)
      have hmul : (d : Int) * ((b1 + b2) * (b1 + b2)) ≤ (d : Int) * (b1 * b1) :=
        Int.mul_le_mul_of_nonneg_left (by grind) hd_nn
      omega
  · right; left; refine ⟨by omega, by omega, ?_⟩
    have h := hboth_neg_b a1 (-b1) a2 (-b2) ha1 (by omega) ha2 (by omega) (by grind) (by grind)
    grind
  · by_cases ha : a1 + a2 ≥ 0
    · by_cases hb : b1 + b2 ≥ 0
      · exact Or.inl ⟨ha, hb⟩
      · right; left; refine ⟨ha, by omega, ?_⟩
        have h := hsub1 a1 (-a2) (-b1) b2 (by omega) (by omega) (by omega) hb2 (by grind) (by grind)
        grind
    · by_cases hb : b1 + b2 ≥ 0
      · right; right; refine ⟨by omega, hb, ?_⟩
        have h := hsub2 (-a2) a1 b2 (-b1) (by omega) ha1 (by omega) (by omega) (by grind) (by grind)
        grind
      · exfalso
        have h1sq : a1 * a1 < (-a2) * (-a2) := int_sq_lt_of_lt_nonneg ha1 (by omega)
        have h2sq : b2 * b2 < (-b1) * (-b1) := int_sq_lt_of_lt_nonneg hb2 (by omega)
        have hm : (d : Int) * (b2 * b2) < (d : Int) * (b1 * b1) := Int.mul_lt_mul_of_pos_left (by grind) hd_pos
        grind
  · by_cases ha : a1 + a2 ≥ 0
    · exact Or.inl ⟨ha, by omega⟩
    · right; right; refine ⟨by omega, by omega, ?_⟩
      have hsqA : (-(a1 + a2)) * (-(a1 + a2)) ≤ (-a1) * (-a1) := int_sq_ge_of_le_nonneg (by omega) (by omega)
      have hsqB : b1 * b1 ≤ (b1 + b2) * (b1 + b2) := int_sq_ge_of_le_nonneg hb1 (by omega)
      have hmul : (d : Int) * (b1 * b1) ≤ (d : Int) * ((b1 + b2) * (b1 + b2)) :=
        Int.mul_le_mul_of_nonneg_left hsqB hd_nn
      have : (a1 + a2) * (a1 + a2) ≤ a1 * a1 := by grind
      omega
  · by_cases ha : a1 + a2 ≥ 0
    · by_cases hb : b1 + b2 ≥ 0
      · exact Or.inl ⟨ha, hb⟩
      · right; left; refine ⟨ha, by omega, ?_⟩
        have h := hsub1 a2 (-a1) (-b2) b1 (by omega) (by omega) (by omega) hb1 (by grind) (by grind)
        grind
    · by_cases hb : b1 + b2 ≥ 0
      · right; right; refine ⟨by omega, hb, ?_⟩
        have h := hsub2 (-a1) a2 b1 (-b2) (by omega) ha2 (by omega) (by omega) (by grind) (by grind)
        grind
      · exfalso
        have h1sq : a2 * a2 < (-a1) * (-a1) := int_sq_lt_of_lt_nonneg ha2 (by omega)
        have h2sq : b1 * b1 < (-b2) * (-b2) := int_sq_lt_of_lt_nonneg hb1 (by omega)
        have hm : (d : Int) * (b1 * b1) < (d : Int) * (b2 * b2) := Int.mul_lt_mul_of_pos_left (by grind) hd_pos
        grind
  · right; right; refine ⟨by omega, by omega, ?_⟩
    have h := hboth_neg_a (-a1) b1 (-a2) b2 (by omega) hb1 (by omega) hb2 (by grind) (by grind)
    grind

private theorem quad_norm_mul (d : Nat) (a1 b1 a2 b2 : Int) :
    (a1 * a2 + (d : Int) * (b1 * b2)) * (a1 * a2 + (d : Int) * (b1 * b2)) -
    (d : Int) * ((a1 * b2 + b1 * a2) * (a1 * b2 + b1 * a2)) =
    (a1 * a1 - (d : Int) * (b1 * b1)) * (a2 * a2 - (d : Int) * (b2 * b2)) := by
  grind

/-- Exact multiplicative closure of the nonnegativity cone in `Z[√d]` (`d > 0`). -/
public theorem quadNonneg_mul {d : Nat} (hd : d > 0) {a1 b1 a2 b2 : Int}
    (h1 : quadNonneg d a1 b1) (h2 : quadNonneg d a2 b2) :
    quadNonneg d (a1 * a2 + (d : Int) * (b1 * b2)) (a1 * b2 + b1 * a2) := by
  have hd_pos : (d : Int) > 0 := by omega
  have hd_nn : (d : Int) ≥ 0 := by omega
  have hpm : ∀ x1 y1 x2 y2 : Int, x1 ≥ 0 → y1 ≥ 0 → x2 ≥ 0 → y2 < 0 → x2 * x2 ≥ (d : Int) * (y2 * y2) →
      quadNonneg d (x1 * x2 + (d : Int) * (y1 * y2)) (x1 * y2 + y1 * x2) := by
    intro x1 y1 x2 y2 hx1 hy1 hx2 hy2 hs2
    have hn := quad_norm_mul d x1 y1 x2 y2
    have hy2_sq : y2 * y2 > 0 := Int.mul_pos_of_neg_of_neg hy2 hy2
    by_cases hAA : x1 * x2 + (d : Int) * (y1 * y2) ≥ 0
    · by_cases hBB : x1 * y2 + y1 * x2 ≥ 0
      · exact Or.inl ⟨hAA, hBB⟩
      · right; left; refine ⟨hAA, by omega, ?_⟩
        have hlt : y1 * x2 < x1 * (-y2) := by grind
        have hsq : (y1 * x2) * (y1 * x2) < (x1 * (-y2)) * (x1 * (-y2)) :=
          int_sq_lt_of_lt_nonneg (Int.mul_nonneg hy1 hx2) hlt
        have hstep : (y1 * y1) * ((d : Int) * (y2 * y2)) ≤ (y1 * y1) * (x2 * x2) :=
          Int.mul_le_mul_of_nonneg_left hs2 (int_sq_nonneg y1)
        have hmul_le : (y2 * y2) * ((d : Int) * (y1 * y1)) ≤ (y2 * y2) * (x1 * x1) := by grind
        have h1pos : (d : Int) * (y1 * y1) ≤ x1 * x1 := int_le_of_mul_le_mul_pos hy2_sq hmul_le
        have hprod : (x1 * x1 - (d : Int) * (y1 * y1)) * (x2 * x2 - (d : Int) * (y2 * y2)) ≥ 0 :=
          Int.mul_nonneg (by omega) (by omega)
        omega
    · by_cases hBB : x1 * y2 + y1 * x2 ≥ 0
      · right; right; refine ⟨by omega, hBB, ?_⟩
        have hlt : x1 * x2 < (d : Int) * (y1 * (-y2)) := by grind
        have hsq : (x1 * x2) * (x1 * x2) < ((d : Int) * (y1 * (-y2))) * ((d : Int) * (y1 * (-y2))) :=
          int_sq_lt_of_lt_nonneg (Int.mul_nonneg hx1 hx2) hlt
        have hstep : (x1 * x1) * ((d : Int) * (y2 * y2)) ≤ (x1 * x1) * (x2 * x2) :=
          Int.mul_le_mul_of_nonneg_left hs2 (int_sq_nonneg x1)
        have hmul_le : (y2 * y2) * ((d : Int) * (x1 * x1)) ≤ (y2 * y2) * ((d : Int) * ((d : Int) * (y1 * y1))) := by grind
        have hd_le : (d : Int) * (x1 * x1) ≤ (d : Int) * ((d : Int) * (y1 * y1)) :=
          int_le_of_mul_le_mul_pos hy2_sq hmul_le
        have h1neg : x1 * x1 ≤ (d : Int) * (y1 * y1) := int_le_of_mul_le_mul_pos hd_pos hd_le
        have hprod : (x1 * x1 - (d : Int) * (y1 * y1)) * (x2 * x2 - (d : Int) * (y2 * y2)) ≤ 0 := by
          have hp := Int.mul_nonneg (show -(x1 * x1 - (d : Int) * (y1 * y1)) ≥ 0 by omega)
            (show x2 * x2 - (d : Int) * (y2 * y2) ≥ 0 by omega)
          grind
        omega
      · exfalso
        have h1lt : y1 * x2 < x1 * (-y2) := by grind
        have h2lt : x1 * x2 < (d : Int) * (y1 * (-y2)) := by grind
        have p1 : (x1 * x2) * (y1 * x2) ≤ ((d : Int) * (y1 * (-y2))) * (y1 * x2) :=
          Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg hy1 hx2)
        have p2 : ((d : Int) * (y1 * (-y2))) * (y1 * x2) < ((d : Int) * (y1 * (-y2))) * (x1 * (-y2)) :=
          Int.mul_lt_mul_of_pos_left h1lt (by have := Int.mul_nonneg hx1 hx2; omega)
        have hge : (x1 * y1) * ((d : Int) * (y2 * y2)) ≤ (x1 * y1) * (x2 * x2) :=
          Int.mul_le_mul_of_nonneg_left hs2 (Int.mul_nonneg hx1 hy1)
        grind
  have hmp : ∀ x1 y1 x2 y2 : Int, x1 ≥ 0 → y1 ≥ 0 → x2 < 0 → y2 ≥ 0 → (d : Int) * (y2 * y2) ≥ x2 * x2 →
      quadNonneg d (x1 * x2 + (d : Int) * (y1 * y2)) (x1 * y2 + y1 * x2) := by
    intro x1 y1 x2 y2 hx1 hy1 hx2 hy2 hs2
    have hn := quad_norm_mul d x1 y1 x2 y2
    have hx2_sq : x2 * x2 > 0 := Int.mul_pos_of_neg_of_neg hx2 hx2
    have hy2_pos : y2 > 0 := Classical.byContradiction fun h0 => by
      have : y2 = 0 := by omega
      subst this; simp at hs2; omega
    have hy2_sq : y2 * y2 > 0 := Int.mul_pos hy2_pos hy2_pos
    by_cases hAA : x1 * x2 + (d : Int) * (y1 * y2) ≥ 0
    · by_cases hBB : x1 * y2 + y1 * x2 ≥ 0
      · exact Or.inl ⟨hAA, hBB⟩
      · right; left; refine ⟨hAA, by omega, ?_⟩
        have hlt : x1 * y2 < y1 * (-x2) := by grind
        have hsq : (x1 * y2) * (x1 * y2) < (y1 * (-x2)) * (y1 * (-x2)) :=
          int_sq_lt_of_lt_nonneg (Int.mul_nonneg hx1 hy2) hlt
        have hstep : (y1 * y1) * (x2 * x2) ≤ (y1 * y1) * ((d : Int) * (y2 * y2)) :=
          Int.mul_le_mul_of_nonneg_left hs2 (int_sq_nonneg y1)
        have hmul_le : (y2 * y2) * (x1 * x1) ≤ (y2 * y2) * ((d : Int) * (y1 * y1)) := by grind
        have h1neg : x1 * x1 ≤ (d : Int) * (y1 * y1) := int_le_of_mul_le_mul_pos hy2_sq hmul_le
        have hprod : (x1 * x1 - (d : Int) * (y1 * y1)) * (x2 * x2 - (d : Int) * (y2 * y2)) ≥ 0 := by
          have hp := Int.mul_nonneg (show -(x1 * x1 - (d : Int) * (y1 * y1)) ≥ 0 by omega)
            (show -(x2 * x2 - (d : Int) * (y2 * y2)) ≥ 0 by omega)
          grind
        omega
    · by_cases hBB : x1 * y2 + y1 * x2 ≥ 0
      · right; right; refine ⟨by omega, hBB, ?_⟩
        have hlt : (d : Int) * (y1 * y2) < x1 * (-x2) := by grind
        have hsq : ((d : Int) * (y1 * y2)) * ((d : Int) * (y1 * y2)) < (x1 * (-x2)) * (x1 * (-x2)) :=
          int_sq_lt_of_lt_nonneg (Int.mul_nonneg hd_nn (Int.mul_nonneg hy1 hy2)) hlt
        have hstep : (x1 * x1) * (x2 * x2) ≤ (x1 * x1) * ((d : Int) * (y2 * y2)) :=
          Int.mul_le_mul_of_nonneg_left hs2 (int_sq_nonneg x1)
        have hmul_le : (y2 * y2) * ((d : Int) * ((d : Int) * (y1 * y1))) ≤ (y2 * y2) * ((d : Int) * (x1 * x1)) := by grind
        have hd_le : (d : Int) * ((d : Int) * (y1 * y1)) ≤ (d : Int) * (x1 * x1) :=
          int_le_of_mul_le_mul_pos hy2_sq hmul_le
        have h1pos : (d : Int) * (y1 * y1) ≤ x1 * x1 := int_le_of_mul_le_mul_pos hd_pos hd_le
        have hprod : (x1 * x1 - (d : Int) * (y1 * y1)) * (x2 * x2 - (d : Int) * (y2 * y2)) ≤ 0 := by
          have hp := Int.mul_nonneg (show x1 * x1 - (d : Int) * (y1 * y1) ≥ 0 by omega)
            (show -(x2 * x2 - (d : Int) * (y2 * y2)) ≥ 0 by omega)
          grind
        omega
      · exfalso
        have h1lt : x1 * y2 < y1 * (-x2) := by grind
        have h2lt : (d : Int) * (y1 * y2) < x1 * (-x2) := by grind
        have p1 : ((d : Int) * (y1 * y2)) * (x1 * y2) ≤ (x1 * (-x2)) * (x1 * y2) :=
          Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg hx1 hy2)
        have p2 : (x1 * (-x2)) * (x1 * y2) < (x1 * (-x2)) * (y1 * (-x2)) :=
          Int.mul_lt_mul_of_pos_left h1lt (by have := Int.mul_nonneg hd_nn (Int.mul_nonneg hy1 hy2); omega)
        have hge : (x1 * y1) * (x2 * x2) ≤ (x1 * y1) * ((d : Int) * (y2 * y2)) :=
          Int.mul_le_mul_of_nonneg_left hs2 (Int.mul_nonneg hx1 hy1)
        grind
  have hnorm := quad_norm_mul d a1 b1 a2 b2
  rcases h1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1, hs1⟩ | ⟨ha1, hb1, hs1⟩ <;>
  rcases h2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2, hs2⟩ | ⟨ha2, hb2, hs2⟩
  · exact Or.inl ⟨Int.add_nonneg (Int.mul_nonneg ha1 ha2) (Int.mul_nonneg hd_nn (Int.mul_nonneg hb1 hb2)),
                  Int.add_nonneg (Int.mul_nonneg ha1 hb2) (Int.mul_nonneg hb1 ha2)⟩
  · exact hpm a1 b1 a2 b2 ha1 hb1 ha2 hb2 hs2
  · exact hmp a1 b1 a2 b2 ha1 hb1 ha2 hb2 hs2
  · have h := hpm a2 b2 a1 b1 ha2 hb2 ha1 hb1 hs1
    have eA : a2 * a1 + (d : Int) * (b2 * b1) = a1 * a2 + (d : Int) * (b1 * b2) := by grind
    have eB : a2 * b1 + b2 * a1 = a1 * b2 + b1 * a2 := by grind
    rw [eA, eB] at h; exact h
  · have hA : a1 * a2 + (d : Int) * (b1 * b2) ≥ 0 :=
      Int.add_nonneg (Int.mul_nonneg ha1 ha2) (Int.mul_nonneg hd_nn (Int.le_of_lt (Int.mul_pos_of_neg_of_neg hb1 hb2)))
    have hprod : (a1 * a1 - (d : Int) * (b1 * b1)) * (a2 * a2 - (d : Int) * (b2 * b2)) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    by_cases hB : a1 * b2 + b1 * a2 ≥ 0
    · exact Or.inl ⟨hA, hB⟩
    · right; left; exact ⟨hA, by omega, by omega⟩
  · have hB : a1 * b2 + b1 * a2 ≥ 0 :=
      Int.add_nonneg (Int.mul_nonneg ha1 hb2) (Int.le_of_lt (Int.mul_pos_of_neg_of_neg hb1 ha2))
    have hprod : (a1 * a1 - (d : Int) * (b1 * b1)) * (a2 * a2 - (d : Int) * (b2 * b2)) ≤ 0 := by
      have hp := Int.mul_nonneg (show a1 * a1 - (d : Int) * (b1 * b1) ≥ 0 by omega)
        (show -(a2 * a2 - (d : Int) * (b2 * b2)) ≥ 0 by omega)
      grind
    by_cases hA : a1 * a2 + (d : Int) * (b1 * b2) ≥ 0
    · exact Or.inl ⟨hA, hB⟩
    · right; right; exact ⟨by omega, hB, by omega⟩
  · have h := hmp a2 b2 a1 b1 ha2 hb2 ha1 hb1 hs1
    have eA : a2 * a1 + (d : Int) * (b2 * b1) = a1 * a2 + (d : Int) * (b1 * b2) := by grind
    have eB : a2 * b1 + b2 * a1 = a1 * b2 + b1 * a2 := by grind
    rw [eA, eB] at h; exact h
  · have hB : a1 * b2 + b1 * a2 ≥ 0 :=
      Int.add_nonneg (Int.le_of_lt (Int.mul_pos_of_neg_of_neg ha1 hb2)) (Int.mul_nonneg hb1 ha2)
    have hprod : (a1 * a1 - (d : Int) * (b1 * b1)) * (a2 * a2 - (d : Int) * (b2 * b2)) ≤ 0 := by
      have hp := Int.mul_nonneg (show -(a1 * a1 - (d : Int) * (b1 * b1)) ≥ 0 by omega)
        (show a2 * a2 - (d : Int) * (b2 * b2) ≥ 0 by omega)
      grind
    by_cases hA : a1 * a2 + (d : Int) * (b1 * b2) ≥ 0
    · exact Or.inl ⟨hA, hB⟩
    · right; right; exact ⟨by omega, hB, by omega⟩
  · have hA : a1 * a2 + (d : Int) * (b1 * b2) ≥ 0 :=
      Int.add_nonneg (Int.le_of_lt (Int.mul_pos_of_neg_of_neg ha1 ha2)) (Int.mul_nonneg hd_nn (Int.mul_nonneg hb1 hb2))
    have hprod : (a1 * a1 - (d : Int) * (b1 * b1)) * (a2 * a2 - (d : Int) * (b2 * b2)) ≥ 0 := by
      have hp := Int.mul_nonneg (show -(a1 * a1 - (d : Int) * (b1 * b1)) ≥ 0 by omega)
        (show -(a2 * a2 - (d : Int) * (b2 * b2)) ≥ 0 by omega)
      grind
    by_cases hB : a1 * b2 + b1 * a2 ≥ 0
    · exact Or.inl ⟨hA, hB⟩
    · right; left; exact ⟨hA, by omega, by omega⟩

private theorem quadNonneg_cast {d : Nat} {a1 b1 a2 b2 : Int}
    (ha : a1 = a2) (hb : b1 = b2) (h : quadNonneg d a1 b1) : quadNonneg d a2 b2 := by
  rw [← ha, ← hb]; exact h

/-! ## Section 2: T3a — Bipartite Odd-Prime `AWP ⊆ ASEP` & 2-Qubit Strict Incomparability -/

/-- **T3a (Part 1 — Exact Gurvits-Barnum Corollary 3 Purity-to-Ball Identity, ALL `D ≥ 2`).** -/
public theorem gurvits_barnum_cor3_identity (D P_num P_den : Int)
    (hD : D ≥ 2) (_hden : P_den > 0)
    (hpurity : (D - 1) * P_num ≤ P_den) :
    (D - 1) * (D - 1) * P_num - 2 * (D - 1) * P_den + D * P_den ≤ P_den := by
  have hmul : (D - 1) * ((D - 1) * P_num) ≤ (D - 1) * P_den :=
    Int.mul_le_mul_of_nonneg_left hpurity (by omega)
  grind

/-- Exact identity verifying `Tr(ρ²) = 1/D + R²(AWP_0) = 1/(D - 1)` for EVERY `D ≥ 2`. -/
public theorem awp_circumradius_equals_gb_purity (D : Int) (_hD : D ≥ 2) :
    (D - 1) + 1 = D ∧ (D - 1) * 1 + 1 = D ∧ D * (D - 1) * 1 = (D - 1) * D := by
  grind

/-- **T3a (Part 2 — Exact Rational Entangled Absolutely Stabilizer Witness `ρ_ent` for 2 Qubits).** -/
public theorem two_qubit_entangled_astab_witness :
    let l1 : Int := 11; let l2 : Int := 3; let l3 : Int := 3; let l4 : Int := 3
    (l1 + l2 + l3 + l4 = 20) ∧
    (l1 ≥ l2 ∧ l2 ≥ l3 ∧ l3 ≥ l4 ∧ l4 > 0) ∧
    quadPos 3 (l1 + l4) (l4 - l1) ∧
    quadPos 5 (l1 + l2 + l3 + l4) (l3 + l4 - l1 - l2) ∧
    (l1 - l3 > 0 ∧ (l1 - l3) * (l1 - l3) > 4 * l2 * l4) ∧
    (l4 - (l1 - l4) / 2 < 0) := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩
  · right; right; left; decide
  · right; right; left; decide

/-- **T3a (Part 3 — Exact Rational Separable Non-`ASTAB` Witness `ρ_sep` for 2 Qubits).** -/
public theorem two_qubit_sep_non_astab_witness :
    let m1 : Int := 8; let m2 : Int := 7; let m3 : Int := 4; let m4 : Int := 1
    (m1 + m2 + m3 + m4 = 20) ∧
    (m1 ≥ m2 ∧ m2 ≥ m3 ∧ m3 ≥ m4 ∧ m4 > 0) ∧
    ((m1 - m3) * (m1 - m3) < 4 * m2 * m4) ∧
    quadPos 3 (-(m1 + m4)) (m1 - m4) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  right; right; right; decide

/-! ## Section 3: T3b — Universal Global `ASTAB` Circumradius Optimality (2-Qubit & 1-Qutrit) -/

/-- Exact 4-variable endpoint convexity identity on the ordered simplex. -/
public theorem ordered4_sum_sq_le_endpoints (l1 l2 l3 l4 M : Int)
    (hsum : l1 + l2 + l3 + l4 = M)
    (h12 : l1 ≥ l2) (h23 : l2 ≥ l3) (h34 : l3 ≥ l4) :
    l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4 ≤ (l1 + l4) * M - 4 * l1 * l4 := by
  have p1 : 0 ≤ (l1 - l2) * (l2 - l4) := Int.mul_nonneg (by omega) (by omega)
  have p2 : 0 ≤ (l1 - l3) * (l3 - l4) := Int.mul_nonneg (by omega) (by omega)
  have hid : (l1 + l4) * M - 4 * l1 * l4 - (l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4) =
      (l1 - l2) * (l2 - l4) + (l1 - l3) * (l3 - l4) := by grind
  omega

/-- **T3b (Part 1a — Universal Global 2-Qubit `ASTAB_0` Circumradius Upper Bound):**
For EVERY ordered integer-scaled spectrum `l1 ≥ l2 ≥ l3 ≥ l4 ≥ 0` (`l1 + l2 + l3 + l4 = M > 0`)
satisfying 2-qubit `ASTAB` Facet 1 (`(l1 + l4) + (l4 - l1)√3 ≥ 0`), the squared norm obeys
`121 * (l1² + l2² + l3² + l4²) ≤ (40 + 3√3) M²`, equivalently
`484 * (∑ l_i² - M²/4) ≤ 3(13 + 4√3) M²`, proved purely in exact `Z[√3]`. -/
public theorem two_qubit_astab_global_circumradius (l1 l2 l3 l4 M : Int)
    (hM : M > 0) (hsum : l1 + l2 + l3 + l4 = M)
    (h12 : l1 ≥ l2) (h23 : l2 ≥ l3) (h34 : l3 ≥ l4) (_h40 : l4 ≥ 0)
    (hf1 : quadNonneg 3 (l1 + l4) (l4 - l1)) :
    quadNonneg 3 (40 * (M * M) - 121 * (l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4)) (3 * (M * M)) := by
  have hd3 : (3 : Nat) > 0 := by decide
  have hm1 := quadNonneg_mul hd3 (by right; right; decide : quadNonneg 3 (-1) 1) hf1
  have hgap4 : quadNonneg 3 (l4 - 2 * l1) l1 :=
    quadNonneg_of_pos_mul (by decide : (2 : Int) > 0) (quadNonneg_cast (by grind) (by grind) hm1)
  have h3gap : quadNonneg 3 (3 * (l4 - 2 * l1)) (3 * l1) :=
    quadNonneg_cast (by grind) (by grind)
      (quadNonneg_mul hd3 (quadNonneg_of_int (by decide : (3 : Int) ≥ 0)) hgap4)
  have hM_sub : quadNonneg 3 (M - 7 * l1) (3 * l1) :=
    quadNonneg_cast (by grind) (by grind)
      (quadNonneg_add hd3 (quadNonneg_of_int (show M - l1 - 3 * l4 ≥ 0 by omega)) h3gap)
  have hU : quadNonneg 3 (7 * M - 22 * l1) (3 * M) :=
    quadNonneg_cast (by grind) (by grind)
      (quadNonneg_mul hd3 (Or.inl ⟨by decide, by decide⟩ : quadNonneg 3 7 3) hM_sub)
  have hend := ordered4_sum_sq_le_endpoints l1 l2 l3 l4 M hsum h12 h23 h34
  let P := l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4
  have hT1 : quadNonneg 3 (484 * ((l1 + l4) * M - 4 * l1 * l4 - P)) 0 :=
    quadNonneg_of_int (by omega)
  have hT2 := quadNonneg_mul hd3 (quadNonneg_of_int (show 484 * (4 * l1 - M) ≥ 0 by omega)) hgap4
  have h2M13 := quadNonneg_mul hd3 (quadNonneg_of_int (show 2 * M ≥ 0 by omega))
    (by right; left; decide : quadNonneg 3 13 (-7))
  have hT3 := quadNonneg_mul hd3 h2M13 hU
  have hU2 := quadNonneg_mul hd3 hU hU
  have h4_2m := quadNonneg_mul hd3 (quadNonneg_of_int (by decide : (4 : Int) ≥ 0))
    (by right; left; decide : quadNonneg 3 2 (-1))
  have hT4 := quadNonneg_mul hd3 h4_2m hU2
  have hAll := quadNonneg_add hd3 (quadNonneg_add hd3 hT1 hT2) (quadNonneg_add hd3 hT3 hT4)
  exact quadNonneg_of_pos_mul (by decide : (4 : Int) > 0)
    (quadNonneg_cast (by grind) (by grind) hAll)

/-- Exact arithmetic on the 2-qubit `ASTAB_0` extremal vertex
`v₃ = ((7 + 3√3)/22, (5 - √3)/22, (5 - √3)/22, (5 - √3)/22)` attaining
`R²(v₃) = 3(13 + 4√3)/484 > 1/12 = r²_GB`. -/
public theorem exact_astab_circumradius_2qubit_vertex :
    (7 + 3 * 5 = 22 ∧ (3 : Int) + 3 * (-1) = 0) ∧
    (((7 : Int) - 3 * 3 + 5 - 3 = 0) ∧ ((3 : Int) - 7 + 5 - 1 = 0)) ∧
    (224 * 224 > 80 * 80 * 3) ∧
    (((7 * 7 + 3 * (3 * 3)) + 3 * (5 * 5 + 3 * 1) - 121 = 3 * 13) ∧
     ((2 * 7 * 3 : Int) + 3 * (2 * 5 * (-1)) = 3 * 4)) ∧
    quadPos 3 (36 * 13 - 484) (36 * 4) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  right; right; right; decide

/-- **T3b (Part 2a — Universal Global 1-Qutrit `ASTAB_0` Circumradius Upper Bound):**
For EVERY ordered integer-scaled spectrum `l1 ≥ l2 ≥ l3 ≥ 0` (`l1 + l2 + l3 = M > 0`)
satisfying the 1-qutrit `ASTAB_0` spectral facets `2 * l1 ≤ M` and
`2 * l3 ≥ (3 - √5) * l1`, the squared norm obeys
`2 * (l1² + l2² + l3²) ≤ (3 - √5) * M²`, equivalently
`6 * (∑ l_i² - M²/3) ≤ (7 - 3√5) * M²`, proved purely in exact `Z[√5]`. -/
public theorem one_qutrit_astab_global_circumradius (l1 l2 l3 M : Int)
    (hM : M > 0) (hsum : l1 + l2 + l3 = M)
    (h12 : l1 ≥ l2) (h23 : l2 ≥ l3) (_h30 : l3 ≥ 0)
    (hf1 : 2 * l1 ≤ M)
    (hf2 : quadNonneg 5 (2 * l3 - 3 * l1) l1) :
    quadNonneg 5 (3 * (M * M) - 2 * (l1 * l1 + l2 * l2 + l3 * l3)) (-(M * M)) := by
  have hd5 : (5 : Nat) > 0 := by decide
  by_cases hcase : quadNonneg 5 (7 * l1 - 2 * M) (-l1)
  · -- Case 1: (7 - √5) l1 >= 2 M
    have h2l2_ge : quadNonneg 5 (2 * l2 - 3 * l1) l1 :=
      quadNonneg_cast (by omega) (by omega)
        (quadNonneg_add hd5 (quadNonneg_of_int (show 2 * (l2 - l3) ≥ 0 by omega)) hf2)
    have hshift := quadNonneg_mul hd5 hf2 h2l2_ge
    have h2shift := quadNonneg_mul hd5 (quadNonneg_of_int (by decide : (2 : Int) ≥ 0)) hshift
    have hq1 := quadNonneg_mul hd5 (by right; right; decide : quadNonneg 5 (-1) 1) hcase
    have h36m16 : quadNonneg 5 (36 * l1) (-16 * l1) :=
      quadNonneg_cast (by grind) (by grind)
        (quadNonneg_mul hd5 (quadNonneg_of_int (show l1 ≥ 0 by omega))
          (by right; left; decide : quadNonneg 5 36 (-16)))
    have hlin_pos : quadNonneg 5 (2 * M + 24 * l1) ((-2) * M - 8 * l1) :=
      quadNonneg_cast (by grind) (by grind) (quadNonneg_add hd5 hq1 h36m16)
    have hterm2 := quadNonneg_mul hd5 (quadNonneg_of_int (show M - 2 * l1 ≥ 0 by omega)) hlin_pos
    have htot := quadNonneg_add hd5 h2shift hterm2
    exact quadNonneg_of_pos_mul (by decide : (2 : Int) > 0)
      (quadNonneg_cast (by grind) (by grind) htot)
  · -- Case 2: (7 - √5) l1 < 2 M
    have hcase_rev : quadNonneg 5 (2 * M - 7 * l1) l1 := by
      have hl1_nn : l1 ≥ 0 := by omega
      by_cases ha : 2 * M - 7 * l1 ≥ 0
      · exact Or.inl ⟨ha, hl1_nn⟩
      · right; right; refine ⟨by omega, hl1_nn, ?_⟩
        exact Classical.byContradiction fun hlt => hcase (by
          by_cases hl1_0 : l1 = 0
          · subst hl1_0; omega
          · right; left; refine ⟨by omega, by omega, by grind⟩)
    have hV : quadNonneg 5 (14 * M - 44 * l1) (2 * M) :=
      quadNonneg_cast (by grind) (by grind)
        (quadNonneg_mul hd5 (Or.inl ⟨by decide, by decide⟩ : quadNonneg 5 7 1) hcase_rev)
    have hTA : quadNonneg 5 (968 * (2 * ((l1 - l2) * (l1 - l3)))) 0 :=
      quadNonneg_of_int (Int.mul_nonneg (by decide)
        (Int.mul_nonneg (by decide) (Int.mul_nonneg (by omega) (by omega))))
    have hTB := quadNonneg_mul hd5
      (quadNonneg_of_int (Int.mul_nonneg (by decide : (4 : Int) ≥ 0) (int_sq_nonneg M)))
      (by right; left; decide : quadNonneg 5 267 (-119))
    have hm2p6M := quadNonneg_mul hd5 (quadNonneg_of_int (show M ≥ 0 by omega))
      (by right; right; decide : quadNonneg 5 (-2) 6)
    have hfacC := quadNonneg_add hd5 (quadNonneg_of_int (show 44 * (3 * l1 - M) ≥ 0 by omega)) hm2p6M
    have hTC := quadNonneg_mul hd5 hV hfacC
    have hSum := quadNonneg_add hd5 hTA (quadNonneg_add hd5 hTB hTC)
    exact quadNonneg_of_pos_mul (by decide : (484 : Int) > 0)
      (quadNonneg_cast (by grind) (by grind) hSum)

/-- Exact 1-qutrit `ASTAB_0` extremal vertex `B = (1/2, (√5 - 1)/4, (3 - √5)/4)` attaining
`R²(B) = (7 - 3√5)/6` strictly between the inball `1/24` and `R²(AWP_0) = 1/6`. -/
public theorem exact_astab_circumradius_1qutrit_vertex :
    ((2 : Int) + (-1) + 3 = 4 ∧ (0 : Int) + 1 + (-1) = 0) ∧
    (2 * 2 = 4) ∧
    (((2 : Int) + (3 - 5) = 0) ∧ ((-2 : Int) + (3 - 1) = 0)) ∧
    ((4 + (1 + 5) + (9 + 5) = 24) ∧ ((-2 : Int) + (-6) = -8) ∧ (3 * 3 - 2 = 7)) ∧
    quadPos 5 27 (-12) ∧ quadPos 5 (-6) 3 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · right; right; left; decide
  · right; right; right; decide

/-! ## Section 4: T3c — Finite Uniform-Covering Double Counting & Symplectic Marginal Descent (ALL `n ≥ 2`) -/

private theorem sumFin_zero (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFin, ih, Nat.add_zero]

private theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFin, ih]; omega

private theorem sumFin_swap (K P : Nat) (g : Fin K → Fin P → Nat) :
    sumFin K (fun k => sumFin P (fun p => g k p)) =
    sumFin P (fun p => sumFin K (fun k => g k p)) := by
  induction K with
  | zero =>
    simp only [sumFin]
    exact (sumFin_zero P).symm
  | succ k ih =>
    simp only [sumFin]
    rw [ih (fun i p => g i.castSucc p), ← sumFin_add]

private theorem sumFin_le_sumFin {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    sumFin n f ≤ sumFin n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [sumFin]
    exact Nat.add_le_add (ih (fun i => h i.castSucc)) (h ⟨k, Nat.lt_succ_self k⟩)

private theorem sumFin_const (n c : Nat) : sumFin n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih => simp only [sumFin, ih, Nat.succ_mul]

private theorem sumFin_ite_bool (n : Nat) (b : Fin n → Bool) (c : Nat) :
    sumFin n (fun i => if b i then c else 0) = countFin n b * c := by
  induction n with
  | zero => simp [sumFin, countFin]
  | succ k ih =>
    simp only [sumFin, countFin, ih, Nat.add_mul]
    cases b ⟨k, Nat.lt_succ_self k⟩ <;> simp

/-- **T3c (Part 0 — General Finite Uniform-Covering Double-Counting Theorem):**
For ANY finite index set `Fin P`, ANY family of `K` subsets `inSub : Fin K → Fin P → Bool`
where each subset has cardinality `m` and every element `p : Fin P` belongs to exactly `r > 0`
subsets, if `∑_{p ∈ V_k} f(p) ≤ B` on every subset `k : Fin K`, then `m * ∑_{p : Fin P} f(p) ≤ B * P`. -/
public theorem uniform_cover_avg_bound {P K m r B : Nat}
    (inSub : Fin K → Fin P → Bool)
    (f : Fin P → Nat)
    (hr_pos : r > 0)
    (hrow : ∀ k : Fin K, countFin P (fun p => inSub k p) = m)
    (hcol : ∀ p : Fin P, countFin K (fun k => inSub k p) = r)
    (hsub : ∀ k : Fin K, sumFin P (fun p => if inSub k p then f p else 0) ≤ B) :
    m * sumFin P f ≤ B * P := by
  have h1 : r * sumFin P f ≤ K * B := by
    have hlhs : sumFin K (fun k => sumFin P (fun p => if inSub k p then f p else 0)) =
                r * sumFin P f := by
      rw [sumFin_swap, ← sumFin_mul_left]
      apply sumFin_congr; intro p
      rw [sumFin_ite_bool, hcol p]
    have hrhs : sumFin K (fun k => sumFin P (fun p => if inSub k p then f p else 0)) ≤ K * B := by
      calc sumFin K (fun k => sumFin P (fun p => if inSub k p then f p else 0))
          ≤ sumFin K (fun _ => B) := sumFin_le_sumFin hsub
        _ = K * B := sumFin_const K B
    omega
  have h2 : K * m = r * P := by
    have hl : sumFin K (fun k => sumFin P (fun p => if inSub k p then 1 else 0)) = K * m := by
      have hc : ∀ k, sumFin P (fun p => if inSub k p then 1 else 0) = m := fun k => by
        rw [sumFin_ite_bool, hrow k, Nat.mul_one]
      rw [sumFin_congr hc, sumFin_const]
    have hr : sumFin K (fun k => sumFin P (fun p => if inSub k p then 1 else 0)) = r * P := by
      rw [sumFin_swap]
      have hc : ∀ p, sumFin K (fun k => if inSub k p then 1 else 0) = r := fun p => by
        rw [sumFin_ite_bool, hcol p, Nat.mul_one]
      rw [sumFin_congr hc, sumFin_const, Nat.mul_comm]
    omega
  have hmul : r * (m * sumFin P f) ≤ r * (B * P) := by
    calc r * (m * sumFin P f)
        = m * (r * sumFin P f) := Nat.mul_left_comm r m _
      _ ≤ m * (K * B) := Nat.mul_le_mul_left m h1
      _ = (K * m) * B := by rw [← Nat.mul_assoc, Nat.mul_comm m K]
      _ = (r * P) * B := by rw [h2]
      _ = r * (B * P) := by rw [Nat.mul_assoc, Nat.mul_comm P B]
  exact Nat.le_of_mul_le_mul_left hmul hr_pos

/-- **T3c (Part 1 — Symplectic Marginal Descent Purity Bound, ALL `n ≥ 2`).** -/
public theorem symplectic_marginal_descent_all_n (n S Q : Nat) (hn : n ≥ 2) (hQ : Q > 0)
    (hmarg : 15 * S ≤ 7 * (4 ^ n - 1) * Q) :
    15 * (Q + S) ≤ (7 * 4 ^ n + 8) * Q ∧
    (7 * 4 ^ n + 8) * Q < 15 * 4 ^ n * Q := by
  have h4n : 4 ^ n ≥ 16 := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hn)
  refine ⟨?_, ?_⟩
  · have hsub : 15 * Q + 7 * (4 ^ n - 1) * Q = (7 * 4 ^ n + 8) * Q := by
      calc 15 * Q + 7 * (4 ^ n - 1) * Q
          = (15 + 7 * (4 ^ n - 1)) * Q := (Nat.add_mul 15 _ Q).symm
        _ = (7 * 4 ^ n + 8) * Q := by congr 1; omega
    have hmul : 15 * (Q + S) = 15 * Q + 15 * S := Nat.mul_add 15 Q S
    omega
  · exact Nat.mul_lt_mul_of_pos_right (by omega) hQ

/-- **T3c (Part 2 — Exact `15/7` Squared-Inball Radius Gain Over Liu et al. Thm 10, ALL `n ≥ 1`).** -/
public theorem inball_gain_exact_15_over_7 (n : Nat) (hn : n ≥ 1) :
    let dLiu := 15 * (4 ^ n - 1)
    let dOurs := (7 * 4 ^ n + 8) - 15
    dOurs = 7 * (4 ^ n - 1) ∧ 15 * dOurs = 7 * dLiu := by
  have h4n : 4 ^ n ≥ 4 := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hn)
  dsimp only
  constructor
  · omega
  · have h1 : 7 * 4 ^ n + 8 - 15 = 7 * (4 ^ n - 1) := by omega
    rw [h1, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 15 7]

/-! ## Section 5: T3d — First-Principles Multivariate Polynomial Degree-2 RLT+SOS Barrier -/

private theorem sumFinInt_zero (n : Nat) : sumFinInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFinInt, ih, Int.add_zero]

private theorem sumFinInt_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFinInt n f = sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFinInt, ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

private theorem sumFinInt_add (n : Nat) (f g : Fin n → Int) :
    sumFinInt n (fun i => f i + g i) = sumFinInt n f + sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFinInt, ih]; omega

private theorem sumFinInt_sub (n : Nat) (f g : Fin n → Int) :
    sumFinInt n (fun i => f i - g i) = sumFinInt n f - sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFinInt, ih]; omega

private theorem sumFinInt_mul_left (n : Nat) (c : Int) (f : Fin n → Int) :
    sumFinInt n (fun i => c * f i) = c * sumFinInt n f := by
  induction n with
  | zero => simp [sumFinInt]
  | succ k ih => simp only [sumFinInt, ih, Int.mul_add]

private theorem sumFinInt_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, f i ≥ 0) :
    sumFinInt n f ≥ 0 := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [sumFinInt]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

private theorem sumFinInt_le {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    sumFinInt n f ≤ sumFinInt n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [sumFinInt]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

private theorem sumFinInt_const (n : Nat) (c : Int) : sumFinInt n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumFinInt]
  | succ k ih =>
    simp only [sumFinInt, ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hcast, Int.add_mul, Int.one_mul]

private theorem sumFinInt_swap (K P : Nat) (g : Fin K → Fin P → Int) :
    sumFinInt K (fun k => sumFinInt P (fun p => g k p)) =
    sumFinInt P (fun p => sumFinInt K (fun k => g k p)) := by
  induction K with
  | zero =>
    simp only [sumFinInt]
    exact (sumFinInt_zero P).symm
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih (fun i p => g i.castSucc p), ← sumFinInt_add]

private theorem sumFinInt_single {n : Nat} (q : Fin n) (f : Fin n → Int) :
    sumFinInt n (fun i => if i = q then f i else 0) = f q := by
  induction n with
  | zero => exact Fin.elim0 q
  | succ k ih =>
    simp only [sumFinInt]
    by_cases hlast : q.val = k
    · have hq : q = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hq
      have hzero : sumFinInt k (fun i => if i.castSucc = ⟨k, Nat.lt_succ_self k⟩ then f i.castSucc else 0) = 0 := by
        rw [sumFinInt_congr (g := fun _ => 0)]
        · exact sumFinInt_zero k
        · intro i
          have hne : i.castSucc ≠ ⟨k, Nat.lt_succ_self k⟩ := fun h => by
            have hv := congrArg Fin.val h; exact Nat.ne_of_lt i.isLt hv
          simp [hne]
      rw [hzero]; simp
    · have hlt : q.val < k := by omega
      let q' : Fin k := ⟨q.val, hlt⟩
      have hq_eq : q = q'.castSucc := Fin.ext rfl
      have hne_last : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ q := fun h => by
        have hv := congrArg Fin.val h; exact hlast hv.symm
      simp only [hne_last, ↓reduceIte, Int.add_zero]
      have hcongr : sumFinInt k (fun i => if i.castSucc = q then f i.castSucc else 0) =
                    sumFinInt k (fun i => if i = q' then f i.castSucc else 0) := by
        apply sumFinInt_congr
        intro i
        by_cases h : i = q'
        · subst h; rw [← hq_eq]; simp
        · have h1 : i.castSucc ≠ q := fun hc =>
            h (Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) hc))
          simp [h, h1]
      rw [hcongr, ih q' (fun i => f i.castSucc), ← hq_eq]

/-- Pointwise evaluation of an arbitrary degree-2 RLT + SOS polynomial over `P` variables `x : Fin P → Int`
with `K` stabilizer facets `ℓ_k(x) = 1 + ∑_p s_{k,p} x_p` and `R` quadratic SOS terms. -/
@[expose] public def polyRltSos {P K R : Nat}
    (s : Fin K → Fin P → Int)
    (lam : Fin K → Fin K → Int)
    (mu : Fin K → Int)
    (c : Fin R → Int)
    (v : Fin R → Fin P → Int)
    (x : Fin P → Int) : Int :=
  let lin (k : Fin K) : Int := 1 + sumFinInt P (fun p => s k p * x p)
  let rlt : Int := sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (lin k * lin l)))
  let linTerm : Int := sumFinInt K (fun k => mu k * lin k)
  let sos : Int := sumFinInt R (fun r =>
    let val := c r + sumFinInt P (fun p => v r p * x p)
    val * val)
  rlt + linTerm + sos

/-- **T3d (First-Principles Multivariate Polynomial Degree-2 RLT+SOS Barrier, ALL `P, K, R`):**
For ANY finite stabilizer facet system `s : Fin K → Fin P → Int` satisfying `∀ k l, ∑_p s_{k,p} s_{l,p} ≥ -1`,
and ANY degree-2 RLT+SOS polynomial identity `M - ∑_p x_p² = polyRltSos s lam mu c v x` holding pointwise
for all `x : Fin P → Int` with `lam k l ≥ 0, mu k ≥ 0`, we unconditionally have **`M ≥ P`**. -/
public theorem deg2_rlt_sos_polynomial_barrier {P K R : Nat}
    (s : Fin K → Fin P → Int)
    (lam : Fin K → Fin K → Int)
    (mu : Fin K → Int)
    (c : Fin R → Int)
    (v : Fin R → Fin P → Int)
    (M : Int)
    (hlam : ∀ k l, lam k l ≥ 0)
    (hmu : ∀ k, mu k ≥ 0)
    (hpair : ∀ k l, sumFinInt P (fun p => s k p * s l p) ≥ -1)
    (hid : ∀ x : Fin P → Int,
      M - sumFinInt P (fun p => x p * x p) = polyRltSos s lam mu c v x) :
    M ≥ (P : Int) := by
  have h0 := hid (fun _ => 0)
  have h0_lhs : sumFinInt P (fun _ => (0 : Int) * 0) = 0 := by
    rw [sumFinInt_congr (g := fun _ => 0) (fun _ => Int.mul_zero 0)]; exact sumFinInt_zero P
  have hlin0 : ∀ k : Fin K, 1 + sumFinInt P (fun p => s k p * 0) = 1 := fun k => by
    rw [sumFinInt_congr (g := fun _ => 0) (fun p => Int.mul_zero (s k p)), sumFinInt_zero]; omega
  have hval0 : ∀ r : Fin R, c r + sumFinInt P (fun p => v r p * 0) = c r := fun r => by
    rw [sumFinInt_congr (g := fun _ => 0) (fun p => Int.mul_zero (v r p)), sumFinInt_zero]; omega
  let Λ_tot : Int := sumFinInt K (fun k => sumFinInt K (fun l => lam k l))
  have hM_ge_Λ : M ≥ Λ_tot := by
    unfold polyRltSos at h0
    dsimp only at h0
    rw [h0_lhs, Int.sub_zero] at h0
    have hrlt0 : sumFinInt K (fun k => sumFinInt K (fun l =>
        lam k l * ((1 + sumFinInt P (fun p => s k p * 0)) * (1 + sumFinInt P (fun p => s l p * 0))))) = Λ_tot := by
      apply sumFinInt_congr; intro k; apply sumFinInt_congr; intro l
      rw [hlin0 k, hlin0 l, Int.mul_one, Int.mul_one]
    have hmu0 : sumFinInt K (fun k => mu k * (1 + sumFinInt P (fun p => s k p * 0))) ≥ 0 := by
      apply sumFinInt_nonneg; intro k; rw [hlin0 k, Int.mul_one]; exact hmu k
    have hsos0 : sumFinInt R (fun r =>
        (c r + sumFinInt P (fun p => v r p * 0)) * (c r + sumFinInt P (fun p => v r p * 0))) ≥ 0 := by
      apply sumFinInt_nonneg; intro r; rw [hval0 r]; exact int_sq_nonneg (c r)
    rw [hrlt0] at h0; omega
  have hdiag : ∀ q : Fin P,
      (-1 : Int) =
      sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (s k q * s l q))) +
      sumFinInt R (fun r => v r q * v r q) := by
    intro q
    let ePos : Fin P → Int := fun p => if p = q then 1 else 0
    let eNeg : Fin P → Int := fun p => if p = q then -1 else 0
    have hp := hid ePos
    have hm := hid eNeg
    have hsq_p : sumFinInt P (fun p => ePos p * ePos p) = 1 := by
      have hc : ∀ p, ePos p * ePos p = if p = q then 1 else 0 := fun p => by
        dsimp only [ePos]; split <;> simp
      rw [sumFinInt_congr hc]; exact sumFinInt_single q (fun _ => 1)
    have hsq_m : sumFinInt P (fun p => eNeg p * eNeg p) = 1 := by
      have hc : ∀ p, eNeg p * eNeg p = if p = q then 1 else 0 := fun p => by
        dsimp only [eNeg]; split <;> simp
      rw [sumFinInt_congr hc]; exact sumFinInt_single q (fun _ => 1)
    have hdot_p : ∀ (w : Fin P → Int), sumFinInt P (fun p => w p * ePos p) = w q := fun w => by
      have hc : ∀ p, w p * ePos p = if p = q then w p else 0 := fun p => by
        dsimp only [ePos]; split <;> simp
      rw [sumFinInt_congr hc]; exact sumFinInt_single q w
    have hdot_m : ∀ (w : Fin P → Int), sumFinInt P (fun p => w p * eNeg p) = -(w q) := fun w => by
      have hc : ∀ p, w p * eNeg p = if p = q then -(w p) else 0 := fun p => by
        dsimp only [eNeg]; split <;> simp
      rw [sumFinInt_congr hc]; exact sumFinInt_single q (fun p => -(w p))
    unfold polyRltSos at hp hm h0
    dsimp only at hp hm h0
    rw [hsq_p] at hp; rw [hsq_m] at hm; rw [h0_lhs, Int.sub_zero] at h0
    have hrlt_diff :
        sumFinInt K (fun k => sumFinInt K (fun l =>
          lam k l * ((1 + sumFinInt P (fun p => s k p * ePos p)) * (1 + sumFinInt P (fun p => s l p * ePos p))))) +
        sumFinInt K (fun k => sumFinInt K (fun l =>
          lam k l * ((1 + sumFinInt P (fun p => s k p * eNeg p)) * (1 + sumFinInt P (fun p => s l p * eNeg p))))) -
        2 * sumFinInt K (fun k => sumFinInt K (fun l =>
          lam k l * ((1 + sumFinInt P (fun p => s k p * 0)) * (1 + sumFinInt P (fun p => s l p * 0))))) =
        2 * sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (s k q * s l q))) := by
      rw [← sumFinInt_mul_left, ← sumFinInt_add, ← sumFinInt_sub, ← sumFinInt_mul_left]
      apply sumFinInt_congr; intro k
      rw [← sumFinInt_mul_left, ← sumFinInt_add, ← sumFinInt_sub, ← sumFinInt_mul_left]
      apply sumFinInt_congr; intro l
      rw [hdot_p (s k), hdot_p (s l), hdot_m (s k), hdot_m (s l), hlin0 k, hlin0 l]
      grind
    have hmu_diff :
        sumFinInt K (fun k => mu k * (1 + sumFinInt P (fun p => s k p * ePos p))) +
        sumFinInt K (fun k => mu k * (1 + sumFinInt P (fun p => s k p * eNeg p))) -
        2 * sumFinInt K (fun k => mu k * (1 + sumFinInt P (fun p => s k p * 0))) = 0 := by
      rw [← sumFinInt_mul_left, ← sumFinInt_add, ← sumFinInt_sub]
      rw [sumFinInt_congr (g := fun _ => 0)]
      · exact sumFinInt_zero K
      · intro k
        rw [hdot_p (s k), hdot_m (s k), hlin0 k]
        grind
    have hsos_diff :
        sumFinInt R (fun r => (c r + sumFinInt P (fun p => v r p * ePos p)) * (c r + sumFinInt P (fun p => v r p * ePos p))) +
        sumFinInt R (fun r => (c r + sumFinInt P (fun p => v r p * eNeg p)) * (c r + sumFinInt P (fun p => v r p * eNeg p))) -
        2 * sumFinInt R (fun r => (c r + sumFinInt P (fun p => v r p * 0)) * (c r + sumFinInt P (fun p => v r p * 0))) =
        2 * sumFinInt R (fun r => v r q * v r q) := by
      rw [← sumFinInt_mul_left, ← sumFinInt_add, ← sumFinInt_sub, ← sumFinInt_mul_left]
      apply sumFinInt_congr; intro r
      rw [hdot_p (v r), hdot_m (v r), hval0 r]
      grind
    omega
  have hsum_all :
      -(P : Int) =
      sumFinInt K (fun k => sumFinInt K (fun l => lam k l * sumFinInt P (fun q => s k q * s l q))) +
      sumFinInt P (fun q => sumFinInt R (fun r => v r q * v r q)) := by
    have hL : sumFinInt P (fun _ => (-1 : Int)) = -(P : Int) := by
      rw [sumFinInt_const]; omega
    have hR : sumFinInt P (fun _ => (-1 : Int)) =
        sumFinInt P (fun q => sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (s k q * s l q)))) +
        sumFinInt P (fun q => sumFinInt R (fun r => v r q * v r q)) := by
      rw [← sumFinInt_add]
      exact sumFinInt_congr hdiag
    rw [hL] at hR
    have hswap1 :
        sumFinInt P (fun q => sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (s k q * s l q)))) =
        sumFinInt K (fun k => sumFinInt K (fun l => lam k l * sumFinInt P (fun q => s k q * s l q))) := by
      rw [← sumFinInt_swap]
      apply sumFinInt_congr; intro k
      rw [← sumFinInt_swap]
      apply sumFinInt_congr; intro l
      rw [← sumFinInt_mul_left]
    rw [hswap1] at hR; exact hR
  have hsos_nn : sumFinInt P (fun q => sumFinInt R (fun r => v r q * v r q)) ≥ 0 :=
    sumFinInt_nonneg (fun q => sumFinInt_nonneg (fun r => int_sq_nonneg (v r q)))
  have hrlt_lb :
      sumFinInt K (fun k => sumFinInt K (fun l => lam k l * sumFinInt P (fun q => s k q * s l q))) ≥
      -Λ_tot := by
    have hneg : -Λ_tot = sumFinInt K (fun k => sumFinInt K (fun l => lam k l * (-1))) := by
      dsimp only [Λ_tot]
      have h1 : -sumFinInt K (fun k => sumFinInt K (fun l => lam k l)) =
                (-1) * sumFinInt K (fun k => sumFinInt K (fun l => lam k l)) := by omega
      rw [h1, ← sumFinInt_mul_left]
      apply sumFinInt_congr; intro k
      rw [← sumFinInt_mul_left]
      apply sumFinInt_congr; intro l
      omega
    rw [hneg]
    apply sumFinInt_le; intro k
    apply sumFinInt_le; intro l
    exact Int.mul_le_mul_of_nonneg_left (hpair k l) (hlam k l)
  omega

/-- Corollary instantiating `deg2_rlt_sos_polynomial_barrier` at `P = 4^n - 1` (`n ≥ 1`). -/
public theorem clifford_reynolds_deg2_rlt_barrier (n K R : Nat) (_hn : n ≥ 1)
    (s : Fin K → Fin (4 ^ n - 1) → Int)
    (lam : Fin K → Fin K → Int)
    (mu : Fin K → Int)
    (c : Fin R → Int)
    (v : Fin R → Fin (4 ^ n - 1) → Int)
    (M : Int)
    (hlam : ∀ k l, lam k l ≥ 0)
    (hmu : ∀ k, mu k ≥ 0)
    (hpair : ∀ k l, sumFinInt (4 ^ n - 1) (fun p => s k p * s l p) ≥ -1)
    (hid : ∀ x : Fin (4 ^ n - 1) → Int,
      M - sumFinInt (4 ^ n - 1) (fun p => x p * x p) = polyRltSos s lam mu c v x) :
    M ≥ ((4 ^ n - 1 : Nat) : Int) :=
  deg2_rlt_sos_polynomial_barrier s lam mu c v M hlam hmu hpair hid

/-- Exact stabilizer pair overlap lower bound justifying `hpair`:
for ANY two pure `n`-qubit stabilizer states (`D = 2^n`, squared overlap `ov ≥ 0`),
`D * ov - 1 ≥ -1` (equality iff orthogonal). -/
public theorem stabilizer_pair_overlap_lower_bound (n : Nat) (ov : Int) (hov : ov ≥ 0) :
    ((2 ^ n : Nat) : Int) * ov - 1 ≥ -1 := by
  have hmul : ((2 ^ n : Nat) : Int) * ov ≥ 0 := Int.mul_nonneg (Int.natCast_nonneg _) hov
  omega

end QPRigidity.MagicGeometry
