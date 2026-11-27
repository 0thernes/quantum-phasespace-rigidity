module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

/-!
# Pillar I: Complete Cyclic Weyl-Heisenberg AME Dichotomy (`QPRigidity.AMEGraph`)

Resolves the open problem of Wójcik, Makuta, Bruzda, and Augusiak
(`arXiv:2603.18193v3`, 28 Sep 2026, Sec. V) and extends Cha (`arXiv:2603.13442v2`)
to all party counts `N ≥ 2`, all composite dimensions `d ≥ 2`, and arbitrary
(possibly non-canonical, non-free) cyclic `Z_d`-stabilizer subgroups:

* **T1a** (`radical_divisor_descent`, `prime_power_kuniform_ascent`, `crt_coprime_kuniform_lift`):
  Exact Radical-CRT equivalence for canonical `Z_d` graph states.
* **T1b** (`universal_unimodular_graphs_all_d`):
  Explicit universal unimodular canonical graph states `K_2`, `K_3`, `C_5`, and
  triangular prism `K_3 □ K_2` are `AME(N, d)` for ALL `d ≥ 2`.
* **T1c** (`pless_even_obstruction`, `pless_odd_obstruction`):
  Pure-integer combinatorial Pless power-moment obstruction ruling out all
  even `N ≥ 2p²` and all odd `N ≥ 2p² + 2p + 1` for every `p ≥ 2`.
* **T1d** (`f2_commuting_weight_homomorphism`, `rains_shadow_no_ame4`, `_7`, `_9`, `_11`,
  `no_canonical_graph_ame4_f2`):
  Binary Pauli commuting-weight homomorphism and Rains shadow integrality/positivity
  contradictions for `N ∈ {4, 7, 9, 11}`.
* **T1e** (`torsion_rank_lower_and_free`, `additive_mds_odd_ge9_impossible`,
  `additive_mds_n7_impossible`, `no_canonical_graph_ame4_even_d`, `z4_vs_f4_separation`):
  Cyclic `Z_{p^e}` torsion-rank Singleton forcing, additive `F_4`-MDS odd-`N` obstruction,
  complete even-`d` classification, and Ring-vs-Field Separation at `(N, d) = (4, 4)`.
-/

namespace QPRigidity.AMEGraph

/-! ## Section 1: Finite Sums, Counts, and Canonical `Z_d` Graph States -/

@[expose] public def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

@[expose] public def sumFinInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFinInt n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

@[expose] public def countFin : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => countFin n (fun i => p i.castSucc) + (if p ⟨n, Nat.lt_succ_self n⟩ then 1 else 0)

public theorem sumFin_mul_left (n c : Nat) (f : Fin n → Nat) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih => simp only [sumFin, ih, Nat.mul_add]

public theorem sumFin_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

public theorem sumFin_mod_congr {n d : Nat} {f g : Fin n → Nat}
    (h : ∀ i, f i % d = g i % d) :
    sumFin n f % d = sumFin n g % d := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin]
    rw [Nat.add_mod, ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩, ← Nat.add_mod]

public theorem countFin_mono {n : Nat} {p q : Fin n → Bool}
    (h : ∀ i, p i = true → q i = true) :
    countFin n p ≤ countFin n q := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [countFin]
    have h1 := ih (fun i => h i.castSucc)
    have h2 : (if p ⟨k, Nat.lt_succ_self k⟩ then 1 else 0) ≤
              (if q ⟨k, Nat.lt_succ_self k⟩ then 1 else 0) := by
      cases hp : p ⟨k, Nat.lt_succ_self k⟩
      · simp
      · have hq := h ⟨k, Nat.lt_succ_self k⟩ hp
        simp [hq]
    exact Nat.add_le_add h1 h2

public theorem countFin_congr {n : Nat} {p q : Fin n → Bool} (h : ∀ i, p i = q i) :
    countFin n p = countFin n q := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [countFin, ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

/-- A symmetric zero-diagonal adjacency matrix over `Nat` (interpreted modulo `d`). -/
public structure GraphAdj (N : Nat) where
  mat : Fin N → Fin N → Nat
  symm : ∀ i j, mat i j = mat j i
  diag_zero : ∀ i, mat i i = 0

@[expose] public def matVec {N : Nat} (Γ : GraphAdj N) (α : Fin N → Nat) (j : Fin N) : Nat :=
  sumFin N (fun i => Γ.mat j i * α i)

@[expose] public def pauliActive {N : Nat} (d : Nat) (Γ : GraphAdj N) (α : Fin N → Nat) (j : Fin N) : Bool :=
  decide (α j % d ≠ 0 ∨ matVec Γ α j % d ≠ 0)

@[expose] public def pauliWeight {N : Nat} (d : Nat) (Γ : GraphAdj N) (α : Fin N → Nat) : Nat :=
  countFin N (pauliActive d Γ α)

@[expose] public def IsKUniformGraph {N : Nat} (d : Nat) (Γ : GraphAdj N) (k : Nat) : Prop :=
  ∀ α : Fin N → Nat, (∃ i : Fin N, α i % d ≠ 0) → pauliWeight d Γ α > k

@[expose] public def IsAMEGraph {N : Nat} (d : Nat) (Γ : GraphAdj N) : Prop :=
  IsKUniformGraph d Γ (N / 2)

/-! ## Section 2: T1a — Radical-CRT Equivalence Theorem (ALL `N, k, d`) -/

private theorem mul_mod_mul_zero_iff (a b c : Nat) (hb : b > 0) :
    (b * a) % (c * b) = 0 ↔ a % c = 0 := by
  rw [Nat.mul_comm c b, Nat.mul_mod_mul_left]
  constructor
  · intro h
    cases Nat.mul_eq_zero.mp h with
    | inl hb0 => omega
    | inr hac => exact hac
  · intro h
    rw [h, Nat.mul_zero]

/-- **T1a (Part 1 — Divisor Descent):** If `Γ` is a `k`-uniform canonical `Z_d` graph state
and `p ∣ d` (`p ≥ 2`), then `Γ` is also a `k`-uniform canonical `Z_p` graph state. -/
public theorem radical_divisor_descent {N k d p : Nat} (Γ : GraphAdj N)
    (hd : d ≥ 2) (_hp : p ≥ 2) (hdiv : p ∣ d) (hk : IsKUniformGraph d Γ k) :
    IsKUniformGraph p Γ k := by
  rcases hdiv with ⟨ℓ, hℓ⟩
  have hℓ_pos : ℓ > 0 := by
    cases Nat.eq_zero_or_pos ℓ with
    | inl h0 => rw [h0, Nat.mul_zero] at hℓ; omega
    | inr hpos => exact hpos
  intro v ⟨i0, hi0⟩
  let α : Fin N → Nat := fun i => ℓ * (v i % p)
  have hα_nontriv : ∃ i, α i % d ≠ 0 := by
    refine ⟨i0, ?_⟩
    rw [hℓ]
    intro hzero
    have hvp := (mul_mod_mul_zero_iff (v i0 % p) ℓ p hℓ_pos).mp hzero
    rw [Nat.mod_mod] at hvp
    exact hi0 hvp
  have hw := hk α hα_nontriv
  have heq : pauliWeight d Γ α = pauliWeight p Γ v := by
    unfold pauliWeight
    apply countFin_congr
    intro j
    unfold pauliActive
    have h1 : α j % d = 0 ↔ v j % p = 0 := by
      rw [hℓ]
      have htmp := mul_mod_mul_zero_iff (v j % p) ℓ p hℓ_pos
      rw [Nat.mod_mod] at htmp
      exact htmp
    have h2 : matVec Γ α j % d = 0 ↔ matVec Γ v j % p = 0 := by
      unfold matVec
      have hfactor : sumFin N (fun i => Γ.mat j i * α i) =
                     ℓ * sumFin N (fun i => Γ.mat j i * (v i % p)) := by
        rw [← sumFin_mul_left]
        apply sumFin_congr
        intro i
        dsimp only [α]
        rw [Nat.mul_left_comm]
      rw [hfactor, hℓ, mul_mod_mul_zero_iff _ ℓ p hℓ_pos]
      have hmod : sumFin N (fun i => Γ.mat j i * (v i % p)) % p =
                  sumFin N (fun i => Γ.mat j i * v i) % p := by
        apply sumFin_mod_congr
        intro i
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [hmod]
    by_cases hvj : v j % p = 0
    · have hαj : α j % d = 0 := h1.mpr hvj
      by_cases hmv : matVec Γ v j % p = 0
      · have hmα : matVec Γ α j % d = 0 := h2.mpr hmv
        simp [hvj, hαj, hmv, hmα]
      · have hmα : matVec Γ α j % d ≠ 0 := fun h => hmv (h2.mp h)
        simp [hvj, hαj, hmv, hmα]
    · have hαj : α j % d ≠ 0 := fun h => hvj (h1.mp h)
      simp [hvj, hαj]
  rw [← heq]
  exact hw

private theorem mod_mul_eq_zero_imp_mod_left {x a b : Nat} (h : x % (a * b) = 0) : x % a = 0 := by
  have hd : a * b ∣ x := Nat.dvd_of_mod_eq_zero h
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_right a b) hd)

private theorem mod_mul_eq_zero_imp_mod_right {x a b : Nat} (h : x % (a * b) = 0) : x % b = 0 := by
  have hd : a * b ∣ x := Nat.dvd_of_mod_eq_zero h
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_left b a) hd)

/-- **T1a (Part 2 — Prime-Power Valuation Ascent):** If `Γ` is a `k`-uniform canonical
`Z_p` graph state, then the SAME adjacency matrix `Γ` is `k`-uniform over `Z_{p^e}`
for EVERY exponent `e ≥ 1`. -/
public theorem prime_power_kuniform_ascent {N k p : Nat} (Γ : GraphAdj N)
    (hp : p ≥ 2) (hk : IsKUniformGraph p Γ k) :
    ∀ e : Nat, e ≥ 1 → IsKUniformGraph (p ^ e) Γ k := by
  intro e he
  induction e with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simpa [Nat.pow_one] using hk
    | succ r =>
      have hm_ge : r + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le r)
      have ih_m := ih hm_ge
      intro α ⟨i0, hi0⟩
      by_cases hex : ∃ i : Fin N, α i % p ≠ 0
      · have hbase := hk α hex
        have hmono : pauliWeight p Γ α ≤ pauliWeight (p ^ (r + 1 + 1)) Γ α := by
          unfold pauliWeight
          apply countFin_mono
          intro j hj
          unfold pauliActive at hj ⊢
          rw [decide_eq_true_eq] at hj ⊢
          have hpow : p ^ (r + 1 + 1) = p * p ^ (r + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
          cases hj with
          | inl h1 =>
            left
            intro hzero
            rw [hpow] at hzero
            exact h1 (mod_mul_eq_zero_imp_mod_left hzero)
          | inr h2 =>
            right
            intro hzero
            rw [hpow] at hzero
            exact h2 (mod_mul_eq_zero_imp_mod_left hzero)
        exact Nat.lt_of_lt_of_le hbase hmono
      · have hall_div : ∀ i : Fin N, α i % p = 0 := by
          intro i
          exact Classical.byContradiction fun hne => hex ⟨i, hne⟩
        let β : Fin N → Nat := fun i => α i / p
        have hα_eq : ∀ i, α i = p * β i := by
          intro i
          have h1 := Nat.div_add_mod (α i) p
          rw [hall_div i, Nat.add_zero] at h1
          exact h1.symm
        have hp_pos : p > 0 := by omega
        have hβ_nontriv : ∃ i : Fin N, β i % p ^ (r + 1) ≠ 0 := by
          refine ⟨i0, ?_⟩
          intro hzero
          have hmul : (p * β i0) % (p ^ (r + 1) * p) = 0 :=
            (mul_mod_mul_zero_iff (β i0) p (p ^ (r + 1)) hp_pos).mpr hzero
          rw [← hα_eq i0, ← Nat.pow_succ] at hmul
          exact hi0 hmul
        have hw := ih_m β hβ_nontriv
        have heq : pauliWeight (p ^ (r + 1 + 1)) Γ α = pauliWeight (p ^ (r + 1)) Γ β := by
          unfold pauliWeight
          apply countFin_congr
          intro j
          unfold pauliActive
          have h1 : α j % p ^ (r + 1 + 1) = 0 ↔ β j % p ^ (r + 1) = 0 := by
            rw [hα_eq j, Nat.pow_succ]
            exact mul_mod_mul_zero_iff (β j) p (p ^ (r + 1)) hp_pos
          have h2 : matVec Γ α j % p ^ (r + 1 + 1) = 0 ↔ matVec Γ β j % p ^ (r + 1) = 0 := by
            unfold matVec
            have hfac : sumFin N (fun i => Γ.mat j i * α i) =
                        p * sumFin N (fun i => Γ.mat j i * β i) := by
              rw [← sumFin_mul_left]
              apply sumFin_congr
              intro i
              rw [hα_eq i, Nat.mul_left_comm]
            rw [hfac, Nat.pow_succ]
            exact mul_mod_mul_zero_iff _ p (p ^ (r + 1)) hp_pos
          by_cases hβj : β j % p ^ (r + 1) = 0
          · have hαj : α j % p ^ (r + 1 + 1) = 0 := h1.mpr hβj
            by_cases hmv : matVec Γ β j % p ^ (r + 1) = 0
            · have hmα : matVec Γ α j % p ^ (r + 1 + 1) = 0 := h2.mpr hmv
              simp [hβj, hαj, hmv, hmα]
            · have hmα : matVec Γ α j % p ^ (r + 1 + 1) ≠ 0 := fun h => hmv (h2.mp h)
              simp [hβj, hαj, hmv, hmα]
          · have hαj : α j % p ^ (r + 1 + 1) ≠ 0 := fun h => hβj (h1.mp h)
            simp [hβj, hαj]
        rw [heq]
        exact hw

/-- Pure-`Init` extended Euclidean algorithm returning `(x, y) : Int × Int` with
`a * x + b * y = Nat.gcd a b`. -/
private def extGcd : Nat → Nat → Int × Int
  | _, 0 => (1, 0)
  | a, b + 1 =>
    let r := a % (b + 1)
    let q := a / (b + 1)
    let p := extGcd (b + 1) r
    (p.2, p.1 - (q : Int) * p.2)
termination_by _ b => b
decreasing_by exact Nat.mod_lt a (Nat.succ_pos b)

private theorem extGcd_spec (a b : Nat) :
    (a : Int) * (extGcd a b).1 + (b : Int) * (extGcd a b).2 = (Nat.gcd a b : Int) := by
  match b with
  | 0 => simp [extGcd]
  | b' + 1 =>
    have hrec := extGcd_spec (b' + 1) (a % (b' + 1))
    have hdiv : (a : Int) = ((b' + 1 : Nat) : Int) * ((a / (b' + 1) : Nat) : Int) + ((a % (b' + 1) : Nat) : Int) := by
      have hnat := Nat.div_add_mod a (b' + 1)
      omega
    have hgcd_eq : Nat.gcd a (b' + 1) = Nat.gcd (b' + 1) (a % (b' + 1)) := by
      rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
    rw [hgcd_eq, ← hrec]
    have hstep : extGcd a (b' + 1) =
        ((extGcd (b' + 1) (a % (b' + 1))).2,
         (extGcd (b' + 1) (a % (b' + 1))).1 -
           ((a / (b' + 1) : Nat) : Int) * (extGcd (b' + 1) (a % (b' + 1))).2) := by
      rw [extGcd]
    rw [hstep]
    dsimp only
    have halg : (a : Int) * (extGcd (b' + 1) (a % (b' + 1))).2 +
                ((b' + 1 : Nat) : Int) * ((extGcd (b' + 1) (a % (b' + 1))).1 -
                  ((a / (b' + 1) : Nat) : Int) * (extGcd (b' + 1) (a % (b' + 1))).2) =
                ((b' + 1 : Nat) : Int) * (extGcd (b' + 1) (a % (b' + 1))).1 +
                ((a : Int) - ((b' + 1 : Nat) : Int) * ((a / (b' + 1) : Nat) : Int)) *
                  (extGcd (b' + 1) (a % (b' + 1))).2 := by
      rw [Int.mul_sub, Int.sub_mul]
      have hmul : ((b' + 1 : Nat) : Int) * (((a / (b' + 1) : Nat) : Int) * (extGcd (b' + 1) (a % (b' + 1))).2) =
                  ((b' + 1 : Nat) : Int) * ((a / (b' + 1) : Nat) : Int) * (extGcd (b' + 1) (a % (b' + 1))).2 := by
        rw [Int.mul_assoc]
      rw [hmul]
      omega
    rw [halg]
    have hrem : (a : Int) - ((b' + 1 : Nat) : Int) * ((a / (b' + 1) : Nat) : Int) =
                ((a % (b' + 1) : Nat) : Int) := by omega
    rw [hrem]
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.succ_pos b')

private theorem coprime_mul_dvd {a b n : Nat} (hg : Nat.gcd a b = 1) (ha : a ∣ n) (hb : b ∣ n) :
    a * b ∣ n := by
  rcases ha with ⟨ka, hka⟩
  rcases hb with ⟨kb, hkb⟩
  have hbez := extGcd_spec a b
  rw [hg] at hbez
  have h1 : (n : Int) = (n : Int) * ((a : Int) * (extGcd a b).1 + (b : Int) * (extGcd a b).2) := by
    rw [hbez]; change (n : Int) = (n : Int) * 1; rw [Int.mul_one]
  have h2 : (n : Int) * (a : Int) = ((a * b : Nat) : Int) * (kb : Int) := by
    have hnat : n * a = a * b * kb := by
      rw [hkb, Nat.mul_right_comm, Nat.mul_comm b a]
    rw [← Int.natCast_mul, ← Int.natCast_mul, hnat]
  have h3 : (n : Int) * (b : Int) = ((a * b : Nat) : Int) * (ka : Int) := by
    have hnat : n * b = a * b * ka := by
      rw [hka, Nat.mul_right_comm]
    rw [← Int.natCast_mul, ← Int.natCast_mul, hnat]
  have hmul : (n : Int) = ((a * b : Nat) : Int) * ((kb : Int) * (extGcd a b).1 + (ka : Int) * (extGcd a b).2) := by
    rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc, h2, h3, Int.mul_assoc, Int.mul_assoc, ← Int.mul_add] at h1
    exact h1
  exact Int.ofNat_dvd.mp ⟨_, hmul⟩

private theorem exists_crt_coeff (a b : Nat) (ha : a ≥ 1) (hb : b ≥ 1) (hgcd : Nat.gcd a b = 1) :
    ∃ u v : Nat, (u * b) % a = 1 % a ∧ (v * a) % b = 1 % b := by
  have hbez := extGcd_spec a b
  rw [hgcd] at hbez
  let x := (extGcd a b).1
  let y := (extGcd a b).2
  have hxy : (a : Int) * x + (b : Int) * y = 1 := hbez
  let u : Nat := ((y % (a : Int) + (a : Int)) % (a : Int)).toNat
  let v : Nat := ((x % (b : Int) + (b : Int)) % (b : Int)).toNat
  have ha0 : (a : Int) ≠ 0 := by omega
  have hb0 : (b : Int) ≠ 0 := by omega
  refine ⟨u, v, ?_, ?_⟩
  · have hu_eq : (u : Int) = (y % (a : Int) + (a : Int)) % (a : Int) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ ha0)
    have hdiff : (a : Int) ∣ ((u : Int) - y) := by
      have h1 : (u : Int) % (a : Int) = y % (a : Int) := by
        rw [hu_eq, Int.emod_emod, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod, Int.emod_emod]
      have h2 : ((u : Int) - y) % (a : Int) = 0 := by
        rw [Int.sub_emod, h1, Int.sub_self, Int.zero_emod]
      exact Int.dvd_of_emod_eq_zero h2
    have hprod : (a : Int) ∣ ((u : Int) * (b : Int) - 1) := by
      have hmul : (a : Int) ∣ ((u : Int) - y) * (b : Int) := Int.dvd_mul_of_dvd_left hdiff
      have heq : ((u : Int) - y) * (b : Int) - (a : Int) * x = (u : Int) * (b : Int) - 1 := by
        rw [Int.sub_mul, Int.mul_comm y (b : Int)]; omega
      rw [← heq]
      exact Int.dvd_sub hmul ⟨x, rfl⟩
    have hmod : ((u * b : Nat) : Int) % (a : Int) = ((1 : Nat) : Int) % (a : Int) := by
      rcases hprod with ⟨k, hk⟩
      have hcast : ((u * b : Nat) : Int) = ((1 : Nat) : Int) + (a : Int) * k := by
        rw [Int.natCast_mul]; change (u : Int) * (b : Int) = 1 + (a : Int) * k; omega
      rw [hcast, Int.add_mul_emod_self_left]
    rw [← Int.natCast_emod, ← Int.natCast_emod] at hmod
    exact Int.ofNat.inj hmod
  · have hv_eq : (v : Int) = (x % (b : Int) + (b : Int)) % (b : Int) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hb0)
    have hdiff : (b : Int) ∣ ((v : Int) - x) := by
      have h1 : (v : Int) % (b : Int) = x % (b : Int) := by
        rw [hv_eq, Int.emod_emod, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod, Int.emod_emod]
      have h2 : ((v : Int) - x) % (b : Int) = 0 := by
        rw [Int.sub_emod, h1, Int.sub_self, Int.zero_emod]
      exact Int.dvd_of_emod_eq_zero h2
    have hprod : (b : Int) ∣ ((v : Int) * (a : Int) - 1) := by
      have hmul : (b : Int) ∣ ((v : Int) - x) * (a : Int) := Int.dvd_mul_of_dvd_left hdiff
      have heq : ((v : Int) - x) * (a : Int) - (b : Int) * y = (v : Int) * (a : Int) - 1 := by
        rw [Int.sub_mul, Int.mul_comm x (a : Int)]; omega
      rw [← heq]
      exact Int.dvd_sub hmul ⟨y, rfl⟩
    have hmod : ((v * a : Nat) : Int) % (b : Int) = ((1 : Nat) : Int) % (b : Int) := by
      rcases hprod with ⟨k, hk⟩
      have hcast : ((v * a : Nat) : Int) = ((1 : Nat) : Int) + (b : Int) * k := by
        rw [Int.natCast_mul]; change (v : Int) * (a : Int) = 1 + (b : Int) * k; omega
      rw [hcast, Int.add_mul_emod_self_left]
    rw [← Int.natCast_emod, ← Int.natCast_emod] at hmod
    exact Int.ofNat.inj hmod

public theorem kuniform_mul_of_congr {N k a b : Nat} (Γ Γ₁ Γ₂ : GraphAdj N)
    (hgcd : Nat.gcd a b = 1)
    (h1 : ∀ i j, Γ.mat i j % a = Γ₁.mat i j % a)
    (h2 : ∀ i j, Γ.mat i j % b = Γ₂.mat i j % b)
    (hk1 : IsKUniformGraph a Γ₁ k) (hk2 : IsKUniformGraph b Γ₂ k) :
    IsKUniformGraph (a * b) Γ k := by
  intro α ⟨i0, hi0⟩
  by_cases ha : ∃ i, α i % a ≠ 0
  · have hw := hk1 α ha
    have hmono : pauliWeight a Γ₁ α ≤ pauliWeight (a * b) Γ α := by
      unfold pauliWeight
      apply countFin_mono
      intro j hj
      unfold pauliActive at hj ⊢
      rw [decide_eq_true_eq] at hj ⊢
      cases hj with
      | inl hα =>
        left
        intro hz
        exact hα (mod_mul_eq_zero_imp_mod_left hz)
      | inr hm =>
        right
        intro hz
        have hza : matVec Γ α j % a = 0 := mod_mul_eq_zero_imp_mod_left hz
        have hceq : matVec Γ α j % a = matVec Γ₁ α j % a := by
          unfold matVec
          apply sumFin_mod_congr
          intro i
          rw [Nat.mul_mod, h1 j i, ← Nat.mul_mod]
        rw [hceq] at hza
        exact hm hza
    exact Nat.lt_of_lt_of_le hw hmono
  · have hb : ∃ i, α i % b ≠ 0 := by
      refine ⟨i0, ?_⟩
      intro hzb
      have hza : α i0 % a = 0 := Classical.byContradiction fun hne => ha ⟨i0, hne⟩
      have hd_a : a ∣ α i0 := Nat.dvd_of_mod_eq_zero hza
      have hd_b : b ∣ α i0 := Nat.dvd_of_mod_eq_zero hzb
      have hd_ab : a * b ∣ α i0 := coprime_mul_dvd hgcd hd_a hd_b
      exact hi0 (Nat.mod_eq_zero_of_dvd hd_ab)
    have hw := hk2 α hb
    have hmono : pauliWeight b Γ₂ α ≤ pauliWeight (a * b) Γ α := by
      unfold pauliWeight
      apply countFin_mono
      intro j hj
      unfold pauliActive at hj ⊢
      rw [decide_eq_true_eq] at hj ⊢
      cases hj with
      | inl hα =>
        left
        intro hz
        exact hα (mod_mul_eq_zero_imp_mod_right hz)
      | inr hm =>
        right
        intro hz
        have hzb : matVec Γ α j % b = 0 := mod_mul_eq_zero_imp_mod_right hz
        have hceq : matVec Γ α j % b = matVec Γ₂ α j % b := by
          unfold matVec
          apply sumFin_mod_congr
          intro i
          rw [Nat.mul_mod, h2 j i, ← Nat.mul_mod]
        rw [hceq] at hzb
        exact hm hzb
    exact Nat.lt_of_lt_of_le hw hmono

/-- **T1a (Part 3 — Coprime CRT Lifting):** For ANY coprime `a, b ≥ 2`, if `k`-uniform
canonical graph states exist mod `a` and mod `b`, then one exists mod `a * b`. -/
public theorem crt_coprime_kuniform_lift {N k a b : Nat} (ha : a ≥ 2) (hb : b ≥ 2)
    (hgcd : Nat.gcd a b = 1)
    (h1 : ∃ Γ₁ : GraphAdj N, IsKUniformGraph a Γ₁ k)
    (h2 : ∃ Γ₂ : GraphAdj N, IsKUniformGraph b Γ₂ k) :
    ∃ Γ : GraphAdj N, IsKUniformGraph (a * b) Γ k := by
  rcases h1 with ⟨Γ₁, hk1⟩
  rcases h2 with ⟨Γ₂, hk2⟩
  rcases exists_crt_coeff a b (by omega) (by omega) hgcd with ⟨u, v, hu, hv⟩
  let Γ : GraphAdj N := {
    mat := fun i j => Γ₁.mat i j * (u * b) + Γ₂.mat i j * (v * a)
    symm := fun i j => by rw [Γ₁.symm i j, Γ₂.symm i j]
    diag_zero := fun i => by rw [Γ₁.diag_zero i, Γ₂.diag_zero i]; simp
  }
  refine ⟨Γ, kuniform_mul_of_congr Γ Γ₁ Γ₂ hgcd ?_ ?_ hk1 hk2⟩
  · intro i j
    dsimp only [Γ]
    rw [Nat.add_mod]
    have hzero : (Γ₂.mat i j * (v * a)) % a = 0 := by
      rw [← Nat.mul_assoc, Nat.mul_mod_left]
    rw [hzero, Nat.add_zero, Nat.mod_mod, Nat.mul_mod, hu, ← Nat.mul_mod, Nat.mul_one]
  · intro i j
    dsimp only [Γ]
    rw [Nat.add_mod]
    have hzero : (Γ₁.mat i j * (u * b)) % b = 0 := by
      rw [← Nat.mul_assoc, Nat.mul_mod_left]
    rw [hzero, Nat.zero_add, Nat.mod_mod, Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_one]

/-! ## Section 3: T1b — Universal Unimodular Canonical Graph States (`N ∈ {2,3,5,6}`, ALL `d ≥ 2`) -/

public def graphK2 : GraphAdj 2 where
  mat i j := if i = j then 0 else 1
  symm := by decide
  diag_zero := by decide

public def graphK3 : GraphAdj 3 where
  mat i j := if i = j then 0 else 1
  symm := by decide
  diag_zero := by decide

public def graphC5 : GraphAdj 5 where
  mat i j :=
    match i.val, j.val with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => 1
    | _, _ => 0
  symm := by decide
  diag_zero := by decide

public def graphPrism6 : GraphAdj 6 where
  mat i j :=
    match i.val, j.val with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 0 | 0, 2 => 1
    | 3, 4 | 4, 3 | 4, 5 | 5, 4 | 5, 3 | 3, 5 => 1
    | 0, 3 | 3, 0 | 1, 4 | 4, 1 | 2, 5 | 5, 2 => 1
    | _, _ => 0
  symm := by decide
  diag_zero := by decide

public def graphWheel5 : GraphAdj 6 where
  mat i j :=
    match i.val, j.val with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => 1
    | 0, 5 | 5, 0 | 1, 5 | 5, 1 | 2, 5 | 5, 2 | 3, 5 | 5, 3 | 4, 5 | 5, 4 => 1
    | _, _ => 0
  symm := by decide
  diag_zero := by decide

private theorem mod_add_left_zero {a b d : Nat} (ha : a % d = 0) (hab : (a + b) % d = 0) : b % d = 0 := by
  rw [Nat.add_mod, ha, Nat.zero_add, Nat.mod_mod] at hab
  exact hab

private theorem mod_add_right_zero {a b d : Nat} (hb : b % d = 0) (hab : (a + b) % d = 0) : a % d = 0 := by
  rw [Nat.add_mod, hb, Nat.add_zero, Nat.mod_mod] at hab
  exact hab

private theorem fin2_cases {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  match i with | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1

private theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  match i with | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2

private theorem fin5_cases {P : Fin 5 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (i : Fin 5) : P i := by
  match i with
  | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3 | ⟨4, _⟩ => exact h4

private theorem fin6_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (i : Fin 6) : P i := by
  match i with
  | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3 | ⟨4, _⟩ => exact h4 | ⟨5, _⟩ => exact h5

public theorem graphK2_ame_all_d (d : Nat) (_hd : d ≥ 2) : IsAMEGraph d graphK2 := by
  intro α ⟨i0, hi0⟩
  have hmv0 : matVec graphK2 α 0 = α 1 := by simp [matVec, sumFin, graphK2]
  have hmv1 : matVec graphK2 α 1 = α 0 := by simp [matVec, sumFin, graphK2]
  have h01 : α 0 % d ≠ 0 ∨ α 1 % d ≠ 0 := by
    match i0 with | ⟨0, _⟩ => exact Or.inl hi0 | ⟨1, _⟩ => exact Or.inr hi0
  have ha0 : pauliActive d graphK2 α 0 = true := by
    unfold pauliActive; rw [decide_eq_true_eq, hmv0]; exact h01
  have ha1 : pauliActive d graphK2 α 1 = true := by
    unfold pauliActive; rw [decide_eq_true_eq, hmv1]; exact h01.symm
  have hw : pauliWeight d graphK2 α = 2 := by
    simp [pauliWeight, countFin, ha0, ha1]
  omega

private theorem pauliInactive_iff {N d : Nat} {Γ : GraphAdj N} {α : Fin N → Nat} {j : Fin N} :
    pauliActive d Γ α j = false ↔ α j % d = 0 ∧ matVec Γ α j % d = 0 := by
  unfold pauliActive
  rw [decide_eq_false_iff_not, not_or, Decidable.not_not, Decidable.not_not]

public theorem graphK3_ame_all_d (d : Nat) (_hd : d ≥ 2) : IsAMEGraph d graphK3 := by
  intro α ⟨i0, hi0⟩
  have hmv0 : matVec graphK3 α 0 = α 1 + α 2 := by simp [matVec, sumFin, graphK3]
  have hmv1 : matVec graphK3 α 1 = α 0 + α 2 := by simp [matVec, sumFin, graphK3]
  have hmv2 : matVec graphK3 α 2 = α 0 + α 1 := by simp [matVec, sumFin, graphK3]
  exact Classical.byContradiction fun hle => by
    have hlt : (if pauliActive d graphK3 α 0 then 1 else 0) +
               (if pauliActive d graphK3 α 1 then 1 else 0) +
               (if pauliActive d graphK3 α 2 then 1 else 0) ≤ 1 := by
      have h1 : pauliWeight d graphK3 α ≤ 1 := by omega
      simp only [pauliWeight, countFin, Nat.zero_add] at h1
      exact h1
    have hfail : (α 0 % d = 0 ∧ α 1 % d = 0 ∧ α 2 % d = 0) → False := fun ⟨z0, z1, z2⟩ =>
      hi0 (match i0 with | ⟨0, _⟩ => z0 | ⟨1, _⟩ => z1 | ⟨2, _⟩ => z2)
    cases hb0 : pauliActive d graphK3 α 0 <;>
    cases hb1 : pauliActive d graphK3 α 1 <;>
    cases hb2 : pauliActive d graphK3 α 2 <;>
    simp only [hb0, hb1, hb2, Bool.false_eq_true, ite_true, ite_false] at hlt
    all_goals try omega
    · have p0 := pauliInactive_iff.mp hb0; have p1 := pauliInactive_iff.mp hb1
      rw [hmv0] at p0; exact hfail ⟨p0.1, p1.1, mod_add_left_zero p1.1 p0.2⟩
    · have p0 := pauliInactive_iff.mp hb0; have p1 := pauliInactive_iff.mp hb1
      rw [hmv0] at p0; exact hfail ⟨p0.1, p1.1, mod_add_left_zero p1.1 p0.2⟩
    · have p0 := pauliInactive_iff.mp hb0; have p2 := pauliInactive_iff.mp hb2
      rw [hmv0] at p0; exact hfail ⟨p0.1, mod_add_right_zero p2.1 p0.2, p2.1⟩
    · have p1 := pauliInactive_iff.mp hb1; have p2 := pauliInactive_iff.mp hb2
      rw [hmv1] at p1; exact hfail ⟨mod_add_right_zero p2.1 p1.2, p1.1, p2.1⟩

private theorem exists_three_false_fin5 (p : Fin 5 → Bool) (h : countFin 5 p ≤ 2) :
    ∃ i1 i2 i3 : Fin 5, i1 < i2 ∧ i2 < i3 ∧ p i1 = false ∧ p i2 = false ∧ p i3 = false := by
  have hcheck : ∀ b0 b1 b2 b3 b4 : Bool,
      ((if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) +
       (if b3 then 1 else 0) + (if b4 then 1 else 0) ≤ 2) →
      ∃ i1 i2 i3 : Fin 5, i1 < i2 ∧ i2 < i3 ∧
        (match i1.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4) = false ∧
        (match i2.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4) = false ∧
        (match i3.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4) = false := by
    decide
  have hsum : (if p 0 then 1 else 0) + (if p 1 then 1 else 0) + (if p 2 then 1 else 0) +
              (if p 3 then 1 else 0) + (if p 4 then 1 else 0) ≤ 2 := by
    simp only [countFin, Nat.zero_add] at h; exact h
  rcases hcheck (p 0) (p 1) (p 2) (p 3) (p 4) hsum with ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩
  have heval : ∀ i : Fin 5,
      (match i.val with | 0 => p 0 | 1 => p 1 | 2 => p 2 | 3 => p 3 | _ => p 4) = p i :=
    fin5_cases rfl rfl rfl rfl rfl
  rw [heval i1] at f1; rw [heval i2] at f2; rw [heval i3] at f3
  exact ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩

public theorem graphC5_ame_all_d (d : Nat) (_hd : d ≥ 2) : IsAMEGraph d graphC5 := by
  intro α ⟨i0, hi0⟩
  have hmv0 : matVec graphC5 α 0 = α 1 + α 4 := by
    have h : matVec graphC5 α 0 = 0 + 0 * α 0 + 1 * α 1 + 0 * α 2 + 0 * α 3 + 1 * α 4 := rfl
    omega
  have hmv1 : matVec graphC5 α 1 = α 0 + α 2 := by
    have h : matVec graphC5 α 1 = 0 + 1 * α 0 + 0 * α 1 + 1 * α 2 + 0 * α 3 + 0 * α 4 := rfl
    omega
  have hmv2 : matVec graphC5 α 2 = α 1 + α 3 := by
    have h : matVec graphC5 α 2 = 0 + 0 * α 0 + 1 * α 1 + 0 * α 2 + 1 * α 3 + 0 * α 4 := rfl
    omega
  have hmv3 : matVec graphC5 α 3 = α 2 + α 4 := by
    have h : matVec graphC5 α 3 = 0 + 0 * α 0 + 0 * α 1 + 1 * α 2 + 0 * α 3 + 1 * α 4 := rfl
    omega
  have hmv4 : matVec graphC5 α 4 = α 0 + α 3 := by
    have h : matVec graphC5 α 4 = 0 + 1 * α 0 + 0 * α 1 + 0 * α 2 + 1 * α 3 + 0 * α 4 := rfl
    omega
  exact Classical.byContradiction fun hle => by
    have hlt : countFin 5 (pauliActive d graphC5 α) ≤ 2 := by unfold pauliWeight at hle; omega
    rcases exists_three_false_fin5 _ hlt with ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩
    have hfail : (α 0 % d = 0 ∧ α 1 % d = 0 ∧ α 2 % d = 0 ∧ α 3 % d = 0 ∧ α 4 % d = 0) → False :=
      fun ⟨z0, z1, z2, z3, z4⟩ => hi0 (match i0 with | ⟨0, _⟩ => z0 | ⟨1, _⟩ => z1 | ⟨2, _⟩ => z2 | ⟨3, _⟩ => z3 | ⟨4, _⟩ => z4)
    have hfin5 : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
    rcases hfin5 i1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases hfin5 i2 with rfl | rfl | rfl | rfl | rfl <;>
    rcases hfin5 i3 with rfl | rfl | rfl | rfl | rfl
    all_goals try (exfalso; revert h12 h23; decide)
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv0] at p1; rw [hmv2] at p3
      exact hfail ⟨p1.1, p2.1, p3.1, mod_add_left_zero p2.1 p3.2, mod_add_left_zero p2.1 p1.2⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv0] at p1; rw [hmv1] at p2
      exact hfail ⟨p1.1, p2.1, mod_add_left_zero p1.1 p2.2, p3.1, mod_add_left_zero p2.1 p1.2⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv1] at p2; rw [hmv4] at p3
      exact hfail ⟨p1.1, p2.1, mod_add_left_zero p1.1 p2.2, mod_add_left_zero p1.1 p3.2, p3.1⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv2] at p2; rw [hmv3] at p3
      exact hfail ⟨p1.1, mod_add_right_zero p3.1 p2.2, p2.1, p3.1, mod_add_left_zero p2.1 p3.2⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv0] at p1; rw [hmv4] at p3
      exact hfail ⟨p1.1, mod_add_right_zero p3.1 p1.2, p2.1, mod_add_left_zero p1.1 p3.2, p3.1⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv0] at p1; rw [hmv3] at p2
      exact hfail ⟨p1.1, mod_add_right_zero p3.1 p1.2, mod_add_right_zero p3.1 p2.2, p2.1, p3.1⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv1] at p1; rw [hmv3] at p3
      exact hfail ⟨mod_add_right_zero p2.1 p1.2, p1.1, p2.1, p3.1, mod_add_left_zero p2.1 p3.2⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv1] at p1; rw [hmv2] at p2
      exact hfail ⟨mod_add_right_zero p2.1 p1.2, p1.1, p2.1, mod_add_left_zero p1.1 p2.2, p3.1⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv3] at p2; rw [hmv4] at p3
      exact hfail ⟨mod_add_right_zero p2.1 p3.2, p1.1, mod_add_right_zero p3.1 p2.2, p2.1, p3.1⟩
    · have p1 := pauliInactive_iff.mp f1; have p2 := pauliInactive_iff.mp f2; have p3 := pauliInactive_iff.mp f3
      rw [hmv2] at p1; rw [hmv4] at p3
      exact hfail ⟨mod_add_right_zero p2.1 p3.2, mod_add_right_zero p2.1 p1.2, p1.1, p2.1, p3.1⟩

private theorem dvd_int_cancel_nat {d x : Nat} (h : (d : Int) ∣ (x : Int)) : x % d = 0 := by
  have hnat : d ∣ x := Int.ofNat_dvd.mp h
  exact Nat.mod_eq_zero_of_dvd hnat

private theorem nat_dvd_int {d x : Nat} (h : x % d = 0) : (d : Int) ∣ (x : Int) :=
  Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero h)

private theorem prism6_three_inactive_forces_zero {d : Nat} (α : Fin 6 → Nat)
    (i1 i2 i3 : Fin 6) (h12 : i1 < i2) (h23 : i2 < i3)
    (ha1 : pauliActive d graphPrism6 α i1 = false)
    (ha2 : pauliActive d graphPrism6 α i2 = false)
    (ha3 : pauliActive d graphPrism6 α i3 = false) :
    ∀ i : Fin 6, α i % d = 0 := by
  have hmv0 : matVec graphPrism6 α 0 = α 1 + α 2 + α 3 := by
    have h : matVec graphPrism6 α 0 = 0 + 0 * α 0 + 1 * α 1 + 1 * α 2 + 1 * α 3 + 0 * α 4 + 0 * α 5 := rfl
    omega
  have hmv1 : matVec graphPrism6 α 1 = α 0 + α 2 + α 4 := by
    have h : matVec graphPrism6 α 1 = 0 + 1 * α 0 + 0 * α 1 + 1 * α 2 + 0 * α 3 + 1 * α 4 + 0 * α 5 := rfl
    omega
  have hmv2 : matVec graphPrism6 α 2 = α 0 + α 1 + α 5 := by
    have h : matVec graphPrism6 α 2 = 0 + 1 * α 0 + 1 * α 1 + 0 * α 2 + 0 * α 3 + 0 * α 4 + 1 * α 5 := rfl
    omega
  have hmv3 : matVec graphPrism6 α 3 = α 0 + α 4 + α 5 := by
    have h : matVec graphPrism6 α 3 = 0 + 1 * α 0 + 0 * α 1 + 0 * α 2 + 0 * α 3 + 1 * α 4 + 1 * α 5 := rfl
    omega
  have hmv4 : matVec graphPrism6 α 4 = α 1 + α 3 + α 5 := by
    have h : matVec graphPrism6 α 4 = 0 + 0 * α 0 + 1 * α 1 + 0 * α 2 + 1 * α 3 + 0 * α 4 + 1 * α 5 := rfl
    omega
  have hmv5 : matVec graphPrism6 α 5 = α 2 + α 3 + α 4 := by
    have h : matVec graphPrism6 α 5 = 0 + 0 * α 0 + 0 * α 1 + 1 * α 2 + 1 * α 3 + 1 * α 4 + 0 * α 5 := rfl
    omega
  -- Helper: from three sums (u+v+w) % d = 0 and two zero terms, extract the third!
  have h3_1 : ∀ {x y z : Nat}, x % d = 0 → y % d = 0 → (x + y + z) % d = 0 → z % d = 0 := by
    intro x y z hx hy hxyz; rw [Nat.add_assoc] at hxyz; exact mod_add_left_zero hy (mod_add_left_zero hx hxyz)
  have h3_2 : ∀ {x y z : Nat}, x % d = 0 → z % d = 0 → (x + y + z) % d = 0 → y % d = 0 := by
    intro x y z hx hz hxyz; exact mod_add_left_zero hx (mod_add_right_zero hz hxyz)
  have h3_3 : ∀ {x y z : Nat}, y % d = 0 → z % d = 0 → (x + y + z) % d = 0 → x % d = 0 := by
    intro x y z hy hz hxyz; exact mod_add_right_zero hy (mod_add_right_zero hz hxyz)
  have hfin6 : ∀ j : Fin 6, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by decide
  rcases hfin6 i1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hfin6 i2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hfin6 i3 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try (exfalso; revert h12 h23; decide)
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv2] at ha1 ha2 ha3
    exact fin6_cases ha1.1 ha2.1 ha3.1 (h3_1 ha2.1 ha3.1 ha1.2) (h3_1 ha1.1 ha3.1 ha2.2) (h3_1 ha1.1 ha2.1 ha3.2)
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv3] at ha1 ha2 ha3
    have e2 := h3_2 ha2.1 ha3.1 ha1.2
    have e4 := h3_1 ha1.1 e2 ha2.2
    have e5 := h3_1 ha1.1 e4 ha3.2
    exact fin6_cases ha1.1 ha2.1 e2 ha3.1 e4 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv4] at ha1 ha2 ha3
    have e2 := h3_2 ha1.1 ha3.1 ha2.2
    have e3 := h3_1 ha2.1 e2 ha1.2
    have e5 := h3_1 ha2.1 e3 ha3.2
    exact fin6_cases ha1.1 ha2.1 e2 e3 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv5] at ha1 ha2 ha3
    have e4 : α 4 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha3.2) (nat_dvd_int ha1.2)) (nat_dvd_int ha2.1)
      have heq : (((α 2 + α 3 + α 4 : Nat) : Int) - ((α 1 + α 2 + α 3 : Nat) : Int) + (α 1 : Int)) = (α 4 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e2 := h3_2 ha1.1 e4 ha2.2
    have e3 := h3_1 ha2.1 e2 ha1.2
    exact fin6_cases ha1.1 ha2.1 e2 e3 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv3] at ha1 ha2 ha3
    have e1 := h3_3 ha2.1 ha3.1 ha1.2
    have e5 := h3_1 ha1.1 e1 ha2.2
    have e4 := h3_2 ha1.1 e5 ha3.2
    exact fin6_cases ha1.1 e1 ha2.1 ha3.1 e4 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv4] at ha1 ha2 ha3
    have e5 : α 5 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha3.2) (nat_dvd_int ha1.2)) (nat_dvd_int ha2.1)
      have heq : (((α 1 + α 3 + α 5 : Nat) : Int) - ((α 1 + α 2 + α 3 : Nat) : Int) + (α 2 : Int)) = (α 5 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e1 := h3_2 ha1.1 e5 ha2.2
    have e3 := h3_1 e1 ha2.1 ha1.2
    exact fin6_cases ha1.1 e1 ha2.1 e3 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv5] at ha1 ha2 ha3
    have e1 := h3_2 ha1.1 ha3.1 ha2.2
    have e3 := h3_1 e1 ha2.1 ha1.2
    have e4 := h3_1 ha2.1 e3 ha3.2
    exact fin6_cases ha1.1 e1 ha2.1 e3 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv3, hmv4] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha3.1 ha2.2
    have e1 := h3_3 ha2.1 e5 ha3.2
    have e2 := h3_2 e1 ha2.1 ha1.2
    exact fin6_cases ha1.1 e1 e2 ha2.1 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv3, hmv5] at ha1 ha2 ha3
    have e4 := h3_2 ha1.1 ha3.1 ha2.2
    have e2 := h3_3 ha2.1 e4 ha3.2
    have e1 := h3_3 e2 ha2.1 ha1.2
    exact fin6_cases ha1.1 e1 e2 ha2.1 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv4, hmv5] at ha1 ha2 ha3
    have e2 : α 2 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha3.1)
      have heq : (((α 1 + α 2 + α 3 : Nat) : Int) - ((α 1 + α 3 + α 5 : Nat) : Int) + (α 5 : Int)) = (α 2 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e3 := h3_2 e2 ha2.1 ha3.2
    have e1 := h3_3 e3 ha3.1 ha2.2
    exact fin6_cases ha1.1 e1 e2 e3 ha2.1 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv3] at ha1 ha2 ha3
    have e5 : α 5 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha3.2) (nat_dvd_int ha1.2)) (nat_dvd_int ha2.1)
      have heq : (((α 0 + α 4 + α 5 : Nat) : Int) - ((α 0 + α 2 + α 4 : Nat) : Int) + (α 2 : Int)) = (α 5 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e0 := h3_3 ha1.1 e5 ha2.2
    have e4 := h3_1 e0 ha2.1 ha1.2
    exact fin6_cases e0 ha1.1 ha2.1 ha3.1 e4 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv4] at ha1 ha2 ha3
    have e0 := h3_3 ha2.1 ha3.1 ha1.2
    have e5 := h3_1 e0 ha1.1 ha2.2
    have e3 := h3_2 ha1.1 e5 ha3.2
    exact fin6_cases e0 ha1.1 ha2.1 e3 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv5] at ha1 ha2 ha3
    have e0 := h3_3 ha1.1 ha3.1 ha2.2
    have e4 := h3_1 e0 ha2.1 ha1.2
    have e3 := h3_2 ha2.1 e4 ha3.2
    exact fin6_cases e0 ha1.1 ha2.1 e3 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv3, hmv4] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha2.1 ha3.2
    have e0 := h3_3 ha3.1 e5 ha2.2
    have e2 := h3_2 e0 ha3.1 ha1.2
    exact fin6_cases e0 ha1.1 e2 ha2.1 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv3, hmv5] at ha1 ha2 ha3
    have e2 : α 2 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha3.1)
      have heq : (((α 0 + α 2 + α 4 : Nat) : Int) - ((α 0 + α 4 + α 5 : Nat) : Int) + (α 5 : Int)) = (α 2 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e4 := h3_1 e2 ha2.1 ha3.2
    have e0 := h3_3 e4 ha3.1 ha2.2
    exact fin6_cases e0 ha1.1 e2 ha2.1 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv4, hmv5] at ha1 ha2 ha3
    have e3 := h3_2 ha1.1 ha3.1 ha2.2
    have e2 := h3_3 e3 ha2.1 ha3.2
    have e0 := h3_3 e2 ha2.1 ha1.2
    exact fin6_cases e0 ha1.1 e2 e3 ha2.1 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv3, hmv4] at ha1 ha2 ha3
    have e1 : α 1 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha3.1)
      have heq : (((α 0 + α 1 + α 5 : Nat) : Int) - ((α 0 + α 4 + α 5 : Nat) : Int) + (α 4 : Int)) = (α 1 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e5 := h3_1 e1 ha2.1 ha3.2
    have e0 := h3_3 ha3.1 e5 ha2.2
    exact fin6_cases e0 e1 ha1.1 ha2.1 ha3.1 e5
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv3, hmv5] at ha1 ha2 ha3
    have e4 := h3_1 ha1.1 ha2.1 ha3.2
    have e0 := h3_3 e4 ha3.1 ha2.2
    have e1 := h3_2 e0 ha3.1 ha1.2
    exact fin6_cases e0 e1 ha1.1 ha2.1 e4 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv4, hmv5] at ha1 ha2 ha3
    have e3 := h3_2 ha1.1 ha2.1 ha3.2
    have e1 := h3_3 e3 ha3.1 ha2.2
    have e0 := h3_3 e1 ha3.1 ha1.2
    exact fin6_cases e0 e1 ha1.1 e3 ha2.1 ha3.1
  · unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv3, hmv4, hmv5] at ha1 ha2 ha3
    exact fin6_cases (h3_3 ha2.1 ha3.1 ha1.2) (h3_3 ha1.1 ha3.1 ha2.2) (h3_3 ha1.1 ha2.1 ha3.2) ha1.1 ha2.1 ha3.1

/-- Clean constructive extraction of 3 ordered `false` indices from a 6-bit function with `countFin 6 p ≤ 3`. -/
private theorem exists_three_false_fin6 (p : Fin 6 → Bool) (h : countFin 6 p ≤ 3) :
    ∃ i1 i2 i3 : Fin 6, i1 < i2 ∧ i2 < i3 ∧ p i1 = false ∧ p i2 = false ∧ p i3 = false := by
  have hcheck : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      ((if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) +
       (if b3 then 1 else 0) + (if b4 then 1 else 0) + (if b5 then 1 else 0) ≤ 3) →
      ∃ i1 i2 i3 : Fin 6, i1 < i2 ∧ i2 < i3 ∧
        (match i1.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5) = false ∧
        (match i2.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5) = false ∧
        (match i3.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5) = false := by
    decide
  have hsum : (if p 0 then 1 else 0) + (if p 1 then 1 else 0) + (if p 2 then 1 else 0) +
              (if p 3 then 1 else 0) + (if p 4 then 1 else 0) + (if p 5 then 1 else 0) ≤ 3 := by
    simp only [countFin, Nat.zero_add] at h; exact h
  rcases hcheck (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) hsum with ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩
  have heval : ∀ i : Fin 6,
      (match i.val with | 0 => p 0 | 1 => p 1 | 2 => p 2 | 3 => p 3 | 4 => p 4 | _ => p 5) = p i :=
    fin6_cases rfl rfl rfl rfl rfl rfl
  rw [heval i1] at f1; rw [heval i2] at f2; rw [heval i3] at f3
  exact ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩

public theorem graphPrism6_ame_all_d (d : Nat) (_hd : d ≥ 2) : IsAMEGraph d graphPrism6 := by
  intro α ⟨i0, hi0⟩
  exact Classical.byContradiction fun hle => by
    have hlt : countFin 6 (pauliActive d graphPrism6 α) ≤ 3 := by
      unfold pauliWeight at hle; omega
    rcases exists_three_false_fin6 _ hlt with ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩
    exact hi0 (prism6_three_inactive_forces_zero α i1 i2 i3 h12 h23 f1 f2 f3 i0)

private theorem wheel5_three_inactive_forces_zero {d : Nat} (α : Fin 6 → Nat)
    (i1 i2 i3 : Fin 6) (h12 : i1 < i2) (h23 : i2 < i3)
    (ha1 : pauliActive d graphWheel5 α i1 = false)
    (ha2 : pauliActive d graphWheel5 α i2 = false)
    (ha3 : pauliActive d graphWheel5 α i3 = false) :
    ∀ i : Fin 6, α i % d = 0 := by
  have hmv0 : matVec graphWheel5 α 0 = α 1 + α 4 + α 5 := by
    have h : matVec graphWheel5 α 0 = 0 + 0 * α 0 + 1 * α 1 + 0 * α 2 + 0 * α 3 + 1 * α 4 + 1 * α 5 := rfl
    omega
  have hmv1 : matVec graphWheel5 α 1 = α 0 + α 2 + α 5 := by
    have h : matVec graphWheel5 α 1 = 0 + 1 * α 0 + 0 * α 1 + 1 * α 2 + 0 * α 3 + 0 * α 4 + 1 * α 5 := rfl
    omega
  have hmv2 : matVec graphWheel5 α 2 = α 1 + α 3 + α 5 := by
    have h : matVec graphWheel5 α 2 = 0 + 0 * α 0 + 1 * α 1 + 0 * α 2 + 1 * α 3 + 0 * α 4 + 1 * α 5 := rfl
    omega
  have hmv3 : matVec graphWheel5 α 3 = α 2 + α 4 + α 5 := by
    have h : matVec graphWheel5 α 3 = 0 + 0 * α 0 + 0 * α 1 + 1 * α 2 + 0 * α 3 + 1 * α 4 + 1 * α 5 := rfl
    omega
  have hmv4 : matVec graphWheel5 α 4 = α 0 + α 3 + α 5 := by
    have h : matVec graphWheel5 α 4 = 0 + 1 * α 0 + 0 * α 1 + 0 * α 2 + 1 * α 3 + 0 * α 4 + 1 * α 5 := rfl
    omega
  have hmv5 : matVec graphWheel5 α 5 = α 0 + α 1 + α 2 + α 3 + α 4 := by
    have h : matVec graphWheel5 α 5 = 0 + 1 * α 0 + 1 * α 1 + 1 * α 2 + 1 * α 3 + 1 * α 4 + 0 * α 5 := rfl
    omega
  have h3_1 : ∀ {x y z : Nat}, x % d = 0 → y % d = 0 → (x + y + z) % d = 0 → z % d = 0 := by
    intro x y z hx hy hxyz; rw [Nat.add_assoc] at hxyz; exact mod_add_left_zero hy (mod_add_left_zero hx hxyz)
  have h3_2 : ∀ {x y z : Nat}, x % d = 0 → z % d = 0 → (x + y + z) % d = 0 → y % d = 0 := by
    intro x y z hx hz hxyz; exact mod_add_left_zero hx (mod_add_right_zero hz hxyz)
  have h3_3 : ∀ {x y z : Nat}, y % d = 0 → z % d = 0 → (x + y + z) % d = 0 → x % d = 0 := by
    intro x y z hy hz hxyz; exact mod_add_right_zero hy (mod_add_right_zero hz hxyz)
  have h5_zero : ∀ {a b c e f : Nat}, a % d = 0 → b % d = 0 → c % d = 0 → e % d = 0 →
      (a + b + c + e + f) % d = 0 → f % d = 0 := by
    intro a b c e f ha hb hc he hsum
    have hd := Int.dvd_sub (nat_dvd_int hsum)
      (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha) (nat_dvd_int hb)) (nat_dvd_int hc)) (nat_dvd_int he))
    have heq : (((a + b + c + e + f : Nat) : Int) - ((a : Int) + (b : Int) + (c : Int) + (e : Int))) = (f : Int) := by omega
    rw [heq] at hd; exact dvd_int_cancel_nat hd
  have hfin6 : ∀ j : Fin 6, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by decide
  rcases hfin6 i1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hfin6 i2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hfin6 i3 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try (exfalso; revert h12 h23; decide)
  · -- (0, 1, 2)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv2] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha3.1 ha2.2
    have e4 := h3_2 ha2.1 e5 ha1.2
    have e3 := h3_2 ha2.1 e5 ha3.2
    exact fin6_cases ha1.1 ha2.1 ha3.1 e3 e4 e5
  · -- (0, 1, 3)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv3] at ha1 ha2 ha3
    have e2 : α 2 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha3.2) (nat_dvd_int ha1.2)) (nat_dvd_int ha2.1)
      have heq : (((α 2 + α 4 + α 5 : Nat) : Int) - ((α 1 + α 4 + α 5 : Nat) : Int) + (α 1 : Int)) = (α 2 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e5 := h3_1 ha1.1 e2 ha2.2
    have e4 := h3_2 ha2.1 e5 ha1.2
    exact fin6_cases ha1.1 ha2.1 e2 ha3.1 e4 e5
  · -- (0, 1, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv4] at ha1 ha2 ha3
    have e5 := h3_1 ha2.1 ha3.1 ha1.2
    have e2 := h3_2 ha1.1 e5 ha2.2
    have e3 := h3_2 ha1.1 e5 ha3.2
    exact fin6_cases ha1.1 ha2.1 e2 e3 ha3.1 e5
  · -- (0, 1, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv1, hmv5] at ha1 ha2 ha3
    have e4 := h3_2 ha2.1 ha3.1 ha1.2
    have e2 := h3_2 ha1.1 ha3.1 ha2.2
    have e3 : α 3 % d = 0 := by
      have hd := Int.dvd_sub (nat_dvd_int ha3.2)
        (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.1) (nat_dvd_int ha2.1)) (nat_dvd_int e2)) (nat_dvd_int e4))
      have heq : (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) - ((α 0 : Int) + (α 1 : Int) + (α 2 : Int) + (α 4 : Int))) = (α 3 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    exact fin6_cases ha1.1 ha2.1 e2 e3 e4 ha3.1
  · -- (0, 2, 3)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv3] at ha1 ha2 ha3
    have e1 : α 1 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha1.2) (nat_dvd_int ha3.2)) (nat_dvd_int ha2.1)
      have heq : (((α 1 + α 4 + α 5 : Nat) : Int) - ((α 2 + α 4 + α 5 : Nat) : Int) + (α 2 : Int)) = (α 1 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e5 := h3_1 e1 ha3.1 ha2.2
    have e4 := h3_2 e1 e5 ha1.2
    exact fin6_cases ha1.1 e1 ha2.1 ha3.1 e4 e5
  · -- (0, 2, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv4] at ha1 ha2 ha3
    have e1 : α 1 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (nat_dvd_int ha2.2) (nat_dvd_int ha1.1)) (nat_dvd_int ha3.2)
      have heq : (((α 1 + α 3 + α 5 : Nat) : Int) + (α 0 : Int) - ((α 0 + α 3 + α 5 : Nat) : Int)) = (α 1 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e5 := h3_1 e1 ha3.1 ha1.2
    have e3 := h3_2 e1 e5 ha2.2
    exact fin6_cases ha1.1 e1 ha2.1 e3 ha3.1 e5
  · -- (0, 2, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv2, hmv5] at ha1 ha2 ha3
    have e1 : α 1 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
        (Int.dvd_add (nat_dvd_int ha3.2) (Int.dvd_add (nat_dvd_int ha3.1) (nat_dvd_int ha3.1)))
      have heq : (((α 1 + α 4 + α 5 : Nat) : Int) + ((α 1 + α 3 + α 5 : Nat) : Int) + (α 0 : Int) + (α 2 : Int) -
                  (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) + ((α 5 : Int) + (α 5 : Int)))) = (α 1 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e4 := h3_2 e1 ha3.1 ha1.2
    have e3 := h3_2 e1 ha3.1 ha2.2
    exact fin6_cases ha1.1 e1 ha2.1 e3 e4 ha3.1
  · -- (0, 3, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv3, hmv4] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha2.1 ha3.2
    have e1 := h3_3 ha3.1 e5 ha1.2
    have e2 := h3_3 ha3.1 e5 ha2.2
    exact fin6_cases ha1.1 e1 e2 ha2.1 ha3.1 e5
  · -- (0, 3, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv3, hmv5] at ha1 ha2 ha3
    have e4 : α 4 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
        (Int.dvd_add (nat_dvd_int ha3.2) (Int.dvd_add (nat_dvd_int ha3.1) (nat_dvd_int ha3.1)))
      have heq : (((α 1 + α 4 + α 5 : Nat) : Int) + ((α 2 + α 4 + α 5 : Nat) : Int) + (α 0 : Int) + (α 3 : Int) -
                  (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) + ((α 5 : Int) + (α 5 : Int)))) = (α 4 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e1 := h3_3 e4 ha3.1 ha1.2
    have e2 := h3_3 e4 ha3.1 ha2.2
    exact fin6_cases ha1.1 e1 e2 ha2.1 e4 ha3.1
  · -- (0, 4, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv0, hmv4, hmv5] at ha1 ha2 ha3
    have e1 := h3_3 ha2.1 ha3.1 ha1.2
    have e3 := h3_2 ha1.1 ha3.1 ha2.2
    have e2 : α 2 % d = 0 := by
      have hd := Int.dvd_sub (nat_dvd_int ha3.2)
        (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.1) (nat_dvd_int e1)) (nat_dvd_int e3)) (nat_dvd_int ha2.1))
      have heq : (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) - ((α 0 : Int) + (α 1 : Int) + (α 3 : Int) + (α 4 : Int))) = (α 2 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    exact fin6_cases ha1.1 e1 e2 e3 ha2.1 ha3.1
  · -- (1, 2, 3)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv3] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha3.1 ha2.2
    have e0 := h3_3 ha2.1 e5 ha1.2
    have e4 := h3_2 ha2.1 e5 ha3.2
    exact fin6_cases e0 ha1.1 ha2.1 ha3.1 e4 e5
  · -- (1, 2, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv4] at ha1 ha2 ha3
    have e3 : α 3 % d = 0 := by
      have hd := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha3.2) (nat_dvd_int ha1.2)) (nat_dvd_int ha2.1)
      have heq : (((α 0 + α 3 + α 5 : Nat) : Int) - ((α 0 + α 2 + α 5 : Nat) : Int) + (α 2 : Int)) = (α 3 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e5 := h3_1 ha1.1 e3 ha2.2
    have e0 := h3_3 ha2.1 e5 ha1.2
    exact fin6_cases e0 ha1.1 ha2.1 e3 ha3.1 e5
  · -- (1, 2, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv2, hmv5] at ha1 ha2 ha3
    have e0 := h3_3 ha2.1 ha3.1 ha1.2
    have e3 := h3_2 ha1.1 ha3.1 ha2.2
    have e4 := h5_zero e0 ha1.1 ha2.1 e3 ha3.2
    exact fin6_cases e0 ha1.1 ha2.1 e3 e4 ha3.1
  · -- (1, 3, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv3, hmv4] at ha1 ha2 ha3
    have e2 : α 2 % d = 0 := by
      have hd2 := Int.dvd_add (Int.dvd_sub (nat_dvd_int ha1.2) (nat_dvd_int ha3.2)) (nat_dvd_int ha2.1)
      have heq2 : (((α 0 + α 2 + α 5 : Nat) : Int) - ((α 0 + α 3 + α 5 : Nat) : Int) + (α 3 : Int)) = (α 2 : Int) := by omega
      rw [heq2] at hd2; exact dvd_int_cancel_nat hd2
    have e5 := h3_1 e2 ha3.1 ha2.2
    have e0 := h3_3 e2 e5 ha1.2
    exact fin6_cases e0 ha1.1 e2 ha2.1 ha3.1 e5
  · -- (1, 3, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv3, hmv5] at ha1 ha2 ha3
    have e2 : α 2 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
        (Int.dvd_add (nat_dvd_int ha3.2) (Int.dvd_add (nat_dvd_int ha3.1) (nat_dvd_int ha3.1)))
      have heq : (((α 0 + α 2 + α 5 : Nat) : Int) + ((α 2 + α 4 + α 5 : Nat) : Int) + (α 1 : Int) + (α 3 : Int) -
                  (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) + ((α 5 : Int) + (α 5 : Int)))) = (α 2 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e0 := h3_3 e2 ha3.1 ha1.2
    have e4 := h3_2 e2 ha3.1 ha2.2
    exact fin6_cases e0 ha1.1 e2 ha2.1 e4 ha3.1
  · -- (1, 4, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv1, hmv4, hmv5] at ha1 ha2 ha3
    have e0 : α 0 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
        (Int.dvd_add (nat_dvd_int ha3.2) (Int.dvd_add (nat_dvd_int ha3.1) (nat_dvd_int ha3.1)))
      have heq : (((α 0 + α 2 + α 5 : Nat) : Int) + ((α 0 + α 3 + α 5 : Nat) : Int) + (α 1 : Int) + (α 4 : Int) -
                  (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) + ((α 5 : Int) + (α 5 : Int)))) = (α 0 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e2 := h3_2 e0 ha3.1 ha1.2
    have e3 := h3_2 e0 ha3.1 ha2.2
    exact fin6_cases e0 ha1.1 e2 e3 ha2.1 ha3.1
  · -- (2, 3, 4)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv3, hmv4] at ha1 ha2 ha3
    have e5 := h3_1 ha1.1 ha3.1 ha2.2
    have e1 := h3_3 ha2.1 e5 ha1.2
    have e0 := h3_3 ha2.1 e5 ha3.2
    exact fin6_cases e0 e1 ha1.1 ha2.1 ha3.1 e5
  · -- (2, 3, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv3, hmv5] at ha1 ha2 ha3
    have e1 := h3_3 ha2.1 ha3.1 ha1.2
    have e4 := h3_2 ha1.1 ha3.1 ha2.2
    have e0 : α 0 % d = 0 := by
      have hd := Int.dvd_sub (nat_dvd_int ha3.2)
        (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int e1) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1)) (nat_dvd_int e4))
      have heq : (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) - ((α 1 : Int) + (α 2 : Int) + (α 3 : Int) + (α 4 : Int))) = (α 0 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    exact fin6_cases e0 e1 ha1.1 ha2.1 e4 ha3.1
  · -- (2, 4, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv2, hmv4, hmv5] at ha1 ha2 ha3
    have e3 : α 3 % d = 0 := by
      have hd := Int.dvd_sub (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int ha1.2) (nat_dvd_int ha2.2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
        (Int.dvd_add (nat_dvd_int ha3.2) (Int.dvd_add (nat_dvd_int ha3.1) (nat_dvd_int ha3.1)))
      have heq : (((α 1 + α 3 + α 5 : Nat) : Int) + ((α 0 + α 3 + α 5 : Nat) : Int) + (α 2 : Int) + (α 4 : Int) -
                  (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) + ((α 5 : Int) + (α 5 : Int)))) = (α 3 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    have e1 := h3_3 e3 ha3.1 ha1.2
    have e0 := h3_3 e3 ha3.1 ha2.2
    exact fin6_cases e0 e1 ha1.1 e3 ha2.1 ha3.1
  · -- (3, 4, 5)
    unfold pauliActive at ha1 ha2 ha3
    simp only [decide_eq_false_iff_not, not_or, Decidable.not_not, hmv3, hmv4, hmv5] at ha1 ha2 ha3
    have e2 := h3_3 ha2.1 ha3.1 ha1.2
    have e0 := h3_3 ha1.1 ha3.1 ha2.2
    have e1 : α 1 % d = 0 := by
      have hd := Int.dvd_sub (nat_dvd_int ha3.2)
        (Int.dvd_add (Int.dvd_add (Int.dvd_add (nat_dvd_int e0) (nat_dvd_int e2)) (nat_dvd_int ha1.1)) (nat_dvd_int ha2.1))
      have heq : (((α 0 + α 1 + α 2 + α 3 + α 4 : Nat) : Int) - ((α 0 : Int) + (α 2 : Int) + (α 3 : Int) + (α 4 : Int))) = (α 1 : Int) := by omega
      rw [heq] at hd; exact dvd_int_cancel_nat hd
    exact fin6_cases e0 e1 e2 ha1.1 ha2.1 ha3.1

public theorem graphWheel5_ame_all_d (d : Nat) (_hd : d ≥ 2) : IsAMEGraph d graphWheel5 := by
  intro α ⟨i0, hi0⟩
  exact Classical.byContradiction fun hle => by
    have hlt : countFin 6 (pauliActive d graphWheel5 α) ≤ 3 := by
      unfold pauliWeight at hle; omega
    rcases exists_three_false_fin6 _ hlt with ⟨i1, i2, i3, h12, h23, f1, f2, f3⟩
    exact hi0 (wheel5_three_inactive_forces_zero α i1 i2 i3 h12 h23 f1 f2 f3 i0)

/-- **T1b (Universal Unimodular Existence Theorem):** For ALL `d ≥ 2`, canonical `Z_d`
graph-state `AME(N, d)` exists for every `N ∈ {2, 3, 5, 6}` via `K_2`, `K_3`, `C_5`,
`K_3 □ K_2`, and `W_5`. -/
public theorem universal_unimodular_graphs_all_d (d : Nat) (hd : d ≥ 2) :
    IsAMEGraph d graphK2 ∧ IsAMEGraph d graphK3 ∧
    IsAMEGraph d graphC5 ∧ IsAMEGraph d graphPrism6 ∧ IsAMEGraph d graphWheel5 :=
  ⟨graphK2_ame_all_d d hd, graphK3_ame_all_d d hd, graphC5_ame_all_d d hd,
   graphPrism6_ame_all_d d hd, graphWheel5_ame_all_d d hd⟩

/-! ## Section 4: T1c — Pure-Integer Combinatorial Pless Power-Moment Obstruction (ALL `p ≥ 2`) -/

@[expose] public def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

public theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ _ => rfl
  | succ m ih =>
    cases k with
    | zero => omega
    | succ r =>
      simp only [choose]
      rw [ih (by omega), ih (by omega)]

public theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [choose, ih, choose_eq_zero_of_lt (Nat.lt_succ_self m)]

public theorem choose_one_right (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [choose, ih]
    omega

public theorem succ_mul_choose_eq (n k : Nat) (hk : k ≤ n) :
    (k + 1) * choose n (k + 1) = (n - k) * choose n k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ m ih =>
    cases k with
    | zero => simp [choose, choose_one_right]; omega
    | succ r =>
      by_cases hrm : r + 1 ≤ m
      · have h1 := ih (r + 1) hrm
        have h2 := ih r (by omega)
        simp only [choose]
        have hstep1 : (r + 2) * (choose m (r + 1) + choose m (r + 2)) =
                      (r + 1) * choose m (r + 1) + choose m (r + 1) + (r + 2) * choose m (r + 2) := by
          rw [Nat.mul_add, Nat.add_mul (r + 1) 1, Nat.one_mul]
        rw [hstep1, h2, h1]
        have hsub : m + 1 - (r + 1) = m - r := by omega
        have hsub2 : 1 + (m - (r + 1)) = m - r := by omega
        rw [hsub, Nat.mul_add, Nat.add_assoc]
        congr 1
        calc choose m (r + 1) + (m - (r + 1)) * choose m (r + 1)
            = (1 + (m - (r + 1))) * choose m (r + 1) := by rw [Nat.add_mul, Nat.one_mul]
          _ = (m - r) * choose m (r + 1) := by rw [hsub2]
      · have heq : m = r := by omega
        subst heq
        simp [choose_eq_zero_of_lt (Nat.lt_succ_self (m + 1))]

public theorem choose_pos {n k : Nat} (hk : k ≤ n) : choose n k > 0 := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; decide
  | succ m ih =>
    cases k with
    | zero => simp [choose]
    | succ r =>
      simp only [choose]
      have h1 := ih (k := r) (by omega)
      omega

public structure PlessEvenSpec (k p : Nat) (A : Nat → Nat) : Prop where
  a0 : A 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → A w = 0
  moment_r1 : choose (2 * k) (k - 1) + A (k + 1) = choose (2 * k) (k - 1) * p ^ 2
  moment_r2 : choose (2 * k) (k - 2) + A (k + 1) * (k - 1) + A (k + 2) =
              choose (2 * k) (k - 2) * p ^ 4

public structure PlessOddSpec (k p : Nat) (A : Nat → Nat) : Prop where
  a0 : A 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → A w = 0
  moment_r1 : choose (2 * k + 1) k + A (k + 1) = choose (2 * k + 1) k * p
  moment_r2 : choose (2 * k + 1) (k - 1) + A (k + 1) * k + A (k + 2) =
              choose (2 * k + 1) (k - 1) * p ^ 3

/-- **T1c (Part 1 — Even-`N` Pless Obstruction, ALL `p ≥ 2`):** `k < p²`. -/
public theorem pless_even_obstruction {k p : Nat} {A : Nat → Nat}
    (hp : p ≥ 2) (hk : k ≥ 2) (hs : PlessEvenSpec k p A) : k < p ^ 2 := by
  have hcho_pos : choose (2 * k) (k - 2) > 0 := choose_pos (by omega)
  have hrel : (k - 1) * choose (2 * k) (k - 1) = (k + 2) * choose (2 * k) (k - 2) := by
    have h := succ_mul_choose_eq (2 * k) (k - 2) (by omega)
    have he1 : k - 2 + 1 = k - 1 := by omega
    have he2 : 2 * k - (k - 2) = k + 2 := by omega
    rw [he1, he2] at h; exact h
  have hp2_ge : p ^ 2 ≥ 4 := by
    have : p ^ 2 = p * p := by simp [Nat.pow_succ]
    have hmul : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
    omega
  have ha1 : A (k + 1) = choose (2 * k) (k - 1) * (p ^ 2 - 1) := by
    have h1 := hs.moment_r1
    have hmul : choose (2 * k) (k - 1) * p ^ 2 = choose (2 * k) (k - 1) + choose (2 * k) (k - 1) * (p ^ 2 - 1) := by
      calc choose (2 * k) (k - 1) * p ^ 2
          = choose (2 * k) (k - 1) * (1 + (p ^ 2 - 1)) := by congr 1; omega
        _ = choose (2 * k) (k - 1) + choose (2 * k) (k - 1) * (p ^ 2 - 1) := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hterm : A (k + 1) * (k - 1) = (k + 2) * choose (2 * k) (k - 2) * (p ^ 2 - 1) := by
    calc A (k + 1) * (k - 1)
        = choose (2 * k) (k - 1) * (p ^ 2 - 1) * (k - 1) := by rw [ha1]
      _ = ((k - 1) * choose (2 * k) (k - 1)) * (p ^ 2 - 1) := by
          rw [Nat.mul_right_comm, Nat.mul_comm (choose (2 * k) (k - 1)) (k - 1)]
      _ = (k + 2) * choose (2 * k) (k - 2) * (p ^ 2 - 1) := by rw [hrel]
  have h2 := hs.moment_r2
  rw [hterm] at h2
  have hp4 : p ^ 4 = 1 + (p ^ 2 - 1) * (p ^ 2 + 1) := by
    have hpow : p ^ 4 = p ^ 2 * p ^ 2 := by simp [Nat.pow_succ, Nat.mul_assoc]
    rw [hpow]
    have hsub : (p ^ 2 - 1) * (p ^ 2 + 1) + 1 = p ^ 2 * p ^ 2 := by
      calc (p ^ 2 - 1) * (p ^ 2 + 1) + 1
          = (p ^ 2 - 1) * p ^ 2 + (p ^ 2 - 1) + 1 := by rw [Nat.mul_add, Nat.mul_one]
        _ = (p ^ 2 - 1) * p ^ 2 + p ^ 2 := by omega
        _ = (p ^ 2 - 1 + 1) * p ^ 2 := by rw [Nat.add_mul, Nat.one_mul]
        _ = p ^ 2 * p ^ 2 := by congr 1; omega
    omega
  have hineq : choose (2 * k) (k - 2) * ((k + 2) * (p ^ 2 - 1)) ≤
               choose (2 * k) (k - 2) * ((p ^ 2 + 1) * (p ^ 2 - 1)) := by
    have hlhs : choose (2 * k) (k - 2) + (k + 2) * choose (2 * k) (k - 2) * (p ^ 2 - 1) =
                choose (2 * k) (k - 2) + choose (2 * k) (k - 2) * ((k + 2) * (p ^ 2 - 1)) := by
      congr 1; rw [Nat.mul_comm (k + 2), Nat.mul_assoc]
    have hrhs : choose (2 * k) (k - 2) * p ^ 4 =
                choose (2 * k) (k - 2) + choose (2 * k) (k - 2) * ((p ^ 2 + 1) * (p ^ 2 - 1)) := by
      rw [hp4, Nat.mul_add, Nat.mul_one, Nat.mul_comm (p ^ 2 - 1) (p ^ 2 + 1)]
    omega
  have hcancel1 : (k + 2) * (p ^ 2 - 1) ≤ (p ^ 2 + 1) * (p ^ 2 - 1) :=
    Nat.le_of_mul_le_mul_left hineq hcho_pos
  have hcancel2 : k + 2 ≤ p ^ 2 + 1 :=
    Nat.le_of_mul_le_mul_right hcancel1 (by omega)
  omega

/-- **T1c (Part 2 — Odd-`N` Pless Obstruction, ALL `p ≥ 2`):** `k < p² + p`. -/
public theorem pless_odd_obstruction {k p : Nat} {A : Nat → Nat}
    (hp : p ≥ 2) (hk : k ≥ 2) (hs : PlessOddSpec k p A) : k < p ^ 2 + p := by
  have hcho_pos : choose (2 * k + 1) (k - 1) > 0 := choose_pos (by omega)
  have hrel : k * choose (2 * k + 1) k = (k + 2) * choose (2 * k + 1) (k - 1) := by
    have h := succ_mul_choose_eq (2 * k + 1) (k - 1) (by omega)
    have he1 : k - 1 + 1 = k := by omega
    have he2 : 2 * k + 1 - (k - 1) = k + 2 := by omega
    rw [he1, he2] at h; exact h
  have ha1 : A (k + 1) = choose (2 * k + 1) k * (p - 1) := by
    have h1 := hs.moment_r1
    have hmul : choose (2 * k + 1) k * p = choose (2 * k + 1) k + choose (2 * k + 1) k * (p - 1) := by
      calc choose (2 * k + 1) k * p
          = choose (2 * k + 1) k * (1 + (p - 1)) := by congr 1; omega
        _ = choose (2 * k + 1) k + choose (2 * k + 1) k * (p - 1) := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hterm : A (k + 1) * k = (k + 2) * choose (2 * k + 1) (k - 1) * (p - 1) := by
    calc A (k + 1) * k
        = choose (2 * k + 1) k * (p - 1) * k := by rw [ha1]
      _ = (k * choose (2 * k + 1) k) * (p - 1) := by
          rw [Nat.mul_right_comm, Nat.mul_comm (choose (2 * k + 1) k) k]
      _ = (k + 2) * choose (2 * k + 1) (k - 1) * (p - 1) := by rw [hrel]
  have h2 := hs.moment_r2
  rw [hterm] at h2
  have hp3 : p ^ 3 = 1 + (p ^ 2 + p + 1) * (p - 1) := by
    have hpow2 : p ^ 2 = p * p := by simp [Nat.pow_succ]
    have hpow3 : p ^ 3 = p * p * p := by simp [Nat.pow_succ, Nat.mul_assoc]
    rw [hpow3, hpow2]
    have hexp : (p * p + p + 1) * (p - 1) + 1 = p * p * p := by
      have h1 : (p * p + p + 1) * p = (p * p + p + 1) * (p - 1) + (p * p + p + 1) := by
        calc (p * p + p + 1) * p = (p * p + p + 1) * ((p - 1) + 1) := by congr 1; omega
          _ = (p * p + p + 1) * (p - 1) + (p * p + p + 1) := by rw [Nat.mul_add, Nat.mul_one]
      have h2 : (p * p + p + 1) * p = p * p * p + p * p + p := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      omega
    omega
  have hineq : choose (2 * k + 1) (k - 1) * ((k + 2) * (p - 1)) ≤
               choose (2 * k + 1) (k - 1) * ((p ^ 2 + p + 1) * (p - 1)) := by
    have hlhs : choose (2 * k + 1) (k - 1) + (k + 2) * choose (2 * k + 1) (k - 1) * (p - 1) =
                choose (2 * k + 1) (k - 1) + choose (2 * k + 1) (k - 1) * ((k + 2) * (p - 1)) := by
      congr 1; rw [Nat.mul_comm (k + 2), Nat.mul_assoc]
    have hrhs : choose (2 * k + 1) (k - 1) * p ^ 3 =
                choose (2 * k + 1) (k - 1) + choose (2 * k + 1) (k - 1) * ((p ^ 2 + p + 1) * (p - 1)) := by
      rw [hp3, Nat.mul_add, Nat.mul_one]
    omega
  have hcancel1 : (k + 2) * (p - 1) ≤ (p ^ 2 + p + 1) * (p - 1) :=
    Nat.le_of_mul_le_mul_left hineq hcho_pos
  have hcancel2 : k + 2 ≤ p ^ 2 + p + 1 :=
    Nat.le_of_mul_le_mul_right hcancel1 (by omega)
  omega

/-! ## Section 5: T1d — Binary Commuting-Weight Homomorphism & Rains Shadow (`N ∈ {4,7,9,11}`) -/

public def wtBit (p : Bool × Bool) : Nat := if p.1 || p.2 then 1 else 0
public def sympBit (p q : Bool × Bool) : Bool := xor (p.1 && q.2) (p.2 && q.1)
public def xorBit (p q : Bool × Bool) : Bool × Bool := (xor p.1 q.1, xor p.2 q.2)

public theorem wtBit_xor_mod2 (a b : Bool × Bool) :
    (wtBit (xorBit a b) + wtBit a + wtBit b) % 2 = (if sympBit a b then 1 else 0) := by
  cases a with | mk a1 a2 =>
  cases b with | mk b1 b2 =>
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> rfl

public def pauliWeightF2 {N : Nat} (u : Fin N → Bool × Bool) : Nat :=
  sumFin N (fun i => wtBit (u i))

public def sympF2 : {N : Nat} → (Fin N → Bool × Bool) → (Fin N → Bool × Bool) → Bool
  | 0, _, _ => false
  | n + 1, u, v => xor (sympF2 (fun i => u i.castSucc) (fun i => v i.castSucc))
                       (sympBit (u ⟨n, Nat.lt_succ_self n⟩) (v ⟨n, Nat.lt_succ_self n⟩))

public def xorF2 {N : Nat} (u v : Fin N → Bool × Bool) : Fin N → Bool × Bool :=
  fun i => xorBit (u i) (v i)

/-- **T1d (Part 1 — Commuting-Weight Homomorphism, ALL `N`).** -/
public theorem f2_commuting_weight_homomorphism {N : Nat} (u v : Fin N → Bool × Bool) :
    (pauliWeightF2 (xorF2 u v) + pauliWeightF2 u + pauliWeightF2 v) % 2 =
    (if sympF2 u v then 1 else 0) := by
  induction N with
  | zero => rfl
  | succ k ih =>
    let u' : Fin k → Bool × Bool := fun i => u i.castSucc
    let v' : Fin k → Bool × Bool := fun i => v i.castSucc
    have hih := ih u' v'
    have hlast := wtBit_xor_mod2 (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, Nat.lt_succ_self k⟩)
    unfold pauliWeightF2 xorF2 at hih ⊢
    simp only [sumFin]
    have hrearr :
        (sumFin k (fun i => wtBit (xorBit (u i.castSucc) (v i.castSucc))) +
          wtBit (xorBit (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, Nat.lt_succ_self k⟩))) +
        (sumFin k (fun i => wtBit (u i.castSucc)) + wtBit (u ⟨k, Nat.lt_succ_self k⟩)) +
        (sumFin k (fun i => wtBit (v i.castSucc)) + wtBit (v ⟨k, Nat.lt_succ_self k⟩)) =
        (sumFin k (fun i => wtBit (xorBit (u' i) (v' i))) +
          sumFin k (fun i => wtBit (u' i)) + sumFin k (fun i => wtBit (v' i))) +
        (wtBit (xorBit (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, Nat.lt_succ_self k⟩)) +
          wtBit (u ⟨k, Nat.lt_succ_self k⟩) + wtBit (v ⟨k, Nat.lt_succ_self k⟩)) := by
      dsimp only [u', v']; omega
    rw [hrearr, Nat.add_mod, hih, hlast]
    have hsymp : sympF2 u v = xor (sympF2 u' v') (sympBit (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, Nat.lt_succ_self k⟩)) := rfl
    rw [hsymp]
    generalize sympF2 u' v' = b1
    generalize sympBit (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, Nat.lt_succ_self k⟩) = b2
    cases b1 <;> cases b2 <;> rfl

public theorem f2_commuting_weight_additive {N : Nat} (u v : Fin N → Bool × Bool)
    (hcomm : sympF2 u v = false) :
    pauliWeightF2 (xorF2 u v) % 2 = (pauliWeightF2 u + pauliWeightF2 v) % 2 := by
  have h := f2_commuting_weight_homomorphism u v
  rw [hcomm] at h
  simp only [Bool.false_eq_true, ite_false] at h
  omega

public def krawtchouk4 (j w N : Nat) : Int :=
  sumFinInt (j + 1) (fun r =>
    let sign : Int := if r.val % 2 = 0 then 1 else -1
    sign * (3 ^ (j - r.val) : Nat) * (choose w r.val : Int) * (choose (N - w) (j - r.val) : Int))

public structure RainsShadowQubitAME (N : Nat) (A : Fin (N + 1) → Nat) (S : Fin (N + 1) → Nat) : Prop where
  a0 : A ⟨0, Nat.zero_lt_succ N⟩ = 1
  zero_below : ∀ w : Fin (N + 1), 1 ≤ w.val → w.val ≤ N / 2 → A w = 0
  macwilliams : ∀ j : Fin (N + 1),
    sumFinInt (N + 1) (fun w => (A w : Int) * krawtchouk4 j.val w.val N) =
    (2 ^ N : Int) * (A j : Int)
  shadow : ∀ j : Fin (N + 1),
    sumFinInt (N + 1) (fun w =>
      (if w.val % 2 = 0 then (1 : Int) else -1) * (A w : Int) * krawtchouk4 j.val w.val N) =
    (2 ^ N : Int) * (S j : Int)

public theorem rains_shadow_no_ame4 {A S : Fin 5 → Nat} (h : RainsShadowQubitAME 4 A S) : False := by
  have hm0 := h.macwilliams ⟨0, by decide⟩
  have hm1 := h.macwilliams ⟨1, by decide⟩
  have hm2 := h.macwilliams ⟨2, by decide⟩
  have hs0 := h.shadow ⟨0, by decide⟩
  have ha0 := h.a0
  have ha1 := h.zero_below ⟨1, by decide⟩ (by decide) (by decide)
  have ha2 := h.zero_below ⟨2, by decide⟩ (by decide) (by decide)
  simp only [sumFinInt, Fin.castSucc_mk] at hm0 hm1 hm2 hs0
  rw [ha0, ha1, ha2] at hm0 hm1 hm2 hs0
  simp only [show krawtchouk4 0 0 4 = 1 by decide, show krawtchouk4 0 3 4 = 1 by decide, show krawtchouk4 0 4 4 = 1 by decide,
             show krawtchouk4 1 0 4 = 12 by decide, show krawtchouk4 1 3 4 = 0 by decide, show krawtchouk4 1 4 4 = -4 by decide,
             show krawtchouk4 2 0 4 = 54 by decide, show krawtchouk4 2 3 4 = -6 by decide, show krawtchouk4 2 4 4 = 6 by decide] at hm0 hm1 hm2 hs0
  simp at hm0 hm1 hm2 hs0
  omega

public theorem rains_shadow_no_ame7 {A S : Fin 8 → Nat} (h : RainsShadowQubitAME 7 A S) : False := by
  have hm0 := h.macwilliams ⟨0, by decide⟩
  have hm1 := h.macwilliams ⟨1, by decide⟩
  have hm2 := h.macwilliams ⟨2, by decide⟩
  have hm3 := h.macwilliams ⟨3, by decide⟩
  have hs1 := h.shadow ⟨1, by decide⟩
  have ha0 := h.a0
  have ha1 := h.zero_below ⟨1, by decide⟩ (by decide) (by decide)
  have ha2 := h.zero_below ⟨2, by decide⟩ (by decide) (by decide)
  have ha3 := h.zero_below ⟨3, by decide⟩ (by decide) (by decide)
  simp only [sumFinInt, Fin.castSucc_mk] at hm0 hm1 hm2 hm3 hs1
  rw [ha0, ha1, ha2, ha3] at hm0 hm1 hm2 hm3 hs1
  simp only [show krawtchouk4 0 0 7 = 1 by decide, show krawtchouk4 0 4 7 = 1 by decide, show krawtchouk4 0 5 7 = 1 by decide, show krawtchouk4 0 6 7 = 1 by decide, show krawtchouk4 0 7 7 = 1 by decide,
             show krawtchouk4 1 0 7 = 21 by decide, show krawtchouk4 1 4 7 = 5 by decide, show krawtchouk4 1 5 7 = 1 by decide, show krawtchouk4 1 6 7 = -3 by decide, show krawtchouk4 1 7 7 = -7 by decide,
             show krawtchouk4 2 0 7 = 189 by decide, show krawtchouk4 2 4 7 = -3 by decide, show krawtchouk4 2 5 7 = -11 by decide, show krawtchouk4 2 6 7 = -3 by decide, show krawtchouk4 2 7 7 = 21 by decide,
             show krawtchouk4 3 0 7 = 945 by decide, show krawtchouk4 3 4 7 = -31 by decide, show krawtchouk4 3 5 7 = 5 by decide, show krawtchouk4 3 6 7 = 25 by decide, show krawtchouk4 3 7 7 = -35 by decide] at hm0 hm1 hm2 hm3 hs1
  simp at hm0 hm1 hm2 hm3 hs1
  omega

public theorem rains_shadow_no_ame9 {A S : Fin 10 → Nat} (h : RainsShadowQubitAME 9 A S) : False := by
  have hm0 := h.macwilliams ⟨0, by decide⟩
  have hm1 := h.macwilliams ⟨1, by decide⟩
  have hm2 := h.macwilliams ⟨2, by decide⟩
  have hm3 := h.macwilliams ⟨3, by decide⟩
  have hm4 := h.macwilliams ⟨4, by decide⟩
  have hs1 := h.shadow ⟨1, by decide⟩
  have ha0 := h.a0
  have ha1 := h.zero_below ⟨1, by decide⟩ (by decide) (by decide)
  have ha2 := h.zero_below ⟨2, by decide⟩ (by decide) (by decide)
  have ha3 := h.zero_below ⟨3, by decide⟩ (by decide) (by decide)
  have ha4 := h.zero_below ⟨4, by decide⟩ (by decide) (by decide)
  simp only [sumFinInt, Fin.castSucc_mk] at hm0 hm1 hm2 hm3 hm4 hs1
  rw [ha0, ha1, ha2, ha3, ha4] at hm0 hm1 hm2 hm3 hm4 hs1
  simp only [show krawtchouk4 0 0 9 = 1 by decide, show krawtchouk4 0 5 9 = 1 by decide, show krawtchouk4 0 6 9 = 1 by decide, show krawtchouk4 0 7 9 = 1 by decide, show krawtchouk4 0 8 9 = 1 by decide, show krawtchouk4 0 9 9 = 1 by decide,
             show krawtchouk4 1 0 9 = 27 by decide, show krawtchouk4 1 5 9 = 7 by decide, show krawtchouk4 1 6 9 = 3 by decide, show krawtchouk4 1 7 9 = -1 by decide, show krawtchouk4 1 8 9 = -5 by decide, show krawtchouk4 1 9 9 = -9 by decide,
             show krawtchouk4 2 0 9 = 324 by decide, show krawtchouk4 2 5 9 = 4 by decide, show krawtchouk4 2 6 9 = -12 by decide, show krawtchouk4 2 7 9 = -12 by decide, show krawtchouk4 2 8 9 = 4 by decide, show krawtchouk4 2 9 9 = 36 by decide,
             show krawtchouk4 3 0 9 = 2268 by decide, show krawtchouk4 3 5 9 = -52 by decide, show krawtchouk4 3 6 9 = -20 by decide, show krawtchouk4 3 7 9 = 28 by decide, show krawtchouk4 3 8 9 = 28 by decide, show krawtchouk4 3 9 9 = -84 by decide,
             show krawtchouk4 4 0 9 = 10206 by decide, show krawtchouk4 4 5 9 = -34 by decide, show krawtchouk4 4 6 9 = 78 by decide, show krawtchouk4 4 7 9 = 14 by decide, show krawtchouk4 4 8 9 = -98 by decide, show krawtchouk4 4 9 9 = 126 by decide] at hm0 hm1 hm2 hm3 hm4 hs1
  simp at hm0 hm1 hm2 hm3 hm4 hs1
  omega

public theorem rains_shadow_no_ame11 {A S : Fin 12 → Nat} (h : RainsShadowQubitAME 11 A S) : False := by
  have hm0 := h.macwilliams ⟨0, by decide⟩
  have hm1 := h.macwilliams ⟨1, by decide⟩
  have hm2 := h.macwilliams ⟨2, by decide⟩
  have hm3 := h.macwilliams ⟨3, by decide⟩
  have hm4 := h.macwilliams ⟨4, by decide⟩
  have hm5 := h.macwilliams ⟨5, by decide⟩
  have hs3 := h.shadow ⟨3, by decide⟩
  have ha0 := h.a0
  have ha1 := h.zero_below ⟨1, by decide⟩ (by decide) (by decide)
  have ha2 := h.zero_below ⟨2, by decide⟩ (by decide) (by decide)
  have ha3 := h.zero_below ⟨3, by decide⟩ (by decide) (by decide)
  have ha4 := h.zero_below ⟨4, by decide⟩ (by decide) (by decide)
  have ha5 := h.zero_below ⟨5, by decide⟩ (by decide) (by decide)
  simp only [sumFinInt, Fin.castSucc_mk] at hm0 hm1 hm2 hm3 hm4 hm5 hs3
  rw [ha0, ha1, ha2, ha3, ha4, ha5] at hm0 hm1 hm2 hm3 hm4 hm5 hs3
  simp only [show krawtchouk4 0 0 11 = 1 by decide, show krawtchouk4 0 6 11 = 1 by decide, show krawtchouk4 0 7 11 = 1 by decide, show krawtchouk4 0 8 11 = 1 by decide, show krawtchouk4 0 9 11 = 1 by decide, show krawtchouk4 0 10 11 = 1 by decide, show krawtchouk4 0 11 11 = 1 by decide,
             show krawtchouk4 1 0 11 = 33 by decide, show krawtchouk4 1 6 11 = 9 by decide, show krawtchouk4 1 7 11 = 5 by decide, show krawtchouk4 1 8 11 = 1 by decide, show krawtchouk4 1 9 11 = -3 by decide, show krawtchouk4 1 10 11 = -7 by decide, show krawtchouk4 1 11 11 = -11 by decide,
             show krawtchouk4 2 0 11 = 495 by decide, show krawtchouk4 2 6 11 = 15 by decide, show krawtchouk4 2 7 11 = -9 by decide, show krawtchouk4 2 8 11 = -17 by decide, show krawtchouk4 2 9 11 = -9 by decide, show krawtchouk4 2 10 11 = 15 by decide, show krawtchouk4 2 11 11 = 55 by decide,
             show krawtchouk4 3 0 11 = 4455 by decide, show krawtchouk4 3 6 11 = -65 by decide, show krawtchouk4 3 7 11 = -53 by decide, show krawtchouk4 3 8 11 = 7 by decide, show krawtchouk4 3 9 11 = 51 by decide, show krawtchouk4 3 10 11 = 15 by decide, show krawtchouk4 3 11 11 = -165 by decide,
             show krawtchouk4 4 0 11 = 26730 by decide, show krawtchouk4 4 6 11 = -150 by decide, show krawtchouk4 4 7 11 = 74 by decide, show krawtchouk4 4 8 11 = 106 by decide, show krawtchouk4 4 9 11 = -54 by decide, show krawtchouk4 4 10 11 = -150 by decide, show krawtchouk4 4 11 11 = 330 by decide,
             show krawtchouk4 5 0 11 = 112266 by decide, show krawtchouk4 5 6 11 = 282 by decide, show krawtchouk4 5 7 11 = 210 by decide, show krawtchouk4 5 8 11 = -182 by decide, show krawtchouk4 5 9 11 = -126 by decide, show krawtchouk4 5 10 11 = 378 by decide, show krawtchouk4 5 11 11 = -462 by decide] at hm0 hm1 hm2 hm3 hm4 hm5 hs3
  simp at hm0 hm1 hm2 hm3 hm4 hm5 hs3
  omega

/-- Direct exhaustive obstruction on 4-vertex canonical `Z_2` graph states (ZERO shadow assumption!):
for every 6-bit binary symmetric graph on 4 vertices, some nonzero `α ∈ {0,1}^4` has Pauli weight ≤ 2. -/
private def graph4FromBits (e01 e02 e03 e12 e13 e23 : Bool) : Fin 4 → Fin 4 → Nat :=
  fun i j =>
    let b :=
      match i.val, j.val with
      | 0, 1 | 1, 0 => e01
      | 0, 2 | 2, 0 => e02
      | 0, 3 | 3, 0 => e03
      | 1, 2 | 2, 1 => e12
      | 1, 3 | 3, 1 => e13
      | 2, 3 | 3, 2 => e23
      | _, _ => false
    if b then 1 else 0

private def weight4Bits (e01 e02 e03 e12 e13 e23 : Bool) (a0 a1 a2 a3 : Bool) : Nat :=
  let g := graph4FromBits e01 e02 e03 e12 e13 e23
  let av : Fin 4 → Nat := fun i =>
    match i.val with | 0 => if a0 then 1 else 0 | 1 => if a1 then 1 else 0
                     | 2 => if a2 then 1 else 0 | _ => if a3 then 1 else 0
  countFin 4 (fun j => decide (av j % 2 ≠ 0 ∨ sumFin 4 (fun i => g j i * av i) % 2 ≠ 0))

private theorem all_64_graphs_have_weight_le2 :
    ∀ e01 e02 e03 e12 e13 e23 : Bool,
      ∃ a0 a1 a2 a3 : Bool, (a0 = true ∨ a1 = true ∨ a2 = true ∨ a3 = true) ∧
        weight4Bits e01 e02 e03 e12 e13 e23 a0 a1 a2 a3 ≤ 2 := by
  decide

public theorem no_canonical_graph_ame4_f2 (Γ : GraphAdj 4) : ¬ IsAMEGraph 2 Γ := by
  intro hame
  let e01 := decide (Γ.mat 0 1 % 2 = 1)
  let e02 := decide (Γ.mat 0 2 % 2 = 1)
  let e03 := decide (Γ.mat 0 3 % 2 = 1)
  let e12 := decide (Γ.mat 1 2 % 2 = 1)
  let e13 := decide (Γ.mat 1 3 % 2 = 1)
  let e23 := decide (Γ.mat 2 3 % 2 = 1)
  rcases all_64_graphs_have_weight_le2 e01 e02 e03 e12 e13 e23 with ⟨a0, a1, a2, a3, hne, hle⟩
  let α : Fin 4 → Nat := fun i =>
    match i.val with | 0 => if a0 then 1 else 0 | 1 => if a1 then 1 else 0
                     | 2 => if a2 then 1 else 0 | _ => if a3 then 1 else 0
  have hα_nt : ∃ i : Fin 4, α i % 2 ≠ 0 := by
    rcases hne with h0 | h1 | h2 | h3
    · exact ⟨0, by simp [α, h0]⟩
    · exact ⟨1, by simp [α, h1]⟩
    · exact ⟨2, by simp [α, h2]⟩
    · exact ⟨3, by simp [α, h3]⟩
  have hgt : pauliWeight 2 Γ α > 2 := hame α hα_nt
  have hmat_mod : ∀ i j : Fin 4, Γ.mat i j % 2 = graph4FromBits e01 e02 e03 e12 e13 e23 i j % 2 := by
    have hd0 := Γ.diag_zero 0; have hd1 := Γ.diag_zero 1; have hd2 := Γ.diag_zero 2; have hd3 := Γ.diag_zero 3
    have hs01 := Γ.symm 1 0; have hs02 := Γ.symm 2 0; have hs03 := Γ.symm 3 0
    have hs12 := Γ.symm 2 1; have hs13 := Γ.symm 3 1; have hs23 := Γ.symm 3 2
    have hfin4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    have hbit : ∀ n : Nat, n % 2 = (if decide (n % 2 = 1) then 1 else 0) % 2 := by
      intro n; by_cases h : n % 2 = 1 <;> simp [h] <;> omega
    intro i j
    rcases hfin4 i with rfl | rfl | rfl | rfl <;>
    rcases hfin4 j with rfl | rfl | rfl | rfl
    · simp [hd0, graph4FromBits]
    · exact hbit (Γ.mat 0 1)
    · exact hbit (Γ.mat 0 2)
    · exact hbit (Γ.mat 0 3)
    · rw [hs01]; exact hbit (Γ.mat 0 1)
    · simp [hd1, graph4FromBits]
    · exact hbit (Γ.mat 1 2)
    · exact hbit (Γ.mat 1 3)
    · rw [hs02]; exact hbit (Γ.mat 0 2)
    · rw [hs12]; exact hbit (Γ.mat 1 2)
    · simp [hd2, graph4FromBits]
    · exact hbit (Γ.mat 2 3)
    · rw [hs03]; exact hbit (Γ.mat 0 3)
    · rw [hs13]; exact hbit (Γ.mat 1 3)
    · rw [hs23]; exact hbit (Γ.mat 2 3)
    · simp [hd3, graph4FromBits]
  have hweq : pauliWeight 2 Γ α = weight4Bits e01 e02 e03 e12 e13 e23 a0 a1 a2 a3 := by
    unfold pauliWeight weight4Bits
    apply countFin_congr
    intro j
    unfold pauliActive matVec
    have hsm : sumFin 4 (fun i => Γ.mat j i * α i) % 2 =
               sumFin 4 (fun i => graph4FromBits e01 e02 e03 e12 e13 e23 j i * α i) % 2 := by
      apply sumFin_mod_congr
      intro i
      rw [Nat.mul_mod, hmat_mod j i, ← Nat.mul_mod]
    rw [hsm]
  omega

/-! ## Section 6: T1e — Cyclic Torsion-Rank Forcing, Additive MDS Obstruction & `Z_4` vs `F_4` Separation -/

public theorem torsion_rank_lower_and_free {m e N : Nat} (a : Fin m → Nat)
    (he : e ≥ 1) (hle : ∀ i, a i ≤ e) (hsum : sumFin m a = e * N) :
    m ≥ N ∧ (m = N → ∀ i, a i = e) := by
  have hbound : ∀ (r : Nat) (f : Fin r → Nat), (∀ i, f i ≤ e) → sumFin r f ≤ r * e := by
    intro r
    induction r with
    | zero => intro _ _; simp [sumFin]
    | succ q ih =>
      intro f hf
      simp only [sumFin]
      have h1 := ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
      have h2 := hf ⟨q, Nat.lt_succ_self q⟩
      have hm : (q + 1) * e = q * e + e := Nat.succ_mul q e
      omega
  have hb := hbound m a hle
  have hm_ge : m ≥ N := by
    have hmul : e * N ≤ e * m := by rw [Nat.mul_comm e m]; omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  refine ⟨hm_ge, ?_⟩
  intro hmn
  subst hmn
  intro i0
  exact Classical.byContradiction fun hne => by
    have hlt : a i0 < e := by have := hle i0; omega
    have hstrict : ∀ (r : Nat) (f : Fin r → Nat) (j : Fin r),
        (∀ i, f i ≤ e) → f j < e → sumFin r f < r * e := by
      intro r
      induction r with
      | zero => intro _ j; exact Fin.elim0 j
      | succ q ihq =>
        intro f j hf hj
        simp only [sumFin]
        have hm : (q + 1) * e = q * e + e := Nat.succ_mul q e
        by_cases hlast : j.val = q
        · have hjeq : j = ⟨q, Nat.lt_succ_self q⟩ := Fin.ext hlast
          rw [hjeq] at hj
          have hq := hbound q (fun i => f i.castSucc) (fun i => hf i.castSucc)
          omega
        · have hltq : j.val < q := by omega
          have h1 := ihq (fun i => f i.castSucc) ⟨j.val, hltq⟩ (fun i => hf i.castSucc) (by simpa using hj)
          have h2 := hf ⟨q, Nat.lt_succ_self q⟩
          omega
    have hbad := hstrict m a i0 hle hlt
    rw [hsum, Nat.mul_comm e m] at hbad
    omega

public structure AdditiveMDSOdd4 (k : Nat) (B : Nat → Nat) : Prop where
  b0 : B 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → B w = 0
  moment_r1 : choose (2 * k + 1) k + B (k + 1) = choose (2 * k + 1) k * 4
  moment_r2 : choose (2 * k + 1) (k - 1) + B (k + 1) * k + B (k + 2) =
              choose (2 * k + 1) (k - 1) * 16

public theorem additive_mds_odd_ge9_impossible {k : Nat} {B : Nat → Nat}
    (hk : k ≥ 4) (hs : AdditiveMDSOdd4 k B) : False := by
  have hcho_pos : choose (2 * k + 1) (k - 1) > 0 := choose_pos (by omega)
  have hrel : k * choose (2 * k + 1) k = (k + 2) * choose (2 * k + 1) (k - 1) := by
    have h := succ_mul_choose_eq (2 * k + 1) (k - 1) (by omega)
    have he1 : k - 1 + 1 = k := by omega
    have he2 : 2 * k + 1 - (k - 1) = k + 2 := by omega
    rw [he1, he2] at h; exact h
  have hb1 : B (k + 1) = 3 * choose (2 * k + 1) k := by
    have := hs.moment_r1; omega
  have hterm : B (k + 1) * k = 3 * (k + 2) * choose (2 * k + 1) (k - 1) := by
    calc B (k + 1) * k
        = 3 * choose (2 * k + 1) k * k := by rw [hb1]
      _ = 3 * (k * choose (2 * k + 1) k) := by rw [Nat.mul_assoc, Nat.mul_comm (choose (2 * k + 1) k) k]
      _ = 3 * ((k + 2) * choose (2 * k + 1) (k - 1)) := by rw [hrel]
      _ = 3 * (k + 2) * choose (2 * k + 1) (k - 1) := by rw [Nat.mul_assoc]
  have h2 := hs.moment_r2
  rw [hterm] at h2
  have hineq : (3 * (k + 2)) * choose (2 * k + 1) (k - 1) ≤ 15 * choose (2 * k + 1) (k - 1) := by
    omega
  have hcancel : 3 * (k + 2) ≤ 15 := Nat.le_of_mul_le_mul_right hineq hcho_pos
  omega

public theorem additive_mds_n7_impossible {B : Fin 8 → Nat} {A6 : Nat}
    (hb0 : B ⟨0, by decide⟩ = 1)
    (hb1 : B ⟨1, by decide⟩ = 0)
    (hb2 : B ⟨2, by decide⟩ = 0)
    (hb3 : B ⟨3, by decide⟩ = 0)
    (hm3 : choose 7 3 + B ⟨4, by decide⟩ = choose 7 3 * 4)
    (hm2 : choose 7 2 + B ⟨4, by decide⟩ * 3 + B ⟨5, by decide⟩ = choose 7 2 * 16)
    (hm1 : choose 7 1 + B ⟨4, by decide⟩ * 3 + B ⟨5, by decide⟩ * 2 + B ⟨6, by decide⟩ = choose 7 1 * 64)
    (hm0 : 1 + B ⟨4, by decide⟩ + B ⟨5, by decide⟩ + B ⟨6, by decide⟩ + B ⟨7, by decide⟩ = 256)
    (hdual6 : sumFinInt 8 (fun w => (B w : Int) * krawtchouk4 6 w.val 7) = 256 * (A6 : Int)) :
    False := by
  simp only [sumFinInt, Fin.castSucc_mk] at hdual6
  rw [hb0, hb1, hb2, hb3] at hdual6
  simp only [show choose 7 3 = 35 by decide, show choose 7 2 = 21 by decide, show choose 7 1 = 7 by decide,
             show krawtchouk4 6 0 7 = 5103 by decide, show krawtchouk4 6 4 7 = -81 by decide,
             show krawtchouk4 6 5 7 = 39 by decide, show krawtchouk4 6 6 7 = -17 by decide,
             show krawtchouk4 6 7 7 = 7 by decide] at hm3 hm2 hm1 hm0 hdual6
  omega

public theorem no_canonical_graph_ame4_even_d {d : Nat} (hd : d ≥ 2) (heven : 2 ∣ d)
    (Γ : GraphAdj 4) : ¬ IsAMEGraph d Γ := by
  intro hame
  have h2 : IsAMEGraph 2 Γ := radical_divisor_descent Γ hd (by decide) heven hame
  exact no_canonical_graph_ame4_f2 Γ h2

/-! ### Explicit Galois `F_4`-Stabilizer `AME(4, 4)` vs. Cyclic `Z_4` Impossibility -/

public def f4Mul (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, _ | _, 0 => 0
  | 1, x | x, 1 => ⟨x % 4, Nat.mod_lt _ (by decide)⟩
  | 2, 2 => 3
  | 2, 3 | 3, 2 => 1
  | 3, 3 => 2
  | _, _ => 0

public def f4Add (a b : Fin 4) : Fin 4 :=
  ⟨Nat.xor a.val b.val % 4, Nat.mod_lt _ (by decide)⟩

public def f4Trace (a : Fin 4) : Bool := a.val == 2 || a.val == 3

public def f4Symp4 (x z x' z' : Fin 4 → Fin 4) : Bool :=
  let t := fun j : Fin 4 =>
    f4Trace (f4Add (f4Mul (x j) (z' j)) (f4Mul (z j) (x' j)))
  xor (xor (t 0) (t 1)) (xor (t 2) (t 3))

public def f4PauliWeight4 (x z : Fin 4 → Fin 4) : Nat :=
  countFin 4 (fun j => decide (x j ≠ 0 ∨ z j ≠ 0))

public def f4AME4_X (a b : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => f4Add a b
  | ⟨3, _⟩ => f4Add a (f4Mul 2 b)

public def f4AME4_Z (c e : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => f4Add c e
  | ⟨1, _⟩ => f4Add c (f4Mul 2 e)
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => e

public theorem f4_stabilizer_ame4_isotropic :
    ∀ a b c e a' b' c' e' : Fin 4,
      f4Symp4 (f4AME4_X a b) (f4AME4_Z c e) (f4AME4_X a' b') (f4AME4_Z c' e') = false := by
  have hdot : ∀ a b c' e' : Fin 4,
      f4Add (f4Add (f4Mul (f4AME4_X a b 0) (f4AME4_Z c' e' 0))
                   (f4Mul (f4AME4_X a b 1) (f4AME4_Z c' e' 1)))
            (f4Add (f4Mul (f4AME4_X a b 2) (f4AME4_Z c' e' 2))
                   (f4Mul (f4AME4_X a b 3) (f4AME4_Z c' e' 3))) = 0 := by
    decide
  have htr_add : ∀ u v : Fin 4, f4Trace (f4Add u v) = xor (f4Trace u) (f4Trace v) := by decide
  have hmul_comm : ∀ u v : Fin 4, f4Mul u v = f4Mul v u := by decide
  intro a b c e a' b' c' e'
  unfold f4Symp4
  have h1 := hdot a b c' e'
  have h2 := hdot a' b' c e
  have hsum :
      xor (xor (f4Trace (f4Add (f4Mul (f4AME4_X a b 0) (f4AME4_Z c' e' 0))
                               (f4Mul (f4AME4_Z c e 0) (f4AME4_X a' b' 0))))
               (f4Trace (f4Add (f4Mul (f4AME4_X a b 1) (f4AME4_Z c' e' 1))
                               (f4Mul (f4AME4_Z c e 1) (f4AME4_X a' b' 1)))))
          (xor (f4Trace (f4Add (f4Mul (f4AME4_X a b 2) (f4AME4_Z c' e' 2))
                               (f4Mul (f4AME4_Z c e 2) (f4AME4_X a' b' 2))))
               (f4Trace (f4Add (f4Mul (f4AME4_X a b 3) (f4AME4_Z c' e' 3))
                               (f4Mul (f4AME4_Z c e 3) (f4AME4_X a' b' 3))))) =
      xor (f4Trace (f4Add (f4Add (f4Mul (f4AME4_X a b 0) (f4AME4_Z c' e' 0))
                                 (f4Mul (f4AME4_X a b 1) (f4AME4_Z c' e' 1)))
                          (f4Add (f4Mul (f4AME4_X a b 2) (f4AME4_Z c' e' 2))
                                 (f4Mul (f4AME4_X a b 3) (f4AME4_Z c' e' 3)))))
          (f4Trace (f4Add (f4Add (f4Mul (f4AME4_X a' b' 0) (f4AME4_Z c e 0))
                                 (f4Mul (f4AME4_X a' b' 1) (f4AME4_Z c e 1)))
                          (f4Add (f4Mul (f4AME4_X a' b' 2) (f4AME4_Z c e 2))
                                 (f4Mul (f4AME4_X a' b' 3) (f4AME4_Z c e 3))))) := by
    simp only [htr_add, hmul_comm (f4AME4_Z c e _)]
    cases f4Trace (f4Mul (f4AME4_X a b 0) (f4AME4_Z c' e' 0)) <;>
    cases f4Trace (f4Mul (f4AME4_X a b 1) (f4AME4_Z c' e' 1)) <;>
    cases f4Trace (f4Mul (f4AME4_X a b 2) (f4AME4_Z c' e' 2)) <;>
    cases f4Trace (f4Mul (f4AME4_X a b 3) (f4AME4_Z c' e' 3)) <;>
    cases f4Trace (f4Mul (f4AME4_X a' b' 0) (f4AME4_Z c e 0)) <;>
    cases f4Trace (f4Mul (f4AME4_X a' b' 1) (f4AME4_Z c e 1)) <;>
    cases f4Trace (f4Mul (f4AME4_X a' b' 2) (f4AME4_Z c e 2)) <;>
    cases f4Trace (f4Mul (f4AME4_X a' b' 3) (f4AME4_Z c e 3)) <;> rfl
  rw [hsum, h1, h2]
  rfl

public theorem f4_stabilizer_ame4_distance3 :
    ∀ a b c e : Fin 4, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0) →
      f4PauliWeight4 (f4AME4_X a b) (f4AME4_Z c e) ≥ 3 := by
  decide

public theorem z4_vs_f4_separation :
    (∀ Γ : GraphAdj 4, ¬ IsAMEGraph 4 Γ) ∧
    (∀ a b c e a' b' c' e' : Fin 4,
      f4Symp4 (f4AME4_X a b) (f4AME4_Z c e) (f4AME4_X a' b') (f4AME4_Z c' e') = false) ∧
    (∀ a b c e : Fin 4, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0) →
      f4PauliWeight4 (f4AME4_X a b) (f4AME4_Z c e) ≥ 3) :=
  ⟨fun Γ => no_canonical_graph_ame4_even_d (by decide) ⟨2, rfl⟩ Γ,
   f4_stabilizer_ame4_isotropic,
   f4_stabilizer_ame4_distance3⟩

end QPRigidity.AMEGraph
