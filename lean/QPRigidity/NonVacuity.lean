module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import QPRigidity.AMEGraph
public import QPRigidity.ResolvableQLS
public import QPRigidity.MagicGeometry

/-!
# Non-Vacuity Witnesses (`QPRigidity.NonVacuity`)

Certifies that the hypotheses of all three pillars are genuinely inhabited by concrete,
non-trivial mathematical objects (ruling out vacuous truth or degenerate definitions):
1. Pillar I: `graphPrism6` (`AME(6, 12)`), `graphWheel5` (`AME(6, 12)`), `graphC5` (`AME(5, 6)`),
   plus inhabited `PlessEvenSpec 3 2` (`Prism_6` weight enumerator `[1,0,0,0,45,0,18]`)
   and `PlessOddSpec 2 2` (`C_5` weight enumerator `[1,0,0,10,15,6]`).
2. Pillar II:
   - Untwisted quantum-quantum `direct_product_quantum_quantum` instantiated on
     `3-RQLS(11) ⊗ 3-RQLS(13) = 3-RQLS(143)` (`c = 20,449`, zero unitary twist!).
   - Unitary-twisted `direct_product_rqls_lifting` instantiated on
     `3-RQLS(11) ⊗_D MOLS(5) = 3-RQLS(55)` (`c = 3,025`).
3. Pillar III: Inhabited witnesses for `gurvits_barnum_cor3_identity` (`D = 9`, `P = 1/8`),
   `two_qubit_astab_global_circumradius` (`ρ_ent`), `one_qutrit_astab_global_circumradius`,
   `uniform_cover_avg_bound`, `symplectic_marginal_descent_all_n` (`n = 3`), and an exact
   pointwise polynomial witness for `clifford_reynolds_deg2_rlt_barrier` at `n = 1` (`P = 3`,
   attaining `M = 3 = 4¹ - 1` identically across all `x : Fin 3 → Int`!).
-/

namespace QPRigidity.NonVacuity

open QPRigidity.AMEGraph
open QPRigidity.ResolvableQLS
open QPRigidity.MagicGeometry

/-- Non-vacuity witness for Pillar I: concrete `AME(6, 12)` (`Prism_6` and `W_5`),
`AME(5, 6)` (`C_5`), and inhabited `PlessEvenSpec 3 2` / `PlessOddSpec 2 2`. -/
public theorem nonvacuity_pillar1_ame :
    IsAMEGraph 12 graphPrism6 ∧
    IsAMEGraph 12 graphWheel5 ∧
    IsAMEGraph 6 graphC5 ∧
    (∃ A : Nat → Nat, PlessEvenSpec 3 2 A) ∧
    (∃ A : Nat → Nat, PlessOddSpec 2 2 A) := by
  refine ⟨graphPrism6_ame_all_d 12 (by decide), graphWheel5_ame_all_d 12 (by decide),
          graphC5_ame_all_d 6 (by decide), ?_, ?_⟩
  · refine ⟨fun w => match w with | 0 => 1 | 4 => 45 | 6 => 18 | _ => 0, ?_⟩
    exact {
      a0 := rfl
      zero_below := fun w h1 h2 => by
        match w with | 1 => rfl | 2 => rfl | 3 => rfl | 0 => omega | _ + 4 => omega
      moment_r1 := by decide
      moment_r2 := by decide
    }
  · refine ⟨fun w => match w with | 0 => 1 | 3 => 10 | 4 => 15 | 5 => 6 | _ => 0, ?_⟩
    exact {
      a0 := rfl
      zero_below := fun w h1 h2 => by
        match w with | 1 => rfl | 2 => rfl | 0 => omega | _ + 3 => omega
      moment_r1 := by decide
      moment_r2 := by decide
    }

private theorem mod11_line_pair_unique (r s : Fin 3) (i j i' j' : Fin 11) (hrs : r ≠ s)
    (h1 : (j.val + 11 - ((match r.val with | 0 => 7 | 1 => 8 | _ => 10) * i.val) % 11) % 11 =
          (j'.val + 11 - ((match r.val with | 0 => 7 | 1 => 8 | _ => 10) * i'.val) % 11) % 11)
    (h2 : (j.val + 11 - ((match s.val with | 0 => 7 | 1 => 8 | _ => 10) * i.val) % 11) % 11 =
          (j'.val + 11 - ((match s.val with | 0 => 7 | 1 => 8 | _ => 10) * i'.val) % 11) % 11) :
    i = i' ∧ j = j' := by
  have h11 : ∀ c1 c2 : Nat, (c1 = 7 ∨ c1 = 8 ∨ c1 = 10) → (c2 = 7 ∨ c2 = 8 ∨ c2 = 10) → c1 ≠ c2 →
      ∀ a b a' b' : Nat, a < 11 → b < 11 → a' < 11 → b' < 11 →
        (b + 11 - (c1 * a) % 11) % 11 = (b' + 11 - (c1 * a') % 11) % 11 →
        (b + 11 - (c2 * a) % 11) % 11 = (b' + 11 - (c2 * a') % 11) % 11 →
        a = a' ∧ b = b' := by
    intro c1 c2 hc1 hc2 hne a b a' b' ha hb ha' hb' e1 e2
    rcases hc1 with rfl | rfl | rfl <;> rcases hc2 with rfl | rfl | rfl
    all_goals try (exfalso; exact hne rfl)
    all_goals omega
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  have hs : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by omega
  have hne_val : r.val ≠ s.val := fun h => hrs (Fin.ext h)
  rcases hr with hr | hr | hr <;> rcases hs with hs | hs | hs
  all_goals try (exfalso; omega)
  all_goals
    simp only [hr] at h1; simp only [hs] at h2
    have hpair := h11 _ _ (by omega) (by omega) (by omega) i.val j.val i'.val j'.val i.isLt j.isLt i'.isLt j'.isLt h1 h2
    exact ⟨Fin.ext hpair.1, Fin.ext hpair.2⟩

private theorem mod13_line_pair_unique (r s : Fin 3) (i j i' j' : Fin 13) (hrs : r ≠ s)
    (h1 : (j.val + 13 - ((match r.val with | 0 => 7 | 1 => 9 | _ => 10) * i.val) % 13) % 13 =
          (j'.val + 13 - ((match r.val with | 0 => 7 | 1 => 9 | _ => 10) * i'.val) % 13) % 13)
    (h2 : (j.val + 13 - ((match s.val with | 0 => 7 | 1 => 9 | _ => 10) * i.val) % 13) % 13 =
          (j'.val + 13 - ((match s.val with | 0 => 7 | 1 => 9 | _ => 10) * i'.val) % 13) % 13) :
    i = i' ∧ j = j' := by
  have h13 : ∀ c1 c2 : Nat, (c1 = 7 ∨ c1 = 9 ∨ c1 = 10) → (c2 = 7 ∨ c2 = 9 ∨ c2 = 10) → c1 ≠ c2 →
      ∀ a b a' b' : Nat, a < 13 → b < 13 → a' < 13 → b' < 13 →
        (b + 13 - (c1 * a) % 13) % 13 = (b' + 13 - (c1 * a') % 13) % 13 →
        (b + 13 - (c2 * a) % 13) % 13 = (b' + 13 - (c2 * a') % 13) % 13 →
        a = a' ∧ b = b' := by
    intro c1 c2 hc1 hc2 hne a b a' b' ha hb ha' hb' e1 e2
    rcases hc1 with rfl | rfl | rfl <;> rcases hc2 with rfl | rfl | rfl
    all_goals try (exfalso; exact hne rfl)
    all_goals omega
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  have hs : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by omega
  have hne_val : r.val ≠ s.val := fun h => hrs (Fin.ext h)
  rcases hr with hr | hr | hr <;> rcases hs with hs | hs | hs
  all_goals try (exfalso; omega)
  all_goals
    simp only [hr] at h1; simp only [hs] at h2
    have hpair := h13 _ _ (by omega) (by omega) (by omega) i.val j.val i'.val j'.val i.isLt j.isLt i'.isLt j'.isLt h1 h2
    exact ⟨Fin.ext hpair.1, Fin.ext hpair.2⟩

private def rqls11Spec : ResolvableQLSSpec 11 3 where
  ortho i j i' j' :=
    (i = i' ∧ j ≠ j') ∨
    (i ≠ i' ∧ j = j') ∨
    ((i ≠ i' ∨ j ≠ j') ∧
      ((j.val + 11 - (7 * i.val) % 11) % 11 = (j'.val + 11 - (7 * i'.val) % 11) % 11 ∨
       (j.val + 11 - (8 * i.val) % 11) % 11 = (j'.val + 11 - (8 * i'.val) % 11) % 11 ∨
       (j.val + 11 - (10 * i.val) % 11) % 11 = (j'.val + 11 - (10 * i'.val) % 11) % 11))
  nonCollinear i j i' j' := i ≠ i' ∨ j ≠ j'
  ortho_imp_nonCollinear := by
    intro i j i' j' h
    rcases h with ⟨_, hj⟩ | ⟨hi, _⟩ | ⟨hne, _⟩
    · exact Or.inr hj
    · exact Or.inl hi
    · exact hne
  row_ortho i j j' h := Or.inl ⟨rfl, h⟩
  col_ortho i i' j h := Or.inr (Or.inl ⟨h, rfl⟩)
  res r i j :=
    let c := match r.val with | 0 => 7 | 1 => 8 | _ => 10
    ⟨(j.val + 11 - (c * i.val) % 11) % 11, Nat.mod_lt _ (by decide)⟩
  res_row_inj := by
    intro r i j j' h
    have hv := congrArg Fin.val h; dsimp only at hv
    have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
    rcases hr with hr | hr | hr <;> (simp only [hr] at hv; exact Fin.ext (by omega))
  res_col_inj := by
    intro r i i' j h
    have hv := congrArg Fin.val h; dsimp only at hv
    have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
    rcases hr with hr | hr | hr <;> (simp only [hr] at hv; exact Fin.ext (by omega))
  res_mols := fun r s i j i' j' hrs hr hs =>
    mod11_line_pair_unique r s i j i' j' hrs (congrArg Fin.val hr) (congrArg Fin.val hs)
  res_ortho r i j i' j' hne hres := by
    right; right; refine ⟨hne, ?_⟩
    have hval := congrArg Fin.val hres
    match r with
    | ⟨0, _⟩ => exact Or.inl hval
    | ⟨1, _⟩ => exact Or.inr (Or.inl hval)
    | ⟨2, _⟩ => exact Or.inr (Or.inr hval)
  maximal_card _ _ _ _ hne := hne

private def rqls13Spec3 : ResolvableQLSSpec 13 3 where
  ortho i j i' j' :=
    (i = i' ∧ j ≠ j') ∨
    (i ≠ i' ∧ j = j') ∨
    ((i ≠ i' ∨ j ≠ j') ∧
      ((j.val + 13 - (7 * i.val) % 13) % 13 = (j'.val + 13 - (7 * i'.val) % 13) % 13 ∨
       (j.val + 13 - (9 * i.val) % 13) % 13 = (j'.val + 13 - (9 * i'.val) % 13) % 13 ∨
       (j.val + 13 - (10 * i.val) % 13) % 13 = (j'.val + 13 - (10 * i'.val) % 13) % 13))
  nonCollinear i j i' j' := i ≠ i' ∨ j ≠ j'
  ortho_imp_nonCollinear := by
    intro i j i' j' h
    rcases h with ⟨_, hj⟩ | ⟨hi, _⟩ | ⟨hne, _⟩
    · exact Or.inr hj
    · exact Or.inl hi
    · exact hne
  row_ortho i j j' h := Or.inl ⟨rfl, h⟩
  col_ortho i i' j h := Or.inr (Or.inl ⟨h, rfl⟩)
  res r i j :=
    let c := match r.val with | 0 => 7 | 1 => 9 | _ => 10
    ⟨(j.val + 13 - (c * i.val) % 13) % 13, Nat.mod_lt _ (by decide)⟩
  res_row_inj := by
    intro r i j j' h
    have hv := congrArg Fin.val h; dsimp only at hv
    have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
    rcases hr with hr | hr | hr <;> (simp only [hr] at hv; exact Fin.ext (by omega))
  res_col_inj := by
    intro r i i' j h
    have hv := congrArg Fin.val h; dsimp only at hv
    have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
    rcases hr with hr | hr | hr <;> (simp only [hr] at hv; exact Fin.ext (by omega))
  res_mols := fun r s i j i' j' hrs hr hs =>
    mod13_line_pair_unique r s i j i' j' hrs (congrArg Fin.val hr) (congrArg Fin.val hs)
  res_ortho r i j i' j' hne hres := by
    right; right; refine ⟨hne, ?_⟩
    have hval := congrArg Fin.val hres
    match r with
    | ⟨0, _⟩ => exact Or.inl hval
    | ⟨1, _⟩ => exact Or.inr (Or.inl hval)
    | ⟨2, _⟩ => exact Or.inr (Or.inr hval)
  maximal_card _ _ _ _ hne := hne

private def classicalMOLS5_t3 : ClassicalMOLSRes 5 3 where
  sym i j := ⟨(i.val + j.val) % 5, Nat.mod_lt _ (by decide)⟩
  sym_row_inj := by decide
  sym_col_inj := by decide
  res r i j :=
    let c := match r.val with | 0 => 2 | 1 => 3 | _ => 4
    ⟨(c * i.val + j.val) % 5, Nat.mod_lt _ (by decide)⟩
  res_row_inj := by decide
  res_col_inj := by decide
  res_mols := by decide
  res_sym_inj := by decide

/-- Non-vacuity witness for Pillar II: BOTH untwisted quantum-quantum `3-RQLS(143)` (`11 × 13`)
AND unitary-twisted `3-RQLS(55)` (`11 × 5`). -/
public theorem nonvacuity_pillar2_rqls_lifts :
    Nonempty (ResolvableQLSSpec (11 * 13) 3) ∧
    Nonempty (ResolvableQLSSpec (11 * 5) 3) :=
  ⟨⟨direct_product_quantum_quantum (by decide) rqls11Spec rqls13Spec3⟩,
   ⟨direct_product_rqls_lifting (by decide) rqls11Spec classicalMOLS5_t3
      (fun i2 j2 i2' j2' => i2 ≠ i2' ∨ j2 ≠ j2') (fun _ _ _ _ hne _ => hne)⟩⟩

/-- Concrete 1-qubit (`n = 1, P = 3`) stabilizer facets `±e_1, ±e_2, ±e_3` (`K = 6`)
attaining the exact polynomial degree-2 RLT barrier `M = 3 = 4¹ - 1`:
`3 - (x_0² + x_1² + x_2²) = (1+x_0)(1-x_0) + (1+x_1)(1-x_1) + (1+x_2)(1-x_2)`! -/
private def stab1qFacet (k : Fin 6) (p : Fin 3) : Int :=
  if k.val / 2 = p.val then (if k.val % 2 = 0 then 1 else -1) else 0

private def stab1qLam (k l : Fin 6) : Int :=
  if (k.val = 0 ∧ l.val = 1) ∨ (k.val = 2 ∧ l.val = 3) ∨ (k.val = 4 ∧ l.val = 5) then 1 else 0

/-- Non-vacuity witness for Pillar III: inhabits Gurvits-Barnum Cor 3 (`D = 9`),
both global `ASTAB` circumradius theorems, `uniform_cover_avg_bound`, `symplectic_marginal_descent_all_n`,
and an exact sharp pointwise polynomial identity for `clifford_reynolds_deg2_rlt_barrier` (`n = 1, M = 3`)! -/
public theorem nonvacuity_pillar3_magic :
    ((9 - 1 : Int) * (9 - 1) * 1 - 2 * (9 - 1) * 8 + 9 * 8 ≤ 8) ∧
    quadNonneg 3 (40 * (20 * 20) - 121 * (11 * 11 + 3 * 3 + 3 * 3 + 3 * 3)) (3 * (20 * 20)) ∧
    quadNonneg 5 (3 * (4 * 4) - 2 * (2 * 2 + 1 * 1 + 1 * 1)) (-(4 * 4)) ∧
    (15 * (15 + 7 * 63) ≤ (7 * 4 ^ 3 + 8) * 15) ∧
    ((3 : Int) ≥ ((4 ^ 1 - 1 : Nat) : Int)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gurvits_barnum_cor3_identity 9 1 8 (by decide) (by decide) (by decide)
  · exact two_qubit_astab_global_circumradius 11 3 3 3 20 (by decide) rfl
      (by decide) (by decide) (by decide) (by decide) (by right; left; decide)
  · exact one_qutrit_astab_global_circumradius 2 1 1 4 (by decide) rfl
      (by decide) (by decide) (by decide) (by decide) (by right; right; decide)
  · exact (symplectic_marginal_descent_all_n 3 (7 * 63) 15 (by decide) (by decide) (by decide)).1
  · refine clifford_reynolds_deg2_rlt_barrier 1 6 0 (by decide)
      stab1qFacet stab1qLam (fun _ => 0) (fun r => Fin.elim0 r) (fun r => Fin.elim0 r) 3
      (by intro k l; unfold stab1qLam; split <;> decide)
      (by intro _; decide)
      (by
        intro k l
        have h : ∀ k l : Fin 6, sumFinInt 3 (fun p => stab1qFacet k p * stab1qFacet l p) ≥ -1 := by decide
        exact h k l)
      (by
        intro x
        unfold polyRltSos
        simp [sumFinInt, stab1qFacet, stab1qLam]
        grind)

end QPRigidity.NonVacuity
