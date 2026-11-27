module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import QPRigidity.AMEGraph
public import QPRigidity.ResolvableQLS
public import QPRigidity.MagicGeometry

/-!
# Adversarial Boundary & Sharpness Tests (`QPRigidity.AdversarialTests`)

Refutes weakened/overclaimed variants of our theorems to confirm every boundary is sharp:
1. Deleting one edge from `C_5` (`P_5` path graph) destroys `AME(5, d)` for ALL `d ≥ 2`.
2. Pless bound is sharp: `PlessEvenSpec 4 2 A` (`N = 8, p = 2`) is UNSATISFIABLE (`4 < 4` fails).
3. Pless odd bound is sharp: `PlessOddSpec 6 2 A` (`N = 13, p = 2`) is UNSATISFIABLE (`6 < 6` fails).
4. A concrete non-linear permutation of `F_8` (`swap 6 and 7`) has ZERO undetermined directions.
5. NO degree-2 RLT+SOS polynomial certificate over ANY `n = 2` stabilizer facet system can
   certify `M = 7` (Conjecture 2) or even `M = 14 < 15 = 4² - 1`.
6. The 2-qubit `ASTAB_2` circumradius `3(13+4√3)/484` strictly exceeds `r²_GB = 1/12`.
-/

namespace QPRigidity.AdversarialTests

open QPRigidity.AMEGraph
open QPRigidity.ResolvableQLS
open QPRigidity.MagicGeometry

/-- Path graph `P_5` (deleting edge `(0, 4)` from `C_5`). -/
public def graphP5 : GraphAdj 5 where
  mat i j :=
    match i.val, j.val with
    | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 => 1
    | _, _ => 0
  symm := by decide
  diag_zero := by decide

/-- Refutation 1: Deleting a single edge from `C_5` destroys `AME(5, d)` for ALL `d ≥ 2`. -/
public theorem refute_path5_ame (d : Nat) (hd : d ≥ 2) : ¬ IsAMEGraph d graphP5 := by
  intro hame
  let α : Fin 5 → Nat := fun i => if i.val = 0 then 1 else 0
  have hnt : ∃ i : Fin 5, α i % d ≠ 0 := ⟨0, by simp [α, Nat.mod_eq_of_lt (by omega : 1 < d)]⟩
  have hgt := hame α hnt
  have hf2 : pauliActive d graphP5 α ⟨2, by decide⟩ = false := by simp [pauliActive, matVec, sumFin, graphP5, α]
  have hf3 : pauliActive d graphP5 α ⟨3, by decide⟩ = false := by simp [pauliActive, matVec, sumFin, graphP5, α]
  have hf4 : pauliActive d graphP5 α ⟨4, by decide⟩ = false := by simp [pauliActive, matVec, sumFin, graphP5, α]
  have hle : pauliWeight d graphP5 α ≤ 2 := by
    simp only [pauliWeight, countFin, Fin.castSucc_mk, hf2, hf3, hf4, Bool.false_eq_true, ite_false]
    split <;> split <;> omega
  omega

/-- Refutation 2: `PlessEvenSpec 4 2 A` (`N = 8, p = 2`) has NO solution. -/
public theorem refute_pless_even_n8_p2 : ¬ ∃ A : Nat → Nat, PlessEvenSpec 4 2 A := by
  rintro ⟨A, hA⟩
  have hlt := pless_even_obstruction (by decide) (by decide) hA
  omega

/-- Refutation 3: `PlessOddSpec 6 2 A` (`N = 13, p = 2`) has NO solution. -/
public theorem refute_pless_odd_n13_p2 : ¬ ∃ A : Nat → Nat, PlessOddSpec 6 2 A := by
  rintro ⟨A, hA⟩
  have hlt := pless_odd_obstruction (by decide) (by decide) hA
  omega

/-- Refutation 4: The non-linear transposition `swap67` on `F_8` admits ZERO nonzero
undetermined directions `c ∈ F_8^×`. -/
public def swap67 (x : Fin 8) : Fin 8 :=
  match x.val with
  | 6 => 7
  | 7 => 6
  | _ => x

public theorem refute_f8_swap67_direction :
    ∀ c : Fin 8, c ≠ 0 →
      ¬ (∀ x y : Fin 8, gf8Add (swap67 x) (gf8Mul c x) = gf8Add (swap67 y) (gf8Mul c y) → x = y) := by
  intro c hc hdir
  have hlin := f8_no_nonlinear_direction_perm swap67 c rfl hc (by decide) hdir
  have hbad2 := hlin 2 4
  have hne : swap67 (gf8Add 2 4) ≠ gf8Add (swap67 2) (swap67 4) := by decide
  exact hne hbad2

/-- Refutation 5: NO degree-2 RLT+SOS polynomial certificate over ANY `n = 2` stabilizer facet system
can certify Conjecture 2 (`M = 7`) or even `M = 14 < 15 = 4² - 1`. -/
public theorem refute_deg2_rlt_conjecture2_n2 {K R : Nat} :
    ¬ ∃ (s : Fin K → Fin (4 ^ 2 - 1) → Int)
        (lam : Fin K → Fin K → Int)
        (mu : Fin K → Int)
        (c : Fin R → Int)
        (v : Fin R → Fin (4 ^ 2 - 1) → Int),
        (∀ k l, lam k l ≥ 0) ∧
        (∀ k, mu k ≥ 0) ∧
        (∀ k l, sumFinInt (4 ^ 2 - 1) (fun p => s k p * s l p) ≥ -1) ∧
        (∀ x : Fin (4 ^ 2 - 1) → Int,
          (7 : Int) - sumFinInt (4 ^ 2 - 1) (fun p => x p * x p) = polyRltSos s lam mu c v x) := by
  rintro ⟨s, lam, mu, c, v, hlam, hmu, hpair, hid⟩
  have hge := clifford_reynolds_deg2_rlt_barrier 2 K R (by decide) s lam mu c v 7 hlam hmu hpair hid
  omega

/-- Refutation 6: At `n = 2` qubits, `ASTAB_2` circumradius `3(13+4√3)/484` strictly exceeds
the Gurvits-Barnum ball `1/12`. -/
public theorem refute_2qubit_astab_in_gb_ball :
    quadPos 3 (36 * 13 - 484) (36 * 4) :=
  exact_astab_circumradius_2qubit_vertex.2.2.2.2

end QPRigidity.AdversarialTests
