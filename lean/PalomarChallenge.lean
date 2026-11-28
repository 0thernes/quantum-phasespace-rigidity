module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

/-!
# Palomar Comparator Challenge Contract (`PalomarChallenge.lean`)

Self-contained zero-import Lean 4.35.0 statement contract for Palomar Registry
(`lake comparator --config comparator.json --paranoid`). All definitions used in the
14 headline theorem types are declared verbatim here with zero candidate-local imports,
strictly satisfying Palomar v1 `challenge-provenance`. All zero-`sorry` proofs live in
`PalomarSolution.lean` and `QPRigidity.*`.
-/

namespace QPRigidity.Palomar
@[expose] public section

/-! ## 1. Common Finite Sums, Counts, and Binomials -/

def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

def sumFinInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFinInt n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

def countFin : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => countFin n (fun i => p i.castSucc) + (if p ⟨n, Nat.lt_succ_self n⟩ then 1 else 0)

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-! ## 2. Pillar I Definitions: Cyclic `Z_d` Graph States, Pless, Rains, and `F_4` -/

structure GraphAdj (N : Nat) where
  mat : Fin N → Fin N → Nat
  symm : ∀ i j, mat i j = mat j i
  diag_zero : ∀ i, mat i i = 0

def matVec {N : Nat} (Γ : GraphAdj N) (α : Fin N → Nat) (j : Fin N) : Nat :=
  sumFin N (fun i => Γ.mat j i * α i)

def pauliActive {N : Nat} (d : Nat) (Γ : GraphAdj N) (α : Fin N → Nat) (j : Fin N) : Bool :=
  decide (α j % d ≠ 0 ∨ matVec Γ α j % d ≠ 0)

def pauliWeight {N : Nat} (d : Nat) (Γ : GraphAdj N) (α : Fin N → Nat) : Nat :=
  countFin N (pauliActive d Γ α)

def IsKUniformGraph {N : Nat} (d : Nat) (Γ : GraphAdj N) (k : Nat) : Prop :=
  ∀ α : Fin N → Nat, (∃ i : Fin N, α i % d ≠ 0) → pauliWeight d Γ α > k

def IsAMEGraph {N : Nat} (d : Nat) (Γ : GraphAdj N) : Prop :=
  IsKUniformGraph d Γ (N / 2)

def graphK2Mat (i j : Fin 2) : Nat := if i = j then 0 else 1
theorem graphK2_symm : ∀ i j : Fin 2, graphK2Mat i j = graphK2Mat j i := by decide
theorem graphK2_diag : ∀ i : Fin 2, graphK2Mat i i = 0 := by decide
def graphK2 : GraphAdj 2 := ⟨graphK2Mat, graphK2_symm, graphK2_diag⟩

def graphK3Mat (i j : Fin 3) : Nat := if i = j then 0 else 1
theorem graphK3_symm : ∀ i j : Fin 3, graphK3Mat i j = graphK3Mat j i := by decide
theorem graphK3_diag : ∀ i : Fin 3, graphK3Mat i i = 0 := by decide
def graphK3 : GraphAdj 3 := ⟨graphK3Mat, graphK3_symm, graphK3_diag⟩

def graphC5Mat (i j : Fin 5) : Nat :=
  match i.val, j.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => 1
  | _, _ => 0
theorem graphC5_symm : ∀ i j : Fin 5, graphC5Mat i j = graphC5Mat j i := by decide
theorem graphC5_diag : ∀ i : Fin 5, graphC5Mat i i = 0 := by decide
def graphC5 : GraphAdj 5 := ⟨graphC5Mat, graphC5_symm, graphC5_diag⟩

def graphPrism6Mat (i j : Fin 6) : Nat :=
  match i.val, j.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 0 | 0, 2 => 1
  | 3, 4 | 4, 3 | 4, 5 | 5, 4 | 5, 3 | 3, 5 => 1
  | 0, 3 | 3, 0 | 1, 4 | 4, 1 | 2, 5 | 5, 2 => 1
  | _, _ => 0
theorem graphPrism6_symm : ∀ i j : Fin 6, graphPrism6Mat i j = graphPrism6Mat j i := by decide
theorem graphPrism6_diag : ∀ i : Fin 6, graphPrism6Mat i i = 0 := by decide
def graphPrism6 : GraphAdj 6 := ⟨graphPrism6Mat, graphPrism6_symm, graphPrism6_diag⟩

def graphWheel5Mat (i j : Fin 6) : Nat :=
  match i.val, j.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 0 | 0, 4 => 1
  | 0, 5 | 5, 0 | 1, 5 | 5, 1 | 2, 5 | 5, 2 | 3, 5 | 5, 3 | 4, 5 | 5, 4 => 1
  | _, _ => 0
theorem graphWheel5_symm : ∀ i j : Fin 6, graphWheel5Mat i j = graphWheel5Mat j i := by decide
theorem graphWheel5_diag : ∀ i : Fin 6, graphWheel5Mat i i = 0 := by decide
def graphWheel5 : GraphAdj 6 := ⟨graphWheel5Mat, graphWheel5_symm, graphWheel5_diag⟩

structure PlessEvenSpec (k p : Nat) (A : Nat → Nat) : Prop where
  a0 : A 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → A w = 0
  moment_r1 : choose (2 * k) (k - 1) + A (k + 1) = choose (2 * k) (k - 1) * p ^ 2
  moment_r2 : choose (2 * k) (k - 2) + A (k + 1) * (k - 1) + A (k + 2) =
              choose (2 * k) (k - 2) * p ^ 4

structure PlessOddSpec (k p : Nat) (A : Nat → Nat) : Prop where
  a0 : A 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → A w = 0
  moment_r1 : choose (2 * k + 1) k + A (k + 1) = choose (2 * k + 1) k * p
  moment_r2 : choose (2 * k + 1) (k - 1) + A (k + 1) * k + A (k + 2) =
              choose (2 * k + 1) (k - 1) * p ^ 3

def wtBit (p : Bool × Bool) : Nat := if p.1 || p.2 then 1 else 0
def sympBit (p q : Bool × Bool) : Bool := xor (p.1 && q.2) (p.2 && q.1)
def xorBit (p q : Bool × Bool) : Bool × Bool := (xor p.1 q.1, xor p.2 q.2)

def pauliWeightF2 {N : Nat} (u : Fin N → Bool × Bool) : Nat :=
  sumFin N (fun i => wtBit (u i))

def sympF2 : {N : Nat} → (Fin N → Bool × Bool) → (Fin N → Bool × Bool) → Bool
  | 0, _, _ => false
  | n + 1, u, v => xor (sympF2 (fun i => u i.castSucc) (fun i => v i.castSucc))
                       (sympBit (u ⟨n, Nat.lt_succ_self n⟩) (v ⟨n, Nat.lt_succ_self n⟩))

def xorF2 {N : Nat} (u v : Fin N → Bool × Bool) : Fin N → Bool × Bool :=
  fun i => xorBit (u i) (v i)

def krawtchouk4 (j w N : Nat) : Int :=
  sumFinInt (j + 1) (fun r =>
    let sign : Int := if r.val % 2 = 0 then 1 else -1
    sign * (3 ^ (j - r.val) : Nat) * (choose w r.val : Int) * (choose (N - w) (j - r.val) : Int))

structure RainsShadowQubitAME (N : Nat) (A : Fin (N + 1) → Nat) (S : Fin (N + 1) → Nat) : Prop where
  a0 : A ⟨0, Nat.zero_lt_succ N⟩ = 1
  zero_below : ∀ w : Fin (N + 1), 1 ≤ w.val → w.val ≤ N / 2 → A w = 0
  macwilliams : ∀ j : Fin (N + 1),
    sumFinInt (N + 1) (fun w => (A w : Int) * krawtchouk4 j.val w.val N) =
    (2 ^ N : Int) * (A j : Int)
  shadow : ∀ j : Fin (N + 1),
    sumFinInt (N + 1) (fun w =>
      (if w.val % 2 = 0 then (1 : Int) else -1) * (A w : Int) * krawtchouk4 j.val w.val N) =
    (2 ^ N : Int) * (S j : Int)

structure AdditiveMDSOdd4 (k : Nat) (B : Nat → Nat) : Prop where
  b0 : B 0 = 1
  zero_below : ∀ w, 1 ≤ w → w ≤ k → B w = 0
  moment_r1 : choose (2 * k + 1) k + B (k + 1) = choose (2 * k + 1) k * 4
  moment_r2 : choose (2 * k + 1) (k - 1) + B (k + 1) * k + B (k + 2) =
              choose (2 * k + 1) (k - 1) * 16

def f4Mul (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, _ | _, 0 => 0
  | 1, x | x, 1 => ⟨x % 4, Nat.mod_lt _ (Nat.zero_lt_succ 3)⟩
  | 2, 2 => 3
  | 2, 3 | 3, 2 => 1
  | 3, 3 => 2
  | _, _ => 0

def f4Add (a b : Fin 4) : Fin 4 :=
  ⟨Nat.xor a.val b.val % 4, Nat.mod_lt _ (Nat.zero_lt_succ 3)⟩

def f4Trace (a : Fin 4) : Bool := a.val == 2 || a.val == 3

def f4Symp4 (x z x' z' : Fin 4 → Fin 4) : Bool :=
  let t := fun j : Fin 4 =>
    f4Trace (f4Add (f4Mul (x j) (z' j)) (f4Mul (z j) (x' j)))
  xor (xor (t 0) (t 1)) (xor (t 2) (t 3))

def f4PauliWeight4 (x z : Fin 4 → Fin 4) : Nat :=
  countFin 4 (fun j => decide (x j ≠ 0 ∨ z j ≠ 0))

def f4AME4_X (a b : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => f4Add a b
  | ⟨3, _⟩ => f4Add a (f4Mul 2 b)

def f4AME4_Z (c e : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => f4Add c e
  | ⟨1, _⟩ => f4Add c (f4Mul 2 e)
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => e

/-! ## 3. Pillar II Definitions: Resolvable Quantum Latin Squares & Finite Fields -/

structure TraceFieldSpec (F B : Type) where
  zero : F
  add : F → F → F
  neg : F → F
  mul : F → F → F
  tr : F → B
  b0 : B
  add_comm : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero : ∀ x, add x zero = x
  add_neg : ∀ x, add x (neg x) = zero
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_comm : ∀ x y, mul x y = mul y x
  mul_zero : ∀ x, mul x zero = zero
  left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  no_zero_div : ∀ x y, mul x y = zero → x = zero ∨ y = zero
  tr_zero : tr zero = b0

def IsTraceSpanning {F B : Type} (K : TraceFieldSpec F B) (S : F → Prop) : Prop :=
  ∀ c : F, (∀ x : F, S x → K.tr (K.mul c x) = K.b0) → c = K.zero

def isBijectiveFin {q : Nat} (f : Fin q → Fin q) : Bool :=
  (List.finRange q).all fun x => (List.finRange q).all fun y => (f x == f y) == (x == y)

def isQR11 (x : Fin 11) : Bool :=
  x.val == 1 || x.val == 3 || x.val == 4 || x.val == 5 || x.val == 9

def mu11 (x : Fin 11) : Fin 11 :=
  if x.val == 0 then 0
  else if isQR11 x then ⟨(7 * x.val) % 11, Nat.mod_lt _ (Nat.zero_lt_succ 10)⟩
  else ⟨(8 * x.val) % 11, Nat.mod_lt _ (Nat.zero_lt_succ 10)⟩

def isQR13 (x : Fin 13) : Bool :=
  x.val == 1 || x.val == 3 || x.val == 4 || x.val == 9 || x.val == 10 || x.val == 12

def mu13 (x : Fin 13) : Fin 13 :=
  if x.val == 0 then 0
  else if isQR13 x then ⟨(9 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩
  else ⟨(10 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩

def gf9Add (x y : Fin 9) : Fin 9 :=
  let a1 := x.val / 3; let b1 := x.val % 3
  let a2 := y.val / 3; let b2 := y.val % 3
  ⟨(3 * ((a1 + a2) % 3) + ((b1 + b2) % 3)) % 9, Nat.mod_lt _ (Nat.zero_lt_succ 8)⟩

def gf9Mul (x y : Fin 9) : Fin 9 :=
  let a1 := x.val / 3; let b1 := x.val % 3
  let a2 := y.val / 3; let b2 := y.val % 3
  let re := (a1 * a2 + 2 * (b1 * b2)) % 3
  let im := (a1 * b2 + b1 * a2) % 3
  ⟨(3 * re + im) % 9, Nat.mod_lt _ (Nat.zero_lt_succ 8)⟩

def gf9Trace (x : Fin 9) : Nat := (2 * (x.val / 3)) % 3

def isSq9 (x : Fin 9) : Bool :=
  x.val == 3 || x.val == 6 || x.val == 1 || x.val == 2

def mu9 (x : Fin 9) : Fin 9 :=
  if x.val == 0 then 0
  else if isSq9 x then x
  else gf9Mul 6 x

def gf16Add (x y : Fin 16) : Fin 16 :=
  ⟨Nat.xor x.val y.val % 16, Nat.mod_lt _ (Nat.zero_lt_succ 15)⟩

def gf16Mul (x y : Fin 16) : Fin 16 :=
  let step := fun (acc a b : Nat) =>
    let acc' := if b % 2 = 1 then Nat.xor acc a else acc
    let a' := (a * 2) % 16
    let a'' := if a ≥ 8 then Nat.xor a' 3 else a'
    (acc', a'', b / 2)
  let s0 := step 0 x.val y.val
  let s1 := step s0.1 s0.2.1 s0.2.2
  let s2 := step s1.1 s1.2.1 s1.2.2
  let s3 := step s2.1 s2.2.1 s2.2.2
  ⟨s3.1 % 16, Nat.mod_lt _ (Nat.zero_lt_succ 15)⟩

def gf16Trace (x : Fin 16) : Bool :=
  let x2 := gf16Mul x x
  let x4 := gf16Mul x2 x2
  let x8 := gf16Mul x4 x4
  (gf16Add (gf16Add x x2) (gf16Add x4 x8)).val != 0

def inCoset2_16 (x : Fin 16) : Bool :=
  x.val == 4 || x.val == 5 || x.val == 6 || x.val == 9 || x.val == 14

def mu16 (x : Fin 16) : Fin 16 :=
  if inCoset2_16 x then gf16Mul 8 x else x

structure ResolvableQLSSpec (v t : Nat) where
  ortho : Fin v → Fin v → Fin v → Fin v → Prop
  nonCollinear : Fin v → Fin v → Fin v → Fin v → Prop
  ortho_imp_nonCollinear : ∀ i j i' j', ortho i j i' j' → nonCollinear i j i' j'
  row_ortho : ∀ i j j', j ≠ j' → ortho i j i j'
  col_ortho : ∀ i i' j, i ≠ i' → ortho i j i' j
  res : Fin t → Fin v → Fin v → Fin v
  res_row_inj : ∀ r i j j', res r i j = res r i j' → j = j'
  res_col_inj : ∀ r i i' j, res r i j = res r i' j → i = i'
  res_mols : ∀ r s i j i' j', r ≠ s → res r i j = res r i' j' → res s i j = res s i' j' → i = i' ∧ j = j'
  res_ortho : ∀ r i j i' j', (i ≠ i' ∨ j ≠ j') → res r i j = res r i' j' → ortho i j i' j'
  maximal_card : ∀ i j i' j', (i ≠ i' ∨ j ≠ j') → nonCollinear i j i' j'

structure ClassicalMOLSRes (v t : Nat) where
  sym : Fin v → Fin v → Fin v
  sym_row_inj : ∀ i j j', sym i j = sym i j' → j = j'
  sym_col_inj : ∀ i i' j, sym i j = sym i' j → i = i'
  res : Fin t → Fin v → Fin v → Fin v
  res_row_inj : ∀ r i j j', res r i j = res r i j' → j = j'
  res_col_inj : ∀ r i i' j, res r i j = res r i' j → i = i'
  res_mols : ∀ r s i j i' j', r ≠ s → res r i j = res r i' j' → res s i j = res s i' j' → i = i' ∧ j = j'
  res_sym_inj : ∀ r i j i' j', res r i j = res r i' j' → sym i j = sym i' j' → i = i' ∧ j = j'

def gf8Add (x y : Fin 8) : Fin 8 :=
  ⟨Nat.xor x.val y.val % 8, Nat.mod_lt _ (Nat.zero_lt_succ 7)⟩

def gf8Mul (x y : Fin 8) : Fin 8 :=
  let step := fun (acc a b : Nat) =>
    let acc' := if b % 2 = 1 then Nat.xor acc a else acc
    let a' := (a * 2) % 8
    let a'' := if a ≥ 4 then Nat.xor a' 3 else a'
    (acc', a'', b / 2)
  let s0 := step 0 x.val y.val
  let s1 := step s0.1 s0.2.1 s0.2.2
  let s2 := step s1.1 s1.2.1 s1.2.2
  ⟨s2.1 % 8, Nat.mod_lt _ (Nat.zero_lt_succ 7)⟩

/-! ## 4. Pillar III Definitions: Ordered Quadratic Rings `Z[√d]` & Degree-2 RLT+SOS -/

def quadNonneg (d : Nat) (a b : Int) : Prop :=
  (a ≥ 0 ∧ b ≥ 0) ∨
  (a ≥ 0 ∧ b < 0 ∧ a * a ≥ (d : Int) * (b * b)) ∨
  (a < 0 ∧ b ≥ 0 ∧ (d : Int) * (b * b) ≥ a * a)

def quadPos (d : Nat) (a b : Int) : Prop :=
  (a > 0 ∧ b ≥ 0) ∨
  (a ≥ 0 ∧ b > 0) ∨
  (a > 0 ∧ b < 0 ∧ a * a > (d : Int) * (b * b)) ∨
  (a ≤ 0 ∧ b > 0 ∧ (d : Int) * (b * b) > a * a)

def polyRltSos {P K R : Nat}
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

/-! ## 5. The 14 Palomar Comparator Challenge Theorems (`T1a`–`T3d` + Master Conjunction) -/

abbrev T1aStmt : Prop :=
  (∀ {N k d p : Nat} (Γ : GraphAdj N), d ≥ 2 → p ≥ 2 → p ∣ d → IsKUniformGraph d Γ k → IsKUniformGraph p Γ k) ∧
  (∀ {N k p : Nat} (Γ : GraphAdj N), p ≥ 2 → IsKUniformGraph p Γ k → ∀ e, e ≥ 1 → IsKUniformGraph (p ^ e) Γ k) ∧
  (∀ {N k a b : Nat}, a ≥ 2 → b ≥ 2 → Nat.gcd a b = 1 →
    (∃ Γ₁ : GraphAdj N, IsKUniformGraph a Γ₁ k) →
    (∃ Γ₂ : GraphAdj N, IsKUniformGraph b Γ₂ k) →
    ∃ Γ : GraphAdj N, IsKUniformGraph (a * b) Γ k)

abbrev T1bStmt : Prop :=
  ∀ d : Nat, d ≥ 2 →
    IsAMEGraph d graphK2 ∧ IsAMEGraph d graphK3 ∧ IsAMEGraph d graphC5 ∧
    IsAMEGraph d graphPrism6 ∧ IsAMEGraph d graphWheel5

abbrev T1cStmt : Prop :=
  (∀ {k p : Nat} {A : Nat → Nat}, p ≥ 2 → k ≥ 2 → PlessEvenSpec k p A → k < p ^ 2) ∧
  (∀ {k p : Nat} {A : Nat → Nat}, p ≥ 2 → k ≥ 2 → PlessOddSpec k p A → k < p ^ 2 + p)

abbrev T1dStmt : Prop :=
  (∀ {N : Nat} (u v : Fin N → Bool × Bool),
    sympF2 u v = false → pauliWeightF2 (xorF2 u v) % 2 = (pauliWeightF2 u + pauliWeightF2 v) % 2) ∧
  (∀ {A S : Fin 5 → Nat}, RainsShadowQubitAME 4 A S → False) ∧
  (∀ {A S : Fin 8 → Nat}, RainsShadowQubitAME 7 A S → False) ∧
  (∀ {A S : Fin 10 → Nat}, RainsShadowQubitAME 9 A S → False) ∧
  (∀ {A S : Fin 12 → Nat}, RainsShadowQubitAME 11 A S → False) ∧
  (∀ Γ : GraphAdj 4, ¬ IsAMEGraph 2 Γ)

abbrev T1eStmt : Prop :=
  (∀ {m e N : Nat} (a : Fin m → Nat), e ≥ 1 → (∀ i, a i ≤ e) → sumFin m a = e * N →
    m ≥ N ∧ (m = N → ∀ i, a i = e)) ∧
  (∀ {k : Nat} {B : Nat → Nat}, k ≥ 4 → AdditiveMDSOdd4 k B → False) ∧
  (∀ {B : Fin 8 → Nat} {A6 : Nat},
    B 0 = 1 → B 1 = 0 → B 2 = 0 → B 3 = 0 →
    choose 7 3 + B 4 = choose 7 3 * 4 →
    choose 7 2 + B 4 * 3 + B 5 = choose 7 2 * 16 →
    choose 7 1 + B 4 * 3 + B 5 * 2 + B 6 = choose 7 1 * 64 →
    1 + B 4 + B 5 + B 6 + B 7 = 256 →
    sumFinInt 8 (fun w => (B w : Int) * krawtchouk4 6 w.val 7) = 256 * (A6 : Int) → False) ∧
  (∀ {d : Nat}, d ≥ 2 → 2 ∣ d → ∀ Γ : GraphAdj 4, ¬ IsAMEGraph d Γ) ∧
  ((∀ Γ : GraphAdj 4, ¬ IsAMEGraph 4 Γ) ∧
   (∀ a b c e a' b' c' e' : Fin 4,
     f4Symp4 (f4AME4_X a b) (f4AME4_Z c e) (f4AME4_X a' b') (f4AME4_Z c' e') = false) ∧
   (∀ a b c e : Fin 4, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0) →
     f4PauliWeight4 (f4AME4_X a b) (f4AME4_Z c e) ≥ 3))

abbrev T2aStmt : Prop :=
  ∀ {F B : Type} (K : TraceFieldSpec F B) (H : F → Prop),
    IsTraceSpanning K H →
    ∀ (u α β : F), u ≠ K.zero → α ≠ β →
    ∀ (f : F → F), f K.zero = K.zero →
    (∀ x, H x → f x = K.mul α x) →
    (∀ x, H x → f (K.mul u x) = K.mul β (K.mul u x)) →
    ∀ a b : F, (a ≠ K.zero ∨ b ≠ K.zero) →
      ∃ z : F, K.tr (K.add (K.mul a (f z)) (K.mul b z)) ≠ K.b0

abbrev T2bStmt : Prop :=
  (isBijectiveFin mu9 = true ∧
   isBijectiveFin (fun x : Fin 9 => gf9Add (mu9 x) (gf9Mul 1 x)) = true ∧
   isBijectiveFin (fun x : Fin 9 => gf9Add (mu9 x) (gf9Mul 2 x)) = true ∧
   (∀ a b : Fin 9, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 9, gf9Trace (gf9Add (gf9Mul a (mu9 z)) (gf9Mul b z)) ≠ 0)) ∧
  (isBijectiveFin mu11 = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨((mu11 x).val + 7 * x.val) % 11, Nat.mod_lt _ (Nat.zero_lt_succ 10)⟩) = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨((mu11 x).val + 8 * x.val) % 11, Nat.mod_lt _ (Nat.zero_lt_succ 10)⟩) = true ∧
   isBijectiveFin (fun x : Fin 11 => ⟨((mu11 x).val + 10 * x.val) % 11, Nat.mod_lt _ (Nat.zero_lt_succ 10)⟩) = true ∧
   (∀ a b : Fin 11, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 11, (a.val * (mu11 z).val + b.val * z.val) % 11 ≠ 0)) ∧
  (isBijectiveFin mu13 = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨((mu13 x).val + 7 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨((mu13 x).val + 9 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨((mu13 x).val + 10 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩) = true ∧
   isBijectiveFin (fun x : Fin 13 => ⟨((mu13 x).val + 11 * x.val) % 13, Nat.mod_lt _ (Nat.zero_lt_succ 12)⟩) = true ∧
   (∀ a b : Fin 13, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 13, (a.val * (mu13 z).val + b.val * z.val) % 13 ≠ 0)) ∧
  (isBijectiveFin mu16 = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul 3 x)) = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul 9 x)) = true ∧
   isBijectiveFin (fun x : Fin 16 => gf16Add (mu16 x) (gf16Mul 10 x)) = true ∧
   (∀ a b : Fin 16, (a ≠ 0 ∨ b ≠ 0) → ∃ z : Fin 16, gf16Trace (gf16Add (gf16Mul a (mu16 z)) (gf16Mul b z)) = true))

abbrev T2cStmt : Prop :=
  (∀ {v1 v2 t : Nat}, v2 > 0 → ResolvableQLSSpec v1 t → ResolvableQLSSpec v2 t →
    Nonempty (ResolvableQLSSpec (v1 * v2) t)) ∧
  (∀ {v1 v2 t : Nat}, v2 > 0 → ResolvableQLSSpec v1 t → (C2 : ClassicalMOLSRes v2 t) →
    (twistSep : Fin v2 → Fin v2 → Fin v2 → Fin v2 → Prop) →
    (∀ i2 j2 i2' j2', (i2 ≠ i2' ∨ j2 ≠ j2') → C2.sym i2 j2 = C2.sym i2' j2' → twistSep i2 j2 i2' j2') →
    Nonempty (ResolvableQLSSpec (v1 * v2) t))

abbrev T2dStmt : Prop :=
  ∀ (μ : Fin 8 → Fin 8) (c : Fin 8), μ 0 = 0 → c ≠ 0 →
    (∀ x y : Fin 8, μ x = μ y → x = y) →
    (∀ x y : Fin 8, gf8Add (μ x) (gf8Mul c x) = gf8Add (μ y) (gf8Mul c y) → x = y) →
    ∀ x y : Fin 8, μ (gf8Add x y) = gf8Add (μ x) (μ y)

abbrev T3aStmt : Prop :=
  (∀ D P_num P_den : Int, D ≥ 2 → P_den > 0 → (D - 1) * P_num ≤ P_den →
    (D - 1) * (D - 1) * P_num - 2 * (D - 1) * P_den + D * P_den ≤ P_den) ∧
  (quadPos 3 (11 + 3) (3 - 11) ∧ quadPos 5 20 (6 - 14) ∧ (((11 : Int) - 3) * (11 - 3) > 4 * 3 * 3)) ∧
  ((((8 : Int) - 4) * (8 - 4) < 4 * 7 * 1) ∧ quadPos 3 (-(8 + 1)) (8 - 1))

abbrev T3bStmt : Prop :=
  (∀ l1 l2 l3 l4 M : Int, M > 0 → l1 + l2 + l3 + l4 = M → l1 ≥ l2 → l2 ≥ l3 → l3 ≥ l4 → l4 ≥ 0 →
    quadNonneg 3 (l1 + l4) (l4 - l1) →
    quadNonneg 3 (40 * (M * M) - 121 * (l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4)) (3 * (M * M))) ∧
  (∀ l1 l2 l3 M : Int, M > 0 → l1 + l2 + l3 = M → l1 ≥ l2 → l2 ≥ l3 → l3 ≥ 0 →
    2 * l1 ≤ M → quadNonneg 5 (2 * l3 - 3 * l1) l1 →
    quadNonneg 5 (3 * (M * M) - 2 * (l1 * l1 + l2 * l2 + l3 * l3)) (-(M * M))) ∧
  (quadPos 3 (36 * 13 - 484) (36 * 4)) ∧
  (quadPos 5 27 (-12) ∧ quadPos 5 (-6) 3)

abbrev T3cStmt : Prop :=
  (∀ {P K m r B : Nat} (inSub : Fin K → Fin P → Bool) (f : Fin P → Nat),
    r > 0 →
    (∀ k : Fin K, countFin P (fun p => inSub k p) = m) →
    (∀ p : Fin P, countFin K (fun k => inSub k p) = r) →
    (∀ k : Fin K, sumFin P (fun p => if inSub k p then f p else 0) ≤ B) →
    m * sumFin P f ≤ B * P) ∧
  (∀ n S Q : Nat, n ≥ 2 → Q > 0 → 15 * S ≤ 7 * (4 ^ n - 1) * Q →
    15 * (Q + S) ≤ (7 * 4 ^ n + 8) * Q ∧ (7 * 4 ^ n + 8) * Q < 15 * 4 ^ n * Q) ∧
  (∀ n : Nat, n ≥ 1 → 15 * ((7 * 4 ^ n + 8) - 15) = 7 * (15 * (4 ^ n - 1)))

abbrev T3dStmt : Prop :=
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

abbrev AllRigidityTheoremsStmt : Prop :=
  T1aStmt ∧ T1bStmt ∧ T1cStmt ∧ T1dStmt ∧ T1eStmt ∧
  T2aStmt ∧ T2bStmt ∧ T2cStmt ∧ T2dStmt ∧
  T3aStmt ∧ T3bStmt ∧ T3cStmt ∧ T3dStmt

theorem prove_t1a : T1aStmt := by sorry
theorem prove_t1b : T1bStmt := by sorry
theorem prove_t1c : T1cStmt := by sorry
theorem prove_t1d : T1dStmt := by sorry
theorem prove_t1e : T1eStmt := by sorry
theorem prove_t2a : T2aStmt := by sorry
theorem prove_t2b : T2bStmt := by sorry
theorem prove_t2c : T2cStmt := by sorry
theorem prove_t2d : T2dStmt := by sorry
theorem prove_t3a : T3aStmt := by sorry
theorem prove_t3b : T3bStmt := by sorry
theorem prove_t3c : T3cStmt := by sorry
theorem prove_t3d : T3dStmt := by sorry
theorem prove_all_rigidity_theorems : AllRigidityTheoremsStmt := by sorry

end
end QPRigidity.Palomar
