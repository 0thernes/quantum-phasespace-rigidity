module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import Challenge

/-!
# Zero-`sorry` Solution Discharging `Challenge.lean` (`Solution.lean`)
-/

namespace Solution

open Challenge
open QPRigidity.AMEGraph
open QPRigidity.ResolvableQLS
open QPRigidity.MagicGeometry

public theorem prove_t1a : T1aStmt :=
  ⟨fun Γ hd hp hdiv hk => radical_divisor_descent Γ hd hp hdiv hk,
   fun Γ hp hk e he => prime_power_kuniform_ascent Γ hp hk e he,
   fun ha hb hgcd h1 h2 => crt_coprime_kuniform_lift ha hb hgcd h1 h2⟩

public theorem prove_t1b : T1bStmt :=
  universal_unimodular_graphs_all_d

public theorem prove_t1c : T1cStmt :=
  ⟨fun hp hk hs => pless_even_obstruction hp hk hs,
   fun hp hk hs => pless_odd_obstruction hp hk hs⟩

public theorem prove_t1d : T1dStmt :=
  ⟨fun u v hc => f2_commuting_weight_additive u v hc,
   fun h => rains_shadow_no_ame4 h,
   fun h => rains_shadow_no_ame7 h,
   fun h => rains_shadow_no_ame9 h,
   fun h => rains_shadow_no_ame11 h,
   no_canonical_graph_ame4_f2⟩

public theorem prove_t1e : T1eStmt :=
  ⟨fun a he hle hsum => torsion_rank_lower_and_free a he hle hsum,
   fun hk hs => additive_mds_odd_ge9_impossible hk hs,
   fun hd heven Γ => no_canonical_graph_ame4_even_d hd heven Γ,
   z4_vs_f4_separation⟩

public theorem prove_t2a : T2aStmt :=
  fun K H hspan u α β hu hαβ f hf0 hfH hfuH a b hab =>
    trace_spanning_coset_nonconstant K H hspan u α β hu hαβ f hf0 hfH hfuH a b hab

public theorem prove_t2b : T2bStmt :=
  ⟨rqls9_t2_maximal_cert, rqls11_t3_maximal_cert, rqls13_t4_maximal_cert, rqls16_t3_maximal_cert⟩

public theorem prove_t2c : T2cStmt :=
  fun hv2 Q1 C2 => ⟨direct_product_rqls_lifting hv2 Q1 C2⟩

public theorem prove_t2d : T2dStmt :=
  f8_no_nonlinear_direction_perm

public theorem prove_t3a : T3aStmt :=
  ⟨gurvits_barnum_cor3_identity,
   ⟨two_qubit_entangled_astab_witness.2.2.1,
    two_qubit_entangled_astab_witness.2.2.2.1,
    two_qubit_entangled_astab_witness.2.2.2.2.1.2⟩,
   ⟨two_qubit_sep_non_astab_witness.2.2.1,
    two_qubit_sep_non_astab_witness.2.2.2⟩⟩

public theorem prove_t3b : T3bStmt :=
  ⟨ordered4_sum_sq_le_endpoints,
   exact_astab_circumradius_2qubit_vertex.2.2.2.2,
   ⟨exact_astab_circumradius_1qutrit_vertex.2.2.2.2.1,
    exact_astab_circumradius_1qutrit_vertex.2.2.2.2.2⟩⟩

public theorem prove_t3c : T3cStmt :=
  ⟨symplectic_marginal_descent_all_n,
   fun n hn => (inball_gain_exact_15_over_7 n hn).2⟩

public theorem prove_t3d : T3dStmt :=
  clifford_reynolds_deg2_rlt_barrier

public theorem prove_all_rigidity_theorems : AllRigidityTheoremsStmt :=
  ⟨prove_t1a, prove_t1b, prove_t1c, prove_t1d, prove_t1e,
   prove_t2a, prove_t2b, prove_t2c, prove_t2d,
   prove_t3a, prove_t3b, prove_t3c, prove_t3d⟩

end Solution
