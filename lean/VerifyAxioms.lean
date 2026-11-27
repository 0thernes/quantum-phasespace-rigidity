module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

import PalomarSolution
import QPRigidity.NonVacuity
import QPRigidity.AdversarialTests

/-!
# Strict Kernel Axiom Audit (`VerifyAxioms.lean`)

Audits exact transitive axiom footprints for all 14 Palomar headline targets
(`T1a`–`T3d` + `ALL`), 3 pillar non-vacuity witnesses, and 6 adversarial boundary
refutations (23 declarations total). Every declaration MUST stay strictly inside
`{propext, Classical.choice, Quot.sound}` (zero `sorryAx`, zero `Lean.ofReduceBool`,
zero custom axioms).
-/

#print axioms QPRigidity.Palomar.prove_t1a
#print axioms QPRigidity.Palomar.prove_t1b
#print axioms QPRigidity.Palomar.prove_t1c
#print axioms QPRigidity.Palomar.prove_t1d
#print axioms QPRigidity.Palomar.prove_t1e
#print axioms QPRigidity.Palomar.prove_t2a
#print axioms QPRigidity.Palomar.prove_t2b
#print axioms QPRigidity.Palomar.prove_t2c
#print axioms QPRigidity.Palomar.prove_t2d
#print axioms QPRigidity.Palomar.prove_t3a
#print axioms QPRigidity.Palomar.prove_t3b
#print axioms QPRigidity.Palomar.prove_t3c
#print axioms QPRigidity.Palomar.prove_t3d
#print axioms QPRigidity.Palomar.prove_all_rigidity_theorems

#print axioms QPRigidity.NonVacuity.nonvacuity_pillar1_ame
#print axioms QPRigidity.NonVacuity.nonvacuity_pillar2_rqls55
#print axioms QPRigidity.NonVacuity.nonvacuity_pillar3_magic

#print axioms QPRigidity.AdversarialTests.refute_path5_ame
#print axioms QPRigidity.AdversarialTests.refute_pless_even_n8_p2
#print axioms QPRigidity.AdversarialTests.refute_pless_odd_n13_p2
#print axioms QPRigidity.AdversarialTests.refute_f8_swap67_direction
#print axioms QPRigidity.AdversarialTests.refute_deg2_rlt_conjecture2_n2
#print axioms QPRigidity.AdversarialTests.refute_2qubit_astab_in_gb_ball
