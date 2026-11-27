module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import Challenge
public import Solution

/-!
# Palomar Comparator Solution (`PalomarSolution.lean`)

Zero-`sorry` implementation discharging all 14 Palomar Comparator targets across
all 6 independent Lean 4.35.0 kernels (`lake comparator --config comparator.json --paranoid`).
-/

namespace QPRigidity.Palomar

open Challenge

public theorem prove_t1a : T1aStmt := Solution.prove_t1a
public theorem prove_t1b : T1bStmt := Solution.prove_t1b
public theorem prove_t1c : T1cStmt := Solution.prove_t1c
public theorem prove_t1d : T1dStmt := Solution.prove_t1d
public theorem prove_t1e : T1eStmt := Solution.prove_t1e
public theorem prove_t2a : T2aStmt := Solution.prove_t2a
public theorem prove_t2b : T2bStmt := Solution.prove_t2b
public theorem prove_t2c : T2cStmt := Solution.prove_t2c
public theorem prove_t2d : T2dStmt := Solution.prove_t2d
public theorem prove_t3a : T3aStmt := Solution.prove_t3a
public theorem prove_t3b : T3bStmt := Solution.prove_t3b
public theorem prove_t3c : T3cStmt := Solution.prove_t3c
public theorem prove_t3d : T3dStmt := Solution.prove_t3d
public theorem prove_all_rigidity_theorems : AllRigidityTheoremsStmt := Solution.prove_all_rigidity_theorems

end QPRigidity.Palomar
