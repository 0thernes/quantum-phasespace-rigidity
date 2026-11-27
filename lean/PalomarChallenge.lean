module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import Challenge

/-!
# Palomar Comparator Challenge Contract (`PalomarChallenge.lean`)

Statement-only contract for `lake comparator --config comparator.json --paranoid`.
Excluded from `defaultTargets` so `lake build` and `lake check --paranoid` never ingest a `sorry`.
-/

namespace QPRigidity.Palomar

open Challenge

public theorem prove_t1a : T1aStmt := by sorry
public theorem prove_t1b : T1bStmt := by sorry
public theorem prove_t1c : T1cStmt := by sorry
public theorem prove_t1d : T1dStmt := by sorry
public theorem prove_t1e : T1eStmt := by sorry
public theorem prove_t2a : T2aStmt := by sorry
public theorem prove_t2b : T2bStmt := by sorry
public theorem prove_t2c : T2cStmt := by sorry
public theorem prove_t2d : T2dStmt := by sorry
public theorem prove_t3a : T3aStmt := by sorry
public theorem prove_t3b : T3bStmt := by sorry
public theorem prove_t3c : T3cStmt := by sorry
public theorem prove_t3d : T3dStmt := by sorry
public theorem prove_all_rigidity_theorems : AllRigidityTheoremsStmt := by sorry

end QPRigidity.Palomar
