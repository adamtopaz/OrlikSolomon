/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Positive fixture: library lemmas and proof-namespace theorems occur only as proofs.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- Proof-only library use inside a subtype witness. -/
def proofOnly : {x : Nat // x = 0} := ⟨0, by
  have _h := @OrlikSolomon.zeroLocus_comp.{0}
  rfl⟩

/-- A local proof and its inferred annotation carry no data. -/
def proofLet : Nat :=
  let _h := @OrlikSolomon.zeroLocus_comp.{0}
  0

namespace OrlikSolomon.MainTheorem.Proof
/-- A proof helper in the exempt implementation namespace. -/
theorem allowedProof : True := by
  have _h := @OrlikSolomon.zeroLocus_comp.{0}
  trivial

end OrlikSolomon.MainTheorem.Proof

/-- A proof helper may be used as a proof argument outside its namespace. -/
def proofRegionOnly : {_x : Nat // True} :=
  ⟨0, OrlikSolomon.MainTheorem.Proof.allowedProof⟩
