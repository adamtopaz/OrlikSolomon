/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: Lean generates an auxiliary theorem whose type contains library data.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- A constant with a nested proof that Lean abstracts into an auxiliary theorem. -/
def generatedAux {k : Type} [Field k] (f : k →ᵃ[k] k) : Nat :=
  let _h : OrlikSolomon.zeroLocus f = OrlikSolomon.zeroLocus f := by
    exact Eq.trans rfl rfl
  0
