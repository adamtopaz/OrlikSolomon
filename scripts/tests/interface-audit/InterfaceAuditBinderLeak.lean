/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: a predicate under dependent binders contains library data.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- A predicate containing a library constant beneath nested binders. -/
def leak {k : Type} [Field k] : (k →ᵃ[k] k) → Prop := fun f =>
  ∀ x : k, x ∈ OrlikSolomon.zeroLocus f
