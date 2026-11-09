/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: a Mathlib-typed definition uses library data in its value.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- A Mathlib-valued function implemented with library data. -/
def leak {k : Type} [Field k] (f : k →ᵃ[k] k) : AffineSubspace k k :=
  OrlikSolomon.zeroLocus f
