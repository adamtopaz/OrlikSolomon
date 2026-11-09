/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: a predicate returning Prop remains data and must be scanned.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- A predicate alias whose body must be audited as data. -/
def leak {k : Type} [Field k] (H : AffineSubspace k k) : Prop :=
  OrlikSolomon.IsHyperplane H
