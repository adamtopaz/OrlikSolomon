/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: a public declaration exposes a library predicate in its type.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

/-- A function whose argument type exposes the library predicate. -/
def leak {k : Type} [Field k] (H : AffineSubspace k k)
    (_h : OrlikSolomon.IsHyperplane H) : Nat := 0
