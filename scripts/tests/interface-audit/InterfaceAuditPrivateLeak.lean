/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: unreferenced private data must still be checked.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

private def orphanedLeak {k : Type} [Field k] (f : k →ᵃ[k] k) : AffineSubspace k k :=
  OrlikSolomon.zeroLocus f
