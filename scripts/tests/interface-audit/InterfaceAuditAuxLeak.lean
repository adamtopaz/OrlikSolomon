/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: an auxiliary-looking theorem has a library-bearing statement.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

-- The internal-looking name is deliberate: such names must not exempt a statement.
set_option linter.auxLemma false in
/-- An auxiliary-looking theorem whose statement must still be audited. -/
theorem untouched._proof_1 {k : Type} [Field k] (f : k →ᵃ[k] k) :
    OrlikSolomon.zeroLocus f = OrlikSolomon.zeroLocus f := rfl
