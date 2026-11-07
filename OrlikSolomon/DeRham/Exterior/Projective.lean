/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of projective modules

Exterior powers preserve a split retraction onto a projective module. A projective module is a
retract of a free module, whose exterior powers are free even when its basis is infinite, so every
exterior power is projective as well. No finite generation or nontriviality is required.

## Main results

* `OrlikSolomon.DeRham.projective_exteriorPower`: every exterior power of a projective module is
  projective. This is the algebraic ingredient of blueprint `lem:dr-projective`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Every exterior power of a projective module is projective. A free module splitting the
original module induces a splitting on exterior powers, and the exterior powers of the free
module are free. The basis may be infinite and the coefficient ring may be zero.

Blueprint: the algebraic step of `lem:dr-projective`. -/
instance projective_exteriorPower [Module.Projective A M] (n : ℕ) :
    Module.Projective A (⋀[A]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A M)
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination A id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

end OrlikSolomon.DeRham
