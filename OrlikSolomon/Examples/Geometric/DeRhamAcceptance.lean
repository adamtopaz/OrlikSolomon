/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Corollaries

/-!
# Unconditional geometric de Rham acceptance consumers

The two equivalences have open-subscheme targets, with no ordinary theory or Laurent variable
in their statements. The equation and ratio consumers use only the public formula lemmas.

Blueprint: acceptance tests for `cor:geo-dr-arrangements`.
-/

@[expose] public section

noncomputable section

open Module
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [Field k] [CharZero k]
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (𝒜 : Arrangement k V)

/-- The affine corollary needs no cohomology theory from its caller. -/
example : OSAlgebra k 𝒜 ≃ₐ[k] DeRham.Cohomology ((SmoothDomain.aff k).complement 𝒜) :=
  DeRham.affineEquiv 𝒜

/-- Its generator is the logarithmic differential of any equation on the actual complement. -/
example (H : 𝒜) {f : V →ᵃ[k] k} (hf : IsEquation f H) :
    DeRham.affineEquiv 𝒜 (generator k 𝒜 H) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).complement 𝒜).obj)
        (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [DeRham.affineEquiv_generator_of_isEquation H hf]

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

/-- The nonempty projective corollary also needs no supplied ordinary theory. -/
example : projectiveAlgebra k P.cone_isCentral ≃ₐ[k]
    DeRham.Cohomology ((SmoothDomain.aff k).projectiveComplement P) :=
  DeRham.projectiveEquiv P

/-- Its differences are logarithmic differentials of the ratios of any chosen equations. -/
example (H K : P) {ℓ ℓ' : Dual k W}
    (hℓ : LinearMap.ker ℓ = (H : Submodule k W))
    (hℓ' : LinearMap.ker ℓ' = (K : Submodule k W)) :
    DeRham.projectiveEquiv P (projectiveDifference k P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).projectiveComplement P).obj)
        (projectiveRatio (ℓ := ℓ) (ℓ' := ℓ') (by rw [hℓ]; exact H.2)
          (by rw [hℓ']; exact K.2)) := by
  rw [DeRham.projectiveEquiv_difference_of_ker_eq H K hℓ hℓ']

end OrlikSolomon.Geometric.Examples
