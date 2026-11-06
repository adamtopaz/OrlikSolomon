/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Ordinary
public import OrlikSolomon.Examples.Polynomials

/-!
# Empty arrangements and zero coefficients

The empty complement has precisely the coefficient algebra in every ambient dimension,
including dimension zero. On the zero theory the same degree-one group of the two-point
complement admits bases with zero and two vectors. Its certified Betti number is nevertheless
two: the count comes from the recursive words and polynomial, not uniqueness of basis cardinality.

Blueprint: items 1 and 9 of "Required mathematical regression examples".
-/

@[expose] public section

noncomputable section

open Module
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement

universe u v w z

namespace OrlikSolomon.DegenerateExamples

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The empty affine arrangement has the coefficient algebra in every dimension. -/
def emptyCohomologyEquiv :
    B ≃ₐ[B] T.C.obj (complement (∅ : Arrangement k V)) :=
  AlgEquiv.ofBijective (Algebra.ofId B _) (T.bijective_algebraMap_complement_empty V)

/-- The empty-complement equivalence is the coefficient structure map. -/
@[simp]
theorem emptyCohomologyEquiv_apply (b : B) :
    emptyCohomologyEquiv T V b = algebraMap B _ b := rfl

/-- Dimension zero is included, without choosing a point of a nonempty complement. -/
example : B ≃ₐ[B] T.C.obj (complement (∅ : Arrangement k PUnit.{u + 1})) :=
  emptyCohomologyEquiv T PUnit

/-- The nonzero localization with no rational points from `Examples/Sanity` has polynomial
`1 + 2 X`. This uses that very arrangement, rather than a separate point-set model. -/
theorem poincarePolynomial_twoPoints :
    Sanity.twoPoints.poincarePolynomial = 1 + 2 * Polynomial.X := by
  classical
  have hzero : zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) =
      ({0} : AffineSubspace (ZMod 2) (ZMod 2)) := by ext x; simp
  have hone : zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) =
      ({1} : AffineSubspace (ZMod 2) (ZMod 2)) := by ext x; simp [sub_eq_zero]
  have heq : Sanity.twoPoints = Examples.twoPoints (0 : ZMod 2) 1 := by
    ext H
    rw [RealizationExamples.mem_twoPoints]
    simp [Examples.twoPoints, hzero, hone, ← Arrangement.mem_hyperplanes]
  rw [heq]
  exact Examples.poincarePolynomial_twoPoints_zmod_two

/-- The same zero module has bases of two different finite cardinalities, while its certified
Betti number is two. Thus basis cardinality alone cannot define the Betti numbers. -/
theorem different_basis_sizes_zeroTheory_twoPoints :
    let T := Sanity.zeroTheory.{0, 0, 0, 0} (ZMod 2)
    let M := T.grading (complement Sanity.twoPoints) (1, 1)
    Nonempty (Basis (Fin 0) PUnit M) ∧ Nonempty (Basis (Fin 2) PUnit M) := by
  dsimp
  let : Subsingleton ((Sanity.zeroTheory.{0, 0, 0, 0} (ZMod 2)).C.obj
      (complement Sanity.twoPoints)) := inferInstanceAs (Subsingleton PUnit)
  constructor
  · exact ⟨Basis.empty _⟩
  · simpa [Sanity.bettiNumber_one_twoPoints] using
      (Sanity.zeroTheory.{0, 0, 0, 0} (ZMod 2)).nonempty_basis_grading_bettiNumber
        Sanity.twoPoints 1

end OrlikSolomon.DegenerateExamples
