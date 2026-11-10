/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Comparison
public import OrlikSolomon.Examples.HyperplaneGT.Diagram
public import OrlikSolomon.Examples.HyperplaneGT.Galois

/-!
# Conditional coefficient and actual-target consumers of the adapter

These consumers use a supplied full geometric ordinary theory. In particular, the
characteristic-two and nonidentity-target statements do not construct or assert the
existence of a nonzero mod-2 realization. They verify that the actual diagram comparisons
require neither nontrivial coefficients nor rational points and retain the target in
dimension zero. No de Rham instance is imported.

The final instance consumers pin the approved transparent carrier synonyms without
introducing duplicate transport instances.

Blueprint: regression consumers for A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u v r b h

open Module

namespace OrlikSolomon.HyperplaneGT.Cohomology.AdapterExamples

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Actual canonical bases exist with independent field and coefficient universes, including
when the coefficient ring is zero. -/
theorem basis_coordinates (A : Arrangement k (Fin n → k)) (x : degreeOne T A) :
    (degreeOneBasis T A).repr x = (degreeOneEquiv T A).symm x :=
  degreeOneBasis_repr T A x

/-- The common actual target uses its ordered two-element basis independently of dimension.
-/
theorem ordered_target_basis (x : degreeOne T (twoPunctureArrangement k)) :
    (targetDegreeOneBasis T).repr x = (targetDegreeOneEquiv T).symm x :=
  targetDegreeOneBasis_repr T x

/-- Both actual diagram comparisons have genuine inverses, including their common target. -/
theorem comparison_roundtrip (g : DiagramAut T C S) :
    (degreeOneDiagramEquiv T C S).symm (degreeOneDiagramEquiv T C S g) = g :=
  (degreeOneDiagramEquiv T C S).symm_apply_apply g

/-- Full actual restriction satisfies the canonical comparison square. -/
theorem restriction_square (g : GradedDiagramAut T C S) :
    degreeOneDiagramEquiv T C S (GradedDiagramAut.toQuadratic T C S g) =
      HyperplaneGT.GradedDiagramAut.toQuadratic R C S (gradedDiagramEquiv T C S g) :=
  GradedDiagramAut.toQuadratic_comparison T C S g

-- These literal-carrier instances failed for an `instance_reducible` diagonal synonym.
-- Keeping the consumers here pins inheritance of the existing direct-sum/product/subgroup
-- instances; there are no duplicate instances in the adapter.
example (X : D.Obj) : AddCommMonoid (diagonal T X) := inferInstance
example (X : D.Obj) : Module R (diagonal T X) := inferInstance
example (X : D.Obj) : Ring (diagonal T X) := inferInstance
example (X : D.Obj) : Algebra R (diagonal T X) := inferInstance
example : Group (QuadraticAutFamily T C) := inferInstance
example : Group (DiagramAut T C S) := inferInstance
example : Group (GradedAutFamily T C) := inferInstance
example : Group (GradedDiagramAut T C S) := inferInstance

section ZeroCoefficients

variable {B₀ : Type b} [CommRing B₀] [Algebra (ZMod 1) B₀]
  {ℬ₀ : ℤ → Submodule (ZMod 1) B₀} [GradedAlgebra ℬ₀]
  (T₀ : Geometric.OrdinaryTheory.{u, 0, b, h} D ℬ₀)

/-- Conditional on a supplied theory with zero coefficients, the actual quadratic group
is trivial while retaining its original actual diagram type. -/
theorem zeroRing_aut_eq_one (g : DiagramAut T₀ C S) : g = 1 := by
  apply (degreeOneDiagramEquiv T₀ C S).injective
  exact Subsingleton.elim _ _

/-- The full actual graded group likewise has its expected zero-coefficient triviality. -/
theorem zeroRing_graded_aut_eq_one (g : GradedDiagramAut T₀ C S) : g = 1 := by
  apply (gradedDiagramEquiv T₀ C S).injective
  exact Subsingleton.elim _ _

end ZeroCoefficients

section CharacteristicTwo

variable {B₂ : Type b} [CommRing B₂] [Algebra (ZMod 2) B₂]
  {ℬ₂ : ℤ → Submodule (ZMod 2) B₂} [GradedAlgebra ℬ₂]
  (T₂ : Geometric.OrdinaryTheory.{u, 0, b, h} D ℬ₂)

/-- Given a full characteristic-two theory, every actual degree-one class squares to zero
by OS transport. No division by two or new mod-2 realization is used. -/
theorem charTwo_square_zero (A : Arrangement k (Fin n → k)) (x : degreeOne T₂ A) :
    (x : T₂.obj (D.complement A)) * (x : T₂.obj (D.complement A)) = 0 :=
  degreeOne_mul_self T₂ A x

/-- Given the same theory, the actual characteristic-two cup kernel is the whole transported
relation span, not merely a containment of the displayed relators. -/
theorem charTwo_whole_kernel (A : Arrangement k (Fin n → k)) :
    LinearMap.ker (cupMap T₂ A) =
      (quadraticRelationSpan (ZMod 2) A).map
        (exteriorPower.map 2 (degreeOneEquiv T₂ A).toLinearMap) := cupKernel_eq T₂ A

/-- At the actual ordered target all degree-one products vanish, conditional on the supplied
full theory; this remains true in characteristic two. -/
theorem charTwo_target_cup_zero : cupMap T₂ (twoPunctureArrangement k) = 0 :=
  target_cupMap_eq_zero T₂

end CharacteristicTwo

section BinaryField

variable {D₂ : Geometric.SmoothDomain (ZMod 2)}
  {B₂ : Type b} [CommRing B₂] [Algebra (ZMod 2) B₂]
  {ℬ₂ : ℤ → Submodule (ZMod 2) B₂} [GradedAlgebra ℬ₂]
  (T₂ : Geometric.OrdinaryTheory.{0, 0, b, h} D₂ ℬ₂)

/-- A conditional actual target interchange in dimension zero. Every stage action remains
identity; the common-target action is retained by the inverse diagram comparison. -/
def zeroDimensionSwap :
    DiagramAut T₂ (DiagramExamples.binarySystem 0) ({0} : Set (ZMod 2)) :=
  (degreeOneDiagramEquiv T₂ _ _).symm (DiagramExamples.zeroDimensionSwap (ZMod 2))

/-- The actual target interchange sends the first canonical logarithmic basis vector to the
second. This statement assumes a full theory, rather than constructing a mod-2 instance. -/
theorem zeroDimensionSwap_target :
    (zeroDimensionSwap T₂).targetEquiv (targetDegreeOneEquiv T₂ (Finsupp.single 0 1)) =
      targetDegreeOneEquiv T₂ (Finsupp.single 1 1) := by
  change ((degreeOneDiagramEquiv T₂ _ _).symm
    (DiagramExamples.zeroDimensionSwap (ZMod 2))).targetEquiv _ = _
  rw [degreeOneDiagramEquiv_symm_target, DiagramExamples.zeroDimensionSwap_target]

/-- Every actual stage component is identity even though the actual target action is not.
-/
theorem zeroDimensionSwap_stage (A : (DiagramExamples.binarySystem 0).Stage) :
    (zeroDimensionSwap T₂).stageEquiv A = LinearEquiv.refl (ZMod 2) _ := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨c, rfl⟩ := (degreeOneEquiv T₂ A.val.val).surjective x
  change ((degreeOneDiagramEquiv T₂ _ _).symm
    (DiagramExamples.zeroDimensionSwap (ZMod 2))).stageEquiv A _ = _
  rw [degreeOneDiagramEquiv_symm_stage, DiagramExamples.zeroDimensionSwap_stage]
  rfl

/-- A supplied full characteristic-two theory has a nonidentity actual common-target
component in dimension zero. No existence of such a nonzero realization is asserted. -/
theorem zeroDimensionSwap_ne_one : zeroDimensionSwap T₂ ≠ 1 := by
  intro he
  have hh := congrArg (degreeOneDiagramEquiv T₂
    (DiagramExamples.binarySystem 0) ({0} : Set (ZMod 2))) he
  change degreeOneDiagramEquiv T₂ _ _ ((degreeOneDiagramEquiv T₂ _ _).symm
    (DiagramExamples.zeroDimensionSwap (ZMod 2))) = _ at hh
  rw [MulEquiv.apply_symm_apply, map_one] at hh
  exact DiagramExamples.zeroDimensionSwap_ne_one hh

/-- The actual two-puncture target over the binary field has an ordered cohomology basis
with the supplied theory, although its coordinate ring has no binary rational point. -/
theorem point_free_target_basis :
    IsEmpty ((markingTarget (ZMod 2)) →ₐ[ZMod 2] ZMod 2) ∧
      Nonempty (Basis (Fin 2) (ZMod 2) (degreeOne T₂ (twoPunctureArrangement (ZMod 2)))) :=
  ⟨GaloisExamples.target_no_rational_points, ⟨targetDegreeOneBasis T₂⟩⟩

end BinaryField

end OrlikSolomon.HyperplaneGT.Cohomology.AdapterExamples
