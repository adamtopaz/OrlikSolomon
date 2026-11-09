/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import OrlikSolomon.Examples.HyperplaneGT.QuadraticKernel
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction.Stage
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import OrlikSolomon.Presentation.Generators

/-!
# Consumers of the full Galois algebra action

These consumers exercise independent universes for the two geometric fields and the
coefficient ring, zero coefficients, dimension zero, and both full families of relators
in arbitrary length. The finite stable closure of the point `x = i` over `ℂ/ℝ` gives a
nontrivial example: complex conjugation moves its actual OS generator over `ℤ`.
The empty-intersection triangle over `𝔽₂` has zero quadratic kernel and still carries its
cubic product relation through the action on the same full quotient.

Blueprint: the finite-stage construction of S02 (`lem:s02`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT.GaloisActionExamples

open OSAlgebra

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
variable {R : Type w} [CommRing R] {n : ℕ}

/-- The coefficient field and the independent coefficient ring are not identified by the
action: every coefficient is fixed. -/
theorem coefficients_fixed (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) (r : R) :
    galoisOSAlgebraEquiv R 𝒜 σ (algebraMap R (OSAlgebra R 𝒜.val) r) =
      algebraMap R (OSAlgebra R 𝒜.val) r := by simp

/-- Moving a hyperplane moves its generator whenever the coefficient ring is nonzero. -/
theorem moved_generator [Nontrivial R] (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (H : 𝒜.val) (hH : galoisLabelEquiv 𝒜 σ H ≠ H) :
    galoisOSAlgebraEquiv R 𝒜 σ (generator R 𝒜.val H) ≠ generator R 𝒜.val H := by
  rw [galoisOSAlgebraEquiv_generator]
  exact (linearIndependent_generator R 𝒜.val).injective.ne hH

/-- Empty-intersection products are preserved in every length, beyond the quadratic ones. -/
theorem empty_intersection_every_length (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (I : List 𝒜.val) (hI : Arrangement.inter I = ⊥) :
    word (generator R 𝒜.val) (I.map (galoisLabelEquiv 𝒜 σ)) = 0 := by
  rw [← galoisOSAlgebraEquiv_word, word_eq_zero_of_inter_eq_bot R 𝒜.val hI, map_zero]

/-- Dependent boundaries are preserved in every length, with their nonempty guard. -/
theorem dependent_boundary_every_length (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (I : List 𝒜.val) (hI : Arrangement.IsDependent I) :
    wordBoundary (generator R 𝒜.val) (I.map (galoisLabelEquiv 𝒜 σ)) = 0 := by
  rw [← galoisOSAlgebraEquiv_wordBoundary,
    wordBoundary_eq_zero_of_isDependent R 𝒜.val hI, map_zero]

/-- The action is available over the zero coefficient ring, without an extra hypothesis. -/
theorem zero_coefficients (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (x : OSAlgebra (ZMod 1) 𝒜.val) : galoisOSAlgebraEquiv (ZMod 1) 𝒜 σ x = x :=
  Subsingleton.elim _ _

/-- Dimension zero needs no special convention about nonempty arrangements. -/
theorem dimension_zero (𝒜 : StableArrangement k₀ k 0) (σ : k ≃ₐ[k₀] k) :
    galoisOSAlgebraEquiv R 𝒜 σ = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro H
  exact (not_isHyperplane_of_subsingleton H.val (𝒜.val.isHyperplane H.property)).elim

/-- Fixed marking labels give fixed generators in characteristic two. -/
theorem marking_characteristic_two (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    {S : Set k₀} (w : Marking S n) (hw : w.Available 𝒜.val) (a : Fin 2) :
    galoisOSAlgebraEquiv (ZMod 2) 𝒜 σ (generator (ZMod 2) 𝒜.val (w.fiberLabel hw a)) =
      generator (ZMod 2) 𝒜.val (w.fiberLabel hw a) := by simp

/-- The empty-intersection triangle over its own base field is a stable stage. -/
def triangleStage : StableArrangement (ZMod 2) (ZMod 2) 2 :=
  ⟨QuadraticKernelExamples.threeLines 1, by
    intro σ H hH
    have hσ : σ = 1 := by
      ext x
      simpa using σ.commutes x
    simpa [hσ] using hH⟩

/-- The actual full quotient can have a nonquadratic defining product even when its entire
quadratic kernel is zero; the Galois action preserves that cubic product relation. -/
theorem triangle_cubic (σ : ZMod 2 ≃ₐ[ZMod 2] ZMod 2) :
    LinearMap.ker (osExteriorSquareMap (ZMod 2) triangleStage.val) = ⊥ ∧
      word (generator (ZMod 2) triangleStage.val)
        (([QuadraticKernelExamples.xLabel 1, QuadraticKernelExamples.yLabel 1,
          QuadraticKernelExamples.diagonalLabel 1] : List triangleStage.val).map
            (galoisLabelEquiv triangleStage σ)) = 0 := by
  constructor
  · exact QuadraticKernelExamples.triangle_kernel (ZMod 2)
  · apply empty_intersection_every_length triangleStage σ
    change Arrangement.inter ([QuadraticKernelExamples.xLabel 1,
      QuadraticKernelExamples.yLabel 1, QuadraticKernelExamples.diagonalLabel 1] :
        List (QuadraticKernelExamples.threeLines (1 : ZMod 2))) = ⊥
    simpa only [Arrangement.inter_cons, Arrangement.inter_nil, inf_top_eq,
      QuadraticKernelExamples.xLabel, QuadraticKernelExamples.yLabel,
      QuadraticKernelExamples.diagonalLabel, inf_assoc] using
      CoordinateExamples.triangle_inter_eq_bot (k := ZMod 2)

/-- The point `x = i` in the complex affine line. -/
def imaginaryHyperplane : Hyperplane ℂ 1 :=
  graphHyperplane 0 (AffineMap.const _ _ Complex.I)

/-- Its finite stable closure over `ℝ`, used only to provide a concrete nontrivial action. -/
def complexStage : StableArrangement ℝ ℂ 1 :=
  ⟨stableClosure {imaginaryHyperplane}, isGaloisStable_stableClosure _⟩

/-- The original point is a genuine label of its finite stable closure. -/
def imaginaryLabel : complexStage.val := by
  refine ⟨imaginaryHyperplane.val, ?_⟩
  change imaginaryHyperplane.val ∈ stableClosure (k₀ := ℝ) {imaginaryHyperplane}
  rw [mem_stableClosure]
  exact subset_galoisClosure _ (by simp)

/-- Complex conjugation acts nontrivially on the hyperplane labels. -/
theorem conjugation_moves_label :
    galoisLabelEquiv complexStage Complex.conjAe imaginaryLabel ≠ imaginaryLabel := by
  intro h
  have hval := congrArg (fun H : complexStage.val ↦ H.val) h
  have hx : (fun _ : Fin 1 ↦ Complex.I) ∈ imaginaryHyperplane.val := by
    simp [imaginaryHyperplane, graphHyperplane, mem_graphSubspace]
  have hx' : (fun _ : Fin 1 ↦ Complex.I) ∈
      fieldAffineSubspace Complex.conjAe.toRingEquiv imaginaryHyperplane.val := by
    rw [galoisLabelEquiv_val] at hval
    exact hval.symm ▸ hx
  rw [mem_fieldAffineSubspace] at hx'
  have heq : (-Complex.I : ℂ) = Complex.I := by
    simpa [imaginaryHyperplane, graphHyperplane, mem_graphSubspace,
      fieldCoordinateAddEquiv_symm_apply, Complex.conjAe] using hx'
  have him := congrArg Complex.im heq
  norm_num at him

/-- The action is nontrivial on the actual full OS algebra with integral coefficients. -/
theorem conjugation_moves_generator :
    galoisOSAlgebraEquiv ℤ complexStage Complex.conjAe
      (generator ℤ complexStage.val imaginaryLabel) ≠
        generator ℤ complexStage.val imaginaryLabel :=
  moved_generator complexStage Complex.conjAe imaginaryLabel conjugation_moves_label

end OrlikSolomon.HyperplaneGT.GaloisActionExamples
