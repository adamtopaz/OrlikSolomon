/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction.Stage

/-!
# The direct Galois action on the full graded diagram

The stage action on the actual full OS presentation, together with the identity on the
one common two-puncture target, defines a full graded diagram automorphism. All inclusion
squares commute. Each marking square commutes because both ordered marking labels are
fixed. The resulting automorphisms form a group action over any commutative coefficient
ring, independently of reconstruction and classification.

Blueprint: S02 (`lem:s02`). The later comparison with the reconstructed Galois map is
separate and is not a premise of this construction.
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

open OSAlgebra

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The stage Galois action commutes with every actual full marking map. -/
theorem galoisOSAlgebraEquiv_osMap (𝒜 : C.Stage) (σ : k ≃ₐ[k₀] k)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    (galoisOSAlgebraEquiv R 𝒜.val σ).toAlgHom.comp (w.osMap R hw) = w.osMap R hw := by
  apply algHom_ext
  intro H
  obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Marking.osMap_generator,
    galoisOSAlgebraEquiv_generator_fiberLabel]

/-- The direct natural graded automorphism induced by a base-field automorphism. Its
common target component is the identity; the stage components use all OS relators.

Blueprint: S02 (`lem:s02`). -/
def galoisGradedAut (σ : k ≃ₐ[k₀] k) : GradedDiagramAut R C S :=
  GradedDiagramAut.ofEquivs (fun 𝒜 ↦ galoisOSAlgebraEquiv R 𝒜.val σ) (AlgEquiv.refl)
    (fun 𝒜 q ↦ map_degree_galoisOSAlgebraEquiv R 𝒜.val σ q)
    (fun q ↦ Submodule.map_id _)
    (fun 𝒜 ℬ h ↦ (galoisOSAlgebraEquiv_naturality R h σ).symm)
    (fun 𝒜 w hw ↦ by
      simpa only [AlgEquiv.refl_toAlgHom, AlgHom.comp_id] using
        galoisOSAlgebraEquiv_osMap R C S 𝒜 σ w hw)

/-- The finite-stage component is the direct presentation automorphism. -/
@[simp]
theorem galoisGradedAut_stageEquiv (σ : k ≃ₐ[k₀] k) (𝒜 : C.Stage) :
    (galoisGradedAut R C S σ).stageEquiv 𝒜 = galoisOSAlgebraEquiv R 𝒜.val σ := rfl

/-- The single common target is fixed identically by the Galois diagram action. -/
@[simp]
theorem galoisGradedAut_targetEquiv (σ : k ≃ₐ[k₀] k) :
    (galoisGradedAut R C S σ).targetEquiv = AlgEquiv.refl := rfl

/-- The diagram action sends every stage generator to its Galois-transformed hyperplane. -/
theorem galoisGradedAut_generator (σ : k ≃ₐ[k₀] k) (𝒜 : C.Stage) (H : 𝒜.val.val) :
    (galoisGradedAut R C S σ).stageEquiv 𝒜 (generator R 𝒜.val.val H) =
      generator R 𝒜.val.val (galoisLabelEquiv 𝒜.val σ H) :=
  galoisOSAlgebraEquiv_generator R 𝒜.val σ H

/-- The identity field automorphism acts identically on the entire marked diagram. -/
@[simp]
theorem galoisGradedAut_one : galoisGradedAut R C S 1 = 1 := by
  apply GradedDiagramAut.ext
  · intro 𝒜
    rw [galoisGradedAut_stageEquiv, GradedDiagramAut.stageEquiv_one]
    exact galoisOSAlgebraEquiv_one R 𝒜.val
  · rw [galoisGradedAut_targetEquiv, GradedDiagramAut.targetEquiv_one]

/-- Galois multiplication agrees with multiplication of full graded diagram automorphisms. -/
theorem galoisGradedAut_mul (σ τ : k ≃ₐ[k₀] k) :
    galoisGradedAut R C S (σ * τ) = galoisGradedAut R C S σ * galoisGradedAut R C S τ := by
  apply GradedDiagramAut.ext
  · intro 𝒜
    rw [galoisGradedAut_stageEquiv, GradedDiagramAut.stageEquiv_mul,
      galoisGradedAut_stageEquiv, galoisGradedAut_stageEquiv]
    exact galoisOSAlgebraEquiv_mul R 𝒜.val σ τ
  · rw [galoisGradedAut_targetEquiv, GradedDiagramAut.targetEquiv_mul,
      galoisGradedAut_targetEquiv, galoisGradedAut_targetEquiv]
    exact (one_mul (1 : OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R]
      OSAlgebra R (twoPunctureArrangement k))).symm

/-- The direct Galois action on the full graded diagram, as a group homomorphism.

Blueprint: the group action in S02 (`lem:s02`). -/
def galoisGradedAction : (k ≃ₐ[k₀] k) →* GradedDiagramAut R C S where
  toFun := galoisGradedAut R C S
  map_one' := galoisGradedAut_one R C S
  map_mul' := galoisGradedAut_mul R C S

@[simp]
theorem galoisGradedAction_apply (σ : k ≃ₐ[k₀] k) :
    galoisGradedAction R C S σ = galoisGradedAut R C S σ := rfl

/-- Inversion agrees with the inverse Galois automorphism throughout the marked diagram. -/
@[simp]
theorem galoisGradedAut_inv (σ : k ≃ₐ[k₀] k) :
    galoisGradedAut R C S σ⁻¹ = (galoisGradedAut R C S σ)⁻¹ :=
  map_inv (galoisGradedAction R C S) σ

end OrlikSolomon.HyperplaneGT
