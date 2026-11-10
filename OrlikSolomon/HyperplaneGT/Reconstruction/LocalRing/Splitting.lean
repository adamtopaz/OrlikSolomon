/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Scalar
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction
public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois

/-!
# The direct Galois section of the reconstructed Galois homomorphism

The existing all-relator graded action restricts through the canonical degree-one map to
the actual quadratic diagram. Its label permutation is the geometric field action and its
common target is the identity. Under the reconstruction hypotheses, extraction recovers
the original field automorphism. This comparison belongs to reconstruction and imposes no
new hypotheses on the independent S02 action.

Blueprint: the comparison after S02 (`lem:s02`) and the splitting in S03 (`thm:s03`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Restrict the existing full graded Galois family to the actual quadratic diagram.
Blueprint: S02 (`lem:s02`) and S03 (`thm:s03`). -/
def galoisQuadraticAut (σ : k ≃ₐ[k₀] k) : DiagramAut R C S :=
  GradedDiagramAut.toQuadratic R C S (galoisGradedAut R C S σ)

/-- The direct Galois action followed by canonical degree-one restriction. -/
def galoisQuadraticAction : (k ≃ₐ[k₀] k) →* DiagramAut R C S :=
  (GradedDiagramAut.toQuadratic R C S).comp (galoisGradedAction R C S)

@[simp]
theorem galoisQuadraticAction_apply (σ : k ≃ₐ[k₀] k) :
    galoisQuadraticAction R C S σ = galoisQuadraticAut R C S σ := rfl

/-- The identity field automorphism gives the identity quadratic family. -/
@[simp]
theorem galoisQuadraticAut_one : galoisQuadraticAut R C S 1 = 1 :=
  (galoisQuadraticAction R C S).map_one

/-- Direct Galois action respects composition in the same order on the quadratic diagram. -/
theorem galoisQuadraticAut_mul (σ τ : k ≃ₐ[k₀] k) :
    galoisQuadraticAut R C S (σ * τ) =
      galoisQuadraticAut R C S σ * galoisQuadraticAut R C S τ :=
  (galoisQuadraticAction R C S).map_mul σ τ

/-- Inverting the field automorphism inverts the restricted Galois family. -/
@[simp]
theorem galoisQuadraticAut_inv (σ : k ≃ₐ[k₀] k) :
    galoisQuadraticAut R C S σ⁻¹ = (galoisQuadraticAut R C S σ)⁻¹ :=
  (galoisQuadraticAction R C S).map_inv σ

/-- The restricted action on a finite-stage generator uses its transformed label. -/
theorem galoisQuadraticAut_stageEquiv_single (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) :
    (galoisQuadraticAut R C S σ).stageEquiv A (Finsupp.single H 1) =
      Finsupp.single (galoisLabelEquiv A.val σ H) 1 := by
  apply (osDegreeOneEquiv R A.val.val).injective
  apply Subtype.ext
  change (osDegreeOneEquiv R A.val.val
    ((galoisGradedAut R C S σ).stageLinearEquiv A (Finsupp.single H 1)) :
      OSAlgebra R A.val.val) = _
  rw [GradedDiagramAut.stageLinearEquiv_apply]
  simp only [osDegreeOneEquiv_single, one_smul]
  exact galoisGradedAut_generator R C S σ A H

/-- The common target of the direct Galois family is the identity in ordered coordinates. -/
@[simp]
theorem galoisQuadraticAut_targetEquiv (σ : k ≃ₐ[k₀] k) :
    (galoisQuadraticAut R C S σ).targetEquiv = 1 := by
  apply LinearEquiv.ext
  intro x
  apply (markingTargetDegreeOneEquiv (k := k) R).injective
  apply Subtype.ext
  change (markingTargetDegreeOneEquiv (k := k) R
    ((galoisGradedAut R C S σ).targetLinearEquiv x) :
      OSAlgebra R (twoPunctureArrangement k)) =
        (markingTargetDegreeOneEquiv (k := k) R x : OSAlgebra R (twoPunctureArrangement k))
  rw [GradedDiagramAut.targetLinearEquiv_apply, galoisGradedAut_targetEquiv]
  rfl

/-- The universal direct Galois action sends a generator to the field-transformed hyperplane. -/
theorem galoisQuadraticAut_universalEquiv_single (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    (galoisQuadraticAut R C S σ).universalEquiv (Finsupp.single H 1) =
      Finsupp.single (σ • H) 1 := by
  classical
  obtain ⟨A, hA⟩ := C.exists_stage_containing {H}
  let H₀ : A.val.val := ⟨H.val, hA H (Finset.mem_singleton_self H)⟩
  have hsingle : finiteStageMap R A.val.val (Finsupp.single H₀ 1) =
      Finsupp.single H 1 := by rw [finiteStageMap_single]; rfl
  rw [← hsingle, DiagramAut.universalEquiv_finiteStageMap,
    galoisQuadraticAut_stageEquiv_single, finiteStageMap_single]
  rfl

variable [IsLocalRing R]

/-- Reconstruction of the direct Galois family recovers exactly its geometric label action. -/
theorem galoisQuadraticAut_hyperplanePerm (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    (galoisQuadraticAut R C S σ).hyperplanePerm hS hn H = σ • H := by
  classical
  have he := (galoisQuadraticAut R C S σ).universalEquiv_single hS hn H
  rw [galoisQuadraticAut_universalEquiv_single] at he
  by_contra hp
  have hv := congrArg (fun x : Hyperplane k n →₀ R ↦
    x ((galoisQuadraticAut R C S σ).hyperplanePerm hS hn H)) he
  simp [hp] at hv
  exact (Units.ne_zero _) hv.symm

/-- The separate reconstruction comparison for the existing full graded Galois action:
degree-one restriction followed by extraction recovers the original automorphism.
Blueprint: the comparison following S02 (`lem:s02`). -/
theorem galoisGradedAut_toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    DiagramAut.toGalois R C S hS hgen hn
      (GradedDiagramAut.toQuadratic R C S (galoisGradedAut R C S σ)) = σ :=
  ((galoisQuadraticAut R C S σ).toGalois_eq_iff_hyperplanePerm hS hgen hn σ).mpr
    (galoisQuadraticAut_hyperplanePerm R C S hS hn σ)

/-- The direct quadratic Galois family is a section of the actual extraction map. -/
@[simp]
theorem galoisQuadraticAut_toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    DiagramAut.toGalois R C S hS hgen hn (galoisQuadraticAut R C S σ) = σ :=
  galoisGradedAut_toGalois R C S hS hgen hn σ

/-- The Galois section is injective, as extraction is its left inverse. -/
theorem galoisQuadraticAction_injective (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    Function.Injective (galoisQuadraticAction R C S) := by
  intro σ τ he
  have h := congrArg (DiagramAut.toGalois R C S hS hgen hn) he
  simpa only [galoisQuadraticAction_apply, galoisQuadraticAut_toGalois] using h

/-- Uniform scalar families have trivial recovered Galois action. -/
@[simp]
theorem scalarQuadraticAut_toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) :
    DiagramAut.toGalois R C S hS hgen hn (scalarQuadraticAut R C S a) = 1 := by
  apply ((scalarQuadraticAut R C S a).toGalois_eq_one_iff_scalar hS hgen hn).mpr
  exact ⟨a, scalarQuadraticAut_stageEquiv_apply R C S a,
    scalarQuadraticAut_targetEquiv_apply R C S a⟩

/-- The kernel of the actual Galois projection is exactly the literal central scalar
subgroup. Both stage and common-target components are retained. Blueprint: S03 (`thm:s03`). -/
theorem DiagramAut.ker_toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut.toGalois R C S hS hgen hn).ker = DiagramAut.scalarSubgroup R C S := by
  ext g
  change DiagramAut.toGalois R C S hS hgen hn g = 1 ↔
    ∃ a : Rˣ, scalarQuadraticAut R C S a = g
  constructor
  · intro hg
    obtain ⟨a, ha, -⟩ := g.scalar_of_toGalois_eq_one hS hgen hn hg
    refine ⟨a, DiagramAut.ext (fun A ↦ ?_) ?_⟩
    · apply LinearEquiv.ext
      intro x
      exact (ha.1 A x).symm
    · apply LinearEquiv.ext
      intro x
      exact (ha.2 x).symm
  · rintro ⟨a, rfl⟩
    exact scalarQuadraticAut_toGalois R C S hS hgen hn a

end OrlikSolomon.HyperplaneGT
