/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Cofinal
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain

/-!
# Classified restriction to cofinal subsystems

The actual restriction maps become equivalences after reconstruction. In classification
coordinates they preserve exactly the coefficient unit and field automorphism, including
the same common target. The inverse is obtained from classification; arbitrary unclassified
diagram families are never assumed to extend.

Forward expansion equations are plain rewrite rules, preserving ordinary two-sided
equivalence cancellation under `simp`.

Blueprint: the pure classification step in E02 (`cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (R : Type r) [CommRing R] (C C' : CofinalSystem k₀ k n) (S : Set k₀)

/-- The direct quadratic Galois family restricts with the same field automorphism. -/
@[simp]
theorem DiagramAut.restrictStages_galoisQuadraticAut (hC : C'.stages ⊆ C.stages)
    (σ : k ≃ₐ[k₀] k) :
    DiagramAut.restrictStages R C C' S hC (galoisQuadraticAut R C S σ) =
      galoisQuadraticAut R C' S σ := by
  rw [galoisQuadraticAut, ← GradedDiagramAut.toQuadratic_restrictStages,
    GradedDiagramAut.restrictStages_galoisGradedAut]
  rfl

section Local

variable [IsLocalRing R]

/-- Restriction to a cofinal subsystem is an equivalence after the proved
quadratic classification. Blueprint: E02 (`cor:e02`). -/
def cofinalRestrictionEquiv (_hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut R C S ≃* DiagramAut R C' S :=
  (quadraticAutEquiv R C S hS hgen hn).symm.trans
    (quadraticAutEquiv R C' S hS hgen hn)

/-- Restriction preserves the complete scalar/Galois classification coordinate. -/
theorem cofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionEquiv R C C' S hC hS hgen hn
      (quadraticAutEquiv R C S hS hgen hn p) =
        quadraticAutEquiv R C' S hS hgen hn p := by
  simp [cofinalRestrictionEquiv]

/-- The classified equivalence's forward map is the literal stage restriction. -/
theorem cofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    cofinalRestrictionEquiv R C C' S hC hS hgen hn g =
      DiagramAut.restrictStages R C C' S hC g := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := (quadraticAutEquiv R C S hS hgen hn).surjective g
  rw [cofinalRestrictionEquiv_classification, quadraticAutEquiv_apply,
    quadraticAutEquiv_apply, map_mul]
  simp

/-- The inverse extends the uniquely determined classified family, with both parameters
unchanged. -/
theorem cofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) :
    (cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g =
      quadraticAutEquiv R C S hS hgen hn
        ((quadraticAutEquiv R C' S hS hgen hn).symm g) := rfl

/-- Restricting and then extending recovers the original entire diagram. -/
theorem cofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (DiagramAut.restrictStages R C C' S hC g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm_apply_apply g

/-- The classified extension restricts back to the given entire subsystem diagram. -/
theorem cofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) :
    DiagramAut.restrictStages R C C' S hC
      ((cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv R C C' S hC hS hgen hn).apply_symm_apply g

/-- Restriction to a cofinal subsystem is an equivalence after the proved
full graded classification. Blueprint: E02 (`cor:e02`). -/
def gradedCofinalRestrictionEquiv (_hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S ≃* GradedDiagramAut R C' S :=
  (gradedClassificationEquiv R C S hS hgen hn).symm.trans
    (gradedClassificationEquiv R C' S hS hgen hn)

/-- Restriction preserves the complete scalar/Galois classification coordinate. -/
theorem gradedCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
      (gradedClassificationEquiv R C S hS hgen hn p) =
        gradedClassificationEquiv R C' S hS hgen hn p := by
  simp [gradedCofinalRestrictionEquiv]

/-- The classified equivalence's forward map is the literal stage restriction. -/
theorem gradedCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages R C C' S hC g := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := (gradedClassificationEquiv R C S hS hgen hn).surjective g
  rw [gradedCofinalRestrictionEquiv_classification, gradedClassificationEquiv_apply,
    gradedClassificationEquiv_apply, map_mul]
  simp

/-- The inverse extends the uniquely determined classified family, with both parameters
unchanged. -/
theorem gradedCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) :
    (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g =
      gradedClassificationEquiv R C S hS hgen hn
        ((gradedClassificationEquiv R C' S hS hgen hn).symm g) := rfl

/-- Restricting and then extending recovers the original entire diagram. -/
theorem gradedCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (GradedDiagramAut.restrictStages R C C' S hC g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm_apply_apply g

/-- The classified extension restricts back to the given entire subsystem diagram. -/
theorem gradedCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) :
    GradedDiagramAut.restrictStages R C C' S hC
      ((gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).apply_symm_apply g

/-- Graded and quadratic cofinal equivalences commute with actual degree-one restriction. -/
theorem cofinalRestrictionEquiv_toQuadratic (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    cofinalRestrictionEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.toQuadratic R C S g) =
    GradedDiagramAut.toQuadratic R C' S
      (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g) := by
  simp only [cofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_apply,
    GradedDiagramAut.toQuadratic_restrictStages]


/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem DiagramAut.restrictStages_quadraticAutEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    DiagramAut.restrictStages R C C' S hC (quadraticAutEquiv R C S hS hgen hn p) =
      quadraticAutEquiv R C' S hS hgen hn p := by
  rw [← cofinalRestrictionEquiv_apply, cofinalRestrictionEquiv_classification]

/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem GradedDiagramAut.restrictStages_gradedClassificationEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.restrictStages R C C' S hC (gradedClassificationEquiv R C S hS hgen hn p) =
      gradedClassificationEquiv R C' S hS hgen hn p := by
  rw [← gradedCofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_classification]

end Local

section Domain

variable [IsDomain R]

/-- Restriction to a cofinal subsystem is an equivalence after the proved
quadratic classification. Blueprint: E02 (`cor:e02`). -/
def domainCofinalRestrictionEquiv (_hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut R C S ≃* DiagramAut R C' S :=
  (coefficientDomainAutEquiv R C S hS hgen hn).symm.trans
    (coefficientDomainAutEquiv R C' S hS hgen hn)

/-- Restriction preserves the complete scalar/Galois classification coordinate. -/
theorem domainCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionEquiv R C C' S hC hS hgen hn
      (coefficientDomainAutEquiv R C S hS hgen hn p) =
        coefficientDomainAutEquiv R C' S hS hgen hn p := by
  simp [domainCofinalRestrictionEquiv]

/-- The classified equivalence's forward map is the literal stage restriction. -/
theorem domainCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    domainCofinalRestrictionEquiv R C C' S hC hS hgen hn g =
      DiagramAut.restrictStages R C C' S hC g := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := (coefficientDomainAutEquiv R C S hS hgen hn).surjective g
  rw [domainCofinalRestrictionEquiv_classification, coefficientDomainAutEquiv_apply,
    coefficientDomainAutEquiv_apply, map_mul]
  simp

/-- The inverse extends the uniquely determined classified family, with both parameters
unchanged. -/
theorem domainCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) :
    (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g =
      coefficientDomainAutEquiv R C S hS hgen hn
        ((coefficientDomainAutEquiv R C' S hS hgen hn).symm g) := rfl

/-- Restricting and then extending recovers the original entire diagram. -/
theorem domainCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (DiagramAut.restrictStages R C C' S hC g) = g := by
  rw [← domainCofinalRestrictionEquiv_apply]
  exact (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm_apply_apply g

/-- The classified extension restricts back to the given entire subsystem diagram. -/
theorem domainCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) :
    DiagramAut.restrictStages R C C' S hC
      ((domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g) = g := by
  rw [← domainCofinalRestrictionEquiv_apply]
  exact (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).apply_symm_apply g

/-- Restriction to a cofinal subsystem is an equivalence after the proved
full graded classification. Blueprint: E02 (`cor:e02`). -/
def domainGradedCofinalRestrictionEquiv (_hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S ≃* GradedDiagramAut R C' S :=
  (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm.trans
    (coefficientDomainGradedClassificationEquiv R C' S hS hgen hn)

/-- Restriction preserves the complete scalar/Galois classification coordinate. -/
theorem domainGradedCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn p) =
        coefficientDomainGradedClassificationEquiv R C' S hS hgen hn p := by
  simp [domainGradedCofinalRestrictionEquiv]

/-- The classified equivalence's forward map is the literal stage restriction. -/
theorem domainGradedCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages R C C' S hC g := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).surjective g
  rw [domainGradedCofinalRestrictionEquiv_classification,
    coefficientDomainGradedClassificationEquiv_apply,
    coefficientDomainGradedClassificationEquiv_apply, map_mul]
  simp

/-- The inverse extends the uniquely determined classified family, with both parameters
unchanged. -/
theorem domainGradedCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) :
    (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn
        ((coefficientDomainGradedClassificationEquiv R C' S hS hgen hn).symm g) := rfl

/-- Restricting and then extending recovers the original entire diagram. -/
theorem domainGradedCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (GradedDiagramAut.restrictStages R C C' S hC g) = g := by
  rw [← domainGradedCofinalRestrictionEquiv_apply]
  exact (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm_apply_apply g

/-- The classified extension restricts back to the given entire subsystem diagram. -/
theorem domainGradedCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) :
    GradedDiagramAut.restrictStages R C C' S hC
      ((domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g) = g := by
  rw [← domainGradedCofinalRestrictionEquiv_apply]
  exact (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).apply_symm_apply g

/-- Graded and quadratic cofinal equivalences commute with actual degree-one restriction. -/
theorem domainCofinalRestrictionEquiv_toQuadratic (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    domainCofinalRestrictionEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.toQuadratic R C S g) =
    GradedDiagramAut.toQuadratic R C' S
      (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g) := by
  simp only [domainCofinalRestrictionEquiv_apply, domainGradedCofinalRestrictionEquiv_apply,
    GradedDiagramAut.toQuadratic_restrictStages]


/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem DiagramAut.restrictStages_coefficientDomainAutEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    DiagramAut.restrictStages R C C' S hC (coefficientDomainAutEquiv R C S hS hgen hn p) =
      coefficientDomainAutEquiv R C' S hS hgen hn p := by
  rw [← domainCofinalRestrictionEquiv_apply, domainCofinalRestrictionEquiv_classification]

/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem GradedDiagramAut.restrictStages_coefficientDomainGradedClassificationEquiv
    (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.restrictStages R C C' S hC
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn p) =
      coefficientDomainGradedClassificationEquiv R C' S hS hgen hn p := by
  rw [← domainGradedCofinalRestrictionEquiv_apply,
    domainGradedCofinalRestrictionEquiv_classification]

end Domain

/-- The cofinal equivalences agree on the local/domain overlap, by literal restriction. -/
theorem domainCofinalRestrictionEquiv_eq_cofinalRestrictionEquiv [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionEquiv R C C' S hC hS hgen hn =
      cofinalRestrictionEquiv R C C' S hC hS hgen hn := by
  apply MulEquiv.ext
  intro g
  rw [domainCofinalRestrictionEquiv_apply, cofinalRestrictionEquiv_apply]

/-- The cofinal equivalences agree on the local/domain overlap, by literal restriction. -/
theorem domainGradedCofinalRestrictionEquiv_eq_gradedCofinalRestrictionEquiv
    [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn =
      gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn := by
  apply MulEquiv.ext
  intro g
  rw [domainGradedCofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_apply]

end OrlikSolomon.HyperplaneGT
