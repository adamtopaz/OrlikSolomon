/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Reconstruction
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Cofinal

/-!
# Algebraic cofinal wrappers for the ordinary de Rham diagram

Literal selected-stage restriction keeps the old ordinary actions and the one original
common target. It exists in every dimension without marking or field-extension conditions.
The new algebraic equivalences compose the old twists with the existing theory-level
cofinal equivalences, retaining exactly their marking and dimension hypotheses.

This algebraic-only leaf imports no new topology module. No classification argument,
extension axiom or union closure is introduced. The ordinary cofinal homeomorphisms are
separate final T17 upgrades; these names are genuinely new algebraic wrappers.

Blueprint: algebraic cofinal prerequisites of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

namespace DiagramAut

/-- Select literal ordinary stages, retaining the entire original common target. -/
def restrictStages (hC : C'.stages ⊆ C.stages) : DiagramAut C S →* DiagramAut C' S where
  toFun g :=
    ofEquivs (C := C') (S := S) (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A ↦ g.map_cupKernel (CofinalSystem.stageInclusion hC A))
    (fun A B h ↦ g.inclusion_naturality
      (show CofinalSystem.stageInclusion hC A ≤ CofinalSystem.stageInclusion hC B from h))
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction chooses the literal selected ordinary stage, on its whole component. -/
@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut C S) (A : C'.Stage) :
    (restrictStages C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

/-- Restriction keeps the one complete ordinary target exactly unchanged. -/
@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages) (g : DiagramAut C S) :
    (restrictStages C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restricting an ordinary diagram to the same stages changes no component. -/
@[simp]
theorem restrictStages_refl (g : DiagramAut C S) :
    restrictStages C C S (Set.Subset.refl _) g = g :=
  DiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive literal ordinary restrictions select the same stages and common target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages) (g : DiagramAut C S) :
    restrictStages C' C'' S hC' (restrictStages C C' S hC g) =
      restrictStages C C'' S (hC'.trans hC) g :=
  DiagramAut.ext (fun _ ↦ rfl) rfl

end DiagramAut

/-- Literal ordinary stage selection agrees with the exact old theory-level restriction. -/
theorem quadraticTwistEquiv_restrictStages (hC : C'.stages ⊆ C.stages) (g : DiagramAut C S) :
    quadraticTwistEquiv C' S (DiagramAut.restrictStages C C' S hC g) =
      Cohomology.DiagramAut.restrictStages Tdr C C' S hC (quadraticTwistEquiv C S g) := by
  apply Cohomology.DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    intro x
    apply (degreeOneUntwist A.val.val).injective
    exact (quadraticTwistEquiv_stage C' S (DiagramAut.restrictStages C C' S hC g) A x).trans
      (quadraticTwistEquiv_stage C S g (CofinalSystem.stageInclusion hC A) x).symm
  · apply LinearEquiv.ext
    intro x
    apply (degreeOneUntwist (twoPunctureArrangement k)).injective
    exact (quadraticTwistEquiv_target C' S (DiagramAut.restrictStages C C' S hC g) x).trans
      (quadraticTwistEquiv_target C S g x).symm

namespace GradedDiagramAut

/-- Select literal ordinary stages, retaining the entire original common target. -/
def restrictStages (hC : C'.stages ⊆ C.stages) : GradedDiagramAut C S →* GradedDiagramAut C' S where
  toFun g :=
    ofEquivs (C := C') (S := S) (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A q ↦ g.map_degree (CofinalSystem.stageInclusion hC A) q)
    (fun q ↦ g.map_target_degree q)
    (fun A B h ↦ g.inclusion_naturality
      (show CofinalSystem.stageInclusion hC A ≤ CofinalSystem.stageInclusion hC B from h))
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction chooses the literal selected ordinary stage, on its whole component. -/
@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut C S) (A : C'.Stage) :
    (restrictStages C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

/-- Restriction keeps the one complete ordinary target exactly unchanged. -/
@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages) (g : GradedDiagramAut C S) :
    (restrictStages C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restricting an ordinary diagram to the same stages changes no component. -/
@[simp]
theorem restrictStages_refl (g : GradedDiagramAut C S) :
    restrictStages C C S (Set.Subset.refl _) g = g :=
  GradedDiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive literal ordinary restrictions select the same stages and common target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages) (g : GradedDiagramAut C S) :
    restrictStages C' C'' S hC' (restrictStages C C' S hC g) =
      restrictStages C C'' S (hC'.trans hC) g :=
  GradedDiagramAut.ext (fun _ ↦ rfl) rfl

end GradedDiagramAut

/-- Literal ordinary stage selection agrees with the exact old theory-level restriction. -/
theorem gradedTwistEquiv_restrictStages (hC : C'.stages ⊆ C.stages) (g : GradedDiagramAut C S) :
    gradedTwistEquiv C' S (GradedDiagramAut.restrictStages C C' S hC g) =
      Cohomology.GradedDiagramAut.restrictStages Tdr C C' S hC (gradedTwistEquiv C S g) := by
  apply Cohomology.GradedDiagramAut.ext
  · intro A
    apply AlgEquiv.ext
    intro x
    apply (diagonalUntwist ((Geometric.SmoothDomain.aff k).complement A.val.val)).injective
    exact (gradedTwistEquiv_stage C' S (GradedDiagramAut.restrictStages C C' S hC g) A x).trans
      (gradedTwistEquiv_stage C S g (CofinalSystem.stageInclusion hC A) x).symm
  · apply AlgEquiv.ext
    intro x
    apply (diagonalUntwist (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff
      k))).injective
    exact (gradedTwistEquiv_target C' S (GradedDiagramAut.restrictStages C C' S hC g) x).trans
      (gradedTwistEquiv_target C S g x).symm

/-- Literal ordinary H¹ restriction commutes with literal selected-stage restriction. -/
theorem GradedDiagramAut.toQuadratic_restrictStages (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut C S) :
    GradedDiagramAut.toQuadratic C' S (GradedDiagramAut.restrictStages C C' S hC g) =
      DiagramAut.restrictStages C C' S hC (GradedDiagramAut.toQuadratic C S g) := by
  apply (quadraticTwistEquiv C' S).injective
  exact (GradedDiagramAut.toQuadratic_comparison C' S
    (GradedDiagramAut.restrictStages C C' S hC g)).trans
      ((congrArg (Cohomology.GradedDiagramAut.toQuadratic Tdr C' S)
        (gradedTwistEquiv_restrictStages C C' S hC g)).trans
          ((Cohomology.GradedDiagramAut.toQuadratic_restrictStages
            Tdr C C' S hC (gradedTwistEquiv C S g)).trans
              ((congrArg (Cohomology.DiagramAut.restrictStages Tdr C C' S hC)
                (GradedDiagramAut.toQuadratic_comparison C S g).symm).trans
                  (quadraticTwistEquiv_restrictStages C C' S hC
                    (GradedDiagramAut.toQuadratic C S g)).symm)))

/-- The new ordinary cofinal equivalence is the old theory-level equivalence between
exact old twists. Only the old marking and dimension hypotheses enter its inverse. -/
def cofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : DiagramAut C S ≃* DiagramAut C' S :=
  (quadraticTwistEquiv C S).trans
    ((Cohomology.cofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
      (quadraticTwistEquiv C' S).symm)

/-- The new algebraic wrapper is exactly the old theory/twist composite. -/
theorem cofinalRestrictionEquiv_eq_composite (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionEquiv C C' S hC hS hgen hn = (quadraticTwistEquiv C S).trans
      ((Cohomology.cofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
        (quadraticTwistEquiv C' S).symm) := rfl

/-- The ordinary cofinal equivalence has literal selected-stage restriction as forward map. -/
theorem cofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    cofinalRestrictionEquiv C C' S hC hS hgen hn g = DiagramAut.restrictStages C C' S hC g := by
  apply (quadraticTwistEquiv C' S).injective
  simp only [cofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    Cohomology.cofinalRestrictionEquiv_apply, quadraticTwistEquiv_restrictStages]

/-- The forward homomorphism is exactly the new literal restriction homomorphism. -/
theorem cofinalRestrictionEquiv_toMonoidHom (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionEquiv C C' S hC hS hgen hn).toMonoidHom =
      DiagramAut.restrictStages C C' S hC :=
  MonoidHom.ext (cofinalRestrictionEquiv_apply C C' S hC hS hgen hn)

/-- The inverse runs the target twist, the old theory inverse and the source inverse twist. -/
theorem cofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    (cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g = (quadraticTwistEquiv C S).symm
      ((Cohomology.cofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).symm
        (quadraticTwistEquiv C' S g)) := rfl

/-- The canonical algebraic cofinal wrapper preserves the exact old classified parameters. -/
theorem cofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : kˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionEquiv C C' S hC hS hgen hn (quadraticReconstruction C S hS hgen hn p) =
      quadraticReconstruction C' S hS hgen hn p := by
  apply (quadraticTwistEquiv C' S).injective
  simp only [cofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    quadraticTwistEquiv_quadraticReconstruction, Cohomology.cofinalRestrictionEquiv_classification]

/-- Extending the literal restriction recovers every ordinary component and its target. -/
theorem cofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    (cofinalRestrictionEquiv C C' S hC hS hgen hn).symm
        (DiagramAut.restrictStages C C' S hC g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv C C' S hC hS hgen hn).symm_apply_apply g

/-- The canonical ordinary extension restricts back on every selected component and target. -/
theorem cofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    DiagramAut.restrictStages C C' S hC
        ((cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv C C' S hC hS hgen hn).apply_symm_apply g

/-- The canonical inverse extension retains the whole original common target. -/
theorem cofinalRestrictionEquiv_symm_targetEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    ((cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g).targetEquiv = g.targetEquiv := by
  have h := congrArg (fun f : DiagramAut C' S ↦ f.targetEquiv)
    (cofinalRestrictionEquiv_right_inv C C' S hC hS hgen hn g)
  exact h

/-- The old local and domain descriptions agree for this same coefficient field. -/
theorem cofinalRestrictionEquiv_eq_domain_composite (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionEquiv C C' S hC hS hgen hn = (quadraticTwistEquiv C S).trans
      ((Cohomology.domainCofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
        (quadraticTwistEquiv C' S).symm) := by
  rw [Cohomology.domainCofinalRestrictionEquiv_eq_cofinalRestrictionEquiv]
  rfl

/-- The new ordinary cofinal equivalence is the old theory-level equivalence between
exact old twists. Only the old marking and dimension hypotheses enter its inverse. -/
def gradedCofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : GradedDiagramAut C S ≃* GradedDiagramAut C' S :=
  (gradedTwistEquiv C S).trans
    ((Cohomology.gradedCofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
      (gradedTwistEquiv C' S).symm)

/-- The new algebraic wrapper is exactly the old theory/twist composite. -/
theorem gradedCofinalRestrictionEquiv_eq_composite (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionEquiv C C' S hC hS hgen hn = (gradedTwistEquiv C S).trans
      ((Cohomology.gradedCofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
        (gradedTwistEquiv C' S).symm) := rfl

/-- The ordinary cofinal equivalence has literal selected-stage restriction as forward map. -/
theorem gradedCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    gradedCofinalRestrictionEquiv C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages C C' S hC g := by
  apply (gradedTwistEquiv C' S).injective
  simp only [gradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    Cohomology.gradedCofinalRestrictionEquiv_apply, gradedTwistEquiv_restrictStages]

/-- The forward homomorphism is exactly the new literal restriction homomorphism. -/
theorem gradedCofinalRestrictionEquiv_toMonoidHom (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).toMonoidHom =
      GradedDiagramAut.restrictStages C C' S hC :=
  MonoidHom.ext (gradedCofinalRestrictionEquiv_apply C C' S hC hS hgen hn)

/-- The inverse runs the target twist, the old theory inverse and the source inverse twist. -/
theorem gradedCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm g = (gradedTwistEquiv C S).symm
      ((Cohomology.gradedCofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).symm
        (gradedTwistEquiv C' S g)) := rfl

/-- The canonical algebraic cofinal wrapper preserves the exact old classified parameters. -/
theorem gradedCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : kˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionEquiv C C' S hC hS hgen hn (gradedReconstruction C S hS hgen hn p) =
      gradedReconstruction C' S hS hgen hn p := by
  apply (gradedTwistEquiv C' S).injective
  simp only [gradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    gradedTwistEquiv_gradedReconstruction, Cohomology.gradedCofinalRestrictionEquiv_classification]

/-- Extending the literal restriction recovers every ordinary component and its target. -/
theorem gradedCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm
        (GradedDiagramAut.restrictStages C C' S hC g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm_apply_apply g

/-- The canonical ordinary extension restricts back on every selected component and target. -/
theorem gradedCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    GradedDiagramAut.restrictStages C C' S hC
        ((gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).apply_symm_apply g

/-- The canonical inverse extension retains the whole original common target. -/
theorem gradedCofinalRestrictionEquiv_symm_targetEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    ((gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm g).targetEquiv = g.targetEquiv := by
  have h := congrArg (fun f : GradedDiagramAut C' S ↦ f.targetEquiv)
    (gradedCofinalRestrictionEquiv_right_inv C C' S hC hS hgen hn g)
  exact h

/-- The old local and domain descriptions agree for this same coefficient field. -/
theorem gradedCofinalRestrictionEquiv_eq_domain_composite (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionEquiv C C' S hC hS hgen hn = (gradedTwistEquiv C S).trans
      ((Cohomology.domainGradedCofinalRestrictionEquiv Tdr C C' S hC hS hgen hn).trans
        (gradedTwistEquiv C' S).symm) := by
  rw [Cohomology.domainGradedCofinalRestrictionEquiv_eq_gradedCofinalRestrictionEquiv]
  rfl

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
