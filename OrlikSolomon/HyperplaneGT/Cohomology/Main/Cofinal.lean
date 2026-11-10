/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification
public import OrlikSolomon.HyperplaneGT.Reconstruction.Cofinal

/-!
# Actual cohomology restriction to cofinal subsystems

Restriction retains the literal actual stage components and one common target, over every
commutative coefficient ring. Its compatibility with A04 is componentwise. Reconstruction
then proves invertibility, preserving the scalar and Galois classification coordinates;
no extension theorem for arbitrary unclassified diagram families is assumed.

Forward expansion equations are plain rewrite rules, preserving ordinary two-sided
equivalence cancellation under `simp`.

Blueprint: cofinal independence in E02 (`cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- Restrict the actual cohomology family, retaining the same common target and all actual
arrow squares. No reconstruction hypotheses enter this map. Blueprint: E02 (`cor:e02`). -/
def restrictStages (hC : C'.stages ⊆ C.stages) :
    DiagramAut T C S →* DiagramAut T C' S where
  toFun g :=
    ofEquivs (T := T) (C := C') (S := S) (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A ↦ g.map_cupKernel (CofinalSystem.stageInclusion hC A))
    (fun A B h ↦ g.inclusion_naturality
      (show CofinalSystem.stageInclusion hC A ≤ CofinalSystem.stageInclusion hC B from h))
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut T C S) (A : C'.Stage) :
    (restrictStages T C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut T C S) :
    (restrictStages T C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restriction to the same actual family is the identity. -/
@[simp]
theorem restrictStages_refl (g : DiagramAut T C S) :
    restrictStages T C C S (Set.Subset.refl _) g = g :=
  DiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive actual restrictions retain exactly the same components and target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (g : DiagramAut T C S) :
    restrictStages T C' C'' S hC' (restrictStages T C C' S hC g) =
      restrictStages T C C'' S (hC'.trans hC) g :=
  DiagramAut.ext (fun _ ↦ rfl) rfl

end DiagramAut

/-- Actual restriction commutes with the proved A04 comparison, componentwise and at the
single common target. -/
@[simp]
theorem degreeOneDiagramEquiv_restrictStages (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut T C S) :
    degreeOneDiagramEquiv T C' S (DiagramAut.restrictStages T C C' S hC g) =
      HyperplaneGT.DiagramAut.restrictStages R C C' S hC (degreeOneDiagramEquiv T C S g) :=
  HyperplaneGT.DiagramAut.ext (fun _ ↦ rfl) rfl

namespace GradedDiagramAut

/-- Restrict the actual cohomology family, retaining the same common target and all actual
arrow squares. No reconstruction hypotheses enter this map. Blueprint: E02 (`cor:e02`). -/
def restrictStages (hC : C'.stages ⊆ C.stages) :
    GradedDiagramAut T C S →* GradedDiagramAut T C' S where
  toFun g :=
    ofEquivs (T := T) (C := C') (S := S) (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A q ↦ g.map_degree (CofinalSystem.stageInclusion hC A) q)
    (fun q ↦ g.map_target_degree q)
    (fun A B h ↦ g.inclusion_naturality
      (show CofinalSystem.stageInclusion hC A ≤ CofinalSystem.stageInclusion hC B from h))
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut T C S) (A : C'.Stage) :
    (restrictStages T C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut T C S) :
    (restrictStages T C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restriction to the same actual family is the identity. -/
@[simp]
theorem restrictStages_refl (g : GradedDiagramAut T C S) :
    restrictStages T C C S (Set.Subset.refl _) g = g :=
  GradedDiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive actual restrictions retain exactly the same components and target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (g : GradedDiagramAut T C S) :
    restrictStages T C' C'' S hC' (restrictStages T C C' S hC g) =
      restrictStages T C C'' S (hC'.trans hC) g :=
  GradedDiagramAut.ext (fun _ ↦ rfl) rfl

end GradedDiagramAut

/-- Actual restriction commutes with the proved A04 comparison, componentwise and at the
single common target. -/
@[simp]
theorem gradedDiagramEquiv_restrictStages (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut T C S) :
    gradedDiagramEquiv T C' S (GradedDiagramAut.restrictStages T C C' S hC g) =
      HyperplaneGT.GradedDiagramAut.restrictStages R C C' S hC (gradedDiagramEquiv T C S g) :=
  HyperplaneGT.GradedDiagramAut.ext (fun _ ↦ rfl) rfl

/-- Literal actual degree-one restriction commutes with restriction of actual stages. -/
@[simp]
theorem GradedDiagramAut.toQuadratic_restrictStages (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut T C S) :
    GradedDiagramAut.toQuadratic T C' S
      (GradedDiagramAut.restrictStages T C C' S hC g) =
    DiagramAut.restrictStages T C C' S hC (GradedDiagramAut.toQuadratic T C S g) := by
  apply (degreeOneDiagramEquiv T C' S).injective
  rw [GradedDiagramAut.toQuadratic_comparison, gradedDiagramEquiv_restrictStages,
    degreeOneDiagramEquiv_restrictStages, GradedDiagramAut.toQuadratic_comparison,
    HyperplaneGT.GradedDiagramAut.toQuadratic_restrictStages]

section Local

variable [IsLocalRing R]

/-- Actual cofinal restriction is an equivalence after the quadratic
classification, retaining the same actual common target. Blueprint: E02 (`cor:e02`). -/
def cofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut T C S ≃* DiagramAut T C' S :=
  (degreeOneDiagramEquiv T C S).trans
    ((HyperplaneGT.cofinalRestrictionEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramEquiv T C' S).symm)

/-- The classified actual equivalence has the literal actual restriction as forward map. -/
theorem cofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    cofinalRestrictionEquiv T C C' S hC hS hgen hn g = DiagramAut.restrictStages T C C' S hC g := by
  apply (degreeOneDiagramEquiv T C' S).injective
  simp only [cofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    HyperplaneGT.cofinalRestrictionEquiv_apply, degreeOneDiagramEquiv_restrictStages]

/-- The actual restriction preserves the same pair of classified parameters. -/
theorem cofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionEquiv T C C' S hC hS hgen hn
      (localQuadraticReconstruction T C S hS hgen hn p) =
      localQuadraticReconstruction T C' S hS hgen hn p := by
  apply (degreeOneDiagramEquiv T C' S).injective
  simp only [cofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    degreeOneDiagramEquiv_localQuadraticReconstruction,
    HyperplaneGT.cofinalRestrictionEquiv_classification]

/-- The inverse extends the unique classified actual family with unchanged parameters. -/
theorem cofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C' S) :
    (cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g =
      localQuadraticReconstruction T C S hS hgen hn
        ((localQuadraticReconstruction T C' S hS hgen hn).symm g) :=
    rfl

/-- Restricting and then extending recovers the entire original actual diagram. -/
theorem cofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (DiagramAut.restrictStages T C C' S hC g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm_apply_apply g

/-- The unique classified extension restricts back to every actual subsystem component. -/
theorem cofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C' S) :
    DiagramAut.restrictStages T C C' S hC
      ((cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g) = g := by
  rw [← cofinalRestrictionEquiv_apply]
  exact (cofinalRestrictionEquiv T C C' S hC hS hgen hn).apply_symm_apply g

/-- Actual cofinal restriction is an equivalence after the graded
classification, retaining the same actual common target. Blueprint: E02 (`cor:e02`). -/
def gradedCofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃* GradedDiagramAut T C' S :=
  (gradedDiagramEquiv T C S).trans
    ((HyperplaneGT.gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramEquiv T C' S).symm)

/-- The classified actual equivalence has the literal actual restriction as forward map. -/
theorem gradedCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages T C C' S hC g :=
    by
  apply (gradedDiagramEquiv T C' S).injective
  simp only [gradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    HyperplaneGT.gradedCofinalRestrictionEquiv_apply, gradedDiagramEquiv_restrictStages]

/-- The actual restriction preserves the same pair of classified parameters. -/
theorem gradedCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
      (localGradedReconstruction T C S hS hgen hn p) =
      localGradedReconstruction T C' S hS hgen hn p := by
  apply (gradedDiagramEquiv T C' S).injective
  simp only [gradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    gradedDiagramEquiv_localGradedReconstruction,
    HyperplaneGT.gradedCofinalRestrictionEquiv_classification]

/-- The inverse extends the unique classified actual family with unchanged parameters. -/
theorem gradedCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C' S) :
    (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g =
      localGradedReconstruction T C S hS hgen hn
        ((localGradedReconstruction T C' S hS hgen hn).symm g) :=
    rfl

/-- Restricting and then extending recovers the entire original actual diagram. -/
theorem gradedCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (GradedDiagramAut.restrictStages T C C' S hC g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm_apply_apply g

/-- The unique classified extension restricts back to every actual subsystem component. -/
theorem gradedCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C' S) :
    GradedDiagramAut.restrictStages T C C' S hC
      ((gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g) = g := by
  rw [← gradedCofinalRestrictionEquiv_apply]
  exact (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).apply_symm_apply g


/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem DiagramAut.restrictStages_localQuadraticReconstruction (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    DiagramAut.restrictStages T C C' S hC (localQuadraticReconstruction T C S hS hgen hn p) =
      localQuadraticReconstruction T C' S hS hgen hn p := by
  rw [← cofinalRestrictionEquiv_apply, cofinalRestrictionEquiv_classification]

/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem GradedDiagramAut.restrictStages_localGradedReconstruction (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.restrictStages T C C' S hC (localGradedReconstruction T C S hS hgen hn p) =
      localGradedReconstruction T C' S hS hgen hn p := by
  rw [← gradedCofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_classification]

end Local

section Domain

variable [IsDomain R]

/-- Actual cofinal restriction is an equivalence after the quadratic
classification, retaining the same actual common target. Blueprint: E02 (`cor:e02`). -/
def domainCofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut T C S ≃* DiagramAut T C' S :=
  (degreeOneDiagramEquiv T C S).trans
    ((HyperplaneGT.domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramEquiv T C' S).symm)

/-- The classified actual equivalence has the literal actual restriction as forward map. -/
theorem domainCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    domainCofinalRestrictionEquiv T C C' S hC hS hgen hn g =
      DiagramAut.restrictStages T C C' S hC g := by
  apply (degreeOneDiagramEquiv T C' S).injective
  simp only [domainCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    HyperplaneGT.domainCofinalRestrictionEquiv_apply, degreeOneDiagramEquiv_restrictStages]

/-- The actual restriction preserves the same pair of classified parameters. -/
theorem domainCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionEquiv T C C' S hC hS hgen hn
      (domainQuadraticReconstruction T C S hS hgen hn p) =
      domainQuadraticReconstruction T C' S hS hgen hn p := by
  apply (degreeOneDiagramEquiv T C' S).injective
  simp only [domainCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    degreeOneDiagramEquiv_domainQuadraticReconstruction,
    HyperplaneGT.domainCofinalRestrictionEquiv_classification]

/-- The inverse extends the unique classified actual family with unchanged parameters. -/
theorem domainCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C' S) :
    (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g =
      domainQuadraticReconstruction T C S hS hgen hn
        ((domainQuadraticReconstruction T C' S hS hgen hn).symm g) :=
    rfl

/-- Restricting and then extending recovers the entire original actual diagram. -/
theorem domainCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (DiagramAut.restrictStages T C C' S hC g) = g := by
  rw [← domainCofinalRestrictionEquiv_apply]
  exact (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm_apply_apply g

/-- The unique classified extension restricts back to every actual subsystem component. -/
theorem domainCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C' S) :
    DiagramAut.restrictStages T C C' S hC
      ((domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g) = g := by
  rw [← domainCofinalRestrictionEquiv_apply]
  exact (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).apply_symm_apply g

/-- Actual cofinal restriction is an equivalence after the graded
classification, retaining the same actual common target. Blueprint: E02 (`cor:e02`). -/
def domainGradedCofinalRestrictionEquiv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃* GradedDiagramAut T C' S :=
  (gradedDiagramEquiv T C S).trans
    ((HyperplaneGT.domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramEquiv T C' S).symm)

/-- The classified actual equivalence has the literal actual restriction as forward map. -/
theorem domainGradedCofinalRestrictionEquiv_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages T C C' S hC g :=
    by
  apply (gradedDiagramEquiv T C' S).injective
  simp only [domainGradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    HyperplaneGT.domainGradedCofinalRestrictionEquiv_apply, gradedDiagramEquiv_restrictStages]

/-- The actual restriction preserves the same pair of classified parameters. -/
theorem domainGradedCofinalRestrictionEquiv_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
      (domainGradedReconstruction T C S hS hgen hn p) =
      domainGradedReconstruction T C' S hS hgen hn p := by
  apply (gradedDiagramEquiv T C' S).injective
  simp only [domainGradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    gradedDiagramEquiv_domainGradedReconstruction,
    HyperplaneGT.domainGradedCofinalRestrictionEquiv_classification]

/-- The inverse extends the unique classified actual family with unchanged parameters. -/
theorem domainGradedCofinalRestrictionEquiv_symm_apply (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C' S) :
    (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g =
      domainGradedReconstruction T C S hS hgen hn
        ((domainGradedReconstruction T C' S hS hgen hn).symm g) :=
    rfl

/-- Restricting and then extending recovers the entire original actual diagram. -/
theorem domainGradedCofinalRestrictionEquiv_left_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (GradedDiagramAut.restrictStages T C C' S hC g) = g := by
  rw [← domainGradedCofinalRestrictionEquiv_apply]
  exact (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm_apply_apply g

/-- The unique classified extension restricts back to every actual subsystem component. -/
theorem domainGradedCofinalRestrictionEquiv_right_inv (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C' S) :
    GradedDiagramAut.restrictStages T C C' S hC
      ((domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g) = g := by
  rw [← domainGradedCofinalRestrictionEquiv_apply]
  exact (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).apply_symm_apply g


/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem DiagramAut.restrictStages_domainQuadraticReconstruction (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    DiagramAut.restrictStages T C C' S hC (domainQuadraticReconstruction T C S hS hgen hn p) =
      domainQuadraticReconstruction T C' S hS hgen hn p := by
  rw [← domainCofinalRestrictionEquiv_apply, domainCofinalRestrictionEquiv_classification]

/-- Literal restriction carries a classified family to the family with unchanged parameters. -/
@[simp]
theorem GradedDiagramAut.restrictStages_domainGradedReconstruction (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.restrictStages T C C' S hC (domainGradedReconstruction T C S hS hgen hn p) =
      domainGradedReconstruction T C' S hS hgen hn p := by
  rw [← domainGradedCofinalRestrictionEquiv_apply,
    domainGradedCofinalRestrictionEquiv_classification]

end Domain

/-- The cofinal equivalences agree on the local/domain overlap, by literal restriction. -/
theorem domainCofinalRestrictionEquiv_eq_cofinalRestrictionEquiv [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionEquiv T C C' S hC hS hgen hn =
      cofinalRestrictionEquiv T C C' S hC hS hgen hn := by
  apply MulEquiv.ext
  intro g
  rw [domainCofinalRestrictionEquiv_apply, cofinalRestrictionEquiv_apply]

/-- The cofinal equivalences agree on the local/domain overlap, by literal restriction. -/
theorem domainGradedCofinalRestrictionEquiv_eq_gradedCofinalRestrictionEquiv
    [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn =
      gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn := by
  apply MulEquiv.ext
  intro g
  rw [domainGradedCofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_apply]

end OrlikSolomon.HyperplaneGT.Cohomology
