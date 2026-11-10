/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification

/-!
# Canonical independence of an eligible cohomology realization

Compare two existing C1–C5 ordinary theories through their proved OS equivalences.
Generators determine the comparison uniquely, and all ordinary degrees, whole cup kernels,
inclusions, markings and the common target are retained. No theory morphism or identification
of their independently sized weight algebras is assumed.

Blueprint: realization independence in E02 (`cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r b₁ b₂ b₃ h₁ h₂ h₃

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Module

variable {k : Type u} [Field k] {R : Type r} [CommRing R]
  {B₁ : Type b₁} [CommRing B₁] [Algebra R B₁]
  {ℬ₁ : ℤ → Submodule R B₁} [GradedAlgebra ℬ₁] {D₁ : Geometric.SmoothDomain k}
  {B₂ : Type b₂} [CommRing B₂] [Algebra R B₂]
  {ℬ₂ : ℤ → Submodule R B₂} [GradedAlgebra ℬ₂] {D₂ : Geometric.SmoothDomain k}
  {B₃ : Type b₃} [CommRing B₃] [Algebra R B₃]
  {ℬ₃ : ℤ → Submodule R B₃} [GradedAlgebra ℬ₃] {D₃ : Geometric.SmoothDomain k}
  (T₁ : Geometric.OrdinaryTheory.{u, r, b₁, h₁} D₁ ℬ₁)
  (T₂ : Geometric.OrdinaryTheory.{u, r, b₂, h₂} D₂ ℬ₂)
  (T₃ : Geometric.OrdinaryTheory.{u, r, b₃, h₃} D₃ ℬ₃)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The canonical actual full-diagonal comparison. Blueprint: E02 (`cor:e02`). -/
def realizationStageEquiv (A : Arrangement k V) :
    diagonal T₁ (D₁.complement A) ≃ₐ[R] diagonal T₂ (D₂.complement A) :=
  (T₁.diagonalEquiv A).symm.trans (T₂.diagonalEquiv A)

/-- The actual degree-one comparison through the common free hyperplane module. -/
def realizationDegreeOneEquiv (A : Arrangement k V) :
    degreeOne T₁ A ≃ₗ[R] degreeOne T₂ A :=
  (degreeOneEquiv T₁ A).symm.trans (degreeOneEquiv T₂ A)

/-- The full comparison retains every canonical presentation coordinate. -/
@[simp]
theorem realizationStageEquiv_apply (A : Arrangement k V) (x : OSAlgebra R A) :
    realizationStageEquiv T₁ T₂ A (T₁.diagonalEquiv A x) = T₂.diagonalEquiv A x := by
  simp [realizationStageEquiv]

/-- The actual degree-one comparison retains every vector, not only basis generators. -/
@[simp]
theorem realizationDegreeOneEquiv_apply (A : Arrangement k V) (x : A →₀ R) :
    realizationDegreeOneEquiv T₁ T₂ A (degreeOneEquiv T₁ A x) = degreeOneEquiv T₂ A x := by
  simp [realizationDegreeOneEquiv]

/-- The logarithmic generator has the same hyperplane label in both realizations. -/
theorem realizationStageEquiv_generator (A : Arrangement k V) (H : A) :
    realizationStageEquiv T₁ T₂ A
      (T₁.diagonalEquiv A (OSAlgebra.generator R A H)) =
    T₂.diagonalEquiv A (OSAlgebra.generator R A H) := realizationStageEquiv_apply T₁ T₂ A _

/-- Logarithmic generators uniquely determine the full realization comparison. -/
theorem realizationStageEquiv_unique (A : Arrangement k V)
    (e : diagonal T₁ (D₁.complement A) ≃ₐ[R] diagonal T₂ (D₂.complement A))
    (he : ∀ H : A, e (T₁.diagonalEquiv A (OSAlgebra.generator R A H)) =
      T₂.diagonalEquiv A (OSAlgebra.generator R A H)) :
    e = realizationStageEquiv T₁ T₂ A := by
  have h : e.toAlgHom.comp (T₁.diagonalEquiv A).toAlgHom =
      (T₂.diagonalEquiv A).toAlgHom := by
    apply OSAlgebra.algHom_ext
    exact he
  apply AlgEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (T₁.diagonalEquiv A).surjective x
  exact (DFunLike.congr_fun h x).trans (realizationStageEquiv_apply T₁ T₂ A x).symm

/-- Logarithmic basis generators uniquely determine the degree-one comparison. -/
theorem realizationDegreeOneEquiv_unique (A : Arrangement k V)
    (e : degreeOne T₁ A ≃ₗ[R] degreeOne T₂ A)
    (he : ∀ H : A, e (degreeOneEquiv T₁ A (Finsupp.single H 1)) =
      degreeOneEquiv T₂ A (Finsupp.single H 1)) :
    e = realizationDegreeOneEquiv T₁ T₂ A := by
  have h : e.toLinearMap.comp (degreeOneEquiv T₁ A).toLinearMap =
      (degreeOneEquiv T₂ A).toLinearMap := by
    apply Finsupp.lhom_ext
    intro H a
    change e (degreeOneEquiv T₁ A (Finsupp.single H a)) =
      degreeOneEquiv T₂ A (Finsupp.single H a)
    rw [show Finsupp.single H a = a • Finsupp.single H (1 : R) by simp,
      map_smul, map_smul, map_smul, he]
  apply LinearEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (degreeOneEquiv T₁ A).surjective x
  exact (DFunLike.congr_fun h x).trans (realizationDegreeOneEquiv_apply T₁ T₂ A x).symm

/-- A realization compared with itself gives the identity full comparison. -/
@[simp]
theorem realizationStageEquiv_refl (A : Arrangement k V) :
    realizationStageEquiv T₁ T₁ A = AlgEquiv.refl := by
  ext x
  simp [realizationStageEquiv]

/-- A realization compared with itself gives the identity degree-one comparison. -/
@[simp]
theorem realizationDegreeOneEquiv_refl (A : Arrangement k V) :
    realizationDegreeOneEquiv T₁ T₁ A = LinearEquiv.refl R _ := by
  ext x
  simp [realizationDegreeOneEquiv]

/-- Reversing the two realizations gives the inverse full comparison. -/
theorem realizationStageEquiv_symm (A : Arrangement k V) :
    (realizationStageEquiv T₁ T₂ A).symm = realizationStageEquiv T₂ T₁ A := by
  ext x
  rfl

/-- Reversing realizations gives the inverse degree-one comparison. -/
theorem realizationDegreeOneEquiv_symm (A : Arrangement k V) :
    (realizationDegreeOneEquiv T₁ T₂ A).symm = realizationDegreeOneEquiv T₂ T₁ A := by
  ext x
  rfl

/-- Canonical full realization comparisons satisfy the cocycle identity. -/
theorem realizationStageEquiv_trans (A : Arrangement k V) :
    (realizationStageEquiv T₁ T₂ A).trans (realizationStageEquiv T₂ T₃ A) =
      realizationStageEquiv T₁ T₃ A := by
  ext x
  simp [realizationStageEquiv]

/-- Canonical degree-one comparisons satisfy the same cocycle identity. -/
theorem realizationDegreeOneEquiv_trans (A : Arrangement k V) :
    (realizationDegreeOneEquiv T₁ T₂ A).trans (realizationDegreeOneEquiv T₂ T₃ A) =
      realizationDegreeOneEquiv T₁ T₃ A := by
  ext x
  simp [realizationDegreeOneEquiv]

/-- The entire actual ordinary-degree summand is carried onto the corresponding summand. -/
theorem realizationStageEquiv_degree (A : Arrangement k V) (q : ℕ) :
    (diagonalDegree T₁ (D₁.complement A) q).map
      (realizationStageEquiv T₁ T₂ A).toLinearMap = diagonalDegree T₂ (D₂.complement A) q := by
  rw [← map_diagonalEquiv_degree T₁ A q, ← Submodule.map_comp]
  have he : (realizationStageEquiv T₁ T₂ A).toLinearMap.comp
      (T₁.diagonalEquiv A).toLinearMap = (T₂.diagonalEquiv A).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact realizationStageEquiv_apply T₁ T₂ A x
  rw [he]
  exact map_diagonalEquiv_degree T₂ A q

/-- The complete actual cup kernel is carried onto the other realization's cup kernel,
using the proved degree-two structure theorem rather than an added theory morphism. -/
theorem realizationDegreeOneEquiv_cupKernel (A : Arrangement k V) :
    (LinearMap.ker (cupMap T₁ A)).map
      (exteriorPower.map 2 (realizationDegreeOneEquiv T₁ T₂ A).toLinearMap) =
    LinearMap.ker (cupMap T₂ A) := by
  have he : (realizationDegreeOneEquiv T₁ T₂ A).toLinearMap.comp
      (degreeOneEquiv T₁ A).toLinearMap = (degreeOneEquiv T₂ A).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact realizationDegreeOneEquiv_apply T₁ T₂ A x
  have hmem (z : ⋀[R]^2 (degreeOne T₁ A)) :
      exteriorPower.map 2 (realizationDegreeOneEquiv T₁ T₂ A).toLinearMap z ∈
        LinearMap.ker (cupMap T₂ A) ↔ z ∈ LinearMap.ker (cupMap T₁ A) := by
    obtain ⟨x, rfl⟩ := exteriorPower.map_surjective (degreeOneEquiv T₁ A).surjective z
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, he]
    simp only [LinearMap.mem_ker]
    have h₁ := LinearMap.congr_fun (cupMap_comp_coordinates T₁ A) x
    have h₂ := LinearMap.congr_fun (cupMap_comp_coordinates T₂ A) x
    change cupMap T₁ A (exteriorPower.map 2 (degreeOneEquiv T₁ A).toLinearMap x) =
      T₁.degreeEquiv A 2 (osExteriorSquareMap R A x) at h₁
    change cupMap T₂ A (exteriorPower.map 2 (degreeOneEquiv T₂ A).toLinearMap x) =
      T₂.degreeEquiv A 2 (osExteriorSquareMap R A x) at h₂
    rw [h₁, h₂]
    exact (LinearEquiv.map_eq_zero_iff (T₂.degreeEquiv A 2)).trans
      (LinearEquiv.map_eq_zero_iff (T₁.degreeEquiv A 2)).symm
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (hmem z).mpr hz
  · intro y hy
    obtain ⟨z, rfl⟩ := exteriorPower.map_surjective
      (realizationDegreeOneEquiv T₁ T₂ A).surjective y
    exact ⟨z, (hmem z).mp hy, rfl⟩

/-- The common-target comparison retains the same ordered two logarithmic coordinates. -/
@[simp]
theorem realizationDegreeOneEquiv_target (x : Fin 2 →₀ R) :
    realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k)
      (targetDegreeOneEquiv T₁ x) = targetDegreeOneEquiv T₂ x := by
  change degreeOneEquiv T₂ (twoPunctureArrangement k)
    ((degreeOneEquiv T₁ (twoPunctureArrangement k)).symm
      (degreeOneEquiv T₁ (twoPunctureArrangement k)
        (Finsupp.domLCongr (twoPunctureLabelEquiv k) x))) =
    degreeOneEquiv T₂ (twoPunctureArrangement k)
      (Finsupp.domLCongr (twoPunctureLabelEquiv k) x)
  rw [LinearEquiv.symm_apply_apply]

/-- The full comparison commutes with every actual arrangement-inclusion pullback. -/
theorem realizationStageEquiv_inclusion {A A' : Arrangement k V} (hA : A ≤ A') :
    (realizationStageEquiv T₁ T₂ A').toAlgHom.comp
      (diagonalPull T₁ (D₁.complementInclusion hA)) =
    (diagonalPull T₂ (D₂.complementInclusion hA)).comp
      (realizationStageEquiv T₁ T₂ A).toAlgHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (T₁.diagonalEquiv A).surjective x
  have h₁ := DFunLike.congr_fun (diagonalEquiv_inclusion T₁ hA) x
  have h₂ := DFunLike.congr_fun (diagonalEquiv_inclusion T₂ hA) x
  change diagonalPull T₁ _ (T₁.diagonalEquiv A x) =
    T₁.diagonalEquiv A' (OSAlgebra.map R hA x) at h₁
  change diagonalPull T₂ _ (T₂.diagonalEquiv A x) =
    T₂.diagonalEquiv A' (OSAlgebra.map R hA x) at h₂
  change realizationStageEquiv T₁ T₂ A' (diagonalPull T₁ _ (T₁.diagonalEquiv A x)) =
    diagonalPull T₂ _ (realizationStageEquiv T₁ T₂ A (T₁.diagonalEquiv A x))
  rw [h₁, realizationStageEquiv_apply, realizationStageEquiv_apply, h₂]

/-- The degree-one comparison commutes with the same actual inclusion pullback. -/
theorem realizationDegreeOneEquiv_inclusion {A A' : Arrangement k V} (hA : A ≤ A') :
    (realizationDegreeOneEquiv T₁ T₂ A').toLinearMap.comp
      (componentPull T₁ (D₁.complementInclusion hA) 1) =
    (componentPull T₂ (D₂.complementInclusion hA) 1).comp
      (realizationDegreeOneEquiv T₁ T₂ A).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (degreeOneEquiv T₁ A).surjective x
  have h₁ := LinearMap.congr_fun (degreeOneEquiv_inclusion T₁ hA) x
  have h₂ := LinearMap.congr_fun (degreeOneEquiv_inclusion T₂ hA) x
  change componentPull T₁ _ 1 (degreeOneEquiv T₁ A x) =
    degreeOneEquiv T₁ A' (Finsupp.lmapDomain R R (Arrangement.inclusion hA) x) at h₁
  change componentPull T₂ _ 1 (degreeOneEquiv T₂ A x) =
    degreeOneEquiv T₂ A' (Finsupp.lmapDomain R R (Arrangement.inclusion hA) x) at h₂
  change realizationDegreeOneEquiv T₁ T₂ A'
    (componentPull T₁ _ 1 (degreeOneEquiv T₁ A x)) =
      componentPull T₂ _ 1 (realizationDegreeOneEquiv T₁ T₂ A (degreeOneEquiv T₁ A x))
  rw [h₁, realizationDegreeOneEquiv_apply, realizationDegreeOneEquiv_apply, h₂]

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k] {n : ℕ}
  (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The full comparison commutes with every actual tagged marking from the same target. -/
theorem realizationStageEquiv_marking (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (realizationStageEquiv T₁ T₂ A).toAlgHom.comp (diagonalPull T₁ (w.schemeMap D₁ hw)) =
    (diagonalPull T₂ (w.schemeMap D₂ hw)).comp
      (realizationStageEquiv T₁ T₂ (twoPunctureArrangement k)).toAlgHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (T₁.diagonalEquiv (twoPunctureArrangement k)).surjective x
  have h₁ := DFunLike.congr_fun (diagonalEquiv_marking T₁ w hw) x
  have h₂ := DFunLike.congr_fun (diagonalEquiv_marking T₂ w hw) x
  change diagonalPull T₁ _ (T₁.diagonalEquiv _ x) = T₁.diagonalEquiv A (w.osMap R hw x) at h₁
  change diagonalPull T₂ _ (T₂.diagonalEquiv _ x) = T₂.diagonalEquiv A (w.osMap R hw x) at h₂
  change realizationStageEquiv T₁ T₂ A (diagonalPull T₁ _ (T₁.diagonalEquiv _ x)) =
    diagonalPull T₂ _ (realizationStageEquiv T₁ T₂ _ (T₁.diagonalEquiv _ x))
  rw [h₁, realizationStageEquiv_apply, realizationStageEquiv_apply, h₂]

/-- The actual degree-one marking square uses the same ordered common target. -/
theorem realizationDegreeOneEquiv_marking (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (realizationDegreeOneEquiv T₁ T₂ A).toLinearMap.comp
      (componentPull T₁ (w.schemeMap D₁ hw) 1) =
    (componentPull T₂ (w.schemeMap D₂ hw) 1).comp
      (realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k)).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (targetDegreeOneEquiv T₁).surjective x
  have h₁ := LinearMap.congr_fun (degreeOneEquiv_marking T₁ w hw) x
  have h₂ := LinearMap.congr_fun (degreeOneEquiv_marking T₂ w hw) x
  change componentPull T₁ _ 1 (targetDegreeOneEquiv T₁ x) =
    degreeOneEquiv T₁ A (w.basisMap R hw x) at h₁
  change componentPull T₂ _ 1 (targetDegreeOneEquiv T₂ x) =
    degreeOneEquiv T₂ A (w.basisMap R hw x) at h₂
  change realizationDegreeOneEquiv T₁ T₂ A (componentPull T₁ _ 1 (targetDegreeOneEquiv T₁ x)) =
    componentPull T₂ _ 1 (realizationDegreeOneEquiv T₁ T₂ _ (targetDegreeOneEquiv T₁ x))
  rw [h₁, realizationDegreeOneEquiv_apply, realizationDegreeOneEquiv_target, h₂]

/-- The canonical multiplicative comparison of actual degree-one/cup-kernel automorphisms.
Blueprint: E02 (`cor:e02`). -/
def realizationQuadraticAutEquiv : DiagramAut T₁ C S ≃* DiagramAut T₂ C S :=
  (degreeOneDiagramEquiv T₁ C S).trans (degreeOneDiagramEquiv T₂ C S).symm

/-- The canonical multiplicative comparison of full actual graded automorphisms. -/
def realizationGradedAutEquiv : GradedDiagramAut T₁ C S ≃* GradedDiagramAut T₂ C S :=
  (gradedDiagramEquiv T₁ C S).trans (gradedDiagramEquiv T₂ C S).symm

/-- The quadratic comparison is the actual degree-one conjugation at each stage. -/
theorem realizationQuadraticAutEquiv_stage (g : DiagramAut T₁ C S) (A : C.Stage)
    (x : degreeOne T₁ A.val.val) :
    (realizationQuadraticAutEquiv T₁ T₂ C S g).stageEquiv A
      (realizationDegreeOneEquiv T₁ T₂ A.val.val x) =
    realizationDegreeOneEquiv T₁ T₂ A.val.val (g.stageEquiv A x) := by
  obtain ⟨x, rfl⟩ := (degreeOneEquiv T₁ A.val.val).surjective x
  rw [realizationDegreeOneEquiv_apply, ← degreeOneDiagramEquiv_stage T₁ C S g A x,
    realizationDegreeOneEquiv_apply]
  exact degreeOneDiagramEquiv_symm_stage T₂ C S (degreeOneDiagramEquiv T₁ C S g) A x

/-- The quadratic comparison conjugates the single actual target equivalence. -/
theorem realizationQuadraticAutEquiv_target (g : DiagramAut T₁ C S)
    (x : degreeOne T₁ (twoPunctureArrangement k)) :
    (realizationQuadraticAutEquiv T₁ T₂ C S g).targetEquiv
      (realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) x) =
    realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) (g.targetEquiv x) := by
  obtain ⟨x, rfl⟩ := (targetDegreeOneEquiv T₁).surjective x
  rw [realizationDegreeOneEquiv_target, ← degreeOneDiagramEquiv_target T₁ C S g x,
    realizationDegreeOneEquiv_target]
  exact degreeOneDiagramEquiv_symm_target T₂ C S (degreeOneDiagramEquiv T₁ C S g) x

/-- The full comparison is the actual algebra conjugation at every stage. -/
theorem realizationGradedAutEquiv_stage (g : GradedDiagramAut T₁ C S) (A : C.Stage)
    (x : diagonal T₁ (D₁.complement A.val.val)) :
    (realizationGradedAutEquiv T₁ T₂ C S g).stageEquiv A
      (realizationStageEquiv T₁ T₂ A.val.val x) =
    realizationStageEquiv T₁ T₂ A.val.val (g.stageEquiv A x) := by
  obtain ⟨x, rfl⟩ := (T₁.diagonalEquiv A.val.val).surjective x
  rw [realizationStageEquiv_apply, ← gradedDiagramEquiv_stage T₁ C S g A x,
    realizationStageEquiv_apply]
  exact gradedDiagramEquiv_symm_stage T₂ C S (gradedDiagramEquiv T₁ C S g) A x

/-- The full comparison conjugates the one actual common-target algebra automorphism. -/
theorem realizationGradedAutEquiv_target (g : GradedDiagramAut T₁ C S)
    (x : diagonal T₁ (schemeMarkingTarget D₁)) :
    (realizationGradedAutEquiv T₁ T₂ C S g).targetEquiv
      (realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) x) =
    realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) (g.targetEquiv x) := by
  obtain ⟨x, rfl⟩ := (T₁.diagonalEquiv (twoPunctureArrangement k)).surjective x
  rw [realizationStageEquiv_apply, ← gradedDiagramEquiv_target T₁ C S g x,
    realizationStageEquiv_apply]
  exact gradedDiagramEquiv_symm_target T₂ C S (gradedDiagramEquiv T₁ C S g) x

end OrlikSolomon.HyperplaneGT.Cohomology
