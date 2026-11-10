/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Realization
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Quotient

/-!
# Topological independence of an eligible cohomology realization

The four existing quadratic, graded and scalar-quotient realization comparisons are
homeomorphisms for the actual component and quotient topologies. Their data are the old
multiplicative equivalences; continuity follows by composing the canonical adapters.
Independent weight algebras, gradings, admissible domains and cohomology universes are
retained. No classification, algebraicity or morphism between theories is assumed.

Whole stage and common-target formulas, scalar and Galois families, literal restriction,
and the three-realization cocycle use the original comparisons. Expansion rules remain
plain rewrites so both ordinary inverse cancellations stay available to `simp`.

Blueprint: the unclassified realization comparisons in T16 (`thm:t16`).
-/

@[expose] public section

noncomputable section

universe u v r b₁ b₂ b₃ h₁ h₂ h₃

namespace OrlikSolomon.HyperplaneGT.Cohomology

open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R]
  {B₁ : Type b₁} [CommRing B₁] [Algebra R B₁]
  {ℬ₁ : ℤ → Submodule R B₁} [GradedAlgebra ℬ₁] {D₁ : Geometric.SmoothDomain k}
  {B₂ : Type b₂} [CommRing B₂] [Algebra R B₂]
  {ℬ₂ : ℤ → Submodule R B₂} [GradedAlgebra ℬ₂] {D₂ : Geometric.SmoothDomain k}
  {B₃ : Type b₃} [CommRing B₃] [Algebra R B₃]
  {ℬ₃ : ℤ → Submodule R B₃} [GradedAlgebra ℬ₃] {D₃ : Geometric.SmoothDomain k}
  (T₁ : Geometric.OrdinaryTheory.{u, r, b₁, h₁} D₁ ℬ₁)
  (T₂ : Geometric.OrdinaryTheory.{u, r, b₂, h₂} D₂ ℬ₂)
  (T₃ : Geometric.OrdinaryTheory.{u, r, b₃, h₃} D₃ ℬ₃)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The exact old quadratic realization comparison is a topological group isomorphism.
No classification or field-extension condition is needed. Blueprint: T16 (`thm:t16`). -/
def realizationQuadraticContinuousEquiv :
    DiagramAut T₁ C S ≃ₜ* DiagramAut T₂ C S where
  toMulEquiv := realizationQuadraticAutEquiv T₁ T₂ C S
  continuous_toFun := (degreeOneDiagramContinuousEquiv T₂ C S).symm.continuous.comp
    (degreeOneDiagramContinuousEquiv T₁ C S).continuous
  continuous_invFun := (degreeOneDiagramContinuousEquiv T₁ C S).symm.continuous.comp
    (degreeOneDiagramContinuousEquiv T₂ C S).continuous

/-- Forgetting continuity recovers the original quadratic comparison exactly. -/
theorem realizationQuadraticContinuousEquiv_toMulEquiv :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).toMulEquiv =
      realizationQuadraticAutEquiv T₁ T₂ C S := rfl

/-- The topological quadratic comparison has the original forward function. -/
theorem realizationQuadraticContinuousEquiv_coe :
    ⇑(realizationQuadraticContinuousEquiv T₁ T₂ C S) = realizationQuadraticAutEquiv T₁ T₂ C S := rfl

/-- The quadratic homeomorphism evaluates by the original comparison. -/
theorem realizationQuadraticContinuousEquiv_apply (x : DiagramAut T₁ C S) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S x = realizationQuadraticAutEquiv T₁ T₂ C S x :=
      rfl

/-- The inverse quadratic homeomorphism is the original inverse comparison. -/
theorem realizationQuadraticContinuousEquiv_symm_apply (x : DiagramAut T₂ C S) :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).symm x =
      (realizationQuadraticAutEquiv T₁ T₂ C S).symm x := rfl

/-- Comparing a realization with itself gives the identity quadratic map. -/
theorem realizationQuadraticContinuousEquiv_refl :
    realizationQuadraticContinuousEquiv T₁ T₁ C S = ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro x
  change (degreeOneDiagramEquiv T₁ C S).symm (degreeOneDiagramEquiv T₁ C S x) = x
  exact (degreeOneDiagramEquiv T₁ C S).symm_apply_apply x

/-- Reversing the realizations gives the inverse quadratic homeomorphism. -/
theorem realizationQuadraticContinuousEquiv_symm :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).symm = realizationQuadraticContinuousEquiv T₂
      T₁ C S := by
  apply DFunLike.ext
  intro x
  rfl

/-- The quadratic realization homeomorphisms satisfy the three-realization cocycle. -/
theorem realizationQuadraticContinuousEquiv_trans :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).trans (realizationQuadraticContinuousEquiv T₂
      T₃ C S) =
      realizationQuadraticContinuousEquiv T₁ T₃ C S := by
  apply DFunLike.ext
  intro x
  change (degreeOneDiagramEquiv T₃ C S).symm
    (degreeOneDiagramEquiv T₂ C S ((degreeOneDiagramEquiv T₂ C S).symm (degreeOneDiagramEquiv T₁
      C S x))) =
      (degreeOneDiagramEquiv T₃ C S).symm (degreeOneDiagramEquiv T₁ C S x)
  rw [MulEquiv.apply_symm_apply]

/-- The exact old full graded realization comparison is a topological group isomorphism.
No classification or field-extension condition is needed. Blueprint: T16 (`thm:t16`). -/
def realizationGradedContinuousEquiv :
    GradedDiagramAut T₁ C S ≃ₜ* GradedDiagramAut T₂ C S where
  toMulEquiv := realizationGradedAutEquiv T₁ T₂ C S
  continuous_toFun := (gradedDiagramContinuousEquiv T₂ C S).symm.continuous.comp
    (gradedDiagramContinuousEquiv T₁ C S).continuous
  continuous_invFun := (gradedDiagramContinuousEquiv T₁ C S).symm.continuous.comp
    (gradedDiagramContinuousEquiv T₂ C S).continuous

/-- Forgetting continuity recovers the original full graded comparison exactly. -/
theorem realizationGradedContinuousEquiv_toMulEquiv :
    (realizationGradedContinuousEquiv T₁ T₂ C S).toMulEquiv =
      realizationGradedAutEquiv T₁ T₂ C S := rfl

/-- The topological full graded comparison has the original forward function. -/
theorem realizationGradedContinuousEquiv_coe :
    ⇑(realizationGradedContinuousEquiv T₁ T₂ C S) = realizationGradedAutEquiv T₁ T₂ C S := rfl

/-- The full graded homeomorphism evaluates by the original comparison. -/
theorem realizationGradedContinuousEquiv_apply (x : GradedDiagramAut T₁ C S) :
    realizationGradedContinuousEquiv T₁ T₂ C S x = realizationGradedAutEquiv T₁ T₂ C S x := rfl

/-- The inverse full graded homeomorphism is the original inverse comparison. -/
theorem realizationGradedContinuousEquiv_symm_apply (x : GradedDiagramAut T₂ C S) :
    (realizationGradedContinuousEquiv T₁ T₂ C S).symm x =
      (realizationGradedAutEquiv T₁ T₂ C S).symm x := rfl

/-- Comparing a realization with itself gives the identity full graded map. -/
theorem realizationGradedContinuousEquiv_refl :
    realizationGradedContinuousEquiv T₁ T₁ C S = ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro x
  change (gradedDiagramEquiv T₁ C S).symm (gradedDiagramEquiv T₁ C S x) = x
  exact (gradedDiagramEquiv T₁ C S).symm_apply_apply x

/-- Reversing the realizations gives the inverse full graded homeomorphism. -/
theorem realizationGradedContinuousEquiv_symm :
    (realizationGradedContinuousEquiv T₁ T₂ C S).symm = realizationGradedContinuousEquiv T₂ T₁ C
      S := by
  apply DFunLike.ext
  intro x
  rfl

/-- The full graded realization homeomorphisms satisfy the three-realization cocycle. -/
theorem realizationGradedContinuousEquiv_trans :
    (realizationGradedContinuousEquiv T₁ T₂ C S).trans (realizationGradedContinuousEquiv T₂ T₃ C
      S) =
      realizationGradedContinuousEquiv T₁ T₃ C S := by
  apply DFunLike.ext
  intro x
  change (gradedDiagramEquiv T₃ C S).symm
    (gradedDiagramEquiv T₂ C S ((gradedDiagramEquiv T₂ C S).symm (gradedDiagramEquiv T₁ C S x))) =
      (gradedDiagramEquiv T₃ C S).symm (gradedDiagramEquiv T₁ C S x)
  rw [MulEquiv.apply_symm_apply]

/-- The exact old quadratic scalar-quotient realization comparison is a topological group
isomorphism.
No classification or field-extension condition is needed. Blueprint: T16 (`thm:t16`). -/
def realizationQuadraticScalarQuotientContinuousEquiv :
    (DiagramAut T₁ C S ⧸ DiagramAut.scalarSubgroup T₁ C S) ≃ₜ* (DiagramAut T₂ C S ⧸
      DiagramAut.scalarSubgroup T₂ C S) where
  toMulEquiv := realizationQuadraticScalarQuotientEquiv T₁ T₂ C S
  continuous_toFun := (DiagramAut.scalarQuotientContinuousComparison T₂ C S).symm.continuous.comp
    (DiagramAut.scalarQuotientContinuousComparison T₁ C S).continuous
  continuous_invFun := (DiagramAut.scalarQuotientContinuousComparison T₁ C S).symm.continuous.comp
    (DiagramAut.scalarQuotientContinuousComparison T₂ C S).continuous

/-- Forgetting continuity recovers the original quadratic scalar-quotient comparison exactly. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_toMulEquiv :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).toMulEquiv =
      realizationQuadraticScalarQuotientEquiv T₁ T₂ C S := rfl

/-- The topological quadratic scalar-quotient comparison has the original forward function. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_coe :
    ⇑(realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S) =
      realizationQuadraticScalarQuotientEquiv T₁ T₂ C S := rfl

/-- The quadratic scalar-quotient homeomorphism evaluates by the original comparison. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_apply (x : (DiagramAut T₁ C S ⧸
  DiagramAut.scalarSubgroup T₁ C S)) :
    realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S x =
      realizationQuadraticScalarQuotientEquiv T₁ T₂ C S x := rfl

/-- The inverse quadratic scalar-quotient homeomorphism is the original inverse comparison. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_symm_apply (x : (DiagramAut T₂ C S ⧸
  DiagramAut.scalarSubgroup T₂ C S)) :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).symm x =
      (realizationQuadraticScalarQuotientEquiv T₁ T₂ C S).symm x := rfl

/-- Comparing a realization with itself gives the identity quadratic scalar-quotient map. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_refl :
    realizationQuadraticScalarQuotientContinuousEquiv T₁ T₁ C S = ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro x
  change (DiagramAut.scalarQuotientComparison T₁ C S).symm (DiagramAut.scalarQuotientComparison
    T₁ C S x) = x
  exact (DiagramAut.scalarQuotientComparison T₁ C S).symm_apply_apply x

/-- Reversing the realizations gives the inverse quadratic scalar-quotient homeomorphism. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_symm :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).symm =
      realizationQuadraticScalarQuotientContinuousEquiv T₂ T₁ C S := by
  apply DFunLike.ext
  intro x
  rfl

/-- The quadratic scalar-quotient realization homeomorphisms satisfy the three-realization
cocycle. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_trans :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).trans
      (realizationQuadraticScalarQuotientContinuousEquiv T₂ T₃ C S) =
      realizationQuadraticScalarQuotientContinuousEquiv T₁ T₃ C S := by
  apply ContinuousMulEquiv.ext
  intro x
  simp only [ContinuousMulEquiv.trans_apply,
    realizationQuadraticScalarQuotientContinuousEquiv_apply,
    realizationQuadraticScalarQuotientEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The exact old full graded scalar-quotient realization comparison is a topological group
isomorphism.
No classification or field-extension condition is needed. Blueprint: T16 (`thm:t16`). -/
def realizationGradedScalarQuotientContinuousEquiv :
    (GradedDiagramAut T₁ C S ⧸ GradedDiagramAut.scalarSubgroup T₁ C S) ≃ₜ* (GradedDiagramAut T₂ C
      S ⧸ GradedDiagramAut.scalarSubgroup T₂ C S) where
  toMulEquiv := realizationGradedScalarQuotientEquiv T₁ T₂ C S
  continuous_toFun := (GradedDiagramAut.scalarQuotientContinuousComparison T₂ C
    S).symm.continuous.comp
    (GradedDiagramAut.scalarQuotientContinuousComparison T₁ C S).continuous
  continuous_invFun := (GradedDiagramAut.scalarQuotientContinuousComparison T₁ C
    S).symm.continuous.comp
    (GradedDiagramAut.scalarQuotientContinuousComparison T₂ C S).continuous

/-- Forgetting continuity recovers the original full graded scalar-quotient comparison exactly. -/
theorem realizationGradedScalarQuotientContinuousEquiv_toMulEquiv :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).toMulEquiv =
      realizationGradedScalarQuotientEquiv T₁ T₂ C S := rfl

/-- The topological full graded scalar-quotient comparison has the original forward function. -/
theorem realizationGradedScalarQuotientContinuousEquiv_coe :
    ⇑(realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S) =
      realizationGradedScalarQuotientEquiv T₁ T₂ C S := rfl

/-- The full graded scalar-quotient homeomorphism evaluates by the original comparison. -/
theorem realizationGradedScalarQuotientContinuousEquiv_apply (x : (GradedDiagramAut T₁ C S ⧸
  GradedDiagramAut.scalarSubgroup T₁ C S)) :
    realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S x =
      realizationGradedScalarQuotientEquiv T₁ T₂ C S x := rfl

/-- The inverse full graded scalar-quotient homeomorphism is the original inverse comparison. -/
theorem realizationGradedScalarQuotientContinuousEquiv_symm_apply (x : (GradedDiagramAut T₂ C S ⧸
  GradedDiagramAut.scalarSubgroup T₂ C S)) :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).symm x =
      (realizationGradedScalarQuotientEquiv T₁ T₂ C S).symm x := rfl

/-- Comparing a realization with itself gives the identity full graded scalar-quotient map. -/
theorem realizationGradedScalarQuotientContinuousEquiv_refl :
    realizationGradedScalarQuotientContinuousEquiv T₁ T₁ C S = ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro x
  change (GradedDiagramAut.scalarQuotientComparison T₁ C S).symm
    (GradedDiagramAut.scalarQuotientComparison T₁ C S x) = x
  exact (GradedDiagramAut.scalarQuotientComparison T₁ C S).symm_apply_apply x

/-- Reversing the realizations gives the inverse full graded scalar-quotient homeomorphism. -/
theorem realizationGradedScalarQuotientContinuousEquiv_symm :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).symm =
      realizationGradedScalarQuotientContinuousEquiv T₂ T₁ C S := by
  apply DFunLike.ext
  intro x
  rfl

/-- The full graded scalar-quotient realization homeomorphisms satisfy the three-realization
cocycle. -/
theorem realizationGradedScalarQuotientContinuousEquiv_trans :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).trans
      (realizationGradedScalarQuotientContinuousEquiv T₂ T₃ C S) =
      realizationGradedScalarQuotientContinuousEquiv T₁ T₃ C S := by
  apply ContinuousMulEquiv.ext
  intro x
  simp only [ContinuousMulEquiv.trans_apply, realizationGradedScalarQuotientContinuousEquiv_apply,
    realizationGradedScalarQuotientEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The whole actual stage action is conjugated by its canonical realization comparison. -/
theorem realizationQuadraticContinuousEquiv_stage (g : DiagramAut T₁ C S) (A : C.Stage)
    (x : degreeOne T₁ A.val.val) :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S g).stageEquiv A
        (realizationDegreeOneEquiv T₁ T₂ A.val.val x) =
      realizationDegreeOneEquiv T₁ T₂ A.val.val (g.stageEquiv A x) :=
  realizationQuadraticAutEquiv_stage T₁ T₂ C S g A x

/-- The inverse conjugates the same entire actual stage using the reverse realization. -/
theorem realizationQuadraticContinuousEquiv_symm_stage (g : DiagramAut T₂ C S) (A : C.Stage)
    (x : degreeOne T₂ A.val.val) :
    ((realizationQuadraticContinuousEquiv T₁ T₂ C S).symm g).stageEquiv A
        (realizationDegreeOneEquiv T₂ T₁ A.val.val x) =
      realizationDegreeOneEquiv T₂ T₁ A.val.val (g.stageEquiv A x) := by
  rw [realizationQuadraticContinuousEquiv_symm]
  exact realizationQuadraticContinuousEquiv_stage T₂ T₁ C S g A x

/-- The whole actual target action is conjugated by its canonical realization comparison. -/
theorem realizationQuadraticContinuousEquiv_target (g : DiagramAut T₁ C S)
    (x : degreeOne T₁ (twoPunctureArrangement k)) :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S g).targetEquiv
        (realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) x) =
      realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) (g.targetEquiv x) :=
  realizationQuadraticAutEquiv_target T₁ T₂ C S g x

/-- The inverse conjugates the same entire actual target using the reverse realization. -/
theorem realizationQuadraticContinuousEquiv_symm_target (g : DiagramAut T₂ C S)
    (x : degreeOne T₂ (twoPunctureArrangement k)) :
    ((realizationQuadraticContinuousEquiv T₁ T₂ C S).symm g).targetEquiv
        (realizationDegreeOneEquiv T₂ T₁ (twoPunctureArrangement k) x) =
      realizationDegreeOneEquiv T₂ T₁ (twoPunctureArrangement k) (g.targetEquiv x) := by
  rw [realizationQuadraticContinuousEquiv_symm]
  exact realizationQuadraticContinuousEquiv_target T₂ T₁ C S g x

/-- The whole actual stage action is conjugated by its canonical realization comparison. -/
theorem realizationGradedContinuousEquiv_stage (g : GradedDiagramAut T₁ C S) (A : C.Stage)
    (x : diagonal T₁ (D₁.complement A.val.val)) :
    (realizationGradedContinuousEquiv T₁ T₂ C S g).stageEquiv A
        (realizationStageEquiv T₁ T₂ A.val.val x) =
      realizationStageEquiv T₁ T₂ A.val.val (g.stageEquiv A x) :=
  realizationGradedAutEquiv_stage T₁ T₂ C S g A x

/-- The inverse conjugates the same entire actual stage using the reverse realization. -/
theorem realizationGradedContinuousEquiv_symm_stage (g : GradedDiagramAut T₂ C S) (A : C.Stage)
    (x : diagonal T₂ (D₂.complement A.val.val)) :
    ((realizationGradedContinuousEquiv T₁ T₂ C S).symm g).stageEquiv A
        (realizationStageEquiv T₂ T₁ A.val.val x) =
      realizationStageEquiv T₂ T₁ A.val.val (g.stageEquiv A x) := by
  rw [realizationGradedContinuousEquiv_symm]
  exact realizationGradedContinuousEquiv_stage T₂ T₁ C S g A x

/-- The whole actual target action is conjugated by its canonical realization comparison. -/
theorem realizationGradedContinuousEquiv_target (g : GradedDiagramAut T₁ C S)
    (x : diagonal T₁ (schemeMarkingTarget D₁)) :
    (realizationGradedContinuousEquiv T₁ T₂ C S g).targetEquiv
        (realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) x) =
      realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) (g.targetEquiv x) :=
  realizationGradedAutEquiv_target T₁ T₂ C S g x

/-- The inverse conjugates the same entire actual target using the reverse realization. -/
theorem realizationGradedContinuousEquiv_symm_target (g : GradedDiagramAut T₂ C S)
    (x : diagonal T₂ (schemeMarkingTarget D₂)) :
    ((realizationGradedContinuousEquiv T₁ T₂ C S).symm g).targetEquiv
        (realizationStageEquiv T₂ T₁ (twoPunctureArrangement k) x) =
      realizationStageEquiv T₂ T₁ (twoPunctureArrangement k) (g.targetEquiv x) := by
  rw [realizationGradedContinuousEquiv_symm]
  exact realizationGradedContinuousEquiv_target T₂ T₁ C S g x

/-- The quotient comparison takes an actual representative to its canonical conjugate. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_map (g : DiagramAut T₁ C S) :
    realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S (DiagramAut.scalarQuotientMap T₁
      C S g) =
      DiagramAut.scalarQuotientMap T₂ C S (realizationQuadraticContinuousEquiv T₁ T₂ C S g) :=
  realizationQuadraticScalarQuotientEquiv_map T₁ T₂ C S g

/-- The inverse quotient comparison retains the opposite actual representative. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_symm_map (g : DiagramAut T₂ C S) :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).symm
      (DiagramAut.scalarQuotientMap T₂ C S g) =
      DiagramAut.scalarQuotientMap T₁ C S ((realizationQuadraticContinuousEquiv T₁ T₂ C S).symm
        g) := by
  rw [realizationQuadraticScalarQuotientContinuousEquiv_symm,
    realizationQuadraticScalarQuotientContinuousEquiv_map, realizationQuadraticContinuousEquiv_symm]

/-- The quotient comparison takes an actual representative to its canonical conjugate. -/
theorem realizationGradedScalarQuotientContinuousEquiv_map (g : GradedDiagramAut T₁ C S) :
    realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S (GradedDiagramAut.scalarQuotientMap
      T₁ C S g) =
      GradedDiagramAut.scalarQuotientMap T₂ C S (realizationGradedContinuousEquiv T₁ T₂ C S g) :=
  realizationGradedScalarQuotientEquiv_map T₁ T₂ C S g

/-- The inverse quotient comparison retains the opposite actual representative. -/
theorem realizationGradedScalarQuotientContinuousEquiv_symm_map (g : GradedDiagramAut T₂ C S) :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).symm
      (GradedDiagramAut.scalarQuotientMap T₂ C S g) =
      GradedDiagramAut.scalarQuotientMap T₁ C S ((realizationGradedContinuousEquiv T₁ T₂ C
        S).symm g) := by
  apply (Equiv.symm_apply_eq
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).toEquiv).mpr
  exact ((realizationGradedScalarQuotientContinuousEquiv_map T₁ T₂ C S
    ((realizationGradedContinuousEquiv T₁ T₂ C S).symm g)).trans
      (congrArg (GradedDiagramAut.scalarQuotientMap T₂ C S)
        ((realizationGradedContinuousEquiv T₁ T₂ C S).apply_symm_apply g))).symm

/-- The canonical realization comparison preserves the same scalar family. -/
theorem realizationQuadraticContinuousEquiv_scalarQuadraticAction (a : Rˣ) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S (scalarQuadraticAction T₁ C S a) =
      scalarQuadraticAction T₂ C S a :=
  realizationQuadraticAutEquiv_scalarQuadraticAction T₁ T₂ C S a

/-- The canonical realization comparison preserves the same galois family. -/
theorem realizationQuadraticContinuousEquiv_galoisQuadraticAction (a : k ≃ₐ[k₀] k) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S (galoisQuadraticAction T₁ C S a) =
      galoisQuadraticAction T₂ C S a :=
  realizationQuadraticAutEquiv_galoisQuadraticAction T₁ T₂ C S a

/-- Realization comparison commutes with literal stage restriction without classification. -/
theorem realizationQuadraticContinuousEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (g : DiagramAut T₁ C S) :
    realizationQuadraticContinuousEquiv T₁ T₂ C' S (DiagramAut.restrictStages T₁ C C' S hC g) =
      DiagramAut.restrictStages T₂ C C' S hC (realizationQuadraticContinuousEquiv T₁ T₂ C S g) :=
  realizationQuadraticAutEquiv_restrictStages T₁ T₂ C S C' hC g

/-- The canonical realization comparison preserves the same scalar family. -/
theorem realizationGradedContinuousEquiv_scalarGradedAction (a : Rˣ) :
    realizationGradedContinuousEquiv T₁ T₂ C S (scalarGradedAction T₁ C S a) = scalarGradedAction
      T₂ C S a :=
  realizationGradedAutEquiv_scalarGradedAction T₁ T₂ C S a

/-- The canonical realization comparison preserves the same galois family. -/
theorem realizationGradedContinuousEquiv_galoisGradedAction (a : k ≃ₐ[k₀] k) :
    realizationGradedContinuousEquiv T₁ T₂ C S (galoisGradedAction T₁ C S a) = galoisGradedAction
      T₂ C S a :=
  realizationGradedAutEquiv_galoisGradedAction T₁ T₂ C S a

/-- Realization comparison commutes with literal stage restriction without classification. -/
theorem realizationGradedContinuousEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (g : GradedDiagramAut T₁ C S) :
    realizationGradedContinuousEquiv T₁ T₂ C' S (GradedDiagramAut.restrictStages T₁ C C' S hC g) =
      GradedDiagramAut.restrictStages T₂ C C' S hC (realizationGradedContinuousEquiv T₁ T₂ C S g) :=
  realizationGradedAutEquiv_restrictStages T₁ T₂ C S C' hC g

/-- The actual degree-one restriction commutes with realization comparison over every ring. -/
theorem realizationContinuousEquiv_toQuadratic (g : GradedDiagramAut T₁ C S) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S
        (GradedDiagramAut.toQuadratic T₁ C S g) =
      GradedDiagramAut.toQuadratic T₂ C S (realizationGradedContinuousEquiv T₁ T₂ C S g) :=
  realizationAutEquiv_toQuadratic T₁ T₂ C S g

end OrlikSolomon.HyperplaneGT.Cohomology
