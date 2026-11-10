/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient

/-!
# Actual cofinal scalar-quotient squares

The new quotient congruences retain the literal actual restrictions, their composition,
the old Galois coordinates and the degree-one square. All pointwise, explicit-condition
and algebraic scalar classifiers commute with these maps. Unrelated families are compared
through their union, without closure of either family under arrangement unions.

Main results are `cofinalScalarQuotientContinuousEquiv_refl`, `_trans`, `_classification`,
`_pointwise`, `_krull`, `_algebraic`, `_restriction` and `_union_comparison`, with exact
graded/domain counterparts. No quotient topology or scalar subgroup is redefined.

Blueprint: actual cofinal scalar-quotient compatibility in T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalScalarQuotientContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).injective
  exact cofinalScalarQuotientContinuousEquiv_galois T C C S (Set.Subset.refl _) hS hgen hn z

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem cofinalScalarQuotientContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (cofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn) =
      cofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn).injective
  change DiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn
      (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z)) =
    DiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn
      (cofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn z)
  rw [cofinalScalarQuotientContinuousEquiv_galois, cofinalScalarQuotientContinuousEquiv_galois,
    cofinalScalarQuotientContinuousEquiv_galois]

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem cofinalScalarQuotientContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((cofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).trans
        (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((cofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [cofinalScalarQuotientContinuousEquiv_galois]
  have he := cofinalScalarQuotientContinuousEquiv_galois T (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((cofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalScalarQuotientContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn).injective
  exact gradedCofinalScalarQuotientContinuousEquiv_galois T C C S (Set.Subset.refl _) hS hgen hn z

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀
    k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (gradedCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn) =
      gradedCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn).injective
  change GradedDiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn
      (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z)) =
    GradedDiagramAut.localScalarQuotientEquiv T C'' S hS hgen hn
      (gradedCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn z)
  rw [gradedCofinalScalarQuotientContinuousEquiv_galois,
    gradedCofinalScalarQuotientContinuousEquiv_galois,
    gradedCofinalScalarQuotientContinuousEquiv_galois]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((gradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn).trans
        (GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((gradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [gradedCofinalScalarQuotientContinuousEquiv_galois]
  have he := gradedCofinalScalarQuotientContinuousEquiv_galois T (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((gradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem domainCofinalScalarQuotientContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalScalarQuotientContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).injective
  exact domainCofinalScalarQuotientContinuousEquiv_galois T C C S (Set.Subset.refl _) hS hgen hn z

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem domainCofinalScalarQuotientContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (domainCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn) =
      domainCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn).injective
  change DiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn
      (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z)) =
    DiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn
      (domainCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn z)
  rw [domainCofinalScalarQuotientContinuousEquiv_galois,
    domainCofinalScalarQuotientContinuousEquiv_galois,
    domainCofinalScalarQuotientContinuousEquiv_galois]

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem domainCofinalScalarQuotientContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((domainCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [domainCofinalScalarQuotientContinuousEquiv_galois]
  have he := domainCofinalScalarQuotientContinuousEquiv_galois T (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((domainCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).injective
  exact domainGradedCofinalScalarQuotientContinuousEquiv_galois T C C S (Set.Subset.refl _) hS hgen
    hn z

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem
    k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (domainGradedCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn) =
      domainGradedCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn).injective
  change GradedDiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C' C'' S hC' hS hgen hn
      (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z)) =
    GradedDiagramAut.domainScalarQuotientEquiv T C'' S hS hgen hn
      (domainGradedCofinalScalarQuotientContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn z)
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_galois,
    domainGradedCofinalScalarQuotientContinuousEquiv_galois,
    domainGradedCofinalScalarQuotientContinuousEquiv_galois]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainGradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainGradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).trans
        (GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((domainGradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_galois]
  have he := domainGradedCofinalScalarQuotientContinuousEquiv_galois T (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((domainGradedCofinalScalarQuotientContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Local and domain scalar-quotient restriction agree on their coefficient overlap. -/
theorem domainCofinalScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn =
      cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro q
  rw [domainCofinalScalarQuotientContinuousEquiv_apply, cofinalScalarQuotientContinuousEquiv_apply]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Local and domain scalar-quotient restriction agree on their coefficient overlap. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn =
      gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro q
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_apply,
    gradedCofinalScalarQuotientContinuousEquiv_apply]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Cofinal scalar-quotient restriction commutes with the exact old degree-one quotient map. -/
theorem cofinalScalarQuotientContinuousEquiv_restriction [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn q) =
      localScalarQuotientRestrictionContinuousEquiv T C' S hS hgen hn
        (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) := by
  apply (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (localScalarQuotientRestrictionEquiv T C S hS hgen hn q)) =
    DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
      (localScalarQuotientRestrictionEquiv T C' S hS hgen hn
        (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q))
  rw [cofinalScalarQuotientContinuousEquiv_galois, localScalarQuotientEquiv_restriction,
    localScalarQuotientEquiv_restriction, gradedCofinalScalarQuotientContinuousEquiv_galois]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Cofinal scalar-quotient restriction commutes with the exact old degree-one quotient map. -/
theorem domainCofinalScalarQuotientContinuousEquiv_restriction [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn q) =
      domainScalarQuotientRestrictionContinuousEquiv T C' S hS hgen hn
        (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) := by
  apply (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (domainScalarQuotientRestrictionEquiv T C S hS hgen hn q)) =
    DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
      (domainScalarQuotientRestrictionEquiv T C' S hS hgen hn
        (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q))
  rw [domainCofinalScalarQuotientContinuousEquiv_galois, domainScalarQuotientEquiv_restriction,
    domainScalarQuotientEquiv_restriction, domainGradedCofinalScalarQuotientContinuousEquiv_galois]

/-- Forgetting topology gives the disclosed old classifier-coordinate composite. -/
theorem cofinalScalarQuotientContinuousEquiv_classification [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).trans
        (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  rw [cofinalScalarQuotientContinuousEquiv_galois, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Forgetting topology gives the disclosed old classifier-coordinate composite. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_classification [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      (GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn).trans
        (GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  rw [gradedCofinalScalarQuotientContinuousEquiv_galois, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

/-- Forgetting topology gives the disclosed old classifier-coordinate composite. -/
theorem domainCofinalScalarQuotientContinuousEquiv_classification [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  rw [domainCofinalScalarQuotientContinuousEquiv_galois, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

set_option maxHeartbeats 600000 in
-- Elaborating the inherited full actual cohomology quotient carrier exceeds the default budget.
/-- Forgetting topology gives the disclosed old classifier-coordinate composite. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_classification [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      (GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).trans
        (GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_galois, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

section Pointwise

open scoped GaloisPointwise

/-- The pointwise scalar classifier retains the same Galois coordinate after restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_pointwise [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.localScalarQuotientContinuousEquiv T C' S hS hgen hn) =
      DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact cofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The pointwise scalar classifier retains the same Galois coordinate after restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_pointwise [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.localScalarQuotientContinuousEquiv T C' S hS hgen hn) =
      GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact gradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The pointwise scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_pointwise [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.domainScalarQuotientContinuousEquiv T C' S hS hgen hn) =
      DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The pointwise scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_pointwise [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.domainScalarQuotientContinuousEquiv T C' S hS hgen hn) =
      GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainGradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

end Pointwise

section Krull

/-- The krull scalar classifier retains the same Galois coordinate after restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_krull [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.localScalarQuotientKrullContinuousEquiv T C' S hS hgen hn hK) =
      DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact cofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The krull scalar classifier retains the same Galois coordinate after restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_krull [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C' S hS hgen hn hK) =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact gradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The krull scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_krull [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.domainScalarQuotientKrullContinuousEquiv T C' S hS hgen hn hK) =
      DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The krull scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_krull [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C' S hS hgen hn hK) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainGradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

end Krull

section Algebraic

/-- The algebraic scalar classifier retains the same Galois coordinate after restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_algebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C' S hS hgen hn) =
      DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact cofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The algebraic scalar classifier retains the same Galois coordinate after restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_algebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀
  k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C' S hS hgen hn) =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact gradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The algebraic scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_algebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C' S hS hgen hn) =
      DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

/-- The algebraic scalar classifier retains the same Galois coordinate after restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_algebraic [IsDomain R] [Algebra.IsAlgebraic
  k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).trans
      (GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C' S hS hgen hn) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn z) = _
  exact domainGradedCofinalScalarQuotientContinuousEquiv_galois T C C' S hC hS hgen hn z

end Algebraic

/-- The two degree-one quotient restrictions agree on the coefficient overlap. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn =
      localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  change domainScalarQuotientRestrictionEquiv T C S hS hgen hn z =
    localScalarQuotientRestrictionEquiv T C S hS hgen hn z
  simp only [domainScalarQuotientRestrictionEquiv, localScalarQuotientRestrictionEquiv,
    DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv,
    GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

end OrlikSolomon.HyperplaneGT.Cohomology
