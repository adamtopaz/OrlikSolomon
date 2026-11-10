/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull

/-!
# Classified cofinal restrictions of actual supplied theories

The four existing local/domain actual cofinal equivalences become topological group
isomorphisms for the direct component topologies, without any field-extension hypothesis.
`cofinalRestrictionContinuousEquiv` and its graded/domain counterparts keep the exact M8
maps, selected stages, original common target and classified inverses. The scalar and
Galois coordinates are unchanged. Forward expansion rules are plain rewrites, preserving
bare inverse cancellation.

Blueprint: the actual classified cofinal clauses of T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h x

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

/-- The existing actual cofinal equivalence with both continuity proofs, without K or
algebraicity. Blueprint: T15 (`thm:t15`). -/
def cofinalRestrictionContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut T C S ≃ₜ* DiagramAut T C' S where
  toMulEquiv := cofinalRestrictionEquiv T C C' S hC hS hgen hn
  continuous_toFun := ((degreeOneDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C' S).symm)).continuous_toFun
  continuous_invFun := ((degreeOneDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C' S).symm)).continuous_invFun

/-- Forgetting continuity gives exactly the original classified cofinal map. -/
theorem cofinalRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv = cofinalRestrictionEquiv
      T C C' S hC hS hgen hn := rfl

/-- The original cofinal restriction function is unchanged. -/
theorem cofinalRestrictionContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) = cofinalRestrictionEquiv T C C' S
      hC hS hgen hn := rfl

/-- The forward value is literal selection of actual stages with the same target. -/
theorem cofinalRestrictionContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g = DiagramAut.restrictStages T C C' S
      hC g :=
  cofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g

/-- The continuous inverse uses the exact original classified extension. -/
theorem cofinalRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g = (cofinalRestrictionEquiv T
      C C' S hC hS hgen hn).symm g := rfl

/-- Actual cofinal restriction selects the identical complete stage automorphism. -/
theorem cofinalRestrictionContinuousEquiv_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) (A :
      C'.Stage) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).stageEquiv A = g.stageEquiv
      (CofinalSystem.stageInclusion hC A) := by
  rw [cofinalRestrictionContinuousEquiv_apply]
  rfl

/-- The single entire common target is preserved by cofinal restriction. -/
theorem cofinalRestrictionContinuousEquiv_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv := by
  rw [cofinalRestrictionContinuousEquiv_apply]
  rfl

/-- Classified extension recovers the original complete automorphism at selected stages. -/
theorem cofinalRestrictionContinuousEquiv_symm_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) (A :
      C'.Stage) :
    ((cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A := by
  have he := congrArg (fun z : DiagramAut T C' S ↦ z.stageEquiv A)
    ((cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [cofinalRestrictionContinuousEquiv_stageEquiv] at he
  exact he

/-- Classified extension also recovers the one original common target. -/
theorem cofinalRestrictionContinuousEquiv_symm_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    ((cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).targetEquiv = g.targetEquiv
      := by
  have he := congrArg (fun z : DiagramAut T C' S ↦ z.targetEquiv)
    ((cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [cofinalRestrictionContinuousEquiv_targetEquiv] at he
  exact he

/-- Actual restriction preserves both original reconstruction coordinates. -/
theorem cofinalRestrictionContinuousEquiv_classification [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn (localQuadraticReconstruction T C S hS
      hgen hn p) = localQuadraticReconstruction T C' S hS hgen hn p :=
  cofinalRestrictionEquiv_classification T C C' S hC hS hgen hn p

/-- The continuous cofinal upgrade retains the exact actual adapter square. -/
theorem cofinalRestrictionContinuousEquiv_comparison [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    degreeOneDiagramEquiv T C' S (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) =
      HyperplaneGT.cofinalRestrictionEquiv R C C' S hC hS hgen hn (degreeOneDiagramEquiv T C S g)
        :=
  (degreeOneDiagramEquiv T C' S).apply_symm_apply _

/-- Cofinal restriction to the same chosen family is the identity bundled map. -/
theorem cofinalRestrictionContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [cofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose to literal restriction to the final family. -/
theorem cofinalRestrictionContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv T C' C'' S hC' hS hgen hn) =
      cofinalRestrictionContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [ContinuousMulEquiv.trans_apply, cofinalRestrictionContinuousEquiv_apply,
    cofinalRestrictionContinuousEquiv_apply, cofinalRestrictionContinuousEquiv_apply]
  exact DiagramAut.restrictStages_trans T C C' S C'' hC hC' g

/-- The existing actual cofinal equivalence with both continuity proofs, without K or
algebraicity. Blueprint: T15 (`thm:t15`). -/
def gradedCofinalRestrictionContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃ₜ* GradedDiagramAut T C' S where
  toMulEquiv := gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
  continuous_toFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramContinuousEquiv T C' S).symm)).continuous_toFun
  continuous_invFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramContinuousEquiv T C' S).symm)).continuous_invFun

/-- Forgetting continuity gives exactly the original classified cofinal map. -/
theorem gradedCofinalRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The original cofinal restriction function is unchanged. -/
theorem gradedCofinalRestrictionContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The forward value is literal selection of actual stages with the same target. -/
theorem gradedCofinalRestrictionContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages T C C' S hC g :=
  gradedCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g

/-- The continuous inverse uses the exact original classified extension. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g =
      (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g := rfl

/-- Actual cofinal restriction selects the identical complete stage automorphism. -/
theorem gradedCofinalRestrictionContinuousEquiv_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S)
      (A : C'.Stage) :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).stageEquiv A = g.stageEquiv
      (CofinalSystem.stageInclusion hC A) := by
  rw [gradedCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- The single entire common target is preserved by cofinal restriction. -/
theorem gradedCofinalRestrictionContinuousEquiv_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv
      := by
  rw [gradedCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- Classified extension recovers the original complete automorphism at selected stages. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      (A : C'.Stage) :
    ((gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A := by
  have he := congrArg (fun z : GradedDiagramAut T C' S ↦ z.stageEquiv A)
    ((gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [gradedCofinalRestrictionContinuousEquiv_stageEquiv] at he
  exact he

/-- Classified extension also recovers the one original common target. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    ((gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv := by
  have he := congrArg (fun z : GradedDiagramAut T C' S ↦ z.targetEquiv)
    ((gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [gradedCofinalRestrictionContinuousEquiv_targetEquiv] at he
  exact he

/-- Actual restriction preserves both original reconstruction coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_classification [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn (localGradedReconstruction T C S
      hS hgen hn p) = localGradedReconstruction T C' S hS hgen hn p :=
  gradedCofinalRestrictionEquiv_classification T C C' S hC hS hgen hn p

/-- The continuous cofinal upgrade retains the exact actual adapter square. -/
theorem gradedCofinalRestrictionContinuousEquiv_comparison [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    gradedDiagramEquiv T C' S (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) =
      HyperplaneGT.gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn (gradedDiagramEquiv T C S
        g) :=
  (gradedDiagramEquiv T C' S).apply_symm_apply _

/-- Cofinal restriction to the same chosen family is the identity bundled map. -/
theorem gradedCofinalRestrictionContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [gradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose to literal restriction to the final family. -/
theorem gradedCofinalRestrictionContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
      (gradedCofinalRestrictionContinuousEquiv T C' C'' S hC' hS hgen hn) =
      gradedCofinalRestrictionContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [ContinuousMulEquiv.trans_apply, gradedCofinalRestrictionContinuousEquiv_apply,
    gradedCofinalRestrictionContinuousEquiv_apply, gradedCofinalRestrictionContinuousEquiv_apply]
  exact GradedDiagramAut.restrictStages_trans T C C' S C'' hC hC' g

/-- The existing actual cofinal equivalence with both continuity proofs, without K or
algebraicity. Blueprint: T15 (`thm:t15`). -/
def domainCofinalRestrictionContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut T C S ≃ₜ* DiagramAut T C' S where
  toMulEquiv := domainCofinalRestrictionEquiv T C C' S hC hS hgen hn
  continuous_toFun := ((degreeOneDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C' S).symm)).continuous_toFun
  continuous_invFun := ((degreeOneDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C' S).symm)).continuous_invFun

/-- Forgetting continuity gives exactly the original classified cofinal map. -/
theorem domainCofinalRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      domainCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The original cofinal restriction function is unchanged. -/
theorem domainCofinalRestrictionContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The forward value is literal selection of actual stages with the same target. -/
theorem domainCofinalRestrictionContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g = DiagramAut.restrictStages T
      C C' S hC g :=
  domainCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g

/-- The continuous inverse uses the exact original classified extension. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g =
      (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g := rfl

/-- Actual cofinal restriction selects the identical complete stage automorphism. -/
theorem domainCofinalRestrictionContinuousEquiv_stageEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) (A :
      C'.Stage) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).stageEquiv A = g.stageEquiv
      (CofinalSystem.stageInclusion hC A) := by
  rw [domainCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- The single entire common target is preserved by cofinal restriction. -/
theorem domainCofinalRestrictionContinuousEquiv_targetEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv
      := by
  rw [domainCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- Classified extension recovers the original complete automorphism at selected stages. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) (A :
      C'.Stage) :
    ((domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A := by
  have he := congrArg (fun z : DiagramAut T C' S ↦ z.stageEquiv A)
    ((domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [domainCofinalRestrictionContinuousEquiv_stageEquiv] at he
  exact he

/-- Classified extension also recovers the one original common target. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    ((domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv := by
  have he := congrArg (fun z : DiagramAut T C' S ↦ z.targetEquiv)
    ((domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [domainCofinalRestrictionContinuousEquiv_targetEquiv] at he
  exact he

/-- Actual restriction preserves both original reconstruction coordinates. -/
theorem domainCofinalRestrictionContinuousEquiv_classification [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn (domainQuadraticReconstruction T
      C S hS hgen hn p) = domainQuadraticReconstruction T C' S hS hgen hn p :=
  domainCofinalRestrictionEquiv_classification T C C' S hC hS hgen hn p

/-- The continuous cofinal upgrade retains the exact actual adapter square. -/
theorem domainCofinalRestrictionContinuousEquiv_comparison [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    degreeOneDiagramEquiv T C' S (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g)
      =
      HyperplaneGT.domainCofinalRestrictionEquiv R C C' S hC hS hgen hn (degreeOneDiagramEquiv T C
        S g) :=
  (degreeOneDiagramEquiv T C' S).apply_symm_apply _

/-- Cofinal restriction to the same chosen family is the identity bundled map. -/
theorem domainCofinalRestrictionContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [domainCofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose to literal restriction to the final family. -/
theorem domainCofinalRestrictionContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
      (domainCofinalRestrictionContinuousEquiv T C' C'' S hC' hS hgen hn) =
      domainCofinalRestrictionContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [ContinuousMulEquiv.trans_apply, domainCofinalRestrictionContinuousEquiv_apply,
    domainCofinalRestrictionContinuousEquiv_apply, domainCofinalRestrictionContinuousEquiv_apply]
  exact DiagramAut.restrictStages_trans T C C' S C'' hC hC' g

/-- The existing actual cofinal equivalence with both continuity proofs, without K or
algebraicity. Blueprint: T15 (`thm:t15`). -/
def domainGradedCofinalRestrictionContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃ₜ* GradedDiagramAut T C' S where
  toMulEquiv := domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
  continuous_toFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramContinuousEquiv T C' S).symm)).continuous_toFun
  continuous_invFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((HyperplaneGT.domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
      (gradedDiagramContinuousEquiv T C' S).symm)).continuous_invFun

/-- Forgetting continuity gives exactly the original classified cofinal map. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The original cofinal restriction function is unchanged. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn := rfl

/-- The forward value is literal selection of actual stages with the same target. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages T C C' S hC g :=
  domainGradedCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g

/-- The continuous inverse uses the exact original classified extension. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g =
      (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g := rfl

/-- Actual cofinal restriction selects the identical complete stage automorphism. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_stageEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S)
      (A : C'.Stage) :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := by
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- The single entire common target is preserved by cofinal restriction. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_targetEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g).targetEquiv =
      g.targetEquiv := by
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply]
  rfl

/-- Classified extension recovers the original complete automorphism at selected stages. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsDomain R] (hC : C'.stages
  ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      (A : C'.Stage) :
    ((domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A := by
  have he := congrArg (fun z : GradedDiagramAut T C' S ↦ z.stageEquiv A)
    ((domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [domainGradedCofinalRestrictionContinuousEquiv_stageEquiv] at he
  exact he

/-- Classified extension also recovers the one original common target. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsDomain R] (hC : C'.stages
  ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    ((domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv := by
  have he := congrArg (fun z : GradedDiagramAut T C' S ↦ z.targetEquiv)
    ((domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).apply_symm_apply g)
  rw [domainGradedCofinalRestrictionContinuousEquiv_targetEquiv] at he
  exact he

/-- Actual restriction preserves both original reconstruction coordinates. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_classification [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainGradedReconstruction T C S hS hgen hn p) = domainGradedReconstruction T C' S hS hgen
      hn p :=
  domainGradedCofinalRestrictionEquiv_classification T C C' S hC hS hgen hn p

/-- The continuous cofinal upgrade retains the exact actual adapter square. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_comparison [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    gradedDiagramEquiv T C' S (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      g) =
      HyperplaneGT.domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn (gradedDiagramEquiv T
        C S g) :=
  (gradedDiagramEquiv T C' S).apply_symm_apply _

/-- Cofinal restriction to the same chosen family is the identity bundled map. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionContinuousEquiv T C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose to literal restriction to the final family. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀ k
  n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
      (domainGradedCofinalRestrictionContinuousEquiv T C' C'' S hC' hS hgen hn) =
      domainGradedCofinalRestrictionContinuousEquiv T C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [ContinuousMulEquiv.trans_apply, domainGradedCofinalRestrictionContinuousEquiv_apply,
    domainGradedCofinalRestrictionContinuousEquiv_apply,
    domainGradedCofinalRestrictionContinuousEquiv_apply]
  exact GradedDiagramAut.restrictStages_trans T C C' S C'' hC hC' g

end OrlikSolomon.HyperplaneGT.Cohomology
