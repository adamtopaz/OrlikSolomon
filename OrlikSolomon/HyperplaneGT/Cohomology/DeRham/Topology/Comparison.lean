/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Actions
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Ordinary twists preserve the direct finite-stage topologies

The exact old ordinary-to-diagonal twists preserve equality of every whole stage and
of the original common target. Their kernel preimages and the independently defined
stage bases therefore prove inducingness and continuity of both old inverse maps.
The graded comparison uses the actual diagonal and the full ordinary cohomology algebra;
it does not identify the whole Laurent-weighted algebra or all weight-zero classes.

Both new scalar quotient twists are homeomorphisms for the literal Mathlib quotient
topologies. Continuity descends in both directions along quotient projections, without
classification, scalar closedness, dimension or field-extension hypotheses. All public
expansion equations are plain rewrite rules so bare inverse cancellation remains usable.

Blueprint: twist and quotient-twist prerequisites of T17 (`cor:t17`). The final ordinary
classifiers, scalar-quotient-to-Galois maps and cofinal topological upgrades are separate.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Filter Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

/-- The old twist preserves equality of the entire ordinary stage automorphism. -/
theorem quadraticTwistEquiv_stage_eq_iff (g h : DiagramAut C S) (A : C.Stage) :
    (quadraticTwistEquiv C S g).stageEquiv A = (quadraticTwistEquiv C S h).stageEquiv A ↔
      g.stageEquiv A = h.stageEquiv A := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (degreeOneUntwist A.val.val).surjective x
    exact ((quadraticTwistEquiv_stage C S g A y).symm.trans
      (congrArg (degreeOneUntwist A.val.val) (DFunLike.congr_fun heq y))).trans
        (quadraticTwistEquiv_stage C S h A y)
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (degreeOneUntwist A.val.val).injective
    rw [quadraticTwistEquiv_stage, quadraticTwistEquiv_stage, heq]

/-- The old twist preserves equality of the one entire ordinary target automorphism. -/
theorem quadraticTwistEquiv_target_eq_iff (g h : DiagramAut C S) :
    (quadraticTwistEquiv C S g).targetEquiv = (quadraticTwistEquiv C S h).targetEquiv ↔
      g.targetEquiv = h.targetEquiv := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (degreeOneUntwist (twoPunctureArrangement k)).surjective x
    exact ((quadraticTwistEquiv_target C S g y).symm.trans
      (congrArg (degreeOneUntwist (twoPunctureArrangement k)) (DFunLike.congr_fun heq y))).trans
        (quadraticTwistEquiv_target C S h y)
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (degreeOneUntwist (twoPunctureArrangement k)).injective
    rw [quadraticTwistEquiv_target, quadraticTwistEquiv_target, heq]

/-- The old twist pulls back the complete actual stage-and-target kernel to the ordinary one. -/
theorem quadraticTwistEquiv_preimage_stageKernel (A : C.Stage) :
    (quadraticTwistEquiv C S) ⁻¹' (Cohomology.DiagramAut.stageKernel Tdr C S A : Set _) =
      (DiagramAut.stageKernel C S A : Set _) := by
  ext g
  change quadraticTwistEquiv C S g ∈ Cohomology.DiagramAut.stageKernel Tdr C S A ↔
    g ∈ DiagramAut.stageKernel C S A
  rw [Cohomology.DiagramAut.mem_stageKernel, DiagramAut.mem_stageKernel]
  simpa only [map_one, DiagramAut.stageEquiv_one, DiagramAut.targetEquiv_one,
    Cohomology.DiagramAut.stageEquiv_one, Cohomology.DiagramAut.targetEquiv_one,
    LinearEquiv.one_eq_refl] using
    and_congr (quadraticTwistEquiv_stage_eq_iff C S g 1 A)
      (quadraticTwistEquiv_target_eq_iff C S g 1)

/-- The old twist is inducing by the two direct whole-component neighborhood bases. -/
theorem isInducing_quadraticTwistEquiv : IsInducing (quadraticTwistEquiv C S) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply (DiagramAut.nhds_one_stageBasis C S).eq_of_same_basis
  simpa only [quadraticTwistEquiv_preimage_stageKernel] using
    (Cohomology.DiagramAut.nhds_one_stageBasis Tdr C S).comap (quadraticTwistEquiv C S)

/-- The induced-topology identity follows from the direct definitions and their bases. -/
theorem DiagramAut.stageTopology_eq_induced_quadraticTwistEquiv :
    DiagramAut.stageTopology C S = TopologicalSpace.induced (quadraticTwistEquiv C S)
      (Cohomology.DiagramAut.stageTopology Tdr C S) :=
  (isInducing_quadraticTwistEquiv C S).eq_induced

/-- The exact old ordinary twist, with continuity of the old map and its old inverse. -/
def quadraticTwistContinuousEquiv : DiagramAut C S ≃ₜ* Cohomology.DiagramAut Tdr C S where
  __ := quadraticTwistEquiv C S
  continuous_toFun := (isInducing_quadraticTwistEquiv C S).continuous
  continuous_invFun := ((quadraticTwistEquiv C S).toEquiv.toHomeomorphOfIsInducing
    (isInducing_quadraticTwistEquiv C S)).continuous_invFun

/-- The topological upgrade retains the exact old multiplicative equivalence. -/
theorem quadraticTwistContinuousEquiv_toMulEquiv :
    (quadraticTwistContinuousEquiv C S).toMulEquiv = quadraticTwistEquiv C S := rfl

/-- The topological upgrade retains the exact old forward function. -/
theorem quadraticTwistContinuousEquiv_coe :
    ⇑(quadraticTwistContinuousEquiv C S) = quadraticTwistEquiv C S := rfl

/-- Evaluation of the upgrade is exactly evaluation of the old twist. -/
theorem quadraticTwistContinuousEquiv_apply (g : DiagramAut C S) :
    quadraticTwistContinuousEquiv C S g = quadraticTwistEquiv C S g := rfl

/-- The inverse upgrade retains the exact old inverse function. -/
theorem quadraticTwistContinuousEquiv_symm_coe :
    ⇑(quadraticTwistContinuousEquiv C S).symm = (quadraticTwistEquiv C S).symm := rfl

/-- Evaluation of the inverse upgrade is exactly evaluation of the old inverse twist. -/
theorem quadraticTwistContinuousEquiv_symm_apply (g : Cohomology.DiagramAut Tdr C S) :
    (quadraticTwistContinuousEquiv C S).symm g = (quadraticTwistEquiv C S).symm g := rfl

/-- Untwisting intertwines the whole actual stage with the whole ordinary action. -/
theorem quadraticTwistContinuousEquiv_stage (g : DiagramAut C S) (A : C.Stage)
    (z : Cohomology.degreeOne Tdr A.val.val) :
    degreeOneUntwist A.val.val ((quadraticTwistContinuousEquiv C S g).stageEquiv A z) =
      g.stageEquiv A (degreeOneUntwist A.val.val z) :=
  quadraticTwistEquiv_stage C S g A z

/-- Untwisting intertwines the one whole actual target with the original ordinary target. -/
theorem quadraticTwistContinuousEquiv_target (g : DiagramAut C S)
    (z : Cohomology.degreeOne Tdr (twoPunctureArrangement k)) :
    degreeOneUntwist (twoPunctureArrangement k)
        ((quadraticTwistContinuousEquiv C S g).targetEquiv z) =
      g.targetEquiv (degreeOneUntwist (twoPunctureArrangement k) z) :=
  quadraticTwistEquiv_target C S g z

/-- The inverse twist recovers the whole ordinary stage action from the actual one. -/
theorem quadraticTwistContinuousEquiv_symm_stage (g : Cohomology.DiagramAut Tdr C S)
    (A : C.Stage) (z : Cohomology.degreeOne Tdr A.val.val) :
    ((quadraticTwistContinuousEquiv C S).symm g).stageEquiv A (degreeOneUntwist A.val.val z) =
      degreeOneUntwist A.val.val (g.stageEquiv A z) :=
  quadraticTwistEquiv_symm_stage C S g A z

/-- The inverse twist recovers the complete original ordinary target action. -/
theorem quadraticTwistContinuousEquiv_symm_target (g : Cohomology.DiagramAut Tdr C S)
    (z : Cohomology.degreeOne Tdr (twoPunctureArrangement k)) :
    ((quadraticTwistContinuousEquiv C S).symm g).targetEquiv
        (degreeOneUntwist (twoPunctureArrangement k) z) =
      degreeOneUntwist (twoPunctureArrangement k) (g.targetEquiv z) :=
  quadraticTwistEquiv_symm_target C S g z

/-- The old twist preserves equality of the entire ordinary stage automorphism. -/
theorem gradedTwistEquiv_stage_eq_iff (g h : GradedDiagramAut C S) (A : C.Stage) :
    (gradedTwistEquiv C S g).stageEquiv A = (gradedTwistEquiv C S h).stageEquiv A ↔
      g.stageEquiv A = h.stageEquiv A := by
  constructor
  · intro heq
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (diagonalUntwist ((Daff).complement A.val.val)).surjective x
    exact ((gradedTwistEquiv_stage C S g A y).symm.trans
      (congrArg (diagonalUntwist ((Daff).complement A.val.val)) (DFunLike.congr_fun heq y))).trans
        (gradedTwistEquiv_stage C S h A y)
  · intro heq
    apply AlgEquiv.ext
    intro x
    apply (diagonalUntwist ((Daff).complement A.val.val)).injective
    rw [gradedTwistEquiv_stage, gradedTwistEquiv_stage, heq]

/-- The old twist preserves equality of the one entire ordinary target automorphism. -/
theorem gradedTwistEquiv_target_eq_iff (g h : GradedDiagramAut C S) :
    (gradedTwistEquiv C S g).targetEquiv = (gradedTwistEquiv C S h).targetEquiv ↔
      g.targetEquiv = h.targetEquiv := by
  constructor
  · intro heq
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)).surjective x
    exact ((gradedTwistEquiv_target C S g y).symm.trans
      (congrArg (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)) (DFunLike.congr_fun heq
        y))).trans
        (gradedTwistEquiv_target C S h y)
  · intro heq
    apply AlgEquiv.ext
    intro x
    apply (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)).injective
    rw [gradedTwistEquiv_target, gradedTwistEquiv_target, heq]

/-- The old twist pulls back the complete actual stage-and-target kernel to the ordinary one. -/
theorem gradedTwistEquiv_preimage_stageKernel (A : C.Stage) :
    (gradedTwistEquiv C S) ⁻¹' (Cohomology.GradedDiagramAut.stageKernel Tdr C S A : Set _) =
      (GradedDiagramAut.stageKernel C S A : Set _) := by
  ext g
  change gradedTwistEquiv C S g ∈ Cohomology.GradedDiagramAut.stageKernel Tdr C S A ↔
    g ∈ GradedDiagramAut.stageKernel C S A
  rw [Cohomology.GradedDiagramAut.mem_stageKernel, GradedDiagramAut.mem_stageKernel]
  simpa only [map_one, GradedDiagramAut.stageEquiv_one, GradedDiagramAut.targetEquiv_one,
    Cohomology.GradedDiagramAut.stageEquiv_one, Cohomology.GradedDiagramAut.targetEquiv_one,
    AlgEquiv.aut_one] using
    and_congr (gradedTwistEquiv_stage_eq_iff C S g 1 A) (gradedTwistEquiv_target_eq_iff C S g 1)

/-- The old twist is inducing by the two direct whole-component neighborhood bases. -/
theorem isInducing_gradedTwistEquiv : IsInducing (gradedTwistEquiv C S) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply (GradedDiagramAut.nhds_one_stageBasis C S).eq_of_same_basis
  simpa only [gradedTwistEquiv_preimage_stageKernel] using
    (Cohomology.GradedDiagramAut.nhds_one_stageBasis Tdr C S).comap (gradedTwistEquiv C S)

/-- The induced-topology identity follows from the direct definitions and their bases. -/
theorem GradedDiagramAut.stageTopology_eq_induced_gradedTwistEquiv :
    GradedDiagramAut.stageTopology C S = TopologicalSpace.induced (gradedTwistEquiv C S)
      (Cohomology.GradedDiagramAut.stageTopology Tdr C S) :=
  (isInducing_gradedTwistEquiv C S).eq_induced

/-- The exact old ordinary twist, with continuity of the old map and its old inverse. -/
def gradedTwistContinuousEquiv : GradedDiagramAut C S ≃ₜ* Cohomology.GradedDiagramAut Tdr C S where
  __ := gradedTwistEquiv C S
  continuous_toFun := (isInducing_gradedTwistEquiv C S).continuous
  continuous_invFun := ((gradedTwistEquiv C S).toEquiv.toHomeomorphOfIsInducing
    (isInducing_gradedTwistEquiv C S)).continuous_invFun

/-- The topological upgrade retains the exact old multiplicative equivalence. -/
theorem gradedTwistContinuousEquiv_toMulEquiv :
    (gradedTwistContinuousEquiv C S).toMulEquiv = gradedTwistEquiv C S := rfl

/-- The topological upgrade retains the exact old forward function. -/
theorem gradedTwistContinuousEquiv_coe :
    ⇑(gradedTwistContinuousEquiv C S) = gradedTwistEquiv C S := rfl

/-- Evaluation of the upgrade is exactly evaluation of the old twist. -/
theorem gradedTwistContinuousEquiv_apply (g : GradedDiagramAut C S) :
    gradedTwistContinuousEquiv C S g = gradedTwistEquiv C S g := rfl

/-- The inverse upgrade retains the exact old inverse function. -/
theorem gradedTwistContinuousEquiv_symm_coe :
    ⇑(gradedTwistContinuousEquiv C S).symm = (gradedTwistEquiv C S).symm := rfl

/-- Evaluation of the inverse upgrade is exactly evaluation of the old inverse twist. -/
theorem gradedTwistContinuousEquiv_symm_apply (g : Cohomology.GradedDiagramAut Tdr C S) :
    (gradedTwistContinuousEquiv C S).symm g = (gradedTwistEquiv C S).symm g := rfl

/-- Untwisting intertwines the whole actual stage with the whole ordinary action. -/
theorem gradedTwistContinuousEquiv_stage (g : GradedDiagramAut C S) (A : C.Stage)
    (z : Cohomology.diagonal Tdr ((Daff).complement A.val.val)) :
    diagonalUntwist ((Daff).complement A.val.val)
        ((gradedTwistContinuousEquiv C S g).stageEquiv A z) =
      g.stageEquiv A (diagonalUntwist ((Daff).complement A.val.val) z) :=
  gradedTwistEquiv_stage C S g A z

/-- Untwisting intertwines the one whole actual target with the original ordinary target. -/
theorem gradedTwistContinuousEquiv_target (g : GradedDiagramAut C S)
    (z : Cohomology.diagonal Tdr (Cohomology.schemeMarkingTarget Daff)) :
    diagonalUntwist (Cohomology.schemeMarkingTarget Daff)
        ((gradedTwistContinuousEquiv C S g).targetEquiv z) =
      g.targetEquiv (diagonalUntwist (Cohomology.schemeMarkingTarget Daff) z) :=
  gradedTwistEquiv_target C S g z

/-- The inverse twist recovers the whole ordinary stage action from the actual one. -/
theorem gradedTwistContinuousEquiv_symm_stage (g : Cohomology.GradedDiagramAut Tdr C S)
    (A : C.Stage) (z : Cohomology.diagonal Tdr ((Daff).complement A.val.val)) :
    ((gradedTwistContinuousEquiv C S).symm g).stageEquiv A
        (diagonalUntwist ((Daff).complement A.val.val) z) =
      diagonalUntwist ((Daff).complement A.val.val) (g.stageEquiv A z) :=
  gradedTwistEquiv_symm_stage C S g A z

/-- The inverse twist recovers the complete original ordinary target action. -/
theorem gradedTwistContinuousEquiv_symm_target (g : Cohomology.GradedDiagramAut Tdr C S)
    (z : Cohomology.diagonal Tdr (Cohomology.schemeMarkingTarget Daff)) :
    ((gradedTwistContinuousEquiv C S).symm g).targetEquiv
        (diagonalUntwist (Cohomology.schemeMarkingTarget Daff) z) =
      diagonalUntwist (Cohomology.schemeMarkingTarget Daff) (g.targetEquiv z) :=
  gradedTwistEquiv_symm_target C S g z

namespace DiagramAut

/-- The new ordinary quotient twist preserves the literal quotient topologies in both directions. -/
def scalarQuotientTwistContinuousEquiv :
    (DiagramAut C S ⧸ scalarSubgroup C S) ≃ₜ*
      (Cohomology.DiagramAut Tdr C S ⧸ Cohomology.DiagramAut.scalarSubgroup Tdr C S) where
  __ := scalarQuotientTwistEquiv C S
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut C S ↦
      scalarQuotientTwistEquiv C S (scalarQuotientMap C S g))
    simp only [scalarQuotientTwistEquiv_map]
    change Continuous (QuotientGroup.mk ∘ ⇑(quadraticTwistContinuousEquiv C S).toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (quadraticTwistContinuousEquiv C S).continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (Cohomology.DiagramAut.scalarSubgroup Tdr C S)).continuous_iff.mpr
    change Continuous (fun g : Cohomology.DiagramAut Tdr C S ↦
      (scalarQuotientTwistEquiv C S).symm (Cohomology.DiagramAut.scalarQuotientMap Tdr C S g))
    simp only [scalarQuotientTwistEquiv_symm_map]
    change Continuous (QuotientGroup.mk ∘ ⇑(quadraticTwistContinuousEquiv C S).symm.toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (quadraticTwistContinuousEquiv C S).symm.continuous

/-- The quotient upgrade retains exactly the new algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_toMulEquiv :
    (scalarQuotientTwistContinuousEquiv C S).toMulEquiv = scalarQuotientTwistEquiv C S := rfl

/-- The quotient upgrade retains the exact forward function. -/
theorem scalarQuotientTwistContinuousEquiv_coe :
    ⇑(scalarQuotientTwistContinuousEquiv C S) = scalarQuotientTwistEquiv C S := rfl

/-- The quotient upgrade evaluates by the exact algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_apply (q : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientTwistContinuousEquiv C S q = scalarQuotientTwistEquiv C S q := rfl

/-- The quotient upgrade retains the exact inverse function. -/
theorem scalarQuotientTwistContinuousEquiv_symm_coe :
    ⇑(scalarQuotientTwistContinuousEquiv C S).symm = (scalarQuotientTwistEquiv C S).symm := rfl

/-- The inverse quotient upgrade evaluates by the exact inverse algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_symm_apply
    (q : Cohomology.DiagramAut Tdr C S ⧸ Cohomology.DiagramAut.scalarSubgroup Tdr C S) :
    (scalarQuotientTwistContinuousEquiv C S).symm q = (scalarQuotientTwistEquiv C S).symm q := rfl

/-- Quotient representatives are sent through the exact old ordinary twist. -/
theorem scalarQuotientTwistContinuousEquiv_map (g : DiagramAut C S) :
    scalarQuotientTwistContinuousEquiv C S (scalarQuotientMap C S g) =
      Cohomology.DiagramAut.scalarQuotientMap Tdr C S (quadraticTwistEquiv C S g) :=
  scalarQuotientTwistEquiv_map C S g

/-- Inverse quotient representatives are sent through the exact old inverse twist. -/
theorem scalarQuotientTwistContinuousEquiv_symm_map (g : Cohomology.DiagramAut Tdr C S) :
    (scalarQuotientTwistContinuousEquiv C S).symm
        (Cohomology.DiagramAut.scalarQuotientMap Tdr C S g) =
      scalarQuotientMap C S ((quadraticTwistEquiv C S).symm g) :=
  scalarQuotientTwistEquiv_symm_map C S g

end DiagramAut

namespace GradedDiagramAut

/-- The new ordinary quotient twist preserves the literal quotient topologies in both directions. -/
def scalarQuotientTwistContinuousEquiv :
    (GradedDiagramAut C S ⧸ scalarSubgroup C S) ≃ₜ*
      (Cohomology.GradedDiagramAut Tdr C S ⧸ Cohomology.GradedDiagramAut.scalarSubgroup Tdr C
        S) where
  __ := scalarQuotientTwistEquiv C S
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut C S ↦
      scalarQuotientTwistEquiv C S (scalarQuotientMap C S g))
    simp only [scalarQuotientTwistEquiv_map]
    change Continuous (QuotientGroup.mk ∘ ⇑(gradedTwistContinuousEquiv C S).toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (gradedTwistContinuousEquiv C S).continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S)).continuous_iff.mpr
    change Continuous (fun g : Cohomology.GradedDiagramAut Tdr C S ↦
      (scalarQuotientTwistEquiv C S).symm (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S g))
    simp only [scalarQuotientTwistEquiv_symm_map]
    change Continuous (QuotientGroup.mk ∘ ⇑(gradedTwistContinuousEquiv C S).symm.toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (gradedTwistContinuousEquiv C S).symm.continuous

/-- The quotient upgrade retains exactly the new algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_toMulEquiv :
    (scalarQuotientTwistContinuousEquiv C S).toMulEquiv = scalarQuotientTwistEquiv C S := rfl

/-- The quotient upgrade retains the exact forward function. -/
theorem scalarQuotientTwistContinuousEquiv_coe :
    ⇑(scalarQuotientTwistContinuousEquiv C S) = scalarQuotientTwistEquiv C S := rfl

/-- The quotient upgrade evaluates by the exact algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_apply (q : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientTwistContinuousEquiv C S q = scalarQuotientTwistEquiv C S q := rfl

/-- The quotient upgrade retains the exact inverse function. -/
theorem scalarQuotientTwistContinuousEquiv_symm_coe :
    ⇑(scalarQuotientTwistContinuousEquiv C S).symm = (scalarQuotientTwistEquiv C S).symm := rfl

/-- The inverse quotient upgrade evaluates by the exact inverse algebraic quotient twist. -/
theorem scalarQuotientTwistContinuousEquiv_symm_apply
    (q : Cohomology.GradedDiagramAut Tdr C S ⧸ Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S) :
    (scalarQuotientTwistContinuousEquiv C S).symm q = (scalarQuotientTwistEquiv C S).symm q := rfl

/-- Quotient representatives are sent through the exact old ordinary twist. -/
theorem scalarQuotientTwistContinuousEquiv_map (g : GradedDiagramAut C S) :
    scalarQuotientTwistContinuousEquiv C S (scalarQuotientMap C S g) =
      Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S (gradedTwistEquiv C S g) :=
  scalarQuotientTwistEquiv_map C S g

/-- Inverse quotient representatives are sent through the exact old inverse twist. -/
theorem scalarQuotientTwistContinuousEquiv_symm_map (g : Cohomology.GradedDiagramAut Tdr C S) :
    (scalarQuotientTwistContinuousEquiv C S).symm
        (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S g) =
      scalarQuotientMap C S ((gradedTwistEquiv C S).symm g) :=
  scalarQuotientTwistEquiv_symm_map C S g

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
