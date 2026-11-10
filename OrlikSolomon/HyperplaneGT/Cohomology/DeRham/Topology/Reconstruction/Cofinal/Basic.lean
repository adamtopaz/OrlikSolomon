/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Basic

/-!
# Raw ordinary cofinal restriction and scalar quotient maps

The literal ordinary stage-selection maps are topological embeddings for the direct
finite-stage topologies in every dimension, retaining the one whole original target.
Their scalar-image equality gives honest new Mathlib quotient homomorphisms, continuous
for the literal quotient topologies without classified inverse or closedness assumptions.

This size-only leaf uses the already proved actual restriction and exact old ordinary
comparison squares. It introduces no new family, carrier, topology or instance.
Blueprint: raw cofinal clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v x

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

namespace DiagramAut

/-- The complete selected ordinary stage-and-target kernel pulls back to the same stage. -/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (restrictStages C C' S hC) ⁻¹' (stageKernel C' S A : Set _) =
      (stageKernel C S (CofinalSystem.stageInclusion hC A) : Set _) := by
  ext g
  change restrictStages C C' S hC g ∈ stageKernel C' S A ↔
    g ∈ stageKernel C S (CofinalSystem.stageInclusion hC A)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Literal ordinary cofinal restriction embeds the directly defined topology in all dimensions. -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages C C' S hC) := by
  apply ((quadraticTwistContinuousEquiv C' S).toHomeomorph.isEmbedding.of_comp_iff).mp
  change IsEmbedding (fun g ↦ quadraticTwistEquiv C' S (restrictStages C C' S hC g))
  simp only [quadraticTwistEquiv_restrictStages]
  have he := (Cohomology.DiagramAut.isEmbedding_restrictStages Tdr C C' S hC).comp
    (quadraticTwistContinuousEquiv C S).toHomeomorph.isEmbedding
  change IsEmbedding (fun g ↦ Cohomology.DiagramAut.restrictStages Tdr C C' S hC
    (quadraticTwistEquiv C S g)) at he
  exact he

/-- Cofinality makes the ordinary stage selection injective, including its common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages C C' S hC) :=
  (isEmbedding_restrictStages C C' S hC).injective

/-- The direct topology is induced by the literal ordinary cofinal map. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology C S = TopologicalSpace.induced (restrictStages C C' S hC)
      (stageTopology C' S) := (isEmbedding_restrictStages C C' S hC).isInducing.eq_induced

/-- The old ordinary stage selection is continuous without any classification hypothesis. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages C C' S hC) :=
  (isEmbedding_restrictStages C C' S hC).continuous

/-- Continuity into an ordinary group is tested after literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type x} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → DiagramAut C S) :
    Continuous f ↔ Continuous (restrictStages C C' S hC ∘ f) :=
  (isEmbedding_restrictStages C C' S hC).continuous_iff

/-- Any right inverse of ordinary cofinal restriction is continuous. -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : DiagramAut C' S → DiagramAut C S)
    (hf : Function.RightInverse f (restrictStages C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

/-- Uniform ordinary scalar action restricts to the same unit at all selected stages and target. -/
theorem restrictStages_scalarQuadraticAction (hC : C'.stages ⊆ C.stages) (a : kˣ) :
    restrictStages C C' S hC (scalarQuadraticAction C S a) = scalarQuadraticAction C' S a := by
  apply (quadraticTwistEquiv C' S).injective
  exact (quadraticTwistEquiv_restrictStages C C' S hC (scalarQuadraticAction C S a)).trans
    ((congrArg (Cohomology.DiagramAut.restrictStages Tdr C C' S hC)
      (quadraticTwistEquiv_scalarQuadraticAction C S a)).trans
        ((Cohomology.DiagramAut.restrictStages_scalarQuadraticAction Tdr C C' S hC a).trans
          (quadraticTwistEquiv_scalarQuadraticAction C' S a).symm))

/-- The entire original scalar range maps onto the subsystem's scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup C S).map (restrictStages C C' S hC) = scalarSubgroup C' S := by
  ext g
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarQuadraticAction C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarQuadraticAction C S a, ⟨a, rfl⟩,
      restrictStages_scalarQuadraticAction C C' S hC a⟩

/-- The new ordinary scalar quotient homomorphism is Mathlib's map of literal stage selection. -/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (DiagramAut C S ⧸ scalarSubgroup C S) →* (DiagramAut C' S ⧸ scalarSubgroup C' S) :=
  QuotientGroup.map (scalarSubgroup C S) (scalarSubgroup C' S) (restrictStages C C' S hC)
    ((map_scalarSubgroup_restrictStages C C' S hC) ▸
      (scalarSubgroup C S).le_comap_map (restrictStages C C' S hC))

/-- Ordinary quotient representatives select the same old stages and whole target. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages) (g : DiagramAut C S) :
    restrictStagesScalarQuotient C C' S hC (scalarQuotientMap C S g) =
      scalarQuotientMap C' S (restrictStages C C' S hC g) := rfl

/-- The new ordinary quotient homomorphism is continuous for the literal quotient topologies. -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages C C' S hC))

/-- Raw quotient stage selection commutes with the exact ordinary quotient twists. -/
theorem restrictStagesScalarQuotient_comparison (hC : C'.stages ⊆ C.stages)
    (z : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientTwistEquiv C' S (restrictStagesScalarQuotient C C' S hC z) =
      Cohomology.DiagramAut.restrictStagesScalarQuotient Tdr C C' S hC
        (scalarQuotientTwistEquiv C S z) := by
  have he : (scalarQuotientTwistEquiv C' S).toMonoidHom.comp
      (restrictStagesScalarQuotient C C' S hC) =
        (Cohomology.DiagramAut.restrictStagesScalarQuotient Tdr C C' S hC).comp
          (scalarQuotientTwistEquiv C S).toMonoidHom := by
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro g
    change scalarQuotientTwistEquiv C' S
      (restrictStagesScalarQuotient C C' S hC (scalarQuotientMap C S g)) = _
    exact (scalarQuotientTwistEquiv_map C' S (restrictStages C C' S hC g)).trans
      ((congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C' S)
        (quadraticTwistEquiv_restrictStages C C' S hC g)).trans
          ((Cohomology.DiagramAut.restrictStagesScalarQuotient_map Tdr C C' S hC
            (quadraticTwistEquiv C S g)).symm.trans
              (congrArg (Cohomology.DiagramAut.restrictStagesScalarQuotient Tdr C C' S hC)
                (scalarQuotientTwistEquiv_map C S g).symm)))
  exact DFunLike.congr_fun he z

end DiagramAut

namespace GradedDiagramAut

/-- The complete selected ordinary stage-and-target kernel pulls back to the same stage. -/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (restrictStages C C' S hC) ⁻¹' (stageKernel C' S A : Set _) =
      (stageKernel C S (CofinalSystem.stageInclusion hC A) : Set _) := by
  ext g
  change restrictStages C C' S hC g ∈ stageKernel C' S A ↔
    g ∈ stageKernel C S (CofinalSystem.stageInclusion hC A)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Literal ordinary cofinal restriction embeds the directly defined topology in all dimensions. -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages C C' S hC) := by
  apply ((gradedTwistContinuousEquiv C' S).toHomeomorph.isEmbedding.of_comp_iff).mp
  change IsEmbedding (fun g ↦ gradedTwistEquiv C' S (restrictStages C C' S hC g))
  simp only [gradedTwistEquiv_restrictStages]
  have he := (Cohomology.GradedDiagramAut.isEmbedding_restrictStages Tdr C C' S hC).comp
    (gradedTwistContinuousEquiv C S).toHomeomorph.isEmbedding
  change IsEmbedding (fun g ↦ Cohomology.GradedDiagramAut.restrictStages Tdr C C' S hC
    (gradedTwistEquiv C S g)) at he
  exact he

/-- Cofinality makes the ordinary stage selection injective, including its common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages C C' S hC) :=
  (isEmbedding_restrictStages C C' S hC).injective

/-- The direct topology is induced by the literal ordinary cofinal map. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology C S = TopologicalSpace.induced (restrictStages C C' S hC)
      (stageTopology C' S) := (isEmbedding_restrictStages C C' S hC).isInducing.eq_induced

/-- The old ordinary stage selection is continuous without any classification hypothesis. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages C C' S hC) :=
  (isEmbedding_restrictStages C C' S hC).continuous

/-- Continuity into an ordinary group is tested after literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type x} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → GradedDiagramAut C S) :
    Continuous f ↔ Continuous (restrictStages C C' S hC ∘ f) :=
  (isEmbedding_restrictStages C C' S hC).continuous_iff

/-- Any right inverse of ordinary cofinal restriction is continuous. -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : GradedDiagramAut C' S → GradedDiagramAut C S)
    (hf : Function.RightInverse f (restrictStages C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

/-- Uniform ordinary scalar action restricts to the same unit at all selected stages and target. -/
theorem restrictStages_scalarGradedAction (hC : C'.stages ⊆ C.stages) (a : kˣ) :
    restrictStages C C' S hC (scalarGradedAction C S a) = scalarGradedAction C' S a := by
  apply (gradedTwistEquiv C' S).injective
  exact (gradedTwistEquiv_restrictStages C C' S hC (scalarGradedAction C S a)).trans
    ((congrArg (Cohomology.GradedDiagramAut.restrictStages Tdr C C' S hC)
      (gradedTwistEquiv_scalarGradedAction C S a)).trans
        ((Cohomology.GradedDiagramAut.restrictStages_scalarGradedAction Tdr C C' S hC a).trans
          (gradedTwistEquiv_scalarGradedAction C' S a).symm))

/-- The entire original scalar range maps onto the subsystem's scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup C S).map (restrictStages C C' S hC) = scalarSubgroup C' S := by
  ext g
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarGradedAction C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAction C S a, ⟨a, rfl⟩,
      restrictStages_scalarGradedAction C C' S hC a⟩

/-- The new ordinary scalar quotient homomorphism is Mathlib's map of literal stage selection. -/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (GradedDiagramAut C S ⧸ scalarSubgroup C S) →* (GradedDiagramAut C' S ⧸ scalarSubgroup C' S) :=
  QuotientGroup.map (scalarSubgroup C S) (scalarSubgroup C' S) (restrictStages C C' S hC)
    ((map_scalarSubgroup_restrictStages C C' S hC) ▸
      (scalarSubgroup C S).le_comap_map (restrictStages C C' S hC))

/-- Ordinary quotient representatives select the same old stages and whole target. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages) (g : GradedDiagramAut C S) :
    restrictStagesScalarQuotient C C' S hC (scalarQuotientMap C S g) =
      scalarQuotientMap C' S (restrictStages C C' S hC g) := rfl

/-- The new ordinary quotient homomorphism is continuous for the literal quotient topologies. -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages C C' S hC))

/-- Raw quotient stage selection commutes with the exact ordinary quotient twists. -/
theorem restrictStagesScalarQuotient_comparison (hC : C'.stages ⊆ C.stages)
    (z : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientTwistEquiv C' S (restrictStagesScalarQuotient C C' S hC z) =
      Cohomology.GradedDiagramAut.restrictStagesScalarQuotient Tdr C C' S hC
        (scalarQuotientTwistEquiv C S z) := by
  have he : (scalarQuotientTwistEquiv C' S).toMonoidHom.comp
      (restrictStagesScalarQuotient C C' S hC) =
        (Cohomology.GradedDiagramAut.restrictStagesScalarQuotient Tdr C C' S hC).comp
          (scalarQuotientTwistEquiv C S).toMonoidHom := by
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro g
    change scalarQuotientTwistEquiv C' S
      (restrictStagesScalarQuotient C C' S hC (scalarQuotientMap C S g)) = _
    exact (scalarQuotientTwistEquiv_map C' S (restrictStages C C' S hC g)).trans
      ((congrArg (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C' S)
        (gradedTwistEquiv_restrictStages C C' S hC g)).trans
          ((Cohomology.GradedDiagramAut.restrictStagesScalarQuotient_map Tdr C C' S hC
            (gradedTwistEquiv C S g)).symm.trans
              (congrArg (Cohomology.GradedDiagramAut.restrictStagesScalarQuotient Tdr C C' S hC)
                (scalarQuotientTwistEquiv_map C S g).symm)))
  exact DFunLike.congr_fun he z

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
