/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Comparison
public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Restriction
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Raw cofinal restriction of actual cohomology diagrams

Literal stage selection on the existing actual diagrams is a topological embedding for
arbitrary commutative coefficients, markings and dimensions. The original common target
is retained. `DiagramAut.isEmbedding_restrictStages` and its graded counterpart follow
from the existing actual adapter square and pure cofinal embedding, not classification.

The new `restrictStagesScalarQuotient` homomorphisms use the literal Mathlib quotient map
of actual restriction. Uniform scalar action proves the required scalar-image equality;
continuity uses the quotient topology, without closedness or any lifting assertion.

Blueprint: the raw actual cofinal restriction clauses of T15 (`thm:t15`).
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

namespace DiagramAut

/-- The complete selected-stage-and-target kernel pulls back to its original actual stage.
-/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (restrictStages T C C' S hC) ⁻¹' (stageKernel T C' S A : Set _) =
      (stageKernel T C S (CofinalSystem.stageInclusion hC A) : Set _) := by
  ext g
  change restrictStages T C C' S hC g ∈ stageKernel T C' S A ↔
    g ∈ stageKernel T C S (CofinalSystem.stageInclusion hC A)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Literal restriction to a cofinal subsystem embeds the direct actual topology.
No classified inverse or field-extension hypothesis is used. -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages T C C' S hC) := by
  apply ((degreeOneDiagramContinuousEquiv T C' S).toHomeomorph.isEmbedding.of_comp_iff).mp
  change IsEmbedding (fun g ↦ degreeOneDiagramEquiv T C' S (restrictStages T C C' S hC g))
  simp only [degreeOneDiagramEquiv_restrictStages]
  have he := (HyperplaneGT.DiagramAut.isEmbedding_restrictStages R C C' S hC).comp
    (degreeOneDiagramContinuousEquiv T C S).toHomeomorph.isEmbedding
  change IsEmbedding (fun g ↦ HyperplaneGT.DiagramAut.restrictStages R C C' S hC
    (degreeOneDiagramContinuousEquiv T C S g)) at he
  simpa only [degreeOneDiagramContinuousEquiv_apply] using he

/-- Cofinality makes actual stage selection injective, including its common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).injective

/-- The topology is induced by actual cofinal restriction, without assuming surjectivity. -/
theorem isInducing_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsInducing (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).isInducing

/-- The direct actual topology equals the topology induced by the literal restriction. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology T C S = TopologicalSpace.induced (restrictStages T C C' S hC)
      (stageTopology T C' S) :=
  (isInducing_restrictStages T C C' S hC).eq_induced

/-- Stage selection is continuous for the directly defined actual topologies. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).continuous

/-- Continuity into an actual diagram is tested after its literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type x} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → DiagramAut T C S) :
    Continuous f ↔ Continuous (restrictStages T C C' S hC ∘ f) :=
  (isEmbedding_restrictStages T C C' S hC).continuous_iff

/-- Any actual inverse of literal restriction is continuous; existence is not assumed. -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : DiagramAut T C' S → DiagramAut T C S)
    (hf : Function.RightInverse f (restrictStages T C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp T C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

/-- Uniform scalar action restricts to the same unit on the selected stages and target. -/
theorem restrictStages_scalarQuadraticAction (hC : C'.stages ⊆ C.stages) (a : Rˣ) :
    restrictStages T C C' S hC (scalarQuadraticAction T C S a) =
      scalarQuadraticAction T C' S a := by
  apply (degreeOneDiagramEquiv T C' S).injective
  simp only [degreeOneDiagramEquiv_restrictStages, degreeOneDiagramEquiv_scalarQuadraticAction,
    HyperplaneGT.scalarQuadraticAction_apply,
    HyperplaneGT.DiagramAut.restrictStages_scalarQuadraticAut]

/-- The whole actual scalar range maps onto the subsystem's literal scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup T C S).map (restrictStages T C C' S hC) =
      scalarSubgroup T C' S := by
  ext g
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarQuadraticAction T C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarQuadraticAction T C S a, ⟨a, rfl⟩,
      restrictStages_scalarQuadraticAction T C C' S hC a⟩

/-- The new actual quotient homomorphism is Mathlib's quotient map of literal restriction.
-/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (DiagramAut T C S ⧸ scalarSubgroup T C S) →*
      (DiagramAut T C' S ⧸ scalarSubgroup T C' S) :=
  QuotientGroup.map (scalarSubgroup T C S) (scalarSubgroup T C' S)
    (restrictStages T C C' S hC)
    ((map_scalarSubgroup_restrictStages T C C' S hC) ▸
      (scalarSubgroup T C S).le_comap_map (restrictStages T C C' S hC))

/-- A representative restricts through the existing actual stage selection map. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut T C S) :
    restrictStagesScalarQuotient T C C' S hC (scalarQuotientMap T C S g) =
      scalarQuotientMap T C' S (restrictStages T C C' S hC g) := rfl

/-- Actual scalar-quotient restriction is continuous for the literal quotient topologies,
without any classification, closedness or field-extension assumption. -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient T C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup T C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages T C C' S hC))

end DiagramAut

namespace GradedDiagramAut

/-- The complete selected-stage-and-target kernel pulls back to its original actual stage.
-/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (restrictStages T C C' S hC) ⁻¹' (stageKernel T C' S A : Set _) =
      (stageKernel T C S (CofinalSystem.stageInclusion hC A) : Set _) := by
  ext g
  change restrictStages T C C' S hC g ∈ stageKernel T C' S A ↔
    g ∈ stageKernel T C S (CofinalSystem.stageInclusion hC A)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Literal restriction to a cofinal subsystem embeds the direct actual topology.
No classified inverse or field-extension hypothesis is used. -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages T C C' S hC) := by
  apply ((gradedDiagramContinuousEquiv T C' S).toHomeomorph.isEmbedding.of_comp_iff).mp
  change IsEmbedding (fun g ↦ gradedDiagramEquiv T C' S (restrictStages T C C' S hC g))
  simp only [gradedDiagramEquiv_restrictStages]
  have he := (HyperplaneGT.GradedDiagramAut.isEmbedding_restrictStages R C C' S hC).comp
    (gradedDiagramContinuousEquiv T C S).toHomeomorph.isEmbedding
  change IsEmbedding (fun g ↦ HyperplaneGT.GradedDiagramAut.restrictStages R C C' S hC
    (gradedDiagramContinuousEquiv T C S g)) at he
  simpa only [gradedDiagramContinuousEquiv_apply] using he

/-- Cofinality makes actual stage selection injective, including its common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).injective

/-- The topology is induced by actual cofinal restriction, without assuming surjectivity. -/
theorem isInducing_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsInducing (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).isInducing

/-- The direct actual topology equals the topology induced by the literal restriction. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology T C S = TopologicalSpace.induced (restrictStages T C C' S hC)
      (stageTopology T C' S) :=
  (isInducing_restrictStages T C C' S hC).eq_induced

/-- Stage selection is continuous for the directly defined actual topologies. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages T C C' S hC) :=
  (isEmbedding_restrictStages T C C' S hC).continuous

/-- Continuity into an actual diagram is tested after its literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type x} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → GradedDiagramAut T C S) :
    Continuous f ↔ Continuous (restrictStages T C C' S hC ∘ f) :=
  (isEmbedding_restrictStages T C C' S hC).continuous_iff

/-- Any actual inverse of literal restriction is continuous; existence is not assumed. -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : GradedDiagramAut T C' S → GradedDiagramAut T C S)
    (hf : Function.RightInverse f (restrictStages T C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp T C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

/-- Uniform scalar action restricts to the same unit on the selected stages and target. -/
theorem restrictStages_scalarGradedAction (hC : C'.stages ⊆ C.stages) (a : Rˣ) :
    restrictStages T C C' S hC (scalarGradedAction T C S a) =
      scalarGradedAction T C' S a := by
  apply (gradedDiagramEquiv T C' S).injective
  simp only [gradedDiagramEquiv_restrictStages, gradedDiagramEquiv_scalarGradedAction,
    HyperplaneGT.scalarGradedAction_apply,
    HyperplaneGT.GradedDiagramAut.restrictStages_scalarGradedAut]

/-- The whole actual scalar range maps onto the subsystem's literal scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup T C S).map (restrictStages T C C' S hC) =
      scalarSubgroup T C' S := by
  ext g
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarGradedAction T C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAction T C S a, ⟨a, rfl⟩,
      restrictStages_scalarGradedAction T C C' S hC a⟩

/-- The new actual quotient homomorphism is Mathlib's quotient map of literal restriction.
-/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (GradedDiagramAut T C S ⧸ scalarSubgroup T C S) →*
      (GradedDiagramAut T C' S ⧸ scalarSubgroup T C' S) :=
  QuotientGroup.map (scalarSubgroup T C S) (scalarSubgroup T C' S)
    (restrictStages T C C' S hC)
    ((map_scalarSubgroup_restrictStages T C C' S hC) ▸
      (scalarSubgroup T C S).le_comap_map (restrictStages T C C' S hC))

/-- A representative restricts through the existing actual stage selection map. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut T C S) :
    restrictStagesScalarQuotient T C C' S hC (scalarQuotientMap T C S g) =
      scalarQuotientMap T C' S (restrictStages T C C' S hC g) := rfl

/-- Actual scalar-quotient restriction is continuous for the literal quotient topologies,
without any classification, closedness or field-extension assumption. -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient T C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup T C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages T C C' S hC))

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology
