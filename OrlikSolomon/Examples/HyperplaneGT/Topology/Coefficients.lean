/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Diagram
public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import Mathlib.FieldTheory.KrullTopology

/-!
# Coefficients and the common target in finite-stage topology

The binary dimension-zero fixture has identity at every stage and a nonidentity common
target. The stage-and-target neighborhood basis excludes this automorphism, so a topology
that silently discarded the target would fail this consumer. Over the zero coefficient
ring, both actual pure diagram kernel families are the full subgroups.

Blueprint: coefficient and dimension-zero consumers for T01 (`def:t01`) and T02 (`lem:t02`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.TopologyExamples

open Filter Topology DiagramExamples
open scoped FiniteStageTopology

/-- All stage components of the binary dimension-zero fixture are identity. The common
component is still nontrivial, even though no markings exist in that dimension. -/
theorem binary_zeroDimension_all_stages :
    (∀ 𝒜 : (binarySystem 0).Stage,
      (zeroDimensionSwap (ZMod 2)).stageEquiv 𝒜 = 1) ∧
      zeroDimensionSwap (ZMod 2) ≠ 1 :=
  ⟨fun 𝒜 ↦ zeroDimensionSwap_stage (ZMod 2) 𝒜, zeroDimensionSwap_ne_one⟩

/-- A genuine identity neighborhood excludes a nonidentity target swap even when it acts as
identity at every selected stage. In particular the target test cannot be removed. -/
theorem binary_zeroDimension_target_neighborhood (𝒜 : (binarySystem 0).Stage) :
    (DiagramAut.stageKernel (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2)) 𝒜 : Set _) ∈
        𝓝 (1 : DiagramAut (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2))) ∧
      zeroDimensionSwap (ZMod 2) ∉
        DiagramAut.stageKernel (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2)) 𝒜 := by
  refine ⟨(DiagramAut.nhds_one_stageBasis _ _ _).mem_of_mem trivial, ?_⟩
  intro hmem
  have ht := (DiagramAut.mem_stageKernel _ _ _ _ _).mp hmem |>.2
  apply zeroDimensionSwap_ne_one
  exact DiagramAut.ext (fun ℬ ↦ zeroDimensionSwap_stage (ZMod 2) ℬ) ht

/-- Both pure kernel families retain the zero coefficient ring and its original carriers. -/
theorem zeroRing_stageKernels (𝒜 : (binarySystem 1).Stage) :
    DiagramAut.stageKernel (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2)) 𝒜 = ⊤ ∧
      GradedDiagramAut.stageKernel (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2)) 𝒜 = ⊤ := by
  constructor
  · apply top_unique
    intro g _
    rw [zeroRing_aut_eq_one g]
    exact Subgroup.one_mem _
  · apply top_unique
    intro g _
    rw [zeroRing_graded_aut_eq_one g]
    exact Subgroup.one_mem _

/-- Opening the finite-stage scope does not replace the existing global Galois topology. -/
theorem finiteStageScope_krull (k₀ k : Type*) [Field k₀] [Field k] [Algebra k₀ k] :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

end OrlikSolomon.HyperplaneGT.TopologyExamples
