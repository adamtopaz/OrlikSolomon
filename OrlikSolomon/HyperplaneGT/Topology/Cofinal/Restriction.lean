/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Cofinal
public import OrlikSolomon.HyperplaneGT.Topology.Restriction
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Literal restriction to selected cofinal stages

Literal stage restriction retains the original common target. Over arbitrary commutative
coefficients and in every dimension it is a topological embedding: a selected subsystem
stage above an old finite arrangement controls agreement on the old stage. This proves
inverse continuity whenever an actual inverse exists, without asserting arbitrary extension.

The local and domain classified equivalences adjoin continuity to the exact existing M8
maps. No field-extension hypothesis, union-closure or transported topology is used.
Public expansions are plain rewrites so ordinary inverse cancellation remains available.

Blueprint: T12 (`thm:t12`).
-/

@[expose] public section

noncomputable section

universe u v r w

namespace OrlikSolomon.HyperplaneGT

open Filter Topology
open scoped FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R]
  (C C' : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- The complete stage-and-target kernel pulls back to the indicated original stage. -/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (B : C'.Stage) :
    (restrictStages R C C' S hC) ⁻¹' (stageKernel R C' S B : Set _) =
      (stageKernel R C S (CofinalSystem.stageInclusion hC B) : Set _) := by
  ext g
  change restrictStages R C C' S hC g ∈ stageKernel R C' S B ↔
    g ∈ stageKernel R C S (CofinalSystem.stageInclusion hC B)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Cofinality makes literal restriction faithful, including the unchanged common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages R C C' S hC) := by
  intro g h he
  apply DiagramAut.ext
  · intro A
    obtain ⟨B, hAB⟩ := C'.exists_ge_arrangement A.val.val
    apply stageEquiv_eq_of_le (ℬ := CofinalSystem.stageInclusion hC B) hAB
    exact congrArg (fun f : DiagramAut R C' S ↦ f.stageEquiv B) he
  · exact congrArg (fun f : DiagramAut R C' S ↦ f.targetEquiv) he

/-- The direct topology is induced by literal restriction to a cofinal subsystem.
No inverse or classification is assumed. Blueprint: T12 (`thm:t12`). -/
theorem isInducing_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsInducing (restrictStages R C C' S hC) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply le_antisymm
  · apply ((nhds_one_stageBasis R C S).le_basis_iff
      ((nhds_one_stageBasis R C' S).comap (restrictStages R C C' S hC))).mpr
    intro B _
    refine ⟨CofinalSystem.stageInclusion hC B, trivial, ?_⟩
    rw [preimage_stageKernel_restrictStages]
  · apply (((nhds_one_stageBasis R C' S).comap
      (restrictStages R C C' S hC)).le_basis_iff (nhds_one_stageBasis R C S)).mpr
    intro A _
    obtain ⟨B, hAB⟩ := C'.exists_ge_arrangement A.val.val
    refine ⟨B, trivial, ?_⟩
    rw [preimage_stageKernel_restrictStages]
    exact stageKernel_antitone R C S hAB

/-- The named original topology equals the topology induced by the existing restriction. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology R C S =
      TopologicalSpace.induced (restrictStages R C C' S hC) (stageTopology R C' S) :=
  (isInducing_restrictStages R C C' S hC).eq_induced

/-- Literal cofinal restriction is a topological embedding for arbitrary coefficients
and every dimension. Blueprint: T12 (`thm:t12`). -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages R C C' S hC) :=
  ⟨isInducing_restrictStages R C C' S hC, restrictStages_injective R C C' S hC⟩

/-- Stage selection and the unchanged common target give a continuous group homomorphism. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages R C C' S hC) :=
  (isEmbedding_restrictStages R C C' S hC).continuous

/-- Continuity into the original diagram can be tested after literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type w} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → DiagramAut R C S) :
    Continuous f ↔ Continuous (restrictStages R C C' S hC ∘ f) :=
  (isEmbedding_restrictStages R C C' S hC).continuous_iff

/-- Every actual inverse of literal cofinal restriction is continuous. Existence of such
an inverse is not concluded from cofinality. Blueprint: T12 (`thm:t12`). -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : DiagramAut R C' S → DiagramAut R C S)
    (hf : Function.RightInverse f (restrictStages R C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp R C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

end DiagramAut

namespace GradedDiagramAut

/-- The complete stage-and-target kernel pulls back to the indicated original stage. -/
theorem preimage_stageKernel_restrictStages (hC : C'.stages ⊆ C.stages) (B : C'.Stage) :
    (restrictStages R C C' S hC) ⁻¹' (stageKernel R C' S B : Set _) =
      (stageKernel R C S (CofinalSystem.stageInclusion hC B) : Set _) := by
  ext g
  change restrictStages R C C' S hC g ∈ stageKernel R C' S B ↔
    g ∈ stageKernel R C S (CofinalSystem.stageInclusion hC B)
  simp only [mem_stageKernel, restrictStages_stageEquiv, restrictStages_targetEquiv]
  rfl

/-- Cofinality makes literal restriction faithful, including the unchanged common target. -/
theorem restrictStages_injective (hC : C'.stages ⊆ C.stages) :
    Function.Injective (restrictStages R C C' S hC) := by
  intro g h he
  apply GradedDiagramAut.ext
  · intro A
    obtain ⟨B, hAB⟩ := C'.exists_ge_arrangement A.val.val
    apply stageEquiv_eq_of_le (ℬ := CofinalSystem.stageInclusion hC B) hAB
    exact congrArg (fun f : GradedDiagramAut R C' S ↦ f.stageEquiv B) he
  · exact congrArg (fun f : GradedDiagramAut R C' S ↦ f.targetEquiv) he

/-- The direct topology is induced by literal restriction to a cofinal subsystem.
No inverse or classification is assumed. Blueprint: T12 (`thm:t12`). -/
theorem isInducing_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsInducing (restrictStages R C C' S hC) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply le_antisymm
  · apply ((nhds_one_stageBasis R C S).le_basis_iff
      ((nhds_one_stageBasis R C' S).comap (restrictStages R C C' S hC))).mpr
    intro B _
    refine ⟨CofinalSystem.stageInclusion hC B, trivial, ?_⟩
    rw [preimage_stageKernel_restrictStages]
  · apply (((nhds_one_stageBasis R C' S).comap
      (restrictStages R C C' S hC)).le_basis_iff (nhds_one_stageBasis R C S)).mpr
    intro A _
    obtain ⟨B, hAB⟩ := C'.exists_ge_arrangement A.val.val
    refine ⟨B, trivial, ?_⟩
    rw [preimage_stageKernel_restrictStages]
    exact stageKernel_antitone R C S hAB

/-- The named original topology equals the topology induced by the existing restriction. -/
theorem stageTopology_eq_induced_restrictStages (hC : C'.stages ⊆ C.stages) :
    stageTopology R C S =
      TopologicalSpace.induced (restrictStages R C C' S hC) (stageTopology R C' S) :=
  (isInducing_restrictStages R C C' S hC).eq_induced

/-- Literal cofinal restriction is a topological embedding for arbitrary coefficients
and every dimension. Blueprint: T12 (`thm:t12`). -/
theorem isEmbedding_restrictStages (hC : C'.stages ⊆ C.stages) :
    IsEmbedding (restrictStages R C C' S hC) :=
  ⟨isInducing_restrictStages R C C' S hC, restrictStages_injective R C C' S hC⟩

/-- Stage selection and the unchanged common target give a continuous group homomorphism. -/
theorem continuous_restrictStages (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStages R C C' S hC) :=
  (isEmbedding_restrictStages R C C' S hC).continuous

/-- Continuity into the original diagram can be tested after literal cofinal restriction. -/
theorem continuous_iff_restrictStages_comp {X : Type w} [TopologicalSpace X]
    (hC : C'.stages ⊆ C.stages) (f : X → GradedDiagramAut R C S) :
    Continuous f ↔ Continuous (restrictStages R C C' S hC ∘ f) :=
  (isEmbedding_restrictStages R C C' S hC).continuous_iff

/-- Every actual inverse of literal cofinal restriction is continuous. Existence of such
an inverse is not concluded from cofinality. Blueprint: T12 (`thm:t12`). -/
theorem continuous_inverse_restrictStages (hC : C'.stages ⊆ C.stages)
    (f : GradedDiagramAut R C' S → GradedDiagramAut R C S)
    (hf : Function.RightInverse f (restrictStages R C C' S hC)) : Continuous f := by
  apply (continuous_iff_restrictStages_comp R C C' S hC f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

end GradedDiagramAut

/-- The union of two selected stage families, without assuming either is union-closed. -/
def CofinalSystem.unionStages : CofinalSystem k₀ k n where
  stages := C.stages ∪ C'.stages
  cofinal s := by
    obtain ⟨A, hA, hs⟩ := C.cofinal s
    exact ⟨A, Or.inl hA, hs⟩

/-- The selected family is literally the union of the two original families. -/
theorem CofinalSystem.unionStages_stages :
    (C.unionStages C').stages = C.stages ∪ C'.stages := rfl

/-- The first supplied family is a subsystem of the union family. -/
theorem CofinalSystem.stages_subset_unionStages_left :
    C.stages ⊆ (C.unionStages C').stages := Set.subset_union_left

/-- The second supplied family is a subsystem of the union family. -/
theorem CofinalSystem.stages_subset_unionStages_right :
    C'.stages ⊆ (C.unionStages C').stages := Set.subset_union_right

/-- The exact existing classified cofinal restriction, with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T12 (`thm:t12`). -/
def cofinalRestrictionContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S) (DiagramAut.stageTopology R C S)
      (DiagramAut R C' S) (DiagramAut.stageTopology R C' S) _ _ where
  toMulEquiv := cofinalRestrictionEquiv R C C' S hC hS hgen hn
  continuous_toFun := (DiagramAut.continuous_restrictStages R C C' S hC).congr
    (fun g ↦ (cofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g).symm)
  continuous_invFun := DiagramAut.continuous_inverse_restrictStages R C C' S hC _
    (cofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn)

/-- Forgetting continuity recovers exactly the original M8 equivalence. -/
theorem cofinalRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      cofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The underlying function is the existing classified restriction. -/
theorem cofinalRestrictionContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn : DiagramAut R C S → DiagramAut R
      C' S) = cofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The forward map selects the literal subsystem stages and retains the target. -/
theorem cofinalRestrictionContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g = DiagramAut.restrictStages R C C'
      S hC g :=
  cofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g

/-- The inverse is exactly the old classified extension, with the same coordinates. -/
theorem cofinalRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g = (cofinalRestrictionEquiv
      R C C' S hC hS hgen hn).symm g := rfl

/-- Each subsystem stage is the unchanged original stage component. -/
theorem cofinalRestrictionContinuousEquiv_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) (B : C'.Stage) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).stageEquiv B =
      g.stageEquiv (CofinalSystem.stageInclusion hC B) := by
  rw [cofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_stageEquiv]

/-- Literal cofinal restriction retains the single original target. -/
theorem cofinalRestrictionContinuousEquiv_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv := by
  rw [cofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_targetEquiv]

/-- The classified extension has the given component at every selected subsystem stage. -/
theorem cofinalRestrictionContinuousEquiv_symm_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) (B : C'.Stage) :
    ((cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC B) =
      g.stageEquiv B :=
  congrArg (fun f : DiagramAut R C' S ↦ f.stageEquiv B)
    (cofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- The inverse retains precisely the given original common target. -/
theorem cofinalRestrictionContinuousEquiv_symm_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    ((cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv :=
  congrArg (fun f : DiagramAut R C' S ↦ f.targetEquiv)
    (cofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- Restriction preserves the same primal scalar and field-automorphism coordinates. -/
theorem cofinalRestrictionContinuousEquiv_classification [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn (quadraticAutEquiv R C S hS hgen hn
      p) =
      quadraticAutEquiv R C' S hS hgen hn p :=
  cofinalRestrictionEquiv_classification R C C' S hC hS hgen hn p

/-- Restricting to the same selected family is the identity topological equivalence. -/
theorem cofinalRestrictionContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut R C S) := by
  apply DFunLike.ext
  intro g
  rw [cofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose as literal stage selections. -/
theorem cofinalRestrictionContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
        (cofinalRestrictionContinuousEquiv R C' C'' S hC' hS hgen hn) =
      cofinalRestrictionContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, cofinalRestrictionContinuousEquiv_apply]
  exact DiagramAut.restrictStages_trans R C C' S C'' hC hC' g

/-- The exact existing classified cofinal restriction, with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T12 (`thm:t12`). -/
def gradedCofinalRestrictionContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S)
      (GradedDiagramAut R C' S) (GradedDiagramAut.stageTopology R C' S) _ _ where
  toMulEquiv := gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
  continuous_toFun := (GradedDiagramAut.continuous_restrictStages R C C' S hC).congr
    (fun g ↦ (gradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g).symm)
  continuous_invFun := GradedDiagramAut.continuous_inverse_restrictStages R C C' S hC _
    (gradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn)

/-- Forgetting continuity recovers exactly the original M8 equivalence. -/
theorem gradedCofinalRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The underlying function is the existing classified restriction. -/
theorem gradedCofinalRestrictionContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn : GradedDiagramAut R C S →
      GradedDiagramAut R C' S) = gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The forward map selects the literal subsystem stages and retains the target. -/
theorem gradedCofinalRestrictionContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages R C C' S hC g :=
  gradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g

/-- The inverse is exactly the old classified extension, with the same coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g =
      (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g := rfl

/-- Each subsystem stage is the unchanged original stage component. -/
theorem gradedCofinalRestrictionContinuousEquiv_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) (B : C'.Stage) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).stageEquiv B =
      g.stageEquiv (CofinalSystem.stageInclusion hC B) := by
  rw [gradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_stageEquiv]

/-- Literal cofinal restriction retains the single original target. -/
theorem gradedCofinalRestrictionContinuousEquiv_targetEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).targetEquiv =
      g.targetEquiv := by
  rw [gradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_targetEquiv]

/-- The classified extension has the given component at every selected subsystem stage. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) (B : C'.Stage) :
    ((gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC B) =
      g.stageEquiv B :=
  congrArg (fun f : GradedDiagramAut R C' S ↦ f.stageEquiv B)
    (gradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- The inverse retains precisely the given original common target. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsLocalRing R] (hC : C'.stages
    ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    ((gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv :=
  congrArg (fun f : GradedDiagramAut R C' S ↦ f.targetEquiv)
    (gradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- Restriction preserves the same primal scalar and field-automorphism coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_classification [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn (gradedClassificationEquiv R C
      S hS hgen hn p) =
      gradedClassificationEquiv R C' S hS hgen hn p :=
  gradedCofinalRestrictionEquiv_classification R C C' S hC hS hgen hn p

/-- Restricting to the same selected family is the identity topological equivalence. -/
theorem gradedCofinalRestrictionContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut R C S) := by
  apply DFunLike.ext
  intro g
  rw [gradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose as literal stage selections. -/
theorem gradedCofinalRestrictionContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
        (gradedCofinalRestrictionContinuousEquiv R C' C'' S hC' hS hgen hn) =
      gradedCofinalRestrictionContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, gradedCofinalRestrictionContinuousEquiv_apply]
  exact GradedDiagramAut.restrictStages_trans R C C' S C'' hC hC' g

/-- The exact existing classified cofinal restriction, with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T12 (`thm:t12`). -/
def domainCofinalRestrictionContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S) (DiagramAut.stageTopology R C S)
      (DiagramAut R C' S) (DiagramAut.stageTopology R C' S) _ _ where
  toMulEquiv := domainCofinalRestrictionEquiv R C C' S hC hS hgen hn
  continuous_toFun := (DiagramAut.continuous_restrictStages R C C' S hC).congr
    (fun g ↦ (domainCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g).symm)
  continuous_invFun := DiagramAut.continuous_inverse_restrictStages R C C' S hC _
    (domainCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn)

/-- Forgetting continuity recovers exactly the original M8 equivalence. -/
theorem domainCofinalRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      domainCofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The underlying function is the existing classified restriction. -/
theorem domainCofinalRestrictionContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn : DiagramAut R C S →
      DiagramAut R C' S) = domainCofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The forward map selects the literal subsystem stages and retains the target. -/
theorem domainCofinalRestrictionContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g = DiagramAut.restrictStages
      R C C' S hC g :=
  domainCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g

/-- The inverse is exactly the old classified extension, with the same coordinates. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g =
      (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g := rfl

/-- Each subsystem stage is the unchanged original stage component. -/
theorem domainCofinalRestrictionContinuousEquiv_stageEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) (B : C'.Stage) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).stageEquiv B =
      g.stageEquiv (CofinalSystem.stageInclusion hC B) := by
  rw [domainCofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_stageEquiv]

/-- Literal cofinal restriction retains the single original target. -/
theorem domainCofinalRestrictionContinuousEquiv_targetEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).targetEquiv =
      g.targetEquiv := by
  rw [domainCofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_targetEquiv]

/-- The classified extension has the given component at every selected subsystem stage. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C' S) (B : C'.Stage) :
    ((domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC B) =
      g.stageEquiv B :=
  congrArg (fun f : DiagramAut R C' S ↦ f.stageEquiv B)
    (domainCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- The inverse retains precisely the given original common target. -/
theorem domainCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    ((domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv :=
  congrArg (fun f : DiagramAut R C' S ↦ f.targetEquiv)
    (domainCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- Restriction preserves the same primal scalar and field-automorphism coordinates. -/
theorem domainCofinalRestrictionContinuousEquiv_classification [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn (coefficientDomainAutEquiv R C
      S hS hgen hn p) =
      coefficientDomainAutEquiv R C' S hS hgen hn p :=
  domainCofinalRestrictionEquiv_classification R C C' S hC hS hgen hn p

/-- Restricting to the same selected family is the identity topological equivalence. -/
theorem domainCofinalRestrictionContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut R C S) := by
  apply DFunLike.ext
  intro g
  rw [domainCofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose as literal stage selections. -/
theorem domainCofinalRestrictionContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
        (domainCofinalRestrictionContinuousEquiv R C' C'' S hC' hS hgen hn) =
      domainCofinalRestrictionContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, domainCofinalRestrictionContinuousEquiv_apply]
  exact DiagramAut.restrictStages_trans R C C' S C'' hC hC' g

/-- The exact existing classified cofinal restriction, with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T12 (`thm:t12`). -/
def domainGradedCofinalRestrictionContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S)
      (GradedDiagramAut R C' S) (GradedDiagramAut.stageTopology R C' S) _ _ where
  toMulEquiv := domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
  continuous_toFun := (GradedDiagramAut.continuous_restrictStages R C C' S hC).congr
    (fun g ↦ (domainGradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g).symm)
  continuous_invFun := GradedDiagramAut.continuous_inverse_restrictStages R C C' S hC _
    (domainGradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn)

/-- Forgetting continuity recovers exactly the original M8 equivalence. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn := rfl

/-- The underlying function is the existing classified restriction. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn : GradedDiagramAut R C
      S → GradedDiagramAut R C' S) = domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
      := rfl

/-- The forward map selects the literal subsystem stages and retains the target. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages R C C' S hC g :=
  domainGradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g

/-- The inverse is exactly the old classified extension, with the same coordinates. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g =
      (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g := rfl

/-- Each subsystem stage is the unchanged original stage component. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_stageEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) (B : C'.Stage) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).stageEquiv B =
      g.stageEquiv (CofinalSystem.stageInclusion hC B) := by
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply,
    GradedDiagramAut.restrictStages_stageEquiv]

/-- Literal cofinal restriction retains the single original target. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_targetEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g).targetEquiv =
      g.targetEquiv := by
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply,
    GradedDiagramAut.restrictStages_targetEquiv]

/-- The classified extension has the given component at every selected subsystem stage. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_stageEquiv [IsDomain R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C' S) (B : C'.Stage) :
    ((domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC B) =
      g.stageEquiv B :=
  congrArg (fun f : GradedDiagramAut R C' S ↦ f.stageEquiv B)
    (domainGradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- The inverse retains precisely the given original common target. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_symm_targetEquiv [IsDomain R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    ((domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv :=
  congrArg (fun f : GradedDiagramAut R C' S ↦ f.targetEquiv)
    (domainGradedCofinalRestrictionEquiv_right_inv R C C' S hC hS hgen hn g)

/-- Restriction preserves the same primal scalar and field-automorphism coordinates. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_classification [IsDomain R] (hC : C'.stages
    ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn p) =
      coefficientDomainGradedClassificationEquiv R C' S hS hgen hn p :=
  domainGradedCofinalRestrictionEquiv_classification R C C' S hC hS hgen hn p

/-- Restricting to the same selected family is the identity topological equivalence. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut R C S) := by
  apply DFunLike.ext
  intro g
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.restrictStages_refl]
  rfl

/-- Successive cofinal restrictions compose as literal stage selections. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀
    k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).trans
        (domainGradedCofinalRestrictionContinuousEquiv R C' C'' S hC' hS hgen hn) =
      domainGradedCofinalRestrictionContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, domainGradedCofinalRestrictionContinuousEquiv_apply]
  exact GradedDiagramAut.restrictStages_trans R C C' S C'' hC hC' g

/-- Graded and quadratic cofinal restriction commute with actual degree one. -/
theorem cofinalRestrictionContinuousEquiv_toQuadratic [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn (GradedDiagramAut.toQuadratic R C S
      g) =
      GradedDiagramAut.toQuadratic R C' S
        (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g) :=
  cofinalRestrictionEquiv_toQuadratic R C C' S hC hS hgen hn g

/-- Graded and quadratic cofinal restriction commute with actual degree one. -/
theorem domainCofinalRestrictionContinuousEquiv_toQuadratic [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn (GradedDiagramAut.toQuadratic
      R C S g) =
      GradedDiagramAut.toQuadratic R C' S
        (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g) :=
  domainCofinalRestrictionEquiv_toQuadratic R C C' S hC hS hgen hn g

/-- Local and domain restriction homeomorphisms agree on their coefficient overlap. -/
theorem domainCofinalRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn =
      cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [domainCofinalRestrictionContinuousEquiv_apply, cofinalRestrictionContinuousEquiv_apply]

/-- Local and domain restriction homeomorphisms agree on their coefficient overlap. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn =
      gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply,
    gradedCofinalRestrictionContinuousEquiv_apply]

/-- Comparing unrelated supplied families through their union preserves exactly the old
classification coordinates; no arrangement-union closure is used. -/
theorem cofinalRestrictionContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((cofinalRestrictionContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalRestrictionContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (quadraticAutEquiv R C S hS hgen hn).symm.trans
        (quadraticAutEquiv R C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change ((cofinalRestrictionEquiv R (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn)
      ((cofinalRestrictionEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm g)) = _
  simp only [cofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

/-- Comparing unrelated supplied families through their union preserves exactly the old
classification coordinates; no arrangement-union closure is used. -/
theorem gradedCofinalRestrictionContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((gradedCofinalRestrictionContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalRestrictionContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (gradedClassificationEquiv R C S hS hgen hn).symm.trans
        (gradedClassificationEquiv R C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change ((gradedCofinalRestrictionEquiv R (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn)
      ((gradedCofinalRestrictionEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm g)) = _
  simp only [gradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

/-- Comparing unrelated supplied families through their union preserves exactly the old
classification coordinates; no arrangement-union closure is used. -/
theorem domainCofinalRestrictionContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainCofinalRestrictionContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainCofinalRestrictionContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (coefficientDomainAutEquiv R C S hS hgen hn).symm.trans
        (coefficientDomainAutEquiv R C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change ((domainCofinalRestrictionEquiv R (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn)
      ((domainCofinalRestrictionEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm g)) = _
  simp only [domainCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

/-- Comparing unrelated supplied families through their union preserves exactly the old
classification coordinates; no arrangement-union closure is used. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainGradedCofinalRestrictionContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainGradedCofinalRestrictionContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm.trans
        (coefficientDomainGradedClassificationEquiv R C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change ((domainGradedCofinalRestrictionEquiv R (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn)
      ((domainGradedCofinalRestrictionEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm g)) = _
  simp only [domainGradedCofinalRestrictionEquiv, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

end OrlikSolomon.HyperplaneGT
