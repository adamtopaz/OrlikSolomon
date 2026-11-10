/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Diagram
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Basic

/-!
# Direct finite-stage topology on ordinary de Rham diagrams

The original ordinary H¹ and total-cohomology diagram groups have the induced topology
from their complete discrete stage automorphisms and one original common target. These
are product/subgroup definitions, before any new comparison homeomorphism. No topology
on the geometric field is used, and no dimension or marking hypothesis is imposed.

Named `instance_reducible` topology values expose the existing product representations.
Only the parent `FiniteStageTopology` scope activates the ordinary topology and group/
separation instances. Simultaneous complete-stage-and-target kernels give the identity
basis; old untwisting and generator comparisons prove downward equality without assuming
injectivity of full cohomology inclusions. No selected-stage union closure is needed.

Blueprint: the ordinary clauses of T01–T02 (`def:t01`, `lem:t02`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Filter Topology

-- Prove finite-cylinder compression with abstract factor groups. This prevents tactic
-- elaboration from repeatedly unfolding the constructed ordinary H¹ carrier.
private theorem stageBasis_of_kernel_compression {ι : Type*} {M : ι → Type*} {T : Type*}
    [∀ i, Group (M i)] [Group T] (G : Subgroup ((∀ i, M i) × T))
    (hupper : ∀ I : Finset ι, ∃ j, ∀ i ∈ I,
      DiscreteFamily.stageKernel G j ≤ DiscreteFamily.stageKernel G i) :
    (@nhds G (DiscreteFamily.subgroupTopology G) 1).HasBasis (fun _ : ι ↦ True)
      (fun i ↦ (DiscreteFamily.stageKernel G i : Set G)) := by
  classical
  refine (DiscreteFamily.nhds_one_finiteBasis G).to_hasBasis ?_ ?_
  · intro I hI
    obtain ⟨j, hj⟩ := hupper hI.toFinset
    refine ⟨j, trivial, ?_⟩
    intro g hg
    exact ⟨fun i hi ↦ ((DiscreteFamily.mem_stageKernel G i g).mp
      (hj i (hI.mem_toFinset.mpr hi) hg)).1,
      ((DiscreteFamily.mem_stageKernel G j g).mp hg).2⟩
  · intro i _
    refine ⟨{i}, Set.finite_singleton i, ?_⟩
    intro g hg
    exact (DiscreteFamily.mem_stageKernel G i g).mpr ⟨hg.1 i rfl, hg.2⟩

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

namespace DiagramAut

/-- The direct product of the whole discrete ordinary stage groups and original target.
Blueprint: the ordinary clause of T01 (`def:t01`). -/
@[instance_reducible]
def familyTopology : TopologicalSpace (QuadraticAutFamily C) :=
  DiscreteFamily.topology (fun A : C.Stage ↦ degreeOne A.val.val ≃ₗ[k] degreeOne A.val.val)
    (degreeOne (twoPunctureArrangement k) ≃ₗ[k] degreeOne (twoPunctureArrangement k))

/-- The direct topology on the original ordinary subgroup, before any comparison.
Blueprint: the ordinary clause of T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (DiagramAut C S) :=
  DiscreteFamily.subgroupTopology (quadraticDiagramAutSubgroup C S)

/-- Ordinary finite-stage convergence is induced from the original component product. -/
theorem stageTopology_eq_induced :
    stageTopology C S = TopologicalSpace.induced Subtype.val (familyTopology C) := rfl

/-- Continuity into the ordinary diagram tests every complete stage and the common target.
Every component codomain has the explicitly discrete topology. -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → DiagramAut C S) :
    @Continuous X _ _ (stageTopology C S) f ↔
      (∀ A : C.Stage, @Continuous X _ _ ⊥ (fun x ↦ (f x).stageEquiv A)) ∧
        @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (quadraticDiagramAutSubgroup C S) f

/-- The complete ordinary stage automorphism is a continuous discrete coordinate. -/
theorem continuous_stageEquiv (A : C.Stage) :
    @Continuous _ _ (stageTopology C S) ⊥ (fun g : DiagramAut C S ↦ g.stageEquiv A) :=
  DiscreteFamily.continuous_stageHom (quadraticDiagramAutSubgroup C S) A

/-- The complete original ordinary target is a continuous discrete coordinate. -/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology C S) ⊥ (fun g : DiagramAut C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (quadraticDiagramAutSubgroup C S)

/-- Simultaneous identity on a whole ordinary stage and the one original target.
Blueprint: the ordinary clause of T02 (`lem:t02`). -/
def stageKernel (A : C.Stage) : Subgroup (DiagramAut C S) :=
  DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup C S) A

/-- Kernel membership retains both complete coordinates, including in dimension zero. -/
@[simp]
theorem mem_stageKernel (A : C.Stage) (g : DiagramAut C S) :
    g ∈ stageKernel C S A ↔ g.stageEquiv A = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (quadraticDiagramAutSubgroup C S) A g

/-- A complete-stage-and-target identity condition is a normal subgroup. -/
instance stageKernel_normal (A : C.Stage) : (stageKernel C S A).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup C S) A).Normal

end DiagramAut

namespace GradedDiagramAut

/-- The direct product of the whole discrete ordinary stage groups and original target.
Blueprint: the ordinary clause of T01 (`def:t01`). -/
@[instance_reducible]
def familyTopology : TopologicalSpace (GradedAutFamily C) :=
  DiscreteFamily.topology (fun A : C.Stage ↦ HdR ((Daff).complement A.val.val) ≃ₐ[k]
      HdR ((Daff).complement A.val.val))
    (HdR (Cohomology.schemeMarkingTarget Daff) ≃ₐ[k]
      HdR (Cohomology.schemeMarkingTarget Daff))

/-- The direct topology on the original ordinary subgroup, before any comparison.
Blueprint: the ordinary clause of T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (GradedDiagramAut C S) :=
  DiscreteFamily.subgroupTopology (gradedDiagramAutSubgroup C S)

/-- Ordinary finite-stage convergence is induced from the original component product. -/
theorem stageTopology_eq_induced :
    stageTopology C S = TopologicalSpace.induced Subtype.val (familyTopology C) := rfl

/-- Continuity into the ordinary diagram tests every complete stage and the common target.
Every component codomain has the explicitly discrete topology. -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → GradedDiagramAut C S) :
    @Continuous X _ _ (stageTopology C S) f ↔
      (∀ A : C.Stage, @Continuous X _ _ ⊥ (fun x ↦ (f x).stageEquiv A)) ∧
        @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (gradedDiagramAutSubgroup C S) f

/-- The complete ordinary stage automorphism is a continuous discrete coordinate. -/
theorem continuous_stageEquiv (A : C.Stage) :
    @Continuous _ _ (stageTopology C S) ⊥ (fun g : GradedDiagramAut C S ↦ g.stageEquiv A) :=
  DiscreteFamily.continuous_stageHom (gradedDiagramAutSubgroup C S) A

/-- The complete original ordinary target is a continuous discrete coordinate. -/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology C S) ⊥ (fun g : GradedDiagramAut C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (gradedDiagramAutSubgroup C S)

/-- Simultaneous identity on a whole ordinary stage and the one original target.
Blueprint: the ordinary clause of T02 (`lem:t02`). -/
def stageKernel (A : C.Stage) : Subgroup (GradedDiagramAut C S) :=
  DiscreteFamily.stageKernel (gradedDiagramAutSubgroup C S) A

/-- Kernel membership retains both complete coordinates, including in dimension zero. -/
@[simp]
theorem mem_stageKernel (A : C.Stage) (g : GradedDiagramAut C S) :
    g ∈ stageKernel C S A ↔ g.stageEquiv A = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (gradedDiagramAutSubgroup C S) A g

/-- A complete-stage-and-target identity condition is a normal subgroup. -/
instance stageKernel_normal (A : C.Stage) : (stageKernel C S A).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (gradedDiagramAutSubgroup C S) A).Normal

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham

namespace OrlikSolomon.HyperplaneGT.FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Activate the direct ordinary topology only in the existing finite-stage scope. -/
scoped instance deRhamDiagramTopologicalSpace :
    TopologicalSpace (Cohomology.DeRham.DiagramAut C S) :=
  Cohomology.DeRham.DiagramAut.stageTopology C S

/-- The direct ordinary component topology is a topological group. -/
scoped instance deRhamDiagramIsTopologicalGroup :
    IsTopologicalGroup (Cohomology.DeRham.DiagramAut C S) :=
  DiscreteFamily.isTopologicalGroup (Cohomology.DeRham.quadraticDiagramAutSubgroup C S)

/-- Distinct ordinary diagrams are separated by complete discrete coordinates. -/
scoped instance deRhamDiagramT2Space : T2Space (Cohomology.DeRham.DiagramAut C S) :=
  DiscreteFamily.t2Space (Cohomology.DeRham.quadraticDiagramAutSubgroup C S)

/-- Complete ordinary coordinates separate points by complementary clopen sets. -/
scoped instance deRhamDiagramTotallySeparatedSpace :
    TotallySeparatedSpace (Cohomology.DeRham.DiagramAut C S) :=
  DiscreteFamily.totallySeparatedSpace (Cohomology.DeRham.quadraticDiagramAutSubgroup C S)

/-- Activate the direct ordinary topology only in the existing finite-stage scope. -/
scoped instance deRhamGradedTopologicalSpace :
    TopologicalSpace (Cohomology.DeRham.GradedDiagramAut C S) :=
  Cohomology.DeRham.GradedDiagramAut.stageTopology C S

/-- The direct ordinary component topology is a topological group. -/
scoped instance deRhamGradedIsTopologicalGroup :
    IsTopologicalGroup (Cohomology.DeRham.GradedDiagramAut C S) :=
  DiscreteFamily.isTopologicalGroup (Cohomology.DeRham.gradedDiagramAutSubgroup C S)

/-- Distinct ordinary diagrams are separated by complete discrete coordinates. -/
scoped instance deRhamGradedT2Space : T2Space (Cohomology.DeRham.GradedDiagramAut C S) :=
  DiscreteFamily.t2Space (Cohomology.DeRham.gradedDiagramAutSubgroup C S)

/-- Complete ordinary coordinates separate points by complementary clopen sets. -/
scoped instance deRhamGradedTotallySeparatedSpace :
    TotallySeparatedSpace (Cohomology.DeRham.GradedDiagramAut C S) :=
  DiscreteFamily.totallySeparatedSpace (Cohomology.DeRham.gradedDiagramAutSubgroup C S)

end OrlikSolomon.HyperplaneGT.FiniteStageTopology

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Filter Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} {C : CofinalSystem k₀ k n} {S : Set k₀}

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

namespace DiagramAut

/-- Equality on a larger ordinary stage descends along the actual inclusion. The old
untwisting and generator comparisons supply this without full inclusion injectivity. -/
theorem stageEquiv_eq_of_le {A B : C.Stage} (hAB : A ≤ B)
    {g h : DiagramAut C S} (hB : g.stageEquiv B = h.stageEquiv B) :
    g.stageEquiv A = h.stageEquiv A := by
  have hB' : (quadraticTwistEquiv C S g).stageEquiv B =
      (quadraticTwistEquiv C S h).stageEquiv B := by
    apply LinearEquiv.ext
    intro x
    apply (degreeOneUntwist B.val.val).injective
    rw [quadraticTwistEquiv_stage, quadraticTwistEquiv_stage, hB]
  have hA := Cohomology.DiagramAut.stageEquiv_eq_of_le hAB hB'
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (degreeOneUntwist A.val.val).surjective x
  exact ((quadraticTwistEquiv_stage C S g A y).symm.trans
    (congrArg (degreeOneUntwist A.val.val) (DFunLike.congr_fun hA y))).trans
      (quadraticTwistEquiv_stage C S h A y)

variable (C S)

/-- Enlarging a selected stage shrinks its whole ordinary stage-and-target kernel. -/
theorem stageKernel_antitone : Antitone (stageKernel C S) := by
  intro A B hAB g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel C S B g).mp hg
  exact (mem_stageKernel C S A g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) hAB hstage, htarget⟩

/-- Each whole ordinary stage-and-target identity condition is clopen. -/
theorem isClopen_stageKernel (A : C.Stage) :
    IsClopen (stageKernel C S A : Set (DiagramAut C S)) :=
  DiscreteFamily.isClopen_stageKernel (quadraticDiagramAutSubgroup C S) A

/-- Every coset of an ordinary whole-stage-and-target kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (A : C.Stage) (g : DiagramAut C S) :
    IsClopen {h : DiagramAut C S | g⁻¹ * h ∈ stageKernel C S A} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (quadraticDiagramAutSubgroup C S) A g

/-- One complete ordinary stage and the original target give the identity neighborhood
basis, in every dimension. Blueprint: the ordinary clause of T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : DiagramAut C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ (stageKernel C S A : Set (DiagramAut C S))) := by
  have hupper : ∀ I : Finset C.Stage, ∃ B, ∀ A ∈ I,
      stageKernel C S B ≤ stageKernel C S A := by
    intro I
    obtain ⟨B, hB⟩ := C.exists_ge_finset I
    exact ⟨B, fun A hA ↦ stageKernel_antitone C S (hB A hA)⟩
  exact stageBasis_of_kernel_compression (quadraticDiagramAutSubgroup C S) hupper

end DiagramAut

namespace GradedDiagramAut

/-- Equality on a larger ordinary stage descends along the actual inclusion. The old
untwisting and generator comparisons supply this without full inclusion injectivity. -/
theorem stageEquiv_eq_of_le {A B : C.Stage} (hAB : A ≤ B)
    {g h : GradedDiagramAut C S} (hB : g.stageEquiv B = h.stageEquiv B) :
    g.stageEquiv A = h.stageEquiv A := by
  have hB' : (gradedTwistEquiv C S g).stageEquiv B = (gradedTwistEquiv C S h).stageEquiv B := by
    apply AlgEquiv.ext
    intro x
    apply (diagonalUntwist ((Daff).complement B.val.val)).injective
    rw [gradedTwistEquiv_stage, gradedTwistEquiv_stage, hB]
  have hA := Cohomology.GradedDiagramAut.stageEquiv_eq_of_le hAB hB'
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (diagonalUntwist ((Daff).complement A.val.val)).surjective x
  rw [← gradedTwistEquiv_stage, ← gradedTwistEquiv_stage, hA]

variable (C S)

/-- Enlarging a selected stage shrinks its whole ordinary stage-and-target kernel. -/
theorem stageKernel_antitone : Antitone (stageKernel C S) := by
  intro A B hAB g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel C S B g).mp hg
  exact (mem_stageKernel C S A g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) hAB hstage, htarget⟩

/-- Each whole ordinary stage-and-target identity condition is clopen. -/
theorem isClopen_stageKernel (A : C.Stage) :
    IsClopen (stageKernel C S A : Set (GradedDiagramAut C S)) :=
  DiscreteFamily.isClopen_stageKernel (gradedDiagramAutSubgroup C S) A

/-- Every coset of an ordinary whole-stage-and-target kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (A : C.Stage) (g : GradedDiagramAut C S) :
    IsClopen {h : GradedDiagramAut C S | g⁻¹ * h ∈ stageKernel C S A} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (gradedDiagramAutSubgroup C S) A g

/-- One complete ordinary stage and the original target give the identity neighborhood
basis, in every dimension. Blueprint: the ordinary clause of T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : GradedDiagramAut C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ (stageKernel C S A : Set (GradedDiagramAut C S))) := by
  apply stageBasis_of_kernel_compression (gradedDiagramAutSubgroup C S)
  intro I
  obtain ⟨B, hB⟩ := C.exists_ge_finset I
  exact ⟨B, fun A hA ↦ stageKernel_antitone C S (hB A hA)⟩

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
