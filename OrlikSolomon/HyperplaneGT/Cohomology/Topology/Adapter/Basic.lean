/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Comparison
public import OrlikSolomon.HyperplaneGT.Topology.Basic

/-!
# Direct finite-stage topologies on actual cohomology diagrams

The old actual degree-one and diagonal diagram groups inherit the product topology of
complete discrete stage automorphism groups and their one complete common target.
These definitions use their original subgroups, before the topological adapter comparisons.
No topology on coefficients, classification hypothesis or continuity axiom is required.

The named topology values are `instance_reducible` so inherited Mathlib topology instances
can see their product and induced representations. Only the existing deliberate
`FiniteStageTopology` scope registers diagram topology and separation instances.

## Main definitions and results

* `DiagramAut.familyTopology`, `DiagramAut.stageTopology` and their graded counterparts
  give the direct actual topology and its component continuity criterion.
* `DiagramAut.stageKernel` and its graded counterpart retain both a complete stage and
  the one original common target.
* `DiagramAut.nhds_one_stageBasis` and its graded counterpart reduce finite component
  agreement to one supplied upper stage; no union closure is assumed.

Blueprint: the actual supplied-theory clauses of T01–T02 (`def:t01`, `lem:t02`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Filter Topology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- The product topology on the old complete actual stage groups and one actual target.
Blueprint: the actual-theory clause of T01 (`def:t01`). -/
@[instance_reducible]
def familyTopology : TopologicalSpace (QuadraticAutFamily T C) :=
  DiscreteFamily.topology (fun A : C.Stage ↦ (degreeOne T A.val.val) ≃ₗ[R] (degreeOne T A.val.val))
    ((degreeOne T (twoPunctureArrangement k)) ≃ₗ[R] (degreeOne T (twoPunctureArrangement k)))

/-- The direct subgroup topology on the original actual diagram, including its common target.
Blueprint: the actual-theory clause of T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (DiagramAut T C S) :=
  DiscreteFamily.subgroupTopology (quadraticDiagramAutSubgroup T C S)

/-- The actual diagram topology is induced from its original component product. -/
theorem stageTopology_eq_induced :
    stageTopology T C S = TopologicalSpace.induced Subtype.val (familyTopology T C) := rfl

/-- A map into the actual diagram is continuous exactly when all complete components are.
The codomain topology on each component group is explicitly discrete. -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → DiagramAut T C S) :
    @Continuous X _ _ (stageTopology T C S) f ↔
      (∀ A : C.Stage, @Continuous X _ _ ⊥ (fun x ↦ (f x).stageEquiv A)) ∧
        @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (quadraticDiagramAutSubgroup T C S) f

/-- The projection to a complete actual stage automorphism is continuous. -/
theorem continuous_stageEquiv (A : C.Stage) :
    @Continuous _ _ (stageTopology T C S) ⊥
      (fun g : DiagramAut T C S ↦ g.stageEquiv A) :=
  DiscreteFamily.continuous_stageHom (quadraticDiagramAutSubgroup T C S) A

/-- The projection to the one complete actual target automorphism is continuous. -/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology T C S) ⊥
      (fun g : DiagramAut T C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (quadraticDiagramAutSubgroup T C S)

/-- Simultaneous identity on a complete actual stage and the one original actual target.
Blueprint: the actual-theory clause of T02 (`lem:t02`). -/
def stageKernel (A : C.Stage) : Subgroup (DiagramAut T C S) :=
  DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup T C S) A

/-- Kernel membership retains both complete components, also for empty stages. -/
@[simp]
theorem mem_stageKernel (A : C.Stage) (g : DiagramAut T C S) :
    g ∈ stageKernel T C S A ↔ g.stageEquiv A = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (quadraticDiagramAutSubgroup T C S) A g

instance stageKernel_normal (A : C.Stage) : (stageKernel T C S A).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup T C S) A).Normal

end DiagramAut

namespace GradedDiagramAut

/-- The product topology on the old complete actual stage groups and one actual target.
Blueprint: the actual-theory clause of T01 (`def:t01`). -/
@[instance_reducible]
def familyTopology : TopologicalSpace (GradedAutFamily T C) :=
  DiscreteFamily.topology (fun A : C.Stage ↦
    diagonal T (D.complement A.val.val) ≃ₐ[R] diagonal T (D.complement A.val.val))
    ((diagonal T (schemeMarkingTarget D)) ≃ₐ[R] (diagonal T (schemeMarkingTarget D)))

/-- The direct subgroup topology on the original actual diagram, including its common target.
Blueprint: the actual-theory clause of T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (GradedDiagramAut T C S) :=
  DiscreteFamily.subgroupTopology (gradedDiagramAutSubgroup T C S)

/-- The actual diagram topology is induced from its original component product. -/
theorem stageTopology_eq_induced :
    stageTopology T C S = TopologicalSpace.induced Subtype.val (familyTopology T C) := rfl

/-- A map into the actual diagram is continuous exactly when all complete components are.
The codomain topology on each component group is explicitly discrete. -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → GradedDiagramAut T C S) :
    @Continuous X _ _ (stageTopology T C S) f ↔
      (∀ A : C.Stage, @Continuous X _ _ ⊥ (fun x ↦ (f x).stageEquiv A)) ∧
        @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (gradedDiagramAutSubgroup T C S) f

/-- The projection to a complete actual stage automorphism is continuous. -/
theorem continuous_stageEquiv (A : C.Stage) :
    @Continuous _ _ (stageTopology T C S) ⊥
      (fun g : GradedDiagramAut T C S ↦ g.stageEquiv A) :=
  DiscreteFamily.continuous_stageHom (gradedDiagramAutSubgroup T C S) A

/-- The projection to the one complete actual target automorphism is continuous. -/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology T C S) ⊥
      (fun g : GradedDiagramAut T C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (gradedDiagramAutSubgroup T C S)

/-- Simultaneous identity on a complete actual stage and the one original actual target.
Blueprint: the actual-theory clause of T02 (`lem:t02`). -/
def stageKernel (A : C.Stage) : Subgroup (GradedDiagramAut T C S) :=
  DiscreteFamily.stageKernel (gradedDiagramAutSubgroup T C S) A

/-- Kernel membership retains both complete components, also for empty stages. -/
@[simp]
theorem mem_stageKernel (A : C.Stage) (g : GradedDiagramAut T C S) :
    g ∈ stageKernel T C S A ↔ g.stageEquiv A = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (gradedDiagramAutSubgroup T C S) A g

instance stageKernel_normal (A : C.Stage) : (stageKernel T C S A).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (gradedDiagramAutSubgroup T C S) A).Normal

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology

namespace OrlikSolomon.HyperplaneGT.FiniteStageTopology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Activate the direct actual topology only in the existing finite-stage scope. -/
scoped instance cohomologyDiagramTopologicalSpace :
    TopologicalSpace (Cohomology.DiagramAut T C S) :=
  Cohomology.DiagramAut.stageTopology T C S

scoped instance cohomologyDiagramIsTopologicalGroup :
    IsTopologicalGroup (Cohomology.DiagramAut T C S) :=
  DiscreteFamily.isTopologicalGroup (Cohomology.quadraticDiagramAutSubgroup T C S)

scoped instance cohomologyDiagramT2Space : T2Space (Cohomology.DiagramAut T C S) :=
  DiscreteFamily.t2Space (Cohomology.quadraticDiagramAutSubgroup T C S)

scoped instance cohomologyDiagramTotallySeparatedSpace :
    TotallySeparatedSpace (Cohomology.DiagramAut T C S) :=
  DiscreteFamily.totallySeparatedSpace (Cohomology.quadraticDiagramAutSubgroup T C S)

/-- Activate the direct actual topology only in the existing finite-stage scope. -/
scoped instance cohomologyGradedTopologicalSpace :
    TopologicalSpace (Cohomology.GradedDiagramAut T C S) :=
  Cohomology.GradedDiagramAut.stageTopology T C S

scoped instance cohomologyGradedIsTopologicalGroup :
    IsTopologicalGroup (Cohomology.GradedDiagramAut T C S) :=
  DiscreteFamily.isTopologicalGroup (Cohomology.gradedDiagramAutSubgroup T C S)

scoped instance cohomologyGradedT2Space : T2Space (Cohomology.GradedDiagramAut T C S) :=
  DiscreteFamily.t2Space (Cohomology.gradedDiagramAutSubgroup T C S)

scoped instance cohomologyGradedTotallySeparatedSpace :
    TotallySeparatedSpace (Cohomology.GradedDiagramAut T C S) :=
  DiscreteFamily.totallySeparatedSpace (Cohomology.gradedDiagramAutSubgroup T C S)

end OrlikSolomon.HyperplaneGT.FiniteStageTopology

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Filter Topology
open scoped FiniteStageTopology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  {T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ}
  {n : ℕ} {C : CofinalSystem k₀ k n} {S : Set k₀}

namespace DiagramAut

/-- Equality at a larger actual stage descends along the actual inclusion pullback.
The existing generator coordinates reduce this to free inclusion and algebra generation. -/
theorem stageEquiv_eq_of_le {A B : C.Stage} (hAB : A ≤ B)
    {g h : DiagramAut T C S} (hB : g.stageEquiv B = h.stageEquiv B) :
    g.stageEquiv A = h.stageEquiv A := by
  have hB' : (degreeOneDiagramEquiv T C S g).stageEquiv B =
      (degreeOneDiagramEquiv T C S h).stageEquiv B := by
    apply LinearEquiv.ext
    intro x
    apply (degreeOneEquiv T B.val.val).injective
    rw [degreeOneDiagramEquiv_stage, degreeOneDiagramEquiv_stage, hB]
  have hA := HyperplaneGT.DiagramAut.stageEquiv_eq_of_le hAB hB'
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (degreeOneEquiv T A.val.val).surjective x
  rw [← degreeOneDiagramEquiv_stage, ← degreeOneDiagramEquiv_stage, hA]

variable (T C S)

/-- Enlarging a selected stage shrinks the actual simultaneous stage-and-target kernel. -/
theorem stageKernel_antitone : Antitone (stageKernel T C S) := by
  intro A B hAB g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel T C S B g).mp hg
  exact (mem_stageKernel T C S A g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) hAB hstage, htarget⟩

/-- An actual complete-stage-and-target identity condition is clopen. -/
theorem isClopen_stageKernel (A : C.Stage) :
    IsClopen (stageKernel T C S A : Set (DiagramAut T C S)) :=
  DiscreteFamily.isClopen_stageKernel (quadraticDiagramAutSubgroup T C S) A

/-- Each left coset of an actual complete-stage-and-target kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (A : C.Stage) (g : DiagramAut T C S) :
    IsClopen {h : DiagramAut T C S | g⁻¹ * h ∈ stageKernel T C S A} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (quadraticDiagramAutSubgroup T C S) A g

/-- One complete actual stage and the original actual target give the identity basis.
Only a cofinal upper stage is used; coefficients may be zero and the dimension arbitrary.
Blueprint: the actual-theory clause of T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : DiagramAut T C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ (stageKernel T C S A : Set (DiagramAut T C S))) := by
  classical
  refine (DiscreteFamily.nhds_one_finiteBasis (quadraticDiagramAutSubgroup T C S)).to_hasBasis ?_ ?_
  · intro I hI
    obtain ⟨B, hB⟩ := C.exists_ge_finset hI.toFinset
    refine ⟨B, trivial, ?_⟩
    intro g hg
    obtain ⟨hstage, htarget⟩ := (mem_stageKernel T C S B g).mp hg
    exact ⟨fun A hA ↦ stageEquiv_eq_of_le (h := 1)
      (hB A (hI.mem_toFinset.mpr hA)) hstage, htarget⟩
  · intro A _
    refine ⟨{A}, Set.finite_singleton A, ?_⟩
    intro g hg
    exact (mem_stageKernel T C S A g).mpr ⟨hg.1 A rfl, hg.2⟩

end DiagramAut

namespace GradedDiagramAut

/-- Equality at a larger actual stage descends along the actual inclusion pullback.
The existing generator coordinates reduce this to free inclusion and algebra generation. -/
theorem stageEquiv_eq_of_le {A B : C.Stage} (hAB : A ≤ B)
    {g h : GradedDiagramAut T C S} (hB : g.stageEquiv B = h.stageEquiv B) :
    g.stageEquiv A = h.stageEquiv A := by
  have hB' : (gradedDiagramEquiv T C S g).stageEquiv B =
      (gradedDiagramEquiv T C S h).stageEquiv B := by
    apply AlgEquiv.ext
    intro x
    apply (T.diagonalEquiv B.val.val).injective
    rw [gradedDiagramEquiv_stage, gradedDiagramEquiv_stage, hB]
  have hA := HyperplaneGT.GradedDiagramAut.stageEquiv_eq_of_le hAB hB'
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (T.diagonalEquiv A.val.val).surjective x
  rw [← gradedDiagramEquiv_stage, ← gradedDiagramEquiv_stage, hA]

variable (T C S)

/-- Enlarging a selected stage shrinks the actual simultaneous stage-and-target kernel. -/
theorem stageKernel_antitone : Antitone (stageKernel T C S) := by
  intro A B hAB g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel T C S B g).mp hg
  exact (mem_stageKernel T C S A g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) hAB hstage, htarget⟩

/-- An actual complete-stage-and-target identity condition is clopen. -/
theorem isClopen_stageKernel (A : C.Stage) :
    IsClopen (stageKernel T C S A : Set (GradedDiagramAut T C S)) :=
  DiscreteFamily.isClopen_stageKernel (gradedDiagramAutSubgroup T C S) A

/-- Each left coset of an actual complete-stage-and-target kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (A : C.Stage) (g : GradedDiagramAut T C S) :
    IsClopen {h : GradedDiagramAut T C S | g⁻¹ * h ∈ stageKernel T C S A} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (gradedDiagramAutSubgroup T C S) A g

/-- One complete actual stage and the original actual target give the identity basis.
Only a cofinal upper stage is used; coefficients may be zero and the dimension arbitrary.
Blueprint: the actual-theory clause of T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : GradedDiagramAut T C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ (stageKernel T C S A : Set (GradedDiagramAut T C S))) := by
  classical
  refine (DiscreteFamily.nhds_one_finiteBasis (gradedDiagramAutSubgroup T C S)).to_hasBasis ?_ ?_
  · intro I hI
    obtain ⟨B, hB⟩ := C.exists_ge_finset hI.toFinset
    refine ⟨B, trivial, ?_⟩
    intro g hg
    obtain ⟨hstage, htarget⟩ := (mem_stageKernel T C S B g).mp hg
    exact ⟨fun A hA ↦ stageEquiv_eq_of_le (h := 1)
      (hB A (hI.mem_toFinset.mpr hA)) hstage, htarget⟩
  · intro A _
    refine ⟨{A}, Set.finite_singleton A, ?_⟩
    intro g hg
    exact (mem_stageKernel T C S A g).mpr ⟨hg.1 A rfl, hg.2⟩

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology
