/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic
public import OrlikSolomon.Topology.DiscreteFamily

/-!
# Direct component topologies on the marked diagrams

`DiagramAut.stageTopology` and `GradedDiagramAut.stageTopology` are induced from the
products of discrete complete stage automorphism groups and the one discrete common target.
The existing carriers, group laws and homogeneous-degree conditions are unchanged.

The `FiniteStageTopology` scope provides the named topologies and their topological-group,
Hausdorff and total-separation instances. No topology is installed on the coefficient ring
or globally on linear or algebra equivalences. The component criteria use explicit discrete
codomains, independently of any other topology on the underlying mathematical data.

Blueprint: the pure diagram portions of T01 (`def:t01`) and T02 (`lem:t02`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- The direct product topology on complete discrete linear stage groups and the one target.
Blueprint: T01 (`def:t01`). -/
@[instance_reducible]
def familyTopology : TopologicalSpace (QuadraticAutFamily R C) :=
  DiscreteFamily.topology
    (fun 𝒜 : C.Stage ↦ (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R))
    ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R))

/-- Finite-stage convergence on the existing marked quadratic diagram group. The common
complete target component is included even for empty stages. Blueprint: T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (DiagramAut R C S) :=
  DiscreteFamily.subgroupTopology (quadraticDiagramAutSubgroup R C S)

/-- The quadratic diagram topology is literally the induced topology of its old subgroup. -/
theorem stageTopology_eq_induced :
    stageTopology R C S = TopologicalSpace.induced Subtype.val (familyTopology R C) := rfl

/-- Continuity into the quadratic diagram is precisely continuity of every complete stage
and the single complete target into their discrete topologies. Blueprint: T01 (`def:t01`). -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → DiagramAut R C S) :
    @Continuous X _ _ (stageTopology R C S) f ↔
      (∀ 𝒜 : C.Stage, @Continuous X _ _ ⊥
        (fun x ↦ (f x).stageEquiv 𝒜)) ∧
      @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (quadraticDiagramAutSubgroup R C S) f

/-- Projection to a whole finite-stage automorphism is continuous into the discrete group. -/
theorem continuous_stageEquiv (𝒜 : C.Stage) :
    @Continuous _ _ (stageTopology R C S) ⊥
      (fun g : DiagramAut R C S ↦ g.stageEquiv 𝒜) :=
  DiscreteFamily.continuous_stageHom (quadraticDiagramAutSubgroup R C S) 𝒜

/-- Projection to the whole common-target automorphism is continuous into the discrete group.
-/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology R C S) ⊥ (fun g : DiagramAut R C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (quadraticDiagramAutSubgroup R C S)

end DiagramAut

namespace GradedDiagramAut

/-- The direct product topology of discrete full stage algebra automorphisms and one target.
The degree-preservation conditions remain in the existing subgroup. Blueprint: T01 (`def:t01`).
-/
@[instance_reducible]
def familyTopology : TopologicalSpace (GradedAutFamily R C) :=
  DiscreteFamily.topology
    (fun 𝒜 : C.Stage ↦ OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val)
    (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R] OSAlgebra R (twoPunctureArrangement k))

/-- Finite-stage convergence on the existing full marked graded diagram group. This uses
complete algebra automorphisms, not only their generators. Blueprint: T01 (`def:t01`). -/
@[instance_reducible]
def stageTopology : TopologicalSpace (GradedDiagramAut R C S) :=
  DiscreteFamily.subgroupTopology (gradedDiagramAutSubgroup R C S)

/-- The full graded diagram topology is induced from its original ambient product. -/
theorem stageTopology_eq_induced :
    stageTopology R C S = TopologicalSpace.induced Subtype.val (familyTopology R C) := rfl

/-- Continuity into the full graded diagram is continuity of every complete stage and target
algebra automorphism into its discrete topology. Blueprint: T01 (`def:t01`). -/
theorem continuous_stageTopology_iff {X : Type*} [TopologicalSpace X]
    (f : X → GradedDiagramAut R C S) :
    @Continuous X _ _ (stageTopology R C S) f ↔
      (∀ 𝒜 : C.Stage, @Continuous X _ _ ⊥
        (fun x ↦ (f x).stageEquiv 𝒜)) ∧
      @Continuous X _ _ ⊥ (fun x ↦ (f x).targetEquiv) :=
  DiscreteFamily.continuous_iff (gradedDiagramAutSubgroup R C S) f

/-- Projection to a whole stage algebra automorphism is continuous into the discrete group.
-/
theorem continuous_stageEquiv (𝒜 : C.Stage) :
    @Continuous _ _ (stageTopology R C S) ⊥
      (fun g : GradedDiagramAut R C S ↦ g.stageEquiv 𝒜) :=
  DiscreteFamily.continuous_stageHom (gradedDiagramAutSubgroup R C S) 𝒜

/-- Projection to the whole target algebra automorphism is continuous into the discrete group.
-/
theorem continuous_targetEquiv :
    @Continuous _ _ (stageTopology R C S) ⊥ (fun g : GradedDiagramAut R C S ↦ g.targetEquiv) :=
  DiscreteFamily.continuous_targetHom (gradedDiagramAutSubgroup R C S)

end GradedDiagramAut

namespace FiniteStageTopology

/-- The direct quadratic topology is activated only by opening `FiniteStageTopology`. -/
scoped instance diagramTopologicalSpace : TopologicalSpace (DiagramAut R C S) :=
  DiagramAut.stageTopology R C S

/-- The direct full graded topology is activated only by opening `FiniteStageTopology`. -/
scoped instance gradedTopologicalSpace : TopologicalSpace (GradedDiagramAut R C S) :=
  GradedDiagramAut.stageTopology R C S

scoped instance diagramIsTopologicalGroup : IsTopologicalGroup (DiagramAut R C S) :=
  DiscreteFamily.isTopologicalGroup (quadraticDiagramAutSubgroup R C S)

scoped instance gradedIsTopologicalGroup : IsTopologicalGroup (GradedDiagramAut R C S) :=
  DiscreteFamily.isTopologicalGroup (gradedDiagramAutSubgroup R C S)

scoped instance diagramT2Space : T2Space (DiagramAut R C S) :=
  DiscreteFamily.t2Space (quadraticDiagramAutSubgroup R C S)

scoped instance gradedT2Space : T2Space (GradedDiagramAut R C S) :=
  DiscreteFamily.t2Space (gradedDiagramAutSubgroup R C S)

scoped instance diagramTotallySeparatedSpace : TotallySeparatedSpace (DiagramAut R C S) :=
  DiscreteFamily.totallySeparatedSpace (quadraticDiagramAutSubgroup R C S)

scoped instance gradedTotallySeparatedSpace : TotallySeparatedSpace (GradedDiagramAut R C S) :=
  DiscreteFamily.totallySeparatedSpace (gradedDiagramAutSubgroup R C S)

end FiniteStageTopology

end OrlikSolomon.HyperplaneGT
