/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Degree-one restriction preserves the full diagram topology

The existing `GradedDiagramAut.toQuadratic` is a topological embedding for arbitrary
commutative coefficients and every dimension. Equality of each complete algebra component
is equivalent to equality of its degree-one restriction, because the algebra is generated
in degree one. This includes the original common target, even when all stages are empty.

The direct graded topology is therefore exactly the topology induced by restriction.
`GradedDiagramAut.continuous_iff_toQuadratic_comp` tests continuity through that existing
map, and `GradedDiagramAut.continuous_inverse_toQuadratic` proves continuity of any actual
inverse. No extension of arbitrary quadratic automorphisms is assumed.

Blueprint: T04 (`lem:t04`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT.GradedDiagramAut

open Filter Topology
open scoped FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} {R : Type r} [CommRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- Equality of complete stage algebra automorphisms is equivalent to equality of their
canonical degree-one restrictions. No quadratic presentation assumption is needed. -/
theorem stageEquiv_eq_iff_toQuadratic (g h : GradedDiagramAut R C S) (𝒜 : C.Stage) :
    g.stageEquiv 𝒜 = h.stageEquiv 𝒜 ↔
      (toQuadratic R C S g).stageEquiv 𝒜 = (toQuadratic R C S h).stageEquiv 𝒜 := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (osDegreeOneEquiv R 𝒜.val.val).injective
    apply Subtype.ext
    change (osDegreeOneEquiv R 𝒜.val.val (g.stageLinearEquiv 𝒜 x) : OSAlgebra R 𝒜.val.val) =
      osDegreeOneEquiv R 𝒜.val.val (h.stageLinearEquiv 𝒜 x)
    rw [stageLinearEquiv_apply, stageLinearEquiv_apply, heq]
  · intro heq
    apply AlgEquiv.coe_toAlgHom_injective
    apply OSAlgebra.algHom_ext
    intro H
    change g.stageLinearEquiv 𝒜 = h.stageLinearEquiv 𝒜 at heq
    have hgen := congrArg (fun f : (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) ↦
      (osDegreeOneEquiv R 𝒜.val.val (f (Finsupp.single H 1)) : OSAlgebra R 𝒜.val.val)) heq
    rw [stageLinearEquiv_apply, stageLinearEquiv_apply] at hgen
    simpa using hgen

/-- The same degree-one faithfulness holds for the single original common target. -/
theorem targetEquiv_eq_iff_toQuadratic (g h : GradedDiagramAut R C S) :
    g.targetEquiv = h.targetEquiv ↔
      (toQuadratic R C S g).targetEquiv = (toQuadratic R C S h).targetEquiv := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (markingTargetDegreeOneEquiv (k := k) R).injective
    apply Subtype.ext
    change (markingTargetDegreeOneEquiv (k := k) R (g.targetLinearEquiv x) :
      OSAlgebra R (twoPunctureArrangement k)) =
      markingTargetDegreeOneEquiv (k := k) R (h.targetLinearEquiv x)
    rw [targetLinearEquiv_apply, targetLinearEquiv_apply, heq]
  · intro heq
    apply AlgEquiv.coe_toAlgHom_injective
    apply OSAlgebra.algHom_ext
    intro H
    obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
    change g.targetLinearEquiv = h.targetLinearEquiv at heq
    have hgen := congrArg (fun f : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R) ↦
      (markingTargetDegreeOneEquiv (k := k) R (f (Finsupp.single a 1)) :
        OSAlgebra R (twoPunctureArrangement k))) heq
    rw [targetLinearEquiv_apply, targetLinearEquiv_apply] at hgen
    simpa using hgen

variable (R C S)

/-- Kernel membership commutes with restriction, including the single common target. -/
theorem mem_stageKernel_toQuadratic (g : GradedDiagramAut R C S) (𝒜 : C.Stage) :
    toQuadratic R C S g ∈ DiagramAut.stageKernel R C S 𝒜 ↔
      g ∈ stageKernel R C S 𝒜 := by
  rw [DiagramAut.mem_stageKernel, mem_stageKernel]
  simpa only [map_one, stageEquiv_one, targetEquiv_one, DiagramAut.stageEquiv_one,
    DiagramAut.targetEquiv_one, LinearEquiv.one_eq_refl, AlgEquiv.aut_one] using
    and_congr (stageEquiv_eq_iff_toQuadratic g 1 𝒜).symm
      (targetEquiv_eq_iff_toQuadratic g 1).symm

/-- Restriction pulls back each quadratic stage-and-target kernel to exactly the full
graded kernel. In particular the common target is retained. Blueprint: T04 (`lem:t04`). -/
theorem preimage_stageKernel (𝒜 : C.Stage) :
    (toQuadratic R C S) ⁻¹' (DiagramAut.stageKernel R C S 𝒜 : Set _) =
      (stageKernel R C S 𝒜 : Set _) := by
  ext g
  change toQuadratic R C S g ∈ DiagramAut.stageKernel R C S 𝒜 ↔
    g ∈ stageKernel R C S 𝒜
  exact mem_stageKernel_toQuadratic R C S g 𝒜

/-- The direct full graded topology is induced by the existing degree-one restriction:
the stage-and-target neighborhood bases agree exactly. Blueprint: T04 (`lem:t04`). -/
theorem isInducing_toQuadratic : IsInducing (toQuadratic R C S) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply (nhds_one_stageBasis R C S).eq_of_same_basis
  simpa only [preimage_stageKernel] using
    (DiagramAut.nhds_one_stageBasis R C S).comap (toQuadratic R C S)

/-- Equality of the named direct graded topology with the topology induced by degree one.
This does not replace its original definition from complete algebra components. -/
theorem stageTopology_eq_induced_toQuadratic :
    stageTopology R C S =
      TopologicalSpace.induced (toQuadratic R C S) (DiagramAut.stageTopology R C S) :=
  (isInducing_toQuadratic R C S).eq_induced

/-- The exact existing degree-one restriction is a topological embedding for all
commutative coefficients and dimensions. Blueprint: T04 (`lem:t04`). -/
theorem isEmbedding_toQuadratic : IsEmbedding (toQuadratic R C S) :=
  ⟨isInducing_toQuadratic R C S, toQuadratic_injective⟩

/-- Restriction to degree one is continuous for the direct diagram topologies. -/
theorem continuous_toQuadratic : Continuous (toQuadratic R C S) :=
  (isEmbedding_toQuadratic R C S).continuous

/-- A map into the full graded diagram is continuous exactly when its actual degree-one
restriction is continuous. -/
theorem continuous_iff_toQuadratic_comp {X : Type*} [TopologicalSpace X]
    (f : X → GradedDiagramAut R C S) :
    Continuous f ↔ Continuous (toQuadratic R C S ∘ f) :=
  (isEmbedding_toQuadratic R C S).continuous_iff

/-- Any actual inverse of the existing degree-one restriction is continuous. In particular
this applies to each M8 restriction equivalence when its classification hypotheses hold.
Blueprint: T04 (`lem:t04`). -/
theorem continuous_inverse_toQuadratic (f : DiagramAut R C S → GradedDiagramAut R C S)
    (hf : Function.RightInverse f (toQuadratic R C S)) : Continuous f := by
  apply (continuous_iff_toQuadratic_comp R C S f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

end OrlikSolomon.HyperplaneGT.GradedDiagramAut
