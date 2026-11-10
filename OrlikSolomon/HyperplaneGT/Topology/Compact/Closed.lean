/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Basic

/-!
# Closedness of the actual marked diagram subgroups

The quadratic and full graded diagram groups are closed in their original products of
discrete complete stage automorphism groups and the one common target. Relation and degree
preservation involve one complete coordinate; each arrow equation involves two. Arbitrary
intersections impose all these conditions, without a finiteness assumption on the family,
the degrees or the available markings.

No coefficient topology, classification, algebraicity or nontriviality hypothesis enters.
Blueprint: the closed-subgroup assertions of T03 (`prop:t03`).
-/

@[expose] public section

universe u v r

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Whole quadratic-relation preservation and every inclusion/marking square cut out a
closed subgroup of the original discrete ambient product. Blueprint: T03 (`prop:t03`). -/
theorem DiagramAut.isClosed_subgroup :
    @IsClosed (QuadraticAutFamily R C) (DiagramAut.familyTopology R C)
      (quadraticDiagramAutSubgroup R C S : Set (QuadraticAutFamily R C)) := by
  let : ∀ 𝒜 : C.Stage, TopologicalSpace
      ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) := fun _ ↦ ⊥
  let : ∀ 𝒜 : C.Stage, DiscreteTopology
      ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) := fun _ ↦ discreteTopology_bot _
  let : TopologicalSpace ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) := ⊥
  let : DiscreteTopology ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) := discreteTopology_bot _
  have hstage (𝒜 : C.Stage) : Continuous (fun g : QuadraticAutFamily R C ↦ g.1 𝒜) :=
    (continuous_apply 𝒜).comp continuous_fst
  have htarget : Continuous (fun g : QuadraticAutFamily R C ↦ g.2) := continuous_snd
  change IsClosed {g : QuadraticAutFamily R C | _}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun 𝒜 ↦ ?_).inter
    ((isClosed_iInter fun 𝒜 ↦ isClosed_iInter fun ℬ ↦ isClosed_iInter fun h ↦ ?_).inter
      (isClosed_iInter fun 𝒜 ↦ isClosed_iInter fun w ↦ isClosed_iInter fun hw ↦ ?_))
  · exact (isClosed_discrete {f : (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) |
        (quadraticRelationSpan R 𝒜.val.val).map (exteriorPower.map 2 f.toLinearMap) =
          quadraticRelationSpan R 𝒜.val.val}).preimage
      (hstage 𝒜)
  · exact (isClosed_discrete {p :
        ((ℬ.val.val →₀ R) ≃ₗ[R] (ℬ.val.val →₀ R)) ×
          ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) |
        p.1.toLinearMap.comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
          (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp p.2.toLinearMap}).preimage
      ((hstage ℬ).prodMk (hstage 𝒜))
  · exact (isClosed_discrete {p :
        ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) ×
          ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) |
        p.1.toLinearMap.comp (w.basisMap R hw) =
          (w.basisMap R hw).comp p.2.toLinearMap}).preimage
      ((hstage 𝒜).prodMk htarget)

/-- Every degree condition and every full-algebra arrow equation defines a closed cylinder
in the original full automorphism product. Blueprint: T03 (`prop:t03`). -/
theorem GradedDiagramAut.isClosed_subgroup :
    @IsClosed (GradedAutFamily R C) (GradedDiagramAut.familyTopology R C)
      (gradedDiagramAutSubgroup R C S : Set (GradedAutFamily R C)) := by
  let : ∀ 𝒜 : C.Stage, TopologicalSpace
      (OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val) := fun _ ↦ ⊥
  let : ∀ 𝒜 : C.Stage, DiscreteTopology
      (OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val) := fun _ ↦ discreteTopology_bot _
  let : TopologicalSpace
      (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R] OSAlgebra R (twoPunctureArrangement k)) := ⊥
  let : DiscreteTopology
      (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R] OSAlgebra R (twoPunctureArrangement k)) :=
    discreteTopology_bot _
  have hstage (𝒜 : C.Stage) : Continuous (fun g : GradedAutFamily R C ↦ g.1 𝒜) :=
    (continuous_apply 𝒜).comp continuous_fst
  have htarget : Continuous (fun g : GradedAutFamily R C ↦ g.2) := continuous_snd
  change IsClosed {g : GradedAutFamily R C | _}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun 𝒜 ↦ isClosed_iInter fun q ↦ ?_).inter
    ((isClosed_iInter fun q ↦ ?_).inter
      ((isClosed_iInter fun 𝒜 ↦ isClosed_iInter fun ℬ ↦ isClosed_iInter fun h ↦ ?_).inter
        (isClosed_iInter fun 𝒜 ↦ isClosed_iInter fun w ↦ isClosed_iInter fun hw ↦ ?_)))
  · exact (isClosed_discrete {f : OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val |
        (OSAlgebra.degree R 𝒜.val.val q).map f.toLinearMap =
          OSAlgebra.degree R 𝒜.val.val q}).preimage
      (hstage 𝒜)
  · exact (isClosed_discrete {f : OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R]
        OSAlgebra R (twoPunctureArrangement k) |
        (OSAlgebra.degree R (twoPunctureArrangement k) q).map f.toLinearMap =
          OSAlgebra.degree R (twoPunctureArrangement k) q}).preimage htarget
  · exact (isClosed_discrete {p :
        (OSAlgebra R ℬ.val.val ≃ₐ[R] OSAlgebra R ℬ.val.val) ×
          (OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val) |
        p.1.toAlgHom.comp (OSAlgebra.map R h) =
          (OSAlgebra.map R h).comp p.2.toAlgHom}).preimage
      ((hstage ℬ).prodMk (hstage 𝒜))
  · exact (isClosed_discrete {p :
        (OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val) ×
          (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R]
            OSAlgebra R (twoPunctureArrangement k)) |
        p.1.toAlgHom.comp (w.osMap R hw) = (w.osMap R hw).comp p.2.toAlgHom}).preimage
      ((hstage 𝒜).prodMk htarget)

/-- The old quadratic diagram subgroup embeds as a closed subspace for its exact T01
topology and its original ambient topology. -/
theorem DiagramAut.isClosedEmbedding_subtype :
    @Topology.IsClosedEmbedding (DiagramAut R C S) (QuadraticAutFamily R C)
      (DiagramAut.stageTopology R C S) (DiagramAut.familyTopology R C) (fun g ↦ g.val) := by
  let : TopologicalSpace (QuadraticAutFamily R C) := DiagramAut.familyTopology R C
  exact Topology.IsClosedEmbedding.subtypeVal (DiagramAut.isClosed_subgroup R C S)

/-- The old full graded diagram subgroup embeds as a closed subspace for its exact T01
topology, without replacing any full automorphism factor. -/
theorem GradedDiagramAut.isClosedEmbedding_subtype :
    @Topology.IsClosedEmbedding (GradedDiagramAut R C S) (GradedAutFamily R C)
      (GradedDiagramAut.stageTopology R C S) (GradedDiagramAut.familyTopology R C)
      (fun g ↦ g.val) := by
  let : TopologicalSpace (GradedAutFamily R C) := GradedDiagramAut.familyTopology R C
  exact Topology.IsClosedEmbedding.subtypeVal (GradedDiagramAut.isClosed_subgroup R C S)

end OrlikSolomon.HyperplaneGT
