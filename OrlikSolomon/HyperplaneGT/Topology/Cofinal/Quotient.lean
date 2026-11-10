/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Quotient.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Cofinal restriction on the actual scalar quotients

Literal stage restriction preserves the full image of the existing scalar homomorphism.
It therefore descends to the original Mathlib scalar quotients over every commutative ring.
The old local and domain group equivalences induce quotient equivalences; continuity in
both directions follows from the actual quotient universal property. No scalar closedness,
Krull comparison or transported topology is needed.

These are new wrappers of the quotient equivalences induced by the old cofinal maps,
with exact `QuotientGroup.congr` descriptions. They retain the same target on representatives.
Expansion equations are plain rewrites, preserving ordinary inverse cancellation.

Blueprint: T12 (`thm:t12`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Topology
open scoped FiniteStageTopology

/-- Both directions descend through the actual quotient universal properties, without
closedness hypotheses or a transported topology. -/
private theorem continuous_quotient_congr {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (H : Subgroup A) (K : Subgroup B)
    [H.Normal] [K.Normal] (e : A ≃ₜ* B) (he : H.map e.toMulEquiv = K) :
    Continuous (QuotientGroup.congr H K e.toMulEquiv he) ∧
      Continuous (QuotientGroup.congr H K e.toMulEquiv he).symm := by
  constructor
  · exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.continuous_toFun)
  · exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.continuous_invFun)

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R]
  (C C' : CofinalSystem k₀ k n) (S : Set k₀)

/-- The scalar quotient equivalence induced by the exact old cofinal group equivalence,
with continuity in both original quotient topologies. Blueprint: T12 (`thm:t12`). -/
def cofinalScalarQuotientContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) ≃ₜ*
      (DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S) where
  toMulEquiv := QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup
    R C' S)
    (cofinalRestrictionEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_cofinalRestrictionEquiv R C C' S hC hS hgen hn)
  continuous_toFun := by
    exact (continuous_quotient_congr (DiagramAut.scalarSubgroup R C S)
    (DiagramAut.scalarSubgroup R C' S) (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_cofinalRestrictionEquiv R C C' S hC hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_quotient_congr (DiagramAut.scalarSubgroup R C S)
    (DiagramAut.scalarSubgroup R C' S) (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_cofinalRestrictionEquiv R C C' S hC hS hgen hn)).2

/-- Forgetting topology gives the exact induced old cofinal quotient equivalence. -/
theorem cofinalScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C' S)
        (cofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_cofinalRestrictionEquiv R C C' S hC hS hgen hn) := rfl

/-- On representatives the new homeomorphism is the literal quotient restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap R C
      S g) =
      DiagramAut.scalarQuotientMap R C' S (DiagramAut.restrictStages R C C' S hC g) := by
  change DiagramAut.scalarQuotientMap R C' S (cofinalRestrictionEquiv R C C' S hC hS hgen hn g) = _
  rw [cofinalRestrictionEquiv_apply]

/-- The forward map on scalar classes is exactly the generic literal quotient homomorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :
    cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q =
      DiagramAut.restrictStagesScalarQuotient R C C' S hC q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  exact cofinalScalarQuotientContinuousEquiv_map R C C' S hC hS hgen hn g

/-- The underlying function is the unchanged literal quotient restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn : (DiagramAut R C S ⧸
      DiagramAut.scalarSubgroup R C S) →
      (DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S)) =
      DiagramAut.restrictStagesScalarQuotient R C C' S hC :=
  funext (cofinalScalarQuotientContinuousEquiv_apply R C C' S hC hS hgen hn)

/-- The inverse is the class of the original classified extension of a representative. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
      (DiagramAut.scalarQuotientMap R C' S g) =
      DiagramAut.scalarQuotientMap R C S ((cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
        g) := rfl

/-- The same direct Galois family represents the corresponding class in the subsystem. -/
theorem cofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsLocalRing R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn (DiagramAut.scalarQuotientSection
      R C S σ) =
      DiagramAut.scalarQuotientSection R C' S σ := by
  rw [DiagramAut.scalarQuotientSection_apply, cofinalScalarQuotientContinuousEquiv_map]
  rw [DiagramAut.restrictStages_galoisQuadraticAut]
  rfl

/-- The descended Galois coordinate is unchanged on the actual scalar quotients. -/
theorem cofinalScalarQuotientContinuousEquiv_galois [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :
    DiagramAut.scalarQuotientEquiv R C' S hS hgen hn (cofinalScalarQuotientContinuousEquiv R C C'
      S hC hS hgen hn q) =
      DiagramAut.scalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨σ, rfl⟩ := (DiagramAut.scalarQuotientEquiv R C S hS hgen hn).symm.surjective q
  rw [DiagramAut.scalarQuotientEquiv_symm_apply,
    cofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    DiagramAut.scalarQuotientEquiv_section]
  exact ((DiagramAut.scalarQuotientEquiv R C S hS hgen hn).apply_symm_apply σ).symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  change cofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn
    (DiagramAut.scalarQuotientMap R C S g) = DiagramAut.scalarQuotientMap R C S g
  rw [cofinalScalarQuotientContinuousEquiv_map, DiagramAut.restrictStages_refl]

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem cofinalScalarQuotientContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).trans
      (cofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn) =
      cofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  change cofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap R
      C S g)) =
    cofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn
      (DiagramAut.scalarQuotientMap R C S g)
  rw [cofinalScalarQuotientContinuousEquiv_map, cofinalScalarQuotientContinuousEquiv_map,
    cofinalScalarQuotientContinuousEquiv_map,
    DiagramAut.restrictStages_trans]

/-- The scalar quotient equivalence induced by the exact old cofinal group equivalence,
with continuity in both original quotient topologies. Blueprint: T12 (`thm:t12`). -/
def gradedCofinalScalarQuotientContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃ₜ*
      (GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) where
  toMulEquiv := QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S)
    (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
  continuous_toFun := by
    exact (continuous_quotient_congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S) (gradedCofinalRestrictionContinuousEquiv R C C' S hC
      hS hgen hn)
    (map_scalarSubgroup_gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_quotient_congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S) (gradedCofinalRestrictionContinuousEquiv R C C' S hC
      hS hgen hn)
    (map_scalarSubgroup_gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).2

/-- Forgetting topology gives the exact induced old cofinal quotient equivalence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
        (GradedDiagramAut.scalarSubgroup R C' S)
        (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn) := rfl

/-- On representatives the new homeomorphism is the literal quotient restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g) =
      GradedDiagramAut.scalarQuotientMap R C' S (GradedDiagramAut.restrictStages R C C' S hC g)
        := by
  change GradedDiagramAut.scalarQuotientMap R C' S (gradedCofinalRestrictionEquiv R C C' S hC hS
    hgen hn g) = _
  rw [gradedCofinalRestrictionEquiv_apply]

/-- The forward map on scalar classes is exactly the generic literal quotient homomorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q =
      GradedDiagramAut.restrictStagesScalarQuotient R C C' S hC q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  exact gradedCofinalScalarQuotientContinuousEquiv_map R C C' S hC hS hgen hn g

/-- The underlying function is the unchanged literal quotient restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn : (GradedDiagramAut R C S
      ⧸ GradedDiagramAut.scalarSubgroup R C S) →
      (GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S)) =
      GradedDiagramAut.restrictStagesScalarQuotient R C C' S hC :=
  funext (gradedCofinalScalarQuotientContinuousEquiv_apply R C C' S hC hS hgen hn)

/-- The inverse is the class of the original classified extension of a representative. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap R C' S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((gradedCofinalRestrictionEquiv R C C' S hC hS
        hgen hn).symm g) := rfl

/-- The same direct Galois family represents the corresponding class in the subsystem. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsLocalRing R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientSection R C S σ) =
      GradedDiagramAut.scalarQuotientSection R C' S σ := by
  rw [GradedDiagramAut.scalarQuotientSection_apply, gradedCofinalScalarQuotientContinuousEquiv_map]
  rw [GradedDiagramAut.restrictStages_galoisGradedAut]
  rfl

/-- The descended Galois coordinate is unchanged on the actual scalar quotients. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_galois [IsLocalRing R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    GradedDiagramAut.scalarQuotientEquiv R C' S hS hgen hn
      (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) =
      GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨σ, rfl⟩ := (GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn).symm.surjective q
  rw [GradedDiagramAut.scalarQuotientEquiv_symm_apply,
    gradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    GradedDiagramAut.scalarQuotientEquiv_section]
  exact ((GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn).apply_symm_apply σ).symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_refl [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change gradedCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn
    (GradedDiagramAut.scalarQuotientMap R C S g) = GradedDiagramAut.scalarQuotientMap R C S g
  rw [gradedCofinalScalarQuotientContinuousEquiv_map, GradedDiagramAut.restrictStages_refl]

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_trans [IsLocalRing R] (C'' : CofinalSystem k₀
    k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).trans
      (gradedCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn) =
      gradedCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change gradedCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)) =
    gradedCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)
  rw [gradedCofinalScalarQuotientContinuousEquiv_map,
    gradedCofinalScalarQuotientContinuousEquiv_map, gradedCofinalScalarQuotientContinuousEquiv_map,
    GradedDiagramAut.restrictStages_trans]

/-- The scalar quotient equivalence induced by the exact old cofinal group equivalence,
with continuity in both original quotient topologies. Blueprint: T12 (`thm:t12`). -/
def domainCofinalScalarQuotientContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) ≃ₜ*
      (DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S) where
  toMulEquiv := QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup
    R C' S)
    (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)
  continuous_toFun := by
    exact (continuous_quotient_congr (DiagramAut.scalarSubgroup R C S)
    (DiagramAut.scalarSubgroup R C' S) (domainCofinalRestrictionContinuousEquiv R C C' S hC hS
      hgen hn)
    (map_scalarSubgroup_domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_quotient_congr (DiagramAut.scalarSubgroup R C S)
    (DiagramAut.scalarSubgroup R C' S) (domainCofinalRestrictionContinuousEquiv R C C' S hC hS
      hgen hn)
    (map_scalarSubgroup_domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)).2

/-- Forgetting topology gives the exact induced old cofinal quotient equivalence. -/
theorem domainCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C' S)
        (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainCofinalRestrictionEquiv R C C' S hC hS hgen hn) := rfl

/-- On representatives the new homeomorphism is the literal quotient restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_map [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientMap R C S g) =
      DiagramAut.scalarQuotientMap R C' S (DiagramAut.restrictStages R C C' S hC g) := by
  change DiagramAut.scalarQuotientMap R C' S (domainCofinalRestrictionEquiv R C C' S hC hS hgen
    hn g) = _
  rw [domainCofinalRestrictionEquiv_apply]

/-- The forward map on scalar classes is exactly the generic literal quotient homomorphism. -/
theorem domainCofinalScalarQuotientContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q =
      DiagramAut.restrictStagesScalarQuotient R C C' S hC q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  exact domainCofinalScalarQuotientContinuousEquiv_map R C C' S hC hS hgen hn g

/-- The underlying function is the unchanged literal quotient restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn : (DiagramAut R C S ⧸
      DiagramAut.scalarSubgroup R C S) →
      (DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S)) =
      DiagramAut.restrictStagesScalarQuotient R C C' S hC :=
  funext (domainCofinalScalarQuotientContinuousEquiv_apply R C C' S hC hS hgen hn)

/-- The inverse is the class of the original classified extension of a representative. -/
theorem domainCofinalScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C' S) :
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
      (DiagramAut.scalarQuotientMap R C' S g) =
      DiagramAut.scalarQuotientMap R C S ((domainCofinalRestrictionEquiv R C C' S hC hS hgen
        hn).symm g) := rfl

/-- The same direct Galois family represents the corresponding class in the subsystem. -/
theorem domainCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsDomain R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientSection R C S σ) =
      DiagramAut.scalarQuotientSection R C' S σ := by
  rw [DiagramAut.scalarQuotientSection_apply, domainCofinalScalarQuotientContinuousEquiv_map]
  rw [DiagramAut.restrictStages_galoisQuadraticAut]
  rfl

/-- The descended Galois coordinate is unchanged on the actual scalar quotients. -/
theorem domainCofinalScalarQuotientContinuousEquiv_galois [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :
    DiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn
      (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) =
      DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨σ, rfl⟩ := (DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).symm.surjective q
  rw [DiagramAut.domainScalarQuotientEquiv_symm_apply,
    domainCofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    DiagramAut.domainScalarQuotientEquiv_section]
  exact ((DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).apply_symm_apply σ).symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem domainCofinalScalarQuotientContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  change domainCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn
    (DiagramAut.scalarQuotientMap R C S g) = DiagramAut.scalarQuotientMap R C S g
  rw [domainCofinalScalarQuotientContinuousEquiv_map, DiagramAut.restrictStages_refl]

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem domainCofinalScalarQuotientContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).trans
      (domainCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn) =
      domainCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (DiagramAut.scalarSubgroup R C S) q
  change domainCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientMap R C S g)) =
    domainCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn
      (DiagramAut.scalarQuotientMap R C S g)
  rw [domainCofinalScalarQuotientContinuousEquiv_map,
    domainCofinalScalarQuotientContinuousEquiv_map, domainCofinalScalarQuotientContinuousEquiv_map,
    DiagramAut.restrictStages_trans]

/-- The scalar quotient equivalence induced by the exact old cofinal group equivalence,
with continuity in both original quotient topologies. Blueprint: T12 (`thm:t12`). -/
def domainGradedCofinalScalarQuotientContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃ₜ*
      (GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) where
  toMulEquiv := QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S)
    (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
    (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
  continuous_toFun := by
    exact (continuous_quotient_congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S) (domainGradedCofinalRestrictionContinuousEquiv R C
      C' S hC hS hgen hn)
    (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_quotient_congr (GradedDiagramAut.scalarSubgroup R C S)
    (GradedDiagramAut.scalarSubgroup R C' S) (domainGradedCofinalRestrictionContinuousEquiv R C
      C' S hC hS hgen hn)
    (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).2

/-- Forgetting topology gives the exact induced old cofinal quotient equivalence. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages
    ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
        (GradedDiagramAut.scalarSubgroup R C' S)
        (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn) := rfl

/-- On representatives the new homeomorphism is the literal quotient restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_map [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g) =
      GradedDiagramAut.scalarQuotientMap R C' S (GradedDiagramAut.restrictStages R C C' S hC g)
        := by
  change GradedDiagramAut.scalarQuotientMap R C' S (domainGradedCofinalRestrictionEquiv R C C' S
    hC hS hgen hn g) = _
  rw [domainGradedCofinalRestrictionEquiv_apply]

/-- The forward map on scalar classes is exactly the generic literal quotient homomorphism. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q =
      GradedDiagramAut.restrictStagesScalarQuotient R C C' S hC q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  exact domainGradedCofinalScalarQuotientContinuousEquiv_map R C C' S hC hS hgen hn g

/-- The underlying function is the unchanged literal quotient restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn : (GradedDiagramAut
      R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) →
      (GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S)) =
      GradedDiagramAut.restrictStagesScalarQuotient R C C' S hC :=
  funext (domainGradedCofinalScalarQuotientContinuousEquiv_apply R C C' S hC hS hgen hn)

/-- The inverse is the class of the original classified extension of a representative. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C' S) :
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap R C' S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((domainGradedCofinalRestrictionEquiv R C C' S hC
        hS hgen hn).symm g) := rfl

/-- The same direct Galois family represents the corresponding class in the subsystem. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsDomain R] (hC :
    C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientSection R C S σ) =
      GradedDiagramAut.scalarQuotientSection R C' S σ := by
  rw [GradedDiagramAut.scalarQuotientSection_apply,
    domainGradedCofinalScalarQuotientContinuousEquiv_map]
  rw [GradedDiagramAut.restrictStages_galoisGradedAut]
  rfl

/-- The descended Galois coordinate is unchanged on the actual scalar quotients. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_galois [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    GradedDiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn
      (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) =
      GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨σ, rfl⟩ := (GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).symm.surjective q
  rw [GradedDiagramAut.domainScalarQuotientEquiv_symm_apply,
    domainGradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    GradedDiagramAut.domainScalarQuotientEquiv_section]
  exact ((GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).apply_symm_apply σ).symm

/-- Quotient restriction to the same family is the identity homeomorphism. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_refl [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change domainGradedCofinalScalarQuotientContinuousEquiv R C C S (Set.Subset.refl _) hS hgen hn
    (GradedDiagramAut.scalarQuotientMap R C S g) = GradedDiagramAut.scalarQuotientMap R C S g
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_map, GradedDiagramAut.restrictStages_refl]

/-- Successive literal cofinal scalar-quotient restrictions compose unchanged. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_trans [IsDomain R] (C'' : CofinalSystem
    k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).trans
      (domainGradedCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn) =
      domainGradedCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change domainGradedCofinalScalarQuotientContinuousEquiv R C' C'' S hC' hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)) =
    domainGradedCofinalScalarQuotientContinuousEquiv R C C'' S (hC'.trans hC) hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_map,
    domainGradedCofinalScalarQuotientContinuousEquiv_map,
    domainGradedCofinalScalarQuotientContinuousEquiv_map,
    GradedDiagramAut.restrictStages_trans]

/-- The inverse on arbitrary scalar classes is exactly the inverse of the induced old
multiplicative quotient equivalence. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S) :
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C' S)
        (cofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_cofinalRestrictionEquiv R C C' S hC hS hgen hn)).symm q := rfl

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem cofinalScalarQuotientContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((cofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (DiagramAut.scalarQuotientEquiv R C S hS hgen hn).trans
        (DiagramAut.scalarQuotientEquiv R C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (DiagramAut.scalarQuotientEquiv R C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change DiagramAut.scalarQuotientEquiv R C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((cofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [cofinalScalarQuotientContinuousEquiv_galois]
  have he := cofinalScalarQuotientContinuousEquiv_galois R (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((cofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- The inverse on arbitrary scalar classes is exactly the inverse of the induced old
multiplicative quotient equivalence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
        (GradedDiagramAut.scalarSubgroup R C' S)
        (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).symm q := rfl

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((gradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn).trans
        (GradedDiagramAut.scalarQuotientEquiv R C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (GradedDiagramAut.scalarQuotientEquiv R C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change GradedDiagramAut.scalarQuotientEquiv R C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((gradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [gradedCofinalScalarQuotientContinuousEquiv_galois]
  have he := gradedCofinalScalarQuotientContinuousEquiv_galois R (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((gradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- The inverse on arbitrary scalar classes is exactly the inverse of the induced old
multiplicative quotient equivalence. -/
theorem domainCofinalScalarQuotientContinuousEquiv_symm_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S) :
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (DiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C' S)
        (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainCofinalRestrictionEquiv R C C' S hC hS hgen hn)).symm q := rfl

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem domainCofinalScalarQuotientContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (DiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change DiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((domainCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [domainCofinalScalarQuotientContinuousEquiv_galois]
  have he := domainCofinalScalarQuotientContinuousEquiv_galois R (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((domainCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- The inverse on arbitrary scalar classes is exactly the inverse of the induced old
multiplicative quotient equivalence. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_symm_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) :
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S)
        (GradedDiagramAut.scalarSubgroup R C' S)
        (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn)).symm q
          := rfl

/-- Comparing unrelated selected families through their union preserves the exact old
Galois quotient coordinate, without arrangement-union closure. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainGradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainGradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn).trans
        (GradedDiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro q
  apply (GradedDiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change GradedDiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C' S
      (C.stages_subset_unionStages_right C') hS hgen hn
      ((domainGradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm q)) = _
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_galois]
  have he := domainGradedCofinalScalarQuotientContinuousEquiv_galois R (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
    ((domainGradedCofinalScalarQuotientContinuousEquiv R (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm q)
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Local and domain scalar-quotient restriction agree on their coefficient overlap. -/
theorem domainCofinalScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn =
      cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro q
  rw [domainCofinalScalarQuotientContinuousEquiv_apply, cofinalScalarQuotientContinuousEquiv_apply]

/-- Local and domain scalar-quotient restriction agree on their coefficient overlap. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn =
      gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro q
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_apply,
    gradedCofinalScalarQuotientContinuousEquiv_apply]

/-- Cofinal scalar-quotient restriction commutes with the exact old degree-one quotient map. -/
theorem cofinalScalarQuotientContinuousEquiv_restriction [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (scalarQuotientRestrictionEquiv R C S hS hgen hn q) =
      scalarQuotientRestrictionEquiv R C' S hS hgen hn
        (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) := by
  apply (DiagramAut.scalarQuotientEquiv R C' S hS hgen hn).injective
  rw [cofinalScalarQuotientContinuousEquiv_galois, scalarQuotientEquiv_restriction,
    scalarQuotientEquiv_restriction, gradedCofinalScalarQuotientContinuousEquiv_galois]

/-- Cofinal scalar-quotient restriction commutes with the exact old degree-one quotient map. -/
theorem domainCofinalScalarQuotientContinuousEquiv_restriction [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
      (domainScalarQuotientRestrictionEquiv R C S hS hgen hn q) =
      domainScalarQuotientRestrictionEquiv R C' S hS hgen hn
        (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) := by
  apply (DiagramAut.domainScalarQuotientEquiv R C' S hS hgen hn).injective
  rw [domainCofinalScalarQuotientContinuousEquiv_galois, domainScalarQuotientEquiv_restriction,
    domainScalarQuotientEquiv_restriction, domainGradedCofinalScalarQuotientContinuousEquiv_galois]

end OrlikSolomon.HyperplaneGT
