/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Restriction
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Quotient

/-!
# New actual cofinal scalar-quotient equivalences

These are new routine quotient congruences of the exact existing actual cofinal group
maps, with proved scalar-image equalities. The actual old scalar subgroups, quotient
carriers, quotient topology and projections are unchanged. No old cofinal quotient
equivalence is asserted to have existed. Both directions descend through Mathlib's
quotient universal properties; no closedness, K or algebraicity hypothesis is used.

`cofinalScalarQuotientContinuousEquiv` and its graded/domain counterparts retain the
literal quotient restriction on representatives and the same Galois coordinate.

Blueprint: the actual cofinal scalar-quotient clauses of T15 (`thm:t15`).
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

/-- The exact old actual cofinal group map preserves the entire literal scalar range. -/
theorem map_scalarSubgroup_cofinalRestrictionEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut.scalarSubgroup T C S).map (cofinalRestrictionEquiv T C C' S hC hS hgen
      hn).toMonoidHom =
      DiagramAut.scalarSubgroup T C' S := by
  have he : (cofinalRestrictionEquiv T C C' S hC hS hgen hn).toMonoidHom =
    DiagramAut.restrictStages T C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact cofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g
  rw [he]
  exact DiagramAut.map_scalarSubgroup_restrictStages T C C' S hC

/-- The new actual cofinal quotient equivalence is the congruence of the old group map,
with the original Mathlib quotient topologies. Blueprint: T15 (`thm:t15`). -/
def cofinalScalarQuotientContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) ≃ₜ*
      (DiagramAut T C' S ⧸ DiagramAut.scalarSubgroup T C' S) where
  toMulEquiv := QuotientGroup.congr (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T
    C' S)
      (cofinalRestrictionEquiv T C C' S hC hS hgen hn) (map_scalarSubgroup_cofinalRestrictionEquiv
        T C C' S hC hS hgen hn)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup T C S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen
        hn).continuous_toFun)
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup T C' S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen
        hn).continuous_invFun)

/-- The algebraic field is explicitly the new congruence of the exact old group map. -/
theorem cofinalScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv = QuotientGroup.congr
      (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T C' S)
      (cofinalRestrictionEquiv T C C' S hC hS hgen hn) (map_scalarSubgroup_cofinalRestrictionEquiv
        T C C' S hC hS hgen hn) := rfl

/-- A representative restricts by the existing actual stage selection and common target.
-/
theorem cofinalScalarQuotientContinuousEquiv_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap T C S
      g) =
      DiagramAut.scalarQuotientMap T C' S (DiagramAut.restrictStages T C C' S hC g) := by
  change DiagramAut.scalarQuotientMap T C' S (cofinalRestrictionEquiv T C C' S hC hS hgen hn g) = _
  rw [cofinalRestrictionEquiv_apply]

/-- The forward quotient function is literal actual scalar-quotient restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      DiagramAut.restrictStagesScalarQuotient T C C' S hC q := by
  refine Quotient.inductionOn q ?_
  intro g
  exact cofinalScalarQuotientContinuousEquiv_map T C C' S hC hS hgen hn g

/-- The whole forward function is the actual quotient map of literal restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn) =
      DiagramAut.restrictStagesScalarQuotient T C C' S hC := by
  funext q
  exact cofinalScalarQuotientContinuousEquiv_apply T C C' S hC hS hgen hn q

/-- The inverse class is represented by the exact old actual classified extension. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (DiagramAut.scalarQuotientMap T C' S g) =
      DiagramAut.scalarQuotientMap T C S ((cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g)
        := rfl

/-- Actual cofinal quotient restriction preserves the exact old Galois coordinate. -/
theorem cofinalScalarQuotientContinuousEquiv_galois [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn (cofinalScalarQuotientContinuousEquiv T C
      C' S hC hS hgen hn q) =
      DiagramAut.localScalarQuotientEquiv T C S hS hgen hn q := by
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap T C
      S g)) =
      DiagramAut.localScalarQuotientEquiv T C S hS hgen hn (DiagramAut.scalarQuotientMap T C S g)
  rw [cofinalScalarQuotientContinuousEquiv_map]
  exact DiagramAut.localScalarQuotientEquiv_restrictStages T C S C' hC hS hgen hn g

/-- The actual quotient adapter square is the exact old-adapter and pure-T12 comparison.
-/
theorem cofinalScalarQuotientContinuousEquiv_comparison [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    DiagramAut.scalarQuotientComparison T C' S (cofinalScalarQuotientContinuousEquiv T C C' S hC hS
      hgen hn q) =
      (HyperplaneGT.cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.scalarQuotientComparison T C' S
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap T C
      S g)) =
      (HyperplaneGT.cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S (DiagramAut.scalarQuotientMap T C S g))
  rw [cofinalScalarQuotientContinuousEquiv_map, DiagramAut.scalarQuotientComparison_map,
    DiagramAut.scalarQuotientComparison_map, HyperplaneGT.cofinalScalarQuotientContinuousEquiv_map]
  rw [degreeOneDiagramEquiv_restrictStages]

/-- The comparison also gives the explicit old-adapter/pure-T12 composite value. -/
theorem cofinalScalarQuotientContinuousEquiv_old_composite [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      (DiagramAut.scalarQuotientComparison T C' S).symm
      ((HyperplaneGT.cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S q)) := by
  apply (DiagramAut.scalarQuotientComparison T C' S).injective
  rw [MulEquiv.apply_symm_apply]
  exact cofinalScalarQuotientContinuousEquiv_comparison T C C' S hC hS hgen hn q

/-- The exact old actual cofinal group map preserves the entire literal scalar range. -/
theorem map_scalarSubgroup_gradedCofinalRestrictionEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut.scalarSubgroup T C S).map (gradedCofinalRestrictionEquiv T C C' S hC hS hgen
      hn).toMonoidHom =
      GradedDiagramAut.scalarSubgroup T C' S := by
  have he : (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).toMonoidHom =
    GradedDiagramAut.restrictStages T C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact gradedCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g
  rw [he]
  exact GradedDiagramAut.map_scalarSubgroup_restrictStages T C C' S hC

/-- The new actual cofinal quotient equivalence is the congruence of the old group map,
with the original Mathlib quotient topologies. Blueprint: T15 (`thm:t15`). -/
def gradedCofinalScalarQuotientContinuousEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃ₜ*
      (GradedDiagramAut T C' S ⧸ GradedDiagramAut.scalarSubgroup T C' S) where
  toMulEquiv := QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S)
    (GradedDiagramAut.scalarSubgroup T C' S)
      (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup T C S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS
        hgen hn).continuous_toFun)
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup T C' S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS
        hgen hn).continuous_invFun)

/-- The algebraic field is explicitly the new congruence of the exact old group map. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S) (GradedDiagramAut.scalarSubgroup
      T C' S)
      (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn) := rfl

/-- A representative restricts by the existing actual stage selection and common target.
-/
theorem gradedCofinalScalarQuotientContinuousEquiv_map [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
      GradedDiagramAut.scalarQuotientMap T C' S (GradedDiagramAut.restrictStages T C C' S hC g) :=
        by
  change GradedDiagramAut.scalarQuotientMap T C' S (gradedCofinalRestrictionEquiv T C C' S hC hS
    hgen hn g) = _
  rw [gradedCofinalRestrictionEquiv_apply]

/-- The forward quotient function is literal actual scalar-quotient restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      GradedDiagramAut.restrictStagesScalarQuotient T C C' S hC q := by
  refine Quotient.inductionOn q ?_
  intro g
  exact gradedCofinalScalarQuotientContinuousEquiv_map T C C' S hC hS hgen hn g

/-- The whole forward function is the actual quotient map of literal restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn) =
      GradedDiagramAut.restrictStagesScalarQuotient T C C' S hC := by
  funext q
  exact gradedCofinalScalarQuotientContinuousEquiv_apply T C C' S hC hS hgen hn q

/-- The inverse class is represented by the exact old actual classified extension. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap T C' S g) =
      GradedDiagramAut.scalarQuotientMap T C S ((gradedCofinalRestrictionEquiv T C C' S hC hS hgen
        hn).symm g) := rfl

set_option maxHeartbeats 600000 in
-- These full actual quotient comparisons elaborate inherited diagonal/cohomology carriers;
-- keep the larger budget local to the comparison proof.
/-- Actual cofinal quotient restriction preserves the exact old Galois coordinate. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_galois [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
      (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) =
      GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn q := by
  refine Quotient.inductionOn q ?_
  intro g
  change GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g)) =
      GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn
        (GradedDiagramAut.scalarQuotientMap T C S g)
  rw [gradedCofinalScalarQuotientContinuousEquiv_map]
  exact GradedDiagramAut.localScalarQuotientEquiv_restrictStages T C S C' hC hS hgen hn g

set_option maxHeartbeats 600000 in
-- These full actual quotient comparisons elaborate inherited diagonal/cohomology carriers;
-- keep the larger budget local to the comparison proof.
/-- The actual quotient adapter square is the exact old-adapter and pure-T12 comparison.
-/
theorem gradedCofinalScalarQuotientContinuousEquiv_comparison [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    GradedDiagramAut.scalarQuotientComparison T C' S (gradedCofinalScalarQuotientContinuousEquiv T
      C C' S hC hS hgen hn q) =
      (HyperplaneGT.gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change GradedDiagramAut.scalarQuotientComparison T C' S
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g)) =
      (HyperplaneGT.gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S (GradedDiagramAut.scalarQuotientMap T C S
          g))
  rw [gradedCofinalScalarQuotientContinuousEquiv_map,
    GradedDiagramAut.scalarQuotientComparison_map,
    GradedDiagramAut.scalarQuotientComparison_map,
      HyperplaneGT.gradedCofinalScalarQuotientContinuousEquiv_map]
  rw [gradedDiagramEquiv_restrictStages]

/-- The comparison also gives the explicit old-adapter/pure-T12 composite value. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_old_composite [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      (GradedDiagramAut.scalarQuotientComparison T C' S).symm
      ((HyperplaneGT.gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S q)) := by
  apply (GradedDiagramAut.scalarQuotientComparison T C' S).injective
  rw [MulEquiv.apply_symm_apply]
  exact gradedCofinalScalarQuotientContinuousEquiv_comparison T C C' S hC hS hgen hn q

/-- The exact old actual cofinal group map preserves the entire literal scalar range. -/
theorem map_scalarSubgroup_domainCofinalRestrictionEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut.scalarSubgroup T C S).map (domainCofinalRestrictionEquiv T C C' S hC hS hgen
      hn).toMonoidHom =
      DiagramAut.scalarSubgroup T C' S := by
  have he : (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).toMonoidHom =
    DiagramAut.restrictStages T C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact domainCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g
  rw [he]
  exact DiagramAut.map_scalarSubgroup_restrictStages T C C' S hC

/-- The new actual cofinal quotient equivalence is the congruence of the old group map,
with the original Mathlib quotient topologies. Blueprint: T15 (`thm:t15`). -/
def domainCofinalScalarQuotientContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) ≃ₜ*
      (DiagramAut T C' S ⧸ DiagramAut.scalarSubgroup T C' S) where
  toMulEquiv := QuotientGroup.congr (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T
    C' S)
      (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainCofinalRestrictionEquiv T C C' S hC hS hgen hn)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup T C S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (domainCofinalRestrictionContinuousEquiv T C C' S hC hS
        hgen hn).continuous_toFun)
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup T C' S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (domainCofinalRestrictionContinuousEquiv T C C' S hC hS
        hgen hn).continuous_invFun)

/-- The algebraic field is explicitly the new congruence of the exact old group map. -/
theorem domainCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T C' S)
      (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainCofinalRestrictionEquiv T C C' S hC hS hgen hn) := rfl

/-- A representative restricts by the existing actual stage selection and common target.
-/
theorem domainCofinalScalarQuotientContinuousEquiv_map [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap
      T C S g) =
      DiagramAut.scalarQuotientMap T C' S (DiagramAut.restrictStages T C C' S hC g) := by
  change DiagramAut.scalarQuotientMap T C' S (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn
    g) = _
  rw [domainCofinalRestrictionEquiv_apply]

/-- The forward quotient function is literal actual scalar-quotient restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      DiagramAut.restrictStagesScalarQuotient T C C' S hC q := by
  refine Quotient.inductionOn q ?_
  intro g
  exact domainCofinalScalarQuotientContinuousEquiv_map T C C' S hC hS hgen hn g

/-- The whole forward function is the actual quotient map of literal restriction. -/
theorem domainCofinalScalarQuotientContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn) =
      DiagramAut.restrictStagesScalarQuotient T C C' S hC := by
  funext q
  exact domainCofinalScalarQuotientContinuousEquiv_apply T C C' S hC hS hgen hn q

/-- The inverse class is represented by the exact old actual classified extension. -/
theorem domainCofinalScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C' S) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (DiagramAut.scalarQuotientMap T C' S g) =
      DiagramAut.scalarQuotientMap T C S ((domainCofinalRestrictionEquiv T C C' S hC hS hgen
        hn).symm g) := rfl

/-- Actual cofinal quotient restriction preserves the exact old Galois coordinate. -/
theorem domainCofinalScalarQuotientContinuousEquiv_galois [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
      (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) =
      DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q := by
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientMap T C S g)) =
      DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn (DiagramAut.scalarQuotientMap T C S g)
  rw [domainCofinalScalarQuotientContinuousEquiv_map]
  exact DiagramAut.domainScalarQuotientEquiv_restrictStages T C S C' hC hS hgen hn g

/-- The actual quotient adapter square is the exact old-adapter and pure-T12 comparison.
-/
theorem domainCofinalScalarQuotientContinuousEquiv_comparison [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    DiagramAut.scalarQuotientComparison T C' S (domainCofinalScalarQuotientContinuousEquiv T C C' S
      hC hS hgen hn q) =
      (HyperplaneGT.domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.scalarQuotientComparison T C' S
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientMap T C S g)) =
      (HyperplaneGT.domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S (DiagramAut.scalarQuotientMap T C S g))
  rw [domainCofinalScalarQuotientContinuousEquiv_map, DiagramAut.scalarQuotientComparison_map,
    DiagramAut.scalarQuotientComparison_map,
      HyperplaneGT.domainCofinalScalarQuotientContinuousEquiv_map]
  rw [degreeOneDiagramEquiv_restrictStages]

/-- The comparison also gives the explicit old-adapter/pure-T12 composite value. -/
theorem domainCofinalScalarQuotientContinuousEquiv_old_composite [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      (DiagramAut.scalarQuotientComparison T C' S).symm
      ((HyperplaneGT.domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (DiagramAut.scalarQuotientComparison T C S q)) := by
  apply (DiagramAut.scalarQuotientComparison T C' S).injective
  rw [MulEquiv.apply_symm_apply]
  exact domainCofinalScalarQuotientContinuousEquiv_comparison T C C' S hC hS hgen hn q

/-- The exact old actual cofinal group map preserves the entire literal scalar range. -/
theorem map_scalarSubgroup_domainGradedCofinalRestrictionEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut.scalarSubgroup T C S).map (domainGradedCofinalRestrictionEquiv T C C' S hC hS
      hgen hn).toMonoidHom =
      GradedDiagramAut.scalarSubgroup T C' S := by
  have he : (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).toMonoidHom =
    GradedDiagramAut.restrictStages T C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact domainGradedCofinalRestrictionEquiv_apply T C C' S hC hS hgen hn g
  rw [he]
  exact GradedDiagramAut.map_scalarSubgroup_restrictStages T C C' S hC

/-- The new actual cofinal quotient equivalence is the congruence of the old group map,
with the original Mathlib quotient topologies. Blueprint: T15 (`thm:t15`). -/
def domainGradedCofinalScalarQuotientContinuousEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃ₜ*
      (GradedDiagramAut T C' S ⧸ GradedDiagramAut.scalarSubgroup T C' S) where
  toMulEquiv := QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S)
    (GradedDiagramAut.scalarSubgroup T C' S)
      (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup T C S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC
        hS hgen hn).continuous_toFun)
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup T C' S)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC
        hS hgen hn).continuous_invFun)

/-- The algebraic field is explicitly the new congruence of the exact old group map. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).toMulEquiv =
      QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S) (GradedDiagramAut.scalarSubgroup
      T C' S)
      (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn) := rfl

/-- A representative restricts by the existing actual stage selection and common target.
-/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_map [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
      GradedDiagramAut.scalarQuotientMap T C' S (GradedDiagramAut.restrictStages T C C' S hC g) :=
        by
  change GradedDiagramAut.scalarQuotientMap T C' S (domainGradedCofinalRestrictionEquiv T C C' S hC
    hS hgen hn g) = _
  rw [domainGradedCofinalRestrictionEquiv_apply]

/-- The forward quotient function is literal actual scalar-quotient restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_apply [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      GradedDiagramAut.restrictStagesScalarQuotient T C C' S hC q := by
  refine Quotient.inductionOn q ?_
  intro g
  exact domainGradedCofinalScalarQuotientContinuousEquiv_map T C C' S hC hS hgen hn g

/-- The whole forward function is the actual quotient map of literal restriction. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_coe [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn) =
      GradedDiagramAut.restrictStagesScalarQuotient T C C' S hC := by
  funext q
  exact domainGradedCofinalScalarQuotientContinuousEquiv_apply T C C' S hC hS hgen hn q

/-- The inverse class is represented by the exact old actual classified extension. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C' S)
      :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap T C' S g) =
      GradedDiagramAut.scalarQuotientMap T C S ((domainGradedCofinalRestrictionEquiv T C C' S hC hS
        hgen hn).symm g) := rfl

set_option maxHeartbeats 600000 in
-- These full actual quotient comparisons elaborate inherited diagonal/cohomology carriers;
-- keep the larger budget local to the comparison proof.
/-- Actual cofinal quotient restriction preserves the exact old Galois coordinate. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_galois [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
      (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) =
      GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q := by
  refine Quotient.inductionOn q ?_
  intro g
  change GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g)) =
      GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn
        (GradedDiagramAut.scalarQuotientMap T C S g)
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_map]
  exact GradedDiagramAut.domainScalarQuotientEquiv_restrictStages T C S C' hC hS hgen hn g

set_option maxHeartbeats 600000 in
-- These full actual quotient comparisons elaborate inherited diagonal/cohomology carriers;
-- keep the larger budget local to the comparison proof.
/-- The actual quotient adapter square is the exact old-adapter and pure-T12 comparison.
-/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_comparison [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    GradedDiagramAut.scalarQuotientComparison T C' S
      (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q) =
      (HyperplaneGT.domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change GradedDiagramAut.scalarQuotientComparison T C' S
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g)) =
      (HyperplaneGT.domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S (GradedDiagramAut.scalarQuotientMap T C S
          g))
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_map,
    GradedDiagramAut.scalarQuotientComparison_map,
    GradedDiagramAut.scalarQuotientComparison_map,
      HyperplaneGT.domainGradedCofinalScalarQuotientContinuousEquiv_map]
  rw [gradedDiagramEquiv_restrictStages]

/-- The comparison also gives the explicit old-adapter/pure-T12 composite value. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_old_composite [IsDomain R] (hC : C'.stages
  ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn q =
      (GradedDiagramAut.scalarQuotientComparison T C' S).symm
      ((HyperplaneGT.domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn)
        (GradedDiagramAut.scalarQuotientComparison T C S q)) := by
  apply (GradedDiagramAut.scalarQuotientComparison T C' S).injective
  rw [MulEquiv.apply_symm_apply]
  exact domainGradedCofinalScalarQuotientContinuousEquiv_comparison T C C' S hC hS hgen hn q

/-- The inverse on arbitrary classes is exactly the inverse of the disclosed new
congruence of the original group equivalence. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C' S ⧸ DiagramAut.scalarSubgroup T C' S) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T C' S)
        (cofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_cofinalRestrictionEquiv T C C' S hC hS hgen hn)).symm q := rfl

/-- The same actual Galois family represents the scalar class in the cofinal subsystem.
-/
theorem cofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsLocalRing R] (hC : C'.stages
  ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn (DiagramAut.scalarQuotientSection T
      C S σ) =
      DiagramAut.scalarQuotientSection T C' S σ := by
  apply (DiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  rw [cofinalScalarQuotientContinuousEquiv_galois, DiagramAut.localScalarQuotientEquiv_section,
    DiagramAut.localScalarQuotientEquiv_section]

/-- The inverse on arbitrary classes is exactly the inverse of the disclosed new
congruence of the original group equivalence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C' S ⧸ GradedDiagramAut.scalarSubgroup T C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S) (GradedDiagramAut.scalarSubgroup
        T C' S)
        (gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)).symm q := rfl

/-- The same actual Galois family represents the scalar class in the cofinal subsystem.
-/
theorem gradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsLocalRing R] (hC :
  C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientSection T C S σ) =
      GradedDiagramAut.scalarQuotientSection T C' S σ := by
  apply (GradedDiagramAut.localScalarQuotientEquiv T C' S hS hgen hn).injective
  rw [gradedCofinalScalarQuotientContinuousEquiv_galois,
    GradedDiagramAut.localScalarQuotientEquiv_section,
    GradedDiagramAut.localScalarQuotientEquiv_section]

/-- The inverse on arbitrary classes is exactly the inverse of the disclosed new
congruence of the original group equivalence. -/
theorem domainCofinalScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C' S ⧸ DiagramAut.scalarSubgroup T C' S) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (DiagramAut.scalarSubgroup T C S) (DiagramAut.scalarSubgroup T C' S)
        (domainCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainCofinalRestrictionEquiv T C C' S hC hS hgen hn)).symm q := rfl

/-- The same actual Galois family represents the scalar class in the cofinal subsystem.
-/
theorem domainCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsDomain R] (hC :
  C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientSection T C S σ) =
      DiagramAut.scalarQuotientSection T C' S σ := by
  apply (DiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  rw [domainCofinalScalarQuotientContinuousEquiv_galois,
    DiagramAut.domainScalarQuotientEquiv_section,
    DiagramAut.domainScalarQuotientEquiv_section]

/-- The inverse on arbitrary classes is exactly the inverse of the disclosed new
congruence of the original group equivalence. -/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hC : C'.stages ⊆
  C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C' S ⧸ GradedDiagramAut.scalarSubgroup T C' S) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm q =
      (QuotientGroup.congr (GradedDiagramAut.scalarSubgroup T C S) (GradedDiagramAut.scalarSubgroup
        T C' S)
        (domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)
        (map_scalarSubgroup_domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn)).symm q :=
          rfl

/-- The same actual Galois family represents the scalar class in the cofinal subsystem.
-/
theorem domainGradedCofinalScalarQuotientContinuousEquiv_scalarQuotientSection [IsDomain R] (hC :
  C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientSection T C S σ) =
      GradedDiagramAut.scalarQuotientSection T C' S σ := by
  apply (GradedDiagramAut.domainScalarQuotientEquiv T C' S hS hgen hn).injective
  rw [domainGradedCofinalScalarQuotientContinuousEquiv_galois,
    GradedDiagramAut.domainScalarQuotientEquiv_section,
    GradedDiagramAut.domainScalarQuotientEquiv_section]

end OrlikSolomon.HyperplaneGT.Cohomology
