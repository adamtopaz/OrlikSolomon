/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Restriction
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Literal cofinal restriction on scalar classes

The original scalar ranges map onto the corresponding subsystem scalar ranges, so literal
stage selection descends to Mathlib's actual quotient groups. This continuity result uses
arbitrary commutative coefficients and all dimensions. Scalar compatibility for the four
old classified group equivalences is recorded without changing any underlying map.

Blueprint: the literal quotient-map part of T12 (`thm:t12`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Topology
open scoped FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R]
  (C C' : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- Literal restriction carries the whole scalar range onto the subsystem scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup R C S).map (restrictStages R C C' S hC) =
      scalarSubgroup R C' S := by
  ext g
  constructor
  · rintro ⟨h, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarQuadraticAut R C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarQuadraticAut R C S a, ⟨a, rfl⟩,
      restrictStages_scalarQuadraticAut R C C' S hC a⟩

/-- The literal stage restriction on the original quotient by the scalar range. -/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (DiagramAut R C S ⧸ scalarSubgroup R C S) →*
      (DiagramAut R C' S ⧸ scalarSubgroup R C' S) :=
  QuotientGroup.map (scalarSubgroup R C S) (scalarSubgroup R C' S)
    (restrictStages R C C' S hC)
    ((map_scalarSubgroup_restrictStages R C C' S hC) ▸
      (scalarSubgroup R C S).le_comap_map (restrictStages R C C' S hC))

/-- The descended map is precisely the class of the literal restriction of a representative. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut R C S) :
    restrictStagesScalarQuotient R C C' S hC (scalarQuotientMap R C S g) =
      scalarQuotientMap R C' S (restrictStages R C C' S hC g) := rfl

/-- Literal scalar-quotient restriction is continuous in Mathlib's actual quotient topology
for arbitrary coefficients and dimensions. Blueprint: T12 (`thm:t12`). -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient R C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages R C C' S hC))

end DiagramAut

namespace GradedDiagramAut

/-- Literal restriction carries the whole scalar range onto the subsystem scalar range. -/
theorem map_scalarSubgroup_restrictStages (hC : C'.stages ⊆ C.stages) :
    (scalarSubgroup R C S).map (restrictStages R C C' S hC) =
      scalarSubgroup R C' S := by
  ext g
  constructor
  · rintro ⟨h, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictStages_scalarGradedAut R C C' S hC a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAut R C S a, ⟨a, rfl⟩,
      restrictStages_scalarGradedAut R C C' S hC a⟩

/-- The literal stage restriction on the original quotient by the scalar range. -/
def restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    (GradedDiagramAut R C S ⧸ scalarSubgroup R C S) →*
      (GradedDiagramAut R C' S ⧸ scalarSubgroup R C' S) :=
  QuotientGroup.map (scalarSubgroup R C S) (scalarSubgroup R C' S)
    (restrictStages R C C' S hC)
    ((map_scalarSubgroup_restrictStages R C C' S hC) ▸
      (scalarSubgroup R C S).le_comap_map (restrictStages R C C' S hC))

/-- The descended map is precisely the class of the literal restriction of a representative. -/
theorem restrictStagesScalarQuotient_map (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut R C S) :
    restrictStagesScalarQuotient R C C' S hC (scalarQuotientMap R C S g) =
      scalarQuotientMap R C' S (restrictStages R C C' S hC g) := rfl

/-- Literal scalar-quotient restriction is continuous in Mathlib's actual quotient topology
for arbitrary coefficients and dimensions. Blueprint: T12 (`thm:t12`). -/
theorem continuous_restrictStagesScalarQuotient (hC : C'.stages ⊆ C.stages) :
    Continuous (restrictStagesScalarQuotient R C C' S hC) :=
  (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (continuous_restrictStages R C C' S hC))

end GradedDiagramAut

/-- The old classified cofinal equivalence preserves exactly the literal scalar range. -/
theorem map_scalarSubgroup_cofinalRestrictionEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut.scalarSubgroup R C S).map (cofinalRestrictionEquiv R C C' S hC hS hgen
      hn).toMonoidHom = DiagramAut.scalarSubgroup R C' S := by
  have he : (cofinalRestrictionEquiv R C C' S hC hS hgen hn).toMonoidHom =
    DiagramAut.restrictStages R C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact cofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g
  rw [he]
  exact DiagramAut.map_scalarSubgroup_restrictStages R C C' S hC

/-- The old classified cofinal equivalence preserves exactly the literal scalar range. -/
theorem map_scalarSubgroup_gradedCofinalRestrictionEquiv [IsLocalRing R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut.scalarSubgroup R C S).map (gradedCofinalRestrictionEquiv R C C' S hC hS
      hgen hn).toMonoidHom = GradedDiagramAut.scalarSubgroup R C' S := by
  have he : (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).toMonoidHom =
    GradedDiagramAut.restrictStages R C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact gradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g
  rw [he]
  exact GradedDiagramAut.map_scalarSubgroup_restrictStages R C C' S hC

/-- The old classified cofinal equivalence preserves exactly the literal scalar range. -/
theorem map_scalarSubgroup_domainCofinalRestrictionEquiv [IsDomain R] (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut.scalarSubgroup R C S).map (domainCofinalRestrictionEquiv R C C' S hC hS hgen
      hn).toMonoidHom = DiagramAut.scalarSubgroup R C' S := by
  have he : (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).toMonoidHom =
    DiagramAut.restrictStages R C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact domainCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g
  rw [he]
  exact DiagramAut.map_scalarSubgroup_restrictStages R C C' S hC

/-- The old classified cofinal equivalence preserves exactly the literal scalar range. -/
theorem map_scalarSubgroup_domainGradedCofinalRestrictionEquiv [IsDomain R] (hC : C'.stages ⊆
    C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut.scalarSubgroup R C S).map (domainGradedCofinalRestrictionEquiv R C C' S hC
      hS hgen hn).toMonoidHom = GradedDiagramAut.scalarSubgroup R C' S := by
  have he : (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).toMonoidHom =
    GradedDiagramAut.restrictStages R C C' S hC := by
    apply MonoidHom.ext
    intro g
    exact domainGradedCofinalRestrictionEquiv_apply R C C' S hC hS hgen hn g
  rw [he]
  exact GradedDiagramAut.map_scalarSubgroup_restrictStages R C C' S hC

end OrlikSolomon.HyperplaneGT
