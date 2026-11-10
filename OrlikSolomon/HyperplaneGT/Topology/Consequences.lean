/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Classification
public import OrlikSolomon.HyperplaneGT.Topology.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.AlexandrovDiscrete

/-!
# Local compactness and the finite-unit criterion

The original quadratic and full graded diagram groups are locally compact in the
classified local-ring and integral-domain ranges. They are compact exactly when the
coefficient unit group is finite. The coefficient ring itself need not be finite.

## Main results

* `DiagramAut.locallyCompactSpace`, `GradedDiagramAut.locallyCompactSpace` and their
  `_of_isDomain` versions give local compactness.
* `DiagramAut.compactSpace_iff_finite_units`, the graded version and their domain versions
  give the exact compactness criterion, with finite-unit and infinite-unit consequences.

The proofs reuse the existing pointwise classifiers and compactness from the supplied
stable cofinal system. No algebraicity, Krull fixing condition or finite coefficient
hypothesis enters these diagram-topology results. T02 supplies Hausdorff and total
separation in the existing scope, and T11 supplies the profinite scalar quotients.
There is no new topology, global instance or bundled replacement group.

Blueprint: T13 (`cor:t13`).
-/

@[expose] public section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open scoped DiscreteCoefficientUnits FiniteStageTopology GaloisPointwise

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- The actual quadratic group with local-ring coefficients is locally compact.
The unit group may be infinite. Blueprint: T13 (`cor:t13`). -/
theorem locallyCompactSpace [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @LocallyCompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) := by
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  let e := quadraticAutContinuousEquiv R C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance

/-- The actual quadratic group with local-ring coefficients is compact precisely
when its discrete coefficient-unit factor is finite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_iff_finite_units [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) ↔ Finite Rˣ := by
  let e := quadraticAutContinuousEquiv R C S hS hgen hn
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  constructor
  · intro h
    let : CompactSpace (DiagramAut R C S) := h
    let : CompactSpace (Rˣ × (k ≃ₐ[k₀] k)) := e.symm.toHomeomorph.compactSpace
    let : CompactSpace Rˣ := Function.Surjective.compactSpace
      (continuous_fst : Continuous (Prod.fst : Rˣ × (k ≃ₐ[k₀] k) → Rˣ))
      Prod.fst_surjective
    exact finite_of_compact_of_discrete
  · intro h
    let : Finite Rˣ := h
    exact e.toHomeomorph.compactSpace

/-- Finite units suffice for compactness of the quadratic group over local-ring
coefficients; the coefficient ring can be infinite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_of_finite_units [IsLocalRing R] [Finite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) :=
  (compactSpace_iff_finite_units R C S hS hgen hn).mpr inferInstance

/-- Infinite units prevent compactness of the quadratic group over local-ring
coefficients, even though the scalar quotient is compact. Blueprint: T13 (`cor:t13`). -/
theorem not_compactSpace_of_infinite_units [IsLocalRing R] [Infinite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ¬ @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) := by
  intro h
  let : Finite Rˣ := (compactSpace_iff_finite_units R C S hS hgen hn).mp h
  exact not_finite Rˣ

/-- The actual quadratic group with integral-domain coefficients is locally compact.
The unit group may be infinite. Blueprint: T13 (`cor:t13`). -/
theorem locallyCompactSpace_of_isDomain [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @LocallyCompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) := by
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  let e := coefficientDomainAutContinuousEquiv R C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance

/-- The actual quadratic group with integral-domain coefficients is compact precisely
when its discrete coefficient-unit factor is finite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_iff_finite_units_of_isDomain [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) ↔ Finite Rˣ := by
  let e := coefficientDomainAutContinuousEquiv R C S hS hgen hn
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  constructor
  · intro h
    let : CompactSpace (DiagramAut R C S) := h
    let : CompactSpace (Rˣ × (k ≃ₐ[k₀] k)) := e.symm.toHomeomorph.compactSpace
    let : CompactSpace Rˣ := Function.Surjective.compactSpace
      (continuous_fst : Continuous (Prod.fst : Rˣ × (k ≃ₐ[k₀] k) → Rˣ))
      Prod.fst_surjective
    exact finite_of_compact_of_discrete
  · intro h
    let : Finite Rˣ := h
    exact e.toHomeomorph.compactSpace

/-- Finite units suffice for compactness of the quadratic group over integral-domain
coefficients; the coefficient ring can be infinite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_of_finite_units_of_isDomain [IsDomain R] [Finite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) :=
  (compactSpace_iff_finite_units_of_isDomain R C S hS hgen hn).mpr inferInstance

/-- Infinite units prevent compactness of the quadratic group over integral-domain
coefficients, even though the scalar quotient is compact. Blueprint: T13 (`cor:t13`). -/
theorem not_compactSpace_of_infinite_units_of_isDomain [IsDomain R] [Infinite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ¬ @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) := by
  intro h
  let : Finite Rˣ := (compactSpace_iff_finite_units_of_isDomain R C S hS hgen hn).mp h
  exact not_finite Rˣ

end DiagramAut

namespace GradedDiagramAut

/-- The actual full graded group with local-ring coefficients is locally compact.
The unit group may be infinite. Blueprint: T13 (`cor:t13`). -/
theorem locallyCompactSpace [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @LocallyCompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) := by
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  let e := gradedClassificationContinuousEquiv R C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance

/-- The actual full graded group with local-ring coefficients is compact precisely
when its discrete coefficient-unit factor is finite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_iff_finite_units [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) ↔ Finite Rˣ := by
  let e := gradedClassificationContinuousEquiv R C S hS hgen hn
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  constructor
  · intro h
    let : CompactSpace (GradedDiagramAut R C S) := h
    let : CompactSpace (Rˣ × (k ≃ₐ[k₀] k)) := e.symm.toHomeomorph.compactSpace
    let : CompactSpace Rˣ := Function.Surjective.compactSpace
      (continuous_fst : Continuous (Prod.fst : Rˣ × (k ≃ₐ[k₀] k) → Rˣ))
      Prod.fst_surjective
    exact finite_of_compact_of_discrete
  · intro h
    let : Finite Rˣ := h
    exact e.toHomeomorph.compactSpace

/-- Finite units suffice for compactness of the full graded group over local-ring
coefficients; the coefficient ring can be infinite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_of_finite_units [IsLocalRing R] [Finite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) :=
  (compactSpace_iff_finite_units R C S hS hgen hn).mpr inferInstance

/-- Infinite units prevent compactness of the full graded group over local-ring
coefficients, even though the scalar quotient is compact. Blueprint: T13 (`cor:t13`). -/
theorem not_compactSpace_of_infinite_units [IsLocalRing R] [Infinite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ¬ @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) := by
  intro h
  let : Finite Rˣ := (compactSpace_iff_finite_units R C S hS hgen hn).mp h
  exact not_finite Rˣ

/-- The actual full graded group with integral-domain coefficients is locally compact.
The unit group may be infinite. Blueprint: T13 (`cor:t13`). -/
theorem locallyCompactSpace_of_isDomain [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @LocallyCompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) := by
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  let e := coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance

/-- The actual full graded group with integral-domain coefficients is compact precisely
when its discrete coefficient-unit factor is finite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_iff_finite_units_of_isDomain [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) ↔ Finite Rˣ := by
  let e := coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn
  let : CompactSpace (k ≃ₐ[k₀] k) :=
    C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  constructor
  · intro h
    let : CompactSpace (GradedDiagramAut R C S) := h
    let : CompactSpace (Rˣ × (k ≃ₐ[k₀] k)) := e.symm.toHomeomorph.compactSpace
    let : CompactSpace Rˣ := Function.Surjective.compactSpace
      (continuous_fst : Continuous (Prod.fst : Rˣ × (k ≃ₐ[k₀] k) → Rˣ))
      Prod.fst_surjective
    exact finite_of_compact_of_discrete
  · intro h
    let : Finite Rˣ := h
    exact e.toHomeomorph.compactSpace

/-- Finite units suffice for compactness of the full graded group over integral-domain
coefficients; the coefficient ring can be infinite. Blueprint: T13 (`cor:t13`). -/
theorem compactSpace_of_finite_units_of_isDomain [IsDomain R] [Finite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) :=
  (compactSpace_iff_finite_units_of_isDomain R C S hS hgen hn).mpr inferInstance

/-- Infinite units prevent compactness of the full graded group over integral-domain
coefficients, even though the scalar quotient is compact. Blueprint: T13 (`cor:t13`). -/
theorem not_compactSpace_of_infinite_units_of_isDomain [IsDomain R] [Infinite Rˣ]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ¬ @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) := by
  intro h
  let : Finite Rˣ := (compactSpace_iff_finite_units_of_isDomain R C S hS hgen hn).mp h
  exact not_finite Rˣ

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT
