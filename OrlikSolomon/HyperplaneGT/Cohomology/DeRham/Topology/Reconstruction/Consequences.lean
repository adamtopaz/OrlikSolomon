/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Consequences
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Local compactness and profinite ordinary scalar quotients

The original ordinary de Rham quadratic and full graded groups are locally compact and
noncompact under precisely the old dimension and generating-marking hypotheses. Infinite
coefficient units follow from the characteristic-zero field itself, rather than an added
input or global instance. The proof reuses T13 through the exact old twists and actual
presentation adapters, without rerunning classification.

Both original literal scalar quotients are Hausdorff, compact and totally separated; their
literal scalar ranges are closed. The compact pointwise Galois factor comes from the supplied
stable system in positive dimension. No algebraicity or Krull fixing condition is needed.
All properties are named theorems on the old carriers and direct topologies, not instances
or new profinite replacement groups. Blueprint: the consequences of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits GaloisPointwise

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

private theorem infinite_coefficient_units : Infinite kˣ := by
  let : Infinite {a : k // a ≠ 0} :=
    (Set.finite_singleton (0 : k)).infinite_compl.to_subtype
  exact Infinite.of_injective (unitsEquivNeZero (G₀ := k)).symm
    (unitsEquivNeZero (G₀ := k)).symm.injective

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

include hS hgen hn

namespace DiagramAut

/-- The complete original ordinary group is locally compact, with no field-extension input.
Blueprint: T17 (`cor:t17`). -/
theorem locallyCompactSpace : @LocallyCompactSpace (DiagramAut C S) (stageTopology C S) := by
  let e := (quadraticTwistContinuousEquiv C S).trans (Cohomology.degreeOneDiagramContinuousEquiv
    Tdr C S)
  let : LocallyCompactSpace (HyperplaneGT.DiagramAut k C S) :=
    HyperplaneGT.DiagramAut.locallyCompactSpace k C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- The characteristic-zero coefficient field has infinitely many actual units, so the
original ordinary group is noncompact, even though its scalar quotient is compact. -/
theorem not_compactSpace : ¬ @CompactSpace (DiagramAut C S) (stageTopology C S) := by
  let : Infinite kˣ := infinite_coefficient_units
  let e := (quadraticTwistContinuousEquiv C S).trans (Cohomology.degreeOneDiagramContinuousEquiv
    Tdr C S)
  intro h
  let : CompactSpace (DiagramAut C S) := h
  exact HyperplaneGT.DiagramAut.not_compactSpace_of_infinite_units k C S hS hgen hn
    e.toHomeomorph.compactSpace

/-- The original literal ordinary scalar quotient is Hausdorff. -/
theorem scalarQuotient_t2Space :
    @T2Space (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) :=
  (scalarQuotientContinuousEquiv C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The literal ordinary scalar quotient is compact from the supplied stable system alone.
Neither algebraicity, the Krull fixing condition nor finite coefficient units is assumed. -/
theorem scalarQuotient_compactSpace :
    @CompactSpace (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (scalarQuotientContinuousEquiv C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The original literal ordinary scalar quotient is totally separated, completing its
explicit profinite property package on the same quotient carrier. -/
theorem scalarQuotient_totallySeparatedSpace :
    @TotallySeparatedSpace (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) := by
  let e := scalarQuotientContinuousEquiv C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

/-- The literal ordinary scalar range is closed, without identifying it with the full center.
Blueprint: T17 (`cor:t17`). -/
theorem scalarSubgroup_isClosed :
    @IsClosed (DiagramAut C S) (stageTopology C S) (scalarSubgroup C S : Set (DiagramAut C S)) := by
  let : T2Space (DiagramAut C S ⧸ scalarSubgroup C S) := scalarQuotient_t2Space C S hS hgen hn
  have h : (scalarSubgroup C S : Set (DiagramAut C S)) =
      scalarQuotientMap C S ⁻¹' ({1} : Set (DiagramAut C S ⧸ scalarSubgroup C S)) :=
    Set.ext fun g ↦ (QuotientGroup.eq_one_iff g).symm
  rw [h]
  exact isClosed_singleton.preimage QuotientGroup.continuous_mk

end DiagramAut

namespace GradedDiagramAut

/-- The complete original ordinary group is locally compact, with no field-extension input.
Blueprint: T17 (`cor:t17`). -/
theorem locallyCompactSpace : @LocallyCompactSpace (GradedDiagramAut C S) (stageTopology C S) := by
  let e := (gradedTwistContinuousEquiv C S).trans (Cohomology.gradedDiagramContinuousEquiv Tdr C S)
  let : LocallyCompactSpace (HyperplaneGT.GradedDiagramAut k C S) :=
    HyperplaneGT.GradedDiagramAut.locallyCompactSpace k C S hS hgen hn
  exact e.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- The characteristic-zero coefficient field has infinitely many actual units, so the
original ordinary group is noncompact, even though its scalar quotient is compact. -/
theorem not_compactSpace : ¬ @CompactSpace (GradedDiagramAut C S) (stageTopology C S) := by
  let : Infinite kˣ := infinite_coefficient_units
  let e := (gradedTwistContinuousEquiv C S).trans (Cohomology.gradedDiagramContinuousEquiv Tdr C S)
  intro h
  let : CompactSpace (GradedDiagramAut C S) := h
  exact HyperplaneGT.GradedDiagramAut.not_compactSpace_of_infinite_units k C S hS hgen hn
    e.toHomeomorph.compactSpace

/-- The original literal ordinary scalar quotient is Hausdorff. -/
theorem scalarQuotient_t2Space :
    @T2Space (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) :=
  (scalarQuotientContinuousEquiv C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The literal ordinary scalar quotient is compact from the supplied stable system alone.
Neither algebraicity, the Krull fixing condition nor finite coefficient units is assumed. -/
theorem scalarQuotient_compactSpace :
    @CompactSpace (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (scalarQuotientContinuousEquiv C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The original literal ordinary scalar quotient is totally separated, completing its
explicit profinite property package on the same quotient carrier. -/
theorem scalarQuotient_totallySeparatedSpace :
    @TotallySeparatedSpace (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S)) := by
  let e := scalarQuotientContinuousEquiv C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

/-- The literal ordinary scalar range is closed, without identifying it with the full center.
Blueprint: T17 (`cor:t17`). -/
theorem scalarSubgroup_isClosed :
    @IsClosed (GradedDiagramAut C S) (stageTopology C S) (scalarSubgroup C S : Set
      (GradedDiagramAut C S)) := by
  let : T2Space (GradedDiagramAut C S ⧸ scalarSubgroup C S) := scalarQuotient_t2Space C S hS hgen
    hn
  have h : (scalarSubgroup C S : Set (GradedDiagramAut C S)) =
      scalarQuotientMap C S ⁻¹' ({1} : Set (GradedDiagramAut C S ⧸ scalarSubgroup C S)) :=
    Set.ext fun g ↦ (QuotientGroup.eq_one_iff g).symm
  rw [h]
  exact isClosed_singleton.preimage QuotientGroup.continuous_mk

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
