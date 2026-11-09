/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Annihilators
public import OrlikSolomon.Examples.HyperplaneGT.Coordinates

/-!
# Trace, decomposition and annihilator consumers

Actual parallel points and concurrent lines over `𝔽₂` exercise the discarded and merged
trace branches. The empty-intersection triangle has distinct retained traces and gives no
kernel difference. The examples also test the zero coefficient ring, a unit over `ℤ/4`,
and the explicit product equivalence and evaluation annihilators without unfolding them.

Blueprint: regression consumers for L01–L03 (`lem:l01`, `def:l02`, `lem:l02`, `lem:l03`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.TraceExamples

open CoordinateExamples

universe u v

/-- The other coordinate axis, regarded as a label off the distinguished axis. -/
def otherAxis : {K : Hyperplane (ZMod 2) 2 // K ≠ xLine (ZMod 2)} :=
  ⟨yLine (ZMod 2), xLine_ne_yLine.symm⟩

/-- A diagonal line, regarded as a label off the distinguished coordinate axis. -/
def diagonal (c : ZMod 2) :
    {K : Hyperplane (ZMod 2) 2 // K ≠ xLine (ZMod 2)} :=
  ⟨diagonalLine c, (xLine_ne_diagonalLine c).symm⟩

private theorem concurrent_dependent :
    DependentTriple (xLine (ZMod 2)) (yLine (ZMod 2)) (diagonalLine (0 : ZMod 2)) :=
  (dependentTriple_iff_trace_eq _ _ _ xLine_ne_yLine
    (xLine_ne_diagonalLine 0) (yLine_ne_diagonalLine 0)).mpr concurrent_traces

/-- The second point of the affine line is discarded, even over `𝔽₂` with `𝔽₂` coefficients.
-/
theorem parallel_trace_zero :
    traceMap (ZMod 2)
      (graphHyperplane (k := ZMod 2) (0 : Fin 1) (AffineMap.const _ _ 0))
      (traceSingle (ZMod 2) _
        ⟨graphHyperplane (k := ZMod 2) (0 : Fin 1) (AffineMap.const _ _ 1),
          parallel_points.1.symm⟩ 1) = 0 := by
  rw [traceMap_traceSingle, (traceLabel_eq_none_iff _ _).mpr parallel_points]
  rfl

/-- Concurrent lines give a genuine kernel difference in the actual universal module.
The coefficient ring is independent of the geometric field. -/
theorem concurrent_difference_in_kernel (R : Type v) [CommRing R] :
    Finsupp.single (yLine (ZMod 2)) (1 : R) - Finsupp.single (diagonalLine (0 : ZMod 2)) 1 ∈
      traceKernel R (xLine (ZMod 2)) := by
  rw [traceKernel_eq_span]
  exact Submodule.subset_span
    (Or.inr ⟨yLine (ZMod 2), diagonalLine 0, concurrent_dependent, rfl⟩)

/-- The actual two trace-map basis images coincide for concurrent lines in characteristic two.
-/
theorem concurrent_trace_equal :
    traceMap (ZMod 2) (xLine (ZMod 2)) (traceSingle (ZMod 2) _ otherAxis 1) =
      traceMap (ZMod 2) (xLine (ZMod 2)) (traceSingle (ZMod 2) _ (diagonal 0) 1) := by
  obtain ⟨J, hK, hL⟩ :=
    (exists_common_traceLabel_iff _ otherAxis (diagonal 0)
      (yLine_ne_diagonalLine 0)).mpr concurrent_dependent
  rw [traceMap_traceSingle, traceMap_traceSingle, hK, hL]

/-- An empty triple intersection does not merge the two retained traces or create a trace
kernel difference. This tests the nonempty guard with the library's actual trace map. -/
theorem empty_triangle_difference_not_in_kernel :
    Finsupp.single (yLine (ZMod 2)) (1 : ZMod 2) -
        Finsupp.single (diagonalLine (1 : ZMod 2)) 1 ∉ traceKernel (ZMod 2) (xLine (ZMod 2)) := by
  intro hx
  have hmem : ((traceSingle (ZMod 2) (xLine (ZMod 2)) otherAxis 1 -
      traceSingle (ZMod 2) (xLine (ZMod 2)) (diagonal 1) 1 : traceDomain (ZMod 2) _) :
        Hyperplane (ZMod 2) 2 →₀ ZMod 2) ∈ traceKernel (ZMod 2) (xLine (ZMod 2)) := by
    simpa only [Submodule.coe_sub, coe_traceSingle, otherAxis, diagonal] using hx
  have hz := (coe_mem_traceKernel_iff _ _ _).mp hmem
  rw [map_sub, sub_eq_zero, traceMap_traceSingle, traceMap_traceSingle] at hz
  cases hK : traceLabel (xLine (ZMod 2)) otherAxis with
  | none => exact not_parallel_axes ((traceLabel_eq_none_iff _ _).mp hK)
  | some J =>
    cases hL : traceLabel (xLine (ZMod 2)) (diagonal 1) with
    | none => exact not_parallel_xLine_diagonalLine 1 ((traceLabel_eq_none_iff _ _).mp hL)
    | some J' =>
      rw [hK, hL] at hz
      have hJJ' : J = J' := Finsupp.single_left_injective (one_ne_zero : (1 : ZMod 2) ≠ 0) hz
      subst J'
      exact triangle_codim_but_not_dependent.2
        ((exists_common_traceLabel_iff _ otherAxis (diagonal 1)
          (yLine_ne_diagonalLine 1)).mp ⟨J, hK, hL⟩)

/-- A unit with nontrivial value in a ring with nilpotents is enough for the centralizer
identity; no integral-domain hypothesis occurs. -/
theorem centralizer_mod_four (H : Hyperplane (ZMod 2) 2) :
    centralizer (universalQuadraticRelationSpan (ZMod 4))
      ((3 : ZMod 4) • (Finsupp.lapply H : Module.Dual (ZMod 4) (Hyperplane (ZMod 2) 2 →₀ ZMod 4))) =
      decomposition (ZMod 4) H :=
  centralizer_unit_smul_delta (ZMod 4) H (⟨3, 3, by decide, by decide⟩ : (ZMod 4)ˣ)

/-- Even when a unit equals zero in the zero ring, its centralizer identity remains valid. -/
theorem centralizer_zero_ring {k : Type u} [Field k] {n : ℕ} (H : Hyperplane k n) :
    centralizer (universalQuadraticRelationSpan (ZMod 1))
      (Finsupp.lapply H : Module.Dual (ZMod 1) (Hyperplane k n →₀ ZMod 1)) =
      decomposition (ZMod 1) H := by
  simpa using centralizer_unit_smul_delta (ZMod 1) H 1

/-- The actual full dual and the trace kernel satisfy the reverse annihilator identity even
with zero coefficients. -/
theorem annihilator_zero_ring {k : Type u} [Field k] {n : ℕ} (H : Hyperplane k n) :
    (decomposition (ZMod 1) H).dualCoannihilator = traceKernel (ZMod 1) H :=
  decomposition_dualCoannihilator _ H

/-- The product equivalence supports ordinary mixed scalar/additive expressions and cancellation.
-/
theorem decomposition_coordinates_add {k : Type u} [Field k] {n : ℕ}
    (R : Type v) [CommRing R] (H : Hyperplane k n) (a : R) (φ ψ : decomposition R H) :
    (decompositionEquiv R H).symm (a • decompositionEquiv R H φ + decompositionEquiv R H ψ) =
      a • φ + ψ := by simp

/-- Dimension zero has no hidden hyperplane label or nonempty-module convention. -/
theorem dimension_zero_vectors {k : Type u} [Field k] (R : Type v) [CommRing R]
    (x : Hyperplane k 0 →₀ R) : x = 0 := by
  let _ := dimension_zero (k := k)
  exact Subsingleton.elim _ _

end OrlikSolomon.HyperplaneGT.TraceExamples
