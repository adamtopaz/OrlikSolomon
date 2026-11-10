/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois.Geometry

/-!
# Geometric regressions for the scalar kernel

Concrete binary-field hyperplanes exercise both connectivity witnesses. The guarded triple
through the axes cannot be the empty triangle. A transverse hyperplane meets both members
of the parallel pair whose union contains every binary rational point of the plane.

These geometric statements use no coefficient ring or point of a complement.
Blueprint: the connectivity in S01 (`lem:s01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.GaloisReconstructionExamples

/-- A guarded triple through the actual binary coordinate axes is different from the empty
binary triangle, whose conventional codimension alone would not detect the empty intersection.
-/
theorem binary_intersecting_triple :
    ∃ L : Hyperplane (ZMod 2) 2,
      DependentTriple (CoordinateExamples.xLine (ZMod 2))
        (CoordinateExamples.yLine (ZMod 2)) L ∧
        L ≠ CoordinateExamples.diagonalLine (1 : ZMod 2) := by
  obtain ⟨L, hL⟩ := exists_dependentTriple_of_inf_ne_bot
    (CoordinateExamples.xLine (ZMod 2)) (CoordinateExamples.yLine (ZMod 2))
    CoordinateExamples.xLine_ne_yLine CoordinateExamples.concurrent_traces.1
  refine ⟨L, hL, ?_⟩
  intro he
  exact CoordinateExamples.triangle_codim_but_not_dependent.2 (he ▸ hL)

/-- The second binary coordinate line, parallel to `x = 0`. -/
def binaryShiftedAxis : Hyperplane (ZMod 2) 2 :=
  graphHyperplane 0 (AffineMap.const _ _ 1)

/-- Membership in the shifted binary coordinate axis is the equation `x₀ = 1`. -/
@[simp]
theorem mem_binaryShiftedAxis (x : Fin 2 → ZMod 2) :
    x ∈ binaryShiftedAxis.val ↔ x 0 = 1 := by
  simp [binaryShiftedAxis]

/-- The two actual binary coordinate fibers are a strict parallel pair. -/
theorem binary_parallel_pair :
    Parallel (CoordinateExamples.xLine (ZMod 2)) binaryShiftedAxis := by
  apply parallel_graphHyperplane_of_sub_eq_const (c := 1) _ one_ne_zero
  ext x
  simp

/-- These two actual parallel hyperplanes cover all binary rational points, so their
complement supplies no rational point for the connectivity proof. -/
theorem binary_parallel_cover (x : Fin 2 → ZMod 2) :
    x ∈ (CoordinateExamples.xLine (ZMod 2)).val ∨ x ∈ binaryShiftedAxis.val := by
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases (x 0) with hx | hx
  · exact Or.inl ((CoordinateExamples.mem_xLine x).mpr hx)
  · exact Or.inr ((mem_binaryShiftedAxis x).mpr hx)

/-- Even this point-free-complement parallel pair has an actual transverse hyperplane
meeting each member nontrivially, distinct from both. -/
theorem binary_parallel_transverse :
    ∃ L : Hyperplane (ZMod 2) 2,
      CoordinateExamples.xLine (ZMod 2) ≠ L ∧ binaryShiftedAxis ≠ L ∧
        (CoordinateExamples.xLine (ZMod 2)).val ⊓ L.val ≠ ⊥ ∧
        binaryShiftedAxis.val ⊓ L.val ≠ ⊥ :=
  exists_hyperplane_meeting_parallel_pair (by decide) _ _ binary_parallel_pair

end OrlikSolomon.HyperplaneGT.GaloisReconstructionExamples
