/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Collineation
public import Mathlib.Algebra.Field.ZMod

/-!
# Consumers of coordinate field reconstruction

These consumers check the public pure-field interfaces: dimension-zero chart functions,
extraction and uniqueness for the identity, the zero-sum line in characteristic two, and
the homogeneous formula at a point at infinity.

Blueprint: `lem:c01`, `lem:c02`, `thm:c03`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT.CollineationExamples

open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {n : ℕ}

/-- The chart theorem applies in dimension zero, where its coordinate family is empty. -/
theorem dimension_zero_chart
    (F : ℙ k (Fin 1 → k) ≃ ℙ k (Fin 1 → k)) (hF : PreservesProjectiveLines F)
    (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i) :
    ∃ f : Fin 0 → (k ≃ k), (∀ i, f i 0 = 0) ∧
      ∀ a : Fin 0 → k, F (affineChartPoint a) =
        affineChartPoint (fun i ↦ f i (a i)) :=
  collineation_coordinate_functions F hF hframe

/-- The identity collineation extracts exactly the identity field automorphism. The proof
uses the public uniqueness theorem, rather than the implementation of the extracted map. -/
theorem identity_field_equiv (hn : 2 ≤ n) :
    coordinateFieldEquiv (Equiv.refl (ℙ k (Fin (n + 1) → k)))
      PreservesProjectiveLines.refl (fun _ ↦ rfl) hn
      (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) = RingEquiv.refl k := by
  apply Eq.symm
  exact coordinateFieldEquiv_unique _ _ _ hn _ _ (RingEquiv.refl k) (fun _ _ ↦ rfl)

/-- In characteristic two, the point with both affine coordinates one lies on the sum-zero
line. Its description uses the origin and the point at infinity, which are distinct. -/
theorem characteristic_two_zero_sum_line :
    affineChartPoint (Pi.single (0 : Fin 2) (1 : ZMod 2) + Pi.single 1 1) ∈
      Projectivization.Subspace.span
        {affineChartPoint (0 : Fin 2 → ZMod 2),
          projectiveDifferencePoint (ZMod 2) (1 : Fin 3) 2 (by decide)} := by
  simpa using (affineChartPoint_mem_sum_line_iff (0 : Fin 2) 1 (by decide)
    (1 : ZMod 2) 1 0).mpr (by decide)

/-- The homogeneous formula fixes `[0:1:1]` over every field, including characteristic two.
This point is outside the normalized affine chart. -/
theorem diagonal_infinity_fixed
    (F : ℙ k (Fin 3 → k) ≃ ℙ k (Fin 3 → k)) (hF : PreservesProjectiveLines F)
    (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
    (hminus0 : ∀ i : Fin 2,
      F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
        projectiveDifferencePoint k i.succ 0 i.succ_ne_zero)
    (hdiff : ∀ i j : Fin 2, ∀ hij : i < j,
      F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) =
        projectiveDifferencePoint k i.succ j.succ
          (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) :
    F (Projectivization.mk k (Fin.cons 0 (fun _ : Fin 2 ↦ (1 : k))) (by
      intro h
      have := congrFun h 1
      simp at this)) =
      Projectivization.mk k (Fin.cons 0 (fun _ : Fin 2 ↦ (1 : k))) (by
        intro h
        have := congrFun h 1
        simp at this) := by
  let a : Fin 3 → k := Fin.cons 0 (fun _ ↦ 1)
  have ha : a ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [a] at this
  have h := coordinateFieldEquiv_mk F hF hframe (by decide : 2 ≤ 2) hminus0 hdiff a ha
  have hv : (fun i ↦ coordinateFieldEquiv F hF hframe (by decide : 2 ≤ 2)
      hminus0 hdiff (a i)) = a := by
    ext i
    cases i using Fin.cases <;> simp [a]
  simpa only [hv] using h

end OrlikSolomon.HyperplaneGT.CollineationExamples
