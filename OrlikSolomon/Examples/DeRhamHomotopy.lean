/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.DeRham.Homotopy

/-!
# Regressions for polynomial homotopy invariance

The integration operator has the expected normalization on `dX`. Polynomial extension
preserves cohomology for the rational dual numbers, which have a nonzero square-zero
function, and for actual zero coefficients. The hypothesis on positive integers fails
in characteristic two.

Blueprint: `thm:dr-homotopy` and the coefficient regressions of `lem:dr-polynomial-splitting`.
-/

@[expose] public section
noncomputable section
open Polynomial

namespace OrlikSolomon.DeRham.Examples

/-- Every positive integer is invertible over the rationals. -/
theorem isUnit_natCast_add_one_rat (n : ℕ) : IsUnit (n + 1 : ℚ) := by
  apply isUnit_iff_ne_zero.mpr
  positivity

/-- The rational dual numbers contain a nonzero square-zero function. -/
theorem dualNumbers_exists_nonzero_square_zero :
    ∃ e : TrivSqZeroExt ℚ ℚ, e ≠ 0 ∧ e ^ 2 = 0 := by
  refine ⟨TrivSqZeroExt.inr 1, ?_, ?_⟩
  · intro h
    have h₁ := congrArg TrivSqZeroExt.snd h
    norm_num at h₁
  · simp only [pow_two, TrivSqZeroExt.inr_mul_inr]

/-- Polynomial homotopy invariance applies to the rational dual numbers, with no smoothness
assumption on the coefficient algebra. -/
theorem dualNumbers_bijective_cohomologyMap_C :
    Function.Bijective
      (Cohomology.map (Polynomial.CAlgHom (R := ℚ) (A := TrivSqZeroExt ℚ ℚ))) :=
  bijective_cohomologyMap_C ℚ (TrivSqZeroExt ℚ ℚ) isUnit_natCast_add_one_rat

/-- The homotopy integrates the new variable differential to the variable function. -/
theorem dualNumbers_homotopy_diff_X :
    polynomialHomotopy ℚ (TrivSqZeroExt ℚ ℚ) isUnit_natCast_add_one_rat
      (diff ℚ (X : (TrivSqZeroExt ℚ ℚ)[X])) =
        algebraMap (TrivSqZeroExt ℚ ℚ)[X] (Forms ℚ (TrivSqZeroExt ℚ ℚ)[X]) X :=
  polynomialHomotopy_diff_X ℚ (TrivSqZeroExt ℚ ℚ) isUnit_natCast_add_one_rat

/-- Positive integers are units even when the coefficient ring is the zero ring. -/
theorem isUnit_natCast_add_one_zero (n : ℕ) : IsUnit (n + 1 : PUnit) :=
  isUnit_of_subsingleton _

/-- The canonical polynomial cohomology map is bijective for the actual zero coefficient ring. -/
theorem zero_bijective_cohomologyMap_C :
    Function.Bijective (Cohomology.map (Polynomial.CAlgHom (R := PUnit) (A := PUnit))) :=
  bijective_cohomologyMap_C PUnit PUnit isUnit_natCast_add_one_zero

/-- The degree-lowering homotopy is defined over the actual zero coefficient ring. -/
theorem zero_homotopy_mem_exteriorPower {n : ℕ} {x : Forms PUnit PUnit[X]}
    (hx : x ∈ ⋀[PUnit[X]]^(n + 1) Ω[PUnit[X]⁄PUnit]) :
    polynomialHomotopy PUnit PUnit isUnit_natCast_add_one_zero x ∈
      ⋀[PUnit[X]]^n Ω[PUnit[X]⁄PUnit] :=
  polynomialHomotopy_mem_exteriorPower PUnit PUnit isUnit_natCast_add_one_zero hx

/-- The integration hypothesis does not hold in characteristic two. -/
theorem not_forall_isUnit_natCast_add_one_charTwo :
    ¬ ∀ n : ℕ, IsUnit (n + 1 : ZMod 2) := by
  intro h
  exact (not_isUnit_zero : ¬ IsUnit (0 : ZMod 2)) (h 1)

end OrlikSolomon.DeRham.Examples
