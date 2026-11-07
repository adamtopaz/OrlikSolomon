/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The weight grading of Laurent polynomials

The ring `R[T;T⁻¹]` is graded by the powers of `T`: the piece of weight `w` is `R T^w`. Mathlib has
this as `AddMonoidAlgebra.grade`, for any additive monoid of exponents. This file gives it a name
and the form in which coefficient rings of cohomology theories use it. It also adds evaluation at
`T = 1`, which forgets the weight.

## Main definitions

* `OrlikSolomon.laurentGrading R w`: the piece `R T^w`, with its `GradedAlgebra` instance.
* `OrlikSolomon.laurentEvalOne R`: the `R`-algebra map `R[T;T⁻¹] → R` that sends `T` to `1`.

## Main results

* `OrlikSolomon.mem_laurentGrading_iff`: the piece of weight `w` consists of the `c • T w`.
* `OrlikSolomon.bijective_algebraMap_laurentGrading_zero`: `R` is the piece of weight zero.
* `OrlikSolomon.eq_laurentEvalOne_smul_T_of_mem`: an element of weight `w` is determined by its
  value at `T = 1`.

## Blueprint

The grading `ℬ` of `def:dr-twisted-functor` and the first field of `lem:dr-ordinary-basic`. It is
also the coefficient ring of the Betti model in the docstring of `OrdinaryTheory`.
-/

@[expose] public section

noncomputable section

open DirectSum
open scoped LaurentPolynomial
open LaurentPolynomial (T)

universe u

namespace OrlikSolomon

variable (R : Type u) [CommSemiring R]

/-- The piece `R T^w` of weight `w` of the Laurent polynomials.

Blueprint: the grading `ℬ` of `def:dr-twisted-functor`. -/
def laurentGrading (w : ℤ) : Submodule R R[T;T⁻¹] :=
  AddMonoidAlgebra.grade R w

instance gradedAlgebraLaurentGrading : GradedAlgebra (laurentGrading R) :=
  inferInstanceAs (GradedAlgebra (AddMonoidAlgebra.grade R : ℤ → Submodule R R[T;T⁻¹]))

/-- The `R`-algebra map `R[T;T⁻¹] → R` that sends `T` to `1`. It splits the inclusion of constants,
and it is injective on each piece of the weight grading. -/
def laurentEvalOne : R[T;T⁻¹] →ₐ[R] R :=
  AddMonoidAlgebra.lift R R ℤ 1

variable {R}

@[simp]
theorem laurentEvalOne_T (w : ℤ) : laurentEvalOne R (T w) = 1 :=
  (AddMonoidAlgebra.lift_single (1 : Multiplicative ℤ →* R) w 1).trans (by simp)

theorem T_mem_laurentGrading (w : ℤ) : (T w : R[T;T⁻¹]) ∈ laurentGrading R w :=
  AddMonoidAlgebra.single_mem_grade w 1

/-- The piece of weight `w` consists of the scalar multiples of `T w`. -/
theorem mem_laurentGrading_iff {w : ℤ} {b : R[T;T⁻¹]} :
    b ∈ laurentGrading R w ↔ ∃ c : R, c • (T w : R[T;T⁻¹]) = b := by
  refine ⟨fun hb ↦ ?_, ?_⟩
  · have hb : b ∈ AddMonoidAlgebra.grade R w := hb
    obtain ⟨c, rfl⟩ := (AddMonoidAlgebra.mem_grade_iff' R w b).1 hb
    refine ⟨c, ?_⟩
    change c • AddMonoidAlgebra.single w (1 : R) = AddMonoidAlgebra.lsingle w c
    rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  · rintro ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (T_mem_laurentGrading w)

/-- The piece of weight `w` is the line spanned by `T w`. -/
theorem laurentGrading_eq_span (w : ℤ) : laurentGrading R w = Submodule.span R {(T w : R[T;T⁻¹])} :=
  Submodule.ext fun _ ↦ by rw [mem_laurentGrading_iff, Submodule.mem_span_singleton]

/-- An element of weight `w` is its value at `T = 1`, times `T w`. -/
theorem eq_laurentEvalOne_smul_T_of_mem {w : ℤ} {b : R[T;T⁻¹]} (hb : b ∈ laurentGrading R w) :
    laurentEvalOne R b • (T w : R[T;T⁻¹]) = b := by
  obtain ⟨c, rfl⟩ := mem_laurentGrading_iff.1 hb
  simp

variable (R) in
/-- `R` is the piece of weight zero of `R[T;T⁻¹]`.

Blueprint: `lem:dr-ordinary-basic`, for the field `bijective_algebraMap_gradeZero`. -/
theorem bijective_algebraMap_laurentGrading_zero :
    Function.Bijective (algebraMap R (laurentGrading R 0)) := by
  refine ⟨fun r s h ↦ ?_, fun b ↦ ?_⟩
  · have h' : algebraMap R R[T;T⁻¹] r = algebraMap R R[T;T⁻¹] s := congrArg Subtype.val h
    have h'' := congrArg (laurentEvalOne R) h'
    rwa [AlgHom.commutes, AlgHom.commutes] at h''
  · obtain ⟨c, hc⟩ := mem_laurentGrading_iff.1 b.2
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hc, LaurentPolynomial.T_zero, Algebra.algebraMap_eq_smul_one]
    rfl

end OrlikSolomon
