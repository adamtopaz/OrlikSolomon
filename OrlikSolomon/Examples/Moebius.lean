/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Combinatorics.Moebius
public import OrlikSolomon.Examples.AffineLines
public import OrlikSolomon.Examples.Parallel

/-!
# Möbius sums for three line arrangements

The codimension-two Möbius sums distinguish three concurrent lines, a triangle and two parallel
lines: their sums are respectively two, three and zero. These use the existing concrete
arrangements over every field, including characteristic two, and compare the new intersection
poset formula with the previously calculated subset polynomials. The concurrent codimension-one
sum is `-3`, which tests the odd-degree sign separately.

The proofs adapt Claude's independent PR #91 review consumer.
Blueprint: `lem:mobius` and regression examples 4, 5 and 6.
-/

@[expose] public section

open Finset Module Polynomial
open OrlikSolomon.Arrangement OrlikSolomon.PresentationExamples OrlikSolomon.AffineLineExamples

universe u

namespace OrlikSolomon.Examples

variable {k : Type u} [Field k]

/-- Three concurrent lines have total Möbius coefficient two in codimension two.
Blueprint: `lem:mobius`, regression example 5. -/
theorem sum_moebius_threeConcurrent_two :
    (∑ X : (threeConcurrent k).IntersectionPoset with codim X.carrier = 2, X.moebius) = 2 := by
  have h := poincarePolynomial_coeff_eq_sum_moebius (threeConcurrent k) 2
  rw [poincarePolynomial_threeConcurrent] at h
  simpa [coeff_X, coeff_one] using h.symm

/-- The three concurrent hyperplanes have Möbius sum minus three in codimension one.
Blueprint: the odd-degree sign in `lem:mobius`, regression example 5. -/
theorem sum_moebius_threeConcurrent_one :
    (∑ X : (threeConcurrent k).IntersectionPoset with codim X.carrier = 1, X.moebius) = -3 := by
  have h := poincarePolynomial_coeff_eq_sum_moebius (threeConcurrent k) 1
  rw [poincarePolynomial_threeConcurrent] at h
  simp [coeff_X, coeff_one] at h
  omega

/-- The three vertices of the affine triangle have total Möbius coefficient three.
Blueprint: `lem:mobius`, regression example 6. -/
theorem sum_moebius_triangle_two :
    (∑ X : (triangle k).IntersectionPoset with codim X.carrier = 2, X.moebius) = 3 := by
  have h := poincarePolynomial_coeff_eq_sum_moebius (triangle k) 2
  rw [poincarePolynomial_triangle] at h
  simpa [coeff_X, coeff_one] using h.symm

/-- The parallel-lines arrangement has no codimension-two contribution, since its empty
intersection is excluded from the poset. Blueprint: `lem:mobius`, regression example 4. -/
theorem sum_moebius_parallelLines_two :
    (∑ X : (parallelLines k).IntersectionPoset with codim X.carrier = 2, X.moebius) = 0 := by
  have h := poincarePolynomial_coeff_eq_sum_moebius (parallelLines k) 2
  rw [poincarePolynomial_parallelLines] at h
  simpa [coeff_X, coeff_one] using h.symm

end OrlikSolomon.Examples
