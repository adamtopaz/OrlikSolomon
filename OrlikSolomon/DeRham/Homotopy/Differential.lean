/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Homotopy.Polynomial
public import OrlikSolomon.DeRham.Homotopy.Integration

/-!
# The differential in polynomial-form coordinates

For `ω = α(X) + dX ∧ β(X)`, the de Rham differential is
`d_A α + dX ∧ (∂_X α - d_A β)`. The coefficient differential is only `k`-linear.

## Main definitions and results

* `polynomialCoefficientD`: the coefficientwise differential on polynomial forms.
* `polynomialCoefficientD_coefficientIntegral`: the coefficient differential commutes with
  integration.
* `d_polynomialForm_components` and `polynomialFormDecomposition_d`: the differential matrix in
  polynomial-form coordinates, including the minus sign on `d_A β`.

Blueprint: the differential formula in `lem:dr-polynomial-splitting`.
-/

@[expose] public section
noncomputable section
open Polynomial

namespace OrlikSolomon.DeRham

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- The coefficientwise de Rham differential on polynomials with form coefficients. -/
def polynomialCoefficientD :
    PolynomialModule A (Forms k A) →ₗ[k] PolynomialModule A (Forms k A) :=
  mapCoefficients k A (d k)

@[simp]
theorem polynomialCoefficientD_single (n : ℕ) (x : Forms k A) :
    polynomialCoefficientD k A (PolynomialModule.single A n x) =
      PolynomialModule.single A n (d k x) :=
  mapCoefficients_single k A _ n x

/-- The coefficient differential commutes with coefficientwise integration. -/
theorem polynomialCoefficientD_coefficientIntegral (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule A (Forms k A)) :
    polynomialCoefficientD k A (coefficientIntegral k A h p) =
      coefficientIntegral k A h (polynomialCoefficientD k A p) :=
  mapCoefficients_coefficientIntegral k A h (d k) p

/-- Differentiating a polynomial of regular forms separates its coefficient and variable terms. -/
theorem d_polynomialFormInclusion (p : PolynomialModule A (Forms k A)) :
    d k (polynomialFormInclusion k A p) =
      polynomialFormInclusion k A (polynomialCoefficientD k A p) +
        diff k (X : A[X]) *
          polynomialFormInclusion k A (coefficientDerivative k A p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add]
    abel
  | single n x =>
    simp only [polynomialCoefficientD_single, coefficientDerivative_single,
      polynomialFormInclusion_single]
    rw [d_smul, (diff k).leibniz_pow, ← Forms.map_d]
    simp only [Nat.cast_smul_eq_nsmul, map_nsmul, smul_mul_assoc, mul_smul_comm]
    module

/-- The variable differential anticommutes with the coefficient differential. -/
theorem d_diff_X_mul_polynomialFormInclusion (p : PolynomialModule A (Forms k A)) :
    d k (diff k (X : A[X]) * polynomialFormInclusion k A p) =
      -(diff k (X : A[X]) * polynomialFormInclusion k A (polynomialCoefficientD k A p)) := by
  rw [d_diff_mul, d_polynomialFormInclusion, mul_add]
  have hzero (x : Forms k A[X]) : diff k (X : A[X]) * (diff k X * x) = 0 := by
    rw [← mul_assoc, diff_mul_self, zero_mul]
  rw [hzero, add_zero]

/-- The differential of `α + dX ∧ β` is `d_A α + dX ∧ (∂_X α - d_A β)`.
Blueprint: `lem:dr-polynomial-splitting`. -/
theorem d_polynomialForm_components (a b : PolynomialModule A (Forms k A)) :
    d k (polynomialFormInclusion k A a + diff k (X : A[X]) * polynomialFormInclusion k A b) =
      polynomialFormInclusion k A (polynomialCoefficientD k A a) +
        diff k (X : A[X]) * polynomialFormInclusion k A
          (coefficientDerivative k A a - polynomialCoefficientD k A b) := by
  rw [map_add, d_polynomialFormInclusion, d_diff_X_mul_polynomialFormInclusion]
  simp only [map_sub, mul_sub]
  abel

/-- The decomposition intertwines `d` with its coefficient/variable matrix. -/
theorem polynomialFormDecomposition_d (x : Forms k A[X]) :
    polynomialFormDecomposition k A (d k x) =
      (polynomialCoefficientD k A (polynomialFormDecomposition k A x).1,
        coefficientDerivative k A (polynomialFormDecomposition k A x).1 -
          polynomialCoefficientD k A (polynomialFormDecomposition k A x).2) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (polynomialFormDecomposition k A).symm.surjective x
  simp only [polynomialFormDecomposition_symm_apply,
    d_polynomialForm_components, polynomialFormDecomposition_inclusion_add_diff_X_mul]

end OrlikSolomon.DeRham
