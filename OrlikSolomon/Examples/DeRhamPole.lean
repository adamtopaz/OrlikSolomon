/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
module

public import OrlikSolomon.DeRham.Pole.Degree
public import OrlikSolomon.Examples.DeRhamHomotopy
public import OrlikSolomon.Examples.DeRhamLog

/-!
# Regressions for global pole comparison

The inclusion-induced comparison is bijective for the disconnected pair `(k × k[X], (1, X))`
over `ℚ`, although no derivation takes this equation to one. The same comparison and its degreewise
inverse apply to a unit equation and to actual zero coefficients. On the punctured rational affine
line, explicit formulas check the inverse pole-order coefficient and the primitive it produces.
The global positive-integer unit hypothesis fails in characteristic two.

## Main results

* `productPolynomial_logComparison_and_no_global_normal`: full comparison on the disconnected
  rational algebra, together with the obstruction to global normalization.
* `productPolynomial_logComparison_degree_inverse`: the actual comparison map is inverse to
  the degreewise inverse on that pair.
* `unitPolynomial_logComparison`: comparison for the unit equation on `ℚ[X]`, with empty divisor.
* `polynomial_positivePoleHomotopy_theta` and `polynomial_primitive_invSelf_pow_theta`: the
  coefficient `-(m + 1)⁻¹` on the rational affine line and its actual primitive.
* `zero_logComparison` and `zero_logComparison_degree_inverse`: comparison and its degreewise
  inverse over the actual zero coefficient ring.

Blueprint: `thm:dr-pole-contraction`, `thm:dr-comparison`, `prop:dr-unit-example`,
`prop:dr-zero-example`, and `prop:dr-product-example`.
-/

@[expose] public section
noncomputable section

namespace OrlikSolomon.DeRham.Examples

open Polynomial Sanity

/-- The canonical comparison holds for the disconnected rational pair, even though no vector field
satisfies the stronger, incorrect global normalization `v(f) = 1`. -/
theorem productPolynomial_logComparison_and_no_global_normal :
    Function.Bijective (LogCohomology.toCohomology ℚ (productPolynomialEquation ℚ)
      (Localization.Away (productPolynomialEquation ℚ))) ∧
    ∀ v : Derivation ℚ (ℚ × ℚ[X]) (ℚ × ℚ[X]), v (productPolynomialEquation ℚ) ≠ 1 :=
  ⟨logToLocalizationQuasiIso ℚ _ _ isUnit_natCast_add_one_rat
      (productPolynomial_isSmoothPrincipalPair ℚ), productPolynomial_no_global_normal ℚ⟩

/-- The normal vector field used by pole contraction is only normal modulo the equation. -/
theorem productPolynomial_euler_normal_modulo :
    productPolynomialNormal ℚ (productPolynomialEquation ℚ) =
      1 + productPolynomialEquation ℚ * (-1, 0) ∧
    productPolynomialNormal ℚ (productPolynomialEquation ℚ) ≠ 1 :=
  ⟨productPolynomialNormal_equation ℚ, productPolynomial_no_global_normal ℚ _⟩

/-- The degreewise inverse on the disconnected example is a genuine inverse to inclusion-induced
comparison, with no assumption that the normal derivation takes the equation to one. -/
theorem productPolynomial_logComparison_degree_inverse (n : ℕ)
    (x : Cohomology.degree ℚ (Localization.Away (productPolynomialEquation ℚ)) n) :
    LogCohomology.toCohomology ℚ (productPolynomialEquation ℚ)
        (Localization.Away (productPolynomialEquation ℚ))
        ((logToLocalizationDegreeEquiv ℚ _ _ isUnit_natCast_add_one_rat
          (productPolynomial_isSmoothPrincipalPair ℚ) n).symm x) = x :=
  toCohomology_logToLocalizationDegreeEquiv_symm _ _ _ _ _ _ _

/-- The unit equation on the rational affine line is a smooth principal pair with zero closed
algebra. -/
theorem unitPolynomial_isSmoothPrincipalPair :
    IsSmoothPrincipalPair (1 : ℚ[X]) (Ideal.Quotient.mkₐ ℚ (Ideal.span {(1 : ℚ[X])})) := by
  have : Subsingleton (ℚ[X] ⧸ Ideal.span {(1 : ℚ[X])}) :=
    unit_quotient_subsingleton (1 : ℚ[X]ˣ)
  exact .of_quotient isUnit_one.mem_nonZeroDivisors

/-- A unit equation with empty divisor is covered by global logarithmic comparison. -/
theorem unitPolynomial_logComparison :
    Function.Bijective
      (LogCohomology.toCohomology ℚ (1 : ℚ[X]) (Localization.Away (1 : ℚ[X]))) :=
  logToLocalizationQuasiIso ℚ _ _ isUnit_natCast_add_one_rat unitPolynomial_isSmoothPrincipalPair

/-- In particular, the inverse on the degree-zero piece exists for a unit equation. -/
theorem unitPolynomial_logComparison_degree_zero_inverse
    (x : Cohomology.degree ℚ (Localization.Away (1 : ℚ[X])) 0) :
    LogCohomology.toCohomology ℚ (1 : ℚ[X]) (Localization.Away (1 : ℚ[X]))
        ((logToLocalizationDegreeEquiv ℚ _ _ isUnit_natCast_add_one_rat
          unitPolynomial_isSmoothPrincipalPair 0).symm x) = x :=
  toCohomology_logToLocalizationDegreeEquiv_symm _ _ _ _ _ _ _

/-- The zero equation on the actual zero algebra is covered, since all positive integers are units
in the zero coefficient ring. -/
theorem zero_logComparison :
    Function.Bijective
      (LogCohomology.toCohomology PUnit (0 : PUnit) (Localization.Away (0 : PUnit))) :=
  logToLocalizationQuasiIso PUnit _ _ isUnit_natCast_add_one_zero
    (isSmoothPrincipalPair_of_subsingleton (k := PUnit) (0 : PUnit))

/-- The degreewise inverse is defined in every degree over the zero coefficient ring, with its
source and target the actual cohomology pieces. -/
theorem zero_logComparison_degree_inverse (n : ℕ)
    (x : Cohomology.degree PUnit (Localization.Away (0 : PUnit)) n) :
    LogCohomology.toCohomology PUnit (0 : PUnit) (Localization.Away (0 : PUnit))
        ((logToLocalizationDegreeEquiv PUnit _ _ isUnit_natCast_add_one_zero
          (isSmoothPrincipalPair_of_subsingleton (k := PUnit) (0 : PUnit)) n).symm x) = x :=
  toCohomology_logToLocalizationDegreeEquiv_symm _ _ _ _ _ _ _

/-- The negative-degree equivalence is also defined for the actual zero ring. -/
example (x : Cohomology.grading PUnit (Localization.Away (0 : PUnit)) (-1)) :
    LogCohomology.toCohomology PUnit (0 : PUnit) (Localization.Away (0 : PUnit))
        ((logToLocalizationGradingEquiv PUnit _ _ isUnit_natCast_add_one_zero
          (isSmoothPrincipalPair_of_subsingleton (k := PUnit) (0 : PUnit)) (-1)).symm x) = x :=
  toCohomology_logToLocalizationGradingEquiv_symm _ _ _ _ _ _ _

section Polynomial

variable (T : Type*) [CommRing T] [Algebra ℚ T] [Algebra ℚ[X] T] [IsScalarTower ℚ ℚ[X] T]
  [IsLocalization.Away (X : ℚ[X]) T]

/-- On the rational affine line, Euler contraction sends the logarithmic class `[dX/X]` to `[1]`.
Blueprint: `lem:dr-euler`. -/
theorem polynomial_logQuotientEulerContraction_theta :
    logQuotientEulerContraction ℚ (X : ℚ[X]) T (derivative' (R := ℚ))
        (Submodule.Quotient.mk (logTheta ℚ (X : ℚ[X]) T)) =
      Submodule.Quotient.mk (1 : logForms ℚ (X : ℚ[X]) T) := by
  rw [logQuotientEulerContraction_mk]
  congr 1
  apply Subtype.ext
  rw [coe_logEulerContraction, coe_logTheta, formContraction_logEulerDerivation_theta]
  simp

/-- In positive pole order `m + 1`, the contracting homotopy sends `[dX/X]` to
`-(m + 1)⁻¹ [1]`. This checks the coefficient and successor indexing on the rational affine line.
Blueprint: `thm:dr-pole-contraction`. -/
theorem polynomial_positivePoleHomotopy_theta (m : ℕ) :
    positivePoleHomotopy ℚ (X : ℚ[X]) T m (derivative' (R := ℚ))
        (isUnit_natCast_add_one_rat m) (Submodule.Quotient.mk (logTheta ℚ (X : ℚ[X]) T)) =
      (-(m + 1 : ℚ)⁻¹) •
        (Submodule.Quotient.mk (1 : logForms ℚ (X : ℚ[X]) T) :
          logForms ℚ (X : ℚ[X]) T ⧸ logIdeal ℚ (X : ℚ[X]) T) := by
  rw [positivePoleHomotopy_apply, polynomial_logQuotientEulerContraction_theta,
    Units.val_inv_eq_inv_val, IsUnit.unit_spec]

/-- The homotopy coefficient gives the actual primitive of `X^{-(m+2)} dX`. At `m = 0` this
is `d(-1/X) = X⁻² dX`, and at `m = 1` it is `d(-1/(2X²)) = X⁻³ dX`.
Blueprint: `thm:dr-pole-contraction`. -/
theorem polynomial_primitive_invSelf_pow_theta (m : ℕ) :
    d ℚ ((-(m + 1 : ℚ)⁻¹) •
        ((IsLocalization.Away.invSelf (X : ℚ[X]) : T) ^ (m + 1) • (1 : Forms ℚ T))) =
      (IsLocalization.Away.invSelf (X : ℚ[X]) : T) ^ (m + 1) • theta ℚ (X : ℚ[X]) T := by
  have hne : (m + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hd : d ℚ (1 : Forms ℚ T) = 0 := by simp
  have hs : ((m + 1 : ℕ) : ℚ[X]) • (theta ℚ (X : ℚ[X]) T * 1) =
      (m + 1 : ℚ) • theta ℚ (X : ℚ[X]) T := by
    rw [mul_one, Nat.cast_smul_eq_nsmul, ← Nat.cast_add_one, Nat.cast_smul_eq_nsmul]
  rw [map_smul, d_invSelf_pow_smul_eq_theta, hd, hs, zero_sub, smul_neg,
    smul_comm ((IsLocalization.Away.invSelf (X : ℚ[X]) : T) ^ (m + 1)), smul_neg, smul_smul,
    neg_mul, inv_mul_cancel₀ hne, neg_smul, neg_neg, one_smul]

end Polynomial

/-- The global positive-integer unit hypothesis fails in characteristic two. -/
example : ¬ ∀ n : ℕ, IsUnit (n + 1 : ZMod 2) :=
  not_forall_isUnit_natCast_add_one_charTwo

end OrlikSolomon.DeRham.Examples
