/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Degree
public import OrlikSolomon.Examples.DeRhamHomotopy
public import OrlikSolomon.Examples.DeRhamLog

/-!
# Regressions for global pole comparison

The inclusion-induced comparison is bijective for the disconnected pair `(k × k[X], (1, X))`
over `ℚ`, although no derivation takes this equation to one. The same comparison and its degreewise
inverse apply to a unit equation and to actual zero coefficients. The positive-integer unit
hypothesis is retained: the earlier characteristic-two regression shows that it fails there.

## Main results

* `productPolynomial_logComparison_and_no_global_normal`: full comparison on the disconnected
  rational algebra, together with the obstruction to global normalization.
* `productPolynomial_logComparison_degree_inverse`: the actual comparison map is inverse to
  the degreewise inverse on that pair.
* `unitPolynomial_logComparison`: comparison for the unit equation on `ℚ[X]`, with empty divisor.
* `zero_logComparison` and `zero_logComparison_degree_inverse`: comparison and its degreewise
  inverse over the actual zero coefficient ring.

Blueprint: `thm:dr-comparison`, `prop:dr-unit-example`, `prop:dr-zero-example`, and
`prop:dr-product-example`.
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

/-- Pole comparison does not silently discard its coefficient hypothesis in characteristic two. -/
example : ¬ ∀ n : ℕ, IsUnit (n + 1 : ZMod 2) :=
  not_forall_isUnit_natCast_add_one_charTwo

end OrlikSolomon.DeRham.Examples
