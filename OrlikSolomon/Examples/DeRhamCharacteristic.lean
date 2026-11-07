/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Cohomology
public import OrlikSolomon.DeRham.Log.Cohomology
public import OrlikSolomon.DeRham.Instance.Twisted
public import OrlikSolomon.DeRham.Pole.Euler
public import OrlikSolomon.Geometry.SmoothAlg
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.CharP.Basic

/-!
# Positive-characteristic obstructions to de Rham invariance

In characteristic `p > 0`, the polynomial function `X^p` is a nonconstant closed function and
`X^(p-1) dX` is closed but not exact. A coefficient functional also detects the Laurent form
`X^(-p-1) dX`, which is neither exact nor cohomologous to a logarithmic form. Thus the two uses
of positive-integer denominators in polynomial homotopy and pole comparison are essential.

## Main results

* `d_algebraMap_X_pow_charP`, `X_pow_ne_C`, and `not_surjective_map_C_of_charP`: a nonconstant
  closed function and failure of affine-line invariance.
* `polynomialCharacteristicForm_not_exact` and `polynomialCharacteristicForm_class_ne_zero`:
  the actual one-form obstruction.
* `laurentCharacteristicForm_eq_T_smul_diff`, `laurentCharacteristicForm_not_exact`, and
  `laurentCharacteristicForm_not_cohomologous_log`: the actual Laurent pole obstruction and
  failure of logarithmic representatives.
* `not_surjective_logToLocalization_of_charP` and `not_surjective_twisted_map_C_of_charP`:
  failures of comparison and of the proposed ordinary model's affine-line map.

The statements hold over any nonzero commutative ring of positive characteristic, in particular
all characteristic-`p` fields. They impose neither a choice of prime field nor perfectness.

Blueprint: `prop:dr-characteristic-p`.
-/

@[expose] public section

noncomputable section

open Polynomial ExteriorAlgebra
open scoped LaurentPolynomial TensorProduct

namespace OrlikSolomon.DeRham.Examples

variable (k : Type*) [CommRing k]

/-- In positive characteristic, the function `X^p` is closed. -/
theorem d_algebraMap_X_pow_charP (p : ℕ) [CharP k p] :
    d k (algebraMap k[X] (Forms k k[X]) (X ^ p)) = 0 := by
  rw [d_algebraMap, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k p, CharP.cast_eq_zero,
    zero_smul]

/-- A positive power of the polynomial variable is not constant over a nonzero ring. -/
theorem X_pow_ne_C [Nontrivial k] {p : ℕ} (hp : 0 < p) (a : k) : (X : k[X]) ^ p ≠ C a := by
  intro h
  have he := congrArg Polynomial.natDegree h
  simp only [natDegree_X_pow, natDegree_C] at he
  omega

/-- The proposed affine-line cohomology map is not surjective in any positive characteristic.
The witness is the actual degree-zero class of `X^p`.

Blueprint: `prop:dr-characteristic-p`. -/
theorem not_surjective_map_C_of_charP [Nontrivial k] (p : ℕ) [CharP k p] (hp : 0 < p) :
    ¬ Function.Surjective (Cohomology.map (Polynomial.CAlgHom : k →ₐ[k] k[X])) := by
  intro h
  obtain ⟨c, hc⟩ := h (Cohomology.mk _ (d_algebraMap_X_pow_charP k p))
  have he := congrArg (Cohomology.toDegreeZero k k[X]) hc
  rw [Cohomology.toDegreeZero_map, Cohomology.toDegreeZero_mk_algebraMap] at he
  exact X_pow_ne_C k hp _ he.symm

/-- The polynomial one-form that detects the failure of integration in characteristic `p`. -/
def polynomialCharacteristicForm (p : ℕ) : Forms k k[X] :=
  (X : k[X]) ^ (p - 1) • diff k (X : k[X])

/-- The polynomial obstruction is a form of exterior degree one. -/
theorem polynomialCharacteristicForm_mem_exteriorPower_one (p : ℕ) :
    polynomialCharacteristicForm k p ∈ ⋀[k[X]]^1 Ω[k[X]⁄k] :=
  Submodule.smul_mem _ _ (diff_mem_exteriorPower_one k X)

private theorem diff_polynomial (a : k[X]) :
    diff k a = derivative a • diff k (X : k[X]) := by
  rw [diff_apply, KaehlerDifferential.polynomial_D_apply, map_smul, ι_D]

/-- The polynomial obstruction is closed, in every characteristic. -/
theorem d_polynomialCharacteristicForm (p : ℕ) : d k (polynomialCharacteristicForm k p) = 0 := by
  rw [polynomialCharacteristicForm, d_smul_diff, diff_polynomial, smul_mul_assoc, diff_mul_self,
    smul_zero]

private theorem polynomial_derivative_ne_X_pow_pred [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) (a : k[X]) : derivative a ≠ (X : k[X]) ^ (p - 1) := by
  intro he
  have hc := congrArg (fun b : k[X] => b.coeff (p - 1)) he
  have hz : (p : k) = 0 := CharP.cast_eq_zero k p
  have hcast : ((p - 1 : ℕ) : k) + 1 = (p : k) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hp]
  rw [coeff_derivative, Nat.sub_add_cancel hp, coeff_X_pow_self, hcast, hz, mul_zero] at hc
  exact zero_ne_one hc

/-- The closed form `X^(p-1) dX` is not the differential of any total polynomial form.

Blueprint: the one-form assertion of `prop:dr-characteristic-p`. -/
theorem polynomialCharacteristicForm_not_exact [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) : ¬ ∃ y : Forms k k[X], d k y = polynomialCharacteristicForm k p := by
  intro he
  have hdeg : polynomialCharacteristicForm k p ∈ ⋀[k[X]]^1 Ω[k[X]⁄k] :=
    Submodule.smul_mem _ _ (diff_mem_exteriorPower_one k X)
  obtain ⟨y, hy, he⟩ := exists_mem_exteriorPower_d_eq hdeg he
  obtain ⟨a, rfl⟩ := (mem_exteriorPower_zero_iff k).1 hy
  rw [d_algebraMap, diff_polynomial, polynomialCharacteristicForm] at he
  have hc := congrArg
    (fun x : Forms k k[X] => algebraMapInv (formContraction k derivative' x)) he
  simp only [map_smul, formContraction_diff, derivative'_apply, derivative_X, map_one] at hc
  simp only [smul_eq_mul, mul_one] at hc
  exact polynomial_derivative_ne_X_pow_pred k p hp a hc

/-- The polynomial one-form obstruction gives an actual nonzero de Rham cohomology class. -/
theorem polynomialCharacteristicForm_class_ne_zero [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) :
    Cohomology.mk (polynomialCharacteristicForm k p) (d_polynomialCharacteristicForm k p) ≠ 0 :=
  fun h => polynomialCharacteristicForm_not_exact k p hp (Cohomology.mk_eq_zero_iff.1 h)

private theorem algebraMapInv_map {A B : Type*} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (x : Forms k A) :
    algebraMapInv (Forms.map φ x) = φ (algebraMapInv x) := by
  induction x using Forms.induction with
  | word a l =>
    cases l with
    | nil => simp [word, Algebra.smul_def, Forms.map_algebraMap]
    | cons b l => simp [word_cons, map_mul, algebraMapInv_diff, Forms.map_diff]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem algebraMapInv_contraction_d {A : Type*} [CommRing A] [Algebra k A]
    (v : Derivation k A A) (x : Forms k A) :
    algebraMapInv (formContraction k v (d k x)) = v (algebraMapInv x) := by
  induction x using Forms.induction with
  | word a l =>
    rw [d_smul_word, formContraction_diff_mul, map_sub, map_smul, map_mul,
      algebraMapInv_diff, zero_mul, sub_zero]
    cases l with
    | nil => simp [word, Algebra.smul_def]
    | cons b l => simp [word_cons, map_mul, algebraMapInv_diff]
  | add x y hx hy => simp only [map_add, hx, hy]

private def characteristicEuler : Derivation k k[T;T⁻¹] k[T;T⁻¹] :=
  logEulerDerivation k (X : k[X]) k[T;T⁻¹] derivative'

private theorem characteristicEuler_T_one :
    characteristicEuler k (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  have h := logEulerDerivation_algebraMap k (X : k[X]) k[T;T⁻¹] derivative' X
  simpa only [characteristicEuler, LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X,
    derivative'_apply, derivative_X, mul_one] using h

private theorem characteristicEuler_T_neg_one :
    characteristicEuler k (LaurentPolynomial.T (-1)) = -LaurentPolynomial.T (-1) := by
  have h := (characteristicEuler k).leibniz_of_mul_eq_one
    (show (LaurentPolynomial.T (-1) : k[T;T⁻¹]) * LaurentPolynomial.T 1 = 1 by
      rw [← LaurentPolynomial.T_add]; norm_num)
  rw [characteristicEuler_T_one] at h
  rw [smul_eq_mul, neg_mul, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add] at h
  exact h

private theorem characteristicEuler_T (n : ℤ) :
    characteristicEuler k (LaurentPolynomial.T n) = (n : k) • LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [LaurentPolynomial.T_add, Derivation.leibniz, ih, characteristicEuler_T_one]
    simp only [smul_eq_mul, mul_smul_comm, Int.cast_add, Int.cast_one, add_smul, one_smul]
    rw [mul_comm (LaurentPolynomial.T 1)]
    exact add_comm _ _
  | pred n ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, Derivation.leibniz, ih,
      characteristicEuler_T_neg_one]
    simp only [smul_eq_mul, mul_neg, mul_smul_comm, Int.cast_add, Int.cast_neg,
      Int.cast_one, add_smul, neg_smul, one_smul]
    rw [mul_comm (LaurentPolynomial.T (-1))]
    abel

private theorem characteristicEuler_coeff (a : k[T;T⁻¹]) (n : ℤ) :
    (characteristicEuler k a).coeff n = (n : k) * a.coeff n := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      ha, hb, mul_add]
  | C_mul_T m a =>
    rw [LaurentPolynomial.C_eq_algebraMap, ← Algebra.smul_def]
    change ((characteristicEuler k).toLinearMap (a • LaurentPolynomial.T m)).coeff n = _
    rw [map_smul]
    change (a • characteristicEuler k (LaurentPolynomial.T m)).coeff n = _
    rw [characteristicEuler_T]
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      LaurentPolynomial.T_apply]
    split_ifs with hm
    · subst m; ring
    · simp

/-- The Laurent one-form `X^(-p-1) dX`, written as `X^(-p) (dX/X)`. -/
def laurentCharacteristicForm (p : ℕ) : Forms k k[T;T⁻¹] :=
  (LaurentPolynomial.T (-(p : ℤ)) : k[T;T⁻¹]) • theta k (X : k[X]) k[T;T⁻¹]

private theorem invSelf_X_eq_T_neg_one :
    (IsLocalization.Away.invSelf (X : k[X]) : k[T;T⁻¹]) = LaurentPolynomial.T (-1) := by
  have h := congrArg (fun z : k[T;T⁻¹] => z * LaurentPolynomial.T (-1))
    (invSelf_mul_self (X : k[X]) (T := k[T;T⁻¹]))
  rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X] at h
  simpa only [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one, one_mul] using h

/-- The logarithmic notation for the obstruction is the literal Laurent form
`X^(-p-1) dX`. -/
theorem laurentCharacteristicForm_eq_T_smul_diff (p : ℕ) :
    laurentCharacteristicForm k p =
      (LaurentPolynomial.T (-(p : ℤ) - 1) : k[T;T⁻¹]) •
        diff k (LaurentPolynomial.T 1 : k[T;T⁻¹]) := by
  rw [laurentCharacteristicForm, theta_eq_invSelf_smul, invSelf_X_eq_T_neg_one,
    LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X, smul_smul,
    ← LaurentPolynomial.T_add, sub_eq_add_neg]

/-- The Laurent obstruction is a form of exterior degree one. -/
theorem laurentCharacteristicForm_mem_exteriorPower_one (p : ℕ) :
    laurentCharacteristicForm k p ∈ ⋀[k[T;T⁻¹]]^1 Ω[k[T;T⁻¹]⁄k] :=
  Submodule.smul_mem _ _ (theta_mem_exteriorPower_one k (X : k[X]) k[T;T⁻¹])

/-- The Laurent obstruction is closed in characteristic `p`, including the characteristic-zero
case `p = 0`, where it is the usual logarithmic one-form. -/
theorem d_laurentCharacteristicForm (p : ℕ) [CharP k p] :
    d k (laurentCharacteristicForm k p) = 0 := by
  have ht : (LaurentPolynomial.T (-(p : ℤ)) : k[T;T⁻¹]) =
      (LaurentPolynomial.T (-1)) ^ p := by
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega
  rw [laurentCharacteristicForm, d_smul, d_theta, smul_zero, add_zero, ht,
    Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k p, CharP.cast_eq_zero, zero_smul, zero_mul]

private theorem contraction_laurentCharacteristicForm (p : ℕ) :
    algebraMapInv (formContraction k (characteristicEuler k) (laurentCharacteristicForm k p)) =
      (LaurentPolynomial.T (-(p : ℤ)) : k[T;T⁻¹]) := by
  rw [laurentCharacteristicForm, map_smul]
  change algebraMapInv ((LaurentPolynomial.T (-(p : ℤ)) : k[T;T⁻¹]) •
    formContraction k (logEulerDerivation k (X : k[X]) k[T;T⁻¹] derivative')
      (theta k (X : k[X]) k[T;T⁻¹])) = _
  rw [formContraction_logEulerDerivation_theta]
  simp

private theorem obstruction_coefficient_d (p : ℕ) [CharP k p] (y : Forms k k[T;T⁻¹]) :
    (algebraMapInv (formContraction k (characteristicEuler k) (d k y))).coeff (-(p : ℤ)) = 0 := by
  rw [algebraMapInv_contraction_d, characteristicEuler_coeff]
  simp only [Int.cast_neg, Int.cast_natCast, CharP.cast_eq_zero, neg_zero, zero_mul]

/-- The Laurent form `X^(-p-1) dX` is not exact. This is an actual obstruction, rather than only
failure of a coefficient-unit hypothesis.

Blueprint: the pole obstruction of `prop:dr-characteristic-p`. -/
theorem laurentCharacteristicForm_not_exact [Nontrivial k] (p : ℕ) [CharP k p] :
    ¬ ∃ y : Forms k k[T;T⁻¹], d k y = laurentCharacteristicForm k p := by
  rintro ⟨y, hy⟩
  have h := obstruction_coefficient_d k p y
  rw [hy, contraction_laurentCharacteristicForm] at h
  simp only [LaurentPolynomial.T_apply, ite_true] at h
  exact one_ne_zero h

/-- The Laurent pole obstruction gives an actual nonzero cohomology class. -/
theorem laurentCharacteristicForm_class_ne_zero [Nontrivial k] (p : ℕ) [CharP k p] :
    Cohomology.mk (laurentCharacteristicForm k p) (d_laurentCharacteristicForm k p) ≠ 0 :=
  fun h => laurentCharacteristicForm_not_exact k p (Cohomology.mk_eq_zero_iff.1 h)

private theorem coeff_toLaurent_of_neg (a : k[X]) {n : ℤ} (hn : n < 0) :
    a.toLaurent.coeff n = 0 := by
  rw [← Finsupp.notMem_support_iff, LaurentPolynomial.support_coeff_toLaurent]
  simp only [Finset.mem_map, Nat.castEmbedding_apply]
  rintro ⟨m, _, hm⟩
  omega

private theorem obstruction_coefficient_log (p : ℕ) (hp : 0 < p)
    {x : Forms k k[T;T⁻¹]} (hx : x ∈ logForms k (X : k[X]) k[T;T⁻¹]) :
    (algebraMapInv (formContraction k (characteristicEuler k) x)).coeff (-(p : ℤ)) = 0 := by
  obtain ⟨ω, η, rfl⟩ := hx
  change (algebraMapInv (formContraction k
    (logEulerDerivation k (X : k[X]) k[T;T⁻¹] derivative')
    (logMk k (X : k[X]) k[T;T⁻¹] (ω, η) : Forms k k[T;T⁻¹]))).coeff _ = 0
  rw [formContraction_logEulerDerivation_logMk, algebraMapInv_map]
  exact coeff_toLaurent_of_neg k _ (by omega)

/-- No logarithmic form represents the Laurent obstruction even up to an arbitrary exact form.
Closedness of the proposed logarithmic representative need not be assumed.

Blueprint: the failure of logarithmic comparison in `prop:dr-characteristic-p`. -/
theorem laurentCharacteristicForm_not_cohomologous_log [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) :
    ¬ ∃ (x : logForms k (X : k[X]) k[T;T⁻¹]) (y : Forms k k[T;T⁻¹]),
      d k y = laurentCharacteristicForm k p - (x : Forms k k[T;T⁻¹]) := by
  rintro ⟨x, y, hy⟩
  have he := obstruction_coefficient_d k p y
  rw [hy, map_sub, map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    contraction_laurentCharacteristicForm, obstruction_coefficient_log k p hp x.property] at he
  simp only [LaurentPolynomial.T_apply, ite_true, sub_zero] at he
  exact one_ne_zero he

/-- The Laurent obstruction's class is outside the image of logarithmic cohomology. -/
theorem laurentCharacteristicForm_class_notMem_range [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) :
    Cohomology.mk (laurentCharacteristicForm k p) (d_laurentCharacteristicForm k p) ∉
      Set.range (LogCohomology.toCohomology k (X : k[X]) k[T;T⁻¹]) := by
  rintro ⟨c, hc⟩
  induction c with
  | mk x hx =>
    rw [LogCohomology.toCohomology_mk] at hc
    obtain ⟨y, hy⟩ := Cohomology.mk_eq_mk_iff.1 hc.symm
    exact laurentCharacteristicForm_not_cohomologous_log k p hp ⟨x, y, hy⟩

/-- Logarithmic comparison is genuinely not surjective in positive characteristic.
This conclusion is about actual cohomology classes, not the unit hypotheses of the comparison
proof.

Blueprint: the pole obstruction of `prop:dr-characteristic-p`. -/
theorem not_surjective_logToLocalization_of_charP [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) :
    ¬ Function.Surjective (LogCohomology.toCohomology k (X : k[X]) k[T;T⁻¹]) :=
  fun h => laurentCharacteristicForm_class_notMem_range k p hp (h _)

/-- The proposed Laurent-twisted ordinary de Rham model also fails affine-line invariance in
positive characteristic. This is an actual failure of its map, rather than a missing hypothesis
for the integration proof.

Blueprint: `prop:dr-characteristic-p`. -/
theorem not_surjective_twisted_map_C_of_charP [Nontrivial k] (p : ℕ) [CharP k p]
    (hp : 0 < p) :
    ¬ Function.Surjective
      (TwistedCohomology.map (Polynomial.CAlgHom : k →ₐ[k] k[X])) := by
  intro h
  apply not_surjective_map_C_of_charP k p hp
  intro c
  obtain ⟨z, hz⟩ := h ((1 : k[T;T⁻¹]) ⊗ₜ[k] c)
  refine ⟨TwistedCohomology.evalOne k k z, ?_⟩
  have he := congrArg (TwistedCohomology.evalOne k k[X]) hz
  simpa only [TwistedCohomology.evalOne_map, TwistedCohomology.evalOne_one_tmul] using he

end OrlikSolomon.DeRham.Examples
