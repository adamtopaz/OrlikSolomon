/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Euler
public import OrlikSolomon.Examples.DeRhamCalculations.Torus
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Matching differential forms on the projective-line charts

The two affine-line charts meet in the Laurent ring, with coordinate maps `X ↦ T` and
`X ↦ T⁻¹`. Their matching degree-zero forms are the diagonal constants, and their matching
positive-degree forms vanish. These statements hold over every commutative coefficient ring.

## Main declarations

* `matchingPolynomials_eq_constants`: the polynomial intersection consists of constants.
* `matchingFormsZeroEquiv`: the matching degree-zero forms are canonically the coefficient ring.
* `matchingForms_positive_subsingleton`: all matching positive-degree forms vanish.
* `closedLaurentZero_eq_constant`: a closed Laurent function in characteristic zero is constant.

These are the algebraic chart computations used for the actual global differential forms and
two-chart Čech calculation of the projective line. Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section
noncomputable section

open Polynomial ExteriorAlgebra
open OrlikSolomon.DeRham
open scoped LaurentPolynomial

namespace OrlikSolomon.Geometric.Examples.NonAffine

universe u

section CommutativeRing

variable {k : Type u} [CommRing k]

private lemma toLaurent_coeff_nat (p : k[X]) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ _

private lemma toLaurent_coeff_neg (p : k[X]) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = n at hm
  omega

/-- Polynomials that agree under inverse Laurent coordinates are the same constant polynomial.
This also computes the global regular functions of the two-chart projective line.

Blueprint: `prop:geo-nonaffine`. -/
lemma matchingPolynomials_eq_constants (p q : k[X])
    (h : p.toLaurent = LaurentPolynomial.invert q.toLaurent) :
    p = C (p.coeff 0) ∧ q = C (p.coeff 0) := by
  have hp (n : ℕ) (hn : n ≠ 0) : p.coeff n = 0 := by
    have hh := congrArg (fun x : LaurentPolynomial k => x.coeff (n : ℤ)) h
    rw [toLaurent_coeff_nat, LaurentPolynomial.invert_apply,
      toLaurent_coeff_neg q _ (by omega)] at hh
    exact hh
  have hq (n : ℕ) (hn : n ≠ 0) : q.coeff n = 0 := by
    have hh := congrArg (fun x : LaurentPolynomial k => x.coeff (-(n : ℤ))) h
    rw [toLaurent_coeff_neg p _ (by omega), LaurentPolynomial.invert_apply,
      neg_neg, toLaurent_coeff_nat] at hh
    exact hh.symm
  have h0 : p.coeff 0 = q.coeff 0 := by
    have hh := congrArg (fun x : LaurentPolynomial k => x.coeff 0) h
    rw [LaurentPolynomial.invert_apply, neg_zero] at hh
    exact (toLaurent_coeff_nat p 0).symm.trans (hh.trans (toLaurent_coeff_nat q 0))
  constructor
  · ext n
    by_cases hn : n = 0
    · subst n; simp
    · simp [coeff_C, hn, hp n hn]
  · ext n
    by_cases hn : n = 0
    · subst n; simpa using h0.symm
    · simp [coeff_C, hn, hq n hn]

/-- Every polynomial one-form is a polynomial multiple of `dX`. -/
lemma polynomialOneForm_eq_smul_diff (x : ⋀[k[X]]^1 Ω[k[X]⁄k]) :
    ∃ a : k[X], (x : Forms k k[X]) = a • diff k (X : k[X]) := by
  obtain ⟨m, hm⟩ := (mem_exteriorPower_one_iff k).1 x.property
  refine ⟨KaehlerDifferential.polynomialEquiv k m, hm.symm.trans ?_⟩
  have h := congrArg (ExteriorAlgebra.ι k[X])
    ((KaehlerDifferential.polynomialEquiv k).symm_apply_apply m)
  simpa only [KaehlerDifferential.polynomialEquiv_symm, LinearMap.map_smul, diff_apply] using h.symm

/-- Exterior powers of polynomial differentials vanish in degrees at least two. -/
lemma polynomialForms_subsingleton (n : ℕ) :
    Subsingleton (⋀[k[X]]^(n + 2) Ω[k[X]⁄k]) := by
  have hs : Submodule.span k[X]
      (Set.range (fun _ : Unit => KaehlerDifferential.D k k[X] X)) = ⊤ := by
    apply top_unique
    intro m _
    have hm := (KaehlerDifferential.polynomialEquiv k).symm_apply_apply m
    rw [KaehlerDifferential.polynomialEquiv_symm] at hm
    rw [← hm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
  exact exteriorPower.subsingleton_of_span_eq_top_of_card_lt _ hs (n + 2) (by simp)

/-- Compatibility of the scalar actions on the Laurent extension of the polynomial ring. -/
private local instance laurentTower : IsScalarTower k k[X] (LaurentPolynomial k) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    simp only [Polynomial.algebraMap_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self])

private def chartEuler : Derivation k (LaurentPolynomial k) (LaurentPolynomial k) :=
  logEulerDerivation k (X : k[X]) (LaurentPolynomial k) derivative'

private lemma chartEuler_T_one :
    chartEuler (k := k) (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  have h := logEulerDerivation_algebraMap k (X : k[X]) (LaurentPolynomial k) derivative' X
  simpa only [chartEuler, LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X, derivative'_apply, derivative_X, mul_one] using h

private lemma chartEuler_T_neg_one :
    chartEuler (k := k) (LaurentPolynomial.T (-1)) = -LaurentPolynomial.T (-1) := by
  have h := (chartEuler (k := k)).leibniz_of_mul_eq_one
    (show (LaurentPolynomial.T (-1) : LaurentPolynomial k) * LaurentPolynomial.T 1 = 1 by
      rw [← LaurentPolynomial.T_add]; norm_num)
  rw [chartEuler_T_one] at h
  rw [smul_eq_mul, neg_mul, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add] at h
  exact h

/-- The two chart modules of one-forms have zero intersection on their overlap. -/
lemma matchingOneForms_eq_zero (p q : ⋀[k[X]]^1 Ω[k[X]⁄k])
    (h : Forms.mapPower (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) 1 p =
      Forms.mapPower (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) 1 q) :
    p = 0 ∧ q = 0 := by
  obtain ⟨a, ha⟩ := polynomialOneForm_eq_smul_diff p
  obtain ⟨b, hb⟩ := polynomialOneForm_eq_smul_diff q
  have hh := congrArg (fun x : ⋀[LaurentPolynomial k]^1 Ω[LaurentPolynomial k⁄k] =>
    ExteriorAlgebra.algebraMapInv (formContraction k (chartEuler (k := k)) x.val)) h
  change ExteriorAlgebra.algebraMapInv (formContraction k (chartEuler (k := k))
    (Forms.map _ p.val)) = ExteriorAlgebra.algebraMapInv (formContraction k (chartEuler (k := k))
    (Forms.map _ q.val)) at hh
  rw [ha, hb, Forms.map_smul, Forms.map_smul, Forms.map_diff, Forms.map_diff] at hh
  simp only [Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, LaurentPolynomial.invert_T,
    formContraction_diff, chartEuler_T_one, chartEuler_T_neg_one,
    map_smul, map_neg, AlgHom.commutes, Algebra.algebraMap_self] at hh
  change a.toLaurent * LaurentPolynomial.T 1 =
    LaurentPolynomial.invert b.toLaurent * -LaurentPolynomial.T (-1) at hh
  have ha0 : a = 0 := by
    ext n
    have hc := congrArg (fun x : LaurentPolynomial k => x.coeff ((n : ℤ) + 1)) hh
    simp only [LaurentPolynomial.T, mul_neg, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      AddMonoidAlgebra.coeff_mul_single_apply, mul_one, LaurentPolynomial.invert_apply] at hc
    have hn : -((n : ℤ) + 1 + -(-1)) < 0 := by omega
    rw [toLaurent_coeff_neg b _ hn] at hc
    simp only [add_neg_cancel_right, toLaurent_coeff_nat, neg_zero] at hc
    simpa only [coeff_zero] using hc
  have hb0 : b = 0 := by
    rw [ha0, map_zero, zero_mul] at hh
    have hu := congrArg (fun x : LaurentPolynomial k => x * LaurentPolynomial.T 1) hh
    simp only [zero_mul, mul_neg, neg_mul, mul_assoc, ← LaurentPolynomial.T_add,
      neg_add_cancel, LaurentPolynomial.T_zero, mul_one] at hu
    apply Polynomial.toLaurent_injective
    apply LaurentPolynomial.invert.injective
    simpa only [map_zero] using (neg_eq_zero.mp hu.symm)
  constructor
  · apply Subtype.ext
    change p.val = 0
    simpa only [ha0, zero_smul] using ha
  · apply Subtype.ext
    change q.val = 0
    simpa only [hb0, zero_smul] using hb

/-- Matching polynomial forms on the two charts with inverse overlap coordinates. -/
def matchingForms (k : Type u) [CommRing k] (n : ℕ) :
    Submodule k ((⋀[k[X]]^n Ω[k[X]⁄k]) × (⋀[k[X]]^n Ω[k[X]⁄k])) :=
  LinearMap.ker
    ((Forms.mapPower (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) n).comp
        (LinearMap.fst k _ _) -
      (Forms.mapPower (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) n).comp
        (LinearMap.snd k _ _))

/-- Membership is equality of the two restrictions to the Laurent overlap. -/
@[simp]
lemma mem_matchingForms {n : ℕ} (p q : ⋀[k[X]]^n Ω[k[X]⁄k]) :
    (p, q) ∈ matchingForms k n ↔
      Forms.mapPower (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) n p =
        Forms.mapPower (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) n q := by
  simp only [matchingForms, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero]

/-- A scalar as a constant polynomial differential form of degree zero. -/
def polynomialConstantForm : k →ₗ[k] ⋀[k[X]]^0 Ω[k[X]⁄k] :=
  (Algebra.linearMap k (Forms k k[X])).codRestrict
    ((⋀[k[X]]^0 Ω[k[X]⁄k]).restrictScalars k) fun c => by
    change algebraMap k (Forms k k[X]) c ∈ ⋀[k[X]]^0 Ω[k[X]⁄k]
    rw [IsScalarTower.algebraMap_apply k k[X] (Forms k k[X])]
    exact algebraMap_mem_exteriorPower_zero k _

/-- The underlying form of a polynomial constant is its scalar image. -/
@[simp]
lemma polynomialConstantForm_coe (c : k) :
    (polynomialConstantForm c : Forms k k[X]) = algebraMap k (Forms k k[X]) c := rfl

/-- Constant functions give matching degree-zero forms on the two charts. -/
def matchingConstants : k →ₗ[k] matchingForms k 0 :=
  ((polynomialConstantForm (k := k)).prod polynomialConstantForm).codRestrict
    (matchingForms k 0) fun c => by
    apply (mem_matchingForms _ _).2
    apply Subtype.ext
    change Forms.map _ (algebraMap k (Forms k k[X]) c) =
      Forms.map _ (algebraMap k (Forms k k[X]) c)
    rw [AlgHom.commutes, AlgHom.commutes]

/-- Both charts of a matching constant are that polynomial constant form. -/
@[simp]
lemma matchingConstants_val (c : k) :
    (matchingConstants c).val = (polynomialConstantForm c, polynomialConstantForm c) := rfl

private lemma matchingConstants_injective : Function.Injective (matchingConstants (k := k)) := by
  intro a b h
  have hh := congrArg (fun x : matchingForms k 0 =>
    (ExteriorAlgebra.algebraMapInv x.val.1.val).coeff 0) h
  change (ExteriorAlgebra.algebraMapInv (algebraMap k (Forms k k[X]) a)).coeff 0 =
    (ExteriorAlgebra.algebraMapInv (algebraMap k (Forms k k[X]) b)).coeff 0 at hh
  rw [IsScalarTower.algebraMap_apply k k[X] (Forms k k[X]),
    IsScalarTower.algebraMap_apply k k[X] (Forms k k[X]),
    AlgHom.commutes, AlgHom.commutes] at hh
  simpa only [Algebra.algebraMap_self, Polynomial.algebraMap_apply, RingHom.id_apply,
    coeff_C_zero] using hh

private lemma matchingConstants_surjective : Function.Surjective (matchingConstants (k := k)) := by
  intro x
  obtain ⟨p, hp⟩ := (mem_exteriorPower_zero_iff k).1 x.val.1.property
  obtain ⟨q, hq⟩ := (mem_exteriorPower_zero_iff k).1 x.val.2.property
  have h := (mem_matchingForms _ _).1 x.property
  have hh := congrArg (fun y : ⋀[LaurentPolynomial k]^0 Ω[LaurentPolynomial k⁄k] =>
    ExteriorAlgebra.algebraMapInv y.val) h
  change ExteriorAlgebra.algebraMapInv (Forms.map _ x.val.1.val) =
    ExteriorAlgebra.algebraMapInv (Forms.map _ x.val.2.val) at hh
  rw [← hp, ← hq, Forms.map_algebraMap, Forms.map_algebraMap,
    AlgHom.commutes, AlgHom.commutes] at hh
  simp only [Algebra.algebraMap_self, Polynomial.toLaurentAlg_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom] at hh
  obtain ⟨hp0, hq0⟩ := matchingPolynomials_eq_constants p q hh
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · change algebraMap k (Forms k k[X]) (p.coeff 0) = x.val.1.val
    rw [IsScalarTower.algebraMap_apply k k[X] (Forms k k[X]), Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ← hp0, hp]
  · change algebraMap k (Forms k k[X]) (p.coeff 0) = x.val.2.val
    rw [IsScalarTower.algebraMap_apply k k[X] (Forms k k[X]), Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ← hq0, hq]

/-- The matching degree-zero forms are exactly the diagonal constants. -/
def matchingFormsZeroEquiv (k : Type u) [CommRing k] : k ≃ₗ[k] matchingForms k 0 :=
  LinearEquiv.ofBijective matchingConstants (by
    exact ⟨matchingConstants_injective, matchingConstants_surjective⟩)

/-- The first chart of a matching constant is that constant form. -/
@[simp]
lemma matchingFormsZeroEquiv_apply (c : k) :
    ((matchingFormsZeroEquiv k c).val.1 : Forms k k[X]) =
      algebraMap k (Forms k k[X]) c := rfl

/-- The second chart of a matching constant is that constant form. -/
@[simp]
lemma matchingFormsZeroEquiv_apply_snd (c : k) :
    ((matchingFormsZeroEquiv k c).val.2 : Forms k k[X]) =
      algebraMap k (Forms k k[X]) c := rfl

/-- There are no nonzero matching positive-degree forms on the two projective-line charts. -/
instance matchingForms_positive_subsingleton (n : ℕ) :
    Subsingleton (matchingForms k (n + 1)) := by
  suffices ∀ x : matchingForms k (n + 1), x = 0 from
    ⟨fun x y => (this x).trans (this y).symm⟩
  intro x
  cases n with
  | zero =>
    obtain ⟨h1, h2⟩ := matchingOneForms_eq_zero x.val.1 x.val.2
      ((mem_matchingForms _ _).1 x.property)
    apply Subtype.ext
    exact Prod.ext h1 h2
  | succ n =>
    have := polynomialForms_subsingleton (k := k) n
    apply Subtype.ext
    exact Subsingleton.elim _ _

end CommutativeRing

section CharacteristicZero

variable {k : Type u} [Field k] [CharZero k]

/-- A closed Laurent function over a characteristic-zero field is constant. This is a
representative-level consequence of the punctured-line degree-zero cohomology computation.

Blueprint: `prop:geo-nonaffine`. -/
lemma closedLaurentZero_eq_constant (x : ⋀[LaurentPolynomial k]^0 Ω[LaurentPolynomial k⁄k])
    (hx : d k (x : Forms k (LaurentPolynomial k)) = 0) :
    ∃ c : k, (x : Forms k (LaurentPolynomial k)) =
      algebraMap k (Forms k (LaurentPolynomial k)) c := by
  obtain ⟨⟨a, b⟩, hab⟩ := (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).surjective
    (Cohomology.mk x.val hx)
  have hz : b = 0 :=
    (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_zero_iff k a b).1
      (hab.symm ▸ Cohomology.mk_mem_degree x.property hx)
  subst b
  have hc := hab.symm
  rw [OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_apply, map_zero, mul_zero, add_zero] at hc
  change Cohomology.mk x.val hx = algebraMap k (Cohomology k (LaurentPolynomial k)) a at hc
  have hh := congrArg (Cohomology.toDegreeZero k (LaurentPolynomial k)) hc
  rw [Cohomology.toDegreeZero_mk, AlgHom.commutes] at hh
  obtain ⟨p, hp⟩ := (mem_exteriorPower_zero_iff k).1 x.property
  rw [← hp, AlgHom.commutes] at hh
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hh
  refine ⟨a, ?_⟩
  rw [← hp, hh,
    ← IsScalarTower.algebraMap_apply k (LaurentPolynomial k) (Forms k (LaurentPolynomial k))]

end CharacteristicZero

end OrlikSolomon.Geometric.Examples.NonAffine
