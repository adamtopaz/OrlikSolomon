/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import OrlikSolomon.DeRham.Corollaries
public import OrlikSolomon.Examples.DeRhamCalculations.Torus
public import OrlikSolomon.Examples.DeRhamLog
public import OrlikSolomon.Examples.DeRhamMaps

/-!
# Worked de Rham calculations

For a unit equation the closed algebra is zero, the localization is the original algebra,
all localized forms are logarithmic, and the residue and Gysin maps vanish. For the actual
zero algebra, forms, ordinary cohomology and Laurent-twisted cohomology vanish in every degree.
These assertions use the existing maps and their actual algebra structures.
For the disconnected complement, the localization is the actual componentwise Laurent
extension, and its cohomology splits by closed idempotents without a Künneth theorem.

## Main results

* `unit_closed_subsingleton`: the closed algebra of a unit equation is zero.
* `unit_logForms_eq_top` and `unit_cohomologyMap_bijective`: a unit changes neither forms nor
  cohomology on localization; no hypothesis on characteristic is needed.
* `unit_residue_eq_zero` and `unit_gysin_eq_zero`: the two maps for the empty divisor are zero.
* `zero_form_eq_zero`, `zero_cohomology_eq_zero` and `zero_twistedCohomology_eq_zero`: actual
  vanishings, including degree zero.
* `productLocalizationEquiv`, `productLaurentCohomologyEquiv`, and
  `productLaurentCohomologyEquiv_mem_degree`: the componentwise localization and its
  degree-preserving cohomology equivalence, with no characteristic or nonzero-ring hypothesis.
* `productCohomologyEquiv` and its degree criterion: two constant classes and one logarithmic
  class, with all higher cohomology zero.
* `productLaurentCohomologyEquiv_theta` and `productPolynomial_residue_theta`: the logarithmic
  generator and its normalized residue in the disconnected example.

Blueprint: `prop:dr-unit-example`, `prop:dr-zero-example`, `prop:dr-product-example`.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped LaurentPolynomial

namespace OrlikSolomon.DeRham.Examples

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}

section Unit

variable (u : Aˣ)

/-- The closed algebra of a unit equation is zero, including for a certified quotient.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_closed_subsingleton (h : IsSmoothPrincipalPair (u : A) φ) : Subsingleton S := by
  have hzero : φ (u : A) = 0 := by
    rw [← RingHom.mem_ker, h.ker_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp (hzero ▸ u.isUnit.map φ))

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away (u : A) T]

include u in
/-- Localizing away from a unit leaves cohomology unchanged, over any coefficient ring.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_cohomologyMap_bijective :
    Function.Bijective (Cohomology.map (IsScalarTower.toAlgHom k A T)) := by
  let e := IsLocalization.atUnit A T (u : A) u.isUnit
  have he : (e.restrictScalars k).toAlgHom = IsScalarTower.toAlgHom k A T := by
    ext a
    simpa using e.commutes a
  rw [← he]
  exact (Cohomology.mapEquiv (e.restrictScalars k)).bijective

include u in
/-- The Laurent-twisted pullback at a unit equation is also bijective, by tensoring the
actual inverse on ordinary cohomology. No smoothness or characteristic hypothesis is needed.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_twistedCohomologyMap_bijective :
    Function.Bijective (TwistedCohomology.map (IsScalarTower.toAlgHom k A T)) :=
  TwistedCohomology.bijective_map (unit_cohomologyMap_bijective u T)

/-- Every form on the localization at a unit is logarithmic.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_logForms_eq_top : logForms k (u : A) T = ⊤ := by
  let e := IsLocalization.atUnit A T (u : A) u.isUnit
  have he : (e.restrictScalars k).toAlgHom = IsScalarTower.toAlgHom k A T := by
    ext a
    simpa using e.commutes a
  apply top_unique
  intro x _
  obtain ⟨ω, hω⟩ := (Forms.mapEquiv (e.restrictScalars k)).surjective x
  have hx : Forms.map (IsScalarTower.toAlgHom k A T) ω = x := by
    simpa only [Forms.mapEquiv_apply, he] using hω
  rw [← hx]
  simpa only [coe_ofRegular] using (ofRegular k (u : A) T ω).property

/-- Gysin is the zero map for a unit equation, since its source is zero.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_gysin_eq_zero (h : IsSmoothPrincipalPair (u : A) φ) : gysin T h = 0 := by
  have := unit_closed_subsingleton u h
  apply LinearMap.ext
  intro c
  rw [Subsingleton.elim c 0, map_zero, LinearMap.zero_apply]

/-- Residue is the zero map for a unit equation, since its target is zero.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_residue_eq_zero (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (h : IsSmoothPrincipalPair (u : A) φ) : residue T hUnits h = 0 := by
  have := unit_closed_subsingleton u h
  exact Subsingleton.elim _ _

/-- The Laurent-twisted Gysin map for a unit equation is zero as well.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_twistedGysin_eq_zero (h : IsSmoothPrincipalPair (u : A) φ) :
    TwistedCohomology.gysin T h = 0 := by
  simp [TwistedCohomology.gysin, TwistedCohomology.twistMap, unit_gysin_eq_zero u T h]

/-- The Laurent-twisted residue for a unit equation is zero as well.
Blueprint: `prop:dr-unit-example`. -/
theorem unit_twistedResidue_eq_zero (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (h : IsSmoothPrincipalPair (u : A) φ) : TwistedCohomology.residue T hUnits h = 0 := by
  simp [TwistedCohomology.residue, TwistedCohomology.twistMap, unit_residue_eq_zero u T hUnits h]

end Unit

section Zero

variable [Subsingleton A]

/-- Every form on the zero algebra vanishes, including forms of degree zero.
Blueprint: `prop:dr-zero-example`. -/
theorem zero_form_eq_zero (x : Forms k A) : x = 0 :=
  Subsingleton.elim _ _

/-- Every ordinary de Rham cohomology class of the zero algebra vanishes.
Blueprint: `prop:dr-zero-example`. -/
theorem zero_cohomology_eq_zero (x : Cohomology k A) : x = 0 :=
  Subsingleton.elim _ _

/-- Every Laurent-twisted cohomology class of the zero algebra vanishes.
Blueprint: `prop:dr-zero-example`. -/
theorem zero_twistedCohomology_eq_zero (x : TwistedCohomology k A) : x = 0 :=
  Subsingleton.elim _ _

end Zero

/-! ### A divisor on one connected component -/

section Product

variable (k : Type*) [CommRing k]

/-- The componentwise polynomial-to-Laurent algebra structure of the disconnected example. -/
instance productLaurentAlgebra : Algebra (k × k[X]) (k × k[T;T⁻¹]) :=
  (RingHom.prodMap (RingHom.id k) (Polynomial.toLaurent (R := k))).toAlgebra

/-- The componentwise localization respects the coefficient algebra. -/
instance productLaurentScalarTower : IsScalarTower k (k × k[X]) (k × k[T;T⁻¹]) :=
  .of_algebraMap_eq fun c => by ext <;> simp [RingHom.algebraMap_toAlgebra]

/-- Inverting `(1,X)` keeps the first component and inverts the second coordinate.
Blueprint: `prop:dr-product-example`. -/
instance productLaurentLocalization :
    IsLocalization.Away (Sanity.productPolynomialEquation k) (k × k[T;T⁻¹]) where
  map_units m := by
    rcases m with ⟨m, hm⟩
    obtain ⟨n, rfl⟩ := hm
    apply Prod.isUnit_iff.2
    constructor
    · simp [Sanity.productPolynomialEquation, RingHom.algebraMap_toAlgebra]
    · simpa [Sanity.productPolynomialEquation, RingHom.algebraMap_toAlgebra] using
        (LaurentPolynomial.isUnit_T (R := k) n)
  surj z := by
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow z.2
    refine ⟨((z.1, p), ⟨Sanity.productPolynomialEquation k ^ n, n, rfl⟩), ?_⟩
    apply Prod.ext
    · simp [Sanity.productPolynomialEquation, RingHom.algebraMap_toAlgebra]
    · simpa [Sanity.productPolynomialEquation, RingHom.algebraMap_toAlgebra] using hp.symm
  exists_of_eq {x y} h := by
    have hx : x = y := by
      apply Prod.ext
      · simpa [RingHom.algebraMap_toAlgebra] using congrArg Prod.fst h
      · exact Polynomial.toLaurent_injective (congrArg Prod.snd h)
    exact ⟨1, by rw [hx]⟩

/-- The actual localization of `k × k[X]` away from `(1,X)` is `k × k[X±1]`.
Blueprint: `prop:dr-product-example`. -/
def productLocalizationEquiv :
    Localization.Away (Sanity.productPolynomialEquation k) ≃ₐ[k] k × k[T;T⁻¹] :=
  (IsLocalization.algEquiv (Submonoid.powers (Sanity.productPolynomialEquation k))
    (Localization.Away (Sanity.productPolynomialEquation k)) (k × k[T;T⁻¹])).restrictScalars k

/-- The logarithmic class on the disconnected complement has residue one.
Blueprint: `prop:dr-product-example`. -/
theorem productPolynomial_residue_theta (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    residue (k × k[T;T⁻¹]) hUnits (productPolynomial_isSmoothPrincipalPair k)
      (Cohomology.mk (theta k (Sanity.productPolynomialEquation k) (k × k[T;T⁻¹]))
        (d_theta _ _ _)) = 1 := by
  exact residue_dlogClass hUnits (productPolynomial_isSmoothPrincipalPair k)
    (IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit
      (S := k × k[T;T⁻¹]) (Sanity.productPolynomialEquation k)))

section Idempotent

variable {k} {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

private theorem diff_idempotent (e : B) (he : e * e = e) : diff k e = 0 := by
  have hd := (diff k : Derivation k B (Forms k B)).leibniz e e
  rw [he] at hd
  have hs := congrArg (fun x : Forms k B => e • x) hd
  simp only [smul_add, smul_smul, he] at hs
  have he0 : e • diff k e = 0 := add_eq_left.1 hs.symm
  simpa only [he0, add_zero] using hd

private theorem idempotent_smul_mul (e : B) (he : e * e = e) (x y : Forms k B) :
    (e • x) * (e • y) = e • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, he]

private theorem support_map_eq (e : B) (he : e * e = e) (φ ψ : A →ₐ[k] B)
    (hφ : ∀ a, e * φ a = e * ψ a) (x : Forms k A) :
    e • Forms.map φ x = e • Forms.map ψ x := by
  have hdiff (a : A) : e • diff k (φ a) = e • diff k (ψ a) := by
    have h := congrArg (diff k : B → Forms k B) (hφ a)
    simpa only [Derivation.leibniz, diff_idempotent e he, smul_zero, add_zero] using h
  induction x using Forms.induction with
  | word a l =>
    induction l with
    | nil =>
      simp only [word_nil, Algebra.smul_def, mul_one, Forms.map_algebraMap]
      simpa only [← map_mul] using congrArg (algebraMap B (Forms k B)) (hφ a)
    | cons b l ih =>
      simp only [word_cons, ← mul_smul_comm a, map_mul]
      rw [← idempotent_smul_mul e he, ← idempotent_smul_mul e he,
        Forms.map_diff, Forms.map_diff, hdiff, ih]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end Idempotent

section Splitting

variable {k} {B : Type*} [CommRing B] [Algebra k B]

private def productSection (ε : B →ₐ[k] k) : B →ₐ[k] k × B :=
  ε.prod (AlgHom.id k B)

private theorem product_forms_decomposition (ε : B →ₐ[k] k) (x : Forms k (k × B)) :
    x = ((1 : k), (0 : B)) •
        Forms.map (Algebra.ofId k (k × B)) (Forms.map (AlgHom.fst k k B) x) +
      ((0 : k), (1 : B)) • Forms.map (productSection ε) (Forms.map (AlgHom.snd k k B) x) := by
  have h₁ := support_map_eq ((1 : k), (0 : B)) (by simp)
    ((Algebra.ofId k (k × B)).comp (AlgHom.fst k k B)) (AlgHom.id k (k × B))
    (fun a => by ext <;> simp) x
  have h₂ := support_map_eq ((0 : k), (1 : B)) (by simp)
    ((productSection ε).comp (AlgHom.snd k k B)) (AlgHom.id k (k × B))
    (fun a => by ext <;> simp [productSection]) x
  rw [Forms.map_comp, Forms.map_id, AlgHom.comp_apply] at h₁ h₂
  rw [h₁, h₂, ← add_smul]
  rw [show ((1 : k), (0 : B)) + ((0 : k), (1 : B)) = (1 : k × B) by ext <;> simp,
    one_smul, AlgHom.id_apply]

private def productCohomologyMap :
    Cohomology k (k × B) →ₐ[k] Cohomology k k × Cohomology k B :=
  (Cohomology.map (AlgHom.fst k k B)).prod (Cohomology.map (AlgHom.snd k k B))

private theorem productCohomologyMap_bijective (ε : B →ₐ[k] k) :
    Function.Bijective (productCohomologyMap (k := k) (B := B)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro c hc
    induction c using Cohomology.induction with
    | mk x hx =>
      have h₁ : Cohomology.map (AlgHom.fst k k B) (Cohomology.mk x hx) = 0 :=
        congrArg Prod.fst hc
      have h₂ : Cohomology.map (AlgHom.snd k k B) (Cohomology.mk x hx) = 0 :=
        congrArg Prod.snd hc
      rw [Cohomology.map_mk, Cohomology.mk_eq_zero_iff] at h₁ h₂
      obtain ⟨y₁, hy₁⟩ := h₁
      obtain ⟨y₂, hy₂⟩ := h₂
      apply Cohomology.mk_eq_zero_iff.2
      refine ⟨((1 : k), (0 : B)) • Forms.map (Algebra.ofId k (k × B)) y₁ +
        ((0 : k), (1 : B)) • Forms.map (productSection ε) y₂, ?_⟩
      simp only [map_add, d_smul, diff_idempotent _ (show ((1 : k), (0 : B)) * (1, 0) =
        (1, 0) by simp), diff_idempotent _ (show ((0 : k), (1 : B)) * (0, 1) =
        (0, 1) by simp), zero_mul, zero_add, ← Forms.map_d, hy₁, hy₂]
      exact (product_forms_decomposition ε x).symm
  · rintro ⟨c₁, c₂⟩
    obtain ⟨x₁, hx₁, rfl⟩ := Cohomology.exists_mk_eq c₁
    obtain ⟨x₂, hx₂, rfl⟩ := Cohomology.exists_mk_eq c₂
    let x := ((1 : k), (0 : B)) • Forms.map (Algebra.ofId k (k × B)) x₁ +
      ((0 : k), (1 : B)) • Forms.map (productSection ε) x₂
    have hx : d k x = 0 := by
      simp only [x, map_add, d_smul, diff_idempotent _ (show ((1 : k), (0 : B)) * (1, 0) =
        (1, 0) by simp), diff_idempotent _ (show ((0 : k), (1 : B)) * (0, 1) =
        (0, 1) by simp), zero_mul, ← Forms.map_d, hx₁, hx₂,
        map_zero, smul_zero, add_zero]
    refine ⟨Cohomology.mk x hx, ?_⟩
    apply Prod.ext
    · change Cohomology.map (AlgHom.fst k k B) (Cohomology.mk x hx) = _
      rw [Cohomology.map_mk]
      apply Cohomology.mk_congr
      simp [x, Forms.map_smul, Forms.map_map, productSection]
    · change Cohomology.map (AlgHom.snd k k B) (Cohomology.mk x hx) = _
      rw [Cohomology.map_mk]
      apply Cohomology.mk_congr
      simp [x, Forms.map_smul, Forms.map_map, productSection]

/-- Cohomology of a product with an augmented algebra splits into the cohomology of its two
components. The two closed idempotents give the inverse, over every commutative base ring. -/
@[no_expose] def productCohomologyEquivOfAugmentation (ε : B →ₐ[k] k) :
    Cohomology k (k × B) ≃ₐ[k] Cohomology k k × Cohomology k B :=
  AlgEquiv.ofBijective productCohomologyMap (productCohomologyMap_bijective ε)

private def productFirstClass : Cohomology k (k × B) :=
  Cohomology.mk (algebraMap (k × B) (Forms k (k × B)) (1, 0))
    (by rw [d_algebraMap]; exact diff_idempotent _ (by simp))

private def productSecondClass : Cohomology k (k × B) :=
  Cohomology.mk (algebraMap (k × B) (Forms k (k × B)) (0, 1))
    (by rw [d_algebraMap]; exact diff_idempotent _ (by simp))

private theorem productCohomologyEquivOfAugmentation_symm (ε : B →ₐ[k] k)
    (c₁ : Cohomology k k) (c₂ : Cohomology k B) :
    (productCohomologyEquivOfAugmentation ε).symm (c₁, c₂) =
      productFirstClass * Cohomology.map (Algebra.ofId k (k × B)) c₁ +
        productSecondClass * Cohomology.map (productSection ε) c₂ := by
  apply (productCohomologyEquivOfAugmentation ε).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Prod.ext
  · change c₁ = Cohomology.map (AlgHom.fst k k B) _
    simp [productFirstClass, productSecondClass, Cohomology.map_map]
  · change c₂ = Cohomology.map (AlgHom.snd k k B) _
    simp [productFirstClass, productSecondClass, Cohomology.map_map, productSection]

/-- The product splitting preserves and reflects every cohomological degree on both components. -/
theorem productCohomologyEquivOfAugmentation_mem_degree (ε : B →ₐ[k] k) (n : ℕ)
    (c : Cohomology k (k × B)) :
    c ∈ Cohomology.degree k (k × B) n ↔
      (productCohomologyEquivOfAugmentation ε c).1 ∈ Cohomology.degree k k n ∧
        (productCohomologyEquivOfAugmentation ε c).2 ∈ Cohomology.degree k B n := by
  constructor
  · intro hc
    exact ⟨Cohomology.map_mem_degree _ hc, Cohomology.map_mem_degree _ hc⟩
  · rintro ⟨hc₁, hc₂⟩
    have hc : c = (productCohomologyEquivOfAugmentation ε).symm
        ((productCohomologyEquivOfAugmentation ε c).1,
          (productCohomologyEquivOfAugmentation ε c).2) := by simp
    rw [hc, productCohomologyEquivOfAugmentation_symm]
    apply add_mem
    · have he : (productFirstClass : Cohomology k (k × B)) ∈ Cohomology.degree k (k × B) 0 :=
        Cohomology.mk_mem_degree (algebraMap_mem_exteriorPower_zero k _) _
      simpa only [zero_add] using SetLike.mul_mem_graded he
        (Cohomology.map_mem_degree (Algebra.ofId k (k × B)) hc₁)
    · have he : (productSecondClass : Cohomology k (k × B)) ∈ Cohomology.degree k (k × B) 0 :=
        Cohomology.mk_mem_degree (algebraMap_mem_exteriorPower_zero k _) _
      simpa only [zero_add] using SetLike.mul_mem_graded he
        (Cohomology.map_mem_degree (productSection ε) hc₂)

end Splitting

/-- De Rham cohomology of the disconnected complement splits by its two idempotents.
This uses neither a characteristic hypothesis nor a Künneth theorem.
Blueprint: `prop:dr-product-example`. -/
@[no_expose] def productLaurentCohomologyEquiv :
    Cohomology k (k × k[T;T⁻¹]) ≃ₐ[k] k × Cohomology k k[T;T⁻¹] :=
  (productCohomologyEquivOfAugmentation (OrlikSolomon.laurentEvalOne k)).trans
    (AlgEquiv.prodCongr (Cohomology.equivOfSurjective Function.surjective_id) AlgEquiv.refl)

/-- The first component is restriction to the point. -/
@[simp]
theorem productLaurentCohomologyEquiv_fst (c : Cohomology k (k × k[T;T⁻¹])) :
    (productLaurentCohomologyEquiv k c).1 =
      Cohomology.toDegreeZero k k (Cohomology.map (AlgHom.fst k k k[T;T⁻¹]) c) := by
  rfl

/-- The second component is restriction to the punctured affine line. -/
@[simp]
theorem productLaurentCohomologyEquiv_snd (c : Cohomology k (k × k[T;T⁻¹])) :
    (productLaurentCohomologyEquiv k c).2 = Cohomology.map (AlgHom.snd k k k[T;T⁻¹]) c := by
  rfl

private def productCoordinateUnit : (k × k[T;T⁻¹])ˣ where
  val := (1, LaurentPolynomial.T 1)
  inv := (1, LaurentPolynomial.T (-1))
  val_inv := by
    apply Prod.ext
    · exact one_mul _
    · change LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) = (1 : k[T;T⁻¹])
      rw [← LaurentPolynomial.T_add]
      norm_num
  inv_val := by
    apply Prod.ext
    · exact one_mul _
    · change LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T 1 = (1 : k[T;T⁻¹])
      rw [← LaurentPolynomial.T_add]
      norm_num

/-- The logarithmic class is zero on the first component and `dX/X` on the second.
Blueprint: `prop:dr-product-example`. -/
theorem productLaurentCohomologyEquiv_theta :
    productLaurentCohomologyEquiv k
      (Cohomology.mk (theta k (Sanity.productPolynomialEquation k) (k × k[T;T⁻¹]))
        (d_theta _ _ _)) =
      (0, Cohomology.mk (theta k (X : k[X]) k[T;T⁻¹]) (d_theta _ _ _)) := by
  have hθ : Cohomology.mk
      (theta k (Sanity.productPolynomialEquation k) (k × k[T;T⁻¹])) (d_theta _ _ _) =
      dlogClass k (productCoordinateUnit k) :=
    (Cohomology.mk_congr (theta_eq_dlog k _ _ (u := productCoordinateUnit k) (by
      ext <;> simp [productCoordinateUnit, Sanity.productPolynomialEquation,
        RingHom.algebraMap_toAlgebra])) _).trans (mk_dlog _ _)
  rw [hθ]
  apply Prod.ext
  · rw [productLaurentCohomologyEquiv_fst, map_dlogClass]
    have hfst : Units.map (AlgHom.fst k k k[T;T⁻¹] : (k × k[T;T⁻¹]) →* k)
        (productCoordinateUnit k) = 1 := by
      ext
      rfl
    rw [hfst, dlogClass_one, map_zero]
  · rw [productLaurentCohomologyEquiv_snd, map_dlogClass]
    change dlogClass k (Units.map (AlgHom.snd k k k[T;T⁻¹]) (productCoordinateUnit k)) =
      dlogClass k (IsLocalization.Away.algebraMap_isUnit (S := k[T;T⁻¹]) (X : k[X])).unit
    apply congrArg (dlogClass k)
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [productCoordinateUnit, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X]

private theorem point_mem_degree_iff (n : ℕ) (c : Cohomology k k) :
    c ∈ Cohomology.degree k k n ↔ n = 0 ∨ c = 0 := by
  constructor
  · intro hc
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (Cohomology.eq_zero_of_mem_degree_point hn hc)
  · rintro (rfl | rfl)
    · induction c using Cohomology.induction with
      | mk x hx =>
        apply Cohomology.mk_mem_degree _ hx
        rw [← Cohomology.algebraMap_algebraMapInv_of_surjective Function.surjective_id x]
        exact algebraMap_mem_exteriorPower_zero _ _
    · exact zero_mem _

/-- The product equivalence respects every cohomological degree, with the point in degree zero.
Blueprint: `prop:dr-product-example`. -/
theorem productLaurentCohomologyEquiv_mem_degree (n : ℕ)
    (c : Cohomology k (k × k[T;T⁻¹])) :
    c ∈ Cohomology.degree k (k × k[T;T⁻¹]) n ↔
      (n = 0 ∨ (productLaurentCohomologyEquiv k c).1 = 0) ∧
        (productLaurentCohomologyEquiv k c).2 ∈ Cohomology.degree k k[T;T⁻¹] n := by
  rw [productCohomologyEquivOfAugmentation_mem_degree (OrlikSolomon.laurentEvalOne k),
    point_mem_degree_iff]
  change (_ ∨ Cohomology.map (AlgHom.fst k k k[T;T⁻¹]) c = 0) ∧ _ ↔
    (_ ∨ Cohomology.toDegreeZero k k (Cohomology.map (AlgHom.fst k k k[T;T⁻¹]) c) = 0) ∧ _
  rw [map_eq_zero_iff _ (Cohomology.bijective_toDegreeZero_of_surjective
    Function.surjective_id).1]
  rfl

end Product

section ProductNumbers

variable (k : Type*) [Field k] [CharZero k]

/-- The disconnected complement has two constant classes and one logarithmic class.
Blueprint: `prop:dr-product-example`. -/
@[no_expose] def productCohomologyEquiv :
    (k × (k × k)) ≃ₗ[k] Cohomology k (k × k[T;T⁻¹]) :=
  (LinearEquiv.prodCongr (LinearEquiv.refl k k) (gmCohomologyEquiv k)).trans
    (productLaurentCohomologyEquiv k).toLinearEquiv.symm

/-- The two constant coefficients have degree zero and the logarithmic coefficient degree one.
Blueprint: `prop:dr-product-example`. -/
theorem productCohomologyEquiv_mem_degree_iff (n : ℕ) (a b c : k) :
    productCohomologyEquiv k (a, (b, c)) ∈ Cohomology.degree k (k × k[T;T⁻¹]) n ↔
      (n = 0 ∨ a = 0) ∧ (n = 0 ∨ b = 0) ∧ (n = 1 ∨ c = 0) := by
  change (productLaurentCohomologyEquiv k).symm (a, gmCohomologyEquiv k (b, c)) ∈ _ ↔ _
  rw [productLaurentCohomologyEquiv_mem_degree, AlgEquiv.apply_symm_apply]
  change (n = 0 ∨ a = 0) ∧
    gmCohomologyEquiv k (b, c) ∈ Cohomology.degree k (SmoothAlg.gm k) n ↔ _
  rw [← Cohomology.grading_natCast, gmCohomologyEquiv_mem_grading_iff]
  simp

/-- The disconnected complement has no cohomology above degree one.
Blueprint: `prop:dr-product-example`. -/
theorem product_eq_zero_of_mem_degree_succ_succ (n : ℕ)
    {z : Cohomology k (k × k[T;T⁻¹])} (hz : z ∈ Cohomology.degree k (k × k[T;T⁻¹]) (n + 2)) :
    z = 0 := by
  obtain ⟨⟨a, b, c⟩, rfl⟩ := (productCohomologyEquiv k).surjective z
  obtain ⟨ha, hb, hc⟩ := (productCohomologyEquiv_mem_degree_iff k (n + 2) a b c).1 hz
  have ha : a = 0 := ha.resolve_left (by omega)
  have hb : b = 0 := hb.resolve_left (by omega)
  have hc : c = 0 := hc.resolve_left (by omega)
  rw [ha, hb, hc]
  exact (productCohomologyEquiv k).map_zero

/-- The third coefficient is the actual logarithmic class on the disconnected complement.
Blueprint: `prop:dr-product-example`. -/
theorem productCohomologyEquiv_generator :
    productCohomologyEquiv k (0, (0, 1)) =
      Cohomology.mk (theta k (Sanity.productPolynomialEquation k) (k × k[T;T⁻¹]))
        (d_theta _ _ _) := by
  apply (productLaurentCohomologyEquiv k).injective
  rw [productLaurentCohomologyEquiv_theta]
  change productLaurentCohomologyEquiv k
    ((productLaurentCohomologyEquiv k).symm (0, gmCohomologyEquiv k (0, 1))) = _
  rw [AlgEquiv.apply_symm_apply]
  rw [gmCohomologyEquiv_apply, map_zero, map_one, mul_one, zero_add]
  congr 1
  let u := (IsLocalization.Away.algebraMap_isUnit (S := k[T;T⁻¹]) (X : k[X])).unit
  have hu : (SmoothAlg.laurentT (SmoothAlg.point k) : k[T;T⁻¹]ˣ) = u := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
    rfl
  exact (congrArg (dlogClass k) hu).trans (mk_dlog u (d_theta _ _ _)).symm

/-- Residue takes the normalized degree-one generator of the disconnected complement to one.
Blueprint: `prop:dr-product-example`. -/
theorem product_residue_generator :
    residue (k × k[T;T⁻¹]) (isUnit_natCast_add_one k) (productPolynomial_isSmoothPrincipalPair k)
      (productCohomologyEquiv k (0, (0, 1))) = 1 := by
  rw [productCohomologyEquiv_generator]
  exact productPolynomial_residue_theta _ _

end ProductNumbers

end OrlikSolomon.DeRham.Examples
