/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Instance.Basic
public import OrlikSolomon.Examples.DeRhamMaps

/-!
# Worked de Rham calculations

For a unit equation the closed algebra is zero, the localization is the original algebra,
all localized forms are logarithmic, and the residue and Gysin maps vanish. For the actual
zero algebra, forms, ordinary cohomology and Laurent-twisted cohomology vanish in every degree.
These assertions use the existing maps and their actual algebra structures.

## Main results

* `unit_closed_subsingleton`: the closed algebra of a unit equation is zero.
* `unit_logForms_eq_top` and `unit_cohomologyMap_bijective`: a unit changes neither forms nor
  cohomology on localization; no hypothesis on characteristic is needed.
* `unit_residue_eq_zero` and `unit_gysin_eq_zero`: the two maps for the empty divisor are zero.
* `zero_form_eq_zero`, `zero_cohomology_eq_zero` and `zero_twistedCohomology_eq_zero`: actual
  vanishings, including degree zero.

Blueprint: `prop:dr-unit-example`, `prop:dr-zero-example`.
-/

@[expose] public section

noncomputable section

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

end OrlikSolomon.DeRham.Examples
