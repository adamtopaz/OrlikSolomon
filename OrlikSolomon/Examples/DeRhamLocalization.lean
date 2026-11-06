/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.DeRham.Localization
public import OrlikSolomon.DeRham.PrincipalQuotient

/-!
# Regressions for forms on a localization and on a principal quotient

These check what is easy to get wrong about `DeRham/Localization` and `DeRham/PrincipalQuotient`:
neither localization nor the conormal map is injective in general, and nothing needs `f` to be a
non-zero-divisor, a non-unit or nonzero, or the rings to be nonzero.

## Main results

* `OrlikSolomon.DeRham.Examples.map_eq_zero_of_isNilpotent`: inverting a nilpotent element kills all
  forms. `OrlikSolomon.DeRham.Examples.map_one_eq_zero_of_away_zero` is the case `f = 0`.
* `OrlikSolomon.DeRham.Examples.differentialIdealPower_unit`: for a unit `f`, the denominator of
  `lem:dr-quotient` is everything, so `S` has no forms.
* `OrlikSolomon.DeRham.Examples.differentialIdealPower_zero_element`: for `f = 0`, the denominator
  vanishes, so that forms on `S = A` are forms on `A`.
* `OrlikSolomon.DeRham.Examples.principalConormalMap_not_injective`: over `ZMod 2`, for `f = X²`,
  the conormal map sends the nonzero class of `f` to `df = 0`. This is why `lem:dr-quotient` claims
  no injectivity on the left.
-/

@[expose] public section

open scoped TensorProduct

namespace OrlikSolomon.DeRham.Examples

open KaehlerDifferential (D)
open IsLocalization.Away (invSelf)
open Polynomial (X)

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]

section Localization

variable {T : Type*} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]

/-- Inverting a nilpotent element kills all forms, so the map to the localization is far from
injective. -/
theorem map_eq_zero_of_isNilpotent {f : A} [IsLocalization.Away f T] (hf : IsNilpotent f)
    (x : Forms k A) : Forms.map (IsScalarTower.toAlgHom k A T) x = 0 := by
  obtain ⟨m, hm⟩ := hf
  exact (Forms.map_eq_zero_iff_of_isLocalizationAway f).2 ⟨m, by rw [hm, zero_smul]⟩

/-- For `f = 0`, the localization map on forms sends even the unit to zero, whatever `A` is. -/
theorem map_one_eq_zero_of_away_zero [IsLocalization.Away (0 : A) T] :
    Forms.map (IsScalarTower.toAlgHom k A T) (1 : Forms k A) = 0 :=
  map_eq_zero_of_isNilpotent (f := 0) IsNilpotent.zero 1

/-- The formula for the differential also holds for `f = 0` and for nilpotent `f`, where everything
is zero. There is no hypothesis on `f` in `d_invSelf_pow_smul`. -/
example (f : A) [IsLocalization.Away f T] (m : ℕ) (ω : Forms k T) :
    d k ((invSelf f : T) ^ m • ω) =
      (invSelf f : T) ^ m • d k ω -
        ((m : T) * (invSelf f : T) ^ (m + 1)) • (diff k (algebraMap A T f) * ω) :=
  d_invSelf_pow_smul k f m ω

/-- A localization of the zero ring has no forms. -/
example [Subsingleton A] (M : Submonoid A) [IsLocalization M T] : Subsingleton (Forms k T) :=
  have : Subsingleton T := (algebraMap A T).codomain_trivial
  inferInstance

end Localization

section Unit

/-- `A` is its own localization away from a unit. So the formula for the differential is an
identity about forms on `A`, in which `dlog k u` is a regular form. -/
example (u : Aˣ) (m : ℕ) (ω : Forms k A) :
    d k ((↑u⁻¹ : A) ^ m • ω) = (↑u⁻¹ : A) ^ m • (d k ω - (m : A) • (dlog k u * ω)) :=
  d_val_inv_pow_smul k u m ω

/-- For a unit `f`, the denominator of `lem:dr-quotient` is everything. So forms on `S`, which is
the zero ring, vanish, in every degree. -/
theorem differentialIdealPower_unit (u : Aˣ) (n : ℕ) :
    differentialIdealPower k (Ideal.span {(u : A)}) n = ⊤ := by
  rw [Ideal.span_singleton_eq_top.2 u.isUnit, differentialIdealPower, Submodule.top_smul,
    top_sup_eq]

end Unit

section Zero

/-- For `f = 0`, the denominator of `lem:dr-quotient` vanishes in every degree. So the quotient is
all of `Ω_A^n`, as it must be for `S = A`. -/
theorem differentialIdealPower_zero_element (n : ℕ) :
    differentialIdealPower k (Ideal.span {(0 : A)}) n = ⊥ := by
  cases n with
  | zero =>
    rw [differentialIdealPower_span_singleton_zero, Ideal.span_singleton_zero, Submodule.bot_smul]
  | succ n =>
    rw [differentialIdealPower_span_singleton_succ, Ideal.span_singleton_zero, Submodule.bot_smul,
      map_zero, wedgeLeft_zero, LinearMap.range_zero, sup_bot_eq]

end Zero

section Conormal

open scoped Polynomial

local notation "P" => (ZMod 2)[X]

/-- The equation `f = X²` is zero in the quotient by it. -/
theorem algebraMap_X_sq : algebraMap P (P ⧸ Ideal.span {(X ^ 2 : P)}) (X ^ 2) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- Over `ZMod 2`, the conormal map of `f = X²` is not injective, because `df = 2X dX = 0` and `f`
is not in `(f²)`. So the right exact sequence of `lem:dr-quotient` cannot be extended by a zero on
the left without a hypothesis such as the smoothness of `lem:dr-conormal`. Here `S` is
`(ZMod 2)[X]/(X²)`, which is not smooth over `ZMod 2`. -/
theorem principalConormalMap_not_injective :
    ¬ Function.Injective
      (principalConormalMap (ZMod 2) (P ⧸ Ideal.span {(X ^ 2 : P)}) algebraMap_X_sq) := by
  intro h
  have hzero : principalConormalMap (ZMod 2) (P ⧸ Ideal.span {(X ^ 2 : P)}) algebraMap_X_sq
      ((Ideal.span {(X ^ 2 : P)}).toCotangent
        ⟨X ^ 2, Ideal.mem_span_singleton_self _⟩) = 0 := by
    rw [principalConormalMap_self, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2,
      show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul, TensorProduct.tmul_zero]
  have hne := (injective_iff_map_eq_zero _).1 h _ hzero
  rw [Ideal.toCotangent_eq_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← pow_mul, Polynomial.X_pow_dvd_iff] at hne
  simpa using hne 2 (by norm_num)

end Conormal

end OrlikSolomon.DeRham.Examples
