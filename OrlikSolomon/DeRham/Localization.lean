/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Away.Basic
public import OrlikSolomon.DeRham.Complex

/-!
# Forms on a localization

Let `T` be a localization of a commutative `k`-algebra `A`, in the sense of `IsLocalization`, so
that this file applies to certified pairs and not only to Mathlib's `Localization`. Then forms on
`T` are the localization of forms on `A`, in each degree, and the differential of a form with a
denominator is given by the quotient rule. Nothing here needs smoothness or injectivity of `A → T`.
The element `f` may be a unit, zero or nilpotent, and `A` may be the zero ring.

## Main definitions

* `OrlikSolomon.DeRham.dlog k u`: the form `du / u` of a unit `u`.
* `OrlikSolomon.DeRham.powerLocalizationEquiv T M n`: the identification `(Ω_A^n)_M ≃ Ω_T^n`.
* `OrlikSolomon.DeRham.extendDerivation T M δ`: the extension to `T` of a derivation on `A` with
  values in a `T`-module.

## Main results

Blueprint `lem:dr-localization`:

* `OrlikSolomon.DeRham.isLocalizedModule_powerMap_kaehlerMap` and
  `OrlikSolomon.DeRham.isBaseChange_powerMap_kaehlerMap`: `Ω_A^n → Ω_T^n` is a localization of
  modules, and a base change. This is the identification, in its characteristic form.
* `OrlikSolomon.DeRham.powerLocalizationEquiv_mk` and
  `OrlikSolomon.DeRham.powerLocalizationEquiv_mk_pow`: the identification sends `x / c` to
  `c⁻¹ x` and `x / f^m` to `f^{-m} x`.
* `OrlikSolomon.DeRham.mapPower_powerLocalizationEquiv`: the identification is natural.
* `OrlikSolomon.DeRham.d_invSelf_pow_smul` and `OrlikSolomon.DeRham.d_invSelf_pow_smul_map`: the
  formula `d(f^{-m} ω) = f^{-m} dω - m f^{-m-1} df ∧ ω`, for `ω` a form on `T` and on `A`.
* `OrlikSolomon.DeRham.d_invSelf_smul_diff` and `OrlikSolomon.DeRham.d_dlog`: `d(df / f) = 0`.

For the consumers of these results:

* `OrlikSolomon.DeRham.Forms.map_eq_zero_iff_of_isLocalizationAway` and
  `OrlikSolomon.DeRham.Forms.mapPower_eq_zero_iff_of_isLocalizationAway`: a form maps to zero
  exactly when a power of `f` kills it.
* `OrlikSolomon.DeRham.Forms.exists_eq_invSelf_pow_smul_map` and
  `OrlikSolomon.DeRham.Forms.exists_eq_invSelf_pow_smul_map_of_mem`: every form on `T` is
  `f^{-m} ω` with `ω` a form on `A`, of the same degree.
* `OrlikSolomon.DeRham.dlog_mul`, `OrlikSolomon.DeRham.Forms.map_dlog`,
  `OrlikSolomon.DeRham.d_val_inv_pow_smul` and `OrlikSolomon.DeRham.d_val_smul`: `dlog` is additive
  and natural, and it gives `d(f^{-m} ξ) = f^{-m} (dξ - m θ ∧ ξ)` and `d(f ξ) = f (θ ∧ ξ + dξ)`.
* `OrlikSolomon.DeRham.extendDerivation_invSelf_pow_mul`: the quotient rule for a derivation.

## Design

The formula for `d` holds for any pair `u * g = 1` in any algebra, in `d_pow_smul_of_mul_eq_one`,
and its forms for `IsLocalization.Away` are its special case `u = invSelf f`,
`g = algebraMap A T f`. For a divisor pair, `dlog k P.eqnUnit` is the form `θ = df / f`.
-/

@[expose] public section

open scoped TensorProduct

namespace OrlikSolomon.DeRham

open KaehlerDifferential (D)
open IsLocalization.Away (invSelf)

variable {k : Type*} [CommRing k]

/-! ### Inverses and the differential -/

section Units

variable {T : Type*} [CommRing T] [Algebra k T]

/-- The quotient rule `D(u^m) = -m u^(m+1) Dg` for `u = g⁻¹`, for any derivation `D`. -/
theorem leibniz_pow_of_mul_eq_one {N : Type*} [AddCommGroup N] [Module T N] [Module k N]
    (D : Derivation k T N) {u g : T} (h : u * g = 1) (m : ℕ) :
    D (u ^ m) = -(((m : T) * u ^ (m + 1)) • D g) := by
  rw [Derivation.leibniz_pow, D.leibniz_of_mul_eq_one h, neg_smul]
  cases m with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul T, smul_neg, smul_neg, smul_smul, smul_smul,
      mul_assoc, ← pow_add]

variable (k) in
/-- The quotient rule `d(u) = -u² dg` for `u = g⁻¹`. -/
theorem diff_of_mul_eq_one {u g : T} (h : u * g = 1) : diff k u = -(u ^ 2 • diff k g) := by
  rw [(diff k).leibniz_of_mul_eq_one h, neg_smul]

variable (k) in
/-- The quotient rule `d(u^m) = -m u^(m+1) dg` for `u = g⁻¹`. -/
theorem diff_pow_of_mul_eq_one {u g : T} (h : u * g = 1) (m : ℕ) :
    diff k (u ^ m) = -(((m : T) * u ^ (m + 1)) • diff k g) :=
  leibniz_pow_of_mul_eq_one (diff k) h m

variable (k) in
/-- The formula `d(u^m ω) = u^m dω - m u^(m+1) dg ∧ ω` for `u = g⁻¹`, on all forms and in any
algebra. This is the formula of `lem:dr-localization`, and `d_invSelf_pow_smul` is its form for a
localization.

Blueprint: `lem:dr-localization`. -/
theorem d_pow_smul_of_mul_eq_one {u g : T} (h : u * g = 1) (m : ℕ) (ω : Forms k T) :
    d k (u ^ m • ω) = u ^ m • d k ω - ((m : T) * u ^ (m + 1)) • (diff k g * ω) := by
  rw [d_smul, diff_pow_of_mul_eq_one k h, neg_mul, smul_mul_assoc, neg_add_eq_sub]

variable (k) in
/-- The form `du / u` of a unit `u`, written `u⁻¹ • du`. For a divisor pair, `dlog k P.eqnUnit` is
the form `θ = df / f`. By `dlog_mul`, the unit changes of `thm:dr-log-naturality` are additive in
`dlog`.

Blueprint: `lem:dr-localization`. -/
noncomputable def dlog (u : Tˣ) : Forms k T :=
  (↑u⁻¹ : T) • diff k (u : T)

variable (k)

theorem dlog_apply (u : Tˣ) : dlog k u = (↑u⁻¹ : T) • diff k (u : T) :=
  rfl

/-- `dlog` in terms of any inverse. -/
theorem dlog_eq_smul {u : Tˣ} {v : T} (h : v * u = 1) : dlog k u = v • diff k (u : T) := by
  rw [dlog_apply, Units.inv_eq_of_mul_eq_one_left h]

@[simp]
theorem dlog_one : dlog k (1 : Tˣ) = 0 := by
  simp [dlog_apply]

/-- `d(uv) / (uv) = du / u + dv / v`. -/
@[simp]
theorem dlog_mul (u v : Tˣ) : dlog k (u * v) = dlog k u + dlog k v := by
  rw [dlog_apply, dlog_apply, dlog_apply, mul_inv_rev, Units.val_mul, Units.val_mul,
    Derivation.leibniz, smul_add, smul_smul, smul_smul, mul_assoc, Units.inv_mul, mul_one,
    mul_right_comm, Units.inv_mul, one_mul, add_comm]

@[simp]
theorem dlog_inv (u : Tˣ) : dlog k u⁻¹ = -dlog k u := by
  rw [eq_neg_iff_add_eq_zero, ← dlog_mul, inv_mul_cancel, dlog_one]

/-- `u • (du / u) = du`. -/
@[simp]
theorem val_smul_dlog (u : Tˣ) : (u : T) • dlog k u = diff k (u : T) := by
  simp [dlog_apply, smul_smul]

theorem dlog_mem_exteriorPower_one (u : Tˣ) : dlog k u ∈ ⋀[T]^1 Ω[T⁄k] :=
  Submodule.smul_mem _ _ (diff_mem_exteriorPower_one k _)

@[simp]
theorem dlog_mul_self (u : Tˣ) : dlog k u * dlog k u = 0 :=
  mul_self_eq_zero_of_mem_exteriorPower_one (dlog_mem_exteriorPower_one k u)

/-- `d(du / u) = 0`.

Blueprint: `lem:dr-localization`. -/
@[simp]
theorem d_dlog (u : Tˣ) : d k (dlog k u) = 0 := by
  rw [dlog_apply, d_smul_diff, diff_of_mul_eq_one k u.inv_mul, neg_mul, smul_mul_assoc,
    diff_mul_self, smul_zero, neg_zero]

/-- `d(du / u ∧ x) = -du / u ∧ dx`. -/
@[simp]
theorem d_dlog_mul (u : Tˣ) (x : Forms k T) : d k (dlog k u * x) = -(dlog k u * d k x) := by
  rw [d_mul_of_mem_exteriorPower k (dlog_mem_exteriorPower_one k u), d_dlog]
  simp

/-- The formula `d(u ξ) = u (θ ∧ ξ + dξ)` for `θ = du / u`, which is what makes `f L^•` a subcomplex
in `lem:dr-log-dga`. -/
theorem d_val_smul (u : Tˣ) (ξ : Forms k T) :
    d k ((u : T) • ξ) = (u : T) • (dlog k u * ξ + d k ξ) := by
  rw [d_smul, smul_add, ← smul_mul_assoc, val_smul_dlog]

/-- The formula `d(u^{-m} ξ) = u^{-m} (dξ - m θ ∧ ξ)` for `θ = du / u`, which is what makes the pole
filtration `def:dr-pole-filtration` a filtration by subcomplexes.

Blueprint: `lem:dr-localization`. -/
theorem d_val_inv_pow_smul (u : Tˣ) (m : ℕ) (ξ : Forms k T) :
    d k ((↑u⁻¹ : T) ^ m • ξ) = (↑u⁻¹ : T) ^ m • (d k ξ - (m : T) • (dlog k u * ξ)) := by
  rw [d_pow_smul_of_mul_eq_one k u.inv_mul, smul_sub, dlog_apply, smul_mul_assoc, smul_smul,
    smul_smul]
  congr 2
  ring

variable {k}

/-- `dlog` is natural. -/
@[simp]
theorem Forms.map_dlog {T' : Type*} [CommRing T'] [Algebra k T'] (φ : T →ₐ[k] T') (u : Tˣ) :
    Forms.map φ (dlog k u) = dlog k (Units.map (φ : T →* T') u) := by
  simp [dlog_apply]

end Units

/-! ### Localizations away from an element -/

section Away

variable {A : Type*} [CommRing A] {T : Type*} [CommRing T] [Algebra A T]

variable (f : A) [IsLocalization.Away f T]

/-- `f⁻¹ f = 1`, in the order of the formulas of this file. -/
theorem invSelf_mul_self : (invSelf f : T) * algebraMap A T f = 1 := by
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

variable [Algebra k T] (k)

/-- The formula `d(f^{-m} ω) = f^{-m} dω - m f^{-m-1} df ∧ ω`, for a form `ω` on the localization.
There is no hypothesis on `f`, and in particular `A → T` need not be injective.

Blueprint: `lem:dr-localization`. -/
theorem d_invSelf_pow_smul (m : ℕ) (ω : Forms k T) :
    d k ((invSelf f : T) ^ m • ω) =
      (invSelf f : T) ^ m • d k ω -
        ((m : T) * (invSelf f : T) ^ (m + 1)) • (diff k (algebraMap A T f) * ω) :=
  d_pow_smul_of_mul_eq_one k (invSelf_mul_self f) m ω

/-- The formula `d(f^{-m} ω) = f^{-m} dω - m f^{-m-1} df ∧ ω`, for the image of a form `ω` on `A`.

Blueprint: `lem:dr-localization`. -/
theorem d_invSelf_pow_smul_map [Algebra k A] [IsScalarTower k A T] (m : ℕ) (ω : Forms k A) :
    d k ((invSelf f : T) ^ m • Forms.map (IsScalarTower.toAlgHom k A T) ω) =
      (invSelf f : T) ^ m • Forms.map (IsScalarTower.toAlgHom k A T) (d k ω) -
        ((m : T) * (invSelf f : T) ^ (m + 1)) •
          Forms.map (IsScalarTower.toAlgHom k A T) (diff k f * ω) := by
  rw [d_invSelf_pow_smul, map_mul, Forms.map_d, Forms.map_diff, IsScalarTower.coe_toAlgHom']

/-- The form `df / f` is closed.

Blueprint: `lem:dr-localization`. -/
@[simp]
theorem d_invSelf_smul_diff : d k ((invSelf f : T) • diff k (algebraMap A T f)) = 0 := by
  have h := d_dlog k (IsLocalization.Away.algebraMap_isUnit (S := T) f).unit
  rwa [dlog_eq_smul k (v := (invSelf f : T)) (invSelf_mul_self f)] at h

/-- For a localization away from `f`, the form `θ = dlog` of the unit `f` is `f⁻¹ df`. -/
theorem dlog_eq_invSelf_smul (h : IsUnit (algebraMap A T f)) :
    dlog k h.unit = (invSelf f : T) • diff k (algebraMap A T f) :=
  dlog_eq_smul k (invSelf_mul_self f)

end Away

section DerivationExt

variable {A : Type*} [CommRing A] {T : Type*} [CommRing T] [Algebra k T] [Algebra A T]
  {N : Type*} [AddCommGroup N] [Module T N] [Module k N]

/-- A derivation on a localization of `A` is determined by its values on `A`. -/
theorem derivation_ext_of_isLocalization (M : Submonoid A) [IsLocalization M T]
    {δ₁ δ₂ : Derivation k T N}
    (h : ∀ a : A, δ₁ (algebraMap A T a) = δ₂ (algebraMap A T a)) : δ₁ = δ₂ := by
  ext t
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalization.surj M t
  have key (δ : Derivation k T N) :
      algebraMap A T c • δ t = δ (algebraMap A T a) - t • δ (algebraMap A T c) := by
    rw [← show t * algebraMap A T c = algebraMap A T a from hc, Derivation.leibniz,
      add_sub_cancel_left]
  rw [← (IsLocalization.map_units T c).smul_left_cancel, key, key, h, h]

end DerivationExt

/-! ### Forms on a localization are a localization -/

section Localization

variable {A : Type*} [CommRing A] [Algebra k A]
  {T : Type*} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]

/-- `Ω_A^n → Ω_T^n` is a localization of `A`-modules, for any localization `T` of `A`. Its
underlying function is `Forms.mapPower (IsScalarTower.toAlgHom k A T) n`, by
`Forms.mapPower_toAlgHom`.

Blueprint: `lem:dr-localization`. -/
instance isLocalizedModule_powerMap_kaehlerMap (M : Submonoid A) [IsLocalization M T] (n : ℕ) :
    IsLocalizedModule M (powerMap T (KaehlerDifferential.map k k A T) n) :=
  isLocalizedModule_powerMap T M n

/-- `Ω_T^n` is the base change of `Ω_A^n` along `A → T`, for any localization `T` of `A`. So
`T ⊗[A] Ω_A^n ≃ₗ[T] Ω_T^n` is `IsBaseChange.equiv` of this statement.

Blueprint: `lem:dr-localization`. -/
theorem isBaseChange_powerMap_kaehlerMap (M : Submonoid A) [IsLocalization M T] (n : ℕ) :
    IsBaseChange T (powerMap T (KaehlerDifferential.map k k A T) n) :=
  (isLocalizedModule_iff_isBaseChange M T _).1 inferInstance

/-- Forms on `A` map to forms on `T` as a localization of `A`-modules, in total degree.

Blueprint: `lem:dr-localization`, in total degree. -/
instance isLocalizedModule_exteriorMap_kaehlerMap (M : Submonoid A) [IsLocalization M T] :
    IsLocalizedModule M (exteriorMap T (KaehlerDifferential.map k k A T)).toLinearMap :=
  (isLocalizedModule_iff_isBaseChange M T _).2 (isBaseChange_exteriorMap T
    ((isLocalizedModule_iff_isBaseChange M T _).1 inferInstance))

variable (T) in
/-- The identification `(Ω_A^n)_M ≃ Ω_T^n` of `A`-modules, for any localization `T` of `A` at a
submonoid `M`. It sends `x / c` to `c⁻¹ • x`, by `powerLocalizationEquiv_mk`.

Blueprint: `lem:dr-localization`. -/
noncomputable def powerLocalizationEquiv (M : Submonoid A) [IsLocalization M T] (n : ℕ) :
    LocalizedModule M (⋀[A]^n Ω[A⁄k]) ≃ₗ[A] ⋀[T]^n Ω[T⁄k] :=
  IsLocalizedModule.iso M (powerMap T (KaehlerDifferential.map k k A T) n)

/-- The identification sends `x / c` to `u • x` for any inverse `u` of `c`.

Blueprint: `lem:dr-localization`. -/
theorem powerLocalizationEquiv_mk_of_mul_eq_one {M : Submonoid A} [IsLocalization M T] {n : ℕ}
    (x : ⋀[A]^n Ω[A⁄k]) (c : M) {u : T} (hu : u * algebraMap A T c = 1) :
    powerLocalizationEquiv T M n (LocalizedModule.mk x c) =
      u • Forms.mapPower (IsScalarTower.toAlgHom k A T) n x := by
  have h : (c : A) • powerLocalizationEquiv T M n (LocalizedModule.mk x c) =
      powerMap T (KaehlerDifferential.map k k A T) n x :=
    IsLocalizedModule.mk'_cancel' (powerMap T (KaehlerDifferential.map k k A T) n) x c
  rw [Forms.mapPower_toAlgHom, ← h, ← algebraMap_smul T (c : A), smul_smul, hu, one_smul]

/-- The identification sends `x / c` to `c⁻¹ • x`, with `c⁻¹` written `IsLocalization.mk' T 1 c`.

Blueprint: `lem:dr-localization`. -/
theorem powerLocalizationEquiv_mk {M : Submonoid A} [IsLocalization M T] {n : ℕ}
    (x : ⋀[A]^n Ω[A⁄k]) (c : M) :
    powerLocalizationEquiv T M n (LocalizedModule.mk x c) =
      IsLocalization.mk' T (1 : A) c • Forms.mapPower (IsScalarTower.toAlgHom k A T) n x :=
  powerLocalizationEquiv_mk_of_mul_eq_one x c <| by
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]

/-- For a localization away from `f`, the identification sends `x / f^m` to `f^{-m} • x`.

Blueprint: `lem:dr-localization`. -/
theorem powerLocalizationEquiv_mk_pow (f : A) [IsLocalization.Away f T] {n : ℕ}
    (x : ⋀[A]^n Ω[A⁄k]) (m : ℕ) :
    powerLocalizationEquiv T (Submonoid.powers f) n
        (LocalizedModule.mk x ⟨f ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers f) m⟩) =
      (invSelf f : T) ^ m • Forms.mapPower (IsScalarTower.toAlgHom k A T) n x :=
  powerLocalizationEquiv_mk_of_mul_eq_one x _ <| by
    rw [map_pow, ← mul_pow, invSelf_mul_self, one_pow]

/-- A map of localizations commutes with the identifications: if `ψ : T → T'` lies over `φ : A → A'`
and `φ` sends `M` to `M'`, then `ψ_*(x / c) = φ_* x / φ c`. Such a `ψ` is unique when it exists, and
no flatness of `φ` is needed.

Blueprint: `lem:dr-localization`, the word "natural". -/
theorem mapPower_powerLocalizationEquiv {M : Submonoid A} [IsLocalization M T]
    {A' : Type*} [CommRing A'] [Algebra k A']
    {T' : Type*} [CommRing T'] [Algebra k T'] [Algebra A' T'] [IsScalarTower k A' T']
    {M' : Submonoid A'} [IsLocalization M' T']
    (φ : A →ₐ[k] A') (ψ : T →ₐ[k] T')
    (h : ψ.comp (IsScalarTower.toAlgHom k A T) = (IsScalarTower.toAlgHom k A' T').comp φ)
    (hM : ∀ c ∈ M, φ c ∈ M') {n : ℕ} (x : ⋀[A]^n Ω[A⁄k]) (c : M) :
    Forms.mapPower ψ n (powerLocalizationEquiv T M n (LocalizedModule.mk x c)) =
      powerLocalizationEquiv T' M' n
        (LocalizedModule.mk (Forms.mapPower φ n x) ⟨φ c, hM c c.2⟩) := by
  have hc : ∀ a, ψ (algebraMap A T a) = algebraMap A' T' (φ a) := fun a =>
    AlgHom.congr_fun h a
  rw [powerLocalizationEquiv_mk, Forms.mapPower_smul,
    powerLocalizationEquiv_mk_of_mul_eq_one (u := ψ (IsLocalization.mk' T (1 : A) c)) _ _
      (by
        rw [Subtype.coe_mk, ← hc, ← map_mul, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
          mul_one, IsLocalization.mk'_self, map_one])]
  congr 1
  rw [← LinearMap.comp_apply, ← Forms.mapPower_comp, h, Forms.mapPower_comp, LinearMap.comp_apply]

namespace Forms

variable (M : Submonoid A) [IsLocalization M T]

/-- A form on `A` maps to zero on a localization exactly when a member of the submonoid kills it.
In particular `A → T` need not be injective on forms.

Blueprint: `lem:dr-localization`, used by `lem:dr-projective`. -/
theorem map_eq_zero_iff_of_isLocalization {x : Forms k A} :
    map (IsScalarTower.toAlgHom k A T) x = 0 ↔ ∃ c : M, (c : A) • x = 0 := by
  rw [map_toAlgHom]
  exact IsLocalizedModule.eq_zero_iff M
    (exteriorMap T (KaehlerDifferential.map k k A T)).toLinearMap

/-- A form of degree `n` on `A` maps to zero on a localization exactly when a member of the
submonoid kills it.

Blueprint: `lem:dr-localization`, used by `lem:dr-projective`. -/
theorem mapPower_eq_zero_iff_of_isLocalization {n : ℕ} {x : ⋀[A]^n Ω[A⁄k]} :
    mapPower (IsScalarTower.toAlgHom k A T) n x = 0 ↔ ∃ c : M, (c : A) • x = 0 := by
  rw [mapPower_toAlgHom]
  exact IsLocalizedModule.eq_zero_iff M (powerMap T (KaehlerDifferential.map k k A T) n)

/-- Two forms on `A` have the same image on a localization exactly when a member of the submonoid
makes them equal.

Blueprint: `lem:dr-localization`. -/
theorem map_eq_map_iff_of_isLocalization {x y : Forms k A} :
    map (IsScalarTower.toAlgHom k A T) x = map (IsScalarTower.toAlgHom k A T) y ↔
      ∃ c : M, (c : A) • x = (c : A) • y := by
  rw [← sub_eq_zero, ← map_sub, map_eq_zero_iff_of_isLocalization M]
  simp only [smul_sub, sub_eq_zero]

/-- Two forms of degree `n` on `A` have the same image on a localization exactly when a member of
the submonoid makes them equal.

Blueprint: `lem:dr-localization`. -/
theorem mapPower_eq_mapPower_iff_of_isLocalization {n : ℕ} {x y : ⋀[A]^n Ω[A⁄k]} :
    mapPower (IsScalarTower.toAlgHom k A T) n x = mapPower (IsScalarTower.toAlgHom k A T) n y ↔
      ∃ c : M, (c : A) • x = (c : A) • y := by
  rw [← sub_eq_zero, ← map_sub, mapPower_eq_zero_iff_of_isLocalization M]
  simp only [smul_sub, sub_eq_zero]

end Forms

/-! ### The form of these statements for a localization away from an element -/

namespace Forms

variable (f : A) [IsLocalization.Away f T]

/-- A form on `A` maps to zero on the localization away from `f` exactly when a power of `f` kills
it. So `Ω_A^• → Ω_T^•` is injective when multiplication by `f` is.

Blueprint: `lem:dr-localization`, used by `lem:dr-projective`. -/
theorem map_eq_zero_iff_of_isLocalizationAway {x : Forms k A} :
    map (IsScalarTower.toAlgHom k A T) x = 0 ↔ ∃ m : ℕ, f ^ m • x = 0 := by
  rw [map_eq_zero_iff_of_isLocalization (Submonoid.powers f)]
  simp [Subtype.exists, Submonoid.mem_powers_iff]

/-- A form of degree `n` on `A` maps to zero on the localization away from `f` exactly when a power
of `f` kills it.

Blueprint: `lem:dr-localization`, used by `lem:dr-projective`. -/
theorem mapPower_eq_zero_iff_of_isLocalizationAway {n : ℕ} {x : ⋀[A]^n Ω[A⁄k]} :
    mapPower (IsScalarTower.toAlgHom k A T) n x = 0 ↔ ∃ m : ℕ, f ^ m • x = 0 := by
  rw [mapPower_eq_zero_iff_of_isLocalization (Submonoid.powers f)]
  simp [Subtype.exists, Submonoid.mem_powers_iff]

/-- Every form on the localization away from `f` is `f^{-m} ω` for a form `ω` on `A`.

Blueprint: `lem:dr-localization`, and the exhaustion in `def:dr-pole-filtration`. -/
theorem exists_eq_invSelf_pow_smul_map (y : Forms k T) :
    ∃ (m : ℕ) (x : Forms k A),
      y = (invSelf f : T) ^ m • map (IsScalarTower.toAlgHom k A T) x := by
  obtain ⟨⟨x, ⟨_, m, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (exteriorMap T (KaehlerDifferential.map k k A T)).toLinearMap y
  refine ⟨m, x, ?_⟩
  rw [map_toAlgHom]
  change _ = _ • exteriorMap T (KaehlerDifferential.map k k A T) x
  rw [← show (f ^ m) • y = exteriorMap T (KaehlerDifferential.map k k A T) x from hx,
    ← algebraMap_smul T (f ^ m), smul_smul, map_pow, ← mul_pow, invSelf_mul_self, one_pow, one_smul]

/-- Every form of degree `n` on the localization away from `f` is `f^{-m} ω` for a form `ω` of
degree `n` on `A`.

Blueprint: `lem:dr-localization`, and the exhaustion in `def:dr-pole-filtration`. -/
theorem exists_eq_invSelf_pow_smul_map_of_mem {n : ℕ} {y : Forms k T} (hy : y ∈ ⋀[T]^n Ω[T⁄k]) :
    ∃ (m : ℕ) (x : Forms k A), x ∈ ⋀[A]^n Ω[A⁄k] ∧
      y = (invSelf f : T) ^ m • map (IsScalarTower.toAlgHom k A T) x := by
  obtain ⟨⟨x, ⟨_, m, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (powerMap T (KaehlerDifferential.map k k A T) n) ⟨y, hy⟩
  refine ⟨m, x, x.2, ?_⟩
  rw [map_toAlgHom, ← coe_powerMap]
  have hx' : (f ^ m) • y = (powerMap T (KaehlerDifferential.map k k A T) n x : Forms k T) :=
    congrArg Subtype.val hx
  rw [← hx', ← algebraMap_smul T (f ^ m), smul_smul, map_pow, ← mul_pow, invSelf_mul_self, one_pow,
    one_smul]

end Forms

/-! ### Extending a derivation to a localization -/

section Derivation

variable {N : Type*} [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
  [Module k N] [IsScalarTower k A N] [IsScalarTower k T N]

variable (T) in
/-- The extension to a localization `T` of `A` of a derivation on `A` with values in a `T`-module.
It is the unique such extension, by `eq_extendDerivation`, and it is given by the quotient rule, by
`extendDerivation_invSelf_pow_mul`. This is the universal property behind
`isLocalizedModule_powerMap_kaehlerMap`.

Blueprint: the proof of `lem:dr-localization`, used by `lem:dr-normal-derivation`. -/
noncomputable def extendDerivation (M : Submonoid A) [IsLocalization M T]
    (δ : Derivation k A N) : Derivation k T N :=
  (((isLocalizedModule_iff_isBaseChange M T (KaehlerDifferential.map k k A T)).1 inferInstance).lift
    δ.liftKaehlerDifferential).compDer (D k T)

@[simp]
theorem extendDerivation_algebraMap (M : Submonoid A) [IsLocalization M T]
    (δ : Derivation k A N) (a : A) : extendDerivation T M δ (algebraMap A T a) = δ a := by
  change IsBaseChange.lift _ _ (D k T (algebraMap A T a)) = _
  rw [← KaehlerDifferential.map_D k k A T, IsBaseChange.lift_eq,
    Derivation.liftKaehlerDifferential_comp_D]

/-- The extension is the only derivation on the localization that restricts to `δ`. -/
theorem eq_extendDerivation (M : Submonoid A) [IsLocalization M T] {δ : Derivation k A N}
    {δ' : Derivation k T N} (h : ∀ a : A, δ' (algebraMap A T a) = δ a) :
    δ' = extendDerivation T M δ :=
  derivation_ext_of_isLocalization M fun a => by rw [h, extendDerivation_algebraMap]

/-- The quotient rule: `δ(a / f^m) = f^{-m} δ(a) - m a f^{-m-1} δ(f)`.

Blueprint: the proof of `lem:dr-localization`. -/
theorem extendDerivation_invSelf_pow_mul (f : A) [IsLocalization.Away f T]
    (δ : Derivation k A N) (m : ℕ) (a : A) :
    extendDerivation T (Submonoid.powers f) δ ((invSelf f : T) ^ m * algebraMap A T a) =
      (invSelf f : T) ^ m • δ a -
        ((m : T) * algebraMap A T a * (invSelf f : T) ^ (m + 1)) • δ f := by
  rw [Derivation.leibniz, leibniz_pow_of_mul_eq_one _ (invSelf_mul_self f),
    extendDerivation_algebraMap, extendDerivation_algebraMap, smul_neg, smul_smul, sub_eq_add_neg]
  congr 3
  ring

end Derivation

end Localization

end OrlikSolomon.DeRham
