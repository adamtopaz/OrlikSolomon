/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Maps.Gysin

/-!
# Naturality of the residue sequence for associated equations

A map of smooth principal pairs is a triple of algebra maps `φ : A → A'`, `ψ : S → S'` and
`χ : T → T'` that commute with the structure maps and with `φ(f) = u f'` for a unit `u` of `A'`.
This file proves that such a map is a morphism of the residue sequences. The point is that
`χ_* θ = θ' + du/u`, whose second term is regular on `A'`. No exact sequence is tensored along `φ`,
and `φ` need not be flat.

None of this uses `thm:dr-comparison`.

## Main definitions

* `OrlikSolomon.DeRham.IsPairHom f π f' π' φ ψ χ`: the conditions on the triple, as one predicate.
  `OrlikSolomon.DivisorPair.Hom.isPairHom` supplies them from a morphism of divisor pairs.
* `OrlikSolomon.DeRham.IsSmoothPrincipalPair.closedMap` and
  `OrlikSolomon.DeRham.localizationMap`: the maps `ψ` and `χ` induced by `φ`.
* `OrlikSolomon.DeRham.logMap H`: the restriction of `χ_*` to logarithmic forms.
* `OrlikSolomon.DeRham.logComplexMap H`, `OrlikSolomon.DeRham.shiftedComplexMap ψ` and
  `OrlikSolomon.DeRham.logResidueShortComplexMap H h h'`: the morphism of short exact sequences of
  complexes.
* `OrlikSolomon.DeRham.LogCohomology.map H`: the induced map on the cohomology of `L`.

## Main results

Blueprint `thm:dr-log-naturality`:

* `OrlikSolomon.DeRham.IsPairHom.map_theta`: `χ_* θ = θ' + du/u`.
* `OrlikSolomon.DeRham.IsPairHom.map_mem_logForms` and
  `OrlikSolomon.DeRham.IsPairHom.map_mem_logPower`: `χ_*` takes logarithmic forms to logarithmic
  forms, in each degree.
* `OrlikSolomon.DeRham.logMap_logMk`: the formula for `χ_*(ω + θ ∧ η)`.
* `OrlikSolomon.DeRham.logMap_logD`: `χ_*` commutes with the differentials.
* `OrlikSolomon.DeRham.logResidue_logMap`: `ρ' χ_* = ψ_* ρ`.
* `OrlikSolomon.DeRham.logMap_ofRegular`: `χ_*` restricts to `φ_*` on regular forms.
* `OrlikSolomon.DeRham.logResidueShortComplexMap`: the morphism of short exact sequences.

Blueprint `thm:dr-naturality`, on the logarithmic side:

* `OrlikSolomon.DeRham.LogCohomology.residue_map`: `H(ρ') χ_* = ψ_* H(ρ)`.
* `OrlikSolomon.DeRham.gysin_map`: `G' ψ_* = φ_* G`, with no sign.
* `OrlikSolomon.DeRham.logForms_eq_of_associated` and
  `OrlikSolomon.DeRham.gysin_eq_of_associated`: replacing `f` by an associated equation changes
  neither the logarithmic forms nor the Gysin map.
* `OrlikSolomon.DeRham.gysin_eq_of_localization`: nor does replacing `T` by another localization.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace OrlikSolomon.DeRham

section Forms

variable {k : Type*} [CommRing k]
  {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {π : A →ₐ[k] S}
  {T : Type*} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  {A' : Type*} [CommRing A'] [Algebra k A'] {f' : A'}
  {S' : Type*} [CommRing S'] [Algebra k S'] {π' : A' →ₐ[k] S'}
  {T' : Type*} [CommRing T'] [Algebra k T'] [Algebra A' T'] [IsScalarTower k A' T']
  {φ : A →ₐ[k] A'} {ψ : S →ₐ[k] S'} {χ : T →ₐ[k] T'}

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "reg'" => Forms.map (IsScalarTower.toAlgHom k A' T')

variable (f f' π π' φ ψ χ) in
/-- The conditions under which `φ : A → A'`, `ψ : S → S'` and `χ : T → T'` are a map of principal
pairs `(A, f, π : A → S, T) → (A', f', π' : A' → S', T')`: both squares commute, and `φ f` is
associated to `f'`, which is the blueprint's `φ(f) = u f'` for a unit `u` of `A'`. There is no
flatness condition. A morphism of divisor pairs is an instance, by
`DivisorPair.Hom.isPairHom`. By `IsPairHom.of_associated`, `IsPairHom.closed_eq` and
`IsPairHom.compl_eq`, the maps `ψ` and `χ` exist for any `φ` with `φ f` associated to `f'`, and are
determined by `φ`.

Blueprint: `thm:dr-log-naturality`. -/
structure IsPairHom : Prop where
  /-- The square of the maps to the closed parts commutes. -/
  comp_closed : ψ.comp π = π'.comp φ
  /-- The square of the maps to the localizations commutes. -/
  comp_compl : χ.comp (IsScalarTower.toAlgHom k A T) = (IsScalarTower.toAlgHom k A' T').comp φ
  /-- The equation goes to a unit multiple of the equation. -/
  associated_eqn : Associated (φ f) f'

namespace IsPairHom

variable (H : IsPairHom f π f' π' φ ψ χ)

include H

theorem closed_apply (a : A) : ψ (π a) = π' (φ a) :=
  DFunLike.congr_fun H.comp_closed a

theorem compl_apply (a : A) : χ (algebraMap A T a) = algebraMap A' T' (φ a) :=
  DFunLike.congr_fun H.comp_compl a

/-- The blueprint's `φ(f) = u f'`. -/
theorem exists_eq_unit_mul : ∃ u : A'ˣ, φ f = u * f' := by
  obtain ⟨u, hu⟩ := H.associated_eqn.symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- `χ_*` restricts to `φ_*` on regular forms. -/
theorem map_map_regular (x : Forms k A) : Forms.map χ (reg x) = reg' (Forms.map φ x) := by
  rw [Forms.map_map, H.comp_compl, Forms.map_map]

/-- `ψ_*` and `φ_*` commute with restriction to the closed part. -/
theorem map_map_closed (x : Forms k A) :
    Forms.map ψ (Forms.map π x) = Forms.map π' (Forms.map φ x) := by
  rw [Forms.map_map, H.comp_closed, Forms.map_map]

variable [IsLocalization.Away f T] [IsLocalization.Away f' T']

local notation "θ" => theta k f T
local notation "θ'" => theta k f' T'

/-- The change of `θ`: `χ_* θ = θ' + du/u` for `φ(f) = u f'`. The second term is regular on `A'`,
and this is what makes `χ_*` preserve logarithmic forms and their residues, with no flatness.

Blueprint: the proof of `thm:dr-log-naturality`. -/
theorem map_theta {u : A'ˣ} (hu : φ f = u * f') :
    Forms.map χ θ = θ' + reg' (dlog k u) := by
  set v := (IsLocalization.Away.algebraMap_isUnit (S := T) f).unit with hv
  set v' := (IsLocalization.Away.algebraMap_isUnit (S := T') f').unit with hv'
  have hmap : Units.map (χ : T →* T') v =
      Units.map (IsScalarTower.toAlgHom k A' T' : A' →* T') u * v' := by
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, hv, hv', IsUnit.unit_spec,
      H.compl_apply, hu, map_mul, IsScalarTower.coe_toAlgHom']
  calc Forms.map χ θ = dlog k (Units.map (χ : T →* T') v) := Forms.map_dlog χ v
    _ = dlog k (Units.map (IsScalarTower.toAlgHom k A' T' : A' →* T') u * v') := by rw [hmap]
    _ = reg' (dlog k u) + θ' := by rw [dlog_mul, ← Forms.map_dlog]; rfl
    _ = θ' + reg' (dlog k u) := add_comm _ _

/-- `χ_*(ω + θ ∧ η) = φ_* ω + du/u ∧ φ_* η + θ' ∧ φ_* η`.

Blueprint: the proof of `thm:dr-log-naturality`. -/
theorem map_add_theta_mul {u : A'ˣ} (hu : φ f = u * f') (ω η : Forms k A) :
    Forms.map χ (reg ω + θ * reg η) =
      reg' (Forms.map φ ω + dlog k u * Forms.map φ η) + θ' * reg' (Forms.map φ η) := by
  rw [map_add, map_mul, H.map_map_regular, H.map_map_regular, H.map_theta hu, add_mul, map_add,
    map_mul]
  abel

/-- `χ_*` takes logarithmic forms to logarithmic forms.

Blueprint: `thm:dr-log-naturality`. -/
theorem map_mem_logForms {x : Forms k T} (hx : x ∈ logForms k f T) :
    Forms.map χ x ∈ logForms k f' T' := by
  obtain ⟨ω, η, rfl⟩ := hx
  obtain ⟨u, hu⟩ := H.exists_eq_unit_mul
  exact ⟨_, _, (H.map_add_theta_mul hu ω η).symm⟩

/-- `χ_*` takes logarithmic forms of degree `n` to logarithmic forms of degree `n`.

Blueprint: `thm:dr-log-naturality`. -/
theorem map_mem_logPower {n : ℕ} {x : Forms k T} (hx : x ∈ logPower k f T n) :
    Forms.map χ x ∈ logPower k f' T' n :=
  mem_logPower_iff.2 ⟨H.map_mem_logForms (mem_logPower_iff.1 hx).1,
    Forms.map_mem_exteriorPower χ (mem_logPower_iff.1 hx).2⟩

end IsPairHom

/-! ### The map on logarithmic forms -/

section LogMap

variable [IsLocalization.Away f T] [IsLocalization.Away f' T']

/-- The restriction of `χ_*` to logarithmic forms, as a `k`-algebra map.

Blueprint: `thm:dr-log-naturality`. -/
def logMap (H : IsPairHom f π f' π' φ ψ χ) : logForms k f T →ₐ[k] logForms k f' T' where
  toFun x := ⟨Forms.map χ x, H.map_mem_logForms x.2⟩
  map_one' := Subtype.ext (map_one (Forms.map χ))
  map_mul' x y := Subtype.ext (map_mul (Forms.map χ) (x : Forms k T) y)
  map_zero' := Subtype.ext (map_zero (Forms.map χ))
  map_add' x y := Subtype.ext (map_add (Forms.map χ) (x : Forms k T) y)
  commutes' c := Subtype.ext ((Forms.map χ).commutes c)

variable (H : IsPairHom f π f' π' φ ψ χ)

@[simp]
theorem coe_logMap (x : logForms k f T) : (logMap H x : Forms k T') = Forms.map χ x :=
  rfl

/-- `χ_*(ω + θ ∧ η) = (φ_* ω + du/u ∧ φ_* η) + θ' ∧ φ_* η`, for `φ(f) = u f'`.

Blueprint: the proof of `thm:dr-log-naturality`. -/
theorem logMap_logMk {u : A'ˣ} (hu : φ f = u * f') (p : Forms k A × Forms k A) :
    logMap H (logMk k f T p) =
      logMk k f' T' (Forms.map φ p.1 + dlog k u * Forms.map φ p.2, Forms.map φ p.2) :=
  Subtype.ext (H.map_add_theta_mul hu p.1 p.2)

/-- `χ_*` restricts to `φ_*` on regular forms. This is the left square of the morphism of residue
sequences.

Blueprint: `thm:dr-log-naturality`. -/
@[simp]
theorem logMap_ofRegular (ω : Forms k A) :
    logMap H (ofRegular k f T ω) = ofRegular k f' T' (Forms.map φ ω) :=
  Subtype.ext (by rw [coe_logMap, coe_ofRegular, coe_ofRegular, H.map_map_regular])

/-- `χ_*` commutes with the differentials of logarithmic forms.

Blueprint: `thm:dr-log-naturality`. -/
@[simp]
theorem logMap_logD (x : logForms k f T) :
    logMap H (logD k f T x) = logD k f' T' (logMap H x) :=
  Subtype.ext (Forms.map_d χ (x : Forms k T))

/-- `ρ' χ_* = ψ_* ρ`. This is the right square of the morphism of residue sequences.

Blueprint: `thm:dr-log-naturality`. -/
theorem logResidue_logMap (h : IsSmoothPrincipalPair f π) (h' : IsSmoothPrincipalPair f' π')
    (x : logForms k f T) :
    logResidue T' h' (logMap H x) = Forms.map ψ (logResidue T h x) := by
  obtain ⟨p, rfl⟩ := logMk_surjective k f T x
  obtain ⟨u, hu⟩ := H.exists_eq_unit_mul
  rw [logMap_logMk H hu, logResidue_logMk, logResidue_logMk, H.map_map_closed]

/-! ### In each degree -/

/-- The restriction of `χ_*` to logarithmic forms of degree `n`, as a `k`-linear map.

Blueprint: `thm:dr-log-naturality`. -/
def logPowerMap (n : ℕ) : logPower k f T n →ₗ[k] logPower k f' T' n where
  toFun x := ⟨Forms.map χ x, H.map_mem_logPower x.2⟩
  map_add' x y := Subtype.ext (map_add (Forms.map χ) (x : Forms k T) y)
  map_smul' c x := Subtype.ext (map_smul (Forms.map χ) c (x : Forms k T))

@[simp]
theorem coe_logPowerMap (n : ℕ) (x : logPower k f T n) :
    (logPowerMap H n x : Forms k T') = Forms.map χ x :=
  rfl

/-- The map in each degree commutes with the differentials. -/
theorem logPowerD_logPowerMap (n : ℕ) (x : logPower k f T n) :
    logPowerD k f' T' n (logPowerMap H n x) = logPowerMap H (n + 1) (logPowerD k f T n x) :=
  Subtype.ext (Forms.map_d χ (x : Forms k T)).symm

/-- The map in each degree commutes with the map from regular forms. -/
theorem logPowerMap_powerToLog (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    logPowerMap H n (powerToLog k f T n x) = powerToLog k f' T' n (Forms.mapPower φ n x) :=
  Subtype.ext (H.map_map_regular (x : Forms k A))

/-- The map in each degree commutes with the map to forms on the localization. -/
theorem logPowerToPower_logPowerMap (n : ℕ) (x : logPower k f T n) :
    logPowerToPower k f' T' n (logPowerMap H n x) =
      Forms.mapPower χ n (logPowerToPower k f T n x) :=
  rfl

/-- The map in each degree commutes with the residues.

Blueprint: `thm:dr-log-naturality`. -/
theorem logPowerResidue_logPowerMap (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (n : ℕ) (x : logPower k f T (n + 1)) :
    logPowerResidue T' h' n (logPowerMap H (n + 1) x) =
      Forms.mapPower ψ n (logPowerResidue T h n x) :=
  Subtype.ext (logResidue_logMap H h h' (logPowerToLogForms k f T (n + 1) x))

end LogMap

/-! ### Existence of the induced maps -/

section Induced

omit [Algebra A T] [IsScalarTower k A T] in
variable (φ) in
/-- The map `ψ : S → S'` induced by `φ : A → A'`, when `φ f` is associated to `f'`. It exists
because `φ f` is zero modulo `f'`.

Blueprint: `thm:dr-log-naturality`. -/
def IsSmoothPrincipalPair.closedMap (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (hφ : Associated (φ f) f') : S →ₐ[k] S' :=
  AlgHom.liftOfSurjective π h.surjective (π'.comp φ) <| by
    intro a ha
    have ha' : π a = 0 := ha
    rw [← RingHom.mem_ker, h.ker_eq, Ideal.mem_span_singleton] at ha'
    obtain ⟨b, rfl⟩ := ha'
    have hf' : π' f' = 0 := by
      rw [← RingHom.mem_ker, h'.ker_eq, Ideal.mem_span_singleton]
    have hf : π' (φ f) = 0 := by
      obtain ⟨u, hu⟩ := hφ.symm
      rw [← hu, map_mul, hf', zero_mul]
    change π' (φ (f * b)) = 0
    rw [map_mul, map_mul, hf, zero_mul]

omit [Algebra A T] [IsScalarTower k A T] in
variable (φ) in
@[simp]
theorem IsSmoothPrincipalPair.closedMap_apply (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (hφ : Associated (φ f) f') (a : A) :
    h.closedMap φ h' hφ (π a) = π' (φ a) :=
  AlgHom.liftOfSurjective_apply π h.surjective (π'.comp φ) _ a

variable [IsLocalization.Away f T] [IsLocalization.Away f' T']

omit [Algebra A T] [IsScalarTower k A T] [IsLocalization.Away f T] [Algebra k T']
  [IsScalarTower k A' T'] in
variable (T') in
/-- `φ f` is invertible in `T'`, when it is associated to `f'`. -/
theorem isUnit_algebraMap_of_associated (hφ : Associated (φ f) f') :
    IsUnit (algebraMap A' T' (φ f)) := by
  obtain ⟨u, hu⟩ := hφ.symm
  rw [← hu, map_mul]
  exact (IsLocalization.Away.algebraMap_isUnit f').mul (u.isUnit.map _)

variable (T T' φ) in
/-- The map `χ : T → T'` induced by `φ : A → A'`, when `φ f` is associated to `f'`. It exists
because `φ f` is invertible in `T'`.

Blueprint: `thm:dr-log-naturality`. -/
def localizationMap (hφ : Associated (φ f) f') : T →ₐ[k] T' :=
  IsLocalization.Away.liftAlgHom (S := T) (f := (IsScalarTower.toAlgHom k A' T').comp φ) f
    (isUnit_algebraMap_of_associated T' hφ)

@[simp]
theorem localizationMap_algebraMap (hφ : Associated (φ f) f') (a : A) :
    localizationMap T T' φ hφ (algebraMap A T a) = algebraMap A' T' (φ a) :=
  IsLocalization.Away.lift_eq (S := T) (g := ((IsScalarTower.toAlgHom k A' T').comp φ : A →+* T')) f
    (isUnit_algebraMap_of_associated T' hφ) a

/-- A map `ψ` commuting with `φ`, with the induced map of localizations, is a map of pairs. -/
theorem IsPairHom.of_comp_closed (hψ : ψ.comp π = π'.comp φ) (hφ : Associated (φ f) f') :
    IsPairHom f π f' π' φ ψ (localizationMap T T' φ hφ) where
  comp_closed := hψ
  comp_compl := AlgHom.ext fun a => by
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', localizationMap_algebraMap]
  associated_eqn := hφ

/-- For any `φ` with `φ f` associated to `f'`, the induced maps are a map of pairs. This holds for
arbitrary `φ`, with no flatness.

Blueprint: `thm:dr-log-naturality`. -/
theorem IsPairHom.of_associated (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (hφ : Associated (φ f) f') :
    IsPairHom f π f' π' φ (h.closedMap φ h' hφ) (localizationMap T T' φ hφ) :=
  .of_comp_closed (AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, IsSmoothPrincipalPair.closedMap_apply]) hφ

omit [IsLocalization.Away f T] [IsLocalization.Away f' T'] in
/-- The map `ψ` of a map of pairs is the induced one. -/
theorem IsPairHom.closed_eq (H : IsPairHom f π f' π' φ ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') : ψ = h.closedMap φ h' H.associated_eqn := by
  ext s
  obtain ⟨a, rfl⟩ := h.surjective s
  rw [H.closed_apply, IsSmoothPrincipalPair.closedMap_apply]

/-- The map `χ` of a map of pairs is the induced one. -/
theorem IsPairHom.compl_eq (H : IsPairHom f π f' π' φ ψ χ) :
    χ = localizationMap T T' φ H.associated_eqn := by
  refine AlgHom.toRingHom_injective
    (IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_))
  simp only [RingHom.comp_apply, RingHom.coe_coe, H.compl_apply, localizationMap_algebraMap]

end Induced

/-! ### Associated equations -/

section Associated

variable {g : A}

/-- Replacing the equation by an associated one, with the same closed part, keeps a smooth principal
pair. -/
theorem IsSmoothPrincipalPair.of_associated (h : IsSmoothPrincipalPair f π) (hf : Associated f g) :
    IsSmoothPrincipalPair g π where
  mem_nonZeroDivisors := by
    obtain ⟨u, rfl⟩ := hf
    exact mul_mem h.mem_nonZeroDivisors u.isUnit.mem_nonZeroDivisors
  surjective := h.surjective
  ker_eq := by
    rw [h.ker_eq]
    exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 hf.dvd')
      (Ideal.span_singleton_le_span_singleton.2 hf.dvd)
  formallySmooth_ambient := h.formallySmooth_ambient
  formallySmooth_closed := h.formallySmooth_closed

/-- The identities are a map of pairs from an equation to an associated one, with the same closed
part and the same localization. So anything natural for maps of pairs is unchanged by replacing `f`
by an associated equation.

Blueprint: `thm:dr-naturality`. -/
theorem IsPairHom.of_associated_id (hf : Associated f g) :
    IsPairHom f π g π (AlgHom.id k A) (AlgHom.id k S) (AlgHom.id k T) where
  comp_closed := rfl
  comp_compl := rfl
  associated_eqn := hf

variable [IsLocalization.Away f T] [IsLocalization.Away g T]

/-- The logarithmic forms do not change on replacing `f` by an associated equation, since the
extra `du/u` is regular.

Blueprint: `thm:dr-naturality`. -/
theorem logForms_eq_of_associated (hf : Associated f g) : logForms k f T = logForms k g T := by
  have key : ∀ {f g : A} [IsLocalization.Away f T] [IsLocalization.Away g T], Associated f g →
      logForms k f T ≤ logForms k g T := by
    intro f g _ _ hf x hx
    have H : IsPairHom f (AlgHom.id k A) g (AlgHom.id k A) (AlgHom.id k A) (AlgHom.id k A)
        (AlgHom.id k T) := IsPairHom.of_associated_id hf
    simpa using H.map_mem_logForms hx
  exact le_antisymm (key hf) (key hf.symm)

end Associated

/-! ### Cohomology -/

section Cohomology

variable [IsLocalization.Away f T] [IsLocalization.Away f' T']

/-- `χ_*` preserves closed logarithmic forms. -/
theorem logD_logMap_eq_zero (H : IsPairHom f π f' π' φ ψ χ) {x : logForms k f T}
    (hx : logD k f T x = 0) : logD k f' T' (logMap H x) = 0 := by
  rw [← logMap_logD, hx, map_zero]

/-- The restriction of `χ_*` to closed logarithmic forms. -/
def logCyclesMap (H : IsPairHom f π f' π' φ ψ χ) : logCycles k f T →ₐ[k] logCycles k f' T' :=
  ((Forms.map χ).comp (logCycles k f T).val).codRestrict (logCycles k f' T') fun z =>
    ⟨H.map_mem_logForms z.2.1, Cohomology.d_map_eq_zero χ (mem_logCycles.1 z.2).2⟩

namespace LogCohomology

/-- The class of the image of a closed logarithmic form. -/
theorem mkₐ_logCyclesMap (H : IsPairHom f π f' π' φ ψ χ) (z : logCycles k f T) :
    mkₐ k f' T' (logCyclesMap H z) = mk (logMap H ⟨z, z.2.1⟩)
      (logD_logMap_eq_zero H (logD_eq_zero_iff.2 (mem_logCycles.1 z.2).2)) :=
  rfl

/-- The map on the cohomology of logarithmic forms induced by a map of pairs. It is `χ_*` on
representatives, by `map_mk`, and it is compatible with the maps of cohomology by
`toCohomology_map`, `map_ofCohomology` and `residue_map`.

Blueprint: `thm:dr-log-naturality`, on cohomology. -/
def map (H : IsPairHom f π f' π' φ ψ χ) : LogCohomology k f T →ₐ[k] LogCohomology k f' T' :=
  lift ((mkₐ k f' T').comp (logCyclesMap H)) fun y => by
    rw [AlgHom.comp_apply, mkₐ_logCyclesMap]
    exact mk_eq_zero_iff.2 ⟨logMap H y, (logMap_logD H y).symm⟩

@[simp]
theorem map_mk (H : IsPairHom f π f' π' φ ψ χ) (x : logForms k f T) (hx : logD k f T x = 0) :
    map H (mk x hx) = mk (logMap H x) (logD_logMap_eq_zero H hx) :=
  rfl

/-- The square of `H^•(L) → H^•(T)` commutes.

Blueprint: the proof of `thm:dr-naturality`. -/
@[simp]
theorem toCohomology_map (H : IsPairHom f π f' π' φ ψ χ) (c : LogCohomology k f T) :
    toCohomology k f' T' (map H c) = Cohomology.map χ (toCohomology k f T c) := by
  induction c with
  | mk x hx => rfl

/-- The square of `H^•(A) → H^•(L)` commutes. -/
@[simp]
theorem map_ofCohomology (H : IsPairHom f π f' π' φ ψ χ) (c : Cohomology k A) :
    map H (ofCohomology k f T c) = ofCohomology k f' T' (Cohomology.map φ c) := by
  induction c with
  | mk ω hω =>
    rw [ofCohomology_mk, map_mk, Cohomology.map_mk, ofCohomology_mk]
    exact mk_eq_mk_iff.2 ⟨0, by rw [map_zero, logMap_ofRegular, sub_self]⟩

/-- `H(ρ') χ_* = ψ_* H(ρ)` on the cohomology of logarithmic forms.

Blueprint: `thm:dr-naturality`, on the logarithmic side. -/
theorem residue_map (H : IsPairHom f π f' π' φ ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (c : LogCohomology k f T) :
    residue T' h' (map H c) = Cohomology.map ψ (residue T h c) := by
  induction c with
  | mk x hx =>
    rw [map_mk, residue_mk, residue_mk, Cohomology.map_mk]
    exact Cohomology.mk_congr (logResidue_logMap H h h' x) _

end LogCohomology

/-- `G' ψ_* = φ_* G`, with no sign: if `λ` lifts `γ` then `χ_* λ` lifts `ψ_* γ`, and its
differential is `χ_* dλ`, which is the image of the regular form `φ_* dλ`.

Blueprint: `thm:dr-naturality`. -/
theorem gysin_map (H : IsPairHom f π f' π' φ ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (c : Cohomology k S) :
    gysin T' h' (Cohomology.map ψ c) = Cohomology.map φ (gysin T h c) := by
  induction c with
  | mk γ hγ =>
    obtain ⟨x, ω, hx, hω⟩ := exists_gysin_representative (T := T) h ⟨γ, hγ⟩
    rw [gysin_mk_of_logResidue_eq h hγ hx hω, Cohomology.map_mk, Cohomology.map_mk,
      gysin_mk_of_logResidue_eq h' _ (x := logMap H x) (ω := Forms.map φ ω)
        (by rw [logResidue_logMap H h h', hx])
        (by rw [← logMap_ofRegular H, hω, logMap_logD])]

end Cohomology

section Associated

variable {g : A} [IsLocalization.Away f T] [IsLocalization.Away g T]

/-- The Gysin map does not change on replacing `f` by an associated equation.

Blueprint: `thm:dr-naturality`. -/
theorem gysin_eq_of_associated (h : IsSmoothPrincipalPair f π) (h' : IsSmoothPrincipalPair g π)
    (hf : Associated f g) : gysin T h' = gysin T h := by
  ext x hx
  have := gysin_map (IsPairHom.of_associated_id (T := T) (π := π) hf) h h' (Cohomology.mk x hx)
  simpa [Cohomology.map_id] using this

/-- `H(ρ)` does not change on replacing `f` by an associated equation, under the identification of
the cohomology of the two logarithmic complexes by `LogCohomology.map`.

Blueprint: `thm:dr-naturality`. -/
theorem LogCohomology.residue_map_of_associated (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair g π) (hf : Associated f g) (c : LogCohomology k f T) :
    residue T h' (map (IsPairHom.of_associated_id (T := T) (π := π) hf) c) = residue T h c := by
  rw [residue_map _ h h', Cohomology.map_id, AlgHom.id_apply]

end Associated

/-- The Gysin map does not depend on the localization. -/
theorem gysin_eq_of_localization (T T' : Type*) [CommRing T] [Algebra k T] [Algebra A T]
    [IsScalarTower k A T] [IsLocalization.Away f T] [CommRing T'] [Algebra k T'] [Algebra A T']
    [IsScalarTower k A T'] [IsLocalization.Away f T'] (h : IsSmoothPrincipalPair f π) :
    gysin T' h = gysin T h := by
  ext x hx
  have H : IsPairHom f π f π (AlgHom.id k A) (AlgHom.id k S)
      (localizationMap T T' (AlgHom.id k A) (Associated.refl f)) :=
    IsPairHom.of_comp_closed (φ := AlgHom.id k A) (ψ := AlgHom.id k S) (π := π) (π' := π) rfl _
  have := gysin_map H h h (Cohomology.mk x hx)
  simpa [Cohomology.map_id] using this

end Forms

/-! ### Complexes -/

section Complex

universe u v

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A] {f : A}
  {S : Type v} [CommRing S] [Algebra k S] {π : A →ₐ[k] S}
  {T : Type v} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]
  {A' : Type v} [CommRing A'] [Algebra k A'] {f' : A'}
  {S' : Type v} [CommRing S'] [Algebra k S'] {π' : A' →ₐ[k] S'}
  {T' : Type v} [CommRing T'] [Algebra k T'] [Algebra A' T'] [IsScalarTower k A' T']
  [IsLocalization.Away f' T']
  {φ : A →ₐ[k] A'} {ψ : S →ₐ[k] S'} {χ : T →ₐ[k] T'}

/-- The chain map `L^• → L'^•` induced by a map of pairs. There is no flatness in this statement.

Blueprint: `thm:dr-log-naturality`. -/
def logComplexMap (H : IsPairHom f π f' π' φ ψ χ) : logComplex k f T ⟶ logComplex k f' T' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (logPowerMap H n)) fun n => by
    rw [logComplex_d, logComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext (logPowerD_logPowerMap H n))

@[simp]
theorem logComplexMap_f (H : IsPairHom f π f' π' φ ψ χ) (n : ℕ) :
    (logComplexMap H).f n = ModuleCat.ofHom (logPowerMap H n) :=
  rfl

/-- The square of the inclusions in forms on the localizations commutes, on complexes.

Blueprint: the proof of `thm:dr-log-naturality`. -/
theorem logComplexMap_comp_logToLocalization (H : IsPairHom f π f' π' φ ψ χ) :
    logComplexMap H ≫ logToLocalization k f' T' = logToLocalization k f T ≫ complexMap χ := by
  ext n : 2
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, logComplexMap_f, logToLocalization_f,
    logToLocalization_f, complexMap_f]
  exact LinearMap.ext fun x => logPowerToPower_logPowerMap H n x

/-- The components of the map `Ω_S^•[-1] → Ω_S'^•[-1]`. -/
def shiftedMapF (ψ : S →ₐ[k] S') :
    (n : ℕ) → (shiftedComplex k S).X n ⟶ (shiftedComplex k S').X n
  | 0 => 0
  | n + 1 => ModuleCat.ofHom (Forms.mapPower ψ n)

/-- The chain map `Ω_S^•[-1] → Ω_S'^•[-1]` induced by `ψ`, whose differentials are `-d`.

Blueprint: `thm:dr-log-naturality`. -/
def shiftedComplexMap (ψ : S →ₐ[k] S') : shiftedComplex k S ⟶ shiftedComplex k S' :=
  CochainComplex.ofHom (shiftedMapF ψ) <| by
    rintro (_ | n)
    · refine Limits.zero_comp.trans ?_
      rw [show (shiftedComplex k S).d 0 (0 + 1) = 0 from shiftedComplex_d_zero k S,
        Limits.zero_comp]
    · rw [shiftedComplex_d_succ, shiftedComplex_d_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : ⋀[S]^n Ω[S⁄k]) => ?_)
      change -powerD k S' n (Forms.mapPower ψ n x) = Forms.mapPower ψ (n + 1) (-powerD k S n x)
      rw [map_neg, Forms.mapPower_powerD]

/-- A map of pairs is a morphism of the residue sequences `0 → Ω_A^• → L^• → Ω_S^•[-1] → 0`. There
is no flatness of `φ` here: nothing is tensored along it.

Blueprint: `thm:dr-log-naturality`. -/
def logResidueShortComplexMap (H : IsPairHom f π f' π' φ ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') :
    logResidueShortComplex T h ⟶ logResidueShortComplex T' h' where
  τ₁ := complexMap φ
  τ₂ := logComplexMap H
  τ₃ := shiftedComplexMap ψ
  comm₁₂ := by
    refine HomologicalComplex.hom_ext _ _ fun n =>
      ModuleCat.hom_ext (LinearMap.ext fun x => (logPowerMap_powerToLog H n x).symm)
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun n =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    cases n with
    | zero => rfl
    | succ n => exact logPowerResidue_logPowerMap H h h' n x

end Complex

/-! ### Divisor pairs -/

section DivisorPair

variable {k : Type*} [CommRing k] {P Q : DivisorPair k}

/-- A morphism of divisor pairs is a map of pairs. Its commuting squares and `Associated` are
exactly the conditions of `IsPairHom`, so all of this file applies to it directly.

Blueprint: `thm:dr-log-naturality`, the last sentence of its proof. -/
theorem _root_.OrlikSolomon.DivisorPair.Hom.isPairHom (F : P ⟶ Q) :
    IsPairHom P.eqn (SmoothAlg.algHom P.i) Q.eqn (SmoothAlg.algHom Q.i)
      (SmoothAlg.algHom F.ambient) (SmoothAlg.algHom F.closed) (SmoothAlg.algHom F.compl) where
  comp_closed := AlgHom.ext fun x => ConcreteCategory.congr_hom F.i_comp x
  comp_compl := AlgHom.ext fun x => ConcreteCategory.congr_hom F.j_comp x
  associated_eqn := F.associated_eqn

end DivisorPair

end OrlikSolomon.DeRham
