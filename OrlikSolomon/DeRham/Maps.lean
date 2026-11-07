/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Maps.Gysin
public import OrlikSolomon.DeRham.Maps.Naturality
public import OrlikSolomon.DeRham.Pole

/-!
# The residue, the Gysin map, exactness and naturality

This is the module to import for the cohomological maps of a smooth principal pair, before the twist
by `t`. It imports the files under `DeRham/Maps`, whose headers list their results, and it uses
`thm:dr-comparison` to pass from the cohomology of logarithmic forms to the cohomology of the
localization.

## Summary of the design

The maps are on the total cohomology, as everything is, and degrees are statements about them. For
`h : IsSmoothPrincipalPair f φ`, for `T` a localization away from `f` and for
`hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)`:

* `gysin T h : Cohomology k S →ₗ[k] Cohomology k A` is `G`. It needs no comparison.
* `residue T hUnits h : Cohomology k T →ₗ[k] Cohomology k S` is `r`, which is `H(ρ)` after the
  inverse of `LogCohomology.toCohomology`. `residue_toCohomology` says so, and
  `residue_mk_of_mem_logForms` is the formula for a closed logarithmic representative.

The sign convention is the blueprint's: `ρ(θ ∧ η) = η|_S`, `ρ d = -d ρ`, the target differential is
`-d`, and `G[γ] = [dλ]`. So `G[γ] = [-θ ∧ dη]` for a regular lift `η`. There is no library
connecting map anywhere. See the header of `DeRham/Maps/Gysin`.

For a morphism of divisor pairs `F : P ⟶ Q`, `F.isPairHom` is the hypothesis of `residue_map` and
`gysin_map`, and for a divisor pair `P`, `P.isSmoothPrincipalPair` is the hypothesis `h`, with `T`
the certified `P.compl`, so that nothing needs transport.

## Main definitions

* `OrlikSolomon.DeRham.residue T hUnits h`: the residue `r : H^•(T) → H^•(S)`.

## Main results

Blueprint `def:dr-gysin`: `OrlikSolomon.DeRham.gysin` and `OrlikSolomon.DeRham.residue`, with
`OrlikSolomon.DeRham.gysin_mk_of_logResidue_eq` and `OrlikSolomon.DeRham.residue_toCohomology`.

Blueprint `lem:dr-exactness`:

* `OrlikSolomon.DeRham.exact_gysin_map`, `OrlikSolomon.DeRham.exact_map_residue` and
  `OrlikSolomon.DeRham.exact_residue_gysin`: exactness of the total maps, which are the three places
  of the sequence.
* `OrlikSolomon.DeRham.isHomogeneousOfShift_gysin` and
  `OrlikSolomon.DeRham.isHomogeneousOfShift_residue`: the maps have shifts `2` and `-1`.
* `OrlikSolomon.DeRham.map_eq_zero_iff_of_mem_grading`,
  `OrlikSolomon.DeRham.residue_eq_zero_iff_of_mem_grading` and
  `OrlikSolomon.DeRham.gysin_eq_zero_iff_of_mem_grading`: exactness in each integer degree.
  `H^(-2)(S)` and `H^(-1)(S)` are zero, and
  `OrlikSolomon.DeRham.map_eq_zero_iff_of_mem_degree_zero`,
  `OrlikSolomon.DeRham.map_eq_zero_iff_of_mem_degree_one` and
  `OrlikSolomon.DeRham.exists_map_eq_of_mem_degree_zero` say what that means for `n = 0` and
  `n = 1`.
* `OrlikSolomon.DeRham.residue_mk_of_mem_logForms` and
  `OrlikSolomon.DeRham.residue_mk_add_theta_mul`: `r[ω + θ ∧ η] = [η|_S]`.
* `OrlikSolomon.DeRham.gysin_mk_of_map_eq`: `G[γ] = [-θ ∧ dη]`.

Blueprint `thm:dr-projection`: `OrlikSolomon.DeRham.residue_mul_map`.

Blueprint `thm:dr-naturality`: `OrlikSolomon.DeRham.residue_map`, `OrlikSolomon.DeRham.gysin_map`,
`OrlikSolomon.DeRham.residue_eq_of_associated` and `OrlikSolomon.DeRham.gysin_eq_of_associated`.

Blueprint `thm:dr-log-naturality` is in `DeRham/Maps/Naturality`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.DeRham

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}
  (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T] (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

/-- The residue `r : H^•(T) → H^•(S)`: the map `H(ρ)` after the inverse of the logarithmic
comparison. It is characterized by `residue_toCohomology`, and by `residue_mk_of_mem_logForms` on a
closed logarithmic representative, of which every class has one. It has shift `-1`, by
`isHomogeneousOfShift_residue`. This is the residue of `OrdinaryTheory` before the twist by `t`.

Blueprint: `def:dr-gysin`. -/
@[no_expose] def residue (h : IsSmoothPrincipalPair f φ) : Cohomology k T →ₗ[k] Cohomology k S :=
  LogCohomology.residue T h ∘ₗ (logToLocalizationEquiv k f T hUnits h).symm.toLinearMap

variable {T}

/-- `r` is `H(ρ)` on the class of a closed logarithmic form.

Blueprint: `def:dr-gysin`. -/
@[simp]
theorem residue_toCohomology (h : IsSmoothPrincipalPair f φ) (c : LogCohomology k f T) :
    residue T hUnits h (LogCohomology.toCohomology k f T c) = LogCohomology.residue T h c := by
  have : (logToLocalizationEquiv k f T hUnits h).symm (LogCohomology.toCohomology k f T c) = c :=
    (logToLocalizationEquiv k f T hUnits h).symm_apply_eq.2
      (logToLocalizationEquiv_apply k f T hUnits h c).symm
  rw [residue, LinearMap.comp_apply]
  exact congrArg _ this

include hUnits in
/-- Every class on `T` has a closed logarithmic representative, by `thm:dr-comparison`, and
`residue_mk_of_mem_logForms` computes its residue.

Blueprint: the proof of `thm:dr-projection`. -/
theorem exists_toCohomology_eq (h : IsSmoothPrincipalPair f φ) (c : Cohomology k T) :
    ∃ c' : LogCohomology k f T, LogCohomology.toCohomology k f T c' = c :=
  (logToLocalizationQuasiIso k f T hUnits h).2 c

/-- `r[λ] = [ρ λ]` for a closed logarithmic form.

Blueprint: `lem:dr-exactness`. -/
theorem residue_mk_of_mem_logForms (h : IsSmoothPrincipalPair f φ) {x : Forms k T}
    (hx : x ∈ logForms k f T) (hd : d k x = 0) :
    residue T hUnits h (Cohomology.mk x hd) =
      Cohomology.mk (logResidue T h ⟨x, hx⟩)
        (d_logResidue_eq_zero h (logD_eq_zero_iff.2 hd)) :=
  residue_toCohomology hUnits h (LogCohomology.mk ⟨x, hx⟩ (logD_eq_zero_iff.2 hd))

/-- `r[ω + θ ∧ η] = [η|_S]`, for a closed logarithmic form. There is no further sign. The class
`[η|_S]` is closed although `η` need not be.

Blueprint: `lem:dr-exactness`. -/
theorem residue_mk_add_theta_mul (h : IsSmoothPrincipalPair f φ) (ω η : Forms k A)
    (hd : d k (reg ω + θ * reg η) = 0) :
    residue T hUnits h (Cohomology.mk (reg ω + θ * reg η) hd) =
      Cohomology.mk (Forms.map φ η) (logResidue_logMk (T := T) h (ω, η) ▸
        d_logResidue_eq_zero h (logD_eq_zero_iff.2 hd)) := by
  rw [residue_mk_of_mem_logForms hUnits h ⟨ω, η, rfl⟩ hd]
  exact Cohomology.mk_congr (logResidue_logMk h (ω, η)) _

/-! ### Exactness -/

variable (T)

include hUnits in
/-- Exactness at `H^n(A)`: a class on `A` vanishes on `T` exactly when it is a Gysin class.

Blueprint: `lem:dr-exactness`. -/
theorem exact_gysin_map (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (gysin T h) (Cohomology.map (IsScalarTower.toAlgHom k A T)) := fun c => by
  rw [← LogCohomology.toCohomology_ofCohomology (f := f),
    map_eq_zero_iff _ (logToLocalizationQuasiIso k f T hUnits h).1]
  exact exact_gysin_ofCohomology T h c

/-- Exactness at `H^n(T)`: a class on `T` has zero residue exactly when it comes from `A`.

Blueprint: `lem:dr-exactness`. -/
theorem exact_map_residue (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (Cohomology.map (IsScalarTower.toAlgHom k A T)) (residue T hUnits h) :=
      fun c => by
  obtain ⟨c, rfl⟩ := exists_toCohomology_eq hUnits h c
  rw [residue_toCohomology, LogCohomology.exact_ofCohomology_residue T h c]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, (LogCohomology.toCohomology_ofCohomology b).symm⟩
  · rintro ⟨b, hb⟩
    rw [← LogCohomology.toCohomology_ofCohomology (f := f)] at hb
    exact ⟨b, (logToLocalizationQuasiIso k f T hUnits h).1 hb⟩

/-- Exactness at `H^(n-1)(S)`: a class on `S` has zero Gysin image exactly when it is a residue.

Blueprint: `lem:dr-exactness`. -/
theorem exact_residue_gysin (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (residue T hUnits h) (gysin T h) := fun c => by
  rw [LogCohomology.exact_residue_gysin T h c]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, residue_toCohomology hUnits h b⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨b, rfl⟩ := exists_toCohomology_eq hUnits h b
    exact ⟨b, (residue_toCohomology hUnits h b).symm⟩

/-- The residue has shift `-1`: it sends `H^p(T)` to `H^(p-1)(S)`, for every integer `p`.

Blueprint: `lem:dr-exactness`, the degrees. -/
theorem isHomogeneousOfShift_residue (h : IsSmoothPrincipalPair f φ) :
    IsHomogeneousOfShift (Cohomology.grading k T) (Cohomology.grading k S) (-1)
      (residue T hUnits h) := by
  intro p c hc
  obtain ⟨c', hc', rfl⟩ :=
    (LogCohomology.isHomogeneousOfShift_toCohomology k f T).exists_mem_preimage_of_surjective
      (logToLocalizationQuasiIso k f T hUnits h).2 (add_zero p) hc
  rw [residue_toCohomology]
  exact LogCohomology.isHomogeneousOfShift_residue T h hc'

/-! ### Exactness in each degree -/

include hUnits in
/-- Exactness at `H^p(A)` in the sequence `H^(p-2)(S) → H^p(A) → H^p(T)`, for every integer `p`.

Blueprint: `lem:dr-exactness`. -/
theorem map_eq_zero_iff_of_mem_grading (h : IsSmoothPrincipalPair f φ) {p q : ℤ} (hq : q + 2 = p)
    {c : Cohomology k A} (hc : c ∈ Cohomology.grading k A p) :
    Cohomology.map (IsScalarTower.toAlgHom k A T) c = 0 ↔
      ∃ y ∈ Cohomology.grading k S q, gysin T h y = c :=
  (IsHomogeneousOfShift.exact_iff_forall_mem (isHomogeneousOfShift_gysin T h)
    (Cohomology.isHomogeneousOfShift_map _)).1 (exact_gysin_map T hUnits h) hq hc

/-- Exactness at `H^p(T)` in the sequence `H^p(A) → H^p(T) → H^(p-1)(S)`, for every integer `p`.

Blueprint: `lem:dr-exactness`. -/
theorem residue_eq_zero_iff_of_mem_grading (h : IsSmoothPrincipalPair f φ) {p : ℤ}
    {c : Cohomology k T} (hc : c ∈ Cohomology.grading k T p) :
    residue T hUnits h c = 0 ↔
      ∃ y ∈ Cohomology.grading k A p, Cohomology.map (IsScalarTower.toAlgHom k A T) y = c :=
  (IsHomogeneousOfShift.exact_iff_forall_mem (Cohomology.isHomogeneousOfShift_map _)
    (isHomogeneousOfShift_residue T hUnits h)).1 (exact_map_residue T hUnits h) (add_zero p) hc

/-- Exactness at `H^q(S)` in the sequence `H^(q+1)(T) → H^q(S) → H^(q+2)(A)`, for every integer `q`.

Blueprint: `lem:dr-exactness`. -/
theorem gysin_eq_zero_iff_of_mem_grading (h : IsSmoothPrincipalPair f φ) {p q : ℤ}
    (hq : p + -1 = q) {c : Cohomology k S} (hc : c ∈ Cohomology.grading k S q) :
    gysin T h c = 0 ↔ ∃ y ∈ Cohomology.grading k T p, residue T hUnits h y = c :=
  (IsHomogeneousOfShift.exact_iff_forall_mem (isHomogeneousOfShift_residue T hUnits h)
    (isHomogeneousOfShift_gysin T h)).1 (exact_residue_gysin T hUnits h) hq hc

include hUnits in
/-- In degree `n = 0`, the source `H^(-2)(S)` is zero, so `H^0(A) → H^0(T)` is injective.

Blueprint: `lem:dr-exactness`, the case `n = 0`. -/
theorem map_eq_zero_iff_of_mem_degree_zero (h : IsSmoothPrincipalPair f φ) {c : Cohomology k A}
    (hc : c ∈ Cohomology.degree k A 0) :
    Cohomology.map (IsScalarTower.toAlgHom k A T) c = 0 ↔ c = 0 := by
  rw [← Cohomology.grading_natCast] at hc
  rw [map_eq_zero_iff_of_mem_grading T hUnits h (q := -2) (by norm_num) hc]
  refine ⟨?_, fun hc => ⟨0, zero_mem _, by rw [map_zero, hc]⟩⟩
  rintro ⟨y, hy, rfl⟩
  rw [Cohomology.eq_zero_of_mem_grading_of_neg (by norm_num) hy, map_zero]

include hUnits in
/-- In degree `n = 1`, the source `H^(-1)(S)` is zero, so `H^1(A) → H^1(T)` is injective.

Blueprint: `lem:dr-exactness`, the case `n = 1`. -/
theorem map_eq_zero_iff_of_mem_degree_one (h : IsSmoothPrincipalPair f φ) {c : Cohomology k A}
    (hc : c ∈ Cohomology.degree k A 1) :
    Cohomology.map (IsScalarTower.toAlgHom k A T) c = 0 ↔ c = 0 := by
  rw [← Cohomology.grading_natCast] at hc
  rw [map_eq_zero_iff_of_mem_grading T hUnits h (q := -1) (by norm_num) hc]
  refine ⟨?_, fun hc => ⟨0, zero_mem _, by rw [map_zero, hc]⟩⟩
  rintro ⟨y, hy, rfl⟩
  rw [Cohomology.eq_zero_of_mem_grading_of_neg (by norm_num) hy, map_zero]

/-- The target of the residue in degree `n = 0` is `H^(-1)(S) = 0`.

Blueprint: `lem:dr-exactness`, the case `n = 0`. -/
theorem residue_eq_zero_of_mem_degree_zero (h : IsSmoothPrincipalPair f φ) {c : Cohomology k T}
    (hc : c ∈ Cohomology.degree k T 0) : residue T hUnits h c = 0 := by
  rw [← Cohomology.grading_natCast] at hc
  exact Cohomology.eq_zero_of_mem_grading_of_neg (p := ((0 : ℕ) : ℤ) + -1) (by norm_num)
    (isHomogeneousOfShift_residue T hUnits h hc)

include hUnits in
/-- In degree `n = 0`, the map `H^0(A) → H^0(T)` is surjective, since the residue vanishes there.
With `map_eq_zero_iff_of_mem_degree_zero`, this says that it is bijective.

Blueprint: `lem:dr-exactness`, the case `n = 0`. -/
theorem exists_map_eq_of_mem_degree_zero (h : IsSmoothPrincipalPair f φ) {c : Cohomology k T}
    (hc : c ∈ Cohomology.degree k T 0) :
    ∃ y ∈ Cohomology.degree k A 0, Cohomology.map (IsScalarTower.toAlgHom k A T) y = c := by
  have h0 := residue_eq_zero_of_mem_degree_zero T hUnits h hc
  rw [← Cohomology.grading_natCast] at hc
  simpa only [Cohomology.grading_natCast] using
    (residue_eq_zero_iff_of_mem_grading T hUnits h hc).1 h0

variable {T}

/-! ### The projection formula -/

/-- The right projection formula `r(a j_*b) = r(a) i_*b`, with no sign. Choose a closed logarithmic
representative of `a`; then this is `lem:dr-form-projection`. This is the sign that
`residue_mul_map` of `OrdinaryTheory` requires.

Blueprint: `thm:dr-projection`. -/
theorem residue_mul_map (h : IsSmoothPrincipalPair f φ) (a : Cohomology k T) (b : Cohomology k A) :
    residue T hUnits h (a * Cohomology.map (IsScalarTower.toAlgHom k A T) b) =
      residue T hUnits h a * Cohomology.map φ b := by
  obtain ⟨a, rfl⟩ := exists_toCohomology_eq hUnits h a
  rw [← LogCohomology.toCohomology_ofCohomology (f := f), ← map_mul, residue_toCohomology,
    residue_toCohomology, LogCohomology.residue_mul_ofCohomology]

/-! ### Naturality -/

section Naturality

variable {T' : Type*} [CommRing T'] {A' : Type*} [CommRing A'] [Algebra k A'] {f' : A'}
  {S' : Type*} [CommRing S'] [Algebra k S'] {π : A →ₐ[k] S} {π' : A' →ₐ[k] S'}
  [Algebra k T'] [Algebra A' T'] [IsScalarTower k A' T'] [IsLocalization.Away f' T']
  {φ : A →ₐ[k] A'} {ψ : S →ₐ[k] S'} {χ : T →ₐ[k] T'}

/-- `r' χ_* = ψ_* r`, for any map of pairs, with no flatness. The square of inclusions of
logarithmic forms commutes, and the inclusions are bijective on cohomology.

Blueprint: `thm:dr-naturality`. -/
theorem residue_map (H : IsPairHom f π f' π' φ ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (x : Cohomology k T) :
    residue T' hUnits h' (Cohomology.map χ x) = Cohomology.map ψ (residue T hUnits h x) := by
  obtain ⟨x, rfl⟩ := exists_toCohomology_eq hUnits h x
  rw [← LogCohomology.toCohomology_map H, residue_toCohomology, residue_toCohomology,
    LogCohomology.residue_map H h h']

end Naturality

/-- The residue does not change on replacing `f` by an associated equation.

Blueprint: `thm:dr-naturality`. -/
theorem residue_eq_of_associated {g : A} [IsLocalization.Away g T]
    (h : IsSmoothPrincipalPair f φ) (h' : IsSmoothPrincipalPair g φ) (hf : Associated f g) :
    residue T hUnits h' = residue T hUnits h := by
  ext x hx
  have := residue_map hUnits (IsPairHom.of_associated_id (T := T) (π := φ) hf) h h'
    (Cohomology.mk x hx)
  simpa [Cohomology.map_id] using this

end OrlikSolomon.DeRham
