/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Log

/-!
# The Gysin map and the logarithmic long exact sequence

For a smooth principal pair, the residue sequence `0 → Ω_A^• → L^• → Ω_S^•[-1] → 0` gives a long
exact sequence
`⋯ → H^(n-2)(S) → H^n(A) → H^n(L) → H^(n-1)(S) → H^(n+1)(A) → ⋯`.
This file constructs its maps on representatives and proves its exactness directly, with no
reference to a library connecting map, so that the signs are the blueprint's and nothing else:
`ρ(θ ∧ η) = η|_S`, `ρ d = -d ρ`, and `G[γ] = [dλ]` for `ρ λ = γ`. This file does not use
`thm:dr-comparison`, so it is about `H^•(L)` and not `H^•(T)`.

As elsewhere, everything is in total degree first, with `LogCohomology.mk`, `Cohomology.mk` and
`Cohomology.induction`, and degrees are statements about the total maps.

## Main definitions

* `OrlikSolomon.DeRham.LogCohomology.residue T h`: the map `H(ρ) : H^•(L) → H^•(S)`.
* `OrlikSolomon.DeRham.gysin T h`: the Gysin map `G : H^•(S) → H^•(A)`.

## Main results

Blueprint `def:dr-gysin`:

* `OrlikSolomon.DeRham.gysin_mk_of_logResidue_eq`: `G[γ] = [dλ]`, for any `λ` with `ρ λ = γ`.
* `OrlikSolomon.DeRham.LogCohomology.residue_mk`: `H(ρ)[λ] = [ρ λ]`.

Blueprint `lem:dr-exactness`, on the logarithmic side:

* `OrlikSolomon.DeRham.LogCohomology.residue_mk_logMk`: `H(ρ)[ω + θ ∧ η] = [η|_S]`.
* `OrlikSolomon.DeRham.gysin_mk_of_map_eq`: `G[γ] = [-θ ∧ dη]`, for any regular lift `η` of `γ`, and
  `OrlikSolomon.DeRham.exists_mem_exteriorPower_map_eq_neg_theta_mul` says that this form is
  regular, in the right degree.
* `OrlikSolomon.DeRham.gysin_mk_of_d_eq`: `G[γ] = [-df ∧ y]`, when `dη = f y + df ∧ z`, which does
  not mention `T`.
* `OrlikSolomon.DeRham.exact_gysin_ofCohomology`,
  `OrlikSolomon.DeRham.LogCohomology.exact_ofCohomology_residue` and
  `OrlikSolomon.DeRham.LogCohomology.exact_residue_gysin`: exactness at the three places.
* `OrlikSolomon.DeRham.isHomogeneousOfShift_gysin` and
  `OrlikSolomon.DeRham.LogCohomology.isHomogeneousOfShift_residue`: the shifts `2` and `-1`.

Blueprint `thm:dr-projection`, on the logarithmic side:
`OrlikSolomon.DeRham.LogCohomology.residue_mul_ofCohomology`, with no sign.

## Connecting maps

The exact sequence is proved on elements. Mathlib's connecting map for `logResidueShortExact` would
need `H^(n+1)(shiftedComplex k S) ≃ H^n(Ω_S)`, with its sign, and a lemma reconciling that map with
`[γ] ↦ [dλ]`. Neither is needed here: `gysin` is defined by the formula, so that nothing depends on
a library convention.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.DeRham

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}
  (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

/-! ### The residue on cohomology -/

variable {T} in
/-- The residue of a closed logarithmic form is closed, since `ρ d = -d ρ`. -/
theorem d_logResidue_eq_zero (h : IsSmoothPrincipalPair f φ) {x : logForms k f T}
    (hx : logD k f T x = 0) : d k (logResidue T h x) = 0 := by
  have := logResidue_logD h x
  rwa [hx, map_zero, eq_comm, neg_eq_zero] at this

/-- The residue, as a `k`-linear map from closed logarithmic forms to closed forms. -/
def logCyclesResidue (h : IsSmoothPrincipalPair f φ) : logCycles k f T →ₗ[k] cycles k S where
  toFun z := ⟨logResidue T h ⟨z, z.2.1⟩,
    d_logResidue_eq_zero h (logD_eq_zero_iff.2 (mem_logCycles.1 z.2).2)⟩
  map_add' x y := Subtype.ext (map_add (logResidue T h) ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
  map_smul' c z := Subtype.ext (map_smul (logResidueₗ T h) c ⟨z, z.2.1⟩)

namespace LogCohomology

/-- The map `H(ρ) : H^•(L) → H^•(S)` on the cohomology of logarithmic forms, characterized by
`residue_mk`. It is well defined because `ρ (d y) = -d (ρ y)`, and it lowers degrees by one, by
`isHomogeneousOfShift_residue`. The minus sign in `ρ d = -d ρ` introduces no sign here.

Blueprint: `def:dr-gysin`, "the map induced by `ρ`". -/
def residue (h : IsSmoothPrincipalPair f φ) : LogCohomology k f T →ₗ[k] Cohomology k S :=
  liftLinear ((Cohomology.mkₐ k S).toLinearMap ∘ₗ logCyclesResidue T h) fun y =>
    Cohomology.mk_eq_zero_iff.2 ⟨-logResidue T h y, by
      rw [map_neg]
      exact (logResidue_logD h y).symm⟩

variable {T}

/-- `H(ρ)[λ] = [ρ λ]`.

Blueprint: `def:dr-gysin`. -/
@[simp]
theorem residue_mk (h : IsSmoothPrincipalPair f φ) (x : logForms k f T) (hx : logD k f T x = 0) :
    residue T h (mk x hx) = Cohomology.mk (logResidue T h x) (d_logResidue_eq_zero h hx) :=
  rfl

/-- `H(ρ)[ω + θ ∧ η] = [η|_S]`, for a closed logarithmic form. There is no further sign.

Blueprint: `lem:dr-exactness`. -/
theorem residue_mk_logMk (h : IsSmoothPrincipalPair f φ) (ω η : Forms k A)
    (hx : logD k f T (logMk k f T (ω, η)) = 0) :
    residue T h (mk (logMk k f T (ω, η)) hx) =
      Cohomology.mk (Forms.map φ η)
        (logResidue_logMk (T := T) h (ω, η) ▸ d_logResidue_eq_zero h hx) := by
  rw [residue_mk]
  exact Cohomology.mk_congr (logResidue_logMk h (ω, η)) _

/-- `H(ρ)` vanishes on the classes of regular forms. -/
@[simp]
theorem residue_ofCohomology (h : IsSmoothPrincipalPair f φ) (c : Cohomology k A) :
    residue T h (ofCohomology k f T c) = 0 := by
  induction c with
  | mk ω hω =>
    rw [ofCohomology_mk, residue_mk]
    exact Cohomology.mk_eq_zero_iff.2 ⟨0, by rw [logResidue_ofRegular, map_zero]⟩

/-- A class in degree `n + 1` has residue in degree `n`.

Blueprint: `lem:dr-exactness`, the degrees. -/
theorem residue_mem_degree (h : IsSmoothPrincipalPair f φ) {n : ℕ} {c : LogCohomology k f T}
    (hc : c ∈ degree k f T (n + 1)) : residue T h c ∈ Cohomology.degree k S n := by
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  exact Cohomology.mk_mem_degree (logResidue_mem_exteriorPower h hxn) _

/-- The residue vanishes in degree zero, whose target is `H^(-1)(S) = 0`.

Blueprint: `lem:dr-exactness`, the degrees. -/
theorem residue_eq_zero_of_mem_degree_zero (h : IsSmoothPrincipalPair f φ)
    {c : LogCohomology k f T} (hc : c ∈ degree k f T 0) : residue T h c = 0 := by
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  rw [residue_mk]
  exact Cohomology.mk_eq_zero_iff.2
    ⟨0, by rw [logResidue_eq_zero_of_mem_logPower_zero h hxn, map_zero]⟩

variable (T) in
/-- `H(ρ)` has shift `-1`: it sends `H^p(L)` to `H^(p-1)(S)`, for every integer `p`.

Blueprint: `lem:dr-exactness`, the degrees. -/
theorem isHomogeneousOfShift_residue (h : IsSmoothPrincipalPair f φ) :
    IsHomogeneousOfShift (grading k f T) (Cohomology.grading k S) (-1) (residue T h) := by
  intro p c hc
  obtain hp | hp := lt_or_ge p 0
  · rw [eq_zero_of_mem_grading_of_neg hp hc, map_zero]
    exact zero_mem _
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [grading_natCast] at hc
  cases n with
  | zero =>
    rw [residue_eq_zero_of_mem_degree_zero h hc]
    exact zero_mem _
  | succ n =>
    have := residue_mem_degree h hc
    rw [← Cohomology.grading_natCast] at this
    convert this using 2
    push_cast
    ring

/-- The right projection formula on cohomology: `H(ρ)(a ∧ b) = H(ρ)(a) ∧ b|_S`, with no sign, since
no factor moves across `θ`.

Blueprint: `thm:dr-projection`, on the logarithmic side. -/
theorem residue_mul_ofCohomology (h : IsSmoothPrincipalPair f φ) (a : LogCohomology k f T)
    (b : Cohomology k A) :
    residue T h (a * ofCohomology k f T b) = residue T h a * Cohomology.map φ b := by
  induction a with
  | mk x hx =>
    induction b with
    | mk ω hω =>
      rw [ofCohomology_mk, mk_mul, residue_mk, residue_mk, Cohomology.map_mk, Cohomology.mk_mul]
      exact Cohomology.mk_congr (logResidue_mul_ofRegular h x ω) _

end LogCohomology

/-! ### The Gysin map -/

omit [IsScalarTower k A T] in
/-- `ofRegular` is `k`-linear. -/
theorem ofRegular_smul [IsScalarTower k A T] (c : k) (ω : Forms k A) :
    ofRegular k f T (c • ω) = c • ofRegular k f T ω :=
  map_smul ((ofRegular k f T).restrictScalars k) c ω

variable {T} in
/-- A logarithmic form whose residue is closed has a regular differential, since
`ρ (d x) = -d (ρ x)`.

Blueprint: `def:dr-gysin`. -/
theorem exists_ofRegular_eq_logD (h : IsSmoothPrincipalPair f φ) {x : logForms k f T}
    (hx : d k (logResidue T h x) = 0) : ∃ ω, ofRegular k f T ω = logD k f T x :=
  (logResidue_eq_zero_iff h).1 (by rw [logResidue_logD, hx, neg_zero])

variable {T} in
/-- The regular form that is the differential of a logarithmic form is closed. This uses the
injectivity of regular forms into logarithmic forms.

Blueprint: `def:dr-gysin`. -/
theorem d_eq_zero_of_ofRegular_eq_logD (h : IsSmoothPrincipalPair f φ) {x : logForms k f T}
    {ω : Forms k A} (hω : ofRegular k f T ω = logD k f T x) : d k ω = 0 :=
  IsSmoothPrincipalPair.ofRegular_injective T h (by
    rw [← logD_ofRegular, hω, logD_logD, map_zero])

variable {T} in
/-- The class `[dλ]` depends only on the residue of `λ`: another lift changes `λ` by a regular form,
and so changes `dλ` by a regular boundary.

Blueprint: the proof of `def:dr-gysin`. -/
theorem mk_eq_mk_of_logResidue_eq (h : IsSmoothPrincipalPair f φ)
    {x x' : logForms k f T} (hres : logResidue T h x = logResidue T h x') {ω ω' : Forms k A}
    (hω : ofRegular k f T ω = logD k f T x) (hω' : ofRegular k f T ω' = logD k f T x') :
    Cohomology.mk ω (d_eq_zero_of_ofRegular_eq_logD h hω) =
      Cohomology.mk ω' (d_eq_zero_of_ofRegular_eq_logD h hω') := by
  obtain ⟨ξ, hξ⟩ := (logResidue_eq_zero_iff h (x := x - x')).1 (by rw [map_sub, hres, sub_self])
  refine Cohomology.mk_eq_mk_iff.2 ⟨ξ, IsSmoothPrincipalPair.ofRegular_injective T h ?_⟩
  rw [← logD_ofRegular, hξ, map_sub, map_sub, hω, hω']

variable {T} in
/-- The representatives of `G[γ]`: every closed form `γ` is the residue of a logarithmic form `x`,
whose differential is a regular form `ω`.

Blueprint: `def:dr-gysin`. -/
theorem exists_gysin_representative (h : IsSmoothPrincipalPair f φ) (γ : cycles k S) :
    ∃ (x : logForms k f T) (ω : Forms k A),
      logResidue T h x = γ ∧ ofRegular k f T ω = logD k f T x := by
  obtain ⟨x, hx⟩ := logResidue_surjective (T := T) h (γ : Forms k S)
  obtain ⟨ω, hω⟩ := exists_ofRegular_eq_logD h (hx ▸ mem_cycles.1 γ.2)
  exact ⟨x, ω, hx, hω⟩

/-- The function underlying the Gysin map on closed forms, by a choice of representative. Use
`gysin_mk_of_logResidue_eq`, which says that the choice does not matter. -/
@[no_expose] def gysinCyclesFun (h : IsSmoothPrincipalPair f φ) (γ : cycles k S) : Cohomology k A :=
  Cohomology.mk (exists_gysin_representative (T := T) h γ).choose_spec.choose
    (d_eq_zero_of_ofRegular_eq_logD h
      (exists_gysin_representative (T := T) h γ).choose_spec.choose_spec.2)

variable {T} in
/-- The value of `gysinCyclesFun` does not depend on the representative. -/
theorem gysinCyclesFun_eq (h : IsSmoothPrincipalPair f φ) (γ : cycles k S) {x : logForms k f T}
    (hx : logResidue T h x = γ) {ω : Forms k A} (hω : ofRegular k f T ω = logD k f T x) :
    gysinCyclesFun T h γ = Cohomology.mk ω (d_eq_zero_of_ofRegular_eq_logD h hω) :=
  have hc := (exists_gysin_representative (T := T) h γ).choose_spec.choose_spec
  mk_eq_mk_of_logResidue_eq h (hc.1.trans hx.symm) hc.2 hω

/-- The Gysin map on closed forms, as a `k`-linear map. -/
@[no_expose] def gysinCycles (h : IsSmoothPrincipalPair f φ) : cycles k S →ₗ[k] Cohomology k A where
  toFun := gysinCyclesFun T h
  map_add' γ γ' := by
    obtain ⟨x, ω, hx, hω⟩ := exists_gysin_representative (T := T) h γ
    obtain ⟨x', ω', hx', hω'⟩ := exists_gysin_representative (T := T) h γ'
    rw [gysinCyclesFun_eq h γ hx hω, gysinCyclesFun_eq h γ' hx' hω',
      gysinCyclesFun_eq h (γ + γ') (x := x + x') (ω := ω + ω')
        (by rw [map_add, hx, hx', Subalgebra.coe_add]) (by rw [map_add, map_add, hω, hω']),
      Cohomology.mk_add]
  map_smul' c γ := by
    obtain ⟨x, ω, hx, hω⟩ := exists_gysin_representative (T := T) h γ
    rw [RingHom.id_apply, gysinCyclesFun_eq h γ hx hω,
      gysinCyclesFun_eq h (c • γ) (x := c • x) (ω := c • ω)
        (by
          have := map_smul (logResidueₗ T h) c x
          rw [logResidueₗ_apply, logResidueₗ_apply, hx] at this
          exact this)
        (by rw [ofRegular_smul, hω, map_smul]),
      Cohomology.mk_smul]

/-- The Gysin map `G : H^•(S) → H^•(A)`, by the blueprint's convention `G[γ] = [dλ]` for `ρ λ = γ`,
with `dλ` viewed as a regular form. This is `gysin_mk_of_logResidue_eq`. It raises degrees by two,
by `isHomogeneousOfShift_gysin`. It is defined by this formula, and not through a library connecting
map, so there is no sign to reconcile.

Blueprint: `def:dr-gysin`. -/
@[no_expose] def gysin (h : IsSmoothPrincipalPair f φ) : Cohomology k S →ₗ[k] Cohomology k A :=
  Cohomology.liftLinear (gysinCycles T h) fun y => by
    obtain ⟨μ, hμ⟩ := logResidue_surjective (T := T) h y
    refine (gysinCyclesFun_eq (T := T) h ⟨d k y, d_d k y⟩ (x := -logD k f T μ) (ω := 0) ?_ ?_).trans
      (Cohomology.mk_zero _)
    · rw [map_neg, logResidue_logD, neg_neg, hμ]
    · rw [map_zero, map_neg, logD_logD, neg_zero]

variable {T}

/-- The defining formula `G[γ] = [dλ]`, for any `λ` with `ρ λ = γ`, with `dλ` the image of the
regular form `ω`.

Blueprint: `def:dr-gysin`. -/
theorem gysin_mk_of_logResidue_eq (h : IsSmoothPrincipalPair f φ) {γ : Forms k S}
    (hγ : d k γ = 0) {x : logForms k f T} (hx : logResidue T h x = γ) {ω : Forms k A}
    (hω : ofRegular k f T ω = logD k f T x) :
    gysin T h (Cohomology.mk γ hγ) = Cohomology.mk ω (d_eq_zero_of_ofRegular_eq_logD h hω) :=
  gysinCyclesFun_eq h ⟨γ, hγ⟩ hx hω

/-! ### The explicit formula -/

/-- The form `-θ ∧ dη` is closed, when it is regular. -/
theorem d_eq_zero_of_map_eq_neg_theta_mul (h : IsSmoothPrincipalPair f φ) {η ω : Forms k A}
    (hω : reg ω = -(θ * reg (d k η))) : d k ω = 0 :=
  h.map_injective T (by
    rw [Forms.map_d, hω, map_zero, map_neg, d_theta_mul, Forms.map_d, d_d, mul_zero, neg_zero,
      neg_zero])

variable (T) in
/-- For a lift `η` of a closed form, the form `-θ ∧ dη` is regular: `(dη)|_S = d(η|_S) = 0`, so
`lem:dr-regularity` applies.

Blueprint: `lem:dr-exactness`, "the expression inside the last brackets is regular". -/
theorem exists_map_eq_neg_theta_mul (h : IsSmoothPrincipalPair f φ) {η : Forms k A}
    (hη : d k (Forms.map φ η) = 0) : ∃ ω, reg ω = -(θ * reg (d k η)) := by
  obtain ⟨ω, hω⟩ := (h.exists_map_eq_theta_mul_map_iff T (η := d k η)).2
    (by rw [Forms.map_d, hη])
  exact ⟨-ω, by rw [map_neg, hω]⟩

variable (T) in
/-- For a lift `η` of degree `q` of a closed form, the form `-θ ∧ dη` is regular of degree `q + 2`.

Blueprint: `lem:dr-exactness`, "the expression inside the last brackets is regular". -/
theorem exists_mem_exteriorPower_map_eq_neg_theta_mul (h : IsSmoothPrincipalPair f φ) {q : ℕ}
    {η : Forms k A} (hηq : η ∈ ⋀[A]^q Ω[A⁄k]) (hη : d k (Forms.map φ η) = 0) :
    ∃ ω ∈ ⋀[A]^(q + 2) Ω[A⁄k], reg ω = -(θ * reg (d k η)) := by
  have hmem := (h.theta_mul_map_mem_regularPower_iff T (d_mem_exteriorPower k hηq)).2
    (by rw [Forms.map_d, hη])
  obtain ⟨ω, hωq, hω⟩ := mem_regularPower.1 hmem
  exact ⟨-ω, neg_mem hωq, by rw [map_neg, hω]⟩

/-- The explicit formula `G[γ] = [-θ ∧ dη]`, for a regular lift `η` of `γ`, with the form in
brackets the image of the regular form `ω`, which exists by `exists_map_eq_neg_theta_mul`. The sign
comes from `d(θ ∧ η) = -θ ∧ dη`, and there is no further factor of `(-1)^q`.

Blueprint: `lem:dr-exactness`. -/
theorem gysin_mk_of_map_eq (h : IsSmoothPrincipalPair f φ) {γ : Forms k S} (hγ : d k γ = 0)
    {η : Forms k A} (hη : Forms.map φ η = γ) {ω : Forms k A} (hω : reg ω = -(θ * reg (d k η))) :
    gysin T h (Cohomology.mk γ hγ) = Cohomology.mk ω (d_eq_zero_of_map_eq_neg_theta_mul h hω) :=
  gysin_mk_of_logResidue_eq h hγ (x := logMk k f T (0, η)) (by rw [logResidue_logMk, hη])
    (Subtype.ext (by
      rw [coe_ofRegular, coe_logD, coe_logMk, d_add_theta_mul, map_zero, map_zero, zero_sub, hω]))

/-- If `dη = f y + df ∧ z`, then `-df ∧ y` is closed. It is `-θ ∧ dη`. -/
theorem d_neg_diff_mul_eq_zero (h : IsSmoothPrincipalPair f φ) {η y z : Forms k A}
    (hd : f • y + diff k f * z = d k η) : d k (-(diff k f * y)) = 0 :=
  d_eq_zero_of_map_eq_neg_theta_mul (T := Localization.Away f) h (η := η)
    (by rw [map_neg, theta_mul_map_of_eq _ hd])

/-- The explicit formula without `T`: if `η` lifts `γ` and `dη = f y + df ∧ z`, as it may be written
by `lem:dr-quotient`, then `G[γ] = [-df ∧ y]`.

Blueprint: `lem:dr-exactness`, using the proof of `lem:dr-regularity`. -/
theorem gysin_mk_of_d_eq (h : IsSmoothPrincipalPair f φ) {γ : Forms k S} (hγ : d k γ = 0)
    {η : Forms k A} (hη : Forms.map φ η = γ) {y z : Forms k A}
    (hd : f • y + diff k f * z = d k η) :
    gysin T h (Cohomology.mk γ hγ) =
      Cohomology.mk (-(diff k f * y)) (d_neg_diff_mul_eq_zero h hd) :=
  gysin_mk_of_map_eq h hγ hη (by rw [map_neg, theta_mul_map_of_eq T hd])

variable (T) in
/-- The Gysin map raises degrees by two.

Blueprint: `def:dr-gysin`, `lem:dr-exactness`. -/
theorem gysin_mem_degree (h : IsSmoothPrincipalPair f φ) {q : ℕ} {c : Cohomology k S}
    (hc : c ∈ Cohomology.degree k S q) : gysin T h c ∈ Cohomology.degree k A (q + 2) := by
  obtain ⟨γ, hγ, hγq, rfl⟩ := Cohomology.mem_degree_iff.1 hc
  obtain ⟨η, hη⟩ := Forms.mapPower_surjective h.surjective q ⟨γ, hγq⟩
  have hη' : Forms.map φ (η : Forms k A) = γ := congrArg Subtype.val hη
  obtain ⟨ω, hωq, hω⟩ := exists_mem_exteriorPower_map_eq_neg_theta_mul T h η.2 (hη' ▸ hγ)
  rw [gysin_mk_of_map_eq h hγ hη' hω]
  exact Cohomology.mk_mem_degree hωq _

variable (T) in
/-- The Gysin map has shift `2`: it sends `H^p(S)` to `H^(p+2)(A)`, for every integer `p`.

Blueprint: `lem:dr-exactness`, the degrees. -/
theorem isHomogeneousOfShift_gysin (h : IsSmoothPrincipalPair f φ) :
    IsHomogeneousOfShift (Cohomology.grading k S) (Cohomology.grading k A) 2 (gysin T h) := by
  intro p c hc
  obtain hp | hp := lt_or_ge p 0
  · rw [Cohomology.eq_zero_of_mem_grading_of_neg hp hc, map_zero]
    exact zero_mem _
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [Cohomology.grading_natCast] at hc
  have := gysin_mem_degree T h hc
  rw [← Cohomology.grading_natCast] at this
  exact_mod_cast this

/-! ### Exactness -/

variable (T) in
/-- Exactness at `H^n(A)`: a class on `A` vanishes in `H^n(L)` exactly when it is a Gysin class. If
`ω = dλ` is regular then `ρ λ` is closed, and it maps to `[ω]`.

Blueprint: `lem:dr-exactness`, on the logarithmic side. -/
theorem exact_gysin_ofCohomology (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (gysin T h) (LogCohomology.ofCohomology k f T) := by
  intro c
  constructor
  · induction c with
    | mk ω hω =>
      rw [LogCohomology.ofCohomology_mk, LogCohomology.mk_eq_zero_iff]
      rintro ⟨y, hy⟩
      have hγ : d k (logResidue T h y) = 0 := by
        have := logResidue_logD h y
        rwa [hy, logResidue_ofRegular, eq_comm, neg_eq_zero] at this
      exact ⟨Cohomology.mk _ hγ, gysin_mk_of_logResidue_eq h hγ rfl hy.symm⟩
  · rintro ⟨c, rfl⟩
    induction c with
    | mk γ hγ =>
      obtain ⟨x, ω, hx, hω⟩ := exists_gysin_representative (T := T) h ⟨γ, hγ⟩
      rw [gysin_mk_of_logResidue_eq h hγ hx hω, LogCohomology.ofCohomology_mk]
      exact LogCohomology.mk_eq_zero_iff.2 ⟨x, hω.symm⟩

namespace LogCohomology

variable (T) in
/-- Exactness at `H^n(L)`: a closed logarithmic form has exact residue exactly when it is
cohomologous, in `L`, to a closed regular form. If `ρ x = d y`, lift `y` to `μ`, and then `x + dμ`
has zero residue.

Blueprint: `lem:dr-exactness`, on the logarithmic side. -/
theorem exact_ofCohomology_residue (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (ofCohomology k f T) (residue T h) := by
  intro c
  constructor
  · induction c with
    | mk x hx =>
      rw [residue_mk, Cohomology.mk_eq_zero_iff]
      rintro ⟨y, hy⟩
      obtain ⟨μ, hμ⟩ := logResidue_surjective (T := T) h y
      obtain ⟨ω, hω⟩ := (logResidue_eq_zero_iff h (x := x + logD k f T μ)).1
        (by rw [map_add, logResidue_logD, hμ, hy, add_neg_cancel])
      have hc : d k ω = 0 := IsSmoothPrincipalPair.ofRegular_injective T h (by
        rw [← logD_ofRegular, hω, map_add, hx, logD_logD, add_zero, map_zero])
      refine ⟨Cohomology.mk ω hc, ?_⟩
      rw [ofCohomology_mk]
      exact mk_eq_mk_iff.2 ⟨μ, by rw [hω, add_sub_cancel_left]⟩
  · rintro ⟨c, rfl⟩
    exact residue_ofCohomology h c

variable (T) in
/-- Exactness at `H^(n-1)(S)`: a class on `S` has zero Gysin image exactly when it is a residue. If
`dλ = ω = dξ` for regular `ξ`, then `λ - ξ` is closed with the same residue.

Blueprint: `lem:dr-exactness`, on the logarithmic side. -/
theorem exact_residue_gysin (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (residue T h) (gysin T h) := by
  intro c
  constructor
  · induction c with
    | mk γ hγ =>
      obtain ⟨x, ω, hx, hω⟩ := exists_gysin_representative (T := T) h ⟨γ, hγ⟩
      rw [gysin_mk_of_logResidue_eq h hγ hx hω, Cohomology.mk_eq_zero_iff]
      rintro ⟨ξ, rfl⟩
      have hd : logD k f T (x - ofRegular k f T ξ) = 0 := by
        rw [map_sub, logD_ofRegular, hω, sub_self]
      refine ⟨mk _ hd, ?_⟩
      rw [residue_mk]
      exact Cohomology.mk_congr (by rw [map_sub, logResidue_ofRegular, sub_zero, hx]) _
  · rintro ⟨c, rfl⟩
    induction c with
    | mk x hx =>
      rw [residue_mk]
      refine (gysin_mk_of_logResidue_eq h _ rfl (ω := 0) ?_).trans (Cohomology.mk_zero _)
      rw [map_zero, hx]

end LogCohomology

end OrlikSolomon.DeRham
