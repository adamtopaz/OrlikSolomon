/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Log.Basic
public import OrlikSolomon.DeRham.PrincipalQuotient
public import OrlikSolomon.DeRham.SmoothPair.Koszul
public import OrlikSolomon.DeRham.SmoothPair.Projective

/-!
# The residue of a logarithmic form

For a smooth principal pair, consisting of a non-zero-divisor `f` of `A` with `A` and `S` formally
smooth, where `φ : A → S` is a surjection with kernel `(f)`, and for `T` a localization of `A` away
from `f`, the form `θ ∧ η` on `T` is regular exactly when `η` restricts to zero on `S`. So
`ρ(ω + θ ∧ η) = η|_S` is well defined, and it is the residue of logarithmic forms. Regular forms are
its kernel, it is surjective, it anticommutes with `d`, and `ρ(α ∧ β) = ρ(α) ∧ β|_S`.

Everything holds for a unit `f`, whose divisor is empty, for the zero ring, and for an `A` that is
not connected.

## Main definitions

* `OrlikSolomon.DeRham.IsSmoothPrincipalPair f φ`: the hypotheses on `f` and `φ`.
* `OrlikSolomon.DeRham.logResidue T h`: the residue `ρ` on all logarithmic forms, semilinear over
  `φ`.
* `OrlikSolomon.DeRham.logResidueₗ T h`: the same map, as a `k`-linear map.
* `OrlikSolomon.DeRham.logPowerResidue T h n`: the residue in degree `n + 1`, as a `k`-linear map
  `L^(n+1) → Ω_S^n`.

## Main results

* `OrlikSolomon.DeRham.IsSmoothPrincipalPair.map_injective`: regular forms inject into forms on `T`,
  so identifying them with their images is harmless. This is `lem:dr-projective` in total degree.
* `OrlikSolomon.DeRham.Forms.map_eq_zero_of_diff_mul_eq_smul`: `lem:dr-modf-koszul` in total degree,
  for any surjection with kernel `(f)`.

Blueprint `lem:dr-regularity`:

* `OrlikSolomon.DeRham.IsSmoothPrincipalPair.exists_map_eq_theta_mul_map_iff`, in total degree.
* `OrlikSolomon.DeRham.IsSmoothPrincipalPair.theta_mul_map_mem_regularPower_iff`, in each degree.

Blueprint `def:dr-residue`: `OrlikSolomon.DeRham.logResidue_logMk`,
`OrlikSolomon.DeRham.logResidue_eq_of_coe_eq` and `OrlikSolomon.DeRham.logResidue_smul`.

Blueprint `thm:dr-residue-sequence`, on elements. `DeRham/Log` packages these as a short exact
sequence of complexes.

* `OrlikSolomon.DeRham.logResidue_logD`: `ρ d = -d ρ`.
* `OrlikSolomon.DeRham.IsSmoothPrincipalPair.ofRegular_injective`,
  `OrlikSolomon.DeRham.exact_ofRegular_logResidue` and
  `OrlikSolomon.DeRham.logResidue_surjective`: exactness in total degree.
* `OrlikSolomon.DeRham.powerToLog_injective`, `OrlikSolomon.DeRham.exact_powerToLog_logPowerResidue`
  and `OrlikSolomon.DeRham.logPowerResidue_surjective`: exactness in each degree.
* `OrlikSolomon.DeRham.logPowerResidue_logPowerD`: `ρ d = -d ρ`, with types indexed by degree.

Blueprint `lem:dr-form-projection`: `OrlikSolomon.DeRham.logResidue_mul_ofRegular`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open CliffordAlgebra (involute)
open KaehlerDifferential (D)

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}

/-- If `df ∧ η = f ω`, then `η` restricts to zero on `S`. This is `lem:dr-modf-koszul`, in total
degree and for any surjection with kernel `(f)`. The smoothness of `A` plays no role.

Blueprint: `lem:dr-modf-koszul`. -/
theorem Forms.map_eq_zero_of_diff_mul_eq_smul [Algebra.FormallySmooth k S]
    (hf : f ∈ nonZeroDivisors A) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {f}) {η ω : Forms k A} (hη : diff k f * η = f • ω) :
    Forms.map φ η = 0 := by
  let e : (A ⧸ Ideal.span {f}) ≃ₐ[k] S :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hφ)
  have : Algebra.FormallySmooth k (A ⧸ Ideal.span {f}) := .of_equiv e.symm
  have he : e.toAlgHom.comp (IsScalarTower.toAlgHom k A (A ⧸ Ideal.span {f})) = φ :=
    AlgHom.ext fun a => Ideal.quotientKerAlgEquivOfSurjective_mk hφ a
  refine eq_of_forall_exteriorProj_eq fun n => Subtype.ext ?_
  have hw : wedgeLeft (D k A f) n (exteriorProj n η) = f • exteriorProj (n + 1) ω := by
    rw [← exteriorProj_ι_mul, ι_D, hη, _root_.map_smul]
  have hK := congrArg Subtype.val <| powerMap_eq_zero_of_wedgeLeft_df_eq_smul f hf
    (exteriorProj n η) (exteriorProj (n + 1) ω) hw
  rw [coe_powerMap, ← Forms.map_toAlgHom] at hK
  rw [Forms.coe_exteriorProj_map, map_zero, ← he, ← Forms.map_map, hK]
  simp

/-- The hypotheses of a smooth principal pair, for a surjection `φ : A → S`, so that they apply to a
divisor pair and not only to `A ⧸ (f)`: `f` is a non-zero-divisor, `φ` is surjective with kernel
`(f)`, and `A` and `S` are formally smooth. No connectedness or nonzero-ring assumption is made, and
`f` may be a unit. `IsSmoothPrincipalPair.of_quotient` is the case of the literal quotient, and
`DivisorPair.isSmoothPrincipalPair` is the case of a divisor pair.

Blueprint: the section "The algebra of a smooth principal pair". -/
structure IsSmoothPrincipalPair (f : A) (φ : A →ₐ[k] S) : Prop where
  /-- The equation is a non-zero-divisor. -/
  mem_nonZeroDivisors : f ∈ nonZeroDivisors A
  /-- The map to the closed part is surjective. -/
  surjective : Function.Surjective φ
  /-- The kernel of the map to the closed part is generated by the equation. -/
  ker_eq : RingHom.ker φ = Ideal.span {f}
  /-- The ambient algebra is formally smooth. -/
  formallySmooth_ambient : Algebra.FormallySmooth k A
  /-- The closed part is formally smooth. -/
  formallySmooth_closed : Algebra.FormallySmooth k S

/-- The literal quotient `A ⧸ (f)` by a non-zero-divisor is a smooth principal pair. -/
theorem IsSmoothPrincipalPair.of_quotient [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.span {f})] (hf : f ∈ nonZeroDivisors A) :
    IsSmoothPrincipalPair f (Ideal.Quotient.mkₐ k (Ideal.span {f})) where
  mem_nonZeroDivisors := hf
  surjective := Ideal.Quotient.mkₐ_surjective k _
  ker_eq := Ideal.Quotient.mkₐ_ker k _
  formallySmooth_ambient := inferInstance
  formallySmooth_closed := inferInstance

namespace IsSmoothPrincipalPair

/-- If `df ∧ η = f ω`, then `η` restricts to zero on `S`.

Blueprint: `lem:dr-modf-koszul`. -/
theorem map_eq_zero_of_diff_mul_eq_smul (h : IsSmoothPrincipalPair f φ) {η ω : Forms k A}
    (hη : diff k f * η = f • ω) : Forms.map φ η = 0 :=
  have := h.formallySmooth_closed
  Forms.map_eq_zero_of_diff_mul_eq_smul h.mem_nonZeroDivisors h.surjective h.ker_eq hη

/-- Multiplication by `f` is injective on all forms.

Blueprint: `lem:dr-projective`, in total degree. -/
theorem isSMulRegular_forms (h : IsSmoothPrincipalPair f φ) : IsSMulRegular (Forms k A) f := by
  have := h.formallySmooth_ambient
  intro x y hxy
  refine eq_of_forall_exteriorProj_eq fun n => DeRham.isSMulRegular_forms h.mem_nonZeroDivisors n ?_
  have := congrArg (exteriorProj n) hxy
  simpa only [_root_.map_smul] using this

/-- Regular forms inject into forms on the localization, in total degree. So the blueprint's
identification of regular forms with their images is harmless.

Blueprint: `lem:dr-projective`, in total degree. -/
theorem map_injective (h : IsSmoothPrincipalPair f φ) (T : Type*) [CommRing T] [Algebra k T]
    [Algebra A T] [IsScalarTower k A T] [IsLocalization.Away f T] :
    Function.Injective (Forms.map (IsScalarTower.toAlgHom k A T)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨m, hm⟩ := (Forms.map_eq_zero_iff_of_isLocalizationAway f).1 hx
  exact (h.isSMulRegular_forms.pow m) (by simpa only [smul_zero] using hm)

end IsSmoothPrincipalPair

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

/-! ### Regularity -/

/-- If `η = f y + df ∧ z` then `θ ∧ η = df ∧ y`, which is regular. This needs no hypothesis on `f`.

Blueprint: the proof of `lem:dr-regularity`. -/
theorem theta_mul_map_of_eq {y z η : Forms k A} (hη : f • y + diff k f * z = η) :
    θ * reg η = reg (diff k f * y) := by
  subst hη
  rw [map_add, map_mul, map_mul, Forms.map_toAlgHom_smul, ← self_smul_theta k f T, mul_add,
    mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← mul_assoc, theta_mul_self,
    zero_mul, smul_zero, add_zero]

namespace IsSmoothPrincipalPair

variable {T}

/-- A form that restricts to zero on `S` is `f y + df ∧ z`, with `y` of the same degree. -/
private theorem exists_smul_add_diff_mul_eq (h : IsSmoothPrincipalPair f φ) {n : ℕ} {η : Forms k A}
    (hη : η ∈ ⋀[A]^n Ω[A⁄k]) (h0 : Forms.map φ η = 0) :
    ∃ y ∈ ⋀[A]^n Ω[A⁄k], ∃ z, f • y + diff k f * z = η := by
  cases n with
  | zero =>
    obtain ⟨y, hy⟩ := (Forms.mapPower_zero_eq_zero_iff_of_ker_eq_span_singleton h.surjective
      h.ker_eq (x := ⟨η, hη⟩)).1 (Subtype.ext h0)
    exact ⟨y, y.2, 0, by simpa using congrArg Subtype.val hy⟩
  | succ n =>
    obtain ⟨y, z, hyz⟩ := (Forms.mapPower_succ_eq_zero_iff_of_ker_eq_span_singleton h.surjective
      h.ker_eq (x := ⟨η, hη⟩)).1 (Subtype.ext h0)
    exact ⟨y, y.2, z, congrArg Subtype.val hyz⟩

variable (T) in
/-- The form `θ ∧ η` is regular exactly when `η` restricts to zero on `S`, in total degree. This
needs the smoothness of `S`, through `lem:dr-modf-koszul`, and it fails for a crossing divisor, by
`prop:dr-crossing-example`.

Blueprint: `lem:dr-regularity`. -/
theorem exists_map_eq_theta_mul_map_iff (h : IsSmoothPrincipalPair f φ) {η : Forms k A} :
    (∃ ω : Forms k A, reg ω = θ * reg η) ↔ Forms.map φ η = 0 := by
  constructor
  · rintro ⟨ω, hω⟩
    refine h.map_eq_zero_of_diff_mul_eq_smul (ω := ω) (h.map_injective T ?_)
    rw [map_mul, Forms.map_toAlgHom_smul, hω, ← self_smul_theta k f T, smul_mul_assoc]
  · intro h0
    obtain ⟨y, z, hyz⟩ :=
      (Forms.map_eq_zero_iff_of_ker_eq_span_singleton h.surjective h.ker_eq).1 h0
    exact ⟨_, (theta_mul_map_of_eq T hyz).symm⟩

variable (T) in
/-- For `η` of degree `n`, the form `θ ∧ η` is regular of degree `n + 1` exactly when `η` restricts
to zero on `S`.

Blueprint: `lem:dr-regularity`. -/
theorem theta_mul_map_mem_regularPower_iff (h : IsSmoothPrincipalPair f φ) {n : ℕ} {η : Forms k A}
    (hη : η ∈ ⋀[A]^n Ω[A⁄k]) :
    θ * reg η ∈ regularPower k A T (n + 1) ↔ Forms.map φ η = 0 := by
  constructor
  · intro hx
    obtain ⟨ω, -, hω⟩ := mem_regularPower.1 hx
    exact (h.exists_map_eq_theta_mul_map_iff T).1 ⟨ω, hω⟩
  · intro h0
    obtain ⟨y, hy, z, hyz⟩ := h.exists_smul_add_diff_mul_eq hη h0
    rw [theta_mul_map_of_eq T hyz]
    exact map_mem_regularPower k T (diff_mul_mem_exteriorPower k f hy)

variable (T) in
/-- The kernel of `(ω, η) ↦ ω + θ ∧ η` lies in the kernel of `(ω, η) ↦ η|_S`, which says that `ρ` is
independent of the decomposition.

Blueprint: `def:dr-residue`. -/
theorem map_eq_zero_of_logMk_eq_zero (h : IsSmoothPrincipalPair f φ) {ω η : Forms k A}
    (hx : logMk k f T (ω, η) = 0) : Forms.map φ η = 0 := by
  refine (h.exists_map_eq_theta_mul_map_iff T).1 ⟨-ω, ?_⟩
  have := congrArg (Subtype.val : logForms k f T → Forms k T) hx
  rw [coe_logMk, Subalgebra.coe_zero, add_comm, add_eq_zero_iff_eq_neg] at this
  rw [map_neg, this]

end IsSmoothPrincipalPair

/-! ### The residue -/

/-- The residue `ρ` of logarithmic forms, characterized by `ρ(ω + θ ∧ η) = η|_S`, which is
`logResidue_logMk`. It is independent of the decomposition, by `lem:dr-regularity`, and semilinear
over `φ`, which is the blueprint's `A`-linearity with `A` acting on the target through `S`. It
lowers degrees by one, by `logResidue_mem_exteriorPower`. `logResidueₗ` is the same map, as a
`k`-linear map.

Blueprint: `def:dr-residue`. -/
@[no_expose] noncomputable def logResidue (h : IsSmoothPrincipalPair f φ) :
    logForms k f T →ₛₗ[(φ : A →+* S)] Forms k S :=
  (LinearMap.ker (logMk k f T)).liftQ
      (Forms.mapₛₗ φ ∘ₛₗ LinearMap.snd A (Forms k A) (Forms k A))
      (fun p hp => h.map_eq_zero_of_logMk_eq_zero T (ω := p.1) (η := p.2) hp) ∘ₛₗ
    ((logMk k f T).quotKerEquivOfSurjective (logMk_surjective k f T)).symm.toLinearMap

variable {T}

/-- The formula `ρ(ω + θ ∧ η) = η|_S`, for `logMk`.

Blueprint: `def:dr-residue`. -/
@[simp]
theorem logResidue_logMk (h : IsSmoothPrincipalPair f φ) (p : Forms k A × Forms k A) :
    logResidue T h (logMk k f T p) = Forms.map φ p.2 := by
  simp only [logResidue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The formula `ρ(ω + θ ∧ η) = η|_S`, for any decomposition of a logarithmic form.

Blueprint: `def:dr-residue`. -/
theorem logResidue_eq_of_coe_eq (h : IsSmoothPrincipalPair f φ) {x : logForms k f T}
    {ω η : Forms k A} (hx : (x : Forms k T) = reg ω + θ * reg η) :
    logResidue T h x = Forms.map φ η := by
  have : x = logMk k f T (ω, η) := Subtype.ext hx
  rw [this, logResidue_logMk]

/-- Regular forms have zero residue. -/
@[simp]
theorem logResidue_ofRegular (h : IsSmoothPrincipalPair f φ) (ω : Forms k A) :
    logResidue T h (ofRegular k f T ω) = 0 := by
  rw [← logMk_mk_zero, logResidue_logMk, map_zero]

/-- `ρ θ = 1`. -/
@[simp]
theorem logResidue_theta (h : IsSmoothPrincipalPair f φ) :
    logResidue T h ⟨θ, theta_mem_logForms k f T⟩ = 1 := by
  rw [logResidue_eq_of_coe_eq h (ω := 0) (η := 1) (by simp), map_one]

/-- The residue is `A`-linear, with `A` acting on the target through `S`.

Blueprint: `def:dr-residue`. -/
theorem logResidue_smul (h : IsSmoothPrincipalPair f φ) (a : A) (x : logForms k f T) :
    logResidue T h (a • x) = φ a • logResidue T h x :=
  map_smulₛₗ (logResidue T h) a x

/-- The residue, as a `k`-linear map. Its underlying function is `logResidue`.

Blueprint: `def:dr-residue`. -/
noncomputable def logResidueₗ (h : IsSmoothPrincipalPair f φ) : logForms k f T →ₗ[k] Forms k S where
  toFun := logResidue T h
  map_add' := map_add _
  map_smul' c x := by
    rw [← algebraMap_smul A c x, logResidue_smul, RingHom.id_apply, AlgHom.commutes,
      algebraMap_smul]

@[simp]
theorem logResidueₗ_apply (h : IsSmoothPrincipalPair f φ) (x : logForms k f T) :
    logResidueₗ h x = logResidue T h x :=
  rfl

/-- The residue anticommutes with the differential: `ρ d = -d ρ`. This is the chain map condition
for the differential `-d` on the target `Ω_S^•[-1]`.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logResidue_logD (h : IsSmoothPrincipalPair f φ) (x : logForms k f T) :
    logResidue T h (logD k f T x) = -d k (logResidue T h x) := by
  obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x
  rw [logD_logMk, logResidue_logMk, logResidue_logMk, map_neg, Forms.map_d]

/-- The residue is surjective, with the explicit preimage `θ ∧ η` of `η|_S`.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logResidue_surjective (h : IsSmoothPrincipalPair f φ) :
    Function.Surjective (logResidue T h) := fun γ => by
  obtain ⟨η, rfl⟩ := Forms.map_surjective h.surjective γ
  exact ⟨logMk k f T (0, η), logResidue_logMk h _⟩

/-- A logarithmic form with zero residue is regular.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logResidue_eq_zero_iff (h : IsSmoothPrincipalPair f φ) {x : logForms k f T} :
    logResidue T h x = 0 ↔ ∃ ω, ofRegular k f T ω = x := by
  constructor
  · obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x
    rw [logResidue_logMk]
    intro h0
    obtain ⟨ω', hω'⟩ := (h.exists_map_eq_theta_mul_map_iff T).2 h0
    refine ⟨ω + ω', Subtype.ext ?_⟩
    rw [coe_ofRegular, coe_logMk, map_add, hω']
  · rintro ⟨ω, rfl⟩
    exact logResidue_ofRegular h ω

variable (T) in
/-- Exactness at logarithmic forms, in total degree.

Blueprint: `thm:dr-residue-sequence`. -/
theorem exact_ofRegular_logResidue (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (ofRegular k f T) (logResidue T h) := fun _ =>
  (logResidue_eq_zero_iff h).trans Set.mem_range.symm

variable (T) in
/-- The map from regular forms to logarithmic forms is injective.

Blueprint: `thm:dr-residue-sequence`. -/
theorem IsSmoothPrincipalPair.ofRegular_injective (h : IsSmoothPrincipalPair f φ) :
    Function.Injective (ofRegular k f T) := fun x y hxy =>
  h.map_injective T (by simpa using congrArg (Subtype.val : logForms k f T → Forms k T) hxy)

/-- The right projection formula `ρ(α ∧ β) = ρ(α) ∧ β|_S`, with no sign, since no factor moves
across `θ`. This fixes the convention needed by `residue_mul_map`.

Blueprint: `lem:dr-form-projection`. -/
theorem logResidue_mul_ofRegular (h : IsSmoothPrincipalPair f φ) (α : logForms k f T)
    (β : Forms k A) :
    logResidue T h (α * ofRegular k f T β) = logResidue T h α * Forms.map φ β := by
  obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T α
  rw [← logMk_mk_zero, logMk_mul_logMk, logResidue_logMk, logResidue_logMk, mul_zero, zero_add,
    map_mul]

/-- The left projection formula `ρ(β ∧ α) = σ(β|_S) ∧ ρ(α)`, with `σ` the grade involution, so the
sign is `(-1)^q` for `β` of degree `q`. The factor `β` moves across `θ`. -/
theorem logResidue_ofRegular_mul (h : IsSmoothPrincipalPair f φ) (β : Forms k A)
    (α : logForms k f T) :
    logResidue T h (ofRegular k f T β * α) =
      involute (Forms.map φ β) * logResidue T h α := by
  obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T α
  rw [← logMk_mk_zero, logMk_mul_logMk, logResidue_logMk, logResidue_logMk, zero_mul, add_zero,
    map_mul, Forms.map_involute]

/-! ### The residue in each degree -/

/-- The residue of a logarithmic form of degree `n + 1` has degree `n`.

Blueprint: `def:dr-residue`. -/
theorem logResidue_mem_exteriorPower (h : IsSmoothPrincipalPair f φ) {n : ℕ} {x : logForms k f T}
    (hx : (x : Forms k T) ∈ logPower k f T (n + 1)) : logResidue T h x ∈ ⋀[S]^n Ω[S⁄k] := by
  obtain ⟨ω, -, η, hη, hx⟩ := mem_logPower_succ.1 hx
  rw [logResidue_eq_of_coe_eq h hx.symm]
  exact Forms.map_mem_exteriorPower φ hη

/-- The residue vanishes in degree zero, since a logarithmic form of degree zero is regular.

Blueprint: `def:dr-residue`, the zero convention. -/
theorem logResidue_eq_zero_of_mem_logPower_zero (h : IsSmoothPrincipalPair f φ)
    {x : logForms k f T} (hx : (x : Forms k T) ∈ logPower k f T 0) : logResidue T h x = 0 := by
  obtain ⟨ω, -, hx⟩ := mem_logPower_zero.1 hx
  exact (logResidue_eq_zero_iff h).2 ⟨ω, Subtype.ext (by simpa using hx)⟩

variable (T) in
/-- The residue in degree `n + 1`, as a `k`-linear map `L^(n+1) → Ω_S^n`. This is `logResidue` with
its domain and codomain restricted, by `coe_logPowerResidue`. It is semilinear over `φ`, by
`logPowerResidue_smul`.

Blueprint: `def:dr-residue`. -/
noncomputable def logPowerResidue (h : IsSmoothPrincipalPair f φ) (n : ℕ) :
    logPower k f T (n + 1) →ₗ[k] ⋀[S]^n Ω[S⁄k] :=
  LinearMap.codRestrict ((⋀[S]^n Ω[S⁄k]).restrictScalars k)
    ((logResidueₗ h).comp ((logPowerToLogForms k f T (n + 1)).restrictScalars k))
    fun x => logResidue_mem_exteriorPower h x.2

@[simp]
theorem coe_logPowerResidue (h : IsSmoothPrincipalPair f φ) (n : ℕ) (x : logPower k f T (n + 1)) :
    (logPowerResidue T h n x : Forms k S) =
      logResidue T h (logPowerToLogForms k f T (n + 1) x) :=
  rfl

/-- The residue in each degree is `A`-linear, with `A` acting on the target through `S`.

Blueprint: `def:dr-residue`. -/
@[simp]
theorem logPowerResidue_smul (h : IsSmoothPrincipalPair f φ) (n : ℕ) (a : A)
    (x : logPower k f T (n + 1)) :
    logPowerResidue T h n (a • x) = φ a • logPowerResidue T h n x :=
  Subtype.ext (logResidue_smul h a (logPowerToLogForms k f T (n + 1) x))

/-- The residue anticommutes with the differential, with types indexed by degree.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logPowerResidue_logPowerD (h : IsSmoothPrincipalPair f φ) (n : ℕ)
    (x : logPower k f T (n + 1)) :
    logPowerResidue T h (n + 1) (logPowerD k f T (n + 1) x) =
      -powerD k S n (logPowerResidue T h n x) :=
  Subtype.ext (logResidue_logD h (logPowerToLogForms k f T (n + 1) x))

/-- The residue of the differential of a logarithmic form of degree zero vanishes, since that form
is regular. This is the anticommutation in degree zero, where the target of the residue is zero.

Blueprint: `thm:dr-residue-sequence`. -/
@[simp]
theorem logPowerResidue_logPowerD_zero (h : IsSmoothPrincipalPair f φ) (x : logPower k f T 0) :
    logPowerResidue T h 0 (logPowerD k f T 0 x) = 0 :=
  Subtype.ext (by
    rw [coe_logPowerResidue, ZeroMemClass.coe_zero]
    have hx := (logResidue_eq_zero_of_mem_logPower_zero h (x := logPowerToLogForms k f T 0 x) x.2)
    have := logResidue_logD h (logPowerToLogForms k f T 0 x)
    rw [hx, map_zero, neg_zero] at this
    exact this)

variable (T) in
/-- The residue in each degree is surjective, with the explicit preimage `θ ∧ η` of `η|_S`.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logPowerResidue_surjective (h : IsSmoothPrincipalPair f φ) (n : ℕ) :
    Function.Surjective (logPowerResidue T h n) := fun γ => by
  obtain ⟨η, rfl⟩ := Forms.mapPower_surjective h.surjective n γ
  refine ⟨⟨θ * reg (η : Forms k A), theta_mul_map_mem_logPower k f T η.2⟩, Subtype.ext ?_⟩
  exact logResidue_eq_of_coe_eq h (ω := 0) (by simp)

/-- `Ω_A^n → L^n` is injective.

Blueprint: `thm:dr-residue-sequence`. -/
theorem powerToLog_injective (h : IsSmoothPrincipalPair f φ) (n : ℕ) :
    Function.Injective (powerToLog k f T n) := fun _ _ hxy =>
  Subtype.ext (h.map_injective T (congrArg (Subtype.val : logPower k f T n → Forms k T) hxy))

/-- A regular form has zero residue in each degree.

Blueprint: `thm:dr-residue-sequence`. -/
@[simp]
theorem logPowerResidue_powerToLog (h : IsSmoothPrincipalPair f φ) (n : ℕ)
    (x : ⋀[A]^(n + 1) Ω[A⁄k]) :
    logPowerResidue T h n (powerToLog k f T (n + 1) x) = 0 := by
  refine Subtype.ext ?_
  rw [coe_logPowerResidue, logPowerToLogForms_powerToLog, logResidue_ofRegular,
    ZeroMemClass.coe_zero]

variable (T) in
/-- Exactness at `L^(n+1)`: a logarithmic form of degree `n + 1` has zero residue exactly when it is
regular of degree `n + 1`. This is where degrees are tracked, since the regular form has to have the
right degree.

Blueprint: `thm:dr-residue-sequence`. -/
theorem exact_powerToLog_logPowerResidue (h : IsSmoothPrincipalPair f φ) (n : ℕ) :
    Function.Exact (powerToLog k f T (n + 1)) (logPowerResidue T h n) := by
  rintro ⟨x, hx⟩
  obtain ⟨ω, hω, η, hη, rfl⟩ := mem_logPower_succ.1 hx
  constructor
  · intro h0
    have h1 : Forms.map φ η = 0 := by
      rw [← logResidue_logMk (T := T) h (ω, η)]
      exact congrArg (Subtype.val : ⋀[S]^n Ω[S⁄k] → Forms k S) h0
    obtain ⟨ω', hω', hω''⟩ :=
      mem_regularPower.1 ((h.theta_mul_map_mem_regularPower_iff T hη).2 h1)
    exact ⟨⟨ω + ω', add_mem hω hω'⟩, Subtype.ext (by simp [hω''])⟩
  · rintro ⟨y, hy⟩
    rw [← hy, logPowerResidue_powerToLog]

end OrlikSolomon.DeRham
