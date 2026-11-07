/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Localization

/-!
# Logarithmic forms

Let `T` be a localization of a commutative `k`-algebra `A` away from an element `f`, in the sense of
`IsLocalization.Away`, so that this file applies to certified pairs. With `θ = df / f`, the
logarithmic forms are the forms `ω + θ ∧ η` on `T`, with `ω` and `η` forms on `A`. They are a
dg subalgebra of the forms on `T`, and `f L^•` is stable under `d`, even though `d` is not
`A`-linear.

Nothing in this file needs smoothness, or that `f` is a non-zero-divisor. Regular forms are not
identified with their images, as the blueprint does using `lem:dr-projective`: here a regular form
is written as its image in `T`, and `Forms.map (IsScalarTower.toAlgHom k A T)` is the map. The
element `f` may be a unit, and `A` may be the zero ring.

## Main definitions

* `OrlikSolomon.DeRham.theta k f T`: the form `θ = df / f`.
* `OrlikSolomon.DeRham.logForms k f T`: all logarithmic forms, an `A`-subalgebra of forms on `T`.
* `OrlikSolomon.DeRham.regularPower k A T n`: the image of `Ω_A^n` in forms on `T`.
* `OrlikSolomon.DeRham.logPower k f T n`: the module `L^n = Ω_A^n + θ ∧ Ω_A^(n-1)`.
* `OrlikSolomon.DeRham.logMk k f T`: the surjection `(ω, η) ↦ ω + θ ∧ η` onto logarithmic forms.
* `OrlikSolomon.DeRham.ofRegular k f T`: the map from forms on `A` to logarithmic forms.
* `OrlikSolomon.DeRham.logD k f T` and `OrlikSolomon.DeRham.logPowerD k f T n`: the differential.
* `OrlikSolomon.DeRham.logIdeal k f T` and `OrlikSolomon.DeRham.logQuotientD k f T`: the ideal
  `f L^•` and the induced differential on `L^• / f L^•`.

## Main results

Blueprint `def:dr-log`: `OrlikSolomon.DeRham.mem_logPower_zero` and
`OrlikSolomon.DeRham.mem_logPower_succ` are the definition in terms of elements.

Blueprint `lem:dr-log-dga`:

* `OrlikSolomon.DeRham.logForms` is a subalgebra, with `OrlikSolomon.DeRham.logMk_mul_logMk` for
  its product, and `logPower` is a grading of it, by `OrlikSolomon.DeRham.gradedMonoid_logPower`,
  `OrlikSolomon.DeRham.logPower_eq_inf` and `OrlikSolomon.DeRham.iSup_logPower`.
* `OrlikSolomon.DeRham.d_add_theta_mul`: `d(ω + θ ∧ η) = dω - θ ∧ dη`, with
  `OrlikSolomon.DeRham.d_mem_logForms` and `OrlikSolomon.DeRham.d_mem_logPower`.
* `OrlikSolomon.DeRham.d_self_smul`, `OrlikSolomon.DeRham.logD_mem_logIdeal` and
  `OrlikSolomon.DeRham.exists_d_self_smul_eq_of_mem_logPower`: `f L^•` is stable under `d`.

## Design

The total algebra is primary, as for forms. So a logarithmic form of degree `n` is an element of
`Forms k T` in `logPower k f T n`, and the operators `logD` and `d` agree by `coe_logD`.
`logPowerD` is `logD` with its types indexed by degree, for complexes. The form `θ` is the form of
any unit of `T` that is the image of `f`, by `theta_eq_dlog`, so for a divisor pair it is
`dlog k P.eqnUnit`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open CliffordAlgebra (involute)
open ExteriorAlgebra (ι)
open IsLocalization.Away (invSelf)

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)

/-- The map on forms along `A → T` is `A`-linear. -/
theorem Forms.map_toAlgHom_smul (a : A) (x : Forms k A) :
    reg (a • x) = a • reg x := by
  rw [Forms.map_smul, IsScalarTower.coe_toAlgHom', algebraMap_smul]

variable (A) in
/-- The image of `Ω_A^n` in forms on `T`, as an `A`-submodule. The blueprint identifies `Ω_A^n` with
this image, using `lem:dr-projective`, and `IsSmoothPrincipalPair.map_injective` justifies that.

Blueprint: `def:dr-log`. -/
noncomputable def regularPower (n : ℕ) : Submodule A (Forms k T) :=
  (⋀[A]^n Ω[A⁄k]).map (exteriorMap T (KaehlerDifferential.map k k A T)).toLinearMap

variable {k T} in
theorem mem_regularPower {n : ℕ} {x : Forms k T} :
    x ∈ regularPower k A T n ↔ ∃ ω ∈ ⋀[A]^n Ω[A⁄k], reg ω = x := by
  simp only [regularPower, Submodule.mem_map, AlgHom.toLinearMap_apply, Forms.map_toAlgHom]

theorem map_mem_regularPower {n : ℕ} {ω : Forms k A} (hω : ω ∈ ⋀[A]^n Ω[A⁄k]) :
    reg ω ∈ regularPower k A T n :=
  mem_regularPower.2 ⟨ω, hω, rfl⟩

theorem regularPower_le_exteriorPower (n : ℕ) :
    regularPower k A T n ≤ (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  intro x hx
  obtain ⟨ω, hω, rfl⟩ := mem_regularPower.1 hx
  exact Forms.map_mem_exteriorPower _ hω

variable [IsLocalization.Away f T]

/-! ### The form `θ` -/

/-- The form `θ = df / f` on the localization `T`. By `theta_eq_dlog` it is `dlog k u` for any unit
`u` of `T` that is the image of `f`, so for a divisor pair it is `dlog k P.eqnUnit`.

Blueprint: the section "Logarithmic forms and the residue sequence". -/
noncomputable def theta : Forms k T :=
  dlog k (IsLocalization.Away.algebraMap_isUnit (S := T) f).unit

local notation "θ" => theta k f T

omit [Algebra k A] [IsScalarTower k A T] in
/-- `θ` is the logarithmic form of any unit that is the image of `f`. -/
theorem theta_eq_dlog {u : Tˣ} (hu : (u : T) = algebraMap A T f) : θ = dlog k u :=
  congrArg (dlog k) (Units.ext hu.symm)

omit [Algebra k A] [IsScalarTower k A T] in
theorem theta_eq_invSelf_smul : θ = (invSelf f : T) • diff k (algebraMap A T f) :=
  dlog_eq_invSelf_smul k f _

/-- `f θ = df`. -/
@[simp]
theorem self_smul_theta : f • θ = reg (diff k f) := by
  rw [Forms.map_diff, ← algebraMap_smul T f, IsScalarTower.coe_toAlgHom']
  exact val_smul_dlog k (IsLocalization.Away.algebraMap_isUnit (S := T) f).unit

omit [Algebra k A] [IsScalarTower k A T] in
theorem theta_mem_exteriorPower_one : θ ∈ ⋀[T]^1 Ω[T⁄k] :=
  dlog_mem_exteriorPower_one k _

omit [Algebra k A] [IsScalarTower k A T] in
@[simp]
theorem theta_mul_self : θ * θ = 0 :=
  dlog_mul_self k _

omit [Algebra k A] [IsScalarTower k A T] in
/-- `dθ = 0`. -/
@[simp]
theorem d_theta : d k θ = 0 :=
  d_dlog k _

omit [Algebra k A] [IsScalarTower k A T] in
/-- `d(θ ∧ x) = -θ ∧ dx`. -/
@[simp]
theorem d_theta_mul (x : Forms k T) : d k (θ * x) = -(θ * d k x) :=
  d_dlog_mul k _ x

/-- The formula `d(f ξ) = f (θ ∧ ξ + dξ)`. This is what makes `f L^•` a subcomplex.

Blueprint: `lem:dr-log-dga`. -/
theorem d_self_smul (ξ : Forms k T) : d k (f • ξ) = f • (θ * ξ + d k ξ) := by
  rw [← algebraMap_smul T f ξ, ← algebraMap_smul T f (θ * ξ + d k ξ)]
  exact d_val_smul k (IsLocalization.Away.algebraMap_isUnit (S := T) f).unit ξ

omit [Algebra k A] [IsScalarTower k A T] in
/-- `θ` moves past a form up to the grade involution, with no degree hypothesis. -/
theorem mul_theta (x : Forms k T) : x * θ = θ * involute x := by
  rw [theta_eq_invSelf_smul, smul_mul_assoc, mul_smul_comm, diff_apply,
    ι_mul_eq_involute_mul _ (involute x), CliffordAlgebra.involute_involute]

omit [Algebra k A] [IsScalarTower k A T] in
theorem theta_mul_mem_exteriorPower {n : ℕ} {x : Forms k T} (hx : x ∈ ⋀[T]^n Ω[T⁄k]) :
    θ * x ∈ ⋀[T]^(n + 1) Ω[T⁄k] := by
  rw [theta_eq_invSelf_smul, smul_mul_assoc]
  exact Submodule.smul_mem _ _ (diff_mul_mem_exteriorPower k _ hx)

omit [Algebra k A] [IsScalarTower k A T] in
/-- The degree zero component of `θ ∧ y` vanishes. -/
@[simp]
theorem exteriorProj_zero_theta_mul (y : Forms k T) : exteriorProj 0 (θ * y) = 0 := by
  rw [theta_eq_invSelf_smul, smul_mul_assoc, _root_.map_smul, diff_apply, exteriorProj_zero_ι_mul,
    smul_zero]

omit [Algebra k A] [IsScalarTower k A T] in
/-- The degree `n + 1` component of `θ ∧ y` is `θ ∧` the degree `n` component of `y`. -/
theorem coe_exteriorProj_succ_theta_mul (n : ℕ) (y : Forms k T) :
    (exteriorProj (n + 1) (θ * y) : Forms k T) = θ * (exteriorProj n y : Forms k T) := by
  rw [theta_eq_invSelf_smul, smul_mul_assoc, smul_mul_assoc, _root_.map_smul, diff_apply,
    exteriorProj_ι_mul, Submodule.coe_smul, coe_wedgeLeft]

/-- The product of two logarithmic forms. The term with two factors `θ` vanishes, and the regular
part `ω` of the left factor moves past `θ` with the grade involution.

Blueprint: the proof of `lem:dr-log-dga`. -/
theorem add_theta_mul_mul_add_theta_mul (ω η ω' η' : Forms k A) :
    (reg ω + θ * reg η) * (reg ω' + θ * reg η') =
      reg (ω * ω') + θ * reg (involute ω * η' + η * ω') := by
  have h₁ : reg ω * (θ * reg η') = θ * (reg (involute ω) * reg η') := by
    rw [← mul_assoc, mul_theta, mul_assoc, Forms.map_involute]
  have h₂ : θ * reg η * (θ * reg η') = 0 := by
    rw [mul_assoc, ← mul_assoc (reg η), mul_theta, mul_assoc, ← mul_assoc θ, theta_mul_self,
      zero_mul]
  simp only [add_mul, mul_add, map_mul, map_add, h₁, h₂, add_zero, mul_assoc]
  abel

/-! ### Logarithmic forms -/

/-- The logarithmic forms `Ω_A^• + θ ∧ Ω_A^•`, an `A`-subalgebra of forms on `T`. Their pieces of
each degree are `logPower`, and this is the total algebra of `lem:dr-log-dga`. As with all forms, it
is an `A`-algebra and a `k`-algebra, and `d` is only `k`-linear on it.

Blueprint: `def:dr-log`, in total degree, and `lem:dr-log-dga`. -/
noncomputable def logForms : Subalgebra A (Forms k T) where
  carrier := {x | ∃ ω η : Forms k A, reg ω + θ * reg η = x}
  mul_mem' := by
    rintro _ _ ⟨ω, η, rfl⟩ ⟨ω', η', rfl⟩
    exact ⟨_, _, (add_theta_mul_mul_add_theta_mul k f T ω η ω' η').symm⟩
  add_mem' := by
    rintro _ _ ⟨ω, η, rfl⟩ ⟨ω', η', rfl⟩
    exact ⟨ω + ω', η + η', by simp only [map_add, mul_add]; abel⟩
  algebraMap_mem' a := ⟨algebraMap A _ a, 0, by
    simp only [Forms.map_algebraMap, IsScalarTower.coe_toAlgHom', map_zero, mul_zero, add_zero,
      ← IsScalarTower.algebraMap_apply]⟩

variable {k f T} in
theorem mem_logForms {x : Forms k T} :
    x ∈ logForms k f T ↔ ∃ ω η : Forms k A, reg ω + θ * reg η = x :=
  Iff.rfl

theorem map_mem_logForms (ω : Forms k A) : reg ω ∈ logForms k f T :=
  ⟨ω, 0, by simp⟩

theorem theta_mul_map_mem_logForms (η : Forms k A) : θ * reg η ∈ logForms k f T :=
  ⟨0, η, by simp⟩

/-- `θ` is a logarithmic form. -/
theorem theta_mem_logForms : θ ∈ logForms k f T := by
  simpa using theta_mul_map_mem_logForms k f T 1

/-- The surjection `(ω, η) ↦ ω + θ ∧ η` from pairs of forms on `A` onto logarithmic forms. It is
`A`-linear. For a smooth principal pair, `IsSmoothPrincipalPair.map_eq_zero_of_logMk_eq_zero` says
that its kernel restricts to zero on `S`, and that is how `logResidue` is defined.

Blueprint: `def:dr-log`. -/
noncomputable def logMk : (Forms k A × Forms k A) →ₗ[A] logForms k f T where
  toFun p := ⟨reg p.1 + θ * reg p.2, p.1, p.2, rfl⟩
  map_add' p q := Subtype.ext <| by
    simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add, Subalgebra.coe_add]
    abel
  map_smul' a p := Subtype.ext <| by
    simp only [Prod.smul_fst, Prod.smul_snd, Forms.map_toAlgHom_smul, RingHom.id_apply,
      Subalgebra.coe_smul, smul_add, mul_smul_comm]

@[simp]
theorem coe_logMk (p : Forms k A × Forms k A) :
    (logMk k f T p : Forms k T) = reg p.1 + θ * reg p.2 :=
  rfl

theorem logMk_surjective : Function.Surjective (logMk k f T) := by
  rintro ⟨_, ω, η, rfl⟩
  exact ⟨(ω, η), rfl⟩

/-- The product of `logMk`, which is the formula for a product of logarithmic forms.

Blueprint: the proof of `lem:dr-log-dga`. -/
theorem logMk_mul_logMk (ω η ω' η' : Forms k A) :
    logMk k f T (ω, η) * logMk k f T (ω', η') =
      logMk k f T (ω * ω', involute ω * η' + η * ω') :=
  Subtype.ext (add_theta_mul_mul_add_theta_mul k f T ω η ω' η')

/-- The `A`-algebra map from forms on `A` to logarithmic forms. Its underlying function is
`Forms.map (IsScalarTower.toAlgHom k A T)`, by `coe_ofRegular`. It is injective for a smooth
principal pair, by `IsSmoothPrincipalPair.ofRegular_injective`. Regular forms act on logarithmic
forms on both sides through it, so `L^•` is a graded left and right module over them.

Blueprint: `def:dr-log`, `lem:dr-log-dga`. -/
noncomputable def ofRegular : Forms k A →ₐ[A] logForms k f T :=
  (exteriorMap T (KaehlerDifferential.map k k A T)).codRestrict (logForms k f T) fun ω => by
    rw [← Forms.map_toAlgHom]
    exact map_mem_logForms k f T ω

@[simp]
theorem coe_ofRegular (ω : Forms k A) : (ofRegular k f T ω : Forms k T) = reg ω :=
  (Forms.map_toAlgHom k A T ω).symm

/-- A regular form is `ω + θ ∧ 0`. -/
theorem logMk_mk_zero (ω : Forms k A) : logMk k f T (ω, 0) = ofRegular k f T ω :=
  Subtype.ext (by simp)

/-! ### The modules `L^n` -/

/-- The module `L^n = Ω_A^n + θ ∧ Ω_A^(n-1)` of logarithmic forms of degree `n`, an `A`-submodule of
forms on `T`, inside `Ω_T^n` by `logPower_le_exteriorPower`. In degree zero it is the image of `A`.

Blueprint: `def:dr-log`. -/
noncomputable def logPower : ℕ → Submodule A (Forms k T)
  | 0 => regularPower k A T 0
  | n + 1 => regularPower k A T (n + 1) ⊔ (regularPower k A T n).map (LinearMap.mulLeft A θ)

variable {k f T} in
/-- A logarithmic form of degree zero is the image of a form of degree zero on `A`.

Blueprint: `def:dr-log`. -/
theorem mem_logPower_zero {x : Forms k T} :
    x ∈ logPower k f T 0 ↔ ∃ ω ∈ ⋀[A]^0 Ω[A⁄k], reg ω = x :=
  mem_regularPower

variable {k f T} in
/-- A logarithmic form of degree `n + 1` is `ω + θ ∧ η`, with `ω` of degree `n + 1` and `η` of
degree `n` on `A`.

Blueprint: `def:dr-log`. -/
theorem mem_logPower_succ {n : ℕ} {x : Forms k T} :
    x ∈ logPower k f T (n + 1) ↔
      ∃ ω ∈ ⋀[A]^(n + 1) Ω[A⁄k], ∃ η ∈ ⋀[A]^n Ω[A⁄k], reg ω + θ * reg η = x := by
  simp only [logPower, Submodule.mem_sup, Submodule.mem_map, LinearMap.mulLeft_apply,
    mem_regularPower]
  constructor
  · rintro ⟨_, ⟨ω, hω, rfl⟩, _, ⟨_, ⟨η, hη, rfl⟩, rfl⟩, rfl⟩
    exact ⟨ω, hω, η, hη, rfl⟩
  · rintro ⟨ω, hω, η, hη, rfl⟩
    exact ⟨_, ⟨ω, hω, rfl⟩, _, ⟨_, ⟨η, hη, rfl⟩, rfl⟩, rfl⟩

/-- A regular form of degree `n` is a logarithmic form of degree `n`. -/
theorem regularPower_le_logPower (n : ℕ) : regularPower k A T n ≤ logPower k f T n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left

theorem map_mem_logPower {n : ℕ} {ω : Forms k A} (hω : ω ∈ ⋀[A]^n Ω[A⁄k]) :
    reg ω ∈ logPower k f T n :=
  regularPower_le_logPower k f T n (map_mem_regularPower k T hω)

/-- `θ ∧ η` is a logarithmic form of degree `n + 1` for `η` of degree `n` on `A`. -/
theorem theta_mul_map_mem_logPower {n : ℕ} {η : Forms k A} (hη : η ∈ ⋀[A]^n Ω[A⁄k]) :
    θ * reg η ∈ logPower k f T (n + 1) :=
  mem_logPower_succ.2 ⟨0, zero_mem _, η, hη, by simp⟩

/-- Logarithmic forms of degree `n` are logarithmic forms. -/
theorem logPower_le_logForms (n : ℕ) :
    logPower k f T n ≤ Subalgebra.toSubmodule (logForms k f T) := by
  intro x hx
  cases n with
  | zero =>
    obtain ⟨ω, -, rfl⟩ := mem_logPower_zero.1 hx
    exact map_mem_logForms k f T ω
  | succ n =>
    obtain ⟨ω, -, η, -, rfl⟩ := mem_logPower_succ.1 hx
    exact ⟨ω, η, rfl⟩

/-- Logarithmic forms of degree `n` are forms of degree `n` on `T`.

Blueprint: `def:dr-log`. -/
theorem logPower_le_exteriorPower (n : ℕ) :
    logPower k f T n ≤ (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  intro x hx
  cases n with
  | zero =>
    obtain ⟨ω, hω, rfl⟩ := mem_logPower_zero.1 hx
    exact Forms.map_mem_exteriorPower _ hω
  | succ n =>
    obtain ⟨ω, hω, η, hη, rfl⟩ := mem_logPower_succ.1 hx
    exact add_mem (Forms.map_mem_exteriorPower _ hω)
      (theta_mul_mem_exteriorPower k f T (Forms.map_mem_exteriorPower _ hη))

variable {k f T} in
/-- `logForms` is homogeneous: the homogeneous components of a logarithmic form are logarithmic
forms. -/
theorem coe_exteriorProj_mem_logPower {x : Forms k T} (hx : x ∈ logForms k f T) (n : ℕ) :
    (exteriorProj n x : Forms k T) ∈ logPower k f T n := by
  obtain ⟨ω, η, rfl⟩ := hx
  cases n with
  | zero =>
    rw [map_add, exteriorProj_zero_theta_mul, add_zero, Forms.coe_exteriorProj_map]
    exact map_mem_logPower k f T (SetLike.coe_mem _)
  | succ n =>
    rw [map_add, Submodule.coe_add, coe_exteriorProj_succ_theta_mul, Forms.coe_exteriorProj_map,
      Forms.coe_exteriorProj_map]
    exact mem_logPower_succ.2 ⟨_, SetLike.coe_mem _, _, SetLike.coe_mem _, rfl⟩

/-- `L^n` is the part of the total logarithmic algebra of degree `n`.

Blueprint: `def:dr-log`, `lem:dr-log-dga`. -/
theorem logPower_eq_inf (n : ℕ) :
    logPower k f T n =
      Subalgebra.toSubmodule (logForms k f T) ⊓ (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  refine le_antisymm (le_inf (logPower_le_logForms k f T n) (logPower_le_exteriorPower k f T n)) ?_
  rintro x ⟨hx₁, hx₂⟩
  rw [← exteriorProj_of_mem hx₂]
  exact coe_exteriorProj_mem_logPower hx₁ n

variable {k f T} in
/-- A form is logarithmic of degree `n` exactly when it is logarithmic and of degree `n`. -/
theorem mem_logPower_iff {n : ℕ} {x : Forms k T} :
    x ∈ logPower k f T n ↔ x ∈ logForms k f T ∧ x ∈ ⋀[T]^n Ω[T⁄k] := by
  rw [logPower_eq_inf]
  rfl

variable {k f T} in
/-- Left wedge by `θ` raises the degree of a logarithmic form by one, by the blueprint's product.

Blueprint: `lem:dr-log-dga`. -/
theorem theta_mul_mem_logPower {n : ℕ} {x : Forms k T} (hx : x ∈ logPower k f T n) :
    θ * x ∈ logPower k f T (n + 1) :=
  mem_logPower_iff.2 ⟨mul_mem (theta_mem_logForms k f T) (mem_logPower_iff.1 hx).1,
    theta_mul_mem_exteriorPower k f T (mem_logPower_iff.1 hx).2⟩

/-- The total logarithmic algebra is the sum of the `L^n`.

Blueprint: `lem:dr-log-dga`. -/
theorem iSup_logPower : ⨆ n, logPower k f T n = Subalgebra.toSubmodule (logForms k f T) := by
  classical
  refine le_antisymm (iSup_le (logPower_le_logForms k f T)) fun x hx => ?_
  rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[T]^i Ω[T⁄k]) x]
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.mem_iSup_of_mem n (coe_exteriorProj_mem_logPower hx n)

/-- The `L^n` are a graded submonoid of forms on `T`: `1 ∈ L^0` and `L^p ∧ L^q ⊆ L^(p+q)`. In
particular `L^•` is a graded left and right module over regular forms.

Blueprint: `lem:dr-log-dga`. -/
instance gradedMonoid_logPower : SetLike.GradedMonoid (logPower k f T) where
  one_mem := mem_logPower_iff.2 ⟨one_mem _, SetLike.GradedOne.one_mem⟩
  mul_mem _ _ _ _ hx hy := mem_logPower_iff.2
    ⟨mul_mem (mem_logPower_iff.1 hx).1 (mem_logPower_iff.1 hy).1,
      SetLike.GradedMul.mul_mem (mem_logPower_iff.1 hx).2 (mem_logPower_iff.1 hy).2⟩

/-! ### The inclusions in each degree -/

/-- The map `Ω_A^n → L^n` on regular forms of degree `n`. It is `Forms.map` with its domain and
codomain restricted, by `coe_powerToLog`, and it is `A`-linear.

Blueprint: `def:dr-log`. -/
noncomputable def powerToLog (n : ℕ) : ⋀[A]^n Ω[A⁄k] →ₗ[A] logPower k f T n where
  toFun x := ⟨reg (x : Forms k A), map_mem_logPower k f T x.2⟩
  map_add' x y := Subtype.ext (map_add reg (x : Forms k A) y)
  map_smul' a x := Subtype.ext (Forms.map_toAlgHom_smul k T a (x : Forms k A))

@[simp]
theorem coe_powerToLog (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    (powerToLog k f T n x : Forms k T) = reg (x : Forms k A) :=
  rfl

/-- `Ω_A^0 → L^0` is surjective, so that `L^0` is the image of `A`, and the residue sequence is
exact in degree zero, where its last term is zero.

Blueprint: "In degree zero it is `A`" in `def:dr-log`. -/
theorem powerToLog_zero_surjective : Function.Surjective (powerToLog k f T 0) := by
  rintro ⟨x, hx⟩
  obtain ⟨ω, hω, rfl⟩ := mem_logPower_zero.1 hx
  exact ⟨⟨ω, hω⟩, rfl⟩

/-- The map `L^n → Ω_T^n`, the inclusion of logarithmic forms of degree `n`. It is `A`-linear.

Blueprint: `def:dr-log`. -/
noncomputable def logPowerToPower (n : ℕ) : logPower k f T n →ₗ[A] ⋀[T]^n Ω[T⁄k] where
  toFun x := ⟨x, logPower_le_exteriorPower k f T n x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_logPowerToPower (n : ℕ) (x : logPower k f T n) :
    (logPowerToPower k f T n x : Forms k T) = x :=
  rfl

theorem logPowerToPower_injective (n : ℕ) : Function.Injective (logPowerToPower k f T n) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : ⋀[T]^n Ω[T⁄k] → Forms k T) h)

/-- The map `L^n → L`, the inclusion of logarithmic forms of degree `n` in all logarithmic forms. -/
noncomputable def logPowerToLogForms (n : ℕ) : logPower k f T n →ₗ[A] logForms k f T where
  toFun x := ⟨x, logPower_le_logForms k f T n x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_logPowerToLogForms (n : ℕ) (x : logPower k f T n) :
    (logPowerToLogForms k f T n x : Forms k T) = x :=
  rfl

theorem logPowerToLogForms_powerToLog (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    logPowerToLogForms k f T n (powerToLog k f T n x) = ofRegular k f T (x : Forms k A) :=
  Subtype.ext (coe_ofRegular k f T (x : Forms k A)).symm

/-- The composite `Ω_A^n → L^n → Ω_T^n` is the map on forms. -/
theorem logPowerToPower_powerToLog (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    logPowerToPower k f T n (powerToLog k f T n x) =
      Forms.mapPower (IsScalarTower.toAlgHom k A T) n x :=
  rfl

/-! ### The differential -/

/-- The formula `d(ω + θ ∧ η) = dω - θ ∧ dη`.

Blueprint: `lem:dr-log-dga`. -/
theorem d_add_theta_mul (ω η : Forms k A) :
    d k (reg ω + θ * reg η) = reg (d k ω) - θ * reg (d k η) := by
  rw [map_add, d_theta_mul, Forms.map_d, Forms.map_d, sub_eq_add_neg]

variable {k f T} in
/-- Logarithmic forms are stable under `d`.

Blueprint: `lem:dr-log-dga`. -/
theorem d_mem_logForms {x : Forms k T} (hx : x ∈ logForms k f T) : d k x ∈ logForms k f T := by
  obtain ⟨ω, η, rfl⟩ := hx
  exact ⟨d k ω, -d k η, by rw [d_add_theta_mul, map_neg, mul_neg, sub_eq_add_neg]⟩

variable {k f T} in
/-- `d` raises the degree of logarithmic forms by one.

Blueprint: `lem:dr-log-dga`. -/
theorem d_mem_logPower {n : ℕ} {x : Forms k T} (hx : x ∈ logPower k f T n) :
    d k x ∈ logPower k f T (n + 1) :=
  mem_logPower_iff.2 ⟨d_mem_logForms (mem_logPower_iff.1 hx).1,
    d_mem_exteriorPower k (mem_logPower_iff.1 hx).2⟩

/-- The differential on logarithmic forms, in total degree. This is `d` with its domain and codomain
restricted, by `coe_logD`.

Blueprint: `lem:dr-log-dga`. -/
noncomputable def logD : logForms k f T →ₗ[k] logForms k f T where
  toFun x := ⟨d k (x : Forms k T), d_mem_logForms x.2⟩
  map_add' x y := Subtype.ext (map_add (d k) (x : Forms k T) y)
  map_smul' c x := Subtype.ext (map_smul (d k) c (x : Forms k T))

@[simp]
theorem coe_logD (x : logForms k f T) : (logD k f T x : Forms k T) = d k (x : Forms k T) :=
  rfl

@[simp]
theorem logD_logD (x : logForms k f T) : logD k f T (logD k f T x) = 0 :=
  Subtype.ext (d_d k _)

/-- `d(ω + θ ∧ η) = dω - θ ∧ dη`, for `logMk`.

Blueprint: `lem:dr-log-dga`. -/
theorem logD_logMk (ω η : Forms k A) :
    logD k f T (logMk k f T (ω, η)) = logMk k f T (d k ω, -d k η) :=
  Subtype.ext <| by
    rw [coe_logD, coe_logMk, coe_logMk, d_add_theta_mul, map_neg, mul_neg, sub_eq_add_neg]

/-- The differential commutes with the map from regular forms. -/
@[simp]
theorem logD_ofRegular (ω : Forms k A) :
    logD k f T (ofRegular k f T ω) = ofRegular k f T (d k ω) :=
  Subtype.ext <| by simp [Forms.map_d]

/-- The differential on logarithmic forms in degree `n`, as a `k`-linear map `L^n → L^(n+1)`. This
is `d` with its domain and codomain restricted, by `coe_logPowerD`. Use it where a complex needs
types indexed by degree, and `d` or `logD` otherwise.

Blueprint: `lem:dr-log-dga`. -/
noncomputable def logPowerD (n : ℕ) : logPower k f T n →ₗ[k] logPower k f T (n + 1) where
  toFun x := ⟨d k (x : Forms k T), d_mem_logPower x.2⟩
  map_add' x y := Subtype.ext (map_add (d k) (x : Forms k T) y)
  map_smul' c x := Subtype.ext (map_smul (d k) c (x : Forms k T))

@[simp]
theorem coe_logPowerD (n : ℕ) (x : logPower k f T n) :
    (logPowerD k f T n x : Forms k T) = d k (x : Forms k T) :=
  rfl

@[simp]
theorem logPowerD_logPowerD (n : ℕ) (x : logPower k f T n) :
    logPowerD k f T (n + 1) (logPowerD k f T n x) = 0 :=
  Subtype.ext (d_d k _)

@[simp]
theorem logPowerD_comp_logPowerD (n : ℕ) :
    logPowerD k f T (n + 1) ∘ₗ logPowerD k f T n = 0 :=
  LinearMap.ext (logPowerD_logPowerD k f T n)

/-- The map from regular forms commutes with the differential. -/
theorem logPowerD_powerToLog (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    logPowerD k f T n (powerToLog k f T n x) = powerToLog k f T (n + 1) (powerD k A n x) :=
  Subtype.ext (Forms.map_d _ (x : Forms k A)).symm

/-- The inclusion in forms on `T` commutes with the differential. -/
theorem logPowerToPower_logPowerD (n : ℕ) (x : logPower k f T n) :
    logPowerToPower k f T (n + 1) (logPowerD k f T n x) =
      powerD k T n (logPowerToPower k f T n x) :=
  rfl

/-! ### The ideal `f L^•` -/

/-- The graded ideal `f L^•` of logarithmic forms, as an `A`-submodule. It is a two-sided ideal, by
`mul_mem_logIdeal_left` and `mul_mem_logIdeal_right`, and it is a subcomplex, by
`logD_mem_logIdeal`.

Blueprint: `lem:dr-log-dga`. -/
noncomputable def logIdeal : Submodule A (logForms k f T) :=
  Ideal.span {f} • ⊤

variable {k f T} in
theorem mem_logIdeal {x : logForms k f T} : x ∈ logIdeal k f T ↔ ∃ y, f • y = x := by
  rw [logIdeal, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

variable {k f T} in
theorem mul_mem_logIdeal_left {x : logForms k f T} (hx : x ∈ logIdeal k f T) (y : logForms k f T) :
    y * x ∈ logIdeal k f T := by
  obtain ⟨z, rfl⟩ := mem_logIdeal.1 hx
  exact mem_logIdeal.2 ⟨y * z, (mul_smul_comm _ _ _).symm⟩

variable {k f T} in
theorem mul_mem_logIdeal_right {x : logForms k f T} (hx : x ∈ logIdeal k f T) (y : logForms k f T) :
    x * y ∈ logIdeal k f T := by
  obtain ⟨z, rfl⟩ := mem_logIdeal.1 hx
  exact mem_logIdeal.2 ⟨z * y, (smul_mul_assoc _ _ _).symm⟩

/-- `f L^•` is stable under `d`, although `d` is not `A`-linear, since `d(f ξ) = f (θ ∧ ξ + dξ)`.

Blueprint: `lem:dr-log-dga`. -/
theorem logD_mem_logIdeal {x : logForms k f T} (hx : x ∈ logIdeal k f T) :
    logD k f T x ∈ logIdeal k f T := by
  obtain ⟨y, rfl⟩ := mem_logIdeal.1 hx
  exact mem_logIdeal.2 ⟨⟨θ, theta_mem_logForms k f T⟩ * y + logD k f T y,
    Subtype.ext (d_self_smul k f T y).symm⟩

/-- `f L^•` is a graded ideal: the homogeneous components of a member of `f L^•` lie in `f L^n`.

Blueprint: `lem:dr-log-dga`. -/
theorem exists_coe_exteriorProj_eq_of_mem_logIdeal {x : logForms k f T} (hx : x ∈ logIdeal k f T)
    (n : ℕ) :
    ∃ y ∈ logPower k f T n, (exteriorProj n (x : Forms k T) : Forms k T) = f • y := by
  obtain ⟨y, rfl⟩ := mem_logIdeal.1 hx
  refine ⟨_, coe_exteriorProj_mem_logPower y.2 n, ?_⟩
  rw [Subalgebra.coe_smul, ← algebraMap_smul T f, ← algebraMap_smul T f, _root_.map_smul,
    Submodule.coe_smul]

/-- The form of `logD_mem_logIdeal` in each degree: `d (f L^n) ⊆ f L^(n+1)`.

Blueprint: `lem:dr-log-dga`. -/
theorem exists_d_self_smul_eq_of_mem_logPower {n : ℕ} {x : Forms k T} (hx : x ∈ logPower k f T n) :
    ∃ y ∈ logPower k f T (n + 1), d k (f • x) = f • y :=
  ⟨θ * x + d k x, add_mem (theta_mul_mem_logPower hx) (d_mem_logPower hx), d_self_smul k f T x⟩

/-- The differential induced by `d` on the quotient `L^• / f L^•`, which exists by
`logD_mem_logIdeal`. It is `k`-linear, and it is characterized by `logQuotientD_mk`.

Blueprint: `lem:dr-log-dga`. -/
noncomputable def logQuotientD :
    (logForms k f T ⧸ logIdeal k f T) →ₗ[k] logForms k f T ⧸ logIdeal k f T :=
  (Submodule.Quotient.restrictScalarsEquiv k (logIdeal k f T)).toLinearMap ∘ₗ
    Submodule.mapQ _ _ (logD k f T) (fun _ hx => logD_mem_logIdeal k f T hx) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv k (logIdeal k f T)).symm.toLinearMap

@[simp]
theorem logQuotientD_mk (x : logForms k f T) :
    logQuotientD k f T (Submodule.Quotient.mk x) = Submodule.Quotient.mk (logD k f T x) :=
  rfl

@[simp]
theorem logQuotientD_logQuotientD (x : logForms k f T ⧸ logIdeal k f T) :
    logQuotientD k f T (logQuotientD k f T x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [logQuotientD_mk, logD_logD, Submodule.Quotient.mk_zero]

end OrlikSolomon.DeRham
