/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Log.Basic
public import OrlikSolomon.DeRham.Pole.Cartan

/-!
# Logarithmic Euler contraction

For `E = f v`, contraction takes every logarithmic form to a regular form and descends to
`J` on `L/fL`. If `v(f) = 1 + f h`, its identities with the differential and left wedge `W`
by `df/f` are `dJ + Jd = 0` and `WJ + JW = id`. Neither the constructions nor these identities
require smoothness or characteristic zero; smooth pairs supply the normal derivation separately.

## Main definitions and results

* `logEulerContraction` and `logEulerContraction_logMk`: the actual contraction, with its regular
  representative and degree-lowering property.
* `logQuotientEulerContraction` and `logQuotientThetaWedge`: the operators `J` and `W` on `L/fL`.
* `logQuotientPower` and the typed restrictions of `d`, `J` and `W`: their exact source and target
  degrees, including vanishing of contraction in degree zero.
* `logEulerLieDerivative_mem_logIdeal`: the Euler Lie derivative takes values in `f L`.
* `logQuotientEulerContraction_anticommute` and `logQuotientThetaWedge_euler_identity`: the two
  identities on the quotient, using precisely normality modulo `f`.

Blueprint: `lem:dr-euler`.
-/

@[expose] public section
noncomputable section
open OrlikSolomon.DeRham IsLocalization.Away
namespace OrlikSolomon.DeRham
variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]
local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)

/-- The localized Euler vector field `E = f v`. No normality hypothesis is needed to define it. -/
def logEulerDerivation (v : Derivation k A A) : Derivation k T T :=
  algebraMap A T f • localizedDerivation k T (Submonoid.powers f) v

/-- The Euler vector field sends a regular function `a` to `f v(a)`. -/
theorem logEulerDerivation_algebraMap (v : Derivation k A A) (a : A) :
    logEulerDerivation k f T v (algebraMap A T a) = algebraMap A T (f * v a) := by
  simp only [logEulerDerivation, smul_apply, localizedDerivation_algebraMap, smul_eq_mul, map_mul]

/-- Euler contraction of a regular form is regular, with preimage `f ι_v ω`. -/
theorem formContraction_logEulerDerivation_map (v : Derivation k A A) (x : Forms k A) :
    formContraction k (logEulerDerivation k f T v) (reg x) = reg (f • formContraction k v x) := by
  rw [logEulerDerivation, formContraction_smul, LinearMap.smul_apply,
    ← map_formContraction_localizedDerivation]
  rw [Forms.map_smul, IsScalarTower.coe_toAlgHom']

/-- Euler contraction of `df/f` is the regular function `v(f)`. -/
theorem formContraction_logEulerDerivation_theta (v : Derivation k A A) :
    formContraction k (logEulerDerivation k f T v) (theta k f T) =
      algebraMap T (Forms k T) (algebraMap A T (v f)) := by
  rw [theta_eq_invSelf_smul, map_smul, formContraction_diff, logEulerDerivation_algebraMap,
    map_mul, map_mul,
    ← Algebra.smul_def, smul_smul, invSelf_mul_self, one_smul]

/-- The contraction of a logarithmic term has the regular preimage
`v(f) η - df ∧ ι_v η`. -/
theorem formContraction_logEulerDerivation_theta_mul_map (v : Derivation k A A) (x : Forms k A) :
    formContraction k (logEulerDerivation k f T v) (theta k f T * reg x) =
      reg (v f • x - diff k f * formContraction k v x) := by
  rw [formContraction_mul_of_mem_exteriorPower k _ (theta_mem_exteriorPower_one k f T),
    formContraction_logEulerDerivation_theta, formContraction_logEulerDerivation_map]
  simp only [Int.natCast_one, Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [← sub_eq_add_neg, ← Algebra.smul_def, map_sub, Forms.map_smul,
    IsScalarTower.coe_toAlgHom', map_mul]
  simp only [algebraMap_smul]
  rw [Forms.map_toAlgHom_smul, mul_smul_comm, ← smul_mul_assoc, self_smul_theta]

/-- An explicit regular preimage for the Euler contraction of every logarithmic form. -/
theorem formContraction_logEulerDerivation_logMk (v : Derivation k A A) (ω η : Forms k A) :
    formContraction k (logEulerDerivation k f T v) (logMk k f T (ω, η) : Forms k T) =
      reg (f • formContraction k v ω + v f • η - diff k f * formContraction k v η) := by
  rw [coe_logMk, map_add, formContraction_logEulerDerivation_map,
    formContraction_logEulerDerivation_theta_mul_map]
  simp only [map_sub, map_add]
  abel

/-- Euler contraction as an actual `A`-linear endomorphism of logarithmic forms. Its values are
regular, by `logEulerContraction_logMk`. Blueprint: `lem:dr-euler`. -/
def logEulerContraction (v : Derivation k A A) : logForms k f T →ₗ[A] logForms k f T :=
  (((formContraction k (logEulerDerivation k f T v)).restrictScalars A).comp
    (logForms k f T).toSubmodule.subtype).codRestrict (logForms k f T).toSubmodule fun x ↦ by
      obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x
      change formContraction k (logEulerDerivation k f T v) (logMk k f T (ω, η) : Forms k T) ∈ _
      rw [formContraction_logEulerDerivation_logMk]
      exact map_mem_logForms k f T _

/-- The restricted Euler contraction is the ambient contraction on forms. -/
@[simp]
theorem coe_logEulerContraction (v : Derivation k A A) (x : logForms k f T) :
    (logEulerContraction k f T v x : Forms k T) =
      formContraction k (logEulerDerivation k f T v) x := rfl

/-- The regular representative of the restricted Euler contraction. -/
theorem logEulerContraction_logMk (v : Derivation k A A) (ω η : Forms k A) :
    logEulerContraction k f T v (logMk k f T (ω, η)) =
      ofRegular k f T (f • formContraction k v ω + v f • η - diff k f * formContraction k v η) := by
  apply Subtype.ext
  rw [coe_logEulerContraction, formContraction_logEulerDerivation_logMk, coe_ofRegular]

/-- Every Euler contraction of a logarithmic form has a regular representative. -/
theorem exists_ofRegular_eq_logEulerContraction (v : Derivation k A A)
    (x : logForms k f T) : ∃ ω : Forms k A, ofRegular k f T ω = logEulerContraction k f T v x := by
  obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x
  exact ⟨_, (logEulerContraction_logMk k f T v ω η).symm⟩

/-- Euler contraction preserves `f L` by its `A`-linearity. -/
theorem logEulerContraction_mem_logIdeal (v : Derivation k A A) {x : logForms k f T}
    (hx : x ∈ logIdeal k f T) :
    logEulerContraction k f T v x ∈ logIdeal k f T := by
  obtain ⟨y, rfl⟩ := mem_logIdeal.1 hx
  exact mem_logIdeal.2 ⟨logEulerContraction k f T v y, (map_smul _ _ _).symm⟩

/-- The induced Euler contraction `J` on the actual module quotient `L/fL`.
Blueprint: `lem:dr-euler`. -/
def logQuotientEulerContraction (v : Derivation k A A) :
    (logForms k f T ⧸ logIdeal k f T) →ₗ[A] logForms k f T ⧸ logIdeal k f T :=
  (logIdeal k f T).mapQ _ (logEulerContraction k f T v)
    (fun _ hx => logEulerContraction_mem_logIdeal k f T v hx)

/-- Compute the descended contraction on a representative. -/
@[simp]
theorem logQuotientEulerContraction_mk (v : Derivation k A A) (x : logForms k f T) :
    logQuotientEulerContraction k f T v (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (logEulerContraction k f T v x) := rfl


/-- The logarithmic form `df/f`, as an element of the logarithmic algebra. -/
def logTheta : logForms k f T := ⟨theta k f T, theta_mem_logForms k f T⟩

/-- The underlying form of the logarithmic generator is `df/f`. -/
@[simp]
theorem coe_logTheta : (logTheta k f T : Forms k T) = theta k f T := rfl

/-- The logarithmic generator is closed. -/
@[simp]
theorem logD_logTheta : logD k f T (logTheta k f T) = 0 :=
  Subtype.ext (d_theta k f T)

/-- The logarithmic generator squares to zero. -/
@[simp]
theorem logTheta_mul_logTheta : logTheta k f T * logTheta k f T = 0 :=
  Subtype.ext (theta_mul_self k f T)

/-- The actual anticommutator of the logarithmic differential and Euler contraction. -/
def logEulerLieDerivative (v : Derivation k A A) : logForms k f T →ₗ[k] logForms k f T :=
  (logD k f T).comp ((logEulerContraction k f T v).restrictScalars k) +
    ((logEulerContraction k f T v).restrictScalars k).comp (logD k f T)

/-- The logarithmic operator agrees with the ambient Lie derivative. -/
@[simp]
theorem coe_logEulerLieDerivative (v : Derivation k A A) (x : logForms k f T) :
    (logEulerLieDerivative k f T v x : Forms k T) =
      lieDerivative k (logEulerDerivation k f T v) x := rfl

/-- The Euler Lie derivative satisfies ordinary Leibniz on the logarithmic algebra. -/
theorem logEulerLieDerivative_mul (v : Derivation k A A) (x y : logForms k f T) :
    logEulerLieDerivative k f T v (x * y) =
      logEulerLieDerivative k f T v x * y + x * logEulerLieDerivative k f T v y := by
  apply Subtype.ext
  simp only [coe_logEulerLieDerivative, Subalgebra.coe_mul, Subalgebra.coe_add, lieDerivative_mul]

/-- The Euler Lie derivative of a regular form belongs to `f L`, with an explicit preimage. -/
theorem logEulerLieDerivative_ofRegular (v : Derivation k A A) (ω : Forms k A) :
    logEulerLieDerivative k f T v (ofRegular k f T ω) =
      f • (logTheta k f T * ofRegular k f T (formContraction k v ω) +
        ofRegular k f T (lieDerivative k v ω)) := by
  apply Subtype.ext
  rw [coe_logEulerLieDerivative, coe_ofRegular, logEulerDerivation, lieDerivative_smul_derivation,
    ← map_formContraction_localizedDerivation, ← map_lieDerivative_localizedDerivation]
  have hd : reg (diff k f) = diff k (algebraMap A T f) := by
    rw [Forms.map_diff, IsScalarTower.coe_toAlgHom']
  rw [← hd, ← self_smul_theta k f T]
  simp only [Subalgebra.coe_smul, Subalgebra.coe_add, Subalgebra.coe_mul, coe_ofRegular,
    logTheta, smul_add, smul_mul_assoc, algebraMap_smul]

/-- If `v(f) = 1 + f h`, the Lie derivative of `df/f` is `f(h df/f + dh)`. -/
theorem logEulerLieDerivative_logTheta (v : Derivation k A A) (h : A) (hv : v f = 1 + f * h) :
    logEulerLieDerivative k f T v (logTheta k f T) =
      f • (h • logTheta k f T + ofRegular k f T (diff k h)) := by
  apply Subtype.ext
  rw [coe_logEulerLieDerivative, cartanFormula]
  change d k (formContraction k (logEulerDerivation k f T v) (theta k f T)) +
    formContraction k (logEulerDerivation k f T v) (d k (theta k f T)) = _
  have hd : reg (diff k (v f)) = diff k (algebraMap A T (v f)) := by
    rw [Forms.map_diff, IsScalarTower.coe_toAlgHom']
  rw [formContraction_logEulerDerivation_theta, d_theta, map_zero, add_zero, d_algebraMap, ← hd, hv]
  simp only [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Forms.map_toAlgHom_smul, Subalgebra.coe_smul, Subalgebra.coe_add, coe_ofRegular,
    logTheta, smul_add, ← self_smul_theta k f T]
  module

/-- A derivation normal modulo `f` has Euler Lie derivative taking all logarithmic forms into
`f L`. Blueprint: the first Euler identity in `lem:dr-euler`. -/
theorem logEulerLieDerivative_mem_logIdeal (v : Derivation k A A) (h : A) (hv : v f = 1 + f * h)
    (x : logForms k f T) : logEulerLieDerivative k f T v x ∈ logIdeal k f T := by
  have hreg (ω : Forms k A) : logEulerLieDerivative k f T v (ofRegular k f T ω) ∈ logIdeal k f T :=
    mem_logIdeal.2 ⟨_, (logEulerLieDerivative_ofRegular k f T v ω).symm⟩
  have htheta : logEulerLieDerivative k f T v (logTheta k f T) ∈ logIdeal k f T :=
    mem_logIdeal.2 ⟨_, (logEulerLieDerivative_logTheta k f T v h hv).symm⟩
  obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x
  have heq : logMk k f T (ω, η) = ofRegular k f T ω + logTheta k f T * ofRegular k f T η := by
    apply Subtype.ext
    simp only [coe_logMk, Subalgebra.coe_add, Subalgebra.coe_mul, coe_ofRegular, logTheta]
  rw [heq, map_add, logEulerLieDerivative_mul]
  exact add_mem (hreg ω) (add_mem (mul_mem_logIdeal_right htheta _)
    (mul_mem_logIdeal_left (hreg η) _))

/-- On `L/fL`, the differential and Euler contraction anticommute. The hypothesis is normality
modulo `f`, rather than equality `v(f) = 1`. Blueprint: `lem:dr-euler`. -/
theorem logQuotientEulerContraction_anticommute (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h)
    (x : logForms k f T ⧸ logIdeal k f T) :
    logQuotientD k f T (logQuotientEulerContraction k f T v x) +
      logQuotientEulerContraction k f T v (logQuotientD k f T x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [logQuotientEulerContraction_mk, logQuotientD_mk, logQuotientD_mk,
    logQuotientEulerContraction_mk, ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.mk_eq_zero _).2 (logEulerLieDerivative_mem_logIdeal k f T v h hv y)

/-- Left wedge by the class of `df/f` on `L/fL`. Blueprint: `lem:dr-euler`. -/
def logQuotientThetaWedge :
    (logForms k f T ⧸ logIdeal k f T) →ₗ[A] logForms k f T ⧸ logIdeal k f T :=
  (logIdeal k f T).mapQ _ (LinearMap.mulLeft A (logTheta k f T))
    (fun _ hx => mul_mem_logIdeal_left hx (logTheta k f T))

/-- Compute left wedge by the logarithmic form on a quotient representative. -/
@[simp]
theorem logQuotientThetaWedge_mk (x : logForms k f T) :
    logQuotientThetaWedge k f T (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (logTheta k f T * x) := rfl

/-- Left wedge by the logarithmic class squares to zero on the quotient. -/
@[simp]
theorem logQuotientThetaWedge_logQuotientThetaWedge
    (x : logForms k f T ⧸ logIdeal k f T) :
    logQuotientThetaWedge k f T (logQuotientThetaWedge k f T x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [logQuotientThetaWedge_mk, logQuotientThetaWedge_mk, ← mul_assoc,
    logTheta_mul_logTheta, zero_mul, Submodule.Quotient.mk_zero]

private theorem logD_logTheta_mul (x : logForms k f T) :
    logD k f T (logTheta k f T * x) = -(logTheta k f T * logD k f T x) := by
  apply Subtype.ext
  exact d_theta_mul k f T (x : Forms k T)

/-- The quotient differential anticommutes with left wedge by the logarithmic class. -/
theorem logQuotientD_logQuotientThetaWedge (x : logForms k f T ⧸ logIdeal k f T) :
    logQuotientD k f T (logQuotientThetaWedge k f T x) =
      -logQuotientThetaWedge k f T (logQuotientD k f T x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [logQuotientThetaWedge_mk, logQuotientD_mk, logQuotientD_mk,
    logQuotientThetaWedge_mk, logD_logTheta_mul, Submodule.Quotient.mk_neg]

/-- The contraction/wedge anticommutator on logarithmic forms is multiplication by `v(f)`. -/
theorem logEulerContraction_logTheta_mul_add (v : Derivation k A A) (x : logForms k f T) :
    logEulerContraction k f T v (logTheta k f T * x) +
      logTheta k f T * logEulerContraction k f T v x = v f • x := by
  apply Subtype.ext
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul,
    coe_logEulerContraction, logTheta]
  rw [formContraction_mul_of_mem_exteriorPower k _ (theta_mem_exteriorPower_one k f T),
    formContraction_logEulerDerivation_theta]
  simp only [Int.natCast_one, Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [neg_add_cancel_right, ← Algebra.smul_def, algebraMap_smul]

/-- Modulo `f L`, wedge by `df/f` and Euler contraction have anticommutator equal to the
identity, since `v(f)` is one modulo `f`. Blueprint: `lem:dr-euler`. -/
theorem logQuotientThetaWedge_euler_identity (v : Derivation k A A) (h : A) (hv : v f = 1 + f * h)
    (x : logForms k f T ⧸ logIdeal k f T) :
    logQuotientThetaWedge k f T (logQuotientEulerContraction k f T v x) +
      logQuotientEulerContraction k f T v (logQuotientThetaWedge k f T x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [logQuotientEulerContraction_mk, logQuotientThetaWedge_mk, logQuotientThetaWedge_mk,
    logQuotientEulerContraction_mk, ← Submodule.Quotient.mk_add, add_comm,
    logEulerContraction_logTheta_mul_add, hv, add_smul, one_smul, Submodule.Quotient.mk_add]
  have hz : Submodule.Quotient.mk ((f * h) • y) = (0 : logForms k f T ⧸ logIdeal k f T) := by
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact mem_logIdeal.2 ⟨h • y, (mul_smul _ _ _).symm⟩
  rw [hz, add_zero]

/-- Euler contraction takes a logarithmic form of degree `n + 1` to a regular form of degree `n`. -/
theorem formContraction_logEulerDerivation_mem_regularPower (v : Derivation k A A)
    {n : ℕ} {x : Forms k T}
    (hx : x ∈ logPower k f T (n + 1)) :
    formContraction k (logEulerDerivation k f T v) x ∈ regularPower k A T n := by
  obtain ⟨ω, hω, η, hη, hEq⟩ := mem_logPower_succ.1 hx
  have hp : diff k f * formContraction k v η ∈ ⋀[A]^n Ω[A⁄k] := by
    cases n with
    | zero => rw [formContraction_eq_zero k v hη, mul_zero]; exact zero_mem _
    | succ n => exact diff_mul_mem_exteriorPower k f (formContraction_mem_exteriorPower k v hη)
  have hg : f • formContraction k v ω + v f • η - diff k f * formContraction k v η ∈
      ⋀[A]^n Ω[A⁄k] :=
    sub_mem (add_mem (Submodule.smul_mem _ _ (formContraction_mem_exteriorPower k v hω))
      (Submodule.smul_mem _ _ hη)) hp
  rw [← hEq]
  have hc := formContraction_logEulerDerivation_logMk k f T v ω η
  rw [coe_logMk] at hc
  rw [hc]
  exact map_mem_regularPower k T hg

/-- The restricted Euler contraction lowers logarithmic degree by one. -/
theorem logEulerContraction_mem_logPower (v : Derivation k A A) {n : ℕ} {x : logForms k f T}
    (hx : (x : Forms k T) ∈ logPower k f T (n + 1)) :
    (logEulerContraction k f T v x : Forms k T) ∈ logPower k f T n :=
  regularPower_le_logPower k f T n (formContraction_logEulerDerivation_mem_regularPower k f T v hx)

/-- Euler contraction vanishes on degree-zero logarithmic forms. -/
theorem logEulerContraction_eq_zero (v : Derivation k A A) {x : logForms k f T}
    (hx : (x : Forms k T) ∈ logPower k f T 0) : logEulerContraction k f T v x = 0 := by
  apply Subtype.ext
  exact formContraction_eq_zero k _ (logPower_le_exteriorPower k f T 0 hx)

/-- The image of logarithmic forms of degree `n` in `L/fL`. This definition uses the actual
module quotient and introduces no choice of representatives. -/
def logQuotientPower (n : ℕ) : Submodule A (logForms k f T ⧸ logIdeal k f T) :=
  ((logPower k f T n).comap (logForms k f T).toSubmodule.subtype).map (logIdeal k f T).mkQ

/-- A homogeneous logarithmic quotient class has a homogeneous logarithmic representative. -/
theorem mem_logQuotientPower {n : ℕ} {x : logForms k f T ⧸ logIdeal k f T} :
    x ∈ logQuotientPower k f T n ↔ ∃ y : logForms k f T,
      (y : Forms k T) ∈ logPower k f T n ∧ Submodule.Quotient.mk y = x := by
  rfl

/-- A homogeneous logarithmic form gives a quotient class of the same degree. -/
theorem logQuotientMk_mem_logQuotientPower {n : ℕ} {x : logForms k f T}
    (hx : (x : Forms k T) ∈ logPower k f T n) :
    (Submodule.Quotient.mk x : logForms k f T ⧸ logIdeal k f T) ∈ logQuotientPower k f T n :=
  (mem_logQuotientPower k f T).2 ⟨x, hx, rfl⟩

/-- The quotient differential raises logarithmic degree by one. -/
theorem logQuotientD_mem_logQuotientPower {n : ℕ}
    {x : logForms k f T ⧸ logIdeal k f T} (hx : x ∈ logQuotientPower k f T n) :
    logQuotientD k f T x ∈ logQuotientPower k f T (n + 1) := by
  obtain ⟨y, hy, rfl⟩ := (mem_logQuotientPower k f T).1 hx
  rw [logQuotientD_mk]
  exact logQuotientMk_mem_logQuotientPower k f T (d_mem_logPower hy)

/-- Wedge by the logarithmic class raises quotient degree by one. -/
theorem logQuotientThetaWedge_mem_logQuotientPower {n : ℕ}
    {x : logForms k f T ⧸ logIdeal k f T} (hx : x ∈ logQuotientPower k f T n) :
    logQuotientThetaWedge k f T x ∈ logQuotientPower k f T (n + 1) := by
  obtain ⟨y, hy, rfl⟩ := (mem_logQuotientPower k f T).1 hx
  rw [logQuotientThetaWedge_mk]
  exact logQuotientMk_mem_logQuotientPower k f T (theta_mul_mem_logPower hy)

/-- Euler contraction lowers positive quotient degree by one. -/
theorem logQuotientEulerContraction_mem_logQuotientPower (v : Derivation k A A) {n : ℕ}
    {x : logForms k f T ⧸ logIdeal k f T} (hx : x ∈ logQuotientPower k f T (n + 1)) :
    logQuotientEulerContraction k f T v x ∈ logQuotientPower k f T n := by
  obtain ⟨y, hy, rfl⟩ := (mem_logQuotientPower k f T).1 hx
  rw [logQuotientEulerContraction_mk]
  exact logQuotientMk_mem_logQuotientPower k f T (logEulerContraction_mem_logPower k f T v hy)

/-- Euler contraction vanishes in quotient degree zero. -/
theorem logQuotientEulerContraction_eq_zero (v : Derivation k A A)
    {x : logForms k f T ⧸ logIdeal k f T} (hx : x ∈ logQuotientPower k f T 0) :
    logQuotientEulerContraction k f T v x = 0 := by
  obtain ⟨y, hy, rfl⟩ := (mem_logQuotientPower k f T).1 hx
  rw [logQuotientEulerContraction_mk, logEulerContraction_eq_zero k f T v hy,
    Submodule.Quotient.mk_zero]

/-- The quotient differential with its source and target degrees. -/
def logQuotientPowerD (n : ℕ) :
    logQuotientPower k f T n →ₗ[k] logQuotientPower k f T (n + 1) :=
  ((logQuotientD k f T).comp ((logQuotientPower k f T n).subtype.restrictScalars k)).codRestrict
    ((logQuotientPower k f T (n + 1)).restrictScalars k)
    fun x ↦ logQuotientD_mem_logQuotientPower k f T x.2

/-- The typed quotient differential is the restriction of the total differential. -/
@[simp]
theorem coe_logQuotientPowerD (n : ℕ) (x : logQuotientPower k f T n) :
    (logQuotientPowerD k f T n x : logForms k f T ⧸ logIdeal k f T) = logQuotientD k f T x := rfl

/-- Left wedge by the logarithmic class with its source and target degrees. -/
def logQuotientPowerThetaWedge (n : ℕ) :
    logQuotientPower k f T n →ₗ[A] logQuotientPower k f T (n + 1) :=
  ((logQuotientThetaWedge k f T).comp (logQuotientPower k f T n).subtype).codRestrict _
    fun x ↦ logQuotientThetaWedge_mem_logQuotientPower k f T x.2

/-- The typed quotient wedge operator is the restriction of the total one. -/
@[simp]
theorem coe_logQuotientPowerThetaWedge (n : ℕ) (x : logQuotientPower k f T n) :
    (logQuotientPowerThetaWedge k f T n x : logForms k f T ⧸ logIdeal k f T) =
      logQuotientThetaWedge k f T x := rfl

/-- Euler contraction with its source and target degrees. -/
def logQuotientPowerEulerContraction (v : Derivation k A A) (n : ℕ) :
    logQuotientPower k f T (n + 1) →ₗ[A] logQuotientPower k f T n :=
  ((logQuotientEulerContraction k f T v).comp
    (logQuotientPower k f T (n + 1)).subtype).codRestrict _
    fun x ↦ logQuotientEulerContraction_mem_logQuotientPower k f T v x.2

/-- The typed quotient contraction is the restriction of the total Euler contraction. -/
@[simp]
theorem coe_logQuotientPowerEulerContraction (v : Derivation k A A) (n : ℕ)
    (x : logQuotientPower k f T (n + 1)) :
    (logQuotientPowerEulerContraction k f T v n x : logForms k f T ⧸ logIdeal k f T) =
      logQuotientEulerContraction k f T v x := rfl

end OrlikSolomon.DeRham
