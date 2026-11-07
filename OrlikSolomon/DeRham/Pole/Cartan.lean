/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Localization

/-!
# Cartan calculus on the de Rham algebra

A derivation determines contraction through the universal property of Kähler differentials.
Its anticommutator with `d` is the Lie derivative, an ordinary derivation preserving degree.
All coefficient algebras are arbitrary commutative algebras; no smoothness, characteristic or
nonzero-ring hypothesis is used.

## Main definitions and results

* `formContraction`: contraction by a derivation, linear in both the form and the derivation.
* `formContraction_mul_of_mem_exteriorPower`: the signed Leibniz rule.
* `lieDerivative` and `cartanFormula`: the actual operator `dι + ιd`.
* `lieDerivative_mul` and `lieDerivative_mem_exteriorPower`: the ordinary Leibniz rule and
  preservation of degree.
* `Forms.map_formContraction` and `Forms.map_lieDerivative`: naturality for compatible vector
  fields along arbitrary maps of algebras.
* `localizedDerivation`, `map_formContraction_localizedDerivation` and
  `map_lieDerivative_localizedDerivation`: the extension of Cartan calculus to localizations.

Blueprint: `lem:dr-cartan`.
-/

@[expose] public section
noncomputable section

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]

/-- Contraction by a derivation: the functional sends `da` to `v(a)`. It is linear in the
vector field and linear over `A` on forms. Blueprint: `lem:dr-cartan`. -/
def formContraction : Derivation k A A →ₗ[A] Forms k A →ₗ[A] Forms k A :=
  exteriorContraction.comp
    (KaehlerDifferential.linearMapEquivDerivation (R := k) (S := A) (M := A)).symm.toLinearMap

/-- Contraction is the existing exterior contraction of the differential functional. -/
theorem formContraction_apply (v : Derivation k A A) (x : Forms k A) :
    formContraction k v x = exteriorContraction v.liftKaehlerDifferential x := rfl

/-- Scaling a derivation scales its contraction. -/
theorem formContraction_smul (a : A) (v : Derivation k A A) :
    formContraction k (a • v) = a • formContraction k v :=
  map_smul (formContraction k) a v

/-- Contraction annihilates functions. -/
@[simp]
theorem formContraction_algebraMap (v : Derivation k A A) (a : A) :
    formContraction k v (algebraMap A (Forms k A) a) = 0 :=
  exteriorContraction_algebraMap _ _

/-- Contraction annihilates the unit form. -/
@[simp]
theorem formContraction_one (v : Derivation k A A) :
    formContraction k v (1 : Forms k A) = 0 :=
  exteriorContraction_one _

/-- Contraction evaluates an exact one-form on the derivation. -/
@[simp]
theorem formContraction_diff (v : Derivation k A A) (a : A) :
    formContraction k v (diff k a) = algebraMap A (Forms k A) (v a) := by
  simp only [formContraction_apply, diff_apply, exteriorContraction_ι,
    Derivation.liftKaehlerDifferential_comp_D]

/-- Contraction against a left exact one-form has its signed product rule. -/
theorem formContraction_diff_mul (v : Derivation k A A) (a : A) (x : Forms k A) :
    formContraction k v (diff k a * x) =
      v a • x - diff k a * formContraction k v x := by
  simp only [formContraction_apply, diff_apply, exteriorContraction_ι_mul,
    Derivation.liftKaehlerDifferential_comp_D]

/-- The signed Leibniz rule for contraction, with the degree of the left factor.
Blueprint: `lem:dr-cartan`. -/
theorem formContraction_mul_of_mem_exteriorPower (v : Derivation k A A)
    {n : ℕ} {x : Forms k A} (hx : x ∈ ⋀[A]^n Ω[A⁄k]) (y : Forms k A) :
    formContraction k v (x * y) = formContraction k v x * y +
      (n : ℤ).negOnePow • (x * formContraction k v y) :=
  exteriorContraction_mul_of_mem_exteriorPower _ hx y

/-- Contraction lowers every positive degree by one. -/
theorem formContraction_mem_exteriorPower (v : Derivation k A A) {n : ℕ} {x : Forms k A}
    (hx : x ∈ ⋀[A]^(n + 1) Ω[A⁄k]) : formContraction k v x ∈ ⋀[A]^n Ω[A⁄k] :=
  exteriorContraction_mem_exteriorPower _ hx

/-- Contraction vanishes in degree zero. -/
theorem formContraction_eq_zero (v : Derivation k A A) {x : Forms k A}
    (hx : x ∈ ⋀[A]^0 Ω[A⁄k]) : formContraction k v x = 0 :=
  exteriorContraction_eq_zero_of_mem_exteriorPower_zero _ hx

/-- The Lie derivative is the anticommutator of `d` and contraction. It is only `k`-linear,
because its action on functions is the given derivation. Blueprint: `lem:dr-cartan`. -/
def lieDerivative (v : Derivation k A A) : Forms k A →ₗ[k] Forms k A :=
  (d k).comp ((formContraction k v).restrictScalars k) +
    ((formContraction k v).restrictScalars k).comp (d k)

/-- Cartan's formula holds for the constructed Lie derivative.
Blueprint: `lem:dr-cartan`. -/
theorem cartanFormula (v : Derivation k A A) (x : Forms k A) :
    lieDerivative k v x = d k (formContraction k v x) + formContraction k v (d k x) := rfl

/-- The Lie derivative of a function is its derivative along the vector field. -/
@[simp]
theorem lieDerivative_algebraMap (v : Derivation k A A) (a : A) :
    lieDerivative k v (algebraMap A (Forms k A) a) =
      algebraMap A (Forms k A) (v a) := by
  simp [cartanFormula]

/-- The Lie derivative of an exact one-form is the differential of the differentiated function. -/
@[simp]
theorem lieDerivative_diff (v : Derivation k A A) (a : A) :
    lieDerivative k v (diff k a) = diff k (v a) := by
  simp [cartanFormula]

/-- The Lie derivative annihilates the unit. -/
@[simp]
theorem lieDerivative_one (v : Derivation k A A) : lieDerivative k v (1 : Forms k A) = 0 := by
  simp [cartanFormula]

/-- The Lie derivative differentiates a scalar coefficient by the vector field. -/
theorem lieDerivative_smul (v : Derivation k A A) (a : A) (x : Forms k A) :
    lieDerivative k v (a • x) = v a • x + a • lieDerivative k v x := by
  simp only [cartanFormula, map_smul, d_smul, map_add, formContraction_diff_mul, smul_add]
  abel

/-- The Lie derivative differentiates a left exact one-form by `d(v(a))`, without a sign. -/
theorem lieDerivative_diff_mul (v : Derivation k A A) (a : A) (x : Forms k A) :
    lieDerivative k v (diff k a * x) =
      diff k (v a) * x + diff k a * lieDerivative k v x := by
  simp only [cartanFormula, formContraction_diff_mul, map_sub, d_smul, d_diff_mul, map_neg,
    mul_add]
  abel

private theorem lieDerivative_word_mul (v : Derivation k A A) (l : List A) (y : Forms k A) :
    lieDerivative k v (word (diff k) l * y) =
      lieDerivative k v (word (diff k) l) * y + word (diff k) l * lieDerivative k v y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, mul_assoc, lieDerivative_diff_mul, ih, mul_add, add_mul]
    abel

/-- The Lie derivative is an ordinary derivation on all forms, including mixed degrees.
Blueprint: `lem:dr-cartan`. -/
theorem lieDerivative_mul (v : Derivation k A A) (x y : Forms k A) :
    lieDerivative k v (x * y) = lieDerivative k v x * y + x * lieDerivative k v y := by
  induction x using Forms.induction with
  | word a l =>
    simp only [smul_mul_assoc, lieDerivative_smul, lieDerivative_word_mul, smul_add, add_mul]
    abel
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz]
    abel

/-- The Lie derivative preserves exterior degree, including degree zero. -/
theorem lieDerivative_mem_exteriorPower (v : Derivation k A A) {n : ℕ} {x : Forms k A}
    (hx : x ∈ ⋀[A]^n Ω[A⁄k]) : lieDerivative k v x ∈ ⋀[A]^n Ω[A⁄k] := by
  rw [cartanFormula]
  cases n with
  | zero =>
    rw [formContraction_eq_zero k v hx, map_zero, zero_add]
    exact formContraction_mem_exteriorPower k v (d_mem_exteriorPower k hx)
  | succ n =>
    exact add_mem (d_mem_exteriorPower k (formContraction_mem_exteriorPower k v hx))
      (formContraction_mem_exteriorPower k v (d_mem_exteriorPower k hx))

/-- The Lie derivative commutes with the de Rham differential. -/
theorem lieDerivative_d (v : Derivation k A A) (x : Forms k A) :
    lieDerivative k v (d k x) = d k (lieDerivative k v x) := by
  simp [cartanFormula]

/-- Rescaling a vector field adds the differential of its scalar coefficient to the Lie
operator. This is the form of Cartan's formula used by the logarithmic Euler vector field. -/
theorem lieDerivative_smul_derivation (v : Derivation k A A) (a : A) (x : Forms k A) :
    lieDerivative k (a • v) x =
      diff k a * formContraction k v x + a • lieDerivative k v x := by
  simp only [cartanFormula, formContraction_smul, LinearMap.smul_apply, d_smul, smul_add]
  abel

section Naturality

variable {B : Type*} [CommRing B] [Algebra k B]

private theorem map_formContraction_word (φ : A →ₐ[k] B)
    (v : Derivation k A A) (w : Derivation k B B) (h : ∀ a, w (φ a) = φ (v a)) (l : List A) :
    Forms.map φ (formContraction k v (word (diff k) l)) =
      formContraction k w (Forms.map φ (word (diff k) l)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, formContraction_diff_mul, map_sub, Forms.map_smul, map_mul,
      Forms.map_diff, h, ih]

/-- Compatible derivations give compatible contractions along an arbitrary algebra map. -/
theorem Forms.map_formContraction (φ : A →ₐ[k] B)
    (v : Derivation k A A) (w : Derivation k B B) (h : ∀ a, w (φ a) = φ (v a))
    (x : Forms k A) :
    Forms.map φ (formContraction k v x) = formContraction k w (Forms.map φ x) := by
  induction x using Forms.induction with
  | word a l =>
    simp only [_root_.map_smul, Forms.map_smul, map_formContraction_word k φ v w h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Compatible derivations give compatible Lie derivatives along an arbitrary algebra map. -/
theorem Forms.map_lieDerivative (φ : A →ₐ[k] B)
    (v : Derivation k A A) (w : Derivation k B B) (h : ∀ a, w (φ a) = φ (v a))
    (x : Forms k A) :
    Forms.map φ (lieDerivative k v x) = lieDerivative k w (Forms.map φ x) := by
  simp only [cartanFormula, map_add, Forms.map_d, Forms.map_formContraction k φ v w h]

end Naturality

section Localization

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]

/-- Extend a vector field to a localization by the existing differential localization API. -/
def localizedDerivation (M : Submonoid A) [IsLocalization M T] (v : Derivation k A A) :
    Derivation k T T :=
  extendDerivation T M ((Algebra.linearMap A T).compDer v)

/-- The extended vector field agrees with the original one on coefficient functions. -/
@[simp]
theorem localizedDerivation_algebraMap (M : Submonoid A) [IsLocalization M T]
    (v : Derivation k A A) (a : A) :
    localizedDerivation k T M v (algebraMap A T a) = algebraMap A T (v a) := by
  simp [localizedDerivation]

/-- Contraction commutes with the inclusion into any localization. No flatness assumption on
another map of algebras is involved. Blueprint: `lem:dr-cartan`. -/
theorem map_formContraction_localizedDerivation (M : Submonoid A) [IsLocalization M T]
    (v : Derivation k A A) (x : Forms k A) :
    Forms.map (IsScalarTower.toAlgHom k A T) (formContraction k v x) =
      formContraction k (localizedDerivation k T M v)
        (Forms.map (IsScalarTower.toAlgHom k A T) x) :=
  Forms.map_formContraction k _ v _ (localizedDerivation_algebraMap k T M v) x

/-- The Lie derivative commutes with the inclusion into any localization.
Blueprint: `lem:dr-cartan`. -/
theorem map_lieDerivative_localizedDerivation (M : Submonoid A) [IsLocalization M T]
    (v : Derivation k A A) (x : Forms k A) :
    Forms.map (IsScalarTower.toAlgHom k A T) (lieDerivative k v x) =
      lieDerivative k (localizedDerivation k T M v)
        (Forms.map (IsScalarTower.toAlgHom k A T) x) :=
  Forms.map_lieDerivative k _ v _ (localizedDerivation_algebraMap k T M v) x

end Localization

end OrlikSolomon.DeRham
