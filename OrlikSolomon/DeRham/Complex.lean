/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import OrlikSolomon.DeRham.Complex.Differential
public import OrlikSolomon.DeRham.Complex.Forms
public import OrlikSolomon.DeRham.Complex.Functoriality
public import OrlikSolomon.DeRham.Complex.Polynomial
public import OrlikSolomon.DeRham.Complex.Presentation

/-!
# The de Rham complex

This is the module to import for the de Rham dg algebra of a commutative algebra `A` over a
commutative ring `k`, with no smoothness hypothesis and no basis of differentials. It imports the
files under `DeRham/Complex`, whose headers list their results, and it packages the differential as
a cochain complex of `k`-modules.

## Summary of the design

Forms are the total algebra `Forms k A`, which is `ExteriorAlgebra A Ω[A⁄k]`. A form of degree `n`
is an element with `x ∈ ⋀[A]^n Ω[A⁄k]`. The differential `d k` is a `k`-linear operator on the total
algebra, and it is not `A`-linear. A map `φ : A →ₐ[k] A'` induces a `k`-algebra map `Forms.map φ`,
semilinear over `φ`. The words `a₀ • word (diff k) [a₁, …, aₙ]` are the normal form, and
`Forms.induction` and `Forms.induction_exteriorPower` are the induction principles on them.

Every statement about `d` and `Forms.map` should go through `d_smul_word`, `d_smul`, `d_mul` and
`Forms.map_smul_word`. The construction of `d` is hidden, and no presentation of `A` is involved.

## Summary of the blueprint

Blueprint `def:dr-forms`: `OrlikSolomon.DeRham.Forms`, `OrlikSolomon.DeRham.diff`,
`OrlikSolomon.DeRham.span_word_diff`, `OrlikSolomon.DeRham.Forms.induction_exteriorPower`.

Blueprint `lem:dr-polynomial-dga`: `OrlikSolomon.DeRham.d_smul_word_X`,
`OrlikSolomon.DeRham.finite_support_pderiv_smul`, `OrlikSolomon.DeRham.eq_d_of_smul_word_X`, with
`d_d` and `d_mul_of_mem_exteriorPower` for the polynomial ring, and Mathlib's
`KaehlerDifferential.mvPolynomialBasis`.

Blueprint `lem:dr-presentation`: `OrlikSolomon.DeRham.differentialIdealPower`,
`OrlikSolomon.DeRham.d_mem_differentialIdeal`,
`OrlikSolomon.DeRham.Forms.map_eq_zero_iff_of_surjective`, `OrlikSolomon.DeRham.quotientEquiv`,
`OrlikSolomon.DeRham.quotientPowerEquiv` and `OrlikSolomon.DeRham.presentationEquiv_dQuotient`.

Blueprint `def:dr-complex`: `OrlikSolomon.DeRham.d`, `OrlikSolomon.DeRham.powerD` and
`OrlikSolomon.DeRham.complex`.

Blueprint `thm:dr-dga`: `OrlikSolomon.DeRham.d_smul_word`, `OrlikSolomon.DeRham.d_d`,
`OrlikSolomon.DeRham.d_mul_of_mem_exteriorPower`,
`OrlikSolomon.DeRham.mul_comm_of_mem_exteriorPower`, `OrlikSolomon.DeRham.eq_d_of_smul_word`,
`OrlikSolomon.DeRham.Forms.map_smul_word`, `OrlikSolomon.DeRham.Forms.map_d`,
`OrlikSolomon.DeRham.Forms.map_id` and `OrlikSolomon.DeRham.Forms.map_map`.

## Main definitions of this file

* `OrlikSolomon.DeRham.complex k A`: the de Rham complex, a cochain complex of `k`-modules.
* `OrlikSolomon.DeRham.complexMap φ`: the chain map of a `k`-algebra map.
* `OrlikSolomon.DeRham.complexFunctor k`: the functor from commutative `k`-algebras.
-/

@[expose] public section

open CategoryTheory

namespace OrlikSolomon.DeRham

universe u v

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {A' A'' : Type v} [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A'']

/-- The de Rham complex of `A` over `k`: the modules `⋀[A]^n Ω[A⁄k]` and the differentials
`powerD k A n`. It is a complex of `k`-modules, since the differentials are not `A`-linear. The
wedge product is the multiplication of `Forms k A`.

Blueprint: `def:dr-complex`. -/
noncomputable def complex : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (⋀[A]^n Ω[A⁄k]))
    (fun n => ModuleCat.ofHom (powerD k A n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, powerD_comp_powerD]
      rfl)

@[simp]
theorem complex_X (n : ℕ) : (complex k A).X n = ModuleCat.of k (⋀[A]^n Ω[A⁄k]) :=
  rfl

@[simp]
theorem complex_d (n : ℕ) : (complex k A).d n (n + 1) = ModuleCat.ofHom (powerD k A n) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (⋀[A]^n Ω[A⁄k]))
    (fun n => ModuleCat.ofHom (powerD k A n)) n

variable {k A}

/-- The chain map of the de Rham complex induced by a `k`-algebra map, which is `Forms.mapPower` in
each degree.

Blueprint: `thm:dr-dga`. -/
noncomputable def complexMap (φ : A →ₐ[k] A') : complex k A ⟶ complex k A' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Forms.mapPower φ n)) fun n => by
    simp only [complex_d, complex_X]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    exact congrArg ModuleCat.ofHom (LinearMap.ext fun x => (Forms.mapPower_powerD φ n x).symm)

@[simp]
theorem complexMap_f (φ : A →ₐ[k] A') (n : ℕ) :
    (complexMap φ).f n = ModuleCat.ofHom (Forms.mapPower φ n) :=
  rfl

/-- The identity induces the identity.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem complexMap_id : complexMap (AlgHom.id k A) = 𝟙 (complex k A) := by
  ext n : 2
  rw [complexMap_f, Forms.mapPower_id]
  rfl

/-- `complexMap` respects composition.

Blueprint: `thm:dr-dga`. -/
theorem complexMap_comp (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') :
    complexMap (ψ.comp φ) = complexMap φ ≫ complexMap ψ := by
  ext n : 2
  rw [HomologicalComplex.comp_f, complexMap_f, complexMap_f, complexMap_f, Forms.mapPower_comp]
  rfl

variable (k) in
/-- The de Rham complex, as a functor from commutative `k`-algebras to cochain complexes of
`k`-modules. Mathlib's `CommAlgCat` is the covariant convention, so that a map `A → A'` of algebras
goes to a chain map in the same direction.

Blueprint: `thm:dr-dga`. -/
noncomputable def complexFunctor : CommAlgCat.{v} k ⥤ CochainComplex (ModuleCat.{v} k) ℕ where
  obj A := complex k A
  map f := complexMap f.hom
  map_id _ := complexMap_id
  map_comp f g := complexMap_comp g.hom f.hom

@[simp]
theorem complexFunctor_obj (B : CommAlgCat.{v} k) : (complexFunctor k).obj B = complex k B :=
  rfl

@[simp]
theorem complexFunctor_map {B C : CommAlgCat.{v} k} (f : B ⟶ C) :
    (complexFunctor k).map f = complexMap f.hom :=
  rfl

end OrlikSolomon.DeRham
