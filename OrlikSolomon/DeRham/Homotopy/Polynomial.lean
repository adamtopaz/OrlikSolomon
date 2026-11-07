/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import OrlikSolomon.DeRham.Complex
public import OrlikSolomon.DeRham.Exterior.BaseChange

/-!
# Splitting polynomial forms along the new variable

The differentials of `A[X]` over `k` split into the differentials coming from `A`
and the free line on `dX`. Both algebras are arbitrary commutative algebras; no
smoothness or nonzero-ring hypothesis is used.

Blueprint: `lem:dr-polynomial-splitting`.
-/

@[expose] public section
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

namespace PolynomialModule

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The tensor corresponding to a monomial with a module coefficient. -/
@[simp]
theorem polynomialTensorProductLEquivPolynomialModule_symm_single (n : ℕ) (x : M) :
    (polynomialTensorProductLEquivPolynomialModule R M).symm (single R n x) =
      ((X : R[X]) ^ n) ⊗ₜ[R] x := by
  change eval X (map R[X] (TensorProduct.mk R R[X] M 1) (single R n x)) = _
  simp [eval_single, TensorProduct.smul_tmul']

end PolynomialModule

namespace OrlikSolomon.DeRham

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- The differentials coming from the coefficient algebra, extended to `A[X]`. -/
def polynomialCotangentInclusion : A[X] ⊗[A] Ω[A⁄k] →ₗ[A[X]] Ω[A[X]⁄k] :=
  mapBaseChange k A A[X]

/-- Differentiation in the polynomial variable, as a functional on one-forms. -/
def polynomialCotangentCoordinate : Ω[A[X]⁄k] →ₗ[A[X]] A[X] :=
  (polynomialEquiv A).toLinearMap.comp (KaehlerDifferential.map k A A[X] A[X])

/-- The polynomial-variable differential has coordinate one. -/
@[simp]
theorem polynomialCotangentCoordinate_D_X :
    polynomialCotangentCoordinate k A (D k A[X] X) = 1 := by
  simp [polynomialCotangentCoordinate]

/-- Extending coefficient differentials to a polynomial ring is injective. -/
theorem polynomialCotangentInclusion_injective :
    Function.Injective (polynomialCotangentInclusion k A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A A[X] x).mp hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  simpa only [hy0, map_zero] using hy.symm

/-- Coefficient differentials are exactly the one-forms with zero variable coordinate. -/
theorem range_polynomialCotangentInclusion :
    LinearMap.range (polynomialCotangentInclusion k A) =
      LinearMap.ker (polynomialCotangentCoordinate k A) := by
  rw [polynomialCotangentInclusion, range_mapBaseChange]
  ext x
  change KaehlerDifferential.map k A A[X] A[X] x = 0 ↔
    polynomialEquiv A (KaehlerDifferential.map k A A[X] A[X] x) = 0
  exact (polynomialEquiv A).map_eq_zero_iff.symm

private def polynomialCotangentRangeEquiv :
    (A[X] ⊗[A] Ω[A⁄k]) ≃ₗ[A[X]] LinearMap.range (polynomialCotangentInclusion k A) :=
  LinearEquiv.ofInjective _ (polynomialCotangentInclusion_injective k A)

/-- Removing the `dX` component and identifying the result with coefficient differentials. -/
@[no_expose]
def polynomialCotangentProjection : Ω[A[X]⁄k] →ₗ[A[X]] A[X] ⊗[A] Ω[A⁄k] :=
  (polynomialCotangentRangeEquiv k A).symm.toLinearMap.comp
    ((LinearMap.id - (polynomialCotangentCoordinate k A).smulRight (D k A[X] X)).codRestrict
      (LinearMap.range (polynomialCotangentInclusion k A)) fun x ↦ by
        rw [range_polynomialCotangentInclusion]
        change polynomialCotangentCoordinate k A
          (x - polynomialCotangentCoordinate k A x • D k A[X] X) = 0
        simp)

/-- The coefficient projection recovers a coefficient one-form. -/
@[simp]
theorem polynomialCotangentProjection_inclusion (x : A[X] ⊗[A] Ω[A⁄k]) :
    polynomialCotangentProjection k A (polynomialCotangentInclusion k A x) = x := by
  apply (polynomialCotangentRangeEquiv k A).injective
  apply Subtype.ext
  have hz : polynomialCotangentCoordinate k A (polynomialCotangentInclusion k A x) = 0 := by
    rw [← LinearMap.mem_ker, ← range_polynomialCotangentInclusion]
    exact LinearMap.mem_range_self _ _
  change ((polynomialCotangentRangeEquiv k A)
    ((polynomialCotangentRangeEquiv k A).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  change polynomialCotangentInclusion k A x -
    polynomialCotangentCoordinate k A (polynomialCotangentInclusion k A x) • D k A[X] X =
      polynomialCotangentInclusion k A x
  simp only [hz, zero_smul, sub_zero]

/-- Inclusion of the coefficient projection subtracts the variable component. -/
theorem polynomialCotangentInclusion_projection (x : Ω[A[X]⁄k]) :
    polynomialCotangentInclusion k A (polynomialCotangentProjection k A x) =
      x - polynomialCotangentCoordinate k A x • D k A[X] X := by
  exact congrArg Subtype.val ((polynomialCotangentRangeEquiv k A).apply_symm_apply _)

/-- One-forms split as coefficient differentials and the line on `dX`. -/
theorem polynomialCotangentSplitting :
    IsLineSplitting (D k A[X] X) (polynomialCotangentCoordinate k A)
      (polynomialCotangentInclusion k A) (polynomialCotangentProjection k A) where
  apply_self := polynomialCotangentCoordinate_D_X k A
  retract_incl := polynomialCotangentProjection_inclusion k A
  incl_retract := polynomialCotangentInclusion_projection k A

/-- Exterior forms on extended coefficient differentials are polynomials in forms on `A`. -/
@[no_expose]
def polynomialCoefficientFormsEquiv :
    ExteriorAlgebra A[X] (A[X] ⊗[A] Ω[A⁄k]) ≃ₗ[A[X]] PolynomialModule A (Forms k A) :=
  (ExteriorAlgebra.baseChangeEquiv A Ω[A⁄k] A[X]).toLinearEquiv.symm ≪≫ₗ
    PolynomialModule.polynomialTensorProductLEquivPolynomialModule A (Forms k A)

/-- Reconstruct a coefficient form from its polynomial coefficients. -/
theorem polynomialCoefficientFormsEquiv_symm_apply (p : PolynomialModule A (Forms k A)) :
    (polynomialCoefficientFormsEquiv k A).symm p =
      ExteriorAlgebra.baseChangeEquiv A Ω[A⁄k] A[X]
        ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule
          A (Forms k A)).symm p) := by
  rfl

/-- Include a polynomial with coefficients in forms on `A` among forms on `A[X]`. -/
@[no_expose]
def polynomialFormInclusion : PolynomialModule A (Forms k A) →ₗ[A[X]] Forms k A[X] :=
  (ExteriorAlgebra.map (polynomialCotangentInclusion k A)).toLinearMap.comp
    (polynomialCoefficientFormsEquiv k A).symm.toLinearMap

/-- Every polynomial form decomposes uniquely as `α(X) + dX ∧ β(X)`.
Blueprint: `lem:dr-polynomial-splitting`. -/
@[no_expose]
def polynomialFormDecomposition :
    Forms k A[X] ≃ₗ[A[X]] PolynomialModule A (Forms k A) × PolynomialModule A (Forms k A) :=
  (polynomialCotangentSplitting k A).exteriorEquiv ≪≫ₗ
    LinearEquiv.prodCongr (polynomialCoefficientFormsEquiv k A)
      (polynomialCoefficientFormsEquiv k A)

/-- The two components are projection to coefficient differentials, before and after contraction
with the polynomial-variable coordinate. -/
theorem polynomialFormDecomposition_apply (x : Forms k A[X]) :
    polynomialFormDecomposition k A x =
      (polynomialCoefficientFormsEquiv k A
        (ExteriorAlgebra.map (polynomialCotangentProjection k A) x),
       polynomialCoefficientFormsEquiv k A
        (ExteriorAlgebra.map (polynomialCotangentProjection k A)
          (exteriorContraction (polynomialCotangentCoordinate k A) x))) := by
  rfl

/-- Recombine the coefficient and variable components of a polynomial form. -/
@[simp]
theorem polynomialFormDecomposition_symm_apply
    (p : PolynomialModule A (Forms k A) × PolynomialModule A (Forms k A)) :
    (polynomialFormDecomposition k A).symm p =
      polynomialFormInclusion k A p.1 + diff k (X : A[X]) * polynomialFormInclusion k A p.2 := by
  rfl

/-- Splitting a form assembled from its two components recovers those components. -/
@[simp]
theorem polynomialFormDecomposition_add
    (a b : PolynomialModule A (Forms k A)) :
    polynomialFormDecomposition k A
      (polynomialFormInclusion k A a + diff k (X : A[X]) * polynomialFormInclusion k A b) =
      (a, b) := by
  rw [← polynomialFormDecomposition_symm_apply k A (a, b), LinearEquiv.apply_symm_apply]

private theorem polynomialFormInclusion_baseChange (x : Forms k A) :
    ExteriorAlgebra.map (polynomialCotangentInclusion k A)
      (ExteriorAlgebra.baseChangeEquiv A Ω[A⁄k] A[X] (1 ⊗ₜ[A] x)) =
      Forms.map (Polynomial.CAlgHom (R := k) (A := A)) x := by
  rw [baseChangeEquiv_one_tmul, ← exteriorMap_self, exteriorMap_comp]
  have h : (polynomialCotangentInclusion k A).restrictScalars A ∘ₗ
      TensorProduct.mk A A[X] Ω[A⁄k] 1 = KaehlerDifferential.map k k A A[X] := by
    ext m
    simp [polynomialCotangentInclusion]
  rw [h, ← Forms.map_toAlgHom k A A[X]]
  rfl

/-- A monomial with form coefficient `ω` includes as `X^n` times the pullback of `ω`. -/
@[simp]
theorem polynomialFormInclusion_single (n : ℕ) (x : Forms k A) :
    polynomialFormInclusion k A (PolynomialModule.single A n x) =
      (X : A[X]) ^ n • Forms.map (Polynomial.CAlgHom (R := k) (A := A)) x := by
  change ExteriorAlgebra.map (polynomialCotangentInclusion k A)
    (ExteriorAlgebra.baseChangeEquiv A Ω[A⁄k] A[X]
      ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule A (Forms k A)).symm
        (PolynomialModule.single A n x))) = _
  rw [PolynomialModule.polynomialTensorProductLEquivPolynomialModule_symm_single]
  have h : ((X : A[X]) ^ n) ⊗ₜ[A] x =
      (X : A[X]) ^ n • ((1 : A[X]) ⊗ₜ[A] x) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, map_smul, polynomialFormInclusion_baseChange]

end OrlikSolomon.DeRham
