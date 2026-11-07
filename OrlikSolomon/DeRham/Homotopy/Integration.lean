/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Differentiating and integrating polynomials with module coefficients

Integration needs only that every positive integer be a unit in the scalar ring.
No nonzero-ring assumption is made. Both operators are linear over that scalar ring,
so they apply when a differential on the coefficient module is only scalar-linear.

## Main definitions and results

* `mapCoefficients` and `mapCoefficients_restrictScalars`: apply a scalar-linear coefficient map
  and compare it with Mathlib's polynomial-module map when the scalar actions are compatible.
* `coefficientDerivative`, `coefficientIntegral` and `integrationScalar`: differentiate and
  integrate, using the inverse of each positive integer.
* `coefficientDerivative_coeff`, `coefficientIntegral_coeff_zero` and
  `coefficientIntegral_coeff_succ`: formulas for every coefficient.
* `coefficientDerivative_coefficientIntegral` and `coefficientIntegral_coefficientDerivative`:
  the two fundamental identities of coefficientwise integration.
* `mapCoefficients_coefficientIntegral`: integration commutes with coefficient-linear maps.

Blueprint: the coefficient calculations in `thm:dr-homotopy`.
-/

@[expose] public section
noncomputable section
open PolynomialModule

namespace OrlikSolomon.DeRham

variable (k R : Type*) [CommRing k] [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module k M]

/-- Apply a scalar-linear map to every polynomial coefficient. -/
def mapCoefficients {N : Type*} [AddCommGroup N] [Module R N] [Module k N]
    (f : M →ₗ[k] N) :
    PolynomialModule R M →ₗ[k] PolynomialModule R N :=
  (coeffLinearEquiv R k).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp (coeffLinearEquiv R k).toLinearMap)

@[simp]
theorem mapCoefficients_single {N : Type*} [AddCommGroup N] [Module R N] [Module k N]
    (f : M →ₗ[k] N) (n : ℕ) (m : M) :
    mapCoefficients k R f (single R n m) = single R n (f m) := by
  simp [mapCoefficients]

/-- Restricting the scalars of a coefficient map agrees with Mathlib's polynomial-module map. -/
theorem mapCoefficients_restrictScalars {N : Type*} [AddCommGroup N] [Module R N] [Module k N]
    [Algebra k R] [IsScalarTower k R M] [IsScalarTower k R N]
    (f : M →ₗ[R] N) (p : PolynomialModule R M) :
    mapCoefficients k R (f.restrictScalars k) p = PolynomialModule.map R f p := rfl

/-- Formal differentiation of a polynomial with module coefficients. -/
def coefficientDerivative : PolynomialModule R M →ₗ[k] PolynomialModule R M :=
  (coeffLinearEquiv R k).symm.toLinearMap.comp
    ((Finsupp.lsum k fun n : ℕ => (n : k) • Finsupp.lsingle (n - 1)).comp
      (coeffLinearEquiv R k).toLinearMap)

@[simp]
theorem coefficientDerivative_single (n : ℕ) (m : M) :
    coefficientDerivative k R (single R n m) = single R (n - 1) ((n : k) • m) := by
  simp [coefficientDerivative]

/-- The coefficient of degree `m` in the formal derivative is `(m + 1)` times the next
coefficient. -/
theorem coefficientDerivative_coeff (p : PolynomialModule R M) (m : ℕ) :
    (coefficientDerivative k R p).coeff m = ((m + 1 : ℕ) : k) • p.coeff (m + 1) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, ha, hb, smul_add]
  | single n x =>
    rw [coefficientDerivative_single]
    cases n with
    | zero => simp
    | succ n =>
      by_cases h : n = m
      · subst h; simp
      · simp [h]

/-- The inverse scalar used to integrate a monomial, without assuming a nonzero ring. -/
def integrationScalar (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) : k :=
  ↑((h n).unit⁻¹)

/-- Coefficientwise integration with zero constant coefficient. -/
def coefficientIntegral (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    PolynomialModule R M →ₗ[k] PolynomialModule R M :=
  (coeffLinearEquiv R k).symm.toLinearMap.comp
    ((Finsupp.lsum k fun n : ℕ => integrationScalar k h n • Finsupp.lsingle (n + 1)).comp
      (coeffLinearEquiv R k).toLinearMap)

@[simp]
theorem coefficientIntegral_single (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) (m : M) :
    coefficientIntegral k R h (single R n m) = single R (n + 1) (integrationScalar k h n • m) := by
  simp [coefficientIntegral]

/-- The constant coefficient of the integral is zero. -/
@[simp]
theorem coefficientIntegral_coeff_zero (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule R M) : (coefficientIntegral k R h p).coeff 0 = 0 := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, hp, hq,
      add_zero]
  | single n x => simp

/-- The coefficient of degree `m + 1` in the integral is the previous coefficient divided by
`m + 1`, using its specified inverse unit. -/
theorem coefficientIntegral_coeff_succ (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule R M) (m : ℕ) :
    (coefficientIntegral k R h p).coeff (m + 1) = integrationScalar k h m • p.coeff m := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, ha, hb, smul_add]
  | single n x =>
    rw [coefficientIntegral_single]
    by_cases hnm : n = m
    · subst hnm; simp
    · simp [hnm]

@[simp]
theorem mul_integrationScalar (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) :
    (n + 1 : k) * integrationScalar k h n = 1 := by
  simpa only [integrationScalar, IsUnit.unit_spec] using Units.mul_inv ((h n).unit)

@[simp]
theorem integrationScalar_mul (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) :
    integrationScalar k h n * (n + 1 : k) = 1 := by
  rw [mul_comm, mul_integrationScalar]

/-- Integrating a constant uses the scalar one. -/
@[simp]
theorem integrationScalar_zero (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    integrationScalar k h 0 = 1 := by
  simpa only [Nat.cast_zero, zero_add, one_mul] using mul_integrationScalar k h 0

/-- Differentiating the integral recovers the original polynomial. -/
@[simp]
theorem coefficientDerivative_coefficientIntegral (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule R M) :
    coefficientDerivative k R (coefficientIntegral k R h p) = p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n m => simp [smul_smul]

/-- Integrating a derivative removes precisely the constant coefficient. -/
theorem coefficientIntegral_coefficientDerivative (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule R M) :
    coefficientIntegral k R h (coefficientDerivative k R p) = p - single R 0 (p.coeff 0) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, coeff_add, Finsupp.add_apply, single_add]; abel
  | single n m =>
    cases n with
    | zero => simp
    | succ n => simp [smul_smul]

/-- Coefficientwise integration commutes with every scalar-linear coefficient map. -/
theorem mapCoefficients_coefficientIntegral {N : Type*} [AddCommGroup N] [Module R N] [Module k N]
    (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (f : M →ₗ[k] N) (p : PolynomialModule R M) :
    mapCoefficients k R f (coefficientIntegral k R h p) =
      coefficientIntegral k R h (mapCoefficients k R f p) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n m => simp

end OrlikSolomon.DeRham
