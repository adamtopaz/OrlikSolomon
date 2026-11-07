/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Differentiating and integrating polynomials with module coefficients

Integration needs only that every positive integer be a unit in the scalar ring.
No nonzero-ring assumption is made. Both operators are linear over that scalar ring,
so they apply when a differential on the coefficient module is only scalar-linear.

Blueprint: the coefficient calculations in `thm:dr-homotopy`.
-/

@[expose] public section
noncomputable section

namespace PolynomialModule

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

/-- Formal differentiation of a polynomial with module coefficients. -/
def derivative : PolynomialModule R M →ₗ[k] PolynomialModule R M :=
  (coeffLinearEquiv R k).symm.toLinearMap.comp
    ((Finsupp.lsum k fun n : ℕ => (n : k) • Finsupp.lsingle (n - 1)).comp
      (coeffLinearEquiv R k).toLinearMap)

@[simp]
theorem derivative_single (n : ℕ) (m : M) :
    derivative k R (single R n m) = single R (n - 1) ((n : k) • m) := by
  simp [derivative]

/-- The inverse scalar used to integrate a monomial, without assuming a nonzero ring. -/
def integrationScalar (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) : k :=
  ↑((h n).unit⁻¹)

/-- Coefficientwise integration with zero constant coefficient. -/
def integral (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    PolynomialModule R M →ₗ[k] PolynomialModule R M :=
  (coeffLinearEquiv R k).symm.toLinearMap.comp
    ((Finsupp.lsum k fun n : ℕ => integrationScalar k h n • Finsupp.lsingle (n + 1)).comp
      (coeffLinearEquiv R k).toLinearMap)

@[simp]
theorem integral_single (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (n : ℕ) (m : M) :
    integral k R h (single R n m) = single R (n + 1) (integrationScalar k h n • m) := by
  simp [integral]

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
theorem derivative_integral (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (p : PolynomialModule R M) :
    derivative k R (integral k R h p) = p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n m => simp [smul_smul]

/-- Integrating a derivative removes precisely the constant coefficient. -/
theorem integral_derivative (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (p : PolynomialModule R M) :
    integral k R h (derivative k R p) = p - single R 0 (p.coeff 0) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, coeff_add, Finsupp.add_apply, single_add]; abel
  | single n m =>
    cases n with
    | zero => simp
    | succ n => simp [smul_smul]

/-- Coefficientwise integration commutes with every scalar-linear coefficient map. -/
theorem mapCoefficients_integral {N : Type*} [AddCommGroup N] [Module R N] [Module k N]
    (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (f : M →ₗ[k] N) (p : PolynomialModule R M) :
    mapCoefficients k R f (integral k R h p) =
      integral k R h (mapCoefficients k R f p) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n m => simp

end PolynomialModule
