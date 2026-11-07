/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.DeRham.Cohomology
public import OrlikSolomon.DeRham.Homotopy.Degree
public import OrlikSolomon.DeRham.Homotopy.Differential

/-!
# Polynomial homotopy invariance of de Rham cohomology

For a commutative `k`-algebra `A`, integration of the `dX` component gives the
homotopy `dK + Kd = 1 - inc ∘ ev₀`, provided positive integers are units in `k`.
There is no smoothness or nonzero-ring hypothesis.

## Main definitions and results

* `polynomialEvaluationAtZero`: the canonical evaluation map of `k`-algebras.
* `polynomialHomotopy` and `polynomialHomotopy_identity`: the explicit integration operator and
  the equation `dK + Kd = id - inc ∘ ev₀`.
* `polynomialHomotopy_mem_exteriorPower` and `polynomialHomotopy_eq_zero`: the homotopy lowers
  degree by one and vanishes in degree zero.
* `polynomialCohomologyEquiv` and `bijective_cohomologyMap_C`: inclusion of constants and
  evaluation at zero are inverse on cohomology.
* `polynomialCohomologyEquiv_mem_degree_iff`: the equivalence preserves and reflects degree.

Blueprint: `thm:dr-homotopy` and `lem:dr-polynomial-splitting`.
-/

@[expose] public section
noncomputable section
open Polynomial

namespace OrlikSolomon.DeRham

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- Evaluation at zero, as a map of `k`-algebras. -/
def polynomialEvaluationAtZero : A[X] →ₐ[k] A :=
  (Polynomial.aeval (R := A) (0 : A)).restrictScalars k

/-- Evaluation retracts the inclusion of constants. -/
@[simp]
theorem polynomialEvaluationAtZero_comp_C :
    (polynomialEvaluationAtZero k A).comp (Polynomial.CAlgHom (R := k) (A := A)) =
      AlgHom.id k A := by
  ext a
  simp [polynomialEvaluationAtZero]

/-- Evaluation of a polynomial form discards all positive powers of the variable. -/
@[simp]
theorem map_polynomialEvaluationAtZero_inclusion (p : PolynomialModule A (Forms k A)) :
    Forms.map (polynomialEvaluationAtZero k A) (polynomialFormInclusion k A p) = p.coeff 0 := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, PolynomialModule.coeff_add, Finsupp.add_apply]
  | single n x =>
    rw [polynomialFormInclusion_single, Forms.map_smul, Forms.map_map,
      polynomialEvaluationAtZero_comp_C, Forms.map_id]
    cases n <;> simp [polynomialEvaluationAtZero]

/-- The variable differential vanishes under evaluation at zero. -/
theorem map_polynomialEvaluationAtZero_diff_X :
    Forms.map (polynomialEvaluationAtZero k A) (diff k (X : A[X])) = 0 := by
  simp [polynomialEvaluationAtZero]

/-- Integrate the variable component of a polynomial form, with zero integration constant.
Blueprint: the explicit homotopy in `thm:dr-homotopy`. -/
def polynomialHomotopy (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    Forms k A[X] →ₗ[k] Forms k A[X] :=
  (polynomialFormInclusion k A).restrictScalars k ∘ₗ
    (coefficientIntegral k A h) ∘ₗ
      (LinearMap.snd k _ _).comp ((polynomialFormDecomposition k A).toLinearMap.restrictScalars k)

/-- The homotopy is the integral of the `dX` component. -/
theorem polynomialHomotopy_apply (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (x : Forms k A[X]) :
    polynomialHomotopy k A h x = polynomialFormInclusion k A
      (coefficientIntegral k A h (polynomialFormDecomposition k A x).2) := by rfl

/-- On `α + dX ∧ β`, the homotopy is `Iβ`. -/
@[simp]
theorem polynomialHomotopy_components (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (a b : PolynomialModule A (Forms k A)) :
    polynomialHomotopy k A h
      (polynomialFormInclusion k A a + diff k (X : A[X]) * polynomialFormInclusion k A b) =
      polynomialFormInclusion k A (coefficientIntegral k A h b) := by
  rw [polynomialHomotopy_apply, polynomialFormDecomposition_inclusion_add_diff_X_mul]

/-- A form coming entirely from coefficient differentials has zero homotopy. -/
@[simp]
theorem polynomialHomotopy_inclusion (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule A (Forms k A)) :
    polynomialHomotopy k A h (polynomialFormInclusion k A p) = 0 := by
  simpa using polynomialHomotopy_components k A h p 0

/-- The homotopy integrates the coefficient of a left factor `dX`. -/
@[simp]
theorem polynomialHomotopy_diff_X_mul_inclusion (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (p : PolynomialModule A (Forms k A)) :
    polynomialHomotopy k A h (diff k (X : A[X]) * polynomialFormInclusion k A p) =
      polynomialFormInclusion k A (coefficientIntegral k A h p) := by
  simpa using polynomialHomotopy_components k A h 0 p

/-- The primitive of the polynomial-variable differential is the variable itself. -/
@[simp]
theorem polynomialHomotopy_diff_X (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    polynomialHomotopy k A h (diff k (X : A[X])) =
      algebraMap A[X] (Forms k A[X]) X := by
  have hK := polynomialHomotopy_diff_X_mul_inclusion k A h
    (PolynomialModule.single A 0 (1 : Forms k A))
  simpa [Algebra.smul_def] using hK

/-- The integration homotopy squares to zero. -/
@[simp]
theorem polynomialHomotopy_polynomialHomotopy (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (x : Forms k A[X]) :
    polynomialHomotopy k A h (polynomialHomotopy k A h x) = 0 := by
  rw [polynomialHomotopy_apply k A h x, polynomialHomotopy_inclusion]

/-- The integration homotopy lowers exterior degree by one. -/
theorem polynomialHomotopy_mem_exteriorPower (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    {n : ℕ} {x : Forms k A[X]} (hx : x ∈ ⋀[A[X]]^(n + 1) Ω[A[X]⁄k]) :
    polynomialHomotopy k A h x ∈ ⋀[A[X]]^n Ω[A[X]⁄k] := by
  rw [polynomialHomotopy_apply, polynomialPowerDecomposition_coe k A n ⟨x, hx⟩]
  let p := (polynomialPowerDecomposition k A n ⟨x, hx⟩).2
  have hmap : coefficientIntegral k A h
      (PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype p) =
      PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype (coefficientIntegral k A h p) := by
    simpa only [mapCoefficients_restrictScalars] using
      (mapCoefficients_coefficientIntegral k A h
        ((⋀[A]^n Ω[A⁄k]).subtype.restrictScalars k) p).symm
  change polynomialFormInclusion k A
    (coefficientIntegral k A h (PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype p)) ∈ _
  rw [hmap]
  exact polynomialFormInclusion_map_mem k A n _

/-- The homotopy vanishes on forms of degree zero. -/
theorem polynomialHomotopy_eq_zero (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    {x : Forms k A[X]} (hx : x ∈ ⋀[A[X]]^0 Ω[A[X]⁄k]) :
    polynomialHomotopy k A h x = 0 := by
  rw [polynomialHomotopy_apply, polynomialFormDecomposition_snd_eq_zero k A hx, map_zero,
    map_zero]

/-- Integration gives the homotopy between the identity and evaluation followed by inclusion.
Blueprint: the actual homotopy equation in `thm:dr-homotopy`. -/
theorem polynomialHomotopy_identity (h : ∀ n : ℕ, IsUnit (n + 1 : k)) (x : Forms k A[X]) :
    d k (polynomialHomotopy k A h x) + polynomialHomotopy k A h (d k x) =
      x - Forms.map ((Polynomial.CAlgHom (R := k) (A := A)).comp
        (polynomialEvaluationAtZero k A)) x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (polynomialFormDecomposition k A).symm.surjective x
  rw [polynomialFormDecomposition_symm_apply, polynomialHomotopy_components,
    d_polynomialFormInclusion, d_polynomialForm_components, polynomialHomotopy_components,
    ← Forms.map_map]
  simp only [map_add, map_mul, map_polynomialEvaluationAtZero_inclusion,
    map_polynomialEvaluationAtZero_diff_X, zero_mul, add_zero,
    coefficientDerivative_coefficientIntegral, map_sub]
  rw [polynomialCoefficientD_coefficientIntegral, coefficientIntegral_coefficientDerivative,
    map_sub, polynomialFormInclusion_single]
  simp only [pow_zero, one_smul]
  abel

/-- Inclusion and evaluation are inverse on de Rham cohomology. The inverse homotopy is the
coefficientwise integration operator above. Blueprint: `thm:dr-homotopy`. -/
def polynomialCohomologyEquiv (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    Cohomology k A ≃ₐ[k] Cohomology k A[X] :=
  AlgEquiv.ofAlgHom (Cohomology.map (Polynomial.CAlgHom (R := k) (A := A)))
    (Cohomology.map (polynomialEvaluationAtZero k A)) (by
      rw [← Cohomology.map_comp]
      have hK := Cohomology.map_eq_map_of_homotopy (polynomialHomotopy k A h)
        (φ := AlgHom.id k A[X])
        (ψ := (Polynomial.CAlgHom (R := k) (A := A)).comp (polynomialEvaluationAtZero k A))
        (fun x ↦ by simpa only [Forms.map_id, AlgHom.id_apply] using
          (polynomialHomotopy_identity k A h x).symm)
      rw [← hK, Cohomology.map_id]) (by
      rw [← Cohomology.map_comp, polynomialEvaluationAtZero_comp_C, Cohomology.map_id])

/-- The canonical cohomology equivalence is induced by inclusion of constants. -/
@[simp]
theorem polynomialCohomologyEquiv_apply (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (x : Cohomology k A) :
    polynomialCohomologyEquiv k A h x =
      Cohomology.map (Polynomial.CAlgHom (R := k) (A := A)) x := rfl

/-- Evaluation at zero is the inverse cohomology map. -/
@[simp]
theorem polynomialCohomologyEquiv_symm_apply (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (x : Cohomology k A[X]) :
    (polynomialCohomologyEquiv k A h).symm x =
      Cohomology.map (polynomialEvaluationAtZero k A) x := rfl

/-- The polynomial cohomology equivalence preserves and reflects cohomological degree. -/
theorem polynomialCohomologyEquiv_mem_degree_iff (h : ∀ n : ℕ, IsUnit (n + 1 : k))
    (n : ℕ) (x : Cohomology k A) :
    polynomialCohomologyEquiv k A h x ∈ Cohomology.degree k A[X] n ↔
      x ∈ Cohomology.degree k A n := by
  constructor
  · intro hx
    have he := Cohomology.map_mem_degree (polynomialEvaluationAtZero k A) hx
    simpa only [← polynomialCohomologyEquiv_symm_apply k A h,
      AlgEquiv.symm_apply_apply] using he
  · exact Cohomology.map_mem_degree _

/-- Polynomial extension induces a bijection on de Rham cohomology whenever positive integers
are units in the coefficient ring. No smoothness assumption is needed.
Blueprint: `thm:dr-homotopy`. -/
theorem bijective_cohomologyMap_C (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    Function.Bijective (Cohomology.map (Polynomial.CAlgHom (R := k) (A := A))) :=
  (polynomialCohomologyEquiv k A h).bijective

end OrlikSolomon.DeRham
