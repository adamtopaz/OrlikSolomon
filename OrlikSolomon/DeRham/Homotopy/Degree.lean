/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Homotopy.Polynomial

/-!
# The degrees of the polynomial-form decomposition

A form of degree `n + 1` decomposes into polynomials in coefficient forms of degree
`n + 1` and `n`. A form of degree zero has no `dX` component. These are the degreewise
restrictions of the total decomposition, with no smoothness assumption.

Blueprint: `lem:dr-polynomial-splitting`.
-/

@[expose] public section
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

namespace OrlikSolomon.DeRham

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- Base-changed coefficient forms of degree `n` are polynomials in forms of degree `n`. -/
@[no_expose]
def polynomialCoefficientPowerEquiv (n : ℕ) :
    ⋀[A[X]]^n (A[X] ⊗[A] Ω[A⁄k]) ≃ₗ[A[X]] PolynomialModule A (⋀[A]^n Ω[A⁄k]) :=
  (powerBaseChangeEquiv A Ω[A⁄k] A[X] n).symm ≪≫ₗ
    PolynomialModule.polynomialTensorProductLEquivPolynomialModule A (⋀[A]^n Ω[A⁄k])

/-- Forgetting the coefficient degree commutes with the coefficient-form equivalence. -/
theorem polynomialCoefficientPowerEquiv_coe (n : ℕ)
    (x : ⋀[A[X]]^n (A[X] ⊗[A] Ω[A⁄k])) :
    PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype (polynomialCoefficientPowerEquiv k A n x) =
      polynomialCoefficientFormsEquiv k A x := by
  obtain ⟨p, rfl⟩ := (polynomialCoefficientPowerEquiv k A n).symm.surjective x
  apply (polynomialCoefficientFormsEquiv k A).symm.injective
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Submodule.coe_add, hp, hq]
  | single m x =>
    simp only [PolynomialModule.map_single, polynomialCoefficientFormsEquiv_symm_apply,
      polynomialCoefficientPowerEquiv, LinearEquiv.symm_trans_apply,
      PolynomialModule.polynomialTensorProductLEquivPolynomialModule_symm_single,
      LinearEquiv.symm_symm, coe_powerBaseChangeEquiv,
      LinearMap.baseChange_tmul]

/-- The degreewise decomposition `Ω^(n+1)(A[X]) = Ω^(n+1)(A)[X] ⊕ dX ∧ Ω^n(A)[X]`.
Blueprint: `lem:dr-polynomial-splitting`. -/
@[no_expose]
def polynomialPowerDecomposition (n : ℕ) :
    ⋀[A[X]]^(n + 1) Ω[A[X]⁄k] ≃ₗ[A[X]]
      PolynomialModule A (⋀[A]^(n + 1) Ω[A⁄k]) × PolynomialModule A (⋀[A]^n Ω[A⁄k]) :=
  (polynomialCotangentSplitting k A).powerEquiv n ≪≫ₗ
    LinearEquiv.prodCongr (polynomialCoefficientPowerEquiv k A (n + 1))
      (polynomialCoefficientPowerEquiv k A n)

/-- The degreewise decomposition is the restriction of the decomposition of total forms. -/
theorem polynomialPowerDecomposition_coe (n : ℕ) (x : ⋀[A[X]]^(n + 1) Ω[A[X]⁄k]) :
    polynomialFormDecomposition k A x =
      (PolynomialModule.map A (⋀[A]^(n + 1) Ω[A⁄k]).subtype
        (polynomialPowerDecomposition k A n x).1,
       PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype
        (polynomialPowerDecomposition k A n x).2) := by
  rw [polynomialFormDecomposition_apply]
  apply Prod.ext
  · simpa [polynomialPowerDecomposition] using
      (polynomialCoefficientPowerEquiv_coe k A (n + 1)
      (exteriorPower.map (n + 1) (polynomialCotangentProjection k A) x)).symm
  · simpa [polynomialPowerDecomposition] using
      (polynomialCoefficientPowerEquiv_coe k A n
      (exteriorPower.map n (polynomialCotangentProjection k A)
        (powerContraction (polynomialCotangentCoordinate k A) n x))).symm

/-- Recombine the degreewise components inside the total algebra of forms. -/
theorem polynomialPowerDecomposition_symm_coe (n : ℕ)
    (p : PolynomialModule A (⋀[A]^(n + 1) Ω[A⁄k]) ×
      PolynomialModule A (⋀[A]^n Ω[A⁄k])) :
    ((polynomialPowerDecomposition k A n).symm p : Forms k A[X]) =
      polynomialFormInclusion k A (PolynomialModule.map A (⋀[A]^(n + 1) Ω[A⁄k]).subtype p.1) +
        diff k (X : A[X]) *
          polynomialFormInclusion k A (PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype p.2) := by
  apply (polynomialFormDecomposition k A).injective
  rw [polynomialPowerDecomposition_coe, LinearEquiv.apply_symm_apply,
    polynomialFormDecomposition_add]

/-- A degree-zero form has no component along `dX`. -/
theorem polynomialFormDecomposition_snd_eq_zero {x : Forms k A[X]}
    (hx : x ∈ ⋀[A[X]]^0 Ω[A[X]⁄k]) : (polynomialFormDecomposition k A x).2 = 0 := by
  rw [polynomialFormDecomposition_apply]
  change polynomialCoefficientFormsEquiv k A
    (ExteriorAlgebra.map (polynomialCotangentProjection k A)
      (exteriorContraction (polynomialCotangentCoordinate k A) x)) = 0
  rw [exteriorContraction_eq_zero_of_mem_exteriorPower_zero _ hx, map_zero, map_zero]

private theorem polynomialMap_coeff {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (p : PolynomialModule A M) (m : ℕ) :
    (PolynomialModule.map A f p).coeff m = f (p.coeff m) := by
  simp [PolynomialModule.map]

/-- Every coefficient of the first component has the degree of the original homogeneous form. -/
theorem polynomialFormDecomposition_fst_mem {n : ℕ} {x : Forms k A[X]}
    (hx : x ∈ ⋀[A[X]]^n Ω[A[X]⁄k]) (m : ℕ) :
    ((polynomialFormDecomposition k A x).1).coeff m ∈ ⋀[A]^n Ω[A⁄k] := by
  have hmap : ExteriorAlgebra.map (polynomialCotangentProjection k A) x ∈
      ⋀[A[X]]^n (A[X] ⊗[A] Ω[A⁄k]) := by
    simpa only [exteriorMap_self] using
      exteriorMap_mem_exteriorPower A[X] (polynomialCotangentProjection k A) hx
  rw [polynomialFormDecomposition_apply]
  change (polynomialCoefficientFormsEquiv k A
    (ExteriorAlgebra.map (polynomialCotangentProjection k A) x)).coeff m ∈ _
  rw [← polynomialCoefficientPowerEquiv_coe k A n ⟨_, hmap⟩, polynomialMap_coeff]
  exact Subtype.coe_prop _

/-- Every coefficient of the variable component has degree one less than the form. -/
theorem polynomialFormDecomposition_snd_mem {n : ℕ} {x : Forms k A[X]}
    (hx : x ∈ ⋀[A[X]]^(n + 1) Ω[A[X]⁄k]) (m : ℕ) :
    ((polynomialFormDecomposition k A x).2).coeff m ∈ ⋀[A]^n Ω[A⁄k] := by
  rw [polynomialPowerDecomposition_coe k A n ⟨x, hx⟩]
  change (PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype
    (polynomialPowerDecomposition k A n ⟨x, hx⟩).2).coeff m ∈ _
  rw [polynomialMap_coeff]
  exact Subtype.coe_prop _

/-- Including a polynomial of homogeneous coefficient forms preserves their exterior degree. -/
theorem polynomialFormInclusion_map_mem (n : ℕ)
    (p : PolynomialModule A (⋀[A]^n Ω[A⁄k])) :
    polynomialFormInclusion k A (PolynomialModule.map A (⋀[A]^n Ω[A⁄k]).subtype p) ∈
      ⋀[A[X]]^n Ω[A[X]⁄k] := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add]; exact add_mem hp hq
  | single m x =>
    rw [PolynomialModule.map_single, polynomialFormInclusion_single]
    exact Submodule.smul_mem _ _ (Forms.map_mem_exteriorPower _ x.2)

end OrlikSolomon.DeRham
