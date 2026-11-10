/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coefficient extension of maps between free modules

A map between free modules extends along a coefficient algebra by applying the coefficient
map to each column. Mathlib's `Finsupp.linearCombination` supplies the extended linear map.
The extension commutes with coefficient maps and composition, so extending inverse maps
gives an equivalence. It is faithful when the coefficient map is injective.

The label types may be infinite, and neither coefficient semiring need be nontrivial.
Blueprint: the matrix coefficient-extension step of S05 (`thm:s05`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe r s u v w

variable (R : Type r) [CommSemiring R] (A : Type s) [CommSemiring A] [Algebra R A]
  {ι : Type u} {κ : Type v} {ν : Type w}

/-- Extend a free-module map by applying the coefficient algebra map to its columns.
No injectivity, finite-rank or nontriviality hypothesis is required. -/
def coefficientExtendLinearMap (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) :
    (ι →₀ A) →ₗ[A] (κ →₀ A) :=
  Finsupp.linearCombination A fun i ↦
    Finsupp.mapRange.linearMap (Algebra.linearMap R A) (f (Finsupp.single i 1))

/-- An extended matrix has the coefficient image of each original column. -/
@[simp]
theorem coefficientExtendLinearMap_single (f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (i : ι) (a : A) :
    coefficientExtendLinearMap R A f (Finsupp.single i a) =
      a • Finsupp.mapRange.linearMap (Algebra.linearMap R A)
        (f (Finsupp.single i 1)) :=
  Finsupp.linearCombination_single A a i

/-- Coefficient extension commutes with the actual coefficient map on every vector. -/
theorem coefficientExtendLinearMap_mapRange (f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (x : ι →₀ R) :
    coefficientExtendLinearMap R A f
        (Finsupp.mapRange.linearMap (Algebra.linearMap R A) x) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A) (f x) := by
  have he : ((coefficientExtendLinearMap R A f).restrictScalars R).comp
      (Finsupp.mapRange.linearMap (Algebra.linearMap R A)) =
      (Finsupp.mapRange.linearMap (Algebra.linearMap R A)).comp f := by
    apply Finsupp.lhom_ext
    intro i c
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Algebra.linearMap_apply, coefficientExtendLinearMap_single]
    rw [show Finsupp.single i c = c • Finsupp.single i (1 : R) by simp, map_smul]
    simp only [← Finsupp.mapRange.linearMap_apply, map_smul,
      IsScalarTower.algebraMap_smul]
  exact LinearMap.congr_fun he x

/-- Extending the identity matrix gives the identity over the coefficient algebra. -/
@[simp]
theorem coefficientExtendLinearMap_id :
    coefficientExtendLinearMap R A (LinearMap.id : (ι →₀ R) →ₗ[R] (ι →₀ R)) =
      LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i a
  simp

/-- Extending a product of matrices equals composing their extensions. -/
theorem coefficientExtendLinearMap_comp (g : (κ →₀ R) →ₗ[R] (ν →₀ R))
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) :
    coefficientExtendLinearMap R A (g.comp f) =
      (coefficientExtendLinearMap R A g).comp (coefficientExtendLinearMap R A f) := by
  apply Finsupp.lhom_ext
  intro i a
  simp only [coefficientExtendLinearMap_single, LinearMap.comp_apply, map_smul,
    coefficientExtendLinearMap_mapRange]

/-- Extending a free-module equivalence extends its inverse as well. -/
def coefficientExtendLinearEquiv (f : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (ι →₀ A) ≃ₗ[A] (κ →₀ A) :=
  LinearEquiv.ofLinearMap (coefficientExtendLinearMap R A f.toLinearMap)
    (coefficientExtendLinearMap R A f.symm.toLinearMap)
    (by rw [← coefficientExtendLinearMap_comp, LinearEquiv.comp_symm,
      coefficientExtendLinearMap_id])
    (by rw [← coefficientExtendLinearMap_comp, LinearEquiv.symm_comp,
      coefficientExtendLinearMap_id])

/-- Forgetting the extended equivalence gives exactly the extended linear map. -/
@[simp]
theorem coefficientExtendLinearEquiv_toLinearMap (f : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (coefficientExtendLinearEquiv R A f).toLinearMap =
      coefficientExtendLinearMap R A f.toLinearMap := rfl

/-- Extending the original inverse gives the inverse of the extended equivalence. -/
@[simp]
theorem coefficientExtendLinearEquiv_symm (f : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    coefficientExtendLinearEquiv R A f.symm = (coefficientExtendLinearEquiv R A f).symm := rfl

/-- The extended equivalence commutes with the actual coefficient map on every vector. -/
theorem coefficientExtendLinearEquiv_mapRange (f : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (x : ι →₀ R) :
    coefficientExtendLinearEquiv R A f
        (Finsupp.mapRange.linearMap (Algebra.linearMap R A) x) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A) (f x) :=
  coefficientExtendLinearMap_mapRange R A f.toLinearMap x

/-- Coefficient extension preserves the literal free-module label maps. -/
@[simp]
theorem coefficientExtendLinearMap_lmapDomain (f : ι → κ) :
    coefficientExtendLinearMap R A (Finsupp.lmapDomain R R f) = Finsupp.lmapDomain A A f := by
  apply Finsupp.lhom_ext
  intro i a
  simp

/-- Extending scalar multiplication applies the coefficient algebra map to the scalar. -/
@[simp]
theorem coefficientExtendLinearMap_smul_id (a : R) :
    coefficientExtendLinearMap R A (a • (LinearMap.id : (ι →₀ R) →ₗ[R] (ι →₀ R))) =
      algebraMap R A a • LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i b
  simp [Algebra.smul_def, mul_comm]

/-- An injective coefficient map detects equality of the original free-module maps. -/
theorem coefficientExtendLinearMap_injective
    (hRA : Function.Injective (algebraMap R A)) :
    Function.Injective (coefficientExtendLinearMap R A (ι := ι) (κ := κ)) := by
  intro f g he
  apply Finsupp.lhom_ext
  intro i r
  have hc := congrArg (fun h : (ι →₀ A) →ₗ[A] (κ →₀ A) ↦ h (Finsupp.single i 1)) he
  simp only [coefficientExtendLinearMap_single, one_smul] at hc
  have hcol : f (Finsupp.single i 1) = g (Finsupp.single i 1) := by
    ext j
    apply hRA
    exact congrArg (fun x : κ →₀ A ↦ x j) hc
  rw [show Finsupp.single i r = r • Finsupp.single i (1 : R) by simp,
    map_smul, map_smul, hcol]

/-- The identity free-module equivalence extends to the identity. -/
@[simp]
theorem coefficientExtendLinearEquiv_refl :
    coefficientExtendLinearEquiv R A (LinearEquiv.refl R (ι →₀ R)) =
      LinearEquiv.refl A (ι →₀ A) := by
  apply LinearEquiv.toLinearMap_injective
  exact coefficientExtendLinearMap_id R A

/-- Coefficient extension commutes with composition of free-module equivalences. -/
theorem coefficientExtendLinearEquiv_trans (f : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (g : (κ →₀ R) ≃ₗ[R] (ν →₀ R)) :
    coefficientExtendLinearEquiv R A (f.trans g) =
      (coefficientExtendLinearEquiv R A f).trans (coefficientExtendLinearEquiv R A g) := by
  apply LinearEquiv.ext
  intro x
  change coefficientExtendLinearMap R A (g.toLinearMap.comp f.toLinearMap) x = _
  rw [coefficientExtendLinearMap_comp]
  rfl

/-- Coefficient extension respects the group multiplication of free-module automorphisms. -/
theorem coefficientExtendLinearEquiv_mul (f g : (ι →₀ R) ≃ₗ[R] (ι →₀ R)) :
    coefficientExtendLinearEquiv R A (f * g) =
      coefficientExtendLinearEquiv R A f * coefficientExtendLinearEquiv R A g := by
  apply LinearEquiv.ext
  intro x
  change coefficientExtendLinearMap R A (f.toLinearMap.comp g.toLinearMap) x = _
  rw [coefficientExtendLinearMap_comp]
  rfl

/-- An injective coefficient map detects equality of the original equivalences. -/
theorem coefficientExtendLinearEquiv_injective
    (hRA : Function.Injective (algebraMap R A)) :
    Function.Injective (coefficientExtendLinearEquiv R A (ι := ι) (κ := κ)) := by
  intro f g he
  apply LinearEquiv.toLinearMap_injective
  apply coefficientExtendLinearMap_injective R A hRA
  exact congrArg LinearEquiv.toLinearMap he

end OrlikSolomon.HyperplaneGT
