/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import OrlikSolomon.DeRham.Exterior.Basic

/-!
# Base change of exterior powers

Mathlib's `ExteriorAlgebra.baseChangeEquiv` is an algebra equivalence
`S ⊗_A ⋀_A M ≃ ⋀_S (S ⊗_A M)` on the total exterior algebra. This file restricts it to homogeneous
components, which needs no flatness because `⋀^n` is a direct summand of the exterior algebra over
any ring, and states it for any base change in the sense of `IsBaseChange`, which is the form that
applies to localizations and polynomial extensions.

## Main results

Blueprint `lem:dr-exterior`:

* `OrlikSolomon.DeRham.isBaseChange_powerMap`: if `M → M'` is a base change along `A → S`, then so
  is `⋀_A^n M → ⋀_S^n M'`. `OrlikSolomon.DeRham.isBaseChange_exteriorMap` is the total form, and
  `OrlikSolomon.DeRham.isLocalizedModule_powerMap` is the form for a localization.
* `OrlikSolomon.DeRham.powerBaseChangeEquiv`: `S ⊗_A ⋀_A^n M ≃ ⋀_S^n (S ⊗_A M)`, with the formula
  `powerBaseChangeEquiv_tmul`, the inverse `powerBaseChangeEquiv_symm_ιMulti`, the comparison
  `coe_powerBaseChangeEquiv` with the total form, and `powerBaseChangeEquiv_naturality`.
-/

@[expose] public section

open scoped TensorProduct

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι ιMulti)

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

variable (S : Type*) [CommRing S] [Algebra A S]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module S M'] [IsScalarTower A S M']

/-- `x ↦ 1 ⊗ x` followed by Mathlib's base change equivalence for exterior algebras is
`exteriorMap` of `m ↦ 1 ⊗ m`. -/
theorem baseChangeEquiv_one_tmul (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.baseChangeEquiv A M S (1 ⊗ₜ x) =
      exteriorMap S (TensorProduct.mk A S M 1) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
    have h : (1 : S) ⊗ₜ[A] (algebraMap A (ExteriorAlgebra A M) a) =
        algebraMap A S a • (1 : S ⊗[A] ExteriorAlgebra A M) := by
      rw [Algebra.algebraMap_eq_smul_one (A := ExteriorAlgebra A M), TensorProduct.tmul_smul,
        Algebra.TensorProduct.one_def, algebraMap_smul]
    rw [h, map_smul, map_one, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A S (ExteriorAlgebra S _) a,
      Algebra.algebraMap_eq_smul_one (A := ExteriorAlgebra S _)]
  | ι m => simpa using ExteriorAlgebra.baseChangeEquiv_apply A M S 1 m
  | mul a b ha hb =>
    have h : (1 : S) ⊗ₜ[A] (a * b) = (1 ⊗ₜ[A] a) * (1 ⊗ₜ[A] b) := by simp
    rw [h, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]

/-- If `g : M → M'` exhibits `M'` as the base change of `M` along `A → S`, then
`⋀_A M → ⋀_S M'` exhibits `⋀_S M'` as the base change of `⋀_A M`.

Blueprint: `lem:dr-exterior`, for the total exterior algebra. -/
theorem isBaseChange_exteriorMap {g : M →ₗ[A] M'} (hg : IsBaseChange S g) :
    IsBaseChange S (exteriorMap S g).toLinearMap := by
  refine IsBaseChange.of_equiv
    ((ExteriorAlgebra.baseChangeEquiv A M S).toLinearEquiv ≪≫ₗ
      (exteriorCongr hg.equiv).toLinearEquiv) fun x => ?_
  change ExteriorAlgebra.map hg.equiv.toLinearMap
    (ExteriorAlgebra.baseChangeEquiv A M S (1 ⊗ₜ x)) = exteriorMap S g x
  rw [baseChangeEquiv_one_tmul]
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι m => simp
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The image of the map underlying a base change spans the target. -/
private theorem span_range_of_isBaseChange {g : M →ₗ[A] M'} (hg : IsBaseChange S g) :
    Submodule.span S (Set.range g) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  obtain ⟨t, rfl⟩ := hg.equiv.surjective y
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    rw [hg.equiv_tmul]
    exact Submodule.smul_mem _ s (Submodule.subset_span ⟨m, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- If `g : M → M'` exhibits `M'` as the base change of `M` along `A → S`, then
`⋀_A^n M → ⋀_S^n M'` exhibits `⋀_S^n M'` as the base change of `⋀_A^n M`. This applies to
localizations through `isLocalizedModule_iff_isBaseChange`.

No flatness is used: `⋀^n` is a direct summand of the exterior algebra over any ring.

Blueprint: `lem:dr-exterior`. -/
theorem isBaseChange_powerMap {g : M →ₗ[A] M'} (hg : IsBaseChange S g) (n : ℕ) :
    IsBaseChange S (powerMap S g n) := by
  let Ψ : S ⊗[A] ⋀[A]^n M →ₗ[S] ⋀[S]^n M' := (powerMap S g n).liftBaseChange S
  have hΨ : ∀ s x, Ψ (s ⊗ₜ x) = s • powerMap S g n x := fun s x => by simp [Ψ]
  have hinj : Function.Injective Ψ := by
    have hcomp : (⋀[S]^n M').subtype ∘ₗ Ψ =
        (isBaseChange_exteriorMap S hg).equiv.toLinearMap ∘ₗ
          ((⋀[A]^n M).subtype.baseChange S) := by
      ext x
      simp [Ψ]
    have hret : Function.Injective ((⋀[A]^n M).subtype.baseChange S) := by
      refine Function.LeftInverse.injective (g := (exteriorProj n).baseChange S) fun t => ?_
      induction t using TensorProduct.inductionOn with
      | tmul s x => simp
      | add a b ha hb => simp only [map_add, ha, hb]
    have h := (isBaseChange_exteriorMap S hg).equiv.injective.comp hret
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp, ← hcomp, LinearMap.coe_comp] at h
    exact Function.Injective.of_comp h
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← exteriorPower.ιMulti_span_of_span S n M' (span_range_of_isBaseChange S hg),
      Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨m, rfl⟩ := Set.range_subset_range_iff_exists_comp.mp ha
    exact ⟨1 ⊗ₜ exteriorPower.ιMulti A n m, by simp [hΨ]⟩
  exact IsBaseChange.of_equiv
    (LinearEquiv.ofBijective Ψ (show Function.Bijective Ψ from ⟨hinj, hsurj⟩))
    fun x => (hΨ 1 x).trans (one_smul _ _)

/-- If `g : M → M'` localizes `M` at a submonoid `T` of `A`, and `S` is the localization of `A` at
`T`, then `⋀_A^n M → ⋀_S^n M'` localizes `⋀_A^n M` at `T`. The kernel of a localization map is
therefore known here: an element dies when a member of `T` kills it.

Blueprint: `lem:dr-exterior`, in the form used by `lem:dr-localization`. -/
theorem isLocalizedModule_powerMap (T : Submonoid A) [IsLocalization T S] {g : M →ₗ[A] M'}
    [IsLocalizedModule T g] (n : ℕ) : IsLocalizedModule T (powerMap S g n) :=
  (isLocalizedModule_iff_isBaseChange T S _).2
    (isBaseChange_powerMap S ((isLocalizedModule_iff_isBaseChange T S g).1 inferInstance) n)

variable (A M) in
/-- Base change of exterior powers, `S ⊗_A ⋀_A^n M ≃ ⋀_S^n (S ⊗_A M)`. It sends
`s ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to `s (1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ)`.

Mathlib's `ExteriorAlgebra.baseChangeEquiv` is the total form of this equivalence, and
`coe_powerBaseChangeEquiv` says that this one is its restriction.

Blueprint: `lem:dr-exterior`. -/
noncomputable def powerBaseChangeEquiv (n : ℕ) :
    S ⊗[A] ⋀[A]^n M ≃ₗ[S] ⋀[S]^n (S ⊗[A] M) :=
  (isBaseChange_powerMap S (TensorProduct.isBaseChange A M S) n).equiv

@[simp]
theorem powerBaseChangeEquiv_tmul (n : ℕ) (s : S) (x : ⋀[A]^n M) :
    powerBaseChangeEquiv A M S n (s ⊗ₜ x) = s • powerMap S (TensorProduct.mk A S M 1) n x :=
  IsBaseChange.equiv_tmul _ s x

/-- The base change of exterior powers is the restriction of the base change of exterior algebras.
-/
theorem coe_powerBaseChangeEquiv (n : ℕ) (t : S ⊗[A] ⋀[A]^n M) :
    (powerBaseChangeEquiv A M S n t : ExteriorAlgebra S (S ⊗[A] M)) =
      ExteriorAlgebra.baseChangeEquiv A M S ((⋀[A]^n M).subtype.baseChange S t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s x =>
    rw [powerBaseChangeEquiv_tmul, LinearMap.baseChange_tmul, ← mul_one s, ← smul_eq_mul,
      ← TensorProduct.smul_tmul', map_smul, baseChangeEquiv_one_tmul]
    simp
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]

/-- The inverse of base change on a word: the scalars come out as a product.

Blueprint: `lem:dr-exterior`. -/
theorem powerBaseChangeEquiv_symm_ιMulti {n : ℕ} (s : Fin n → S) (m : Fin n → M) :
    (powerBaseChangeEquiv A M S n).symm (exteriorPower.ιMulti S n fun i => s i ⊗ₜ m i) =
      (∏ i, s i) ⊗ₜ exteriorPower.ιMulti A n m := by
  rw [LinearEquiv.symm_apply_eq, powerBaseChangeEquiv_tmul, powerMap_ιMulti,
    ← AlternatingMap.map_smul_univ]
  congr 1
  ext i
  simp [TensorProduct.smul_tmul']

/-- Base change of exterior powers is natural in the module. -/
theorem powerBaseChangeEquiv_naturality {N : Type*} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (n : ℕ) (t : S ⊗[A] ⋀[A]^n M) :
    powerBaseChangeEquiv A N S n ((exteriorPower.map n f).baseChange S t) =
      exteriorPower.map n (f.baseChange S) (powerBaseChangeEquiv A M S n t) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s x =>
    have key : powerMap S (TensorProduct.mk A S N 1) n (exteriorPower.map n f x) =
        exteriorPower.map n (f.baseChange S) (powerMap S (TensorProduct.mk A S M 1) n x) := by
      have h : (powerMap S (TensorProduct.mk A S N 1) n) ∘ₗ exteriorPower.map n f =
          ((exteriorPower.map n (f.baseChange S)).restrictScalars A) ∘ₗ
            powerMap S (TensorProduct.mk A S M 1) n := by
        ext m
        simp [Function.comp_def]
      exact LinearMap.congr_fun h x
    simp [key]

end OrlikSolomon.DeRham
