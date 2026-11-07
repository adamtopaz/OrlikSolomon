/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Log.Basic

/-!
# The pole filtration

For a principal localization `T` of `A` at `f`, the pole filtration consists of the images
`f⁻ᵐ Lⁿ` of logarithmic forms. Each stage is a subcomplex, and the stages increase and exhaust
the forms on `T`. No regularity or smoothness hypothesis is needed for these statements.

## Main definitions and results

* `OrlikSolomon.DeRham.poleForms`: the total module `f⁻ᵐ L`.
* `OrlikSolomon.DeRham.poleFiltration`: its homogeneous degree `n` part `f⁻ᵐ Lⁿ`.
* `OrlikSolomon.DeRham.poleForms_monotone`, `OrlikSolomon.DeRham.poleFiltration_monotone`,
  `OrlikSolomon.DeRham.iSup_poleForms` and `OrlikSolomon.DeRham.iSup_poleFiltration`: increasing
  and exhaustive pole bounds, in total degree and in each homogeneous degree.
* `OrlikSolomon.DeRham.logPoleEquiv`: multiplication by `f⁻ᵐ` identifies `L` with its pole stage.
* `OrlikSolomon.DeRham.d_invSelf_pow_smul_eq_theta`: the differential in logarithmic coordinates.
* `OrlikSolomon.DeRham.d_mem_poleForms` and `OrlikSolomon.DeRham.d_mem_poleFiltration`: each stage
  is stable under `d`, with actual restrictions `poleD` and `polePowerD`.

Blueprint: `def:dr-pole-filtration`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open IsLocalization.Away (invSelf)

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- Multiplication of logarithmic forms by `f⁻ᵐ`, as a map to localized forms. -/
noncomputable def logPoleMap (m : ℕ) : logForms k f T →ₗ[A] Forms k T :=
  (DistribSMul.toLinearMap A (Forms k T) ((invSelf f : T) ^ m)).comp
    (logForms k f T).toSubmodule.subtype

@[simp]
theorem logPoleMap_apply (m : ℕ) (x : logForms k f T) :
    logPoleMap k f T m x = (invSelf f : T) ^ m • (x : Forms k T) := rfl

/-- The total module of forms with pole order at most `m`, using logarithmic numerators.

Blueprint: `def:dr-pole-filtration`. -/
noncomputable def poleForms (m : ℕ) : Submodule A (Forms k T) :=
  LinearMap.range (logPoleMap k f T m)

theorem mem_poleForms {m : ℕ} {x : Forms k T} :
    x ∈ poleForms k f T m ↔
      ∃ ξ ∈ logForms k f T, (invSelf f : T) ^ m • ξ = x := by
  simp only [poleForms, LinearMap.mem_range, logPoleMap_apply, Subtype.exists, exists_prop]

/-- The degree `n` part `f⁻ᵐ Lⁿ` of the pole filtration.

Blueprint: `def:dr-pole-filtration`. -/
noncomputable def poleFiltration (m n : ℕ) : Submodule A (Forms k T) :=
  (logPower k f T n).map (DistribSMul.toLinearMap A (Forms k T) ((invSelf f : T) ^ m))

theorem mem_poleFiltration {m n : ℕ} {x : Forms k T} :
    x ∈ poleFiltration k f T m n ↔
      ∃ ξ ∈ logPower k f T n, (invSelf f : T) ^ m • ξ = x := by
  rfl

@[simp]
theorem poleForms_zero : poleForms k f T 0 = (logForms k f T).toSubmodule := by
  ext x
  simp only [mem_poleForms, pow_zero, one_smul, exists_eq_right]
  rfl

@[simp]
theorem poleFiltration_zero (n : ℕ) : poleFiltration k f T 0 n = logPower k f T n := by
  ext x
  simp only [mem_poleFiltration, pow_zero, one_smul, exists_eq_right]

/-- Clearing the denominator in the pole map, without assuming injectivity of `A → T`. -/
theorem self_pow_smul_invSelf_pow_smul (m : ℕ) (x : Forms k T) :
    (f ^ m) • ((invSelf f : T) ^ m • x) = x := by
  rw [← algebraMap_smul T (f ^ m), map_pow, smul_smul, ← mul_pow,
    IsLocalization.Away.mul_invSelf, one_pow, one_smul]

theorem logPoleMap_injective (m : ℕ) : Function.Injective (logPoleMap k f T m) := by
  intro x y h
  apply Subtype.ext
  have he := congrArg (fun z : Forms k T => (f ^ m) • z) h
  simpa only [logPoleMap_apply, self_pow_smul_invSelf_pow_smul] using he

/-- Multiplying a logarithmic numerator by `f` raises the allowed pole bound by one. -/
theorem invSelf_pow_succ_smul_self_smul (m : ℕ) (x : Forms k T) :
    (invSelf f : T) ^ (m + 1) • (f • x) = (invSelf f : T) ^ m • x := by
  rw [← algebraMap_smul T f, smul_smul, pow_succ, mul_assoc, invSelf_mul_self, mul_one]

theorem poleForms_le_succ (m : ℕ) : poleForms k f T m ≤ poleForms k f T (m + 1) := by
  intro x hx
  obtain ⟨ξ, hξ, rfl⟩ := (mem_poleForms k f T).1 hx
  exact (mem_poleForms k f T).2 ⟨f • ξ, (logForms k f T).smul_mem hξ f,
    invSelf_pow_succ_smul_self_smul k f T m ξ⟩

theorem poleFiltration_le_succ (m n : ℕ) :
    poleFiltration k f T m n ≤ poleFiltration k f T (m + 1) n := by
  intro x hx
  obtain ⟨ξ, hξ, rfl⟩ := (mem_poleFiltration k f T).1 hx
  exact (mem_poleFiltration k f T).2 ⟨f • ξ, (logPower k f T n).smul_mem f hξ,
    invSelf_pow_succ_smul_self_smul k f T m ξ⟩

/-- The pole bound defines an increasing filtration. -/
theorem poleForms_monotone : Monotone (poleForms k f T) :=
  monotone_nat_of_le_succ (poleForms_le_succ k f T)

theorem poleFiltration_monotone (n : ℕ) : Monotone (fun m => poleFiltration k f T m n) :=
  monotone_nat_of_le_succ (fun m => poleFiltration_le_succ k f T m n)

theorem poleFiltration_le_exteriorPower (m n : ℕ) :
    poleFiltration k f T m n ≤ (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  intro x hx
  obtain ⟨ξ, hξ, rfl⟩ := (mem_poleFiltration k f T).1 hx
  exact (⋀[T]^n Ω[T⁄k]).smul_mem _ (logPower_le_exteriorPower k f T n hξ)

/-- Every localized form has a finite pole bound. -/
theorem exists_mem_poleForms (x : Forms k T) : ∃ m, x ∈ poleForms k f T m := by
  obtain ⟨m, ξ, rfl⟩ := Forms.exists_eq_invSelf_pow_smul_map f x
  exact ⟨m, (mem_poleForms k f T).2 ⟨_, map_mem_logForms k f T ξ, rfl⟩⟩

/-- Every homogeneous localized form has a finite pole bound in the same degree. -/
theorem exists_mem_poleFiltration {n : ℕ} {x : Forms k T} (hx : x ∈ ⋀[T]^n Ω[T⁄k]) :
    ∃ m, x ∈ poleFiltration k f T m n := by
  obtain ⟨m, ξ, hξ, rfl⟩ := Forms.exists_eq_invSelf_pow_smul_map_of_mem f hx
  exact ⟨m, (mem_poleFiltration k f T).2 ⟨_, map_mem_logPower k f T hξ, rfl⟩⟩

/-- The total pole filtration is exhaustive. -/
theorem iSup_poleForms : ⨆ m, poleForms k f T m = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨m, hm⟩ := exists_mem_poleForms k f T x
  exact (le_iSup (poleForms k f T) m) hm

/-- The filtration exhausts each homogeneous degree separately. -/
theorem iSup_poleFiltration (n : ℕ) :
    ⨆ m, poleFiltration k f T m n = (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  refine le_antisymm (iSup_le (fun m => poleFiltration_le_exteriorPower k f T m n)) ?_
  intro x hx
  obtain ⟨m, hm⟩ := exists_mem_poleFiltration k f T hx
  exact (le_iSup (fun m => poleFiltration k f T m n) m) hm

/-- A form is in the degree `n` pole stage precisely when it is in the total pole stage and has
degree `n`. -/
theorem mem_poleFiltration_iff {m n : ℕ} {x : Forms k T} :
    x ∈ poleFiltration k f T m n ↔ x ∈ poleForms k f T m ∧ x ∈ ⋀[T]^n Ω[T⁄k] := by
  constructor
  · intro hx
    obtain ⟨ξ, hξ, rfl⟩ := (mem_poleFiltration k f T).1 hx
    exact ⟨(mem_poleForms k f T).2 ⟨ξ, logPower_le_logForms k f T n hξ, rfl⟩,
      poleFiltration_le_exteriorPower k f T m n hx⟩
  · rintro ⟨hx, hxn⟩
    obtain ⟨ξ, hξ, h⟩ := (mem_poleForms k f T).1 hx
    have hclear : (f ^ m) • x = ξ := by
      rw [← h, self_pow_smul_invSelf_pow_smul]
    refine (mem_poleFiltration k f T).2 ⟨ξ, mem_logPower_iff.2 ⟨hξ, ?_⟩, h⟩
    rw [← hclear]
    exact ((⋀[T]^n Ω[T⁄k]).restrictScalars A).smul_mem _ hxn

theorem poleFiltration_eq_inf (m n : ℕ) :
    poleFiltration k f T m n = poleForms k f T m ⊓ (⋀[T]^n Ω[T⁄k]).restrictScalars A := by
  ext x
  exact mem_poleFiltration_iff k f T

/-- Multiplication by `f⁻ᵐ` identifies logarithmic forms with the total pole stage. This uses
invertibility in the localization, rather than regularity of `f` in `A`. -/
noncomputable def logPoleEquiv (m : ℕ) : logForms k f T ≃ₗ[A] poleForms k f T m :=
  LinearEquiv.ofInjective (logPoleMap k f T m) (logPoleMap_injective k f T m)

@[simp]
theorem coe_logPoleEquiv (m : ℕ) (x : logForms k f T) :
    (logPoleEquiv k f T m x : Forms k T) = (invSelf f : T) ^ m • (x : Forms k T) := rfl

/-- The differential in logarithmic pole coordinates. -/
theorem d_invSelf_pow_smul_eq_theta (m : ℕ) (ξ : Forms k T) :
    d k ((invSelf f : T) ^ m • ξ) =
      (invSelf f : T) ^ m • (d k ξ - (m : A) • (theta k f T * ξ)) := by
  rw [Nat.cast_smul_eq_nsmul A, ← Nat.cast_smul_eq_nsmul T]
  exact d_invSelf_pow_smul_eq_dlog k f
    (IsLocalization.Away.algebraMap_isUnit (S := T) f) m ξ

/-- Every total pole stage is stable under the differential. -/
theorem d_mem_poleForms {m : ℕ} {x : Forms k T} (hx : x ∈ poleForms k f T m) :
    d k x ∈ poleForms k f T m := by
  obtain ⟨ξ, hξ, rfl⟩ := (mem_poleForms k f T).1 hx
  refine (mem_poleForms k f T).2 ⟨_, (logForms k f T).sub_mem
    (d_mem_logForms hξ) ((logForms k f T).smul_mem
      ((logForms k f T).mul_mem (theta_mem_logForms k f T) hξ) (m : A)), ?_⟩
  exact (d_invSelf_pow_smul_eq_theta k f T m ξ).symm

/-- The pole filtration is by subcomplexes, with differential raising exterior degree by one.

Blueprint: `def:dr-pole-filtration`. -/
theorem d_mem_poleFiltration {m n : ℕ} {x : Forms k T}
    (hx : x ∈ poleFiltration k f T m n) :
    d k x ∈ poleFiltration k f T m (n + 1) := by
  obtain ⟨ξ, hξ, rfl⟩ := (mem_poleFiltration k f T).1 hx
  refine (mem_poleFiltration k f T).2 ⟨_, (logPower k f T (n + 1)).sub_mem
    (d_mem_logPower hξ) ((logPower k f T (n + 1)).smul_mem (m : A)
      (theta_mul_mem_logPower hξ)), ?_⟩
  exact (d_invSelf_pow_smul_eq_theta k f T m ξ).symm

/-- The actual differential restricted to a total pole stage. It is linear over `k`. -/
noncomputable def poleD (m : ℕ) : poleForms k f T m →ₗ[k] poleForms k f T m where
  toFun x := ⟨d k (x : Forms k T), d_mem_poleForms k f T x.property⟩
  map_add' x y := Subtype.ext (map_add (d k) (x : Forms k T) (y : Forms k T))
  map_smul' a x := Subtype.ext (map_smul (d k) a (x : Forms k T))

@[simp]
theorem coe_poleD (m : ℕ) (x : poleForms k f T m) :
    (poleD k f T m x : Forms k T) = d k (x : Forms k T) := rfl

@[simp]
theorem poleD_poleD (m : ℕ) (x : poleForms k f T m) :
    poleD k f T m (poleD k f T m x) = 0 :=
  Subtype.ext (d_d k (x : Forms k T))

/-- The differential between consecutive exterior degrees of one pole stage. -/
noncomputable def polePowerD (m n : ℕ) :
    poleFiltration k f T m n →ₗ[k] poleFiltration k f T m (n + 1) where
  toFun x := ⟨d k (x : Forms k T), d_mem_poleFiltration k f T x.property⟩
  map_add' x y := Subtype.ext (map_add (d k) (x : Forms k T) (y : Forms k T))
  map_smul' a x := Subtype.ext (map_smul (d k) a (x : Forms k T))

@[simp]
theorem coe_polePowerD (m n : ℕ) (x : poleFiltration k f T m n) :
    (polePowerD k f T m n x : Forms k T) = d k (x : Forms k T) := rfl

@[simp]
theorem polePowerD_polePowerD (m n : ℕ) (x : poleFiltration k f T m n) :
    polePowerD k f T m (n + 1) (polePowerD k f T m n x) = 0 :=
  Subtype.ext (d_d k (x : Forms k T))

theorem polePowerD_comp_polePowerD (m n : ℕ) :
    (polePowerD k f T m (n + 1)).comp (polePowerD k f T m n) = 0 :=
  LinearMap.ext (polePowerD_polePowerD k f T m n)

end OrlikSolomon.DeRham
