/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Filtration

/-!
# Complexes in the pole filtration

The degreewise pole modules form complexes of `k`-modules. Their inclusions into localized forms
and into larger pole stages are chain maps. At pole order zero this is the logarithmic complex.

## Main definitions and results

* `OrlikSolomon.DeRham.poleComplex`: the complex with terms `f⁻ᵐ Lⁿ`.
* `OrlikSolomon.DeRham.poleToLocalization`: its inclusion in the de Rham complex on `T`.
* `OrlikSolomon.DeRham.poleInclusion`: the chain map from a smaller to a larger pole bound.

Blueprint: `def:dr-pole-filtration`.
-/

@[expose] public section

open CategoryTheory

namespace OrlikSolomon.DeRham

universe u v

variable (k : Type u) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type v) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- One stage of the logarithmic pole filtration, as a complex of `k`-modules.

Blueprint: `def:dr-pole-filtration`. -/
noncomputable def poleComplex (m : ℕ) : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (poleFiltration k f T m n))
    (fun n => ModuleCat.ofHom (polePowerD k f T m n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, polePowerD_comp_polePowerD]
      rfl)

@[simp]
theorem poleComplex_X (m n : ℕ) :
    (poleComplex k f T m).X n = ModuleCat.of k (poleFiltration k f T m n) := rfl

@[simp]
theorem poleComplex_d (m n : ℕ) :
    (poleComplex k f T m).d n (n + 1) = ModuleCat.ofHom (polePowerD k f T m n) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (poleFiltration k f T m n))
    (fun n => ModuleCat.ofHom (polePowerD k f T m n)) n

/-- The degreewise inclusion of a pole stage into localized forms. -/
noncomputable def polePowerToPower (m n : ℕ) :
    poleFiltration k f T m n →ₗ[A] ⋀[T]^n Ω[T⁄k] where
  toFun x := ⟨x, poleFiltration_le_exteriorPower k f T m n x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_polePowerToPower (m n : ℕ) (x : poleFiltration k f T m n) :
    (polePowerToPower k f T m n x : Forms k T) = x := rfl

theorem polePowerToPower_injective (m n : ℕ) :
    Function.Injective (polePowerToPower k f T m n) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : ⋀[T]^n Ω[T⁄k] => (z : Forms k T)) h)

/-- The chain map including one pole stage in all localized forms. -/
noncomputable def poleToLocalization (m : ℕ) : poleComplex k f T m ⟶ complex k T :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom ((polePowerToPower k f T m n).restrictScalars k)) fun n => by
      rw [poleComplex_d, complex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem poleToLocalization_f (m n : ℕ) :
    (poleToLocalization k f T m).f n =
      ModuleCat.ofHom ((polePowerToPower k f T m n).restrictScalars k) := rfl

/-- Inclusion of pole stages with increasing pole bound. -/
noncomputable def poleInclusion {m p : ℕ} (h : m ≤ p) : poleComplex k f T m ⟶ poleComplex k f T p :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((Submodule.inclusion (poleFiltration_monotone k f T n h)).restrictScalars k)) fun n => by
      rw [poleComplex_d, poleComplex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem poleInclusion_f {m p : ℕ} (h : m ≤ p) (n : ℕ) :
    (poleInclusion k f T h).f n = ModuleCat.ofHom
      ((Submodule.inclusion (poleFiltration_monotone k f T n h)).restrictScalars k) := rfl

theorem poleInclusion_comp_poleToLocalization {m p : ℕ} (h : m ≤ p) :
    poleInclusion k f T h ≫ poleToLocalization k f T p = poleToLocalization k f T m := by
  ext n x
  rfl

end OrlikSolomon.DeRham
