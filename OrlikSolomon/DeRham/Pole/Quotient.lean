/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Euler
public import OrlikSolomon.DeRham.Pole.Filtration

/-!
# Successive quotients of the pole filtration

Multiplication by `f⁻⁽ᵐ⁺¹⁾` identifies `L / f L` with the quotient of pole stage `m + 1` by
stage `m`. This equivalence is linear over `A` and respects exterior degree. No smoothness or
regularity hypothesis is required: denominators are cleared in the localization itself.

## Main definitions and results

* `poleQuotientEquiv`: the `A`-linear identification of the two quotients.
* `poleQuotientProjection`: the surjective projection from a pole stage, whose kernel is the
  previous stage.
* `poleQuotientPowerEquiv`: the identification in each exterior degree.
* `poleQuotientDifferential` and `poleQuotientD_poleQuotientEquiv`: the transported differential
  is `d̄ − (m + 1) W`.

Blueprint: `lem:dr-pole-quotient`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open IsLocalization.Away (invSelf)

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- The previous pole stage, viewed as a submodule of the next stage. -/
noncomputable def polePrevious (m : ℕ) : Submodule A (poleForms k f T (m + 1)) :=
  (poleForms k f T m).comap (poleForms k f T (m + 1)).subtype

@[simp]
theorem mem_polePrevious (m : ℕ) (x : poleForms k f T (m + 1)) :
    x ∈ polePrevious k f T m ↔ (x : Forms k T) ∈ poleForms k f T m := Iff.rfl

/-- The quotient of consecutive total pole stages `F_(m+1) / F_m`. -/
abbrev PoleQuotient (m : ℕ) := poleForms k f T (m + 1) ⧸ polePrevious k f T m

/-- A logarithmic numerator represents a form in the previous pole stage precisely when it
is divisible by `f` in logarithmic forms. -/
theorem logPoleEquiv_mem_polePrevious_iff (m : ℕ) (x : logForms k f T) :
    logPoleEquiv k f T (m + 1) x ∈ polePrevious k f T m ↔ x ∈ logIdeal k f T := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (mem_poleForms k f T).1 hx
    refine mem_logIdeal.2 ⟨⟨y, hy⟩, ?_⟩
    apply logPoleMap_injective k f T (m + 1)
    change (invSelf f : T) ^ (m + 1) • (f • y) = _
    rw [invSelf_pow_succ_smul_self_smul]
    exact he
  · intro hx
    obtain ⟨y, rfl⟩ := mem_logIdeal.1 hx
    exact (mem_poleForms k f T).2 ⟨y, y.property,
      (invSelf_pow_succ_smul_self_smul k f T m y).symm⟩

/-- Multiplication by `f⁻⁽ᵐ⁺¹⁾` sends `f L` onto the previous pole stage. -/
theorem map_logIdeal_logPoleEquiv (m : ℕ) :
    (logIdeal k f T).map (logPoleEquiv k f T (m + 1)).toLinearMap =
      polePrevious k f T m := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (logPoleEquiv_mem_polePrevious_iff k f T m y).2 hy
  · intro hx
    refine ⟨(logPoleEquiv k f T (m + 1)).symm x, ?_,
      (logPoleEquiv k f T (m + 1)).apply_symm_apply x⟩
    exact (logPoleEquiv_mem_polePrevious_iff k f T m _).1 (by simpa using hx)

/-- The logarithmic quotient is the successive pole quotient, by multiplication by
`f⁻⁽ᵐ⁺¹⁾` on representatives.

Blueprint: `lem:dr-pole-quotient`. -/
noncomputable def poleQuotientEquiv (m : ℕ) :
    (logForms k f T ⧸ logIdeal k f T) ≃ₗ[A] PoleQuotient k f T m :=
  Submodule.Quotient.equiv _ _ (logPoleEquiv k f T (m + 1))
    (map_logIdeal_logPoleEquiv k f T m)

@[simp]
theorem poleQuotientEquiv_mk (m : ℕ) (x : logForms k f T) :
    poleQuotientEquiv k f T m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (logPoleEquiv k f T (m + 1) x) := rfl

/-- The canonical quotient projection from the next pole stage, in logarithmic coordinates. -/
noncomputable def poleQuotientProjection (m : ℕ) :
    poleForms k f T (m + 1) →ₗ[A] logForms k f T ⧸ logIdeal k f T :=
  (logIdeal k f T).mkQ.comp (logPoleEquiv k f T (m + 1)).symm.toLinearMap

@[simp]
theorem poleQuotientProjection_logPoleEquiv (m : ℕ) (x : logForms k f T) :
    poleQuotientProjection k f T m (logPoleEquiv k f T (m + 1) x) =
      Submodule.Quotient.mk x := by
  simp [poleQuotientProjection]

/-- The pole quotient identification takes the canonical projection to the actual quotient
class of a pole-stage form. -/
@[simp]
theorem poleQuotientEquiv_poleQuotientProjection (m : ℕ) (x : poleForms k f T (m + 1)) :
    poleQuotientEquiv k f T m (poleQuotientProjection k f T m x) =
      Submodule.Quotient.mk x := by
  obtain ⟨y, rfl⟩ := (logPoleEquiv k f T (m + 1)).surjective x
  rw [poleQuotientProjection_logPoleEquiv, poleQuotientEquiv_mk]

/-- Every logarithmic quotient class has a lift to the next pole stage. -/
theorem poleQuotientProjection_surjective (m : ℕ) :
    Function.Surjective (poleQuotientProjection k f T m) :=
  (Submodule.mkQ_surjective _).comp (logPoleEquiv k f T (m + 1)).symm.surjective

/-- On a scaled logarithmic representative the canonical projection returns its numerator
class, without unfolding the pole-coordinate equivalence. -/
@[simp]
theorem poleQuotientProjection_mk (m : ℕ) (x : logForms k f T) :
    poleQuotientProjection k f T m
      ⟨(invSelf f : T) ^ (m + 1) • (x : Forms k T),
        (mem_poleForms k f T).2 ⟨x, x.property, rfl⟩⟩ = Submodule.Quotient.mk x :=
  poleQuotientProjection_logPoleEquiv k f T m x

/-- The kernel of the canonical projection is exactly the previous pole stage. -/
@[simp]
theorem ker_poleQuotientProjection (m : ℕ) :
    LinearMap.ker (poleQuotientProjection k f T m) = polePrevious k f T m := by
  ext x
  obtain ⟨y, rfl⟩ := (logPoleEquiv k f T (m + 1)).surjective x
  simp only [LinearMap.mem_ker, poleQuotientProjection_logPoleEquiv,
    Submodule.Quotient.mk_eq_zero, logPoleEquiv_mem_polePrevious_iff]

/-- Pole coordinates preserve exterior degree in both directions. -/
theorem logPoleEquiv_mem_poleFiltration_iff (m n : ℕ) (x : logForms k f T) :
    (logPoleEquiv k f T m x : Forms k T) ∈ poleFiltration k f T m n ↔
      (x : Forms k T) ∈ logPower k f T n := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (mem_poleFiltration k f T).1 hx
    have he' : (⟨y, logPower_le_logForms k f T n hy⟩ : logForms k f T) = x :=
      logPoleMap_injective k f T m he
    have hval := congrArg Subtype.val he'
    change y = (x : Forms k T) at hval
    exact hval ▸ hy
  · intro hx
    exact (mem_poleFiltration k f T).2 ⟨x, hx, rfl⟩

/-- The degree `n` part of a successive pole quotient, defined as the image of its homogeneous
pole stage. -/
noncomputable def poleQuotientPower (m n : ℕ) : Submodule A (PoleQuotient k f T m) :=
  ((poleFiltration k f T (m + 1) n).comap (poleForms k f T (m + 1)).subtype).map
    (polePrevious k f T m).mkQ

theorem mem_poleQuotientPower {m n : ℕ} {x : PoleQuotient k f T m} :
    x ∈ poleQuotientPower k f T m n ↔
      ∃ y : poleForms k f T (m + 1), (y : Forms k T) ∈ poleFiltration k f T (m + 1) n ∧
        Submodule.Quotient.mk y = x := Iff.rfl

/-- The actual differential of the larger pole stage preserves its previous stage. -/
theorem poleD_mem_polePrevious (m : ℕ) {x : poleForms k f T (m + 1)}
    (hx : x ∈ polePrevious k f T m) :
    poleD k f T (m + 1) x ∈ polePrevious k f T m :=
  d_mem_poleForms k f T hx

/-- The actual differential induced on the quotient of consecutive pole stages. -/
noncomputable def poleQuotientD (m : ℕ) : PoleQuotient k f T m →ₗ[k] PoleQuotient k f T m :=
  (Submodule.Quotient.restrictScalarsEquiv k (polePrevious k f T m)).toLinearMap ∘ₗ
    Submodule.mapQ _ _ (poleD k f T (m + 1)) (fun _ hx => poleD_mem_polePrevious k f T m hx) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv k (polePrevious k f T m)).symm.toLinearMap

@[simp]
theorem poleQuotientD_mk (m : ℕ) (x : poleForms k f T (m + 1)) :
    poleQuotientD k f T m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (poleD k f T (m + 1) x) := rfl

@[simp]
theorem poleQuotientD_poleQuotientD (m : ℕ) (x : PoleQuotient k f T m) :
    poleQuotientD k f T m (poleQuotientD k f T m x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [poleQuotientD_mk, poleD_poleD, Submodule.Quotient.mk_zero]

/-- The quotient differential raises exterior degree by one. -/
theorem poleQuotientD_mem_poleQuotientPower {m n : ℕ} {x : PoleQuotient k f T m}
    (hx : x ∈ poleQuotientPower k f T m n) :
    poleQuotientD k f T m x ∈ poleQuotientPower k f T m (n + 1) := by
  obtain ⟨y, hy, rfl⟩ := (mem_poleQuotientPower k f T).1 hx
  exact (mem_poleQuotientPower k f T).2
    ⟨poleD k f T (m + 1) y, d_mem_poleFiltration k f T hy, rfl⟩

/-- The quotient equivalence preserves homogeneous pieces in both directions. -/
theorem poleQuotientEquiv_mem_poleQuotientPower_iff (m n : ℕ)
    (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientEquiv k f T m x ∈ poleQuotientPower k f T m n ↔
      x ∈ logQuotientPower k f T n := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (mem_poleQuotientPower k f T).1 hx
    refine (mem_logQuotientPower k f T).2
      ⟨(logPoleEquiv k f T (m + 1)).symm y, ?_, ?_⟩
    · apply (logPoleEquiv_mem_poleFiltration_iff k f T (m + 1) n _).1
      simpa only [LinearEquiv.apply_symm_apply] using hy
    · apply (poleQuotientEquiv k f T m).injective
      simpa only [poleQuotientEquiv_mk, LinearEquiv.apply_symm_apply] using he
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_logQuotientPower k f T).1 hx
    exact (mem_poleQuotientPower k f T).2 ⟨logPoleEquiv k f T (m + 1) y,
      (logPoleEquiv_mem_poleFiltration_iff k f T (m + 1) n y).2 hy, rfl⟩

/-- The canonical projection sends a homogeneous pole-stage form to a logarithmic quotient
class of the same degree. -/
theorem poleQuotientProjection_mem_logQuotientPower {m n : ℕ}
    {x : poleForms k f T (m + 1)}
    (hx : (x : Forms k T) ∈ poleFiltration k f T (m + 1) n) :
    poleQuotientProjection k f T m x ∈ logQuotientPower k f T n := by
  obtain ⟨y, rfl⟩ := (logPoleEquiv k f T (m + 1)).surjective x
  rw [poleQuotientProjection_logPoleEquiv]
  exact logQuotientMk_mem_logQuotientPower k f T
    ((logPoleEquiv_mem_poleFiltration_iff k f T (m + 1) n y).1 hx)

/-- The quotient identification restricted to exterior degree `n`. -/
noncomputable def poleQuotientPowerEquiv (m n : ℕ) :
    logQuotientPower k f T n ≃ₗ[A] poleQuotientPower k f T m n :=
  (poleQuotientEquiv k f T m).submoduleMap _ |>.trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (poleQuotientEquiv_mem_poleQuotientPower_iff k f T m n y).2 hy
      · intro hx
        refine ⟨(poleQuotientEquiv k f T m).symm x, ?_,
          (poleQuotientEquiv k f T m).apply_symm_apply x⟩
        exact (poleQuotientEquiv_mem_poleQuotientPower_iff k f T m n _).1
          (by simpa only [LinearEquiv.apply_symm_apply] using hx)))

@[simp]
theorem coe_poleQuotientPowerEquiv (m n : ℕ) (x : logQuotientPower k f T n) :
    (poleQuotientPowerEquiv k f T m n x : PoleQuotient k f T m) =
      poleQuotientEquiv k f T m x := rfl

/-- The differential in logarithmic coordinates on the pole-order `m + 1` quotient:
`d̄ − (m + 1) W`.

Blueprint: `lem:dr-pole-quotient`. -/
noncomputable def poleQuotientDifferential (m : ℕ) :
    (logForms k f T ⧸ logIdeal k f T) →ₗ[k] logForms k f T ⧸ logIdeal k f T :=
  logQuotientD k f T - (m + 1 : k) • (logQuotientThetaWedge k f T).restrictScalars k

theorem poleQuotientDifferential_apply (m : ℕ) (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientDifferential k f T m x =
      logQuotientD k f T x - (m + 1 : k) • logQuotientThetaWedge k f T x := rfl

/-- The twisted differential computed on a logarithmic representative. -/
theorem poleQuotientDifferential_mk (m : ℕ) (x : logForms k f T) :
    poleQuotientDifferential k f T m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (logD k f T x - (m + 1 : A) • (logTheta k f T * x)) := by
  simp only [poleQuotientDifferential_apply, logQuotientD_mk, logQuotientThetaWedge_mk,
    Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← Nat.cast_add_one,
    Nat.cast_smul_eq_nsmul]

/-- The actual differential in pole coordinates. -/
theorem poleD_logPoleEquiv (m : ℕ) (x : logForms k f T) :
    poleD k f T m (logPoleEquiv k f T m x) =
      logPoleEquiv k f T m (logD k f T x - (m : A) • (logTheta k f T * x)) := by
  apply Subtype.ext
  exact d_invSelf_pow_smul_eq_theta k f T m x

/-- The pole quotient equivalence intertwines the actual differential and `d̄ − (m + 1) W`. -/
theorem poleQuotientD_poleQuotientEquiv (m : ℕ)
    (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientD k f T m (poleQuotientEquiv k f T m x) =
      poleQuotientEquiv k f T m (poleQuotientDifferential k f T m x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [poleQuotientEquiv_mk, poleQuotientD_mk, poleD_logPoleEquiv,
    poleQuotientDifferential_mk, Nat.cast_add, Nat.cast_one]

/-- The canonical projection from a pole stage is a map of complexes. -/
theorem poleQuotientProjection_poleD (m : ℕ) (x : poleForms k f T (m + 1)) :
    poleQuotientProjection k f T m (poleD k f T (m + 1) x) =
      poleQuotientDifferential k f T m (poleQuotientProjection k f T m x) := by
  obtain ⟨y, rfl⟩ := (logPoleEquiv k f T (m + 1)).surjective x
  rw [poleD_logPoleEquiv, poleQuotientProjection_logPoleEquiv,
    poleQuotientProjection_logPoleEquiv, poleQuotientDifferential_mk]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The differential in logarithmic quotient coordinates squares to zero. -/
@[simp]
theorem poleQuotientDifferential_poleQuotientDifferential (m : ℕ)
    (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientDifferential k f T m (poleQuotientDifferential k f T m x) = 0 := by
  apply (poleQuotientEquiv k f T m).injective
  rw [← poleQuotientD_poleQuotientEquiv, ← poleQuotientD_poleQuotientEquiv,
    poleQuotientD_poleQuotientD, map_zero]

/-- The twisted differential raises exterior degree by one. -/
theorem poleQuotientDifferential_mem_logQuotientPower {m n : ℕ}
    {x : logForms k f T ⧸ logIdeal k f T} (hx : x ∈ logQuotientPower k f T n) :
    poleQuotientDifferential k f T m x ∈ logQuotientPower k f T (n + 1) :=
  sub_mem (logQuotientD_mem_logQuotientPower k f T hx)
    (((logQuotientPower k f T (n + 1)).restrictScalars k).smul_mem _
      (logQuotientThetaWedge_mem_logQuotientPower k f T hx))

end OrlikSolomon.DeRham
