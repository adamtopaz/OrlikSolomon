/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Quotient
import Mathlib.Tactic.Module

/-!
# Contraction of positive pole quotients

If `m + 1` is invertible in the coefficient ring and `v(f) = 1` modulo `f`, the actual
operator `−(m + 1)⁻¹ J` contracts `L / f L` with its pole-order differential. Transport along
the quotient identification gives a contraction of `F_(m+1) / F_m`. These maps lower exterior
degree by one and vanish in degree zero. No characteristic-zero, regularity, or smoothness
assumption is needed beyond the displayed unit and normal-derivation hypotheses.

## Main definitions and results

* `positivePoleHomotopy` and `positivePoleQuotientContractible`: the explicit contraction and
  homotopy identity on the logarithmic quotient.
* `poleQuotientHomotopy` and `poleQuotientD_homotopy_add`: the transported operator and identity
  on the actual successive pole quotient.
* `poleQuotientHomotopy_mem_poleQuotientPower` and `poleQuotientHomotopy_eq_zero`: exact
  exterior-degree control, including degree zero.

Blueprint: `thm:dr-pole-contraction`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- The contracting operator `−(m + 1)⁻¹ J` on the logarithmic quotient, for an invertible
positive pole order. -/
noncomputable def positivePoleHomotopy (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) :
    (logForms k f T ⧸ logIdeal k f T) →ₗ[k] logForms k f T ⧸ logIdeal k f T :=
  (-((hm.unit⁻¹ : kˣ) : k)) • (logQuotientEulerContraction k f T v).restrictScalars k

@[simp]
theorem positivePoleHomotopy_apply (m : ℕ) (v : Derivation k A A) (hm : IsUnit (m + 1 : k))
    (x : logForms k f T ⧸ logIdeal k f T) :
    positivePoleHomotopy k f T m v hm x =
      -((hm.unit⁻¹ : kˣ) : k) • logQuotientEulerContraction k f T v x := rfl

/-- The actual homotopy identity on the logarithmic quotient in pole order `m + 1`.

Blueprint: `thm:dr-pole-contraction`. -/
theorem positivePoleQuotientContractible (m : ℕ) (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) (hm : IsUnit (m + 1 : k))
    (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientDifferential k f T m (positivePoleHomotopy k f T m v hm x) +
      positivePoleHomotopy k f T m v hm (poleQuotientDifferential k f T m x) = x := by
  have hi : ((hm.unit⁻¹ : kˣ) : k) * (m + 1 : k) = 1 := by
    simpa only [IsUnit.unit_spec] using Units.inv_mul hm.unit
  simp only [positivePoleHomotopy_apply, poleQuotientDifferential_apply, map_sub, map_smul]
  calc
    _ = (-((hm.unit⁻¹ : kˣ) : k)) •
        (logQuotientD k f T (logQuotientEulerContraction k f T v x) +
          logQuotientEulerContraction k f T v (logQuotientD k f T x)) +
        (((hm.unit⁻¹ : kˣ) : k) * (m + 1 : k)) •
        (logQuotientThetaWedge k f T (logQuotientEulerContraction k f T v x) +
          logQuotientEulerContraction k f T v (logQuotientThetaWedge k f T x)) := by module
    _ = x := by
      rw [logQuotientEulerContraction_anticommute k f T v h hv,
        logQuotientThetaWedge_euler_identity k f T v h hv, smul_zero, zero_add, hi, one_smul]

/-- The logarithmic quotient homotopy lowers positive exterior degree by one. -/
theorem positivePoleHomotopy_mem_logQuotientPower (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) {n : ℕ} {x : logForms k f T ⧸ logIdeal k f T}
    (hx : x ∈ logQuotientPower k f T (n + 1)) :
    positivePoleHomotopy k f T m v hm x ∈ logQuotientPower k f T n :=
  ((logQuotientPower k f T n).restrictScalars k).smul_mem _
    (logQuotientEulerContraction_mem_logQuotientPower k f T v hx)

/-- The logarithmic quotient homotopy vanishes in degree zero. -/
theorem positivePoleHomotopy_eq_zero (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) {x : logForms k f T ⧸ logIdeal k f T}
    (hx : x ∈ logQuotientPower k f T 0) : positivePoleHomotopy k f T m v hm x = 0 := by
  rw [positivePoleHomotopy_apply, logQuotientEulerContraction_eq_zero k f T v hx, smul_zero]

/-- The contracting homotopy on the actual successive pole quotient. -/
noncomputable def poleQuotientHomotopy (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) : PoleQuotient k f T m →ₗ[k] PoleQuotient k f T m :=
  (poleQuotientEquiv k f T m).toLinearMap.restrictScalars k ∘ₗ
    positivePoleHomotopy k f T m v hm ∘ₗ
      (poleQuotientEquiv k f T m).symm.toLinearMap.restrictScalars k

@[simp]
theorem poleQuotientHomotopy_poleQuotientEquiv (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) (x : logForms k f T ⧸ logIdeal k f T) :
    poleQuotientHomotopy k f T m v hm (poleQuotientEquiv k f T m x) =
      poleQuotientEquiv k f T m (positivePoleHomotopy k f T m v hm x) := by
  simp [poleQuotientHomotopy]

/-- The transported contraction satisfies the homotopy identity on the actual pole quotient. -/
theorem poleQuotientD_homotopy_add (m : ℕ) (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) (hm : IsUnit (m + 1 : k)) (x : PoleQuotient k f T m) :
    poleQuotientD k f T m (poleQuotientHomotopy k f T m v hm x) +
      poleQuotientHomotopy k f T m v hm (poleQuotientD k f T m x) = x := by
  obtain ⟨y, rfl⟩ := (poleQuotientEquiv k f T m).surjective x
  rw [poleQuotientHomotopy_poleQuotientEquiv, poleQuotientD_poleQuotientEquiv,
    poleQuotientD_poleQuotientEquiv, poleQuotientHomotopy_poleQuotientEquiv, ← map_add,
    positivePoleQuotientContractible k f T m v h hv hm]

/-- The actual quotient homotopy lowers positive exterior degree by one. -/
theorem poleQuotientHomotopy_mem_poleQuotientPower (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) {n : ℕ} {x : PoleQuotient k f T m}
    (hx : x ∈ poleQuotientPower k f T m (n + 1)) :
    poleQuotientHomotopy k f T m v hm x ∈ poleQuotientPower k f T m n := by
  obtain ⟨y, rfl⟩ := (poleQuotientEquiv k f T m).surjective x
  rw [poleQuotientEquiv_mem_poleQuotientPower_iff] at hx
  rw [poleQuotientHomotopy_poleQuotientEquiv, poleQuotientEquiv_mem_poleQuotientPower_iff]
  exact positivePoleHomotopy_mem_logQuotientPower k f T m v hm hx

/-- The actual quotient homotopy vanishes in exterior degree zero. -/
theorem poleQuotientHomotopy_eq_zero (m : ℕ) (v : Derivation k A A)
    (hm : IsUnit (m + 1 : k)) {x : PoleQuotient k f T m}
    (hx : x ∈ poleQuotientPower k f T m 0) : poleQuotientHomotopy k f T m v hm x = 0 := by
  obtain ⟨y, rfl⟩ := (poleQuotientEquiv k f T m).surjective x
  rw [poleQuotientEquiv_mem_poleQuotientPower_iff] at hx
  rw [poleQuotientHomotopy_poleQuotientEquiv, positivePoleHomotopy_eq_zero k f T m v hm hx,
    map_zero]

end OrlikSolomon.DeRham
