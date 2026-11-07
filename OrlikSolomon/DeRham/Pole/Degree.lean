/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Comparison

/-!
# Degreewise logarithmic comparison

The canonical comparison equivalence preserves and reflects cohomological degree. Its restrictions
identify the natural-degree pieces and the integer-indexed grading pieces, including the zero
pieces in negative degrees. These maps use the inclusion-induced map on representatives; no choice
of normal derivation enters them.

## Main results

* `logToLocalizationEquiv_isHomogeneous` and `logToLocalizationEquiv_symm_isHomogeneous`: both
  directions preserve the integer grading.
* `logToLocalizationEquiv_mem_degree_iff`: comparison preserves and reflects natural degree.
* `logToLocalizationDegreeEquiv` and `logToLocalizationGradingEquiv`: the canonical linear
  equivalences in every natural or integer degree, with coercion formulas in both directions.
* `logToLocalizationEquiv_eq`, `logToLocalizationDegreeEquiv_eq` and
  `logToLocalizationGradingEquiv_eq`: the maps are independent of the certificates for
  invertibility and for the closed algebra of the smooth principal pair.

Blueprint: the assertion in every degree of `thm:dr-comparison`.
-/

@[expose] public section
noncomputable section

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T] {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}
  (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) (hpair : IsSmoothPrincipalPair f φ)

/-- Canonical logarithmic comparison preserves the integer grading. -/
theorem logToLocalizationEquiv_isHomogeneous :
    IsHomogeneousOfShift (LogCohomology.grading k f T) (Cohomology.grading k T) 0
      (logToLocalizationEquiv k f T hUnits hpair) := by
  intro p x hx
  rw [logToLocalizationEquiv_apply]
  exact LogCohomology.isHomogeneousOfShift_toCohomology k f T hx

/-- The inverse of canonical logarithmic comparison also preserves the integer grading. -/
theorem logToLocalizationEquiv_symm_isHomogeneous :
    IsHomogeneousOfShift (Cohomology.grading k T) (LogCohomology.grading k f T) 0
      (logToLocalizationEquiv k f T hUnits hpair).symm := by
  simpa only [neg_zero] using
    (logToLocalizationEquiv_isHomogeneous k f T hUnits hpair).algEquiv_symm

/-- Applying the actual comparison map to the inverse returns the given total class. -/
@[simp]
theorem toCohomology_logToLocalizationEquiv_symm (y : Cohomology k T) :
    LogCohomology.toCohomology k f T ((logToLocalizationEquiv k f T hUnits hpair).symm y) = y := by
  rw [← logToLocalizationEquiv_apply k f T hUnits hpair, AlgEquiv.apply_symm_apply]

/-- The inverse comparison sends an inclusion-induced class back to the original total class. -/
@[simp]
theorem logToLocalizationEquiv_symm_toCohomology (x : LogCohomology k f T) :
    (logToLocalizationEquiv k f T hUnits hpair).symm
      (LogCohomology.toCohomology k f T x) = x := by
  rw [← logToLocalizationEquiv_apply k f T hUnits hpair, AlgEquiv.symm_apply_apply]

/-- Canonical logarithmic comparison preserves the natural-degree pieces. -/
theorem logToLocalizationEquiv_isHomogeneous_degree :
    IsHomogeneousOfShift (LogCohomology.degree k f T) (Cohomology.degree k T) 0
      (logToLocalizationEquiv k f T hUnits hpair).toLinearEquiv :=
  isHomogeneousOfShift_zero_iff.2 fun n x hx => by
    change logToLocalizationEquiv k f T hUnits hpair x ∈ Cohomology.degree k T n
    rw [logToLocalizationEquiv_apply]
    exact LogCohomology.toCohomology_mem_degree hx

/-- Canonical logarithmic comparison preserves and reflects each natural degree. -/
theorem logToLocalizationEquiv_mem_degree_iff (n : ℕ) (x : LogCohomology k f T) :
    logToLocalizationEquiv k f T hUnits hpair x ∈ Cohomology.degree k T n ↔
      x ∈ LogCohomology.degree k f T n := by
  constructor
  · exact (logToLocalizationEquiv_isHomogeneous_degree k f T hUnits hpair).mem_of_map_mem
      (logToLocalizationEquiv k f T hUnits hpair).injective (add_zero n)
  · intro hx
    rw [logToLocalizationEquiv_apply]
    exact LogCohomology.toCohomology_mem_degree hx

/-- The inverse comparison preserves and reflects each natural degree. -/
theorem logToLocalizationEquiv_symm_mem_degree_iff (n : ℕ) (y : Cohomology k T) :
    (logToLocalizationEquiv k f T hUnits hpair).symm y ∈ LogCohomology.degree k f T n ↔
      y ∈ Cohomology.degree k T n := by
  rw [← logToLocalizationEquiv_mem_degree_iff k f T hUnits hpair,
    AlgEquiv.apply_symm_apply]

/-- The canonical equivalence `H^n(L) ≃ H^n(T)` in every natural degree.
Blueprint: `thm:dr-comparison`. -/
def logToLocalizationDegreeEquiv (n : ℕ) :
    LogCohomology.degree k f T n ≃ₗ[k] Cohomology.degree k T n :=
  (logToLocalizationEquiv_isHomogeneous_degree k f T hUnits hpair).componentEquiv (add_zero n)

/-- On underlying cohomology classes, the degreewise equivalence is the actual comparison map. -/
@[simp]
theorem coe_logToLocalizationDegreeEquiv (n : ℕ) (x : LogCohomology.degree k f T n) :
    (logToLocalizationDegreeEquiv k f T hUnits hpair n x : Cohomology k T) =
      LogCohomology.toCohomology k f T x := by
  change logToLocalizationEquiv k f T hUnits hpair x = _
  exact logToLocalizationEquiv_apply k f T hUnits hpair x

/-- The inverse degreewise equivalence is the inverse of the canonical total comparison. -/
@[simp]
theorem coe_logToLocalizationDegreeEquiv_symm (n : ℕ) (y : Cohomology.degree k T n) :
    ((logToLocalizationDegreeEquiv k f T hUnits hpair n).symm y : LogCohomology k f T) =
      (logToLocalizationEquiv k f T hUnits hpair).symm y := rfl

/-- Applying the actual comparison map to the degreewise inverse returns the original class. -/
theorem toCohomology_logToLocalizationDegreeEquiv_symm (n : ℕ)
    (y : Cohomology.degree k T n) :
    LogCohomology.toCohomology k f T
        ((logToLocalizationDegreeEquiv k f T hUnits hpair n).symm y) = y := by
  rw [coe_logToLocalizationDegreeEquiv_symm, ← logToLocalizationEquiv_apply k f T hUnits hpair,
    AlgEquiv.apply_symm_apply]

/-- The canonical comparison equivalence in every integer degree, including negative degrees.
Blueprint: `thm:dr-comparison`. -/
def logToLocalizationGradingEquiv (p : ℤ) :
    LogCohomology.grading k f T p ≃ₗ[k] Cohomology.grading k T p :=
  (logToLocalizationEquiv_isHomogeneous k f T hUnits hpair).componentEquiv
    (e := (logToLocalizationEquiv k f T hUnits hpair).toLinearEquiv) (add_zero p)

/-- The integer-degree equivalence is the actual comparison map on underlying classes. -/
@[simp]
theorem coe_logToLocalizationGradingEquiv (p : ℤ) (x : LogCohomology.grading k f T p) :
    (logToLocalizationGradingEquiv k f T hUnits hpair p x : Cohomology k T) =
      LogCohomology.toCohomology k f T x := by
  change logToLocalizationEquiv k f T hUnits hpair x = _
  exact logToLocalizationEquiv_apply k f T hUnits hpair x

/-- The integer-degree inverse is the inverse of the canonical total comparison. -/
@[simp]
theorem coe_logToLocalizationGradingEquiv_symm (p : ℤ) (y : Cohomology.grading k T p) :
    ((logToLocalizationGradingEquiv k f T hUnits hpair p).symm y : LogCohomology k f T) =
      (logToLocalizationEquiv k f T hUnits hpair).symm y := rfl

/-- The actual comparison map is a left inverse to the inverse in every integer degree. -/
theorem toCohomology_logToLocalizationGradingEquiv_symm (p : ℤ)
    (y : Cohomology.grading k T p) :
    LogCohomology.toCohomology k f T
        ((logToLocalizationGradingEquiv k f T hUnits hpair p).symm y) = y := by
  rw [coe_logToLocalizationGradingEquiv_symm, ← logToLocalizationEquiv_apply k f T hUnits hpair,
    AlgEquiv.apply_symm_apply]

variable {S' : Type*} [CommRing S'] [Algebra k S'] {φ' : A →ₐ[k] S'}
  (hUnits' : ∀ n : ℕ, IsUnit (n + 1 : k)) (hpair' : IsSmoothPrincipalPair f φ')

/-- Canonical comparison is independent even of the chosen presentation of the closed algebra. -/
theorem logToLocalizationEquiv_eq :
    logToLocalizationEquiv k f T hUnits hpair = logToLocalizationEquiv k f T hUnits' hpair' :=
  AlgEquiv.ext fun x => by simp only [logToLocalizationEquiv_apply]

/-- The natural-degree restrictions are independent of the smooth-pair certificates. -/
theorem logToLocalizationDegreeEquiv_eq (n : ℕ) :
    logToLocalizationDegreeEquiv k f T hUnits hpair n =
      logToLocalizationDegreeEquiv k f T hUnits' hpair' n := by
  ext x
  simp only [coe_logToLocalizationDegreeEquiv]

/-- The integer-degree restrictions are independent of the smooth-pair certificates. -/
theorem logToLocalizationGradingEquiv_eq (p : ℤ) :
    logToLocalizationGradingEquiv k f T hUnits hpair p =
      logToLocalizationGradingEquiv k f T hUnits' hpair' p := by
  ext x
  simp only [coe_logToLocalizationGradingEquiv]

end OrlikSolomon.DeRham
