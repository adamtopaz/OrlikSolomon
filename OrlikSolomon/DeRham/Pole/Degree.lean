/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import OrlikSolomon.DeRham.Log
public import OrlikSolomon.DeRham.Pole.Comparison

/-!
# Degreewise logarithmic comparison

The canonical comparison equivalence preserves and reflects cohomological degree. Its restrictions
identify the natural-degree pieces and the integer-indexed grading pieces, including the zero
pieces in negative degrees. These maps use the inclusion-induced map on representatives; no choice
of normal derivation enters them.

## Main results

* `logToLocalization_quasiIso`: the actual algebraic logarithmic inclusion is a quasi-isomorphism.
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

open CategoryTheory CategoryTheory.Limits

universe u v

private theorem moduleCat_homologyπ_eq_zero_iff {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ y, S.f y = S.iCycles z := by
  have hπ := ConcreteCategory.congr_hom S.homology_π_ι z
  simp only [ConcreteCategory.comp_apply] at hπ
  have hi : Function.Injective S.homologyι :=
    (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
  rw [← hi.eq_iff]
  simp only [map_zero, hπ, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

private theorem moduleCat_quasiIso_of_representatives {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hi : ∀ x, S.g x = 0 → (∃ b, T.f b = φ.τ₂ x) → ∃ a, S.f a = x)
    (hs : ∀ y, T.g y = 0 → ∃ x, S.g x = 0 ∧ ∃ b, φ.τ₂ x - y = T.f b) :
    ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (ShortComplex.homologyMap φ).hom.ker_eq_bot.1
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    change ShortComplex.homologyMap φ a = 0 at ha
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance a
    have he := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) z
    simp only [ConcreteCategory.comp_apply] at he
    have hb := (moduleCat_homologyπ_eq_zero_iff T (ShortComplex.cyclesMap φ z)).1
      (he.symm.trans ha)
    have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) z
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc] at hb
    have hd : S.g (S.iCycles z) = 0 := ConcreteCategory.congr_hom S.iCycles_g z
    obtain ⟨b, hb⟩ := hi (S.iCycles z) hd hb
    exact (moduleCat_homologyπ_eq_zero_iff S z).2 ⟨b, hb⟩
  · intro a
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance a
    have hd : T.g (T.iCycles z) = 0 := ConcreteCategory.congr_hom T.iCycles_g z
    obtain ⟨x, hx, b, hb⟩ := hs (T.iCycles z) hd
    let zx := S.cyclesMk x hx
    have hzx : S.iCycles zx = x := S.i_cyclesMk x hx
    refine ⟨S.homologyπ zx, ?_⟩
    have he := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) zx
    simp only [ConcreteCategory.comp_apply] at he
    rw [he]
    apply sub_eq_zero.1
    rw [← map_sub]
    apply (moduleCat_homologyπ_eq_zero_iff T _).2
    refine ⟨b, ?_⟩
    rw [map_sub]
    have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) zx
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc]
    simpa only [hzx] using hb.symm

section AlgebraicComparison

variable (k : Type u) [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
  (f : A) (T : Type v) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]
  {S : Type v} [CommRing S] [Algebra k S] {π : A →ₐ[k] S}

/-- The inclusion of the algebraic logarithmic complex into localized forms is a
quasi-isomorphism when positive integers are units and the ambient algebra and divisor form a
smooth principal pair. This packages the existing degreewise pole comparison as a statement
about the actual chain map, with the same inclusion on representatives. -/
theorem logToLocalization_quasiIso
    (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) (hpair : IsSmoothPrincipalPair f π) :
    QuasiIso (logToLocalization k f T) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ ((ComplexShape.up ℕ).prev n) n (n + 1) rfl
    (CochainComplex.next ℕ n)]
  apply moduleCat_quasiIso_of_representatives
  all_goals simp only [HomologicalComplex.shortComplexFunctor'_obj_X₁,
    HomologicalComplex.shortComplexFunctor'_obj_X₂, HomologicalComplex.shortComplexFunctor'_obj_X₃,
    HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_map_τ₂, logComplex_X, complex_X,
    logToLocalization_f, logComplex_d, complex_d]
  · intro x hx hb
    have hdx : logPowerD k f T n x = 0 := hx
    let xl := logPowerToLogForms k f T n x
    have hxl : logD k f T xl = 0 := Subtype.ext
      (congrArg (fun z : logPower k f T (n + 1) => (z : Forms k T)) hdx)
    have hdxt : d k (x : Forms k T) = 0 := congrArg Subtype.val hdx
    have hxzero : Cohomology.mk (x : Forms k T) hdxt = 0 := by
      apply Cohomology.mk_eq_zero_iff.2
      obtain ⟨b, hb⟩ := hb
      have hb' : logPowerToPower k f T n x ∈ Cohomology.rangeD k T n := by
        rw [← range_complex_d_hom_prev]
        exact ⟨b, hb⟩
      exact Cohomology.mem_rangeD_iff.1 hb'
    have hxlzero : LogCohomology.mk xl hxl = 0 := by
      apply (logToLocalizationQuasiIso k f T hUnits hpair).1
      rw [LogCohomology.toCohomology_mk, map_zero]
      exact hxzero
    cases n with
    | zero =>
      have hxzero := (LogCohomology.mk_eq_zero_iff_of_mem_logPower_zero x.2).1 hxlzero
      have hxx : x = 0 := Subtype.ext
        (congrArg (fun z : logForms k f T => (z : Forms k T)) hxzero)
      exact ⟨0, ((logComplex k f T).d ((ComplexShape.up ℕ).prev 0) 0).hom.map_zero.trans
        hxx.symm⟩
    | succ n =>
      obtain ⟨y, hy, hdy⟩ :=
        (LogCohomology.mk_eq_zero_iff_of_mem_logPower_succ x.2).1 hxlzero
      change ∃ b : (logComplex k f T).X ((ComplexShape.up ℕ).prev (n + 1)),
        ((logComplex k f T).d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom b = x
      rw [CochainComplex.prev_nat_succ n]
      refine ⟨⟨(y : Forms k T), hy⟩, ?_⟩
      rw [logComplex_d]
      change logPowerD k f T n ⟨(y : Forms k T), hy⟩ = x
      exact Subtype.ext (congrArg (fun z : logForms k f T => (z : Forms k T)) hdy)
  · intro y hy
    have hdy : powerD k T n y = 0 := hy
    have hdyt : d k (y : Forms k T) = 0 := congrArg Subtype.val hdy
    let cy : Cohomology.degree k T n := ⟨Cohomology.mk (y : Forms k T) hdyt,
      Cohomology.mk_mem_degree y.2 hdyt⟩
    let cl := (logToLocalizationDegreeEquiv k f T hUnits hpair n).symm cy
    obtain ⟨x, hx, hxn, hxc⟩ := LogCohomology.mem_degree_iff.1 cl.2
    let xp : logPower k f T n := ⟨(x : Forms k T), hxn⟩
    refine ⟨xp, ?_, ?_⟩
    · exact Subtype.ext (congrArg (fun z : logForms k f T => (z : Forms k T)) hx)
    · have heq : Cohomology.mk (x : Forms k T) (logD_eq_zero_iff.1 hx) =
          Cohomology.mk (y : Forms k T) hdyt := by
        have h := toCohomology_logToLocalizationDegreeEquiv_symm k f T hUnits hpair n cy
        rw [← hxc, LogCohomology.toCohomology_mk] at h
        exact h
      have hb : logPowerToPower k f T n xp - y ∈ Cohomology.rangeD k T n :=
        Cohomology.mem_rangeD_iff.2 (Cohomology.mk_eq_mk_iff.1 heq)
      rw [← range_complex_d_hom_prev] at hb
      obtain ⟨b, hb⟩ := hb
      exact ⟨b, hb.symm⟩

end AlgebraicComparison

end OrlikSolomon.DeRham
