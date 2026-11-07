/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import OrlikSolomon.DeRham.Complex
public import OrlikSolomon.DeRham.Log.Basic
public import OrlikSolomon.DeRham.Log.Cohomology
public import OrlikSolomon.DeRham.Log.Residue
public import OrlikSolomon.Geometry.SmoothAlg

/-!
# The logarithmic complex and the residue sequence

This is the module to import for logarithmic forms. It imports the files under `DeRham/Log`, whose
headers list their results, and it packages them as complexes of `k`-modules and as the short exact
sequence
`0 → Ω_A^• → L^• → Ω_S^•[-1] → 0`
of `thm:dr-residue-sequence`, for a smooth principal pair.

## Summary of the design

`T` is a localization of `A` away from `f`, in the sense of `IsLocalization.Away`, and `φ : A → S`
is a surjection with kernel `(f)`, so everything applies to a `DivisorPair`, by
`DivisorPair.isSmoothPrincipalPair` and `DivisorPair.theta_eq_dlog_eqnUnit`. The total algebra is
primary. The logarithmic forms `logForms k f T` are a subalgebra of `Forms k T`, the operator is
`d`, which `logD` restricts, and `logResidue T h` is the residue on all of them, for
`h : IsSmoothPrincipalPair f φ`. `logMk k f T (ω, η)` is the normal form `ω + θ ∧ η`, and
`logResidue_logMk`, `logD_logMk` and `logMk_mul_logMk` compute with it, so
`obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x` is the way to start a proof. The degrees are
submodules `logPower k f T n`, of which `mem_logPower_zero` and `mem_logPower_succ` are the
description in terms of elements, and `powerToLog`, `logPowerD` and `logPowerResidue` are the typed
maps for this file's complexes. `LogCohomology k f T` is the cohomology of the logarithmic forms,
and `LogCohomology.toCohomology` is the map of `thm:dr-comparison`.

## What `def:dr-gysin` uses

The Gysin map of `def:dr-gysin` is `[γ] ↦ [dλ]`, for `λ ∈ L^(q+1)` with `ρ λ = γ`. On elements:

* `logResidue_surjective` and `logPowerResidue_surjective` give `λ`, explicitly `θ ∧ η` for a lift
  `η` of `γ`, by `logResidue_logMk`.
* `logResidue_logD` and `logPowerResidue_logPowerD` are `ρ d = -d ρ`, so `ρ (dλ) = 0`.
* `logResidue_eq_zero_iff` and `exact_powerToLog_logPowerResidue` say that `dλ` is then regular, of
  the right degree, and `IsSmoothPrincipalPair.ofRegular_injective` and `powerToLog_injective` that
  it is the image of a unique form on `A`.

The same data, for Mathlib's long exact sequence, are `logResidueShortComplex` and
`logResidueShortExact`, with the blueprint's shift `shiftedComplex`: the modules `Ω_S^n` in degree
`n + 1` with differential `-d`, and zero in degree zero.

## Main definitions

* `OrlikSolomon.DeRham.logComplex k f T`: the complex `L^•`, of `k`-modules.
* `OrlikSolomon.DeRham.regularToLog k f T` and `OrlikSolomon.DeRham.logToLocalization k f T`: the
  chain maps `Ω_A^• → L^• → Ω_T^•`.
* `OrlikSolomon.DeRham.shiftedComplex k S`: the complex `Ω_S^•[-1]`.
* `OrlikSolomon.DeRham.logResidueHom T h`: the chain map `ρ : L^• → Ω_S^•[-1]`.
* `OrlikSolomon.DeRham.logResidueShortComplex T h`: the sequence of `thm:dr-residue-sequence`.

## Main results

* `OrlikSolomon.DeRham.regularToLog_comp_logToLocalization`: the composite `Ω_A^• → Ω_T^•` is the
  functoriality of forms.
* `OrlikSolomon.DeRham.logResidueShortExact`: blueprint `thm:dr-residue-sequence`.
* `OrlikSolomon.DivisorPair.isSmoothPrincipalPair`: a divisor pair is a smooth principal pair.
-/

@[expose] public section

open CategoryTheory

namespace OrlikSolomon.DeRham

universe u v

section Complex

variable (k : Type u) [CommRing k] {A : Type v} [CommRing A] [Algebra k A] (f : A)
  (T : Type v) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- The logarithmic complex `L^•`, with the modules `logPower k f T n` and the differentials
`logPowerD k f T n`. It is a complex of `k`-modules, since the differentials are not `A`-linear.

Blueprint: `def:dr-log`, `lem:dr-log-dga`. -/
noncomputable def logComplex : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (logPower k f T n))
    (fun n => ModuleCat.ofHom (logPowerD k f T n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, logPowerD_comp_logPowerD]
      rfl)

@[simp]
theorem logComplex_X (n : ℕ) : (logComplex k f T).X n = ModuleCat.of k (logPower k f T n) :=
  rfl

@[simp]
theorem logComplex_d (n : ℕ) :
    (logComplex k f T).d n (n + 1) = ModuleCat.ofHom (logPowerD k f T n) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (logPower k f T n))
    (fun n => ModuleCat.ofHom (logPowerD k f T n)) n

/-- The chain map `Ω_A^• → L^•`.

Blueprint: `thm:dr-residue-sequence`. -/
noncomputable def regularToLog : complex k A ⟶ logComplex k f T :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom ((powerToLog k f T n).restrictScalars k))
    fun n => by
      rw [logComplex_d, complex_d]
      exact ModuleCat.hom_ext (LinearMap.ext (logPowerD_powerToLog k f T n))

@[simp]
theorem regularToLog_f (n : ℕ) :
    (regularToLog k f T).f n = ModuleCat.ofHom ((powerToLog k f T n).restrictScalars k) :=
  rfl

/-- The chain map `L^• → Ω_T^•`, the inclusion of logarithmic forms in forms on the localization.

Blueprint: `def:dr-log`, and the map of `thm:dr-comparison`. -/
noncomputable def logToLocalization : logComplex k f T ⟶ complex k T :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom ((logPowerToPower k f T n).restrictScalars k))
    fun n => by
      rw [logComplex_d, complex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun x => (logPowerToPower_logPowerD k f T n x).symm)

@[simp]
theorem logToLocalization_f (n : ℕ) :
    (logToLocalization k f T).f n = ModuleCat.ofHom ((logPowerToPower k f T n).restrictScalars k) :=
  rfl

/-- The composite `Ω_A^• → L^• → Ω_T^•` is the functoriality of forms along `A → T`.

Blueprint: `def:dr-log`. -/
theorem regularToLog_comp_logToLocalization :
    regularToLog k f T ≫ logToLocalization k f T = complexMap (IsScalarTower.toAlgHom k A T) := by
  ext n : 2
  rw [HomologicalComplex.comp_f, regularToLog_f, logToLocalization_f, complexMap_f]
  exact LinearMap.ext (logPowerToPower_powerToLog k f T n)

end Complex

section Shifted

variable (k : Type u) [CommRing k] (S : Type v) [CommRing S] [Algebra k S]

/-- The modules of `Ω_S^•[-1]`: zero in degree zero, and `Ω_S^n` in degree `n + 1`.

Blueprint: the shift convention of the section "Scope, conventions, and the construction target". -/
noncomputable def shiftedX : ℕ → ModuleCat.{v} k
  | 0 => ModuleCat.of k PUnit
  | n + 1 => ModuleCat.of k (⋀[S]^n Ω[S⁄k])

/-- The differentials of `Ω_S^•[-1]`, which are `-d`.

Blueprint: the shift convention of the section "Scope, conventions, and the construction target". -/
noncomputable def shiftedD : (n : ℕ) → shiftedX k S n ⟶ shiftedX k S (n + 1)
  | 0 => 0
  | n + 1 => ModuleCat.ofHom (-powerD k S n)

/-- The shifted complex `Ω_S^•[-1]`, with `(Ω_S^•[-1])^(n+1) = Ω_S^n` and differential `-d`, and
zero in degree zero. The blueprint extends complexes by zero in negative degrees, and this library's
complexes are indexed by `ℕ`, so this is that convention with the degree shifted up by one.

Blueprint: the shift convention of the section "Scope, conventions, and the construction target". -/
noncomputable def shiftedComplex : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (shiftedX k S) (shiftedD k S) (by
    rintro (_ | n)
    · exact Limits.zero_comp
    · change ModuleCat.ofHom (-powerD k S n) ≫ ModuleCat.ofHom (-powerD k S (n + 1)) = 0
      rw [← ModuleCat.ofHom_comp, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg,
        powerD_comp_powerD]
      rfl)

@[simp]
theorem shiftedComplex_X_zero : (shiftedComplex k S).X 0 = ModuleCat.of k PUnit :=
  rfl

@[simp]
theorem shiftedComplex_X_succ (n : ℕ) :
    (shiftedComplex k S).X (n + 1) = ModuleCat.of k (⋀[S]^n Ω[S⁄k]) :=
  rfl

/-- The differential of the shifted complex is `-d`.

Blueprint: the shift convention of the section "Scope, conventions, and the construction target". -/
theorem shiftedComplex_d_succ (n : ℕ) :
    (shiftedComplex k S).d (n + 1) (n + 1 + 1) = ModuleCat.ofHom (-powerD k S n) :=
  CochainComplex.of_d (shiftedX k S) (shiftedD k S) (n + 1)

/-- The differential of the shifted complex out of degree zero is zero. -/
@[simp]
theorem shiftedComplex_d_zero : (shiftedComplex k S).d 0 1 = 0 :=
  CochainComplex.of_d (shiftedX k S) (shiftedD k S) 0

end Shifted

section Residue

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A] {f : A}
  (T : Type v) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T] {S : Type v} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}

/-- The components of the chain map `ρ : L^• → Ω_S^•[-1]`: zero in degree zero, and
`logPowerResidue` in degree `n + 1`.

Blueprint: `thm:dr-residue-sequence`. -/
noncomputable def logResidueHomF (h : IsSmoothPrincipalPair f φ) :
    (n : ℕ) → (logComplex k f T).X n ⟶ (shiftedComplex k S).X n
  | 0 => 0
  | n + 1 => ModuleCat.ofHom (logPowerResidue T h n)

/-- The residue is a chain map to `Ω_S^•[-1]`, whose differential is `-d`. This is the
anticommutation `logPowerResidue_logPowerD` of the residue with `d`, and in degree zero
`logPowerResidue_logPowerD_zero`.

Blueprint: `thm:dr-residue-sequence`. -/
noncomputable def logResidueHom (h : IsSmoothPrincipalPair f φ) :
    logComplex k f T ⟶ shiftedComplex k S :=
  CochainComplex.ofHom (logResidueHomF T h) <| by
    rintro (_ | n)
    · refine Limits.zero_comp.trans ?_
      rw [logComplex_d]
      exact ModuleCat.hom_ext
        (LinearMap.ext fun x => (logPowerResidue_logPowerD_zero h x).symm)
    · rw [shiftedComplex_d_succ, logComplex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun x => (logPowerResidue_logPowerD h n x).symm)

@[simp]
theorem logResidueHom_f_zero (h : IsSmoothPrincipalPair f φ) : (logResidueHom T h).f 0 = 0 :=
  rfl

@[simp]
theorem logResidueHom_f_succ (h : IsSmoothPrincipalPair f φ) (n : ℕ) :
    (logResidueHom T h).f (n + 1) = ModuleCat.ofHom (logPowerResidue T h n) :=
  rfl

/-- The residue sequence `0 → Ω_A^• → L^• → Ω_S^•[-1] → 0`, as a short complex of complexes of
`k`-modules. It is short exact, by `logResidueShortExact`.

Blueprint: `thm:dr-residue-sequence`. -/
noncomputable def logResidueShortComplex (h : IsSmoothPrincipalPair f φ) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) where
  X₁ := complex k A
  X₂ := logComplex k f T
  X₃ := shiftedComplex k S
  f := regularToLog k f T
  g := logResidueHom T h
  zero := by
    refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    cases n with
    | zero => rfl
    | succ n => exact logPowerResidue_powerToLog h n x

/-- The residue sequence `0 → Ω_A^• → L^• → Ω_S^•[-1] → 0` is a degreewise short exact sequence of
complexes of `k`-modules, for every smooth principal pair.

Blueprint: `thm:dr-residue-sequence`. -/
theorem logResidueShortExact (h : IsSmoothPrincipalPair f φ) :
    (logResidueShortComplex T h).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    refine ModuleCat.shortComplex_shortExact _ ?_ (powerToLog_injective h n) ?_
    · cases n with
      | zero =>
        intro x
        exact ⟨fun _ => powerToLog_zero_surjective k f T x, fun _ => rfl⟩
      | succ n => exact exact_powerToLog_logPowerResidue T h n
    · cases n with
      | zero => exact fun _ => ⟨0, rfl⟩
      | succ n => exact logPowerResidue_surjective T h n

end Residue

section DivisorPair

variable {k : Type u} [CommRing k] (P : DivisorPair k)

/-- A divisor pair is a smooth principal pair, for its equation and its map to the closed part, and
`P.compl` is an `IsLocalization.Away P.eqn` by an instance. So this file applies to it directly,
with no transport.

Blueprint: the section "The algebra of a smooth principal pair". -/
theorem _root_.OrlikSolomon.DivisorPair.isSmoothPrincipalPair :
    IsSmoothPrincipalPair P.eqn (SmoothAlg.algHom P.i) where
  mem_nonZeroDivisors := P.eqn_mem_nonZeroDivisors
  surjective := P.surjective_i
  ker_eq := P.ker_i
  formallySmooth_ambient := inferInstance
  formallySmooth_closed := inferInstance

/-- For a divisor pair, `θ` is the logarithmic form of `P.eqnUnit`. -/
theorem _root_.OrlikSolomon.DivisorPair.theta_eq_dlog_eqnUnit :
    theta k P.eqn P.compl = dlog k P.eqnUnit :=
  theta_eq_dlog k P.eqn P.compl rfl

end DivisorPair

end OrlikSolomon.DeRham
