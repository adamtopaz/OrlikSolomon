/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Log.Cohomology
public import OrlikSolomon.DeRham.Log.Residue
public import OrlikSolomon.DeRham.Pole.Reduction

/-!
# Global logarithmic comparison

Over a coefficient ring in which positive integers are units, the inclusion of the logarithmic
complex in the de Rham complex of a principal localization induces an algebra equivalence on
cohomology for every smooth principal pair. Its forward map is the canonical inclusion-induced
map, rather than a map chosen using a normal derivation. The normal derivation is used only in
the proof of bijectivity by finite pole reduction.

## Main results

* `OrlikSolomon.DeRham.bijective_logToLocalization_of_normalDerivation`: the comparison under the
  more general assumption that a derivation normal modulo `f` exists.
* `OrlikSolomon.DeRham.logToLocalizationQuasiIso`: bijectivity for a smooth principal pair.
* `OrlikSolomon.DeRham.logToLocalizationEquiv`: the canonical algebra equivalence.

Blueprint: `thm:dr-comparison`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- Finite pole reduction proves that the actual inclusion-induced map on total cohomology is
bijective. It suffices to have a derivation normal modulo `f`; smoothness is not otherwise used.

Blueprint: the two finite inductions in `thm:dr-comparison`. -/
theorem bijective_logToLocalization_of_normalDerivation
    (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) : Function.Bijective (LogCohomology.toCohomology k f T) :=
  LogCohomology.bijective_toCohomology_of_forall
    (exists_closed_logForm_sub_d_eq k f T hUnits v h hv)
    (fun x _ hx => exists_logPrimitive_of_exists k f T hUnits v h hv x hx)

variable {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}

/-- Global logarithmic comparison: the inclusion `L → Ω(T)` induces a bijection on total
cohomology. Positive integers need only be units in `k`; there is no nonzero-ring or connectedness
assumption. The map itself is independent of the normal derivation used to prove its bijectivity.

Blueprint: `thm:dr-comparison`. -/
theorem logToLocalizationQuasiIso (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (hpair : IsSmoothPrincipalPair f φ) :
    Function.Bijective (LogCohomology.toCohomology k f T) := by
  have := hpair.formallySmooth_ambient
  have := hpair.formallySmooth_closed
  let e : (A ⧸ Ideal.span {f}) ≃ₐ[k] S :=
    (Ideal.quotientEquivAlgOfEq k hpair.ker_eq.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hpair.surjective)
  have : Algebra.FormallySmooth k (A ⧸ Ideal.span {f}) := .of_equiv e.symm
  obtain ⟨v, h, hv⟩ := exists_normalDerivation_modulo (k := k) f hpair.mem_nonZeroDivisors
  exact bijective_logToLocalization_of_normalDerivation k f T hUnits v h hv

/-- The canonical algebra equivalence from logarithmic cohomology to the cohomology of the
localization. Its forward map is the inclusion-induced map, so the auxiliary normal derivation
does not enter its definition as mathematical data.

Blueprint: the total algebra assertion of `thm:dr-comparison`. -/
@[no_expose] noncomputable def logToLocalizationEquiv (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (hpair : IsSmoothPrincipalPair f φ) : LogCohomology k f T ≃ₐ[k] Cohomology k T :=
  AlgEquiv.ofBijective (LogCohomology.toCohomology k f T)
    (logToLocalizationQuasiIso k f T hUnits hpair)

@[simp]
theorem logToLocalizationEquiv_apply (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (hpair : IsSmoothPrincipalPair f φ) (c : LogCohomology k f T) :
    logToLocalizationEquiv k f T hUnits hpair c = LogCohomology.toCohomology k f T c := by
  unfold logToLocalizationEquiv
  rfl

end OrlikSolomon.DeRham
