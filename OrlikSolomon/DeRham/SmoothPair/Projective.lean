/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Basic
public import OrlikSolomon.DeRham.Exterior.Projective
public import OrlikSolomon.DeRham.Localization

/-!
# Projective forms and injectivity into localization

If the Kähler differentials of a commutative `k`-algebra `A` are projective over `A`, then so is
every exterior degree of forms. In particular this holds when `A` is formally smooth over `k`, by
Mathlib's `Algebra.FormallySmooth.projective_kaehlerDifferential` and
`OrlikSolomon.DeRham.projective_exteriorPower`.

A non-zero-divisor acts injectively on these modules, since projective modules are flat. The
criterion that a form vanishes in a localization precisely when a power of the equation kills it
then proves injectivity into any certified localization away from a regular element.

Neither finite presentation, a field, a smooth quotient, connectedness nor a nonzero coefficient
ring is required. Units and the zero algebra are included.

## Main results

Blueprint `lem:dr-projective`:

* `OrlikSolomon.DeRham.projective_exteriorPower`, together with
  `Algebra.FormallySmooth.projective_kaehlerDifferential`, gives projectivity in every degree.
* `OrlikSolomon.DeRham.isSMulRegular_forms`: a regular element acts injectively in every degree.
* `OrlikSolomon.DeRham.Forms.injective_mapPower_of_isLocalizationAway`: the natural map of forms
  to the localization is injective in every degree.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Module.Projective A Ω[A⁄k]]

/-- A non-zero-divisor acts injectively on each exterior degree of forms when the one-forms are
projective. Formal smoothness of `A` over `k` supplies that projectivity. This includes degree
zero, the zero algebra and unit equations.

Blueprint: the scalar-injectivity assertion of `lem:dr-projective`. -/
theorem isSMulRegular_forms {f : A} (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    IsSMulRegular (⋀[A]^n Ω[A⁄k]) f :=
  Module.Flat.isSMulRegular_of_nonZeroDivisors hf

namespace Forms

variable {T : Type*} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]

/-- Forms on `A` inject into forms on any localization away from a non-zero-divisor, provided
the one-forms on `A` are projective. In particular this holds for a formally smooth `A`.

No injectivity of an arbitrary localization is assumed: if a form maps to zero, the localization
criterion gives a power of `f` killing it, and regularity makes that power injective.

Blueprint: the localization-injectivity assertion of `lem:dr-projective`. -/
theorem injective_mapPower_of_isLocalizationAway {f : A} [IsLocalization.Away f T]
    (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    Function.Injective (mapPower (IsScalarTower.toAlgHom k A T) n) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  obtain ⟨m, hm⟩ := (mapPower_eq_zero_iff_of_isLocalizationAway f).1 hx
  exact (isSMulRegular_forms (k := k) (pow_mem hf m) n) (by simpa only [smul_zero] using hm)

end Forms

end OrlikSolomon.DeRham
