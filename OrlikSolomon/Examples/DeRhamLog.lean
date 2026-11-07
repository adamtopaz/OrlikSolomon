/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Log
public import OrlikSolomon.Examples.DeRhamSmoothPair

/-!
# Regressions for logarithmic forms and the residue sequence

These check what is easy to get wrong about `DeRham/Log`: its statements cover a unit equation,
whose divisor is empty, the zero algebra and a disconnected algebra, they apply to divisor pairs
directly, and their signs are the ones `residue_mul_map` and `def:dr-gysin` need.

## Main results

* `OrlikSolomon.DeRham.Examples.isSmoothPrincipalPair_of_isUnit`: a unit equation with zero closed
  part is a smooth principal pair, and `OrlikSolomon.DeRham.Examples.ofRegular_bijective` says that
  then `L^• = Ω_A^•`. This is the logarithmic part of `prop:dr-unit-example`.
* `OrlikSolomon.DeRham.Examples.isSmoothPrincipalPair_of_subsingleton`: the zero algebra, the
  logarithmic part of `prop:dr-zero-example`.
* `OrlikSolomon.DeRham.Examples.productPolynomial_isSmoothPrincipalPair` and
  `OrlikSolomon.DeRham.Examples.productPolynomial_logResidue_theta`: the equation `(1, X)` on
  `k × k[X]`, where `θ` has residue one, although no derivation takes the equation to one. This is
  the logarithmic part of `prop:dr-product-example`.
* `OrlikSolomon.DeRham.Examples.logResidue_theta_mul_diff` and
  `OrlikSolomon.DeRham.Examples.logResidue_diff_mul_theta`: `ρ(θ ∧ da) = d(a|_S)` and
  `ρ(da ∧ θ) = -d(a|_S)`, so the right projection formula has no sign and the left one does.
-/

@[expose] public section

namespace OrlikSolomon.DeRham.Examples

universe u

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {S : Type*} [CommRing S] [Algebra k S] {f : A} {φ : A →ₐ[k] S}

section Signs

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

/-- `ρ(θ ∧ da) = d(a|_S)`, with no sign. -/
theorem logResidue_theta_mul_diff (h : IsSmoothPrincipalPair f φ) (a : A) :
    logResidue T h (⟨θ, theta_mem_logForms k f T⟩ * ofRegular k f T (diff k a)) = diff k (φ a) := by
  rw [logResidue_mul_ofRegular, logResidue_theta, one_mul, Forms.map_diff]

/-- `ρ(da ∧ θ) = -d(a|_S)`: moving `da` across `θ` changes the sign. Over `ZMod 2` this says nothing
new, and the proof does not divide by two. -/
theorem logResidue_diff_mul_theta (h : IsSmoothPrincipalPair f φ) (a : A) :
    logResidue T h (ofRegular k f T (diff k a) * ⟨θ, theta_mem_logForms k f T⟩) =
      -diff k (φ a) := by
  rw [logResidue_ofRegular_mul, logResidue_theta, mul_one, Forms.map_diff, involute_diff]

/-- `Ω_A^0 → L^0` is bijective: the logarithmic forms of degree zero are the functions on `A`. -/
theorem powerToLog_zero_bijective (h : IsSmoothPrincipalPair f φ) :
    Function.Bijective (powerToLog k f T 0) :=
  ⟨powerToLog_injective h 0, powerToLog_zero_surjective k f T⟩

end Signs

section Unit

/-- A unit equation, with a zero closed part, is a smooth principal pair. So no statement of
`DeRham/Log` assumes that the divisor is nonempty.

Blueprint: `prop:dr-unit-example`. -/
theorem isSmoothPrincipalPair_of_isUnit [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k S]
    [Subsingleton S] (hf : IsUnit f) (φ : A →ₐ[k] S) : IsSmoothPrincipalPair f φ where
  mem_nonZeroDivisors := hf.mem_nonZeroDivisors
  surjective s := ⟨0, Subsingleton.elim _ _⟩
  ker_eq := by
    rw [Ideal.span_singleton_eq_top.2 hf, Ideal.eq_top_iff_one]
    exact Subsingleton.elim _ _
  formallySmooth_ambient := inferInstance
  formallySmooth_closed := inferInstance

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- When the closed part is zero, the residue sequence is `0 → Ω_A → L → 0 → 0`, so all logarithmic
forms are regular, by a unique regular form.

Blueprint: `prop:dr-unit-example`. -/
theorem ofRegular_bijective [Subsingleton S] (h : IsSmoothPrincipalPair f φ) :
    Function.Bijective (ofRegular k f T) :=
  ⟨h.ofRegular_injective T, fun x =>
    (exact_ofRegular_logResidue T h x).1 (Subsingleton.elim (α := Forms k S) _ _)⟩

/-- `A` is its own localization away from a unit, so the whole of `DeRham/Log` applies with `T = A`.
Then `θ` is a regular form, and `L^• = Ω_A^•`. -/
example [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k S] [Subsingleton S] (u : Aˣ)
    (φ : A →ₐ[k] S) :
    letI := IsLocalization.away_of_isUnit_of_bijective A u.isUnit Function.bijective_id
    Function.Bijective (ofRegular k (u : A) A) :=
  letI := IsLocalization.away_of_isUnit_of_bijective A u.isUnit Function.bijective_id
  ofRegular_bijective A (isSmoothPrincipalPair_of_isUnit u.isUnit φ)

end Unit

section Zero

/-- On the zero algebra, every element is a smooth principal equation for the identity.

Blueprint: `prop:dr-zero-example`. -/
theorem isSmoothPrincipalPair_of_subsingleton [Subsingleton A] [Algebra.FormallySmooth k A]
    (f : A) : IsSmoothPrincipalPair f (AlgHom.id k A) :=
  isSmoothPrincipalPair_of_isUnit (isUnit_of_subsingleton f) _

/-- On the zero algebra, the residue sequence is still exact, by the general theorem, and all of its
terms are zero. -/
example {A T : Type u} [CommRing A] [Algebra k A] [Subsingleton A]
    [Algebra.FormallySmooth k A] (f : A) [CommRing T] [Algebra k T] [Algebra A T]
    [IsScalarTower k A T] [IsLocalization.Away f T] :
    (logResidueShortComplex T (isSmoothPrincipalPair_of_subsingleton (k := k) f)).ShortExact :=
  logResidueShortExact T _

/-- Logarithmic forms on the zero algebra vanish. -/
example [Subsingleton A] (T : Type*) [CommRing T] [Algebra k T] [Algebra A T]
    [IsScalarTower k A T] [IsLocalization.Away f T] : Subsingleton (logForms k f T) :=
  have : Subsingleton T := (algebraMap A T).codomain_trivial
  inferInstance

end Zero

section Product

open Sanity

variable (k)

/-- The equation `(1, X)` on the disconnected algebra `k × k[X]` is a smooth principal pair,
although it vanishes on only one component and no derivation takes it to one.

Blueprint: `prop:dr-product-example`. -/
theorem productPolynomial_isSmoothPrincipalPair :
    IsSmoothPrincipalPair (productPolynomialEquation k)
      (Ideal.Quotient.mkₐ k (Ideal.span {productPolynomialEquation k})) :=
  .of_quotient (productPolynomialEquation_regular k)

/-- The residue of `θ = (0, dX / X)` on `k × k[X]` is one.

Blueprint: `prop:dr-product-example`. -/
theorem productPolynomial_logResidue_theta :
    logResidue (Localization.Away (productPolynomialEquation k))
        (productPolynomial_isSmoothPrincipalPair k)
        ⟨theta k (productPolynomialEquation k) (Localization.Away (productPolynomialEquation k)),
          theta_mem_logForms k _ _⟩ = 1 :=
  logResidue_theta _

end Product

section DivisorPair

variable (P : DivisorPair k)

/-- The residue sequence applies directly to a divisor pair, with no transport. -/
example : (logResidueShortComplex P.compl P.isSmoothPrincipalPair).ShortExact :=
  logResidueShortExact P.compl P.isSmoothPrincipalPair

/-- The residue of `dlog k P.eqnUnit` on a divisor pair is one. -/
example : logResidue P.compl P.isSmoothPrincipalPair
    ⟨dlog k P.eqnUnit, P.theta_eq_dlog_eqnUnit ▸ theta_mem_logForms k P.eqn P.compl⟩ = 1 := by
  simp only [← P.theta_eq_dlog_eqnUnit, logResidue_theta]

/-- The residue of a form on the standard pair, which is `(k[t], k, k[t; t⁻¹], t)`. -/
example : logResidue (DivisorPair.standardPair (SmoothAlg.point k)).compl
    (DivisorPair.standardPair (SmoothAlg.point k)).isSmoothPrincipalPair
    ⟨theta k _ _, theta_mem_logForms k _ _⟩ = 1 :=
  logResidue_theta _

end DivisorPair

end OrlikSolomon.DeRham.Examples
