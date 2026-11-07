/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import OrlikSolomon.DeRham.Log.Basic
public import OrlikSolomon.DeRham.PrincipalQuotient

/-!
# The crossing divisor

The equation `xy` in the affine plane is regular, but its quotient is not formally smooth.
Moreover, the logarithmic form `theta * (y dx)` is regular while `y dx` has nonzero restriction
to the quotient. Thus the two presentations of the same logarithmic form would require different
residues. No characteristic-zero assumption is needed for this obstruction.

## Main definitions

* `OrlikSolomon.DeRham.Examples.CrossingPlane`: the polynomial ring in two variables.
* `OrlikSolomon.DeRham.Examples.CrossingDivisor`: its quotient by the product of the variables.

## Main results

Blueprint `prop:dr-crossing-example`:

* `OrlikSolomon.DeRham.Examples.crossingEquation_mem_nonZeroDivisors`: the equation is regular.
* `OrlikSolomon.DeRham.Examples.crossingDivisor_not_formallySmooth`: the quotient is singular.
* `OrlikSolomon.DeRham.Examples.crossing_restriction_ne_zero`: `y dx` restricts nontrivially.
* `OrlikSolomon.DeRham.Examples.crossing_theta_mul`: `theta * (y dx) = dy * dx` is regular.
* `OrlikSolomon.DeRham.Examples.crossing_logMk_eq` and
  `OrlikSolomon.DeRham.Examples.crossing_no_residue`: equal presentations have incompatible
  residues.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.DeRham.Examples

open KaehlerDifferential (D)

variable (k : Type*) [CommRing k]

/-- The coordinate ring `k[x,y]` of the affine plane. -/
abbrev CrossingPlane := MvPolynomial (Fin 2) k

/-- The first coordinate of the crossing plane. -/
def crossingX : CrossingPlane k := MvPolynomial.X 0

/-- The second coordinate of the crossing plane. -/
def crossingY : CrossingPlane k := MvPolynomial.X 1

/-- The equation `xy` of the crossing divisor. -/
def crossingEquation : CrossingPlane k := crossingX k * crossingY k

/-- The singular divisor `k[x,y]/(xy)`. -/
abbrev CrossingDivisor := CrossingPlane k ⧸ Ideal.span {crossingEquation k}

/-- Restriction from the plane to its crossing divisor. -/
def crossingQuotient : CrossingPlane k →ₐ[k] CrossingDivisor k :=
  Ideal.Quotient.mkₐ k _

/-- The product `xy` is a non-zero-divisor over every commutative coefficient ring.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossingEquation_mem_nonZeroDivisors :
    crossingEquation k ∈ nonZeroDivisors (CrossingPlane k) :=
  (MvPolynomial.isRegular_X.mul MvPolynomial.isRegular_X).mem_nonZeroDivisors

/-- The crossing divisor is not formally smooth, since a normal derivation modulo `xy` would
take the value one at the origin, whereas every derivation of `xy` vanishes there.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossingDivisor_not_formallySmooth [Nontrivial k] :
    ¬ Algebra.FormallySmooth k (CrossingDivisor k) := by
  intro h
  let := h
  obtain ⟨v, a, ha⟩ := exists_normalDerivation_modulo (k := k) (crossingEquation k)
    (crossingEquation_mem_nonZeroDivisors k)
  have hv := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : k))) ha
  rw [crossingEquation, Derivation.leibniz] at hv
  simp [crossingX, crossingY] at hv

private def crossingDerivation : Derivation k (CrossingPlane k) (CrossingPlane k) :=
  MvPolynomial.mkDerivation k (fun i => if i = 0 then 1 else -1)

private lemma crossingDerivation_x : crossingDerivation k (crossingX k) = 1 := by
  simp [crossingDerivation, crossingX]

private lemma crossingDerivation_y : crossingDerivation k (crossingY k) = -1 := by
  simp [crossingDerivation, crossingY]

private lemma crossingDerivation_equation :
    crossingDerivation k (crossingEquation k) = crossingY k - crossingX k := by
  simp [crossingEquation, Derivation.leibniz, crossingDerivation_x, crossingDerivation_y,
    sub_eq_add_neg, add_comm]

private def crossingDualEvaluation : CrossingPlane k →ₐ[k] TrivSqZeroExt k k :=
  MvPolynomial.aeval (fun _ => TrivSqZeroExt.inr 1)

private lemma crossingDualEvaluation_x :
    crossingDualEvaluation k (crossingX k) = TrivSqZeroExt.inr 1 := by
  simp [crossingDualEvaluation, crossingX]

private lemma crossingDualEvaluation_y :
    crossingDualEvaluation k (crossingY k) = TrivSqZeroExt.inr 1 := by
  simp [crossingDualEvaluation, crossingY]

private lemma crossingDualEvaluation_equation :
    crossingDualEvaluation k (crossingEquation k) = 0 := by
  simp [crossingEquation, crossingDualEvaluation_x, crossingDualEvaluation_y]

/-- The one-form `y dx` remains nonzero in the differential module of the crossing divisor.
The detector sends both coordinates to the square-zero element `epsilon` and sends
`dx,dy` to `1,-1`. It kills `d(xy)` and detects `y dx` as `epsilon`.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossing_kaehler_restriction_ne_zero [Nontrivial k] :
    KaehlerDifferential.map k k (CrossingPlane k) (CrossingDivisor k)
      (crossingY k • D k (CrossingPlane k) (crossingX k)) ≠ 0 := by
  intro hz
  have hm : crossingY k • D k (CrossingPlane k) (crossingX k) ∈
      LinearMap.ker (KaehlerDifferential.map k k (CrossingPlane k) (CrossingDivisor k)) := hz
  rw [ker_kaehlerMap_of_ker_eq_span_singleton
    (k := k) (CrossingDivisor k) (f := crossingEquation k)
      Ideal.Quotient.mk_surjective Ideal.mk_ker] at hm
  obtain ⟨u, hu, w, hw, heq⟩ := Submodule.mem_sup.1 hm
  rw [Submodule.ideal_span_singleton_smul] at hu
  obtain ⟨u, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hu
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have he := congrArg (fun z => crossingDualEvaluation k
    ((crossingDerivation k).liftKaehlerDifferential z)) heq
  have heps : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) = 0 := by
    simpa [map_add, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Algebra.smul_def, crossingDerivation_x, crossingDerivation_equation,
      map_mul, map_sub, crossingDualEvaluation_x, crossingDualEvaluation_y,
      crossingDualEvaluation_equation] using he.symm
  have := congrArg TrivSqZeroExt.snd heps
  simp at this

/-- The form `y dx` has nonzero restriction to the crossing divisor, also when forms are viewed
in their total exterior algebra.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossing_restriction_ne_zero [Nontrivial k] :
    Forms.map (crossingQuotient k) (crossingY k • diff k (crossingX k)) ≠ 0 := by
  intro hz
  apply crossing_kaehler_restriction_ne_zero k
  apply (ExteriorAlgebra.ι_leftInverse (R := CrossingDivisor k)).injective
  rw [map_zero, map_smul, KaehlerDifferential.map_D,
    ← IsScalarTower.algebraMap_smul (CrossingDivisor k) (crossingY k), map_smul, ι_D]
  simpa only [Forms.map_smul, Forms.map_diff, crossingQuotient,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.algebraMap_eq] using hz

private lemma crossing_wedge :
    diff k (crossingEquation k) * (crossingY k • diff k (crossingX k)) =
      crossingEquation k • (diff k (crossingY k) * diff k (crossingX k)) := by
  simp [crossingEquation, Derivation.leibniz, add_mul, smul_smul, diff_mul_self, mul_comm]

section Localization

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra (CrossingPlane k) T]
  [IsScalarTower k (CrossingPlane k) T] [IsLocalization.Away (crossingEquation k) T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k (CrossingPlane k) T)

/-- Inverting `xy` makes `theta * (y dx)` the regular two-form `dy * dx`.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossing_theta_mul :
    theta k (crossingEquation k) T * reg (crossingY k • diff k (crossingX k)) =
      reg (diff k (crossingY k) * diff k (crossingX k)) := by
  have he : crossingEquation k •
      (theta k (crossingEquation k) T * reg (crossingY k • diff k (crossingX k))) =
      crossingEquation k • reg (diff k (crossingY k) * diff k (crossingX k)) := by
    rw [← smul_mul_assoc, self_smul_theta, ← map_mul, crossing_wedge, Forms.map_smul]
    rfl
  apply (IsLocalization.Away.algebraMap_isUnit (S := T) (crossingEquation k)).smul_left_cancel.1
  simpa only [IsScalarTower.algebraMap_smul] using he

/-- The regular presentation `(dy * dx, 0)` and logarithmic presentation `(0, y dx)` give the
same logarithmic form on the complement of the crossing divisor.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossing_logMk_eq :
    logMk k (crossingEquation k) T (diff k (crossingY k) * diff k (crossingX k), 0) =
      logMk k (crossingEquation k) T (0, crossingY k • diff k (crossingX k)) := by
  apply Subtype.ext
  simpa only [coe_logMk, map_zero, mul_zero, add_zero, zero_add] using
    (crossing_theta_mul k T).symm

/-- No function on logarithmic forms for the crossing divisor can satisfy the proposed residue
formula on every presentation: the regular presentation has residue zero, while `(0, y dx)`
has nonzero residue. No linearity of the hypothetical residue is needed.

Blueprint: `prop:dr-crossing-example`. -/
theorem crossing_no_residue [Nontrivial k] :
    ¬ ∃ ρ : logForms k (crossingEquation k) T → Forms k (CrossingDivisor k),
      ∀ ω η : Forms k (CrossingPlane k),
        ρ (logMk k (crossingEquation k) T (ω, η)) = Forms.map (crossingQuotient k) η := by
  rintro ⟨ρ, hρ⟩
  have he := congrArg ρ (crossing_logMk_eq k T)
  rw [hρ, hρ, map_zero] at he
  exact crossing_restriction_ne_zero k he.symm

end Localization

end OrlikSolomon.DeRham.Examples
