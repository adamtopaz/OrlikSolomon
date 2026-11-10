/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.RatFunc.Field
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Actual automorphisms of a rational function field

Polynomial translation extends to an automorphism of `F(t)`, with explicit variable,
constant and inverse formulas. The automorphism group is nontrivial over every field,
and finite when the constant field is finite: its elements embed into the pairs of
canonical numerator/denominator polynomials of degree less than two.

These are field-theoretic ingredients for blueprint `prop:t08`. Finiteness and
nontriviality are theorems, not global instances; this file defines no topology.

The forward polynomial, variable and constant formulas are plain rewrite lemmas.
Expanding them during simplification can hide an inner translation from ordinary
equivalence cancellation, including on compound rational functions.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT.RatFuncExamples

universe u

variable (F : Type u) [Field F]

/-- Translation of the rational variable, obtained by extending the genuine polynomial
automorphism to its fraction field. -/
noncomputable def translation (a : F) : RatFunc F ≃ₐ[F] RatFunc F :=
  IsFractionRing.algEquivOfAlgEquiv (K := RatFunc F) (L := RatFunc F)
    (Polynomial.algEquivAevalXAddC a)

/-- Rational translation agrees with polynomial translation on the polynomial subring. -/
theorem translation_algebraMap (a : F) (P : Polynomial F) :
    translation F a (algebraMap (Polynomial F) (RatFunc F) P) =
      algebraMap (Polynomial F) (RatFunc F) (Polynomial.algEquivAevalXAddC a P) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

/-- Translation sends the variable to the variable plus the chosen constant. -/
theorem translation_X (a : F) :
    translation F a RatFunc.X = RatFunc.X + RatFunc.C a := by
  simpa using translation_algebraMap F a Polynomial.X

/-- Translation fixes every element of the constant field. -/
theorem translation_C (a b : F) :
    translation F a (RatFunc.C b) = RatFunc.C b :=
  (translation F a).commutes b

/-- Translation by zero is the identity automorphism. -/
@[simp] theorem translation_zero : translation F 0 = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext_X F
  simp [translation_X]

/-- Negating the translation parameter gives the inverse automorphism. This orientation
preserves ordinary equivalence cancellation under `simp`. -/
@[simp] theorem translation_neg (a : F) :
    translation F (-a) = (translation F a).symm := by
  simp only [translation, IsFractionRing.algEquivOfAlgEquiv_symm,
    Polynomial.algEquivAevalXAddC_symm]

/-- Both ordinary inverse cancellations simplify on a genuine compound rational function.
This also guards against forward-expansion rules that hide the inner equivalence. -/
theorem translation_fraction_inverse_forms (a : F) :
    (translation F a).symm (translation F a (1 / (RatFunc.X + RatFunc.C a))) =
      1 / (RatFunc.X + RatFunc.C a) ∧
    translation F a ((translation F a).symm (1 / (RatFunc.X + RatFunc.C a))) =
      1 / (RatFunc.X + RatFunc.C a) := by
  simp

/-- A translation is the identity exactly when its parameter is zero. -/
@[simp] theorem translation_eq_one_iff (a : F) :
    translation F a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hx := DFunLike.congr_fun h RatFunc.X
    simpa [translation_X] using hx
  · rintro rfl
    exact translation_zero F

/-- Translation by one is a nonidentity automorphism, including in characteristic two. -/
theorem translation_one_ne_one : translation F 1 ≠ 1 := by
  simp

/-- The rational function field has a nontrivial automorphism group over its constants. -/
theorem nontrivial_algEquiv : Nontrivial (RatFunc F ≃ₐ[F] RatFunc F) :=
  ⟨⟨translation F 1, 1, translation_one_ne_one F⟩⟩

private theorem mem_degreeLT_two (P : Polynomial F) (h : P.natDegree ≤ 1) :
    P ∈ Polynomial.degreeLT F 2 := by
  apply Polynomial.mem_degreeLT.mpr
  exact Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le h))

/-- Over a finite constant field, the rational function field has finitely many
automorphisms. Canonical numerator and denominator coefficients give the finite bound. -/
theorem finite_algEquiv [Finite F] : Finite (RatFunc F ≃ₐ[F] RatFunc F) := by
  let : Finite (Polynomial.degreeLT F 2) :=
    Finite.of_injective (Polynomial.degreeLTEquiv F 2)
      (Polynomial.degreeLTEquiv F 2).injective
  let encode (σ : RatFunc F ≃ₐ[F] RatFunc F) :
      Polynomial.degreeLT F 2 × Polynomial.degreeLT F 2 :=
    (⟨(σ RatFunc.X).num, mem_degreeLT_two F _
      ((le_max_left _ _).trans_eq (max_natDegree_image_X F σ))⟩,
     ⟨(σ RatFunc.X).denom, mem_degreeLT_two F _
      ((le_max_right _ _).trans_eq (max_natDegree_image_X F σ))⟩)
  apply Finite.of_injective encode
  intro σ τ h
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext_X F
  have hnum : (σ RatFunc.X).num = (τ RatFunc.X).num :=
    congrArg (fun p => (p.1 : Polynomial F)) h
  have hdenom : (σ RatFunc.X).denom = (τ RatFunc.X).denom :=
    congrArg (fun p => (p.2 : Polynomial F)) h
  change σ RatFunc.X = τ RatFunc.X
  rw [← RatFunc.num_div_denom (σ RatFunc.X),
    ← RatFunc.num_div_denom (τ RatFunc.X), hnum, hdenom]

/-- Over every prime field, the actual rational function automorphism group is finite
and nontrivial. Blueprint: field-theoretic ingredients of `prop:t08`. -/
theorem prime_field_automorphisms (p : ℕ) [Fact p.Prime] :
    Finite (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) ∧
      Nontrivial (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) :=
  ⟨finite_algEquiv (ZMod p), nontrivial_algEquiv (ZMod p)⟩

end OrlikSolomon.HyperplaneGT.RatFuncExamples
