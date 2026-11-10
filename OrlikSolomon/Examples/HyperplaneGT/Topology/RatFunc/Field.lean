/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Constants and generators in a rational function field

The only elements of `F(t)` algebraic over `F` are constants. Thus every algebraic
intermediate field is the base field. An `F`-automorphism is determined by its value on
`t`, and the canonical numerator and denominator of that value have maximum degree one.

These Mathlib-only results support the counterexample in blueprint `prop:t08`; they do
not assert its topological conclusions.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT.RatFuncExamples

universe u v

variable (F : Type u) [Field F]

/-- The elements of `F(t)` algebraic over `F` are exactly its constants. -/
theorem isAlgebraic_iff_exists_constant (f : RatFunc F) :
    IsAlgebraic F f ↔ ∃ a : F, f = RatFunc.C a := by
  constructor
  · intro hf
    by_contra h
    exact RatFunc.transcendental_of_ne_C f h hf
  · rintro ⟨a, rfl⟩
    exact isAlgebraic_algebraMap a

/-- An algebraic intermediate field in `F(t)` consists only of constants. -/
theorem intermediateField_eq_bot_of_isAlgebraic
    (E : IntermediateField F (RatFunc F)) [Algebra.IsAlgebraic F E] : E = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxalg : IsAlgebraic F x :=
    (isAlgebraic_algebraMap_iff (R := F) (S := E) (A := RatFunc F)
      (algebraMap E (RatFunc F)).injective).mpr
        (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : E))
  obtain ⟨a, rfl⟩ := (isAlgebraic_iff_exists_constant F x).mp hxalg
  exact ⟨a, rfl⟩

/-- Every finite-dimensional intermediate field in `F(t)` is the base field. -/
theorem intermediateField_eq_bot_of_finiteDimensional
    (E : IntermediateField F (RatFunc F)) [FiniteDimensional F E] : E = ⊥ :=
  intermediateField_eq_bot_of_isAlgebraic F E

/-- Evaluation at the rational variable determines an algebra homomorphism. -/
theorem algHom_ext_X {A : Type v} [Semiring A] [Algebra F A]
    {f g : RatFunc F →ₐ[F] A} (h : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial F))
  apply Polynomial.algHom_ext
  change f (algebraMap (Polynomial F) (RatFunc F) Polynomial.X) =
    g (algebraMap (Polynomial F) (RatFunc F) Polynomial.X)
  simpa only [RatFunc.algebraMap_X] using h

/-- An automorphism's image of the variable still generates the rational function field. -/
theorem adjoin_image_X (σ : RatFunc F ≃ₐ[F] RatFunc F) :
    IntermediateField.adjoin F {σ RatFunc.X} = ⊤ := by
  have h : (σ : RatFunc F →ₐ[F] RatFunc F) '' {RatFunc.X} = {σ RatFunc.X} :=
    Set.image_singleton
  rw [← h, ← IntermediateField.adjoin_map, RatFunc.adjoin_X,
    ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top]

/-- The canonical numerator and denominator of an automorphism's image of the variable
have maximum degree one. -/
theorem max_natDegree_image_X (σ : RatFunc F ≃ₐ[F] RatFunc F) :
    max (σ RatFunc.X).num.natDegree (σ RatFunc.X).denom.natDegree = 1 := by
  rw [← RatFunc.finrank_eq_max_natDegree, adjoin_image_X, IntermediateField.finrank_top]

end OrlikSolomon.HyperplaneGT.RatFuncExamples
