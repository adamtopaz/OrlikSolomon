/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Examples.Realization
public import OrlikSolomon.Presentation.Generators
public import OrlikSolomon.Presentation.Ordinary

/-!
# Regressions for the affine structure theorem

These instantiate the public statements of `Presentation/Structure` and `Presentation/Ordinary` on
the blueprint's regression list. The literal types are written out, so that they test the instances
a user meets as well as the statements.

* `R = ℤ`: `OS_ℤ^p(𝒜) ⊗[ℤ] B_{w - p} ≃ H^{p, w}(U_𝒜)`, and the diagonal.
* `R = ZMod 2`: the same, and the two rational points of `𝔸¹` over `F₂`, whose complement has no
  `F₂`-points. There `e₀ e₁ = 0`, and yet `H^{1, 1}` is free of rank two over `F₂`, with the two
  logarithms independent (`nonempty_basis_grading_twoPoints`, `linearIndependent_logClass`).
* The zero coefficient ring: every statement applies, and every group vanishes.
* Dimension zero: `OS_R(𝒜)` vanishes above degree zero (`degree_eq_bot_of_subsingleton`).
* The case `R = B`, in which the two `B`-algebra structures of `T.C.obj A` could be confused.

Blueprint: the regression list, for `thm:affine` and `cor:ordinary`.
-/

@[expose] public section

noncomputable section

open DirectSum Module
open scoped TensorProduct
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.OrdinaryExamples

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-! ### Integer coefficients -/

section Integers

variable {B : Type w} [CommRing B] {ℬ : ℤ → Submodule ℤ B} [GradedAlgebra ℬ]
  (T : OrdinaryTheory.{u, 0, w, z} k ℬ) (𝒜 : Arrangement k V)

/-- The ordinary groups, with integer coefficients. The equivalence is linear for the module
structure of `T.grading` that comes from the field `T.algebra`, so its type is left to be
inferred. -/
example (p : ℕ) (w : ℤ) := T.ordinaryComponentEquiv 𝒜 p w

/-- The ordinary groups, with integer coefficients, in a literal statement. A literal `≃ₗ[ℤ]` picks
the canonical `ℤ`-module structure of the piece, which agrees only propositionally with the one from
`T.algebra`, as at `R = B`. Pass through additive equivalences, with a coercion. -/
example (p : ℕ) (w : ℤ) :
    degree ℤ 𝒜 p ⊗[ℤ] ℬ (w - p) ≃ₗ[ℤ] T.grading (complement 𝒜) ((p : ℤ), w) :=
  AddEquiv.toIntLinearEquiv (T.ordinaryComponentEquiv 𝒜 p w : _ ≃+ _)

/-- The formula for the ordinary groups, with integer coefficients. -/
example (p : ℕ) (w : ℤ) (x : degree ℤ 𝒜 p) (b : ℬ (w - p)) :
    (T.ordinaryComponentEquiv 𝒜 p w (x ⊗ₜ[ℤ] b) : T.C.obj (complement 𝒜)) =
      (b : B) • T.realizationOverR 𝒜 x := by
  simp

/-- The diagonal, with integer coefficients, in a literal statement. As for the ordinary groups,
pass through ring equivalences, with a coercion. -/
example : OSAlgebra ℤ 𝒜 ≃ₐ[ℤ] ⨁ q : ℕ, diagonalGrading (T.grading (complement 𝒜)) q :=
  RingEquiv.toIntAlgEquiv (T.diagonalEquiv 𝒜 : _ ≃+* _)

/-- The formula for the diagonal, with integer coefficients. -/
example (x : OSAlgebra ℤ 𝒜) :
    coeAlgHom _ (T.diagonalEquiv 𝒜 x) = T.realizationOverR 𝒜 x := by
  simp

/-- Integer multiples commute with the ordinary groups, whatever module structure is used. -/
example (p : ℕ) (w : ℤ) (n : ℤ) (x : degree ℤ 𝒜 p ⊗[ℤ] ℬ (w - p)) :
    T.ordinaryComponentEquiv 𝒜 p w (n • x) = n • T.ordinaryComponentEquiv 𝒜 p w x := by
  simp

/-- The monomial basis, with integer coefficients. -/
example (b : T.LogMonomialBasis 𝒜) (i : b.Index) :
    b.osBasisOverR i = word (generator ℤ 𝒜) (b.word i) := by
  simp

end Integers

/-! ### Characteristic two -/

section CharTwo

variable {B : Type w} [CommRing B] [Algebra (ZMod 2) B] {ℬ : ℤ → Submodule (ZMod 2) B}
  [GradedAlgebra ℬ]

/-- The ordinary groups, in characteristic two. -/
example (T : OrdinaryTheory.{u, 0, w, z} k ℬ) (𝒜 : Arrangement k V) (p : ℕ) (w : ℤ) :
    degree (ZMod 2) 𝒜 p ⊗[ZMod 2] ℬ (w - p) ≃ₗ[ZMod 2] T.grading (complement 𝒜) ((p : ℤ), w) :=
  T.ordinaryComponentEquiv 𝒜 p w

/-- The diagonal, in characteristic two. -/
example (T : OrdinaryTheory.{u, 0, w, z} k ℬ) (𝒜 : Arrangement k V) :
    OSAlgebra (ZMod 2) 𝒜 ≃ₐ[ZMod 2] ⨁ q : ℕ, diagonalGrading (T.grading (complement 𝒜)) q :=
  T.diagonalEquiv 𝒜

open Sanity RealizationExamples

/-- On the two rational points of `𝔸¹` over `F₂`, the group `H^{1, 1}` is free of rank two over the
coefficients. The complement has no `F₂`-points, by `isEmpty_algHom_twoPoints`, so this is not seen
on points, and `2 = 0` in `ZMod 2`. -/
theorem nonempty_basis_grading_twoPoints (T : OrdinaryTheory.{0, 0, w, z} (ZMod 2) ℬ) :
    Nonempty (Basis (Fin 2) (ZMod 2)
      (T.grading (complement twoPoints) (((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) := by
  have h := T.nonempty_basis_grading_bettiNumber twoPoints 1
  rwa [bettiNumber_one_twoPoints] at h

/-- The diagonal sends `e₀` to `[x]` for the equation `x` of the point `0`, in the summand of degree
one, with no further input to `simp`. -/
example (T : OrdinaryTheory.{0, 0, w, z} (ZMod 2) ℬ) :
    T.diagonalEquiv twoPoints (generator (ZMod 2) twoPoints pointZero) =
      of _ 1 ⟨T.logClass (complementUnit twoPoints (AffineMap.id _ _)
        (.of_mem zeroLocus_id_mem_twoPoints)), T.logClass_mem_diagonalGrading _⟩ := by
  simp

end CharTwo

/-! ### Independence of the logarithms -/

section Independence

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)

/-- The logarithms of the hyperplanes of an arrangement are linearly independent over `R`, for every
coefficient ring, including `ZMod 2`. -/
theorem linearIndependent_logClass (𝒜 : Arrangement k V) :
    LinearIndependent R fun H : 𝒜 ↦ T.logClass (equationUnit 𝒜 H) := by
  have h := (linearIndependent_generator R 𝒜).map' (T.realizationOverR 𝒜).toLinearMap
    (LinearMap.ker_eq_bot.2 (T.injective_realizationOverR 𝒜))
  simpa [Function.comp_def] using h

end Independence

/-! ### Degenerate cases -/

section Degenerate

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)

include T in
/-- In dimension zero, the presentation vanishes above degree zero. -/
theorem degree_eq_bot_of_subsingleton [Subsingleton V] (𝒜 : Arrangement k V) (q : ℕ) :
    degree R 𝒜 (q + 1) = ⊥ :=
  T.degree_eq_bot_of_finrank_lt <| by
    rw [finrank_zero_of_subsingleton]
    exact Nat.succ_pos q

/-- The structure theorem with zero coefficients. -/
example (𝒜 : Arrangement k V) :
    OSAlgebra PUnit.{w + 1} 𝒜 ≃ₐ[PUnit.{w + 1}]
      (Sanity.zeroTheory.{u, v, w, z} k).C.obj (complement 𝒜) :=
  (Sanity.zeroTheory.{u, v, w, z} k).affineEquiv 𝒜

/-- At `R = B`, the diagonal piece is the realization map all the same. Here `T.C.obj A` has two
`B`-algebra structures, see `Cohomology/Axioms`, and this tests that the statements mix them
correctly: the types are left to be inferred. -/
example {ℬ' : ℤ → Submodule B B} [GradedAlgebra ℬ'] (T : OrdinaryTheory.{u, w, w, z} k ℬ')
    (𝒜 : Arrangement k V) (x : OSAlgebra B 𝒜) :
    coeAlgHom _ (T.diagonalEquiv 𝒜 x) = T.realizationOverR 𝒜 x :=
  T.coeAlgHom_diagonalEquiv x

end Degenerate

end OrlikSolomon.OrdinaryExamples
