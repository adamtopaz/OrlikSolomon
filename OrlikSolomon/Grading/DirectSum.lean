/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Grading.Basic

/-!
# The internal grading of an external direct sum

An external direct sum of modules is internally graded by the ranges of its summand inclusions.
The component equivalences identify these ranges with the original modules. For a graded algebra,
the internal grading preserves the algebra structure already carried by the external direct sum.

Blueprint: the direct-sum construction in `lem:standard-bridge`.
-/

@[expose] public section

noncomputable section

open DirectSum

namespace OrlikSolomon

section Modules

variable {R ι : Type*} [Semiring R] [DecidableEq ι]
  (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The degree `i` piece of an external direct sum is the range of its summand inclusion. -/
def directSumGrading (i : ι) : Submodule R (⨁ i, M i) :=
  (lof R ι M i).range

/-- A homogeneous element has a representative in its original summand. -/
theorem mem_directSumGrading_iff {i : ι} {x : ⨁ i, M i} :
    x ∈ directSumGrading (R := R) M i ↔ ∃ y : M i, lof R ι M i y = x :=
  Iff.rfl

/-- The summand inclusion lands in its homogeneous component. -/
theorem lof_mem_directSumGrading (i : ι) (x : M i) :
    lof R ι M i x ∈ directSumGrading (R := R) M i :=
  ⟨x, rfl⟩

/-- Each original summand is canonically its homogeneous component in the direct sum. -/
def directSumComponentEquiv (i : ι) : M i ≃ₗ[R] directSumGrading (R := R) M i :=
  LinearEquiv.ofInjective (lof R ι M i) (DirectSum.of_injective (β := M) i)

@[simp]
theorem coe_directSumComponentEquiv (i : ι) (x : M i) :
    (directSumComponentEquiv (R := R) M i x : ⨁ i, M i) = lof R ι M i x := rfl

/-- The ranges of the summand inclusions give the canonical internal decomposition. -/
instance directSumGradingDecomposition : Decomposition (directSumGrading (R := R) M) := by
  let e := congrLinearEquiv (directSumComponentEquiv (R := R) M)
  apply Decomposition.ofLinearMap (directSumGrading (R := R) M) e.toLinearMap
  · apply DirectSum.linearMap_ext R
    intro i
    ext x
    simp [e, coe_congrLinearEquiv]
  · apply DirectSum.linearMap_ext R
    intro i
    ext x
    obtain ⟨x, rfl⟩ := (directSumComponentEquiv (R := R) M i).surjective x
    simp [e, coe_congrLinearEquiv]

/-- To check homogeneity out of the canonical direct-sum grading, it suffices to check the
original summand inclusions. This criterion applies to plain functions as well as linear maps. -/
theorem isHomogeneousOfShift_directSumGrading_iff [Add ι] {N σ : Type*} [SetLike σ N]
    (𝒩 : ι → σ) (a : ι) (f : (⨁ i, M i) → N) :
    IsHomogeneousOfShift (directSumGrading (R := R) M) 𝒩 a f ↔
      ∀ i (x : M i), f (lof R ι M i x) ∈ 𝒩 (i + a) := by
  constructor
  · intro hf i x
    exact hf (lof_mem_directSumGrading M i x)
  · rintro hf i _ ⟨x, rfl⟩
    exact hf i x

end Modules

section Algebras

variable {R ι : Type*} [CommSemiring R] [DecidableEq ι] [AddMonoid ι]
  (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
  [GSemiring A] [GAlgebra R A]

/-- Graded products on the summands give the standard internal algebra grading of their sum. -/
instance directSumGradedAlgebra : GradedAlgebra (directSumGrading (R := R) A) where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨GradedMonoid.GMul.mul x y, (of_mul_of (A := A) x y).symm⟩

end Algebras

end OrlikSolomon
