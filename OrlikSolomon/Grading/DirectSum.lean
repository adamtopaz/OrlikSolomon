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

section ShiftedMaps

variable {R ι : Type*} [Semiring R] [DecidableEq ι] [Add ι]
  (M N : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Assemble degreewise linear maps of shift `a` into a map of external direct sums. -/
def shiftedDirectSumMap (a : ι) (f : ∀ i, M i →ₗ[R] N (i + a)) :
    (⨁ i, M i) →ₗ[R] ⨁ i, N i :=
  DirectSum.toModule R ι _ fun i ↦ (lof R ι N (i + a)).comp (f i)

@[simp]
theorem shiftedDirectSumMap_lof (a : ι) (f : ∀ i, M i →ₗ[R] N (i + a)) (i : ι) (x : M i) :
    shiftedDirectSumMap M N a f (lof R ι M i x) = lof R ι N (i + a) (f i x) :=
  DirectSum.toModule_lof R i x

/-- The sum of maps of shift `a` is homogeneous of shift `a` for the canonical internal gradings. -/
theorem isHomogeneousOfShift_shiftedDirectSumMap (a : ι) (f : ∀ i, M i →ₗ[R] N (i + a)) :
    IsHomogeneousOfShift (directSumGrading (R := R) M) (directSumGrading (R := R) N) a
      (shiftedDirectSumMap M N a f) := by
  rw [isHomogeneousOfShift_directSumGrading_iff]
  intro i x
  rw [shiftedDirectSumMap_lof]
  exact lof_mem_directSumGrading N _ _

end ShiftedMaps

section ReindexEquivalences

variable {R ι κ : Type*} [Semiring R] [DecidableEq ι] [DecidableEq κ]
  (M : ι → Type*) (N : κ → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]

/-- Sum component equivalences whose degrees are reindexed by an equivalence. This constructs,
in particular, the direct sum of degreewise purity equivalences without choosing bases. -/
def reindexedDirectSumEquiv (e : ι ≃ κ) (f : ∀ i, M i ≃ₗ[R] N (e i)) :
    (⨁ i, M i) ≃ₗ[R] ⨁ j, N j :=
  DirectSum.congrLinearEquiv f ≪≫ₗ (DirectSum.lequivCongrLeft R e.symm).symm

@[simp]
theorem reindexedDirectSumEquiv_lof (e : ι ≃ κ) (f : ∀ i, M i ≃ₗ[R] N (e i))
    (i : ι) (x : M i) :
    reindexedDirectSumEquiv M N e f (lof R ι M i x) = lof R κ N (e i) (f i x) := by
  simp only [reindexedDirectSumEquiv, LinearEquiv.trans_apply, coe_congrLinearEquiv,
    DirectSum.lmap_lof]
  exact DirectSum.lequivCongrLeft_symm_lof R

end ReindexEquivalences

section Exactness

variable {R ι : Type*} [Semiring R] [DecidableEq ι] [AddGroup ι]
  (M N P : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

/-- A degreewise exact pair of shifted maps remains exact on finite-support direct sums.
Blueprint: exactness in `lem:standard-bridge`. -/
theorem exact_shiftedDirectSumMap (a b : ι)
    (f : ∀ i, M i →ₗ[R] N (i + a)) (g : ∀ j, N j →ₗ[R] P (j + b))
    (h : ∀ i, Function.Exact (f i) (g (i + a))) :
    Function.Exact (shiftedDirectSumMap M N a f) (shiftedDirectSumMap N P b g) := by
  apply ((isHomogeneousOfShift_shiftedDirectSumMap M N a f).exact_iff_forall_mem
    (isHomogeneousOfShift_shiftedDirectSumMap N P b g)).2
  intro i j hij y hy
  subst j
  obtain ⟨y, rfl⟩ := hy
  constructor
  · intro hgy
    have hg : g (i + a) y = 0 := DirectSum.of_injective (β := P) _ (by
      rw [shiftedDirectSumMap_lof] at hgy
      simpa only [DirectSum.lof_eq_of, map_zero] using hgy)
    obtain ⟨x, hx⟩ := (h i y).1 hg
    exact ⟨lof R ι M i x, lof_mem_directSumGrading M i x, by
      simp only [shiftedDirectSumMap_lof, hx]⟩
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    have hxy : f i x = y := DirectSum.of_injective (β := N) _ (by
      rw [shiftedDirectSumMap_lof] at hx
      simpa only [DirectSum.lof_eq_of] using hx)
    rw [shiftedDirectSumMap_lof, ← hxy, (h i _).2 ⟨x, rfl⟩, map_zero]

end Exactness

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
