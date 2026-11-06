/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of internal gradings

The tensor product of internally graded modules has the product grading. For graded algebras,
coarsening that product grading along an additive degree map gives an internal algebra grading.
The weighted tensor bigrading assigns degree `(n, w + n)` to a tensor of a coefficient of weight
`w` and an element of degree `n`. Blueprint: `def:grading`, `lem:os-basic`.
-/

@[expose] public section

noncomputable section

open TensorProduct DirectSum

namespace OrlikSolomon

section Modules

variable {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (ℳ : ι → Submodule R M) (𝒩 : κ → Submodule R N)

/-- The tensor product component of bidegree `(i, j)` is the image of `ℳ i ⊗ 𝒩 j`.
No flatness assumption is needed: a homogeneous component is a direct summand. -/
def tensorProductGrading (i : ι × κ) : Submodule R (M ⊗[R] N) :=
  (TensorProduct.map (ℳ i.1).subtype (𝒩 i.2).subtype).range

/-- Pure tensors of homogeneous elements belong to their product component. -/
theorem tmul_mem_tensorProductGrading {i : ι} {j : κ} {m : M} {n : N}
    (hm : m ∈ ℳ i) (hn : n ∈ 𝒩 j) :
    m ⊗ₜ[R] n ∈ tensorProductGrading ℳ 𝒩 (i, j) :=
  ⟨⟨m, hm⟩ ⊗ₜ[R] ⟨n, hn⟩, rfl⟩

/-- A product component is spanned by pure tensors of homogeneous elements. -/
theorem tensorProductGrading_eq_span (i : ι × κ) :
    tensorProductGrading ℳ 𝒩 i =
      Submodule.span R {x | ∃ m ∈ ℳ i.1, ∃ n ∈ 𝒩 i.2, m ⊗ₜ[R] n = x} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul m n => exact Submodule.subset_span ⟨m, m.2, n, n.2, rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, n, hn, rfl⟩
    exact tmul_mem_tensorProductGrading ℳ 𝒩 hm hn

/-- Tensor products of maps that preserve homogeneous components preserve the product grading. -/
theorem map_mem_tensorProductGrading {M' N' : Type*} [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] (ℳ' : ι → Submodule R M') (𝒩' : κ → Submodule R N')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : ∀ i, ∀ m ∈ ℳ i, f m ∈ ℳ' i) (hg : ∀ j, ∀ n ∈ 𝒩 j, g n ∈ 𝒩' j)
    {i : ι × κ} {x : M ⊗[R] N} (hx : x ∈ tensorProductGrading ℳ 𝒩 i) :
    TensorProduct.map f g x ∈ tensorProductGrading ℳ' 𝒩' i := by
  obtain ⟨x, rfl⟩ := hx
  induction x with
  | tmul m n =>
    simpa only [TensorProduct.map_tmul, Submodule.coe_subtype] using
      tmul_mem_tensorProductGrading ℳ' 𝒩' (hf _ m m.2) (hg _ n n.2)
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

variable [DecidableEq ι] [DecidableEq κ] [Decomposition ℳ] [Decomposition 𝒩]

/-- Tensor products distribute over the internal decompositions of both factors. -/
def tensorProductDecomposeEquiv :
    M ⊗[R] N ≃ₗ[R] ⨁ i : ι × κ, (ℳ i.1) ⊗[R] (𝒩 i.2) :=
  TensorProduct.congr (decomposeLinearEquiv ℳ) (decomposeLinearEquiv 𝒩) ≪≫ₗ
    TensorProduct.directSum R R (fun i ↦ ℳ i) (fun j ↦ 𝒩 j)

/-- Decomposing a tensor supported in one product component gives its direct-sum inclusion. -/
@[simp]
theorem tensorProductDecomposeEquiv_map (i : ι × κ) (x : (ℳ i.1) ⊗[R] (𝒩 i.2)) :
    tensorProductDecomposeEquiv ℳ 𝒩
        (TensorProduct.map (ℳ i.1).subtype (𝒩 i.2).subtype x) =
      lof R _ (fun i : ι × κ ↦ (ℳ i.1) ⊗[R] (𝒩 i.2)) i x := by
  induction x with
  | tmul m n => simp [tensorProductDecomposeEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Recombining a direct-sum component is the tensor product of the component inclusions. -/
@[simp]
theorem tensorProductDecomposeEquiv_symm_lof (i : ι × κ)
    (x : (ℳ i.1) ⊗[R] (𝒩 i.2)) :
    (tensorProductDecomposeEquiv ℳ 𝒩).symm
        (lof R _ (fun i : ι × κ ↦ (ℳ i.1) ⊗[R] (𝒩 i.2)) i x) =
      TensorProduct.map (ℳ i.1).subtype (𝒩 i.2).subtype x := by
  rw [LinearEquiv.symm_apply_eq, tensorProductDecomposeEquiv_map]

/-- The map from the tensor product of two homogeneous components to the full tensor product
is injective, since both components are direct summands. -/
theorem tensorProductGrading_map_injective (i : ι × κ) :
    Function.Injective (TensorProduct.map (ℳ i.1).subtype (𝒩 i.2).subtype) := by
  intro x y h
  have h' := congrArg (tensorProductDecomposeEquiv ℳ 𝒩) h
  rw [tensorProductDecomposeEquiv_map, tensorProductDecomposeEquiv_map] at h'
  exact DirectSum.of_injective (β := fun i : ι × κ ↦ (ℳ i.1) ⊗[R] (𝒩 i.2)) i h'

/-- Each product component is canonically the tensor product of the two homogeneous components. -/
def tensorProductGradingEquiv (i : ι × κ) :
    (ℳ i.1) ⊗[R] (𝒩 i.2) ≃ₗ[R] tensorProductGrading ℳ 𝒩 i :=
  LinearEquiv.ofInjective _ (tensorProductGrading_map_injective ℳ 𝒩 i)

@[simp]
theorem coe_tensorProductGradingEquiv (i : ι × κ) (x : (ℳ i.1) ⊗[R] (𝒩 i.2)) :
    (tensorProductGradingEquiv ℳ 𝒩 i x : M ⊗[R] N) =
      TensorProduct.map (ℳ i.1).subtype (𝒩 i.2).subtype x := rfl

/-- The product grading decomposes the tensor product without any flatness hypothesis. -/
instance tensorProductGradingDecomposition : Decomposition (tensorProductGrading ℳ 𝒩) := by
  let e := tensorProductDecomposeEquiv ℳ 𝒩 ≪≫ₗ
    congrLinearEquiv (tensorProductGradingEquiv ℳ 𝒩)
  have h : (coeLinearMap (tensorProductGrading ℳ 𝒩)) ∘ₗ e = LinearMap.id := by
    apply (LinearMap.cancel_right (tensorProductDecomposeEquiv ℳ 𝒩).symm.surjective).1
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    change coeLinearMap (tensorProductGrading ℳ 𝒩)
      (congrLinearEquiv (tensorProductGradingEquiv ℳ 𝒩)
        (tensorProductDecomposeEquiv ℳ 𝒩
          ((tensorProductDecomposeEquiv ℳ 𝒩).symm (lof R _ _ i x)))) =
      (tensorProductDecomposeEquiv ℳ 𝒩).symm (lof R _ _ i x)
    rw [LinearEquiv.apply_symm_apply]
    simp [coe_congrLinearEquiv]
  refine .ofLinearMap _ e h ?_
  ext i x
  obtain ⟨x, rfl⟩ := (tensorProductGradingEquiv ℳ 𝒩 i).surjective x
  simp [e, coe_congrLinearEquiv]

end Modules

section TransportModules

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (ℳ : ι → Submodule R M) (e : M ≃ₗ[R] N)

/-- Transport an internal grading along a linear equivalence by mapping each component. -/
def transportGrading (i : ι) : Submodule R N :=
  (ℳ i).map e.toLinearMap

/-- Membership in a transported component can be tested using the inverse equivalence. -/
@[simp]
theorem mem_transportGrading_iff {i : ι} {n : N} :
    n ∈ transportGrading ℳ e i ↔ e.symm n ∈ ℳ i := by
  rw [transportGrading, Submodule.map_equiv_eq_comap_symm]
  rfl

/-- The equivalence sends each original homogeneous component onto its transported component. -/
theorem apply_mem_transportGrading_iff {i : ι} {m : M} :
    e m ∈ transportGrading ℳ e i ↔ m ∈ ℳ i := by
  simp only [mem_transportGrading_iff, e.symm_apply_apply]

/-- The linear equivalence restricts to an equivalence of each original and transported piece. -/
def transportGradingEquiv (i : ι) : ℳ i ≃ₗ[R] transportGrading ℳ e i :=
  e.submoduleMap (ℳ i)

@[simp]
theorem coe_transportGradingEquiv (i : ι) (m : ℳ i) :
    (transportGradingEquiv ℳ e i m : N) = e m := rfl

variable [DecidableEq ι] [Decomposition ℳ]

/-- Transport preserves the internal direct-sum decomposition. -/
instance transportGradingDecomposition : Decomposition (transportGrading ℳ e) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (Decomposition.isInternal ℳ).submodule_iSupIndep.map_orderIso
      (Submodule.orderIsoMapComap e)
  · change (⨆ i, (ℳ i).map e.toLinearMap) = ⊤
    rw [← Submodule.map_iSup, (Decomposition.isInternal ℳ).submodule_iSup_eq_top,
      Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

end TransportModules

section TransportAlgebras

variable {R A C ι : Type*} [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
  [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (e : A ≃ₐ[R] C)

/-- Transport an internal algebra grading along an algebra equivalence. -/
instance transportGradingGradedAlgebra : GradedAlgebra (transportGrading 𝒜 e.toLinearEquiv) where
  one_mem := by
    rw [mem_transportGrading_iff]
    change e.symm 1 ∈ 𝒜 0
    rw [map_one]
    exact SetLike.one_mem_graded 𝒜
  mul_mem i j x y hx hy := by
    rw [mem_transportGrading_iff] at hx hy ⊢
    change e.symm x ∈ 𝒜 i at hx
    change e.symm y ∈ 𝒜 j at hy
    change e.symm (x * y) ∈ 𝒜 (i + j)
    rw [map_mul]
    exact SetLike.mul_mem_graded hx hy

end TransportAlgebras

section TensorAlgebras

variable {R B A ι κ : Type*} [CommSemiring R] [Semiring B] [Semiring A]
  [Algebra R B] [Algebra R A] [DecidableEq ι] [DecidableEq κ]
  [AddMonoid ι] [AddMonoid κ]
  (ℬ : ι → Submodule R B) (𝒜 : κ → Submodule R A) [GradedAlgebra ℬ] [GradedAlgebra 𝒜]

/-- The product grading on a tensor product of graded algebras respects multiplication. -/
instance tensorProductGradingGradedAlgebra : GradedAlgebra (tensorProductGrading ℬ 𝒜) where
  one_mem := by
    change (1 : B ⊗[R] A) ∈ tensorProductGrading ℬ 𝒜 (0, 0)
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_tensorProductGrading ℬ 𝒜
      (SetLike.one_mem_graded ℬ) (SetLike.one_mem_graded 𝒜)
  mul_mem i j := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    induction x with
    | tmul b a =>
      induction y with
      | tmul b' a' =>
        change ((b : B) ⊗ₜ[R] (a : A)) * ((b' : B) ⊗ₜ[R] (a' : A)) ∈
          tensorProductGrading ℬ 𝒜 (i.1 + j.1, i.2 + j.2)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        exact tmul_mem_tensorProductGrading ℬ 𝒜
          (SetLike.mul_mem_graded b.2 b'.2) (SetLike.mul_mem_graded a.2 a'.2)
      | add y z hy hz => simpa only [map_add, mul_add] using Submodule.add_mem _ hy hz
    | add x z hx hz => simpa only [map_add, add_mul] using Submodule.add_mem _ hx hz

end TensorAlgebras

section CoarsenModules

variable {R M ι κ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (ℳ : ι → Submodule R M) (f : ι → κ)

/-- Coarsen a grading by summing the components whose degrees have the same image under `f`.
This also extends a grading along an embedding, giving zero in degrees outside its image. -/
def coarsenGrading (j : κ) : Submodule R M :=
  ⨆ i, ⨆ (_ : f i = j), ℳ i

/-- A homogeneous element stays homogeneous after applying the degree map. -/
theorem mem_coarsenGrading {i : ι} {m : M} (hm : m ∈ ℳ i) :
    m ∈ coarsenGrading ℳ f (f i) :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem rfl hm)

/-- Reindexing along an injective function leaves each existing component unchanged. -/
@[simp]
theorem coarsenGrading_apply (hf : Function.Injective f) (i : ι) :
    coarsenGrading ℳ f (f i) = ℳ i := by
  apply le_antisymm
  · refine iSup_le fun j ↦ iSup_le fun h ↦ ?_
    exact (hf h) ▸ le_rfl
  · exact le_iSup_of_le i (le_iSup_of_le rfl le_rfl)

/-- Extending a grading gives zero in degrees outside the image of the degree map. -/
theorem coarsenGrading_eq_bot {j : κ} (hj : j ∉ Set.range f) :
    coarsenGrading ℳ f j = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun i ↦ iSup_le fun h ↦ ?_
  exact (hj ⟨i, h⟩).elim

/-- A map preserving the original components also preserves their coarsening. -/
theorem map_mem_coarsenGrading {N : Type*} [AddCommGroup N] [Module R N]
    (𝒩 : ι → Submodule R N) (g : M →ₗ[R] N)
    (hg : ∀ i, ∀ m ∈ ℳ i, g m ∈ 𝒩 i) {j : κ} {m : M}
    (hm : m ∈ coarsenGrading ℳ f j) : g m ∈ coarsenGrading 𝒩 f j := by
  have h : coarsenGrading ℳ f j ≤ (coarsenGrading 𝒩 f j).comap g := by
    refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    intro x hx
    change g x ∈ coarsenGrading 𝒩 f j
    rw [← hi]
    exact mem_coarsenGrading 𝒩 f (hg i x hx)
  exact h hm

variable [DecidableEq ι] [DecidableEq κ] [Decomposition ℳ]

/-- Coarsening preserves the internal direct-sum decomposition. -/
instance coarsenGradingDecomposition : Decomposition (coarsenGrading ℳ f) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro j
    have h := (Decomposition.isInternal ℳ).submodule_iSupIndep.disjoint_biSup_biSup
      (s := {i | f i = j}) (t := {i | f i ≠ j}) (by
        rw [Set.disjoint_left]
        exact fun _ hi hni ↦ hni hi)
    apply h.mono_right
    refine iSup_le fun k ↦ iSup_le fun hk ↦ iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    exact le_iSup_of_le i (le_iSup_of_le (by simpa only [Set.mem_ofPred_eq, hi] using hk) le_rfl)
  · apply le_antisymm le_top
    rw [← (Decomposition.isInternal ℳ).submodule_iSup_eq_top]
    exact iSup_le fun i ↦ le_iSup_of_le (f i)
      (le_iSup_of_le i (le_iSup_of_le rfl le_rfl))

end CoarsenModules

section CoarsenAlgebras

variable {R A ι κ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq ι] [DecidableEq κ] [AddMonoid ι] [AddMonoid κ]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f : ι →+ κ)

/-- An additive map of degrees coarsens an internal algebra grading. -/
instance coarsenGradingGradedAlgebra : GradedAlgebra (coarsenGrading 𝒜 f) where
  one_mem := by
    simpa only [map_zero] using mem_coarsenGrading 𝒜 f (SetLike.one_mem_graded 𝒜)
  mul_mem i j x y hx hy := by
    have h : coarsenGrading 𝒜 f i * coarsenGrading 𝒜 f j ≤
        coarsenGrading 𝒜 f (i + j) := by
      simp only [coarsenGrading, Submodule.mul_eq_map₂, Submodule.map₂_iSup_left,
        Submodule.map₂_iSup_right]
      refine iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun b ↦ iSup_le fun hb ↦ ?_
      apply Submodule.map₂_le.2
      intro x hx y hy
      have hab : f (b + a) = i + j := by rw [map_add, hb, ha]
      exact Submodule.mem_iSup_of_mem (b + a)
        (Submodule.mem_iSup_of_mem hab (SetLike.mul_mem_graded hx hy))
    exact h (Submodule.mul_mem_mul hx hy)

end CoarsenAlgebras

/-- The degree map assigning `(n, w + n)` to coefficient weight `w` and algebra degree `n`. -/
def weightedTensorDegree : ℤ × ℕ →+ ℤ × ℤ where
  toFun i := (i.2, i.1 + i.2)
  map_zero' := by simp
  map_add' i j := by
    ext <;> simp [add_assoc, add_left_comm]

/-- The weighted degree map does not identify distinct homogeneous components. -/
theorem weightedTensorDegree_injective : Function.Injective weightedTensorDegree := by
  rintro ⟨w, n⟩ ⟨v, m⟩ h
  have hn : (n : ℤ) = m := congrArg Prod.fst h
  have hw : w + n = v + m := congrArg Prod.snd h
  have hnm : n = m := Int.ofNat_inj.mp hn
  subst m
  exact Prod.ext (add_right_cancel hw) rfl

section WeightedTensor

variable {R B A : Type*} [CommRing R] [Ring B] [Ring A]
  [Algebra R B] [Algebra R A]
  (ℬ : ℤ → Submodule R B) (𝒜 : ℕ → Submodule R A)

/-- The weighted tensor bigrading places a tensor of weight `w` and degree `n` in bidegree
`(n, w + n)`. Blueprint: `def:grading`, `lem:os-basic`. -/
def weightedTensorGrading : ℤ × ℤ → Submodule R (B ⊗[R] A) :=
  coarsenGrading (tensorProductGrading ℬ 𝒜) weightedTensorDegree

/-- A tensor of homogeneous elements has the weighted sum bidegree. -/
theorem tmul_mem_weightedTensorGrading {w : ℤ} {n : ℕ} {b : B} {a : A}
    (hb : b ∈ ℬ w) (ha : a ∈ 𝒜 n) :
    b ⊗ₜ[R] a ∈ weightedTensorGrading ℬ 𝒜 (n, w + n) :=
  mem_coarsenGrading (tensorProductGrading ℬ 𝒜) weightedTensorDegree
    (i := (w, n)) (tmul_mem_tensorProductGrading ℬ 𝒜 hb ha)

/-- Tensor products of maps preserving coefficient weights and algebra degrees preserve the
weighted bigrading. This applies in particular to algebra maps induced by deletion. -/
theorem map_mem_weightedTensorGrading {B' A' : Type*} [Ring B'] [Ring A']
    [Algebra R B'] [Algebra R A'] (ℬ' : ℤ → Submodule R B') (𝒜' : ℕ → Submodule R A')
    (f : B →ₗ[R] B') (g : A →ₗ[R] A')
    (hf : ∀ w, ∀ b ∈ ℬ w, f b ∈ ℬ' w) (hg : ∀ n, ∀ a ∈ 𝒜 n, g a ∈ 𝒜' n)
    {i : ℤ × ℤ} {x : B ⊗[R] A} (hx : x ∈ weightedTensorGrading ℬ 𝒜 i) :
    TensorProduct.map f g x ∈ weightedTensorGrading ℬ' 𝒜' i :=
  map_mem_coarsenGrading (tensorProductGrading ℬ 𝒜) weightedTensorDegree
    (tensorProductGrading ℬ' 𝒜') (TensorProduct.map f g)
    (fun _ _ hx ↦ map_mem_tensorProductGrading ℬ 𝒜 ℬ' 𝒜' f g hf hg hx) hx

/-- The component of bidegree `(n, w + n)` is the image of `ℬ w ⊗ 𝒜 n`. -/
@[simp]
theorem weightedTensorGrading_apply (w : ℤ) (n : ℕ) :
    weightedTensorGrading ℬ 𝒜 (n, w + n) = tensorProductGrading ℬ 𝒜 (w, n) :=
  coarsenGrading_apply _ _ weightedTensorDegree_injective (w, n)

/-- The component of bidegree `(n, w)` uses coefficient weight `w - n`. -/
theorem weightedTensorGrading_apply' (n : ℕ) (w : ℤ) :
    weightedTensorGrading ℬ 𝒜 (n, w) = tensorProductGrading ℬ 𝒜 (w - n, n) := by
  simpa only [sub_add_cancel] using weightedTensorGrading_apply ℬ 𝒜 (w - n) n

/-- The weighted tensor grading has no components of negative cohomological degree. -/
theorem weightedTensorGrading_eq_bot_of_fst_neg {p w : ℤ} (hp : p < 0) :
    weightedTensorGrading ℬ 𝒜 (p, w) = ⊥ := by
  apply coarsenGrading_eq_bot
  rintro ⟨⟨v, n⟩, h⟩
  have hn : (n : ℤ) = p := congrArg Prod.fst h
  exact (not_lt_of_ge (hn ▸ Int.natCast_nonneg n)) hp

section Components

variable [Decomposition ℬ] [Decomposition 𝒜]

/-- The homogeneous component of weighted bidegree `(n, w + n)` is canonically the tensor
product of coefficient weight `w` and algebra degree `n`. -/
def weightedTensorGradingEquiv (w : ℤ) (n : ℕ) :
    (ℬ w) ⊗[R] (𝒜 n) ≃ₗ[R] weightedTensorGrading ℬ 𝒜 (n, w + n) :=
  tensorProductGradingEquiv ℬ 𝒜 (w, n) ≪≫ₗ
    LinearEquiv.ofEq _ _ (weightedTensorGrading_apply ℬ 𝒜 w n).symm

@[simp]
theorem coe_weightedTensorGradingEquiv (w : ℤ) (n : ℕ) (x : (ℬ w) ⊗[R] (𝒜 n)) :
    (weightedTensorGradingEquiv ℬ 𝒜 w n x : B ⊗[R] A) =
      TensorProduct.map (ℬ w).subtype (𝒜 n).subtype x := rfl

/-- The component of bidegree `(n, w)` is the tensor product of coefficient weight `w - n`
and algebra degree `n`. -/
def weightedTensorComponentEquiv (n : ℕ) (w : ℤ) :
    (ℬ (w - n)) ⊗[R] (𝒜 n) ≃ₗ[R] weightedTensorGrading ℬ 𝒜 (n, w) :=
  tensorProductGradingEquiv ℬ 𝒜 (w - n, n) ≪≫ₗ
    LinearEquiv.ofEq _ _ (weightedTensorGrading_apply' ℬ 𝒜 n w).symm

@[simp]
theorem coe_weightedTensorComponentEquiv (n : ℕ) (w : ℤ)
    (x : (ℬ (w - n)) ⊗[R] (𝒜 n)) :
    (weightedTensorComponentEquiv ℬ 𝒜 n w x : B ⊗[R] A) =
      TensorProduct.map (ℬ (w - n)).subtype (𝒜 n).subtype x := rfl

end Components

variable [GradedAlgebra ℬ] [GradedAlgebra 𝒜]

/-- The weighted tensor bigrading is an internal algebra grading. -/
instance weightedTensorGradingGradedAlgebra : GradedAlgebra (weightedTensorGrading ℬ 𝒜) :=
  inferInstanceAs (GradedAlgebra (coarsenGrading (tensorProductGrading ℬ 𝒜)
    weightedTensorDegree))

omit [GradedAlgebra ℬ] in
/-- A coefficient of weight `w` has bidegree `(0, w)` in the tensor product. -/
theorem tmul_one_mem_weightedTensorGrading {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    b ⊗ₜ[R] (1 : A) ∈ weightedTensorGrading ℬ 𝒜 (0, w) := by
  simpa only [Nat.cast_zero, add_zero] using
    tmul_mem_weightedTensorGrading ℬ 𝒜 hb (SetLike.one_mem_graded 𝒜)

omit [GradedAlgebra 𝒜] in
/-- An element of algebra degree `n` has bidegree `(n, n)` in the tensor product. -/
theorem one_tmul_mem_weightedTensorGrading {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    (1 : B) ⊗ₜ[R] a ∈ weightedTensorGrading ℬ 𝒜 (n, n) := by
  simpa only [zero_add] using
    tmul_mem_weightedTensorGrading ℬ 𝒜 (SetLike.one_mem_graded ℬ) ha

end WeightedTensor

end OrlikSolomon
