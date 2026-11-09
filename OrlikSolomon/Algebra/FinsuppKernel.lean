/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Free-module maps that discard or merge labels

An optional label map `f : ι → Option κ` induces `finsuppOptionMap f`, sending the basis vector
at `i` to zero when `f i = none`, and to the basis vector at `j` when `f i = some j`.
This is Mathlib's `Finsupp.lmapDomain` followed by restriction to the `some` labels.

Its kernel over any ring is `finsuppOptionRelationSpan f`: the span of discarded basis vectors
and differences of two basis vectors with the same retained label. No surjectivity, nonzero,
commutativity or finiteness assumption is needed. The maps and their surjectivity API already
work over semirings.

## Main results

* `ker_finsuppOptionMap` identifies the kernel with the explicit relation span.
* `ker_finsuppOptionMap_le_iff` tests containment of the kernel using its two kinds of generators.
* `ker_finsuppOptionMap_le_ker_iff` is the corresponding criterion for another linear map to
  annihilate the kernel.
* `finsuppOptionMap_surjective` proves surjectivity when every retained label occurs.

Blueprint: the generic free-module calculation used in `lem:l01`. The affine trace geometry and
surjectivity on geometric trace labels are separate; this module does not complete that node.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon

variable {ι κ R : Type*}

/-- The linear map induced by an optional label map: `none` discards a basis vector and
`some j` sends it to the basis vector at `j`. -/
def finsuppOptionMap [Semiring R] (f : ι → Option κ) :
    (ι →₀ R) →ₗ[R] κ →₀ R :=
  (Finsupp.lcomapDomain (R := R) (M := R) Option.some (Option.some_injective κ)).comp
    (Finsupp.lmapDomain R R f)

/-- Optional relabeling is domain pushforward followed by restriction to retained labels. -/
theorem finsuppOptionMap_apply [Semiring R] (f : ι → Option κ) (x : ι →₀ R) :
    finsuppOptionMap f x = (Finsupp.mapDomain f x).some := rfl

/-- Optional relabeling on an arbitrary scalar multiple of a basis vector. -/
@[simp]
theorem finsuppOptionMap_single [Semiring R] (f : ι → Option κ) (i : ι) (r : R) :
    finsuppOptionMap (R := R) f (Finsupp.single i r) =
      (f i).elim 0 (fun j => Finsupp.single j r) := by
  cases h : f i <;> simp [finsuppOptionMap_apply, h]

/-- Covering every retained label makes the induced free-module map surjective, including
when the retained label type is empty or the coefficient semiring is the zero semiring. -/
theorem finsuppOptionMap_surjective [Semiring R] (f : ι → Option κ)
    (hf : ∀ j, ∃ i, f i = some j) : Function.Surjective (finsuppOptionMap (R := R) f) := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
  | single j r =>
    obtain ⟨i, hi⟩ := hf j
    exact ⟨Finsupp.single i r, by simp [hi]⟩

/-- Discarding every label gives the zero linear map. -/
@[simp]
theorem finsuppOptionMap_none [Semiring R] :
    finsuppOptionMap (R := R) (fun _ : ι => (none : Option κ)) = 0 := by
  apply Finsupp.lhom_ext
  intro i r
  simp

/-- With no discarded labels, optional relabeling is Mathlib's domain pushforward. -/
@[simp]
theorem finsuppOptionMap_some [Semiring R] (f : ι → κ) :
    finsuppOptionMap (R := R) (fun i => some (f i)) = Finsupp.lmapDomain R R f := by
  apply Finsupp.lhom_ext
  intro i r
  simp

/-- The span of discarded basis vectors and differences in a common retained fiber.
Blueprint: the generic relation span in `lem:l01`. -/
def finsuppOptionRelationSpan [Ring R] (f : ι → Option κ) : Submodule R (ι →₀ R) :=
  Submodule.span R
    ({x | ∃ i, f i = none ∧ x = Finsupp.single i 1} ∪
      {x | ∃ i i' j, f i = some j ∧ f i' = some j ∧
        x = Finsupp.single i 1 - Finsupp.single i' 1})

/-- A discarded basis vector belongs to the relation span. -/
theorem single_mem_finsuppOptionRelationSpan [Ring R] (f : ι → Option κ) {i : ι}
    (hi : f i = none) : Finsupp.single i 1 ∈ finsuppOptionRelationSpan (R := R) f :=
  Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)

/-- The difference of two basis vectors with the same retained label belongs to the relation
span. The labels need not be distinct. -/
theorem sub_mem_finsuppOptionRelationSpan [Ring R] (f : ι → Option κ) {i i' : ι} {j : κ}
    (hi : f i = some j) (hi' : f i' = some j) :
    Finsupp.single i 1 - Finsupp.single i' 1 ∈ finsuppOptionRelationSpan (R := R) f :=
  Submodule.subset_span (Or.inr ⟨i, i', j, hi, hi', rfl⟩)

private theorem finsuppOptionRelationSpan_le_ker [Ring R] (f : ι → Option κ) :
    finsuppOptionRelationSpan (R := R) f ≤ LinearMap.ker (finsuppOptionMap f) := by
  refine Submodule.span_le.mpr ?_
  rintro x (hx | hx)
  · obtain ⟨i, hi, rfl⟩ := hx
    simp [hi]
  · obtain ⟨i, i', j, hi, hi', rfl⟩ := hx
    simp [hi, hi']

private theorem finsuppOptionRelationSpan_mkQ_factor [Ring R] (f : ι → Option κ) :
    ∃ l : (κ →₀ R) →ₗ[R] ((ι →₀ R) ⧸ finsuppOptionRelationSpan (R := R) f),
      l.comp (finsuppOptionMap (R := R) f) = (finsuppOptionRelationSpan (R := R) f).mkQ := by
  classical
  let S := finsuppOptionRelationSpan (R := R) f
  -- Representatives are used only inside this proof; none is part of the public kernel API.
  let b : κ → ((ι →₀ R) ⧸ S) := fun j =>
    if h : ∃ i, f i = some j then S.mkQ (Finsupp.single (Classical.choose h) 1) else 0
  let l := Finsupp.linearCombination R b
  refine ⟨l, Finsupp.lhom_ext fun i r => ?_⟩
  have hsingle : l (finsuppOptionMap f (Finsupp.single i 1)) = S.mkQ (Finsupp.single i 1) := by
    cases hi : f i with
    | none =>
      rw [finsuppOptionMap_single, hi]
      simp only [Option.elim_none, map_zero]
      exact ((Submodule.Quotient.mk_eq_zero S).mpr (single_mem_finsuppOptionRelationSpan f hi)).symm
    | some j =>
      have hj : ∃ i, f i = some j := ⟨i, hi⟩
      have hc : f (Classical.choose hj) = some j := Classical.choose_spec hj
      rw [finsuppOptionMap_single, hi]
      simp only [Option.elim_some, l, Finsupp.linearCombination_single, one_smul, b,
        dite_eq_left hj]
      exact (Submodule.Quotient.eq S).mpr (sub_mem_finsuppOptionRelationSpan f hc hi)
  rw [← Finsupp.smul_single_one i r]
  simpa only [LinearMap.comp_apply, map_smul] using congrArg (r • ·) hsingle

/-- The kernel of an optional relabeling is spanned by discarded basis vectors and differences
of basis vectors with equal retained labels. Blueprint: the generic calculation in `lem:l01`. -/
theorem ker_finsuppOptionMap [Ring R] (f : ι → Option κ) :
    LinearMap.ker (finsuppOptionMap (R := R) f) = finsuppOptionRelationSpan f := by
  apply le_antisymm
  · obtain ⟨l, hl⟩ := finsuppOptionRelationSpan_mkQ_factor (R := R) f
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero (finsuppOptionRelationSpan (R := R) f)).mp
    change (finsuppOptionRelationSpan (R := R) f).mkQ x = 0
    rw [← hl, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  · exact finsuppOptionRelationSpan_le_ker f

/-- A submodule contains the optional relabeling kernel exactly when it contains the discarded
basis vectors and the differences in each retained fiber. -/
theorem ker_finsuppOptionMap_le_iff [Ring R] (f : ι → Option κ)
    (p : Submodule R (ι →₀ R)) :
    LinearMap.ker (finsuppOptionMap f) ≤ p ↔
      (∀ i, f i = none → Finsupp.single i 1 ∈ p) ∧
      ∀ i i' j, f i = some j → f i' = some j →
        Finsupp.single i 1 - Finsupp.single i' 1 ∈ p := by
  rw [ker_finsuppOptionMap]
  constructor
  · intro h
    exact ⟨fun i hi => h (single_mem_finsuppOptionRelationSpan f hi),
      fun i i' j hi hi' => h (sub_mem_finsuppOptionRelationSpan f hi hi')⟩
  · rintro ⟨hnone, hsome⟩
    refine Submodule.span_le.mpr ?_
    rintro x (⟨i, hi, rfl⟩ | ⟨i, i', j, hi, hi', rfl⟩)
    · exact hnone i hi
    · exact hsome i i' j hi hi'

/-- A linear map annihilates the optional relabeling kernel exactly when it vanishes on discarded
basis vectors and is constant on each retained basis fiber. -/
theorem ker_finsuppOptionMap_le_ker_iff [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (f : ι → Option κ) (g : (ι →₀ R) →ₗ[R] M) :
    LinearMap.ker (finsuppOptionMap f) ≤ LinearMap.ker g ↔
      (∀ i, f i = none → g (Finsupp.single i 1) = 0) ∧
      ∀ i i' j, f i = some j → f i' = some j →
        g (Finsupp.single i 1) = g (Finsupp.single i' 1) := by
  rw [ker_finsuppOptionMap_le_iff]
  simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]

end OrlikSolomon
