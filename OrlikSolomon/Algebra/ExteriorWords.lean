/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.NoncommRing

/-!
# Exterior words, signs and boundaries

This file develops the calculus of words in square-zero, pairwise anticommuting elements of a
ring, and of the standard generators of the exterior algebra `ExteriorAlgebra B (I →₀ B)` of a free
module in particular. Lists are used for words because signs need an ordering of the letters.

Everything holds over an arbitrary commutative ring `B`. Nothing here divides by `2`, so `ℤ/2`
coefficients and rings with `2`-torsion are covered. In characteristic two anticommutativity says
nothing about squares, which is why square-zero is a separate condition on an exterior family.

## Main definitions

* `OrlikSolomon.word x l`: the product `x_{i₁} ⋯ x_{iₛ}` for `l = [i₁, …, iₛ]`.
* `OrlikSolomon.wordBoundary x l`: the signed sum `∑ⱼ (-1)ʲ⁻¹ x_{i₁} ⋯ x̂_{iⱼ} ⋯ x_{iₛ}`.
* `OrlikSolomon.IsExteriorFamily x`: the members of the family square to zero and anticommute.
* `OrlikSolomon.exteriorGen B i`: the standard generator `e_i` of `ExteriorAlgebra B (I →₀ B)`.
* `OrlikSolomon.exteriorLift B`: the universal property, an equivalence between exterior families
  in a `B`-algebra `T` and algebra maps `ExteriorAlgebra B (I →₀ B) →ₐ[B] T`.

## Main results

Blueprint `lem:exterior-words`:

* `OrlikSolomon.span_range_word`, `OrlikSolomon.span_range_word_sort` and
  `OrlikSolomon.span_word_length`: words span, as do increasing words, and words of length `n` span
  the `n`th exterior power.
* `OrlikSolomon.IsExteriorFamily.word_eq_zero_of_not_nodup`: repeated letters give zero.
* `OrlikSolomon.IsExteriorFamily.word_ofFn_comp_perm` and `OrlikSolomon.IsExteriorFamily.word_perm`:
  a permutation of the letters multiplies a word by the sign of the permutation.
* `OrlikSolomon.IsExteriorFamily.word_mul_word_comm`: words supercommute according to their lengths.
* `OrlikSolomon.IsExteriorFamily.linearCombination_mul_self` and `OrlikSolomon.exteriorLift`:
  a linear combination of an exterior family squares to zero, hence the lift exists; it is unique
  by `OrlikSolomon.exteriorAlgHom_ext`.

Blueprint `lem:boundary-expansion`:

* `OrlikSolomon.word_sub_eq_wordBoundary_cons`: the product of the differences `x_j - x_i` is the
  boundary of the word `x_i x_{j₁} ⋯ x_{jₛ}`, in any ring.

Blueprint `lem:projective-algebra`:

* `OrlikSolomon.IsExteriorFamily.exists_mem_decomposition_of_sub_mem`: if differences from one
  generator lie in a subalgebra, every element is the sum of a member of that subalgebra and the
  chosen generator times another member.

The word statements are proved for an arbitrary exterior family. To apply them in the exterior
algebra, use `OrlikSolomon.isExteriorFamily_exteriorGen`.
-/

@[expose] public section

namespace OrlikSolomon

variable {B I J T T' : Type*}

/-! ### Words -/

section Word

variable [Monoid T] [Monoid T']

/-- The *word* `x_{i₁} ⋯ x_{iₛ}` of a family `x : I → T` along a list of letters `[i₁, …, iₛ]`.
The empty word is `1`.

Blueprint: the element `e_I` of `def:os`, with `x` the family of generators. -/
def word (x : I → T) (l : List I) : T :=
  (l.map x).prod

@[simp]
theorem word_nil (x : I → T) : word x [] = 1 :=
  rfl

@[simp]
theorem word_cons (x : I → T) (i : I) (l : List I) : word x (i :: l) = x i * word x l := by
  simp [word]

theorem word_singleton (x : I → T) (i : I) : word x [i] = x i := by
  simp

@[simp]
theorem word_append (x : I → T) (l₁ l₂ : List I) :
    word x (l₁ ++ l₂) = word x l₁ * word x l₂ := by
  simp [word]

/-- Renaming the letters of a word is the same as reindexing the family. -/
theorem word_map (x : I → T) (g : J → I) (l : List J) :
    word x (l.map g) = word (fun j => x (g j)) l := by
  simp [word, Function.comp_def]

/-- Multiplicative maps send words to words. -/
@[simp]
theorem map_word {F : Type*} [FunLike F T T'] [MonoidHomClass F T T'] (f : F) (x : I → T)
    (l : List I) : f (word x l) = word (fun i => f (x i)) l := by
  simp [word, map_list_prod, Function.comp_def]

end Word

/-! ### Square-zero, pairwise anticommuting families -/

/-- A family `x : I → T` is an *exterior family* if its members square to zero and members with
distinct indices anticommute. These are the relations of the standard generators of an exterior
algebra.

Neither condition implies the other: in characteristic two, anticommuting elements need not
square to zero. -/
structure IsExteriorFamily [NonUnitalNonAssocSemiring T] (x : I → T) : Prop where
  /-- Each member of the family squares to zero. -/
  mul_self : ∀ i, x i * x i = 0
  /-- Members of the family with distinct indices anticommute. -/
  mul_add_mul_swap_of_ne : ∀ ⦃i j⦄, i ≠ j → x i * x j + x j * x i = 0

namespace IsExteriorFamily

section Semiring

variable [NonUnitalNonAssocSemiring T] {x : I → T}

/-- Members of an exterior family anticommute, even when their indices agree. -/
theorem mul_add_mul_swap (hx : IsExteriorFamily x) (i j : I) : x i * x j + x j * x i = 0 := by
  by_cases h : i = j
  · subst h
    simp [hx.mul_self]
  · exact hx.mul_add_mul_swap_of_ne h

/-- Reindexing an exterior family gives an exterior family, even along a non-injective map. -/
theorem comp (hx : IsExteriorFamily x) (g : J → I) : IsExteriorFamily fun j => x (g j) :=
  ⟨fun j => hx.mul_self (g j), fun i j _ => hx.mul_add_mul_swap (g i) (g j)⟩

/-- The image of an exterior family under a ring homomorphism is an exterior family. -/
theorem map [NonUnitalNonAssocSemiring T'] {F : Type*} [FunLike F T T']
    [NonUnitalRingHomClass F T T'] (hx : IsExteriorFamily x) (f : F) :
    IsExteriorFamily fun i => f (x i) :=
  ⟨fun i => by rw [← map_mul, hx.mul_self, map_zero], fun i j h => by
    rw [← map_mul, ← map_mul, ← map_add, hx.mul_add_mul_swap_of_ne h, map_zero]⟩

end Semiring

section LinearCombination

variable [CommRing B] [Semiring T] [Algebra B T] {x : I → T}

/-- Any two linear combinations of an exterior family anticommute. -/
theorem linearCombination_mul_add_mul_swap (hx : IsExteriorFamily x) (v w : I →₀ B) :
    Finsupp.linearCombination B x v * Finsupp.linearCombination B x w +
      Finsupp.linearCombination B x w * Finsupp.linearCombination B x v = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ =>
    simp only [map_add, add_mul, mul_add]
    rw [add_add_add_comm, h₁, h₂, add_zero]
  | single i a =>
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add] at h₁ h₂ ⊢
      rw [add_add_add_comm, h₁, h₂, add_zero]
    | single j b =>
      simp only [Finsupp.linearCombination_single, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm b a, ← smul_add, hx.mul_add_mul_swap, smul_zero]

/-- Every linear combination of an exterior family squares to zero: the diagonal terms vanish and
the off-diagonal terms cancel in pairs. This is the full input of `ExteriorAlgebra.lift`, which
asks for more than square-zero on a basis. The proof never divides by `2`, so it works in
characteristic two and with `2`-torsion.

Blueprint: `lem:exterior-words`. -/
theorem linearCombination_mul_self (hx : IsExteriorFamily x) (v : I →₀ B) :
    Finsupp.linearCombination B x v * Finsupp.linearCombination B x v = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    simp only [map_add, add_mul, mul_add]
    rw [hv, hw, zero_add, add_zero, hx.linearCombination_mul_add_mul_swap]
  | single i a =>
    simp only [Finsupp.linearCombination_single, smul_mul_assoc, mul_smul_comm, hx.mul_self,
      smul_zero]

end LinearCombination

section Ring

variable [Ring T] {x : I → T}

/-- Anticommutativity as a rewriting rule. -/
theorem mul_eq_neg_mul_swap (hx : IsExteriorFamily x) (i j : I) : x i * x j = -(x j * x i) :=
  eq_neg_of_add_eq_zero_left (hx.mul_add_mul_swap i j)

/-- The differences of an exterior family with one of its members form an exterior family. -/
theorem sub_const (hx : IsExteriorFamily x) (k : I) : IsExteriorFamily fun i => x i - x k := by
  refine ⟨fun i => ?_, fun i j _ => ?_⟩
  · have h := hx.mul_add_mul_swap i k
    calc (x i - x k) * (x i - x k)
        = x i * x i + x k * x k - (x i * x k + x k * x i) := by noncomm_ring
      _ = 0 := by rw [hx.mul_self, hx.mul_self, h, add_zero, sub_zero]
  · calc (x i - x k) * (x j - x k) + (x j - x k) * (x i - x k)
        = (x i * x j + x j * x i) - (x i * x k + x k * x i) - (x j * x k + x k * x j)
            + (x k * x k + x k * x k) := by noncomm_ring
      _ = 0 := by simp [hx.mul_add_mul_swap, hx.mul_self]

/-- A letter moves past a word with the sign given by the length of the word. -/
theorem mul_word_comm (hx : IsExteriorFamily x) (i : I) (l : List I) :
    x i * word x l = (l.length : ℤ).negOnePow • (word x l * x i) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [word_cons, ← mul_assoc, hx.mul_eq_neg_mul_swap i j, neg_mul, mul_assoc, ih]
    simp [Int.negOnePow_succ, mul_assoc, mul_smul_comm]

/-- Two words supercommute according to their lengths.

Blueprint: `lem:exterior-words`. -/
theorem word_mul_word_comm (hx : IsExteriorFamily x) (l₁ l₂ : List I) :
    word x l₁ * word x l₂ =
      ((l₁.length : ℤ) * l₂.length).negOnePow • (word x l₂ * word x l₁) := by
  induction l₁ with
  | nil => simp
  | cons i l₁ ih =>
    rw [word_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc, hx.mul_word_comm, smul_mul_assoc,
      smul_smul, mul_assoc, ← Int.negOnePow_add]
    congr 2
    push_cast [List.length_cons]
    ring

/-- A letter moves to the front of a word with the sign given by the number of letters it passes.

Blueprint: used in `lem:lift-surj`. -/
theorem word_append_cons (hx : IsExteriorFamily x) (l₁ : List I) (i : I) (l₂ : List I) :
    word x (l₁ ++ i :: l₂) = (l₁.length : ℤ).negOnePow • (x i * word x (l₁ ++ l₂)) := by
  induction l₁ with
  | nil => simp
  | cons j l₁ ih =>
    simp only [List.cons_append, word_cons]
    rw [ih, mul_smul_comm, ← mul_assoc (x j), hx.mul_eq_neg_mul_swap j i, neg_mul, mul_assoc]
    simp [Int.negOnePow_succ]

/-- The first occurrence of a letter moves to the front of a word with the sign given by its
position. -/
theorem word_eq_smul_mul_word_erase [DecidableEq I] (hx : IsExteriorFamily x) {i : I} {l : List I}
    (h : i ∈ l) : word x l = (l.idxOf i : ℤ).negOnePow • (x i * word x (l.erase i)) := by
  induction l with
  | nil => simp at h
  | cons j l ih =>
    by_cases hij : j = i
    · subst hij
      simp
    · have hi : i ∈ l := (List.mem_cons.1 h).resolve_left (Ne.symm hij)
      rw [List.idxOf_cons_ne _ hij, List.erase_cons_tail (by simpa using hij), word_cons, word_cons,
        ih hi, mul_smul_comm, ← mul_assoc (x j), hx.mul_eq_neg_mul_swap j i, neg_mul, mul_assoc]
      simp [Int.negOnePow_succ]

/-- Swapping two adjacent letters changes the sign of a word. -/
theorem word_swap (hx : IsExteriorFamily x) (l₁ : List I) (i j : I) (l₂ : List I) :
    word x (l₁ ++ i :: j :: l₂) = -word x (l₁ ++ j :: i :: l₂) := by
  simp only [word_append, word_cons]
  rw [← mul_assoc (x i), hx.mul_eq_neg_mul_swap i j, neg_mul, mul_neg, mul_assoc]

/-- A word containing `i` is killed by `x i` on the left. -/
theorem mul_word_eq_zero_of_mem (hx : IsExteriorFamily x) {i : I} {l : List I} (h : i ∈ l) :
    x i * word x l = 0 := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h
  rw [hx.word_append_cons, mul_smul_comm, ← mul_assoc, hx.mul_self, zero_mul, smul_zero]

/-- A word containing `i` is killed by `x i` on the right. -/
theorem word_mul_eq_zero_of_mem (hx : IsExteriorFamily x) {i : I} {l : List I} (h : i ∈ l) :
    word x l * x i = 0 := by
  have key := hx.mul_word_comm i l
  rw [hx.mul_word_eq_zero_of_mem h] at key
  exact (smul_eq_zero_iff_eq _).1 key.symm

/-- A word with a repeated letter is zero.

Blueprint: `lem:exterior-words`. -/
theorem word_eq_zero_of_not_nodup (hx : IsExteriorFamily x) {l : List I} (h : ¬l.Nodup) :
    word x l = 0 := by
  induction l with
  | nil => simp at h
  | cons i l ih =>
    rw [word_cons]
    by_cases hi : i ∈ l
    · exact hx.mul_word_eq_zero_of_mem hi
    · rw [ih fun hl => h (List.nodup_cons.2 ⟨hi, hl⟩), mul_zero]

/-- Words with the same letters agree up to sign. `IsExteriorFamily.word_perm` identifies the sign
as that of a permutation. -/
theorem exists_word_eq_smul_of_perm (hx : IsExteriorFamily x) {l l' : List I} (h : l.Perm l') :
    ∃ u : ℤˣ, word x l = u • word x l' := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons i _ ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by simp [hu, mul_smul_comm]⟩
  | swap i j l => exact ⟨-1, by simpa using hx.word_swap [] j i l⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨u, hu⟩ := ih₁
    obtain ⟨v, hv⟩ := ih₂
    exact ⟨u * v, by rw [hu, hv, mul_smul]⟩

end Ring

end IsExteriorFamily

/-! ### The signed boundary of a word -/

section Boundary

variable [Ring T] [Ring T']

/-- The *signed boundary* of a word: for `l = [i₁, …, iₛ]` it is
`∑ⱼ (-1)ʲ⁻¹ x_{i₁} ⋯ x̂_{iⱼ} ⋯ x_{iₛ}`, as stated in `wordBoundary_eq_sum`. It is defined for any
family in any ring, and the boundary of the empty word is zero.

Blueprint: the element `∂e_I` of `def:os`, with `x` the family of generators. -/
def wordBoundary (x : I → T) : List I → T
  | [] => 0
  | i :: l => word x l - x i * wordBoundary x l

@[simp]
theorem wordBoundary_nil (x : I → T) : wordBoundary x [] = 0 :=
  rfl

/-- The recursion for the boundary. For `l` a list of representatives, this is the identity
`∂e_{(H, I)} = e_I - e_H ∂e_I` of `lem:representatives`. -/
@[simp]
theorem wordBoundary_cons (x : I → T) (i : I) (l : List I) :
    wordBoundary x (i :: l) = word x l - x i * wordBoundary x l :=
  rfl

theorem wordBoundary_singleton (x : I → T) (i : I) : wordBoundary x [i] = 1 := by
  simp

theorem wordBoundary_pair (x : I → T) (i j : I) : wordBoundary x [i, j] = x j - x i := by
  simp

/-- The boundary of a word of length three, as in the triple relation of `lem:representatives`. -/
theorem wordBoundary_triple (x : I → T) (i j k : I) :
    wordBoundary x [i, j, k] = x j * x k - x i * x k + x i * x j := by
  simp only [wordBoundary_cons, wordBoundary_nil, word_cons, word_nil]
  noncomm_ring

/-- The closed form of the boundary, with positions numbered from zero: the term omitting the
letter in position `j` has sign `(-1)ʲ`.

Blueprint: `def:os`. -/
theorem wordBoundary_eq_sum (x : I → T) (l : List I) :
    wordBoundary x l = ∑ j : Fin l.length, (j.val : ℤ).negOnePow • word x (l.eraseIdx j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wordBoundary_cons, ih]
    change _ = ∑ j : Fin (l.length + 1), _
    rw [Fin.sum_univ_succ]
    simp [Int.negOnePow_succ, Finset.mul_sum, sub_eq_add_neg, mul_smul_comm]

/-- Ring homomorphisms send boundaries of words to boundaries of words. -/
@[simp]
theorem map_wordBoundary {F : Type*} [FunLike F T T'] [RingHomClass F T T'] (f : F) (x : I → T)
    (l : List I) : f (wordBoundary x l) = wordBoundary (fun i => f (x i)) l := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- Renaming the letters of a word is the same as reindexing the family. -/
theorem wordBoundary_map (x : I → T) (g : J → I) (l : List J) :
    wordBoundary x (l.map g) = wordBoundary (fun j => x (g j)) l := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, word_map]

/-- The signed Leibniz rule for the boundary of a concatenation, which holds for any family in any
ring.

Blueprint: `lem:central-boundary`, on words. -/
theorem wordBoundary_append (x : I → T) (l₁ l₂ : List I) :
    wordBoundary x (l₁ ++ l₂) =
      wordBoundary x l₁ * word x l₂ +
        (l₁.length : ℤ).negOnePow • (word x l₁ * wordBoundary x l₂) := by
  induction l₁ with
  | nil => simp
  | cons i l₁ ih =>
    simp only [List.cons_append, wordBoundary_cons, word_append, ih, word_cons, mul_add, sub_mul,
      mul_assoc, List.length_cons, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul,
      mul_smul_comm]
    abel

/-- **Boundary expansion**: `(x_{j₁} - x_i) ⋯ (x_{jₛ} - x_i)` is the boundary of the word
`x_i x_{j₁} ⋯ x_{jₛ}`.

This holds in any ring, and needs only that `x_i` squares to zero and anticommutes with the other
letters. `IsExteriorFamily.word_sub_eq_wordBoundary_cons` is the form stated in the blueprint.

Blueprint: `lem:boundary-expansion`. -/
theorem word_sub_eq_wordBoundary_cons (x : I → T) (i : I) (l : List I) (hi : x i * x i = 0)
    (hl : ∀ j ∈ l, x i * x j + x j * x i = 0) :
    word (fun j => x j - x i) l = wordBoundary x (i :: l) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hij : x j * x i = -(x i * x j) := eq_neg_of_add_eq_zero_right (hl j (by simp))
    rw [word_cons, ih fun k hk => hl k (List.mem_cons_of_mem j hk)]
    simp only [wordBoundary_cons, word_cons]
    calc (x j - x i) * (word x l - x i * wordBoundary x l)
        = x j * word x l - x i * word x l - (x j * x i) * wordBoundary x l
            + (x i * x i) * wordBoundary x l := by noncomm_ring
      _ = x j * word x l - x i * (word x l - x j * wordBoundary x l) := by
        rw [hij, hi]
        noncomm_ring

/-- **Boundary expansion** for an exterior family.

Blueprint: `lem:boundary-expansion`. -/
theorem IsExteriorFamily.word_sub_eq_wordBoundary_cons {x : I → T} (hx : IsExteriorFamily x)
    (i : I) (l : List I) : word (fun j => x j - x i) l = wordBoundary x (i :: l) :=
  OrlikSolomon.word_sub_eq_wordBoundary_cons x i l (hx.mul_self i) fun j _ =>
    hx.mul_add_mul_swap i j

/-- Multiplying the boundary of a word by its first letter gives the rest of the word multiplied by
that letter. So the relation `∂e_{(H, I)} = 0` implies `e_H e_I = 0`.

Blueprint: used in `lem:representatives`. -/
theorem IsExteriorFamily.mul_wordBoundary_cons {x : I → T} (hx : IsExteriorFamily x) (i : I)
    (l : List I) : x i * wordBoundary x (i :: l) = x i * word x l := by
  rw [wordBoundary_cons, mul_sub, ← mul_assoc, hx.mul_self, zero_mul, sub_zero]

end Boundary

/-! ### The standard generators of an exterior algebra and the lift -/

section Generators

variable (B) [CommRing B]

/-- The standard generator `e_i` of the exterior algebra of the free module on `I`. -/
noncomputable def exteriorGen (i : I) : ExteriorAlgebra B (I →₀ B) :=
  ExteriorAlgebra.ι B (Finsupp.single i 1)

/-- The standard generators of the exterior algebra form an exterior family. -/
theorem isExteriorFamily_exteriorGen : IsExteriorFamily (exteriorGen B : I → _) :=
  ⟨fun _ => ExteriorAlgebra.ι_sq_zero _, fun _ _ _ => ExteriorAlgebra.ι_add_mul_swap _ _⟩

/-- The canonical map `ι` is the linear combination of the standard generators. -/
@[simp]
theorem linearCombination_exteriorGen (v : I →₀ B) :
    Finsupp.linearCombination B (exteriorGen B) v = ExteriorAlgebra.ι B v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single i a => simp [exteriorGen, ← map_smul]

variable {B} in
/-- Algebra maps out of the exterior algebra of a free module agree if they agree on the standard
generators. This is the uniqueness part of the lift.

Blueprint: `lem:exterior-words`. -/
@[ext]
theorem exteriorAlgHom_ext [Semiring T] [Algebra B T] {f g : ExteriorAlgebra B (I →₀ B) →ₐ[B] T}
    (h : ∀ i, f (exteriorGen B i) = g (exteriorGen B i)) : f = g := by
  apply ExteriorAlgebra.hom_ext
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  exact h i

/-- The universal property of the exterior algebra of a free module: exterior families in a
`B`-algebra `T` correspond to algebra maps to `T`, with the map sending each `e_i` to `x i`.

There is no assumption on `2`. Mathlib's `ExteriorAlgebra.lift` needs every vector to square to
zero, which `IsExteriorFamily.linearCombination_mul_self` deduces from the family.

Blueprint: `lem:exterior-words`. -/
noncomputable def exteriorLift [Semiring T] [Algebra B T] :
    {x : I → T // IsExteriorFamily x} ≃ (ExteriorAlgebra B (I →₀ B) →ₐ[B] T) where
  toFun x := ExteriorAlgebra.lift B
    ⟨Finsupp.linearCombination B x.1, x.2.linearCombination_mul_self⟩
  invFun f := ⟨fun i => f (exteriorGen B i), (isExteriorFamily_exteriorGen B).map f⟩
  left_inv x := by
    ext i
    simp [exteriorGen]
  right_inv f := by
    ext i
    simp [exteriorGen]

section Lift

variable [Semiring T] [Algebra B T]

@[simp]
theorem exteriorLift_ι (x : {x : I → T // IsExteriorFamily x}) (v : I →₀ B) :
    exteriorLift B x (ExteriorAlgebra.ι B v) = Finsupp.linearCombination B x.1 v := by
  simp [exteriorLift]

@[simp]
theorem exteriorLift_exteriorGen (x : {x : I → T // IsExteriorFamily x}) (i : I) :
    exteriorLift B x (exteriorGen B i) = x.1 i := by
  simp [exteriorGen]

@[simp]
theorem exteriorLift_symm_apply_coe (f : ExteriorAlgebra B (I →₀ B) →ₐ[B] T) (i : I) :
    ((exteriorLift B).symm f).1 i = f (exteriorGen B i) :=
  rfl

/-- An algebra map out of the exterior algebra of a free module is the lift of a family if and only
if it sends each standard generator to the corresponding member of the family.

Blueprint: `lem:exterior-words`. -/
theorem exteriorLift_unique (x : {x : I → T // IsExteriorFamily x})
    (f : ExteriorAlgebra B (I →₀ B) →ₐ[B] T) :
    (∀ i, f (exteriorGen B i) = x.1 i) ↔ f = exteriorLift B x :=
  ⟨fun h => exteriorAlgHom_ext fun i => by simp [h], by
    rintro rfl i
    simp⟩

/-- The lift sends the word in the standard generators to the word in the family. -/
theorem exteriorLift_word (x : {x : I → T // IsExteriorFamily x}) (l : List I) :
    exteriorLift B x (word (exteriorGen B) l) = word x.1 l := by
  simp

end Lift

/-! ### Spanning -/

/-- Words in the standard generators span the exterior algebra.

Blueprint: `lem:exterior-words`. -/
theorem span_range_word :
    Submodule.span B (Set.range (word (exteriorGen B) : List I → _)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro a
  induction a using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
  | ι v =>
    rw [← linearCombination_exteriorGen, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨[i], word_singleton _ _⟩)
  | mul a b ha hb =>
    have hab := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at hab
    refine Submodule.span_mono ?_ hab
    rintro _ ⟨_, ⟨l₁, rfl⟩, _, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨l₁ ++ l₂, word_append _ _ _⟩
  | add a b ha hb => exact add_mem ha hb

/-- Words in strictly increasing letters span the exterior algebra.

Blueprint: `lem:exterior-words`. -/
theorem span_range_word_sort [LinearOrder I] :
    Submodule.span B (Set.range fun s : Finset I => word (exteriorGen B) s.sort) = ⊤ := by
  rw [eq_top_iff, ← span_range_word B, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  by_cases hl : l.Nodup
  · have hp : l.Perm l.toFinset.sort :=
      ((Finset.sort_perm_toList _ _).trans (List.toFinset_toList hl)).symm
    obtain ⟨u, hu⟩ := (isExteriorFamily_exteriorGen B).exists_word_eq_smul_of_perm hp
    have hmem : word (exteriorGen B) l.toFinset.sort ∈
        Submodule.span B (Set.range fun s : Finset I => word (exteriorGen B) s.sort) :=
      Submodule.subset_span ⟨_, rfl⟩
    rw [hu, Units.smul_def]
    exact zsmul_mem hmem _
  · simp [(isExteriorFamily_exteriorGen B).word_eq_zero_of_not_nodup hl]

/-- Words in the standard generators are values of `ExteriorAlgebra.ιMulti`. -/
theorem word_exteriorGen_ofFn {n : ℕ} (v : Fin n → I) :
    word (exteriorGen B) (List.ofFn v) =
      ExteriorAlgebra.ιMulti B n fun k => Finsupp.single (v k) 1 := by
  simp [word, ExteriorAlgebra.ιMulti_apply, List.map_ofFn, Function.comp_def, exteriorGen]

/-- A word of length `n` lies in the `n`th exterior power. -/
theorem word_mem_exteriorPower (l : List I) :
    word (exteriorGen B) l ∈ ⋀[B]^l.length (I →₀ B) := by
  induction l with
  | nil => exact Submodule.one_le.1 (pow_zero _).ge
  | cons i l ih =>
    rw [word_cons, List.length_cons, ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

/-- The signed boundary of a word of length `n` lies in exterior degree `n - 1`.
The boundary of the empty word is zero, so no nonemptiness hypothesis is needed.

Blueprint: the homogeneity of the boundary relators in `lem:os-basic`. -/
theorem wordBoundary_mem_exteriorPower (l : List I) :
    wordBoundary (exteriorGen B) l ∈ ⋀[B]^(l.length - 1) (I →₀ B) := by
  rw [wordBoundary_eq_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h := word_mem_exteriorPower B (l.eraseIdx i)
  simp only [List.length_eraseIdx, ite_eq_left i.isLt] at h
  simpa only [Units.smul_def] using zsmul_mem h (((i.val : ℤ).negOnePow : ℤˣ) : ℤ)

/-- Words of length `n` in the standard generators span the `n`th exterior power.

Blueprint: `lem:exterior-words`. -/
theorem span_word_length (n : ℕ) :
    Submodule.span B {y | ∃ l : List I, l.length = n ∧ word (exteriorGen B) l = y} =
      ⋀[B]^n (I →₀ B) := by
  have hs : Submodule.span B (Set.range fun i : I => Finsupp.single i (1 : B)) = ⊤ := by
    simpa only [Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne (R := B) (ι := I)).span_eq
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl, rfl⟩
    exact word_mem_exteriorPower B l
  · rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top B n (I →₀ B) hs, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    choose v hv using fun k => ha (Set.mem_range_self k)
    refine Submodule.subset_span ⟨List.ofFn v, by simp, ?_⟩
    rw [word_exteriorGen_ofFn]
    exact congrArg _ (funext hv)

/-- Linear maps out of the exterior algebra of a free module agree if they agree on words in the
standard generators. -/
theorem exteriorLinearMap_ext {N : Type*} [AddCommMonoid N] [Module B N]
    {f g : ExteriorAlgebra B (I →₀ B) →ₗ[B] N}
    (h : ∀ l : List I, f (word (exteriorGen B) l) = g (word (exteriorGen B) l)) : f = g :=
  LinearMap.ext_on_range (span_range_word B) h

/-! ### Permutations -/

/-- A permutation of the letters multiplies a word in the standard generators by its sign. -/
theorem word_exteriorGen_ofFn_comp_perm {n : ℕ} (v : Fin n → I) (σ : Equiv.Perm (Fin n)) :
    word (exteriorGen B) (List.ofFn (v ∘ σ)) =
      Equiv.Perm.sign σ • word (exteriorGen B) (List.ofFn v) := by
  rw [word_exteriorGen_ofFn, word_exteriorGen_ofFn]
  exact (ExteriorAlgebra.ιMulti B n).map_perm (fun k => Finsupp.single (v k) 1) σ

end Generators

/-! ### Decomposition by differences -/

namespace IsExteriorFamily

/-- If words in a square-zero anticommuting family span an algebra, any coefficient subalgebra
containing its differences from one generator spans the algebra together with its left multiple
by that generator. Blueprint: the generation step of `lem:projective-algebra`. -/
theorem exists_mem_decomposition_of_sub_mem {I A B : Type*} [CommRing B] [Ring A]
    [Algebra B A] {f : I → A} (hf : IsExteriorFamily f)
    (hspan : Submodule.span B (Set.range (word f : List I → A)) = ⊤)
    (S : Subalgebra B A) (H₀ : I) (hS : ∀ H, f H - f H₀ ∈ S) (x : A) :
    ∃ b ∈ S, ∃ c ∈ S, x = b + f H₀ * c := by
  have hword (l : List I) :
      ∃ b ∈ S, ∃ c ∈ S, word f l = b + f H₀ * c := by
    induction l with
    | nil => exact ⟨1, S.one_mem, 0, S.zero_mem, by simp⟩
    | cons H l ih =>
      obtain ⟨b, hb, c, hc, hl⟩ := ih
      let d := f H - f H₀
      refine ⟨d * b, S.mul_mem (hS H) hb, b - d * c,
        S.sub_mem hb (S.mul_mem (hS H) hc), ?_⟩
      rw [word_cons, hl, mul_add, ← mul_assoc (f H),
        hf.mul_eq_neg_mul_swap H H₀]
      dsimp [d]
      noncomm_ring [← mul_assoc, hf.mul_self]
  have hx : x ∈ Submodule.span B (Set.range (word f : List I → _)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨I, rfl⟩ := hx; exact hword I
  | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b + b', S.add_mem hb hb', c + c', S.add_mem hc hc', ?_⟩
    noncomm_ring
  | smul a x _ hx =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    exact ⟨a • b, S.smul_mem hb a, a • c, S.smul_mem hc a, by
      rw [smul_add, mul_smul_comm]⟩

end IsExteriorFamily

/-! ### Signs for arbitrary exterior families -/

namespace IsExteriorFamily

variable [Ring T] {x : I → T}

/-- A permutation of the letters multiplies a word by the sign of the permutation, with the word
given as a function on `Fin n`.

Blueprint: `lem:exterior-words`. -/
theorem word_ofFn_comp_perm (hx : IsExteriorFamily x) {n : ℕ} (v : Fin n → I)
    (σ : Equiv.Perm (Fin n)) :
    word x (List.ofFn (v ∘ σ)) = Equiv.Perm.sign σ • word x (List.ofFn v) := by
  have h := congrArg (exteriorLift ℤ ⟨x, hx⟩) (word_exteriorGen_ofFn_comp_perm ℤ v σ)
  simpa [Units.smul_def] using h

/-- A permutation of the letters multiplies a word by the sign of the permutation.

Blueprint: `lem:exterior-words`. -/
theorem word_perm (hx : IsExteriorFamily x) (l : List I) (σ : Equiv.Perm (Fin l.length)) :
    word x (List.ofFn fun k => l.get (σ k)) = Equiv.Perm.sign σ • word x l := by
  simpa [Function.comp_def, List.ofFn_get] using hx.word_ofFn_comp_perm l.get σ

end IsExteriorFamily

end OrlikSolomon
