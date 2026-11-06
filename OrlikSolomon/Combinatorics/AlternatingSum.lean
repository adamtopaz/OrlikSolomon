/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Module.NatInt

/-!
# Alternating sums over images of finite sets

An alternating sum over subsets depends only on the distinct images of their elements. This
accounts for duplicate hyperplane traces in deletion--restriction: each nonempty fiber has total
alternating weight `-1`, regardless of its cardinality.

The main result `sum_powerset_image` holds for any function between types and weights in any
additive commutative group. It uses no arrangement or cohomology hypotheses.

Blueprint: the combinatorial cancellation in `lem:polynomial-recursion`.
-/

@[expose] public section

open scoped BigOperators

namespace OrlikSolomon

variable {α β M : Type*} [AddCommGroup M]

private def alternatingSum (s : Finset α) (F : Finset α → M) : M :=
  ∑ t ∈ s.powerset, ((-1 : ℤ) ^ t.card) • F t

private theorem alternatingSum_insert [DecidableEq α] {a : α} {s : Finset α} (ha : a ∉ s)
    (F : Finset α → M) :
    alternatingSum (insert a s) F =
      alternatingSum s F - alternatingSum s (fun t ↦ F (insert a t)) := by
  unfold alternatingSum
  rw [Finset.sum_powerset_insert ha, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := fun h ↦ ha (Finset.mem_powerset.mp ht h)
  simp [Finset.card_insert_of_notMem hat, pow_succ]

private theorem alternatingSum_insert_of_mem [DecidableEq α] {a : α} {s : Finset α}
    (ha : a ∈ s) (F : Finset α → M) :
    alternatingSum s (fun t ↦ F (insert a t)) = 0 := by
  rw [← Finset.insert_erase ha, alternatingSum_insert (Finset.notMem_erase a s)]
  simp only [Finset.insert_idem, sub_self]

/-- Alternating sums over subsets are unchanged by identifying elements with the same image.
Equivalently, summing over all nonempty choices in a fiber gives the same weight as selecting
its image once. This is the duplicate-trace cancellation of deletion--restriction.

Blueprint: `lem:polynomial-recursion`. -/
theorem sum_powerset_image [DecidableEq β] (s : Finset α) (f : α → β) (F : Finset β → M) :
    (∑ t ∈ s.powerset, ((-1 : ℤ) ^ t.card) • F (t.image f)) =
      ∑ u ∈ (s.image f).powerset, ((-1 : ℤ) ^ u.card) • F u := by
  classical
  change alternatingSum s (fun t ↦ F (t.image f)) = alternatingSum (s.image f) F
  induction s using Finset.induction_on generalizing F with
  | empty => simp [alternatingSum]
  | @insert a s ha ih =>
    calc
      alternatingSum (insert a s) (fun t ↦ F (t.image f)) =
          alternatingSum s (fun t ↦ F (t.image f)) -
            alternatingSum s (fun t ↦ F (insert (f a) (t.image f))) := by
        rw [alternatingSum_insert ha]
        simp only [Finset.image_insert]
      _ = alternatingSum (s.image f) F -
          alternatingSum (s.image f) (fun t ↦ F (insert (f a) t)) := by
        rw [ih F, ih (fun t ↦ F (insert (f a) t))]
      _ = alternatingSum ((insert a s).image f) F := by
        rw [Finset.image_insert]
        by_cases h : f a ∈ s.image f
        · rw [Finset.insert_eq_of_mem h, alternatingSum_insert_of_mem h, sub_zero]
        · exact (alternatingSum_insert h F).symm

end OrlikSolomon
