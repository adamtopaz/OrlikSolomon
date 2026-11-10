/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Distinct Frobenius powers on the actual prime-field algebraic closure

The canonical algebraic closure of `ZMod p` has an actual base-field Frobenius
automorphism. Its positive powers cannot be identity: that would put every element of
the infinite algebraically closed field in the finite root set of `X ^ (p ^ m) - X`.
Thus its natural powers embed `ℕ` into the actual field-automorphism group.

The formulas identify the algebra automorphism with Mathlib's `frobeniusEquiv` and
`iterateFrobeniusEquiv`. No infinite group is supplied as a hypothesis. This example leaf
imports neither arrangements nor topology, and installs no new instance.

Blueprint: the required infinite-Galois regression for T02, T05–T07.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT.PrimeClosureExamples

variable (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure (ZMod p)
local notation "G" => K ≃ₐ[ZMod p] K

/-- The actual prime-field Frobenius automorphism on the canonical algebraic closure. -/
noncomputable def frobenius : G :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K

/-- The base-field Frobenius raises each geometric scalar to its `p`th power. -/
theorem frobenius_apply (x : K) : frobenius p x = x ^ p := by
  change x ^ Fintype.card (ZMod p) = x ^ p
  rw [ZMod.card]

/-- The underlying ring equivalence is Mathlib's actual Frobenius equivalence. -/
theorem frobenius_toRingEquiv :
    (frobenius p).toRingEquiv = frobeniusEquiv K p := by
  ext x
  exact frobenius_apply p x

/-- Natural powers of the actual automorphism have the expected iterated power formula. -/
theorem frobenius_pow_apply (m : ℕ) (x : K) :
    ((frobenius p) ^ m) x = x ^ (p ^ m) := by
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K ^ m) x = _
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

/-- The ring equivalence of each natural power is the existing iterated Frobenius. -/
theorem frobenius_pow_toRingEquiv (m : ℕ) :
    ((frobenius p) ^ m).toRingEquiv = iterateFrobeniusEquiv K p m := by
  ext x
  exact frobenius_pow_apply p m x

/-- No positive power of Frobenius is the identity on the actual algebraic closure. -/
theorem frobenius_pow_ne_one (m : ℕ) (hm : 0 < m) :
    (frobenius p) ^ m ≠ 1 := by
  intro h
  have hp : 1 < p ^ m := Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt
  have hroot (x : K) : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).IsRoot x := by
    have hx : x ^ (p ^ m) = x := by
      simpa only [h, AlgEquiv.one_apply] using (frobenius_pow_apply p m x).symm
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero] using hx
  have hinfinite : Set.Infinite
      {x : K | (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).IsRoot x} := by
    have heq : {x : K | (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).IsRoot x} =
        Set.univ := Set.eq_univ_of_forall hroot
    rw [heq]
    exact Set.infinite_univ
  exact Polynomial.X_pow_sub_X_ne_zero hp
    (Polynomial.eq_zero_of_infinite_isRoot _ hinfinite)

/-- All natural Frobenius powers, including exponent zero, are distinct. -/
theorem frobenius_pow_injective :
    Function.Injective (fun m : ℕ ↦ (frobenius p) ^ m) := by
  apply injective_pow_iff_not_isOfFinOrder.mpr
  intro h
  obtain ⟨m, hm, heq⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  exact frobenius_pow_ne_one p m hm heq

/-- The actual automorphism group is infinite, witnessed by distinct Frobenius powers. -/
theorem galois_infinite : Infinite G :=
  Infinite.of_injective (fun m : ℕ ↦ (frobenius p) ^ m) (frobenius_pow_injective p)

/-- Some actual geometric scalar is moved by the prime-field Frobenius. -/
theorem exists_frobenius_moved_scalar : ∃ a : K, frobenius p a ≠ a := by
  have h : frobenius p ≠ 1 := by
    simpa only [pow_one] using frobenius_pow_ne_one p 1 Nat.zero_lt_one
  obtain ⟨a, ha⟩ := DFunLike.exists_ne h
  exact ⟨a, by simpa only [AlgEquiv.one_apply] using ha⟩

end OrlikSolomon.HyperplaneGT.PrimeClosureExamples
