/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Full algebraic dual coordinates and the contragredient action

The dual of a free module on any index type is the full product of coefficient rings.
The equivalence here is Mathlib's free-module universal property with its direction reversed.
Linear automorphisms act on the dual by precomposition with their inverses, giving a left
action which preserves evaluation. No finite-index or reflexivity assumption is used.

Blueprint: `lem:u03`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u v w

variable {R : Type u} [CommSemiring R] {ι : Type v}

/-- The algebraic dual of a free module is the full coefficient product, with coordinates given
by evaluation on the standard basis. Blueprint: `lem:u03`. -/
noncomputable def dualCoordinates : Module.Dual R (ι →₀ R) ≃ₗ[R] (ι → R) :=
  (Finsupp.llift R R R ι).symm

@[simp]
theorem dualCoordinates_apply (φ : Module.Dual R (ι →₀ R)) (i : ι) :
    dualCoordinates φ i = φ (Finsupp.single i 1) := rfl

/-- The inverse coordinate map pairs a coefficient function with the finite support of a vector.
Blueprint: `lem:u03`. -/
theorem dualCoordinates_symm_apply (a : ι → R) (m : ι →₀ R) :
    dualCoordinates.symm a m = m.sum (fun i r ↦ r * a i) := rfl

@[simp]
theorem dualCoordinates_symm_apply_single (a : ι → R) (i : ι) (r : R) :
    dualCoordinates.symm a (Finsupp.single i r) = r * a i := by
  rw [dualCoordinates_symm_apply, Finsupp.sum_single_index (by simp)]

/-- Every functional is the finite sum of its values on standard basis vectors.
Blueprint: `lem:u03`. -/
theorem dual_apply_eq_sum (φ : Module.Dual R (ι →₀ R)) (m : ι →₀ R) :
    φ m = m.sum (fun i r ↦ r * φ (Finsupp.single i 1)) := by
  rw [← dualCoordinates_symm_apply]
  exact congrArg (fun f ↦ f m) (dualCoordinates.symm_apply_apply φ).symm

/-- Evaluation on the standard basis separates functionals, including for infinite index types.
Blueprint: `lem:u03`. -/
theorem dualCoordinates_ext {φ μ : Module.Dual R (ι →₀ R)}
    (h : ∀ i, φ (Finsupp.single i 1) = μ (Finsupp.single i 1)) : φ = μ :=
  dualCoordinates.injective (funext h)

/-- Unit multiples of coordinate functionals agree exactly when both their coordinate labels
and units agree. Nontrivial coefficients distinguish the coordinate lines, for arbitrary index
types. Blueprint: the unit-delta uniqueness in L05 (`thm:l05`), also used in I01. -/
theorem unit_smul_lapply_eq_iff [Nontrivial R] (u v : Rˣ) (i j : ι) :
    (u : R) • (Finsupp.lapply i : Module.Dual R (ι →₀ R)) =
      (v : R) • Finsupp.lapply j ↔ i = j ∧ u = v := by
  constructor
  · intro he
    classical
    have hij : i = j := by
      by_contra hij
      have hv := congrArg (fun φ : Module.Dual R (ι →₀ R) ↦ φ (Finsupp.single i 1)) he
      simp [hij, ne_comm] at hv
    subst j
    have huv : (u : R) = (v : R) := by
      have hv := congrArg (fun φ : Module.Dual R (ι →₀ R) ↦ φ (Finsupp.single i 1)) he
      simpa using hv
    exact ⟨rfl, Units.ext huv⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Evaluation against the full algebraic dual separates finitely supported vectors.
Blueprint: `lem:u03`. -/
theorem finsupp_eq_of_dual_eval_eq {m m' : ι →₀ R}
    (h : ∀ φ : Module.Dual R (ι →₀ R), φ m = φ m') : m = m' := by
  ext i
  exact h (Finsupp.lapply i)

variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- The contragredient homomorphism: an automorphism acts on functionals by precomposition with
its inverse. This direction makes the induced action a left action. Blueprint: `lem:u03`. -/
def dualAction : (M ≃ₗ[R] M) →* (Module.Dual R M ≃ₗ[R] Module.Dual R M) where
  toFun g := g.symm.dualMap
  map_one' := by ext φ m; rfl
  map_mul' g h := by ext φ m; rfl

@[simp]
theorem dualAction_apply (g : M ≃ₗ[R] M) (φ : Module.Dual R M) (m : M) :
    dualAction g φ m = φ (g.symm m) := rfl

/-- Simultaneously acting on a functional and a vector preserves their evaluation.
Blueprint: `lem:u03`. -/
theorem dualAction_apply_apply (g : M ≃ₗ[R] M) (φ : Module.Dual R M) (m : M) :
    dualAction g φ (g m) = φ m := by simp

end OrlikSolomon.HyperplaneGT
