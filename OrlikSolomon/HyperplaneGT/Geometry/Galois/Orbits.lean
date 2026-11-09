/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Pi
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.GroupTheory.GroupAction.Defs
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.System

/-!
# Finite coefficient Galois orbits

Over an algebraic field extension, the conjugates of a scalar lie in the finite root set of
its nonzero minimal polynomial. A finite coefficient tuple therefore has finitely many
conjugates. Applying the equation map gives finite hyperplane orbits, without choosing a
normal closure or assuming perfectness. Taking finitely many orbits supplies the full
cofinal system of stable finite arrangements.

## Main results

* `finite_scalarOrbit` and `finite_coordinateOrbit` give the finite coefficient bounds.
* `finite_orbit` proves finiteness of the actual hyperplane orbit.
* `stableClosure` is a stable finite arrangement containing any prescribed finite set.
* `fullCofinalSystem` selects all stable finite arrangements.

Blueprint: G05 (`lem:g05`) and the existence part of G06 (`def:g06`).
-/

@[expose] public section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]

/-- The conjugates of an algebraic scalar form a finite set: they are roots of its minimal
polynomial over the base field. No separability or normality is required. -/
theorem finite_scalarOrbit (a : k) (ha : IsAlgebraic k₀ a) :
    (Set.range fun σ : k ≃ₐ[k₀] k ↦ σ a).Finite := by
  have hp : (minpoly k₀ a).map (algebraMap k₀ k) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap k₀ k).injective).mpr (minpoly.ne_zero ha.isIntegral)
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  rintro _ ⟨σ, rfl⟩
  change ((minpoly k₀ a).map (algebraMap k₀ k)).eval (σ a) = 0
  rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval_algHom k₀ σ.toAlgHom a

/-- A finite tuple of algebraic coefficients has finitely many simultaneous conjugates. -/
theorem finite_coordinateOrbit {ι : Type w} [Finite ι] (a : ι → k)
    (ha : ∀ i, IsAlgebraic k₀ (a i)) :
    (Set.range fun σ : k ≃ₐ[k₀] k ↦ fun i ↦ σ (a i)).Finite := by
  apply (Set.Finite.pi' (fun i ↦ finite_scalarOrbit (a i) (ha i))).subset
  rintro _ ⟨σ, rfl⟩ i
  exact ⟨σ, rfl⟩

variable [Algebra.IsAlgebraic k₀ k] {n : ℕ}

/-- Every affine hyperplane has finite orbit over an algebraic field extension. The finite
bound uses one fixed equation; equation independence is already part of the group action.

Blueprint: G05 (`lem:g05`). -/
theorem finite_orbit (H : Hyperplane k n) : (MulAction.orbit (k ≃ₐ[k₀] k) H).Finite := by
  let a := affineCoefficients (equation H.val)
  have hc := finite_coordinateOrbit (k₀ := k₀) a
    (fun i ↦ Algebra.IsAlgebraic.isAlgebraic (R := k₀) (a i))
  have hv : (Set.range fun σ : k ≃ₐ[k₀] k ↦ (σ • H).val).Finite := by
    apply (hc.image (fun b ↦ zeroLocus (coefficientForm b))).subset
    rintro _ ⟨σ, rfl⟩
    refine ⟨fun i ↦ σ (a i), ⟨σ, rfl⟩, ?_⟩
    exact (isEquation_fieldAffineForm σ.toRingEquiv (isEquation_equation H.property)).zeroLocus_eq
  have hi : ((fun K : Hyperplane k n ↦ K.val) ''
      MulAction.orbit (k ≃ₐ[k₀] k) H).Finite := by
    simpa only [MulAction.orbit, ← Set.range_comp', Function.comp_def] using hv
  exact hi.of_finite_image Subtype.val_injective.injOn

/-- The finite set underlying the actual Galois orbit of a hyperplane. -/
noncomputable def galoisOrbit (H : Hyperplane k n) : Finset (Hyperplane k n) :=
  (finite_orbit (k₀ := k₀) H).toFinset

@[simp]
theorem mem_galoisOrbit (H K : Hyperplane k n) :
    K ∈ galoisOrbit (k₀ := k₀) H ↔ K ∈ MulAction.orbit (k ≃ₐ[k₀] k) H :=
  Set.Finite.mem_toFinset _

/-- The union of the Galois orbits of a finite set of hyperplanes. -/
noncomputable def galoisClosure (s : Finset (Hyperplane k n)) : Finset (Hyperplane k n) := by
  classical
  exact s.biUnion (galoisOrbit (k₀ := k₀))

@[simp]
theorem mem_galoisClosure (s : Finset (Hyperplane k n)) (H : Hyperplane k n) :
    H ∈ galoisClosure (k₀ := k₀) s ↔ ∃ K ∈ s, H ∈ MulAction.orbit (k ≃ₐ[k₀] k) K := by
  classical
  simp only [galoisClosure, Finset.mem_biUnion, mem_galoisOrbit]

/-- Every original hyperplane belongs to its finite stable enlargement. -/
theorem subset_galoisClosure (s : Finset (Hyperplane k n)) :
    s ⊆ galoisClosure (k₀ := k₀) s := by
  intro H hH
  exact (mem_galoisClosure s H).mpr ⟨H, hH, MulAction.mem_orbit_self H⟩

/-- A stable finite arrangement containing a prescribed finite set of hyperplanes. -/
noncomputable def stableClosure (s : Finset (Hyperplane k n)) : Arrangement k (Fin n → k) := by
  classical
  exact Arrangement.ofFinset ((galoisClosure (k₀ := k₀) s).image Subtype.val)

@[simp]
theorem mem_stableClosure (s : Finset (Hyperplane k n)) (H : Hyperplane k n) :
    H.val ∈ stableClosure (k₀ := k₀) s ↔ H ∈ galoisClosure (k₀ := k₀) s := by
  classical
  simp only [stableClosure, Arrangement.mem_ofFinset, Finset.mem_image]
  constructor
  · rintro ⟨⟨K, hK, hKH⟩, -⟩
    exact Subtype.ext hKH ▸ hK
  · intro hH
    exact ⟨⟨H, hH, rfl⟩, H.property⟩

/-- The finite orbit union is invariant under every coefficient Galois automorphism. -/
theorem isGaloisStable_stableClosure (s : Finset (Hyperplane k n)) :
    IsGaloisStable (k₀ := k₀) (stableClosure (k₀ := k₀) s) := by
  intro σ H hH
  rw [mem_stableClosure, mem_galoisClosure] at hH ⊢
  obtain ⟨K, hK, hH⟩ := hH
  exact ⟨K, hK, MulAction.mem_orbit_of_mem_orbit σ hH⟩

/-- The full collection of finite stable arrangements is a cofinal system. Directedness and
finite common upper stages follow from the generic `CofinalSystem` API.

Blueprint: G05 (`lem:g05`), G06 (`def:g06`). -/
noncomputable def fullCofinalSystem (k₀ : Type v) (k : Type u) [Field k₀] [Field k]
    [Algebra k₀ k] [Algebra.IsAlgebraic k₀ k] (n : ℕ) : CofinalSystem k₀ k n where
  stages := Set.univ
  cofinal s := ⟨⟨stableClosure s, isGaloisStable_stableClosure s⟩, Set.mem_univ _,
    fun H hH ↦ (mem_stableClosure s H).mpr (subset_galoisClosure s hH)⟩

@[simp]
theorem mem_fullCofinalSystem (A : StableArrangement k₀ k n) :
    A ∈ (fullCofinalSystem k₀ k n).stages := Set.mem_univ _

end OrlikSolomon.HyperplaneGT
