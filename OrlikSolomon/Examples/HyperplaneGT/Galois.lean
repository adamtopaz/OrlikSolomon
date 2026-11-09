/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Field.ZMod
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits

/-!
# Galois action and cofinal-stage consumers

These consumers exercise the point API without local semilinear instances, finite stable
enlargement in independent field universes, inherited inclusion morphisms, and the empty
hyperplane type in dimension zero. Over `𝔽₂` the actual orbit of a coordinate hyperplane over
its own base field is a singleton; no characteristic assumption enters the construction.

Blueprint: G04–G06 (`lem:g04`, `lem:g05`, `def:g06`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.GaloisExamples

open CategoryTheory

variable {k : Type u} [Field k]

/-- Point consumers do not need to install inverse-pair instances for the field automorphism. -/
theorem coordinate_inverse {ι : Type*} (σ : k ≃+* k) (x : ι → k) :
    (fieldCoordinateAddEquiv σ ι).symm (fieldCoordinateAddEquiv σ ι x) = x := by
  simp

/-- Rewriting a transformed equation uses the public additive point map. -/
theorem transformed_equation {n : ℕ} (σ : k ≃+* k) (f : (Fin n → k) →ᵃ[k] k)
    (x : Fin n → k) :
    fieldAffineForm σ f (fieldCoordinateAddEquiv σ (Fin n) x) = σ (f x) := by
  rw [fieldAffineForm_apply]

/-- Empty intersections are transported correctly, including the affine bottom convention. -/
theorem empty_intersection (σ : k ≃+* k) {n : ℕ}
    (H K : AffineSubspace k (Fin n → k)) :
    fieldAffineSubspace σ H ⊓ fieldAffineSubspace σ K = ⊥ ↔ H ⊓ K = ⊥ := by
  rw [← fieldAffineSubspace_inf, fieldAffineSubspace_eq_bot_iff]

/-- The geometric and base fields may have independent universes. -/
theorem finite_enlargement {k₀ : Type v} [Field k₀] [Algebra k₀ k]
    [Algebra.IsAlgebraic k₀ k] {n : ℕ} (s : Finset (Hyperplane k n)) :
    ∃ A : StableArrangement k₀ k n, ∀ H ∈ s, H.val ∈ A.val := by
  obtain ⟨A, -, hs⟩ := (fullCofinalSystem k₀ k n).cofinal s
  exact ⟨A, hs⟩

/-- Membership in the constructed finite enlargement is invariant in both directions. -/
theorem enlargement_invariant {k₀ : Type v} [Field k₀] [Algebra k₀ k]
    [Algebra.IsAlgebraic k₀ k] {n : ℕ} (s : Finset (Hyperplane k n))
    (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    (σ • H).val ∈ stableClosure (k₀ := k₀) s ↔ H.val ∈ stableClosure (k₀ := k₀) s :=
  (isGaloisStable_stableClosure s).smul_mem_iff σ H

/-- Common upper stages and their actual inclusion morphisms work for any chosen cofinal
family; the family is not required to contain a union. -/
theorem common_stage {k₀ : Type v} [Field k₀] [Algebra k₀ k] {n : ℕ}
    (C : CofinalSystem k₀ k n) (A B : C.Stage) : ∃ D : C.Stage, Nonempty (A ⟶ D) ∧
      Nonempty (B ⟶ D) := by
  obtain ⟨D, hA, hB⟩ := exists_ge_ge A B
  exact ⟨D, ⟨homOfLE hA⟩, ⟨homOfLE hB⟩⟩

/-- The inherited thin-category composition is available through the named stage carrier. -/
theorem inclusion_comp {k₀ : Type v} [Field k₀] [Algebra k₀ k] {n : ℕ}
    (C : CofinalSystem k₀ k n) (A B D : C.Stage) (hAB : A ≤ B) (hBD : B ≤ D) :
    homOfLE hAB ≫ homOfLE hBD = homOfLE (hAB.trans hBD) := by
  rfl

/-- The full system still has stages when there are no hyperplanes in dimension zero. -/
theorem dimension_zero_stages {k₀ : Type v} [Field k₀] [Algebra k₀ k]
    [Algebra.IsAlgebraic k₀ k] : Nonempty (fullCofinalSystem k₀ k 0).Stage :=
  inferInstance

/-- There is no hidden positive-dimension assumption in the system definition. -/
theorem dimension_zero_no_hyperplane (H : Hyperplane k 0) : False :=
  not_isHyperplane_of_subsingleton H.val H.property

/-- A concrete coordinate hyperplane over `𝔽₂`. -/
def coordinateZero : Hyperplane (ZMod 2) 1 :=
  graphHyperplane 0 (AffineMap.const _ _ 0)

/-- The actual coefficient orbit over the field itself is a singleton, also in characteristic
two. This checks the group action and the finite-orbit set together. -/
theorem characteristic_two_orbit :
    galoisOrbit (k₀ := ZMod 2) coordinateZero = {coordinateZero} := by
  classical
  ext H
  rw [mem_galoisOrbit, MulAction.mem_orbit_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, rfl⟩
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp [hσ]
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

end OrlikSolomon.HyperplaneGT.GaloisExamples
