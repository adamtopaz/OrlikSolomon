/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Primitive
public import OrlikSolomon.HyperplaneGT.Reconstruction.Local.Transfer
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Annihilators

/-!
# Local detection of a unit-supported hyperplane functional

Over a nonzero local coefficient ring, in dimension at least two, a functional is a unit
multiple of a graph delta exactly when it is primitive, vanishes on the actual vertical
module, vanishes at some graph coordinate, and its actual universal-Q centralizer restricts
surjectively onto the vertical module's full dual. The supporting graph and unit are unique,
and its actual universal-Q centralizer is the decomposition submodule.

Primitivity is literal surjectivity. The dimension bound supplies a graph meeting a given
graph. The only coefficient cancellation uses a proved unit through L04; there is no
quotient-isomorphism or infinite-dual reflexivity hypothesis. Blueprint: L05 (`thm:l05`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k : Type u} [Field k] {n : ℕ} (R : Type v) [CommRing R]

private theorem exists_zero_parallel_graph [Nontrivial R]
    (z : Finset (Fin n)) (i : Fin n) (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (φ : Module.Dual R (Hyperplane k n →₀ R))
    (hvertical : verticalRestriction R z φ = 0)
    (hsurj : Function.Surjective (centralizerVerticalRestriction R z φ))
    (H₀ : Hyperplane k n) (h₀ : ¬IsVertical z H₀)
    (hunit : IsUnit (dualCoordinates φ H₀))
    (hzero : ∃ H' : Hyperplane k n, ¬IsVertical z H' ∧ dualCoordinates φ H' = 0) :
    ∃ H₁ : Hyperplane k n,
      ¬IsVertical z H₁ ∧ Parallel H₀ H₁ ∧ dualCoordinates φ H₁ = 0 := by
  obtain ⟨H', hH', hφ'⟩ := hzero
  have hne : H₀ ≠ H' := by
    intro he
    apply hunit.ne_zero
    simpa only [he] using hφ'
  by_cases hp : Parallel H₀ H'
  · exact ⟨H', hH', hp, hφ'⟩
  · obtain ⟨H₁, h₁, h₀₁⟩ := exists_parallel_graph z i hzi H₀ h₀
    refine ⟨H₁, h₁, h₀₁, ?_⟩
    have hmeet : H₀.val ⊓ H'.val ≠ ⊥ := fun hb ↦ hp ⟨hne, hb⟩
    exact (local_transfer R z i hzi φ hvertical hsurj H₀ H₁ H' h₀ h₁ hH'
      hunit h₀₁ hne hmeet).trans hφ'

private theorem eq_smul_delta_of_local_detection [Nontrivial R] (hn : 2 ≤ n)
    (z : Finset (Fin n)) (i : Fin n) (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (φ : Module.Dual R (Hyperplane k n →₀ R))
    (hvertical : verticalRestriction R z φ = 0)
    (hsurj : Function.Surjective (centralizerVerticalRestriction R z φ))
    (H₀ : Hyperplane k n) (h₀ : ¬IsVertical z H₀)
    (hunit : IsUnit (dualCoordinates φ H₀))
    (hzero : ∃ H' : Hyperplane k n, ¬IsVertical z H' ∧ dualCoordinates φ H' = 0) :
    φ = dualCoordinates φ H₀ • Finsupp.lapply H₀ := by
  classical
  obtain ⟨H₁, h₁, h₀₁, hφ₁⟩ :=
    exists_zero_parallel_graph R z i hzi φ hvertical hsurj H₀ h₀ hunit hzero
  have hvanish (K : Hyperplane k n) (hK : ¬IsVertical z K) (hne : H₀ ≠ K) :
      dualCoordinates φ K = 0 := by
    by_cases hp : Parallel H₀ K
    · obtain ⟨H₂, h₂, h₀₂, hmeet⟩ := exists_meeting_graph hn z i hzi H₀ h₀
      have hφ₂ : dualCoordinates φ H₂ = 0 :=
        (local_transfer R z i hzi φ hvertical hsurj H₀ H₁ H₂ h₀ h₁ h₂
          hunit h₀₁ h₀₂ hmeet).symm.trans hφ₁
      exact (local_transfer R z i hzi φ hvertical hsurj H₀ K H₂ h₀ hK h₂
        hunit hp h₀₂ hmeet).trans hφ₂
    · have hmeet : H₀.val ⊓ K.val ≠ ⊥ := fun hb ↦ hp ⟨hne, hb⟩
      exact (local_transfer R z i hzi φ hvertical hsurj H₀ H₁ K h₀ h₁ hK
        hunit h₀₁ hne hmeet).symm.trans hφ₁
  apply dualCoordinates_ext
  intro K
  by_cases hKH : K = H₀
  · subst K
    simp
  · by_cases hK : IsVertical z K
    · have hz := (verticalRestriction_eq_zero_iff R z φ).mp hvertical K hK
      simpa [hKH] using hz
    · have hz := hvanish K hK (Ne.symm hKH)
      simpa [hKH] using hz

/-- In dimension at least two over a nonzero local coefficient ring, the four literal
primitive/vertical/zero-coordinate/centralizer-surjectivity conditions detect exactly a unit
multiple of one graph delta. `IsLocalRing R` includes nontriviality. Blueprint: L05 (`thm:l05`). -/
theorem local_detection_iff [IsLocalRing R] (hn : 2 ≤ n)
    (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (φ : Module.Dual R (Hyperplane k n →₀ R)) :
    (∃ (H : Hyperplane k n) (u : Rˣ),
      ¬IsVertical z H ∧ φ = (u : R) • Finsupp.lapply H) ↔
      Primitive φ ∧ verticalRestriction R z φ = 0 ∧
        (∃ H' : Hyperplane k n,
          ¬IsVertical z H' ∧ dualCoordinates φ H' = 0) ∧
        Function.Surjective (centralizerVerticalRestriction R z φ) := by
  constructor
  · rintro ⟨H, u, hH, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply primitive_of_isUnit_coordinate _ H
      simp
    · rw [map_smul, verticalRestriction_delta R z H hH, smul_zero]
    · obtain ⟨K, hK, hHK⟩ := exists_parallel_graph z i hzi H hH
      refine ⟨K, hK, ?_⟩
      simp [hHK.1]
    · change Function.Surjective ((verticalRestriction R z).comp
        (centralizer (universalQuadraticRelationSpan R)
          ((u : R) • Finsupp.lapply H)).subtype)
      rw [centralizer_unit_smul_delta R H u]
      exact decompositionVerticalRestriction_surjective R z i hzi H hH
  · rintro ⟨hprimitive, hvertical, hzero, hsurj⟩
    obtain ⟨H, hunit⟩ := (primitive_iff_unit_coordinate φ).mp hprimitive
    have hH : ¬IsVertical z H := by
      intro hv
      exact hunit.ne_zero ((verticalRestriction_eq_zero_iff R z φ).mp hvertical H hv)
    have he := eq_smul_delta_of_local_detection R hn z i hzi φ hvertical hsurj H hH hunit hzero
    obtain ⟨u, hu⟩ := hunit
    exact ⟨H, u, hH, by simpa only [dualCoordinates_apply, hu] using he⟩

/-- Local detection recovers one unique graph and one unique unit; the centralizer is the
actual decomposition submodule at that graph. Blueprint: the uniqueness and centralizer clauses
of L05 (`thm:l05`). -/
theorem existsUnique_unit_delta_of_local_detection [IsLocalRing R]
    (hn : 2 ≤ n) (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (φ : Module.Dual R (Hyperplane k n →₀ R))
    (hprimitive : Primitive φ)
    (hvertical : verticalRestriction R z φ = 0)
    (hzero : ∃ H' : Hyperplane k n,
      ¬IsVertical z H' ∧ dualCoordinates φ H' = 0)
    (hsurj : Function.Surjective (centralizerVerticalRestriction R z φ)) :
    ∃! p : Hyperplane k n × Rˣ,
      ¬IsVertical z p.1 ∧ φ = (p.2 : R) • Finsupp.lapply p.1 ∧
        centralizer (universalQuadraticRelationSpan R) φ = decomposition R p.1 := by
  obtain ⟨H, u, hH, hφ⟩ := (local_detection_iff R hn z i hzi φ).mpr
    ⟨hprimitive, hvertical, hzero, hsurj⟩
  refine ⟨(H, u), ⟨hH, hφ, ?_⟩, ?_⟩
  · rw [hφ, centralizer_unit_smul_delta]
  · rintro ⟨K, v⟩ ⟨-, hφ', -⟩
    obtain ⟨hHK, huv⟩ := (unit_smul_lapply_eq_iff u v H K).mp (hφ.symm.trans hφ')
    exact Prod.ext hHK.symm huv.symm

end OrlikSolomon.HyperplaneGT
