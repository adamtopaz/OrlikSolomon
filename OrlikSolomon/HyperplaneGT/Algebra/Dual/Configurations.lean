/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Alternating
public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Relations

/-!
# Commuting functionals on the universal hyperplane module

The global quadratic relation submodule is the actual span of all strict parallel-pair
and guarded dependent-triple relators. Annihilating this span is equivalent to the two
configuration determinant equations. These formulas specialize the generic alternating
pairing and centralizer API, without introducing another relation submodule or diagram.
They hold over every commutative coefficient ring, including the zero ring, in every
ambient dimension and characteristic.

Blueprint: the configuration equations in U04 (`lem:u04`).
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k : Type u} [Field k] {n : ℕ} {R : Type v} [CommRing R]

/-- The determinant on a global pair wedge is its two-coordinate determinant.
Blueprint: the parallel-pair equation in U04 (`lem:u04`). -/
@[simp]
theorem dualDeterminant_universalExteriorPair
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) (H K : Hyperplane k n) :
    dualDeterminant φ ψ (universalExteriorPair R H K) =
      dualCoordinates φ H * dualCoordinates ψ K -
        dualCoordinates φ K * dualCoordinates ψ H :=
  dualDeterminant_single φ ψ H K

/-- The determinant on a global difference wedge is its difference-coordinate determinant.
Blueprint: the dependent-triple equation in U04 (`lem:u04`). -/
@[simp]
theorem dualDeterminant_universalExteriorDifferencePair
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) (H K L : Hyperplane k n) :
    dualDeterminant φ ψ (universalExteriorDifferencePair R H K L) =
      (dualCoordinates φ H - dualCoordinates φ L) *
          (dualCoordinates ψ K - dualCoordinates ψ L) -
        (dualCoordinates φ K - dualCoordinates φ L) *
          (dualCoordinates ψ H - dualCoordinates ψ L) :=
  dualDeterminant_sub_single φ ψ H K L

/-- Commuting for the actual global relation span is equivalent to the determinant equations
on every strict parallel pair and guarded dependent triple. Blueprint: U04 (`lem:u04`). -/
theorem commutes_universalQuadraticRelationSpan_iff
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) :
    Commutes (universalQuadraticRelationSpan R) φ ψ ↔
      (∀ H K : Hyperplane k n, Parallel H K →
        dualCoordinates φ H * dualCoordinates ψ K =
          dualCoordinates φ K * dualCoordinates ψ H) ∧
      (∀ H K L : Hyperplane k n, DependentTriple H K L →
        (dualCoordinates φ H - dualCoordinates φ L) *
            (dualCoordinates ψ K - dualCoordinates ψ L) =
          (dualCoordinates φ K - dualCoordinates φ L) *
            (dualCoordinates ψ H - dualCoordinates ψ L)) := by
  rw [universalQuadraticRelationSpan, commutes_span_iff]
  constructor
  · intro h
    constructor
    · intro H K hHK
      have hdet := h _ (Or.inl ⟨H, K, hHK, rfl⟩)
      rw [dualDeterminant_universalExteriorPair] at hdet
      exact sub_eq_zero.mp hdet
    · intro H K L hHKL
      have hdet := h _ (Or.inr ⟨H, K, L, hHKL, rfl⟩)
      rw [dualDeterminant_universalExteriorDifferencePair] at hdet
      exact sub_eq_zero.mp hdet
  · rintro ⟨hpair, htriple⟩ q (⟨H, K, hHK, rfl⟩ | ⟨H, K, L, hHKL, rfl⟩)
    · rw [dualDeterminant_universalExteriorPair, sub_eq_zero]
      exact hpair H K hHK
    · rw [dualDeterminant_universalExteriorDifferencePair, sub_eq_zero]
      exact htriple H K L hHKL

/-- Membership in a universal-relation centralizer is exactly the two configuration tests.
Blueprint: U04 (`lem:u04`). -/
theorem mem_centralizer_universalQuadraticRelationSpan_iff
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) :
    ψ ∈ centralizer (universalQuadraticRelationSpan R) φ ↔
      (∀ H K : Hyperplane k n, Parallel H K →
        dualCoordinates φ H * dualCoordinates ψ K =
          dualCoordinates φ K * dualCoordinates ψ H) ∧
      (∀ H K L : Hyperplane k n, DependentTriple H K L →
        (dualCoordinates φ H - dualCoordinates φ L) *
            (dualCoordinates ψ K - dualCoordinates ψ L) =
          (dualCoordinates φ K - dualCoordinates φ L) *
            (dualCoordinates ψ H - dualCoordinates ψ L)) := by
  rw [mem_centralizer_iff, commutes_universalQuadraticRelationSpan_iff]

end OrlikSolomon.HyperplaneGT
