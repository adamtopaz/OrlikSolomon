/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Algebra.UnitTransfer
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Configurations
public import OrlikSolomon.HyperplaneGT.Reconstruction.Local.Geometry
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Projection

/-!
# Local transfer from an actual centralizer restriction

The centralizer is defined using the actual universal quadratic relation span, and its
vertical restriction has the actual supported-module dual as target. Surjectivity supplies
a commuting functional with prescribed values on two distinct vertical labels. The guarded
parallel/triple determinant tests then give three equations whose common coefficient is a
unit. The generic unit-transfer calculation equates the other two graph coefficients.

The coefficient ring may be zero and need not be local or a domain. No quotient-isomorphism
hypothesis or substitute for the vertical module is introduced. Blueprint: L04 (`lem:l04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k : Type u} [Field k] {n : ℕ} (R : Type v) [CommRing R]

/-- Restriction of the actual universal-Q centralizer to the actual vertical module.
Blueprint: the map whose surjectivity is used in L04–L05. -/
def centralizerVerticalRestriction (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R)) :
    centralizer (universalQuadraticRelationSpan R) φ →ₗ[R]
      Module.Dual R (verticalModule (k := k) R z) :=
  (verticalRestriction R z).comp
    (centralizer (universalQuadraticRelationSpan R) φ).subtype

/-- Centralizer restriction evaluates the same functional on the same universal vector. -/
@[simp]
theorem centralizerVerticalRestriction_apply
    (z : Finset (Fin n)) (φ : Module.Dual R (Hyperplane k n →₀ R))
    (μ : centralizer (universalQuadraticRelationSpan R) φ)
    (x : verticalModule (k := k) R z) :
    centralizerVerticalRestriction R z φ μ x = μ.val x.val := rfl

/-- Surjectivity of the actual centralizer projection transfers coefficients from a parallel
graph to an intersecting graph. Only the given unit coefficient is cancelled.
Blueprint: L04 (`lem:l04`). -/
theorem local_transfer
    (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (φ : Module.Dual R (Hyperplane k n →₀ R))
    (hvertical : verticalRestriction R z φ = 0)
    (hsurj : Function.Surjective (centralizerVerticalRestriction R z φ))
    (H₀ H₁ H₂ : Hyperplane k n)
    (h₀ : ¬IsVertical z H₀) (h₁ : ¬IsVertical z H₁) (h₂ : ¬IsVertical z H₂)
    (hunit : IsUnit (dualCoordinates φ H₀))
    (h₀₁ : Parallel H₀ H₁) (h₀₂ : H₀ ≠ H₂) (hmeet : H₀.val ⊓ H₂.val ≠ ⊥) :
    dualCoordinates φ H₁ = dualCoordinates φ H₂ := by
  obtain ⟨V₁, V₂, hV₁, hV₂, hne, ht₁, ht₂⟩ :=
    exists_vertical_transfer_pair z i hzi H₀ H₁ H₂ h₀ h₁ h₂ h₀₁ h₀₂ hmeet
  let ψ := verticalRestriction R z (Finsupp.lapply V₂)
  obtain ⟨μ, hμ⟩ := hsurj ψ
  have hμ₁ : dualCoordinates μ.val V₁ = 0 := by
    have hv := LinearMap.congr_fun hμ (verticalSingle R z ⟨V₁, hV₁⟩ 1)
    simpa [ψ, hne, ne_comm] using hv
  have hμ₂ : dualCoordinates μ.val V₂ = 1 := by
    have hv := LinearMap.congr_fun hμ (verticalSingle R z ⟨V₂, hV₂⟩ 1)
    simpa [ψ] using hv
  have hφ₁ := (verticalRestriction_eq_zero_iff R z φ).mp hvertical V₁ hV₁
  have hφ₂ := (verticalRestriction_eq_zero_iff R z φ).mp hvertical V₂ hV₂
  have hcomm := (mem_centralizer_universalQuadraticRelationSpan_iff φ μ.val).mp μ.property
  obtain ⟨u, hu⟩ := hunit
  apply eq_of_unit_transfer u (dualCoordinates φ H₁) (dualCoordinates φ H₂)
    (dualCoordinates μ.val H₀) (dualCoordinates μ.val H₁) (dualCoordinates μ.val H₂)
  · simpa only [hu] using hcomm.1 H₀ H₁ h₀₁
  · simpa only [hu, show dualCoordinates φ V₁ = 0 from hφ₁, hμ₁, sub_zero] using
      hcomm.2 H₀ H₂ V₁ ht₁
  · simpa only [show dualCoordinates φ V₂ = 0 from hφ₂, hμ₂, sub_zero] using
      hcomm.2 H₁ H₂ V₂ ht₂

end OrlikSolomon.HyperplaneGT
