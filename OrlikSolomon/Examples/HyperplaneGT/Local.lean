/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Local
public import OrlikSolomon.Examples.HyperplaneGT.Trace
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Local transfer and detection regressions

The actual centralizer restriction is tested with zero coefficients, nonfield nilpotent
local coefficients and characteristic-two dual numbers. A nonzero functional on the actual
vertical module occurs as a target. A two-supported functional in dimension one satisfies
all four literal detection conditions but is no unit delta, testing the dimension bound.

Blueprint: regression consumers for L04–L05 (`lem:l04`, `thm:l05`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.LocalExamples

universe u v

/-- The scalar three is a nontrivial unit of the nonfield local ring `ℤ/4`. -/
def modFourUnit : (ZMod 4)ˣ := ⟨3, 3, by decide, by decide⟩

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- A graph axis over the two-element geometric field. -/
def axis : Hyperplane (ZMod 2) 2 :=
  graphHyperplane 1 (AffineMap.const _ _ 0)

/-- A unit-supported functional over `ℤ/4` on the actual hyperplane module. -/
def modFourFunctional : Module.Dual (ZMod 4) (Hyperplane (ZMod 2) 2 →₀ ZMod 4) :=
  (modFourUnit : ZMod 4) • Finsupp.lapply axis

/-- The actual unit-delta functional over a nonfield local coefficient ring satisfies all four
conditions; the centralizer target remains the actual vertical-module dual. -/
theorem mod_four_conditions :
    Primitive modFourFunctional ∧
      verticalRestriction (ZMod 4) (omittedCoordinates 1)
        modFourFunctional = 0 ∧
      (∃ H' : Hyperplane (ZMod 2) 2, ¬IsVertical (omittedCoordinates 1) H' ∧
        dualCoordinates modFourFunctional H' = 0) ∧
      Function.Surjective (centralizerVerticalRestriction (ZMod 4) (omittedCoordinates 1)
        modFourFunctional) :=
  (local_detection_iff (ZMod 4) (by decide) _ 1 (mem_omittedCoordinates 1) _).mp
    ⟨axis, modFourUnit, not_isVertical_graphHyperplane 1 _, rfl⟩

/-- The centralizer of the detected functional reaches a nonzero actual vertical coordinate.
The value one on the corresponding supported single rules out a vacuous target. -/
theorem mod_four_nonzero_vertical_target :
    ∃ μ : centralizer (universalQuadraticRelationSpan (ZMod 4))
        modFourFunctional,
      centralizerVerticalRestriction (ZMod 4) (omittedCoordinates 1)
          modFourFunctional μ =
        verticalRestriction (ZMod 4) (omittedCoordinates 1)
          (Finsupp.lapply (CoordinateExamples.xLine (ZMod 2))) ∧
      verticalRestriction (ZMod 4) (omittedCoordinates 1)
          (Finsupp.lapply (CoordinateExamples.xLine (ZMod 2)))
        (verticalSingle (ZMod 4) (omittedCoordinates 1)
          ⟨CoordinateExamples.xLine (ZMod 2), TraceExamples.xLine_isVertical⟩ 1) = 1 := by
  obtain ⟨μ, hμ⟩ := mod_four_conditions.2.2.2
    (verticalRestriction (ZMod 4) (omittedCoordinates 1)
      (Finsupp.lapply (CoordinateExamples.xLine (ZMod 2))))
  exact ⟨μ, hμ, TraceExamples.actual_vertical_coordinate⟩

/-- L04 still applies over the zero ring, with no accidental nontriviality or locality premise.
-/
theorem zero_ring_transfer {k : Type u} [Field k] {n : ℕ}
    (z : Finset (Fin n)) (i : Fin n) (hzi : ∀ j, j ∈ z ↔ j ≠ i)
    (H₀ H₁ H₂ : Hyperplane k n)
    (h₀ : ¬IsVertical z H₀) (h₁ : ¬IsVertical z H₁) (h₂ : ¬IsVertical z H₂)
    (h₀₁ : Parallel H₀ H₁) (h₀₂ : H₀ ≠ H₂) (hmeet : H₀.val ⊓ H₂.val ≠ ⊥) :
    dualCoordinates (0 : Module.Dual (ZMod 1) (Hyperplane k n →₀ ZMod 1)) H₁ =
      dualCoordinates (0 : Module.Dual (ZMod 1) (Hyperplane k n →₀ ZMod 1)) H₂ := by
  apply local_transfer (ZMod 1) z i hzi 0 (by simp) ?_ H₀ H₁ H₂ h₀ h₁ h₂ ?_ h₀₁ h₀₂ hmeet
  · intro ψ
    exact ⟨0, Subsingleton.elim _ _⟩
  · change IsUnit (0 : ZMod 1)
    rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _]
    exact isUnit_one

/-- A nontrivial unit with nilpotent part in the characteristic-two dual-number ring. -/
def dualNumberUnit : (DualNumber (ZMod 2))ˣ :=
  ⟨1 + DualNumber.eps, 1 - DualNumber.eps,
    by simp [add_mul, mul_sub, DualNumber.eps_mul_eps],
    by simp [sub_mul, mul_add, DualNumber.eps_mul_eps]⟩

/-- The nilpotent part makes the scalar unit different from one. -/
theorem dualNumberUnit_ne_one : (dualNumberUnit : DualNumber (ZMod 2)) ≠ 1 := by
  intro he
  have hs := congrArg TrivSqZeroExt.snd he
  simp [dualNumberUnit] at hs

/-- A unit-supported functional over the characteristic-two dual-number ring. -/
def dualNumberFunctional :
    Module.Dual (DualNumber (ZMod 2)) (Hyperplane (ZMod 2) 2 →₀ DualNumber (ZMod 2)) :=
  (dualNumberUnit : DualNumber (ZMod 2)) • Finsupp.lapply axis

/-- The dual-number coefficient ring has a genuinely nonzero square-zero element. -/
theorem binary_dual_number_nilpotent :
    (DualNumber.eps : DualNumber (ZMod 2)) ≠ 0 ∧
      (DualNumber.eps : DualNumber (ZMod 2)) ^ 2 = 0 := by
  constructor
  · intro he
    have hs := congrArg TrivSqZeroExt.snd he
    simp at hs
  · exact DualNumber.eps_pow_two

/-- Detection works over characteristic-two dual numbers with a nonzero nilpotent scalar part,
recovering the unique actual graph/unit pair and its actual global-Q centralizer. -/
theorem binary_dual_number_detection :
    ∃! p : Hyperplane (ZMod 2) 2 × (DualNumber (ZMod 2))ˣ,
      ¬IsVertical (omittedCoordinates 1) p.1 ∧
        dualNumberFunctional =
          (p.2 : DualNumber (ZMod 2)) • Finsupp.lapply p.1 ∧
        centralizer (universalQuadraticRelationSpan (DualNumber (ZMod 2)))
            dualNumberFunctional =
          decomposition (DualNumber (ZMod 2)) p.1 := by
  have hc := (local_detection_iff (DualNumber (ZMod 2)) (by decide) _ 1
    (mem_omittedCoordinates 1) _).mp
      ⟨axis, dualNumberUnit, not_isVertical_graphHyperplane 1 _, rfl⟩
  exact existsUnique_unit_delta_of_local_detection (DualNumber (ZMod 2)) (by decide) _ 1
    (mem_omittedCoordinates 1) _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- The point at the specified value on the affine line over `𝔽₃`. -/
def ternaryPoint (a : ZMod 3) : Hyperplane (ZMod 3) 1 :=
  graphHyperplane 0 (AffineMap.const _ _ a)

/-- Distinct scalar values give distinct actual geometric point labels. -/
theorem ternaryPoint_injective : Function.Injective ternaryPoint := by
  intro a b he
  have hf := graphSubspace_injective (0 : Fin 1) (congrArg Subtype.val he)
  exact DFunLike.congr_fun hf 0

/-- A genuinely two-supported functional on the actual hyperplanes in dimension one. -/
def dimensionOneFunctional : Module.Dual (ZMod 2) (Hyperplane (ZMod 3) 1 →₀ ZMod 2) :=
  Finsupp.lapply (ternaryPoint 0) + Finsupp.lapply (ternaryPoint 1)

private theorem dimensionOneFunctional_at_zero :
    dualCoordinates dimensionOneFunctional (ternaryPoint 0) = 1 := by
  have hne : ternaryPoint 0 ≠ ternaryPoint 1 :=
    fun he ↦ (by decide : (0 : ZMod 3) ≠ 1) (ternaryPoint_injective he)
  simp [dimensionOneFunctional, hne]

private theorem dimensionOneFunctional_at_one :
    dualCoordinates dimensionOneFunctional (ternaryPoint 1) = 1 := by
  have hne : ternaryPoint 1 ≠ ternaryPoint 0 :=
    fun he ↦ (by decide : (1 : ZMod 3) ≠ 0) (ternaryPoint_injective he)
  simp [dimensionOneFunctional, hne]

private theorem dimensionOneFunctional_at_two :
    dualCoordinates dimensionOneFunctional (ternaryPoint 2) = 0 := by
  have hn₀ : ternaryPoint 2 ≠ ternaryPoint 0 :=
    fun he ↦ (by decide : (2 : ZMod 3) ≠ 0) (ternaryPoint_injective he)
  have hn₁ : ternaryPoint 2 ≠ ternaryPoint 1 :=
    fun he ↦ (by decide : (2 : ZMod 3) ≠ 1) (ternaryPoint_injective he)
  simp [dimensionOneFunctional, hn₀, hn₁]

/-- Dimension one cannot be admitted in L05: this actual two-supported functional is primitive,
vanishes vertically and at a graph coordinate, and its actual centralizer restriction is onto,
but it is no unit-supported graph delta. The target is the actual vertical-module dual. -/
theorem dimension_one_counterexample :
    (Primitive dimensionOneFunctional ∧
      verticalRestriction (ZMod 2) (omittedCoordinates (0 : Fin 1)) dimensionOneFunctional = 0 ∧
      (∃ H' : Hyperplane (ZMod 3) 1,
        ¬IsVertical (omittedCoordinates (0 : Fin 1)) H' ∧
          dualCoordinates dimensionOneFunctional H' = 0) ∧
      Function.Surjective (centralizerVerticalRestriction (ZMod 2)
        (omittedCoordinates (0 : Fin 1)) dimensionOneFunctional)) ∧
    ¬∃ (H : Hyperplane (ZMod 3) 1) (u : (ZMod 2)ˣ),
      ¬IsVertical (omittedCoordinates (0 : Fin 1)) H ∧
        dimensionOneFunctional = (u : ZMod 2) • Finsupp.lapply H := by
  constructor
  · have hz : omittedCoordinates (0 : Fin 1) = ∅ := by decide
    rw [hz]
    refine ⟨?_, ?_, ⟨ternaryPoint 2, not_isVertical_empty _,
      dimensionOneFunctional_at_two⟩, ?_⟩
    · apply primitive_of_isUnit_coordinate _ (ternaryPoint 0)
      change IsUnit (dualCoordinates dimensionOneFunctional (ternaryPoint 0))
      rw [dimensionOneFunctional_at_zero]
      exact isUnit_one
    · rw [verticalRestriction_eq_zero_iff]
      intro K hK
      exact (not_isVertical_empty K hK).elim
    · intro ψ
      refine ⟨0, ?_⟩
      ext x
      have hx : x = 0 := by
        apply Subtype.ext
        exact (le_of_eq (verticalModule_empty (k := ZMod 3) (ZMod 2))) x.property
      rw [hx]
      simp
  · rintro ⟨H, u, -, he⟩
    by_cases hH : H = ternaryPoint 0
    · subst H
      have hv := congrArg (fun φ : Module.Dual (ZMod 2) (Hyperplane (ZMod 3) 1 →₀ ZMod 2) ↦
        dualCoordinates φ (ternaryPoint 1)) he
      rw [dimensionOneFunctional_at_one] at hv
      have hn : ternaryPoint 1 ≠ ternaryPoint 0 :=
        fun he ↦ (by decide : (1 : ZMod 3) ≠ 0) (ternaryPoint_injective he)
      simp [hn] at hv
    · have hv := congrArg (fun φ : Module.Dual (ZMod 2) (Hyperplane (ZMod 3) 1 →₀ ZMod 2) ↦
        dualCoordinates φ (ternaryPoint 0)) he
      rw [dimensionOneFunctional_at_zero] at hv
      simp [hH] at hv

end OrlikSolomon.HyperplaneGT.LocalExamples
