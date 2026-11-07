/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Corollaries
public import OrlikSolomon.Examples.Cokernel
public import OrlikSolomon.Examples.Presentation

/-!
# Regressions for the de Rham corollaries

These check the statements of `DeRham/Corollaries` on small arrangements, by computing with them
and not by unfolding them. Nothing here mentions the de Rham instance or its coefficient `t`.

* One point of the affine line, whose complement is `𝔾ₘ = Spec k[x, x⁻¹]`: its de Rham cohomology
  is `k ⊕ k [dx/x]`, with `[dx/x] ≠ 0`.
* The two points `0` and `1` of the affine line over `ℚ`: the generators go to `[dx/x]` and
  `[d(x - 1)/(x - 1)]`, which are linearly independent, and whose product is zero because the points
  are disjoint.
* The two points `[0 : 1]` and `[1 : 0]` of the projective line: the difference `e₀ - e₁` goes to
  the nonzero class `[d(x₀/x₁) / (x₀/x₁)]`, which does not change when an equation is rescaled.

Blueprint: `lem:dr-tau`, `cor:dr-affine`, `cor:dr-projective`.
-/

@[expose] public section

noncomputable section

open Module
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra
open OrlikSolomon.PresentationExamples

universe u

namespace OrlikSolomon.DeRham.CorollaryExamples

/-! ### General consequences -/

section General

variable {k : Type u} [Field k] [CharZero k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (𝒜 : Arrangement k V)

/-- The classes `[df_H / f_H]` of the hyperplanes are linearly independent in `H^1_dR(U_𝒜/k)`. -/
theorem linearIndependent_dlogClass :
    LinearIndependent k fun H : 𝒜 ↦ dlogClass k (equationUnit 𝒜 H) := by
  have h := (linearIndependent_generator k 𝒜).map' (affineEquiv 𝒜).toLinearMap
    (LinearMap.ker_eq_bot.2 (affineEquiv 𝒜).injective)
  simpa [Function.comp_def] using h

/-- `H^q_dR(U_𝒜/k) = 0` above the dimension of the ambient space. -/
theorem degree_complement_eq_bot {q : ℕ} (hq : finrank k V < q) :
    Cohomology.degree k (complement 𝒜) q = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := (affineEquiv 𝒜).surjective c
  have hx := affineEquiv_mem_degree_iff.1 hc
  rw [(ordinaryTheory k).degree_eq_bot_of_finrank_lt hq, Submodule.mem_bot] at hx
  rw [hx, map_zero]

end General

/-! ### One point of the affine line -/

section OnePoint

variable {k : Type u} [Field k] [CharZero k]

/-- The unit `x` on the complement of the origin of the affine line. -/
abbrev unitX (k : Type u) [Field k] : (complement (singlePoint k))ˣ :=
  equationUnit (singlePoint k) (singlePointLabel k)

/-- The generator goes to `[dx/x]`, for the equation `x - 0` of the origin. -/
example :
    affineEquiv (singlePoint k) (generator k _ (singlePointLabel k)) =
      dlogClass k (complementUnit (singlePoint k) (AffineMap.id k k - AffineMap.const k k 0)
        (.of_mem (singlePointLabel k).2)) :=
  affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem (singlePointLabel k).2)

/-- `[dx/x] ≠ 0` on the punctured affine line. -/
theorem dlogClass_unitX_ne_zero : dlogClass k (unitX k) ≠ 0 := by
  rw [← affineEquiv_generator, map_ne_zero_iff _ (affineEquiv _).injective]
  exact (linearIndependent_generator k (singlePoint k)).ne_zero _

/-- `H^0_dR(𝔾ₘ/k)` is one-dimensional. -/
theorem finrank_degree_zero_singlePoint :
    finrank k (Cohomology.degree k (complement (singlePoint k)) 0) = 1 := by
  rw [finrank_degree_complement, bettiNumber_zero]

/-- **`H^1_dR(𝔾ₘ/k) = k [dx/x]`**: every class of degree one is a multiple of `[dx/x]`. -/
theorem exists_eq_smul_dlogClass_unitX {c : Cohomology k (complement (singlePoint k))}
    (hc : c ∈ Cohomology.degree k (complement (singlePoint k)) 1) :
    ∃ a : k, a • dlogClass k (unitX k) = c := by
  have h : finrank k (Cohomology.degree k (complement (singlePoint k)) 1) = 1 := by
    rw [finrank_degree_complement, bettiNumber_one, ← fintypeCard_coe, Fintype.card_eq_one_iff]
    exact ⟨singlePointLabel k, fun _ ↦ Subsingleton.elim _ _⟩
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' (K := k)
    (⟨dlogClass k (unitX k), dlogClass_mem_degree _⟩ :
      Cohomology.degree k (complement (singlePoint k)) 1)
    (fun h ↦ dlogClass_unitX_ne_zero (congrArg Subtype.val h))).1 h ⟨c, hc⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- `H^q_dR(𝔾ₘ/k) = 0` for `q ≥ 2`. -/
theorem degree_singlePoint_eq_bot (q : ℕ) :
    Cohomology.degree k (complement (singlePoint k)) (q + 2) = ⊥ :=
  degree_complement_eq_bot _ (by rw [finrank_self]; omega)

end OnePoint

/-! ### Two points of the affine line over `ℚ` -/

section TwoPoints

/-- The unit `x` on the complement of `{0, 1}` in the rational affine line. -/
abbrev unitZero : (complement (twoPoints ℚ))ˣ :=
  complementUnit (twoPoints ℚ) (AffineMap.id ℚ ℚ - AffineMap.const ℚ ℚ 0)
    (.of_mem (zeroPoint ℚ).2)

/-- The unit `x - 1` on the complement of `{0, 1}` in the rational affine line. -/
abbrev unitOne : (complement (twoPoints ℚ))ˣ :=
  complementUnit (twoPoints ℚ) (AffineMap.id ℚ ℚ - AffineMap.const ℚ ℚ 1)
    (.of_mem (onePoint ℚ).2)

/-- `e₀ ↦ [dx/x]`. -/
theorem affineEquiv_zeroPoint :
    affineEquiv (twoPoints ℚ) (generator ℚ _ (zeroPoint ℚ)) = dlogClass ℚ unitZero :=
  affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem (zeroPoint ℚ).2)

/-- `e₁ ↦ [d(x - 1)/(x - 1)]`. -/
theorem affineEquiv_onePoint :
    affineEquiv (twoPoints ℚ) (generator ℚ _ (onePoint ℚ)) = dlogClass ℚ unitOne :=
  affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem (onePoint ℚ).2)

/-- **`[dx/x]` and `[d(x - 1)/(x - 1)]` are linearly independent** over `ℚ`. -/
theorem linearIndependent_unitZero_unitOne :
    LinearIndependent ℚ ![dlogClass ℚ unitZero, dlogClass ℚ unitOne] := by
  rw [← affineEquiv_zeroPoint, ← affineEquiv_onePoint]
  have h := (linearIndependent_generator ℚ (twoPoints ℚ)).comp ![zeroPoint ℚ, onePoint ℚ]
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [zeroPoint_ne_onePoint, zeroPoint_ne_onePoint.symm])
  have h' := h.map' (affineEquiv (twoPoints ℚ)).toLinearMap
    (LinearMap.ker_eq_bot.2 (affineEquiv _).injective)
  convert h' using 1
  ext i
  fin_cases i <;> rfl

/-- The two classes multiply to zero, because the two points are disjoint, as `e₀ e₁ = 0` in the
Orlik–Solomon algebra. -/
theorem dlogClass_unitZero_mul_dlogClass_unitOne :
    dlogClass ℚ unitZero * dlogClass ℚ unitOne = 0 := by
  rw [← affineEquiv_zeroPoint, ← affineEquiv_onePoint, ← map_mul, twoPoints_product, map_zero]

/-- `H^1_dR` of the complement of two points has dimension two. -/
theorem finrank_degree_one_twoPoints :
    finrank ℚ (Cohomology.degree ℚ (complement (twoPoints ℚ)) 1) = 2 := by
  rw [finrank_degree_complement, bettiNumber_one, ← fintypeCard_coe, Fintype.card_eq_nat_card,
    Nat.card_eq_two_iff' (zeroPoint ℚ)]
  refine ⟨onePoint ℚ, zeroPoint_ne_onePoint.symm, fun H hH ↦ ?_⟩
  rcases (mem_twoPoints _).1 H.2 with h | h
  · exact absurd (Subtype.ext h) hH
  · exact Subtype.ext h

end TwoPoints

/-! ### Two points of the projective line -/

section ProjectiveLine

variable {k : Type u} [Field k]

/-- The form `x₀` on `k²`. -/
abbrev formZero (k : Type u) [Field k] : Dual k (Fin 2 → k) := LinearMap.proj 0

/-- The form `x₁` on `k²`. -/
abbrev formOne (k : Type u) [Field k] : Dual k (Fin 2 → k) := LinearMap.proj 1

theorem formZero_ne_zero : formZero k ≠ 0 := fun h ↦
  one_ne_zero (α := k) (by simpa using LinearMap.congr_fun h ![1, 0])

theorem formOne_ne_zero : formOne k ≠ 0 := fun h ↦
  one_ne_zero (α := k) (by simpa using LinearMap.congr_fun h ![0, 1])

open scoped Classical in
/-- The two points `x₀ = 0` and `x₁ = 0` of the projective line. Their complement is `𝔾ₘ`. -/
def twoProjectivePoints (k : Type u) [Field k] : ProjectiveArrangement k (Fin 2 → k) :=
  ProjectiveArrangement.ofForms {formZero k, formOne k} <| by
    intro ℓ hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl
    exacts [formZero_ne_zero, formOne_ne_zero]

theorem ker_formZero_mem : LinearMap.ker (formZero k) ∈ twoProjectivePoints k :=
  ProjectiveArrangement.ker_mem_ofForms (by simp)

theorem ker_formOne_mem : LinearMap.ker (formOne k) ∈ twoProjectivePoints k :=
  ProjectiveArrangement.ker_mem_ofForms (by simp)

instance : Nonempty (twoProjectivePoints k) :=
  ⟨⟨_, ker_formZero_mem⟩⟩

theorem ker_formZero_ne_ker_formOne : LinearMap.ker (formZero k) ≠ LinearMap.ker (formOne k) := by
  intro h
  have hm : ![0, 1] ∈ LinearMap.ker (formZero k) := by simp
  rw [h] at hm
  simp at hm

variable [CharZero k]

/-- `e₀ - e₁ ↦ [d(x₀/x₁) / (x₀/x₁)]`, by `simp`. -/
theorem projectiveEquiv_twoProjectivePoints :
    projectiveEquiv (twoProjectivePoints k) (projectiveDifference k _
      ((twoProjectivePoints k).coneHyperplaneEquiv ⟨_, ker_formZero_mem⟩)
      ((twoProjectivePoints k).coneHyperplaneEquiv ⟨_, ker_formOne_mem⟩)) =
      dlogClass k (projectiveRatioUnit ker_formZero_mem ker_formOne_mem) := by
  simp

/-- **`[d(x₀/x₁) / (x₀/x₁)] ≠ 0`** on the complement of two points of the projective line. -/
theorem dlogClass_ratio_ne_zero :
    dlogClass k (projectiveRatioUnit (ker_formZero_mem (k := k)) ker_formOne_mem) ≠ 0 := by
  rw [← projectiveEquiv_twoProjectivePoints, map_ne_zero_iff _ (projectiveEquiv _).injective]
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_projectiveDifference, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  refine ker_formZero_ne_ker_formOne (congrArg Subtype.val
    ((twoProjectivePoints k).coneHyperplaneEquiv.injective
      ((linearIndependent_generator k _).injective h')))

/-- The class does not change when an equation is rescaled: `2 x₀` and `x₀` give the same
`[d(ℓ₀/ℓ₁) / (ℓ₀/ℓ₁)]`, because both are the image of `e₀ - e₁`. -/
theorem dlogClass_ratio_two_smul :
    dlogClass k (projectiveRatioUnit (ℓ := (2 : k) • formZero k)
        (by rw [LinearMap.ker_smul _ _ two_ne_zero]; exact ker_formZero_mem) ker_formOne_mem) =
      dlogClass k (projectiveRatioUnit (ker_formZero_mem (k := k)) ker_formOne_mem) := by
  rw [← projectiveEquiv_twoProjectivePoints,
    projectiveEquiv_difference_of_ker_eq ⟨_, ker_formZero_mem⟩ ⟨_, ker_formOne_mem⟩
      (LinearMap.ker_smul _ _ two_ne_zero) rfl]

/-- `H^1_dR` of the complement of two points of the projective line is one-dimensional. -/
theorem finrank_degree_one_twoProjectivePoints :
    finrank k (Cohomology.degree k (projectiveComplement (twoProjectivePoints k)) 1) = 1 := by
  rw [finrank_degree_projectiveComplement, ProjectiveArrangement.bettiNumber_one]
  classical
  have : (twoProjectivePoints k).card = 2 := by
    simp [ProjectiveArrangement.card, twoProjectivePoints, ProjectiveArrangement.ofForms,
      ker_formZero_ne_ker_formOne]
  rw [this]

end ProjectiveLine

end OrlikSolomon.DeRham.CorollaryExamples
