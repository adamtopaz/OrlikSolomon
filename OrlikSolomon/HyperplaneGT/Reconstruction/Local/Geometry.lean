/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates

/-!
# Graph witnesses for local transfer and detection

A nonvertical hyperplane has another graph parallel to it, obtained by adding one to its
graph function. In dimension at least two, changing the graph function by a remaining
coordinate also gives a distinct graph that meets it. The vertical hyperplanes defined by
differences of graph functions supply the guarded dependent triples used in local transfer.

The geometric field is arbitrary. There is no coefficient ring, cohomology theory, Galois
hypothesis or rational point of a complement. Blueprint: the geometric steps in L04–L05
(`lem:l04`, `thm:l05`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- Every graph has a distinct parallel graph, including in characteristic two and dimension
one. Blueprint: the parallel graph witnesses in L04–L05. -/
theorem exists_parallel_graph (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n)
    (hH : ¬IsVertical z H) :
    ∃ K : Hyperplane k n, ¬IsVertical z K ∧ Parallel H K := by
  obtain rfl := eq_omittedCoordinates z i hzi
  obtain ⟨h, hh, -⟩ := existsUnique_graph_of_not_isVertical i H hH
  have heq : graphHyperplane i h = H := Subtype.ext hh
  subst H
  refine ⟨graphHyperplane i (h + AffineMap.const k _ 1),
    not_isVertical_graphHyperplane _ _, ?_⟩
  exact parallel_graphHyperplane_of_sub_eq_const i (c := 1) one_ne_zero (by simp)

/-- In dimension at least two every graph has a distinct graph that meets it. A genuine
remaining coordinate gives a nonconstant difference. Blueprint: the meeting graph in L05. -/
theorem exists_meeting_graph (hn : 2 ≤ n)
    (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n)
    (hH : ¬IsVertical z H) :
    ∃ K : Hyperplane k n,
      ¬IsVertical z K ∧ H ≠ K ∧ H.val ⊓ K.val ≠ ⊥ := by
  classical
  obtain rfl := eq_omittedCoordinates z i hzi
  obtain ⟨h, hh, -⟩ := existsUnique_graph_of_not_isVertical i H hH
  have heq : graphHyperplane i h = H := Subtype.ext hh
  subst H
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  let a : omittedCoordinates i := ⟨j, (mem_omittedCoordinates i j).mpr hji⟩
  let g := h + (LinearMap.proj a : (omittedCoordinates i → k) →ₗ[k] k).toAffineMap
  have hdiff : g - h = (LinearMap.proj a : (omittedCoordinates i → k) →ₗ[k] k).toAffineMap := by
    simp [g]
  have hlin : (g - h).linear ≠ 0 := by
    rw [hdiff]
    change (LinearMap.proj a : (omittedCoordinates i → k) →ₗ[k] k) ≠ 0
    intro hz
    have hv := LinearMap.congr_fun hz (Pi.single a (1 : k))
    simp at hv
  refine ⟨graphHyperplane i g, not_isVertical_graphHyperplane _ _, ?_,
    graphSubspace_inf_ne_bot_of_sub_linear_ne_zero i hlin⟩
  intro heq
  have hfun := graphSubspace_injective i (congrArg Subtype.val heq)
  apply hlin
  rw [← hfun, sub_self]
  rfl

private theorem meets_of_parallel_of_meets {H₀ H₁ H₂ : Hyperplane k n}
    (h₀₁ : Parallel H₀ H₁) (h₀₂ : H₀ ≠ H₂) (hmeet : H₀.val ⊓ H₂.val ≠ ⊥) :
    H₁ ≠ H₂ ∧ H₁.val ⊓ H₂.val ≠ ⊥ := by
  have h₁₂ : H₁ ≠ H₂ := by
    intro heq
    exact hmeet (heq ▸ h₀₁.2)
  refine ⟨h₁₂, ?_⟩
  intro hbot
  have hd₀₁ := (inf_eq_bot_iff_direction_eq H₀ H₁ h₀₁.1).mp h₀₁.2
  have hd₁₂ := (inf_eq_bot_iff_direction_eq H₁ H₂ h₁₂).mp hbot
  exact hmeet ((inf_eq_bot_iff_direction_eq H₀ H₂ h₀₂).mpr (hd₀₁.trans hd₁₂))

private theorem graph_difference_linear_ne_zero (i : Fin n)
    {h₀ h₂ : (omittedCoordinates i → k) →ᵃ[k] k}
    (hne : graphHyperplane i h₀ ≠ graphHyperplane i h₂)
    (hmeet : graphSubspace i h₀ ⊓ graphSubspace i h₂ ≠ ⊥) :
    (h₂ - h₀).linear ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := (AffineMap.linear_eq_zero_iff_exists_const _).mp hz
  by_cases hc₀ : c = 0
  · have hf : h₂ = h₀ := sub_eq_zero.mp (hc.trans (by ext x; simp [hc₀]))
    exact hne (congrArg (graphHyperplane i) hf.symm)
  · exact hmeet (graphSubspace_inf_eq_bot_of_sub_eq_const i hc₀ hc)

private theorem comp_projection_linear_ne_zero (i : Fin n)
    (f : (omittedCoordinates i → k) →ᵃ[k] k) (hf : f.linear ≠ 0) :
    (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).linear ≠ 0 := by
  have hcomp : (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).comp
      (coordinateSection i).toAffineMap = f := by
    ext x
    simp
  intro hz
  apply hf
  have he := congrArg AffineMap.linear hcomp
  change (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).linear.comp
    (coordinateSection i) = f.linear at he
  rw [hz, LinearMap.zero_comp] at he
  exact he.symm

private def verticalDifference (i : Fin n)
    (h₀ h₂ : (omittedCoordinates i → k) →ᵃ[k] k) (hf : (h₂ - h₀).linear ≠ 0) :
    Hyperplane k n :=
  ⟨zeroLocus ((h₂ - h₀).comp (coordinateProjection (omittedCoordinates i)).toAffineMap),
    isHyperplane_zeroLocus_iff.mpr (comp_projection_linear_ne_zero i _ hf)⟩

private theorem mem_verticalDifference (i : Fin n)
    (h₀ h₂ : (omittedCoordinates i → k) →ᵃ[k] k) (hf : (h₂ - h₀).linear ≠ 0)
    (x : Fin n → k) :
    x ∈ (verticalDifference i h₀ h₂ hf).val ↔
      h₂ (coordinateProjection (omittedCoordinates i) x) =
        h₀ (coordinateProjection (omittedCoordinates i) x) := by
  simp [verticalDifference, sub_eq_zero]

private theorem isVertical_verticalDifference (i : Fin n)
    (h₀ h₂ : (omittedCoordinates i → k) →ᵃ[k] k) (hf : (h₂ - h₀).linear ≠ 0) :
    IsVertical (omittedCoordinates i) (verticalDifference i h₀ h₂ hf) := by
  rw [isVertical_iff_of_isEquation _ _
    (isEquation_zeroLocus (comp_projection_linear_ne_zero i _ hf))]
  intro j hj
  have hji : j = i := by simpa using hj
  subst j
  have hz : coordinateProjection (omittedCoordinates i) (Pi.single i (1 : k)) = 0 := by
    ext j
    simp [(mem_omittedCoordinates i j.val).mp j.property]
  rw [affineCoefficients_succ]
  change (h₂ - h₀).linear (coordinateProjection (omittedCoordinates i) (Pi.single i 1)) = 0
  rw [hz, map_zero]

private theorem dependentTriple_graph_verticalDifference (i : Fin n)
    (h₀ h₂ : (omittedCoordinates i → k) →ᵃ[k] k)
    (hne : graphHyperplane i h₀ ≠ graphHyperplane i h₂)
    (hmeet : graphSubspace i h₀ ⊓ graphSubspace i h₂ ≠ ⊥)
    (hf : (h₂ - h₀).linear ≠ 0) :
    DependentTriple (graphHyperplane i h₀) (graphHyperplane i h₂)
      (verticalDifference i h₀ h₂ hf) := by
  have hv := isVertical_verticalDifference i h₀ h₂ hf
  have h₀v : graphHyperplane i h₀ ≠ verticalDifference i h₀ h₂ hf := by
    intro he
    exact not_isVertical_graphHyperplane i h₀ (he.symm ▸ hv)
  have h₂v : graphHyperplane i h₂ ≠ verticalDifference i h₀ h₂ hf := by
    intro he
    exact not_isVertical_graphHyperplane i h₂ (he.symm ▸ hv)
  apply (dependentTriple_iff_trace_eq _ _ _ hne h₀v h₂v).mpr
  refine ⟨hmeet, ?_⟩
  ext x
  simp only [AffineSubspace.mem_inf_iff, coe_graphHyperplane, mem_graphSubspace,
    mem_verticalDifference]
  constructor
  · rintro ⟨hx₀, hx₂⟩
    exact ⟨hx₀, hx₂.symm.trans hx₀⟩
  · rintro ⟨hx₀, hx₂⟩
    exact ⟨hx₀, hx₀.trans hx₂.symm⟩

/-- Three graphs in the transfer configuration give two distinct actual vertical hyperplanes
and the two guarded dependent triples. Nonempty intersections and all inequality guards are
proved, rather than assumed as additional diagram data. Blueprint: the witnesses in L04. -/
theorem exists_vertical_transfer_pair
    (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H₀ H₁ H₂ : Hyperplane k n)
    (h₀ : ¬IsVertical z H₀) (h₁ : ¬IsVertical z H₁) (h₂ : ¬IsVertical z H₂)
    (h₀₁ : Parallel H₀ H₁) (h₀₂ : H₀ ≠ H₂) (hmeet : H₀.val ⊓ H₂.val ≠ ⊥) :
    ∃ V₁ V₂ : Hyperplane k n,
      IsVertical z V₁ ∧ IsVertical z V₂ ∧ V₁ ≠ V₂ ∧
      DependentTriple H₀ H₂ V₁ ∧ DependentTriple H₁ H₂ V₂ := by
  obtain rfl := eq_omittedCoordinates z i hzi
  obtain ⟨h₀f, hh₀, -⟩ := existsUnique_graph_of_not_isVertical i H₀ h₀
  obtain ⟨h₁f, hh₁, -⟩ := existsUnique_graph_of_not_isVertical i H₁ h₁
  obtain ⟨h₂f, hh₂, -⟩ := existsUnique_graph_of_not_isVertical i H₂ h₂
  have he₀ : graphHyperplane i h₀f = H₀ := Subtype.ext hh₀
  have he₁ : graphHyperplane i h₁f = H₁ := Subtype.ext hh₁
  have he₂ : graphHyperplane i h₂f = H₂ := Subtype.ext hh₂
  subst H₀ H₁ H₂
  obtain ⟨h₁₂, hmeet₁₂⟩ := meets_of_parallel_of_meets h₀₁ h₀₂ hmeet
  have hf₁ := graph_difference_linear_ne_zero i h₀₂ hmeet
  have hf₂ := graph_difference_linear_ne_zero i h₁₂ hmeet₁₂
  let V₁ := verticalDifference i h₀f h₂f hf₁
  let V₂ := verticalDifference i h₁f h₂f hf₂
  refine ⟨V₁, V₂, isVertical_verticalDifference i _ _ _,
    isVertical_verticalDifference i _ _ _, ?_,
    dependentTriple_graph_verticalDifference i _ _ h₀₂ hmeet hf₁,
    dependentTriple_graph_verticalDifference i _ _ h₁₂ hmeet₁₂ hf₂⟩
  intro heq
  obtain ⟨x, hx⟩ := V₁.property.nonempty
  have hx₂ : x ∈ V₂.val := heq ▸ hx
  have hx₁ := (mem_verticalDifference i h₀f h₂f hf₁ x).mp hx
  have hx₂' := (mem_verticalDifference i h₁f h₂f hf₂ x).mp hx₂
  let y := graphParam i h₀f (coordinateProjection (omittedCoordinates i) x)
  have hy₀ : y ∈ graphSubspace i h₀f := graphParam_mem i h₀f _
  have hy₁ : y ∈ graphSubspace i h₁f := by
    simp only [y, mem_graphSubspace, graphParam_apply, coordinateSplit_symm_apply_self,
      coordinateProjection_coordinateSplit_symm]
    exact hx₁.symm.trans hx₂'
  have hy : y ∈ (graphHyperplane i h₀f).val ⊓ (graphHyperplane i h₁f).val := ⟨hy₀, hy₁⟩
  rw [h₀₁.2] at hy
  exact AffineSubspace.notMem_bot k _ _ hy

end OrlikSolomon.HyperplaneGT
