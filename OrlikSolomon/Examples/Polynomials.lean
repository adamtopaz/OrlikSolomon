/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Field.ZMod
public import OrlikSolomon.Combinatorics.Betti

/-!
# Regression calculations for subset polynomials

The two-point arrangement checks that an empty intersection is discarded before its dimension
is used. Specialization to `𝔽₂` also checks that no point of the complement is required. The
empty arrangement on the zero-dimensional space is included explicitly. Three hyperplanes with
the same nonempty trace exercise the cancellation of duplicate traces in deletion–restriction.
Three pairwise meeting hyperplanes without a common point give three distinct degree-two terms.

Blueprint: the paragraph "Required mathematical regression examples".
-/

@[expose] public section

open Module Polynomial

namespace OrlikSolomon.Examples

universe u

variable {k : Type u} [Field k]

private theorem isHyperplane_singleton (c : k) : IsHyperplane ({c} : AffineSubspace k k) := by
  rw [isHyperplane_iff_finrank_direction_add_one]
  constructor
  · exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨c, by simp⟩
  · rw [AffineSubspace.direction_singleton]
    simp

/-- The arrangement of two specified rational points of the affine line, with coincident points
identified. -/
noncomputable def twoPoints (a b : k) : Arrangement k k :=
  open scoped Classical in
  { hyperplanes := {({a} : AffineSubspace k k), {b}}
    isHyperplane_of_mem' := by
      intro H hH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact isHyperplane_singleton a
      · exact isHyperplane_singleton b }

private theorem singleton_inf_singleton {a b : k} (hab : a ≠ b) :
    ({a} : AffineSubspace k k) ⊓ {b} = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  simp only [AffineSubspace.mem_inf_iff, AffineSubspace.mem_singleton_iff] at hx
  exact (hab (hx.1.symm.trans hx.2)).elim

/-- Two distinct points have Poincaré polynomial `1 + 2 X`, over any field. In particular the
empty intersection contributes no degree-two term. -/
theorem poincarePolynomial_twoPoints {a b : k} (hab : a ≠ b) :
    (twoPoints a b).poincarePolynomial = 1 + 2 * Polynomial.X := by
  apply Arrangement.poincarePolynomial_pair_disjoint _ _ rfl (singleton_inf_singleton hab)
  exact fun h => hab ((AffineSubspace.singleton_eq_singleton_iff _ _).1 h)

/-- Deleting one of two distinct points leaves one point and an empty restriction. This verifies
the recursion when the other point has an empty trace on the deleted hyperplane. -/
theorem poincarePolynomial_twoPoints_via_deletion_restriction {a b : k} (hab : a ≠ b) :
    (twoPoints a b).poincarePolynomial = 1 + 2 * Polynomial.X := by
  classical
  have hne : ({a} : AffineSubspace k k) ≠ {b} :=
    fun h => hab ((AffineSubspace.singleton_eq_singleton_iff _ _).1 h)
  have hmem : ({a} : AffineSubspace k k) ∈ twoPoints a b := by
    change ({a} : AffineSubspace k k) ∈ ({({a} : AffineSubspace k k), {b}} : Finset _)
    simp
  have hdel : ((twoPoints a b).deletion {a}).hyperplanes = {{b}} := by
    rw [Arrangement.hyperplanes_deletion]
    change ({({a} : AffineSubspace k k), {b}} : Finset _).erase {a} = _
    simp [hne]
  have htrace : ({b} : AffineSubspace k k).comap (chart ({a} : AffineSubspace k k)) = ⊥ :=
    (comap_chart_eq_bot_iff (isHyperplane_singleton a).ne_bot).2
      (singleton_inf_singleton hab)
  have hres : (twoPoints a b).restriction {a} = ∅ := by
    apply Arrangement.ext
    intro L
    rw [← Arrangement.mem_hyperplanes,
      Arrangement.hyperplanes_restriction_eq_erase_image _ (isHyperplane_singleton a), hdel]
    simp [htrace]
  rw [Arrangement.poincarePolynomial_deletion_restriction _ hmem,
    Arrangement.poincarePolynomial_singleton _ hdel, hres,
    Arrangement.poincarePolynomial_empty]
  ring

/-- The characteristic polynomial of two distinct points is `X - 2`. -/
theorem characteristicPolynomial_twoPoints {a b : k} (hab : a ≠ b) :
    (twoPoints a b).characteristicPolynomial = Polynomial.X - 2 := by
  have hne : ({a} : AffineSubspace k k) ≠ {b} :=
    fun h => hab ((AffineSubspace.singleton_eq_singleton_iff _ _).1 h)
  rw [Arrangement.characteristicPolynomial,
    Arrangement.intersectionSum_pair _ hne rfl, singleton_inf_singleton hab]
  rw [Arrangement.characteristicWeight_bot, add_zero,
    Arrangement.characteristicWeight_of_ne_bot top_ne_bot,
    Arrangement.characteristicWeight_of_ne_bot (isHyperplane_singleton a).ne_bot,
    Arrangement.characteristicWeight_of_ne_bot (isHyperplane_singleton b).ne_bot]
  rw [AffineSubspace.direction_top, AffineSubspace.direction_singleton,
    AffineSubspace.direction_singleton]
  simp only [finrank_top, Module.finrank_self, finrank_bot, pow_one, pow_zero]
  ring

/-- The two rational points of `𝔽₂` retain two degree-one contributions. -/
theorem poincarePolynomial_twoPoints_zmod_two :
    (twoPoints (0 : ZMod 2) 1).poincarePolynomial = 1 + 2 * Polynomial.X :=
  poincarePolynomial_twoPoints zero_ne_one

/-- The characteristic polynomial calculation remains valid over `𝔽₂`. -/
theorem characteristicPolynomial_twoPoints_zmod_two :
    (twoPoints (0 : ZMod 2) 1).characteristicPolynomial = Polynomial.X - 2 :=
  characteristicPolynomial_twoPoints zero_ne_one

/-- There are no hyperplanes in the zero-dimensional vector space, and its empty-arrangement
Poincaré polynomial is one. -/
theorem poincarePolynomial_dimension_zero (𝒜 : Arrangement k (Fin 0 → k)) :
    𝒜.poincarePolynomial = 1 := by
  rw [𝒜.eq_empty_of_subsingleton, Arrangement.poincarePolynomial_empty]

open scoped Classical in
/-- Three distinct hyperplanes with the same nonempty trace on one of them have polynomial
`1 + 3 X + 2 X²`. For concurrent lines, the two traces in the restriction must count only once. -/
theorem poincarePolynomial_three_same_trace {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (𝒜 : Arrangement k V) {H K L : AffineSubspace k V}
    (h𝒜 : 𝒜.hyperplanes = {H, K, L}) (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L)
    (htrace : H ⊓ K = H ⊓ L) (hbot : H ⊓ K ≠ ⊥) :
    𝒜.poincarePolynomial = 1 + 3 * Polynomial.X + 2 * Polynomial.X ^ 2 := by
  classical
  have hHmem : H ∈ 𝒜 := by rw [← Arrangement.mem_hyperplanes, h𝒜]; simp
  have hH := 𝒜.isHyperplane hHmem
  have hdel : (𝒜.deletion H).hyperplanes = {K, L} := by
    rw [Arrangement.hyperplanes_deletion, h𝒜]
    simp [hHK, hHL]
  have hmap : K.comap (chart H) = L.comap (chart H) :=
    (comap_chart_eq_comap_chart_iff hH.ne_bot).2 htrace
  have hnonempty : L.comap (chart H) ≠ ⊥ := by
    rw [← hmap]
    exact (comap_chart_eq_bot_iff hH.ne_bot).not.mpr hbot
  have hres : (𝒜.restriction H).hyperplanes = {K.comap (chart H)} := by
    rw [𝒜.hyperplanes_restriction_eq_erase_image hH, hdel]
    simp [hmap, Ne.symm hnonempty]
  have hcommon : H ⊓ K ≤ K ⊓ L := by
    refine le_inf inf_le_right ?_
    rw [htrace]
    exact inf_le_right
  have hKLbot : K ⊓ L ≠ ⊥ := by
    intro h
    rw [h] at hcommon
    exact hbot (le_bot_iff.mp hcommon)
  rw [𝒜.poincarePolynomial_deletion_restriction hHmem,
    Arrangement.poincarePolynomial_pair_meeting _ hKL hdel hKLbot,
    Arrangement.poincarePolynomial_singleton _ hres]
  ring

open scoped Classical in
/-- Three pairwise meeting hyperplanes with empty triple intersection have polynomial
`1 + 3 X + 3 X²`. Their two traces on a chosen hyperplane are distinct and disjoint. -/
theorem poincarePolynomial_three_nonconcurrent {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (𝒜 : Arrangement k V) {H K L : AffineSubspace k V}
    (h𝒜 : 𝒜.hyperplanes = {H, K, L}) (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L)
    (hHKbot : H ⊓ K ≠ ⊥) (hHLbot : H ⊓ L ≠ ⊥) (hKLbot : K ⊓ L ≠ ⊥)
    (htriple : H ⊓ (K ⊓ L) = ⊥) :
    𝒜.poincarePolynomial = 1 + 3 * Polynomial.X + 3 * Polynomial.X ^ 2 := by
  classical
  have hHmem : H ∈ 𝒜 := by rw [← Arrangement.mem_hyperplanes, h𝒜]; simp
  have hH := 𝒜.isHyperplane hHmem
  have hdel : (𝒜.deletion H).hyperplanes = {K, L} := by
    rw [Arrangement.hyperplanes_deletion, h𝒜]
    simp [hHK, hHL]
  have hKbot : K.comap (chart H) ≠ ⊥ :=
    (comap_chart_eq_bot_iff hH.ne_bot).not.mpr hHKbot
  have hLbot : L.comap (chart H) ≠ ⊥ :=
    (comap_chart_eq_bot_iff hH.ne_bot).not.mpr hHLbot
  have hdisjoint : K.comap (chart H) ⊓ L.comap (chart H) = ⊥ := by
    rw [← AffineSubspace.comap_inf]
    exact (comap_chart_eq_bot_iff hH.ne_bot).2 htriple
  have hne : K.comap (chart H) ≠ L.comap (chart H) := by
    intro h
    rw [h, inf_idem] at hdisjoint
    exact hLbot hdisjoint
  have hres : (𝒜.restriction H).hyperplanes = {K.comap (chart H), L.comap (chart H)} := by
    rw [𝒜.hyperplanes_restriction_eq_erase_image hH, hdel]
    simp [Ne.symm hKbot, Ne.symm hLbot]
  rw [𝒜.poincarePolynomial_deletion_restriction hHmem,
    Arrangement.poincarePolynomial_pair_meeting _ hKL hdel hKLbot,
    Arrangement.poincarePolynomial_pair_disjoint _ hne hres hdisjoint]
  ring

end OrlikSolomon.Examples
