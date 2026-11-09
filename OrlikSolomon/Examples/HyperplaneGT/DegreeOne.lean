/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.DegreeOne
public import OrlikSolomon.Examples.Presentation

/-!
# Consumers of canonical degree-one coordinates

These consumers use the public A01 equivalence and its basis and naturality formulas. They
cover the empty arrangement, dimension zero, characteristic-two coefficients on a punctured
line, zero coefficients, and the vanishing of new coordinates under an arrangement inclusion.

Blueprint: A01 (`lem:a01`) and the low-degree regression requirements of M8.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.DegreeOneExamples

open Module OSAlgebra PresentationExamples

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (R : Type v) [CommRing R]

/-- The empty arrangement has zero degree one over every coefficient ring. -/
theorem empty_degree_one [FiniteDimensional k V]
    (x : degree R (∅ : Arrangement k V) 1) : x = 0 := by
  apply (osDegreeOneEquiv R (∅ : Arrangement k V)).symm.injective
  exact Subsingleton.elim _ _

/-- There are no degree-one classes in an arrangement on the zero-dimensional coordinate space.
-/
theorem dimension_zero (𝒜 : Arrangement k (Fin 0 → k)) (x : degree R 𝒜 1) : x = 0 := by
  have h𝒜 := Arrangement.eq_empty_of_subsingleton 𝒜
  subst 𝒜
  exact empty_degree_one R x

/-- The two logarithmic labels on a punctured line have independent coordinates even in
characteristic two, although their product vanishes in the OS algebra. -/
theorem two_points_coordinates :
    (osDegreeOneEquiv (ZMod 2) (twoPoints k)).symm
      (osDegreeOneBasis (ZMod 2) (twoPoints k) (onePoint k) -
        osDegreeOneBasis (ZMod 2) (twoPoints k) (zeroPoint k)) =
      Finsupp.single (onePoint k) 1 - Finsupp.single (zeroPoint k) 1 := by
  simp

/-- A nonempty arrangement still admits its labelled degree-one basis over the zero ring. -/
theorem zero_coefficient_basis :
    Nonempty (Basis (twoPoints k) (ZMod 1) (degree (ZMod 1) (twoPoints k) 1)) :=
  ⟨osDegreeOneBasis (ZMod 1) (twoPoints k)⟩

/-- After including an arrangement, every newly added hyperplane has coefficient zero on the
image of the old degree-one piece. -/
theorem new_coordinate_eq_zero [FiniteDimensional k V] {𝒜 ℬ : Arrangement k V}
    (h : 𝒜 ≤ ℬ) (K : ℬ) (hK : (K : AffineSubspace k V) ∉ 𝒜) (x : degree R 𝒜 1) :
    (osDegreeOneEquiv R ℬ).symm (osDegreeOneMap R h x) K = 0 := by
  rw [osDegreeOneEquiv_symm_map]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨H, hH⟩
  exact hK (congrArg Subtype.val hH ▸ H.2)

/-- Generation has no ambient finite-dimensionality assumption. -/
example (𝒜 : Arrangement k V) (x : OSAlgebra R 𝒜) :
    ∃ c : List 𝒜 →₀ R, Finsupp.linearCombination R (word (generator R 𝒜)) c = x :=
  exists_os_word_sum R 𝒜 x

end OrlikSolomon.HyperplaneGT.DegreeOneExamples
