/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.LowDegrees
public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import OrlikSolomon.Examples.Presentation

/-!
# Consumers of the exact quadratic kernel

These consumers use the actual degree-two quotient and its full kernel equality. They test
empty arrangements, dimension zero, the zero coefficient ring, disjoint points in dimension
one, a concurrent triple in characteristic two, and the empty-intersection triangle.

Blueprint: A02 (`thm:a02`) and the low-degree regressions of M8.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.QuadraticKernelExamples

open Module OSAlgebra CoordinateExamples PresentationExamples

variable {k : Type u} [Field k] (R : Type v) [CommRing R]

/-- No quadratic relations occur in the empty arrangement. -/
theorem empty_kernel {n : ℕ} :
    LinearMap.ker (osExteriorSquareMap R (∅ : Arrangement k (Fin n → k))) = ⊥ := by
  rw [quadraticKernel_eq_span, quadraticRelationSpan]
  simp

/-- Dimension zero creates no hidden nonempty-arrangement hypothesis. -/
theorem dimension_zero_kernel (𝒜 : Arrangement k (Fin 0 → k)) :
    LinearMap.ker (osExteriorSquareMap R 𝒜) = ⊥ := by
  have h𝒜 := Arrangement.eq_empty_of_subsingleton 𝒜
  subst 𝒜
  exact empty_kernel R

/-- The full kernel equality accepts the zero coefficient ring on arbitrary arrangements. -/
theorem zero_coefficients {n : ℕ} (𝒜 : Arrangement k (Fin n → k)) :
    LinearMap.ker (osExteriorSquareMap (ZMod 1) 𝒜) = quadraticRelationSpan (ZMod 1) 𝒜 :=
  quadraticKernel_eq_span (ZMod 1) 𝒜

/-- The wedge of two disjoint points lies in the actual kernel over arbitrary coefficients.
The degree-one boundary remains nonzero when the coefficients are nonzero. -/
theorem two_points_pair :
    osExteriorSquareMap R (twoPoints k)
      (osExteriorPair R (twoPoints k) (zeroPoint k) (onePoint k)) = 0 := by
  have hx : osExteriorPair R (twoPoints k) (zeroPoint k) (onePoint k) ∈
      osQuadraticRelationSpan R (twoPoints k) :=
    Submodule.subset_span (Or.inl ⟨zeroPoint k, onePoint k,
      pointHyperplane_inf_eq_bot zero_ne_one, rfl⟩)
  rw [← osExteriorSquareMap_ker_eq] at hx
  exact hx

/-- The three lines `x = 0`, `y = 0`, `x + y = c`. -/
def threeLines (c : k) : Arrangement k (Fin 2 → k) := by
  classical
  exact Arrangement.ofFinset {(xLine k).val, (yLine k).val, (diagonalLine c).val}

@[simp]
theorem mem_threeLines (c : k) (H : AffineSubspace k (Fin 2 → k)) :
    H ∈ threeLines c ↔ H = (xLine k).val ∨ H = (yLine k).val ∨ H = (diagonalLine c).val := by
  classical
  simp only [threeLines, Arrangement.mem_ofFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl | rfl
    · exact (xLine k).property
    · exact (yLine k).property
    · exact (diagonalLine c).property

/-- The label for the coordinate line `x = 0`. -/
def xLabel (c : k) : threeLines c :=
  ⟨(xLine k).val, (mem_threeLines c _).mpr (Or.inl rfl)⟩

/-- The label for the coordinate line `y = 0`. -/
def yLabel (c : k) : threeLines c :=
  ⟨(yLine k).val, (mem_threeLines c _).mpr (Or.inr (Or.inl rfl))⟩

/-- The label for the diagonal line `x + y = c`. -/
def diagonalLabel (c : k) : threeLines c :=
  ⟨(diagonalLine c).val, (mem_threeLines c _).mpr (Or.inr (Or.inr rfl))⟩

@[simp]
theorem arrangementHyperplane_xLabel (c : k) :
    arrangementHyperplane (threeLines c) (xLabel c) = xLine k := rfl

@[simp]
theorem arrangementHyperplane_yLabel (c : k) :
    arrangementHyperplane (threeLines c) (yLabel c) = yLine k := rfl

@[simp]
theorem arrangementHyperplane_diagonalLabel (c : k) :
    arrangementHyperplane (threeLines c) (diagonalLabel c) = diagonalLine c := rfl

private theorem concurrent_dependent :
    DependentTriple (xLine k) (yLine k) (diagonalLine (0 : k)) :=
  (dependentTriple_iff_trace_eq _ _ _ xLine_ne_yLine
    (xLine_ne_diagonalLine 0) (yLine_ne_diagonalLine 0)).mpr concurrent_traces

/-- The concurrent triple contributes its difference wedge to the full kernel. -/
theorem concurrent_difference_pair :
    osExteriorSquareMap R (threeLines (0 : k))
      (osExteriorDifferencePair R (threeLines (0 : k)) (xLabel 0) (yLabel 0)
        (diagonalLabel 0)) = 0 := by
  have hx := osExteriorDifferencePair_mem_quadraticRelationSpan R (threeLines (0 : k))
    (xLabel 0) (yLabel 0) (diagonalLabel 0) (by simpa using concurrent_dependent (k := k))
  rw [← quadraticKernel_eq_span] at hx
  exact hx

/-- Over characteristic-two coefficients the actual triple relation is the unsigned sum of its
three pair wedges; no division by two or alternating-sign cancellation is assumed. -/
theorem concurrent_char_two :
    osExteriorSquareMap (ZMod 2) (threeLines (0 : ZMod 2))
      (osExteriorPair (ZMod 2) (threeLines (0 : ZMod 2)) (xLabel 0) (yLabel 0) +
        osExteriorPair (ZMod 2) (threeLines (0 : ZMod 2)) (xLabel 0) (diagonalLabel 0) +
        osExteriorPair (ZMod 2) (threeLines (0 : ZMod 2)) (yLabel 0) (diagonalLabel 0)) = 0 := by
  have hneg (x : ⋀[ZMod 2]^2 (threeLines (0 : ZMod 2) →₀ ZMod 2)) : -x = x := by
    rw [← neg_one_smul (ZMod 2) x, show (-1 : ZMod 2) = 1 by decide, one_smul]
  simpa only [osExteriorDifferencePair, sub_eq_add_neg, hneg] using
    concurrent_difference_pair (k := ZMod 2) (ZMod 2)

private theorem threeLines_hyperplane_cases (c : k) (H : threeLines c) :
    arrangementHyperplane (threeLines c) H = xLine k ∨
      arrangementHyperplane (threeLines c) H = yLine k ∨
      arrangementHyperplane (threeLines c) H = diagonalLine c := by
  rcases (mem_threeLines c _).mp H.2 with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

private theorem triangle_no_parallel (H K : threeLines (1 : k)) :
    ¬Parallel (arrangementHyperplane (threeLines (1 : k)) H)
      (arrangementHyperplane (threeLines (1 : k)) K) := by
  rcases threeLines_hyperplane_cases 1 H with hH | hH | hH <;>
    rcases threeLines_hyperplane_cases 1 K with hK | hK | hK <;> rw [hH, hK]
  · exact not_parallel_self _
  · exact not_parallel_axes
  · exact not_parallel_xLine_diagonalLine 1
  · exact (parallel_comm _ _).not.mpr not_parallel_axes
  · exact not_parallel_self _
  · exact not_parallel_yLine_diagonalLine 1
  · exact (parallel_comm _ _).not.mpr (not_parallel_xLine_diagonalLine 1)
  · exact (parallel_comm _ _).not.mpr (not_parallel_yLine_diagonalLine 1)
  · exact not_parallel_self _

private theorem triangle_no_dependent (H K L : threeLines (1 : k)) :
    ¬DependentTriple (arrangementHyperplane (threeLines (1 : k)) H)
      (arrangementHyperplane (threeLines (1 : k)) K)
      (arrangementHyperplane (threeLines (1 : k)) L) := by
  rcases threeLines_hyperplane_cases 1 H with hH | hH | hH <;>
    rcases threeLines_hyperplane_cases 1 K with hK | hK | hK <;>
      rcases threeLines_hyperplane_cases 1 L with hL | hL | hL <;> rw [hH, hK, hL]
  all_goals
    intro hd
    first
    | exact hd.1 rfl
    | exact hd.2.1 rfl
    | exact hd.2.2.1 rfl
    | apply hd.2.2.2.1
      simpa only [inf_assoc, inf_left_comm, inf_comm] using triangle_inter_eq_bot (k := k)

/-- The empty-intersection triangle has no quadratic kernel. In particular its conventional
codimension-two empty intersection does not introduce a dependent-boundary relation. -/
theorem triangle_kernel :
    LinearMap.ker (osExteriorSquareMap R (threeLines (1 : k))) = ⊥ := by
  rw [quadraticKernel_eq_span, quadraticRelationSpan, Submodule.span_eq_bot]
  rintro x (⟨H, K, h, rfl⟩ | ⟨H, K, L, h, rfl⟩)
  · exact (triangle_no_parallel H K h).elim
  · exact (triangle_no_dependent H K L h).elim

end OrlikSolomon.HyperplaneGT.QuadraticKernelExamples
