/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates
public import Mathlib.Algebra.Field.ZMod

/-!
# Coordinate and incidence regressions

These consumers test the coefficient-point inverse, normalized graph charts, parallel points
in dimension one, and both concurrent and empty-intersection triples over `𝔽₂`. The latter
empty triple still has codimension two by the bottom convention, so its rejection tests the
nonemptiness guard in `DependentTriple`.

Blueprint: `lem:g01`, `lem:g02`, `lem:g03`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.CoordinateExamples

variable {k : Type*} [Field k]

/-- There are no affine hyperplanes in dimension zero. -/
theorem dimension_zero : IsEmpty (Hyperplane k 0) := by
  refine ⟨fun H ↦ ?_⟩
  obtain ⟨i, -⟩ := exists_normal_coefficient_ne_zero_of_isEquation
    (isEquation_equation H.property)
  exact Fin.elim0 i

/-- The inverse of the coefficient-point equivalence is usable through its public computation
and cancellation lemmas. -/
theorem coefficientPoint_inverse {n : ℕ} (p : Projectivization k (Fin (n + 1) → k))
    (hp : p ≠ constantPoint k n) :
    coefficientPoint ((coefficientPointEquiv k n).symm ⟨p, hp⟩) = p := by
  simp

/-- A normalized graph chart and its inverse recover the omitted coordinate without unfolding
the affine equivalence. -/
theorem graph_inverse_coordinate {n : ℕ} (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) (z : omittedCoordinates i → k) :
    ((graphProjectionEquiv i h).symm z).val i = h z := by
  simp

/-- The two points of the affine line are strictly parallel, even over `𝔽₂`. -/
theorem parallel_points :
    Parallel (graphHyperplane (k := ZMod 2) (0 : Fin 1) (AffineMap.const _ _ 0))
      (graphHyperplane (k := ZMod 2) (0 : Fin 1) (AffineMap.const _ _ 1)) := by
  apply parallel_graphHyperplane_of_sub_eq_const (c := 1) _ one_ne_zero
  ext z
  simp

/-- Coordinate splitting also works over the zero coefficient ring, before introducing any
geometric field. -/
theorem zero_ring_coordinate_split {n : ℕ} (i : Fin n) (x : Fin n → ZMod 1) :
    (coordinateSplit i).symm (coordinateSplit i x) = x :=
  (coordinateSplit i).symm_apply_apply x

/-- Two graphs with nonconstant difference meet in characteristic two. -/
theorem nonconstant_graphs_meet :
    graphSubspace (k := ZMod 2) (0 : Fin 2) (AffineMap.const _ _ 0) ⊓
      graphSubspace (k := ZMod 2) (0 : Fin 2)
        (LinearMap.proj (⟨1, by decide⟩ : omittedCoordinates (0 : Fin 2))).toAffineMap ≠ ⊥ := by
  apply graphSubspace_inf_ne_bot_of_sub_linear_ne_zero
  intro h
  have hx := congrArg
    (fun f : (omittedCoordinates (0 : Fin 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2 ↦ f (fun _ ↦ 1)) h
  simp at hx

/-- The coordinate line `x = 0` in the affine plane. -/
def xLine (k : Type*) [Field k] : Hyperplane k 2 :=
  graphHyperplane 0 (AffineMap.const _ _ 0)

/-- The coordinate line `y = 0` in the affine plane. -/
def yLine (k : Type*) [Field k] : Hyperplane k 2 :=
  graphHyperplane 1 (AffineMap.const _ _ 0)

/-- The line `x + y = c`, defined by its explicit coefficient tuple. -/
def diagonalLine (c : k) : Hyperplane k 2 :=
  ⟨zeroLocus (coefficientForm ![-c, 1, 1]), isHyperplane_zeroLocus_iff.mpr
    ((coefficientForm_linear_ne_zero_iff _).mpr ⟨0, by simp⟩)⟩

@[simp]
theorem mem_xLine (x : Fin 2 → k) : x ∈ (xLine k).val ↔ x 0 = 0 := by
  simp [xLine]

@[simp]
theorem mem_yLine (x : Fin 2 → k) : x ∈ (yLine k).val ↔ x 1 = 0 := by
  simp [yLine]

@[simp]
theorem mem_diagonalLine (c : k) (x : Fin 2 → k) :
    x ∈ (diagonalLine c).val ↔ x 0 + x 1 = c := by
  simp [diagonalLine, Fin.sum_univ_two, ← sub_eq_add_neg, add_comm (-c), sub_eq_zero]

/-- The two coordinate axes are distinct. -/
theorem xLine_ne_yLine : xLine k ≠ yLine k := by
  intro h
  have hx : ![0, 1] ∈ (xLine k).val := by simp
  rw [h] at hx
  simp at hx

/-- No line `x + y = c` is the line `x = 0`. -/
theorem xLine_ne_diagonalLine (c : k) : xLine k ≠ diagonalLine c := by
  intro h
  have hx : ![0, c + 1] ∈ (xLine k).val := by simp
  rw [h] at hx
  simp at hx

/-- No line `x + y = c` is the line `y = 0`. -/
theorem yLine_ne_diagonalLine (c : k) : yLine k ≠ diagonalLine c := by
  intro h
  have hy : ![c + 1, 0] ∈ (yLine k).val := by simp
  rw [h] at hy
  simp at hy

/-- The coordinate axes are not parallel: their intersection contains the origin. -/
theorem not_parallel_axes : ¬Parallel (xLine k) (yLine k) := by
  rintro ⟨-, hbot⟩
  have hzero : (0 : Fin 2 → k) ∈ (xLine k).val ⊓ (yLine k).val :=
    ⟨(mem_xLine _).mpr rfl, (mem_yLine _).mpr rfl⟩
  rw [hbot] at hzero
  exact AffineSubspace.notMem_bot k _ _ hzero

/-- Each diagonal line meets the first coordinate line. -/
theorem not_parallel_xLine_diagonalLine (c : k) :
    ¬Parallel (xLine k) (diagonalLine c) := by
  rintro ⟨-, hbot⟩
  have hp : ![0, c] ∈ (xLine k).val ⊓ (diagonalLine c).val := by
    constructor <;> simp
  rw [hbot] at hp
  exact AffineSubspace.notMem_bot k _ _ hp

/-- Each diagonal line meets the second coordinate line. -/
theorem not_parallel_yLine_diagonalLine (c : k) :
    ¬Parallel (yLine k) (diagonalLine c) := by
  rintro ⟨-, hbot⟩
  have hp : ![c, 0] ∈ (yLine k).val ⊓ (diagonalLine c).val := by
    constructor <;> simp
  rw [hbot] at hp
  exact AffineSubspace.notMem_bot k _ _ hp

/-- The three concurrent lines have the same nonempty trace on `x = 0`. -/
theorem concurrent_traces :
    (xLine k).val ⊓ (yLine k).val ≠ ⊥ ∧
      (xLine k).val ⊓ (yLine k).val = (xLine k).val ⊓ (diagonalLine (0 : k)).val := by
  constructor
  · intro hbot
    exact not_parallel_axes ⟨xLine_ne_yLine, hbot⟩
  · ext x
    simp only [AffineSubspace.mem_inf_iff, mem_xLine, mem_yLine, mem_diagonalLine]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by rw [hx, hy, zero_add]⟩
    · rintro ⟨hx, hsum⟩
      exact ⟨hx, by simpa only [hx, zero_add] using hsum⟩

/-- Actual `𝔽₂` coefficient points are collinear for the three concurrent lines. -/
theorem concurrent_coefficientPoints_collinear :
    Projectivization.IsCollinear
      {coefficientPoint (xLine (ZMod 2)), coefficientPoint (yLine (ZMod 2)),
        coefficientPoint (diagonalLine (0 : ZMod 2))} := by
  apply (dependentTriple_iff_coefficientPoints_collinear _ _ _ xLine_ne_yLine
    (xLine_ne_diagonalLine 0) (yLine_ne_diagonalLine 0) not_parallel_axes).mp
  exact (dependentTriple_iff_trace_eq _ _ _ xLine_ne_yLine
    (xLine_ne_diagonalLine 0) (yLine_ne_diagonalLine 0)).mpr concurrent_traces

/-- The triangle `x = 0`, `y = 0`, `x + y = 1` has empty triple intersection. -/
theorem triangle_inter_eq_bot :
    (xLine k).val ⊓ (yLine k).val ⊓ (diagonalLine (1 : k)).val = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hx0 := (mem_xLine x).mp hx.1.1
  have hx1 := (mem_yLine x).mp hx.1.2
  have hsum := (mem_diagonalLine 1 x).mp hx.2
  simp [hx0, hx1] at hsum

/-- Over `𝔽₂`, the empty triangle has conventional codimension two but is not dependent.
This guards against defining dependence by codimension alone. -/
theorem triangle_codim_but_not_dependent :
    codim ((xLine (ZMod 2)).val ⊓ (yLine (ZMod 2)).val ⊓
      (diagonalLine (1 : ZMod 2)).val) = 2 ∧
      ¬DependentTriple (xLine (ZMod 2)) (yLine (ZMod 2)) (diagonalLine 1) := by
  constructor
  · rw [triangle_inter_eq_bot, codim_bot]
    simp
  · intro hdep
    exact hdep.2.2.2.1 triangle_inter_eq_bot

/-- The three pairwise nonparallel sides of the `𝔽₂` triangle have noncollinear coefficient
points, unlike the three concurrent lines. -/
theorem triangle_coefficientPoints_not_collinear :
    ¬Projectivization.IsCollinear
      {coefficientPoint (xLine (ZMod 2)), coefficientPoint (yLine (ZMod 2)),
        coefficientPoint (diagonalLine (1 : ZMod 2))} := by
  rw [← dependentTriple_iff_coefficientPoints_collinear _ _ _ xLine_ne_yLine
    (xLine_ne_diagonalLine 1) (yLine_ne_diagonalLine 1) not_parallel_axes]
  exact triangle_codim_but_not_dependent.2

end OrlikSolomon.HyperplaneGT.CoordinateExamples
