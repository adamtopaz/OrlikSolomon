/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Presentation
public import OrlikSolomon.Combinatorics.Betti

/-!
# Two parallel affine lines

The vertical lines `x = 0` and `x = 1` in the affine plane give an arrangement over any field.
Their two generators have zero product, but their difference is nonzero over every nonzero
commutative coefficient ring, including characteristic two. These assertions use the presentation
alone and make no assumption about cohomology.

Blueprint: the parallel-lines regression for `def:os` and `lem:os-basic`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.PresentationExamples

variable {k : Type u} [Field k]

/-- The vertical affine line `x = a` in `k × k`. -/
def verticalLine (a : k) : AffineSubspace k (k × k) :=
  zeroLocus ((LinearMap.fst k k k).toAffineMap - AffineMap.const k (k × k) a)

@[simp]
theorem mem_verticalLine (a : k) (p : k × k) : p ∈ verticalLine a ↔ p.1 = a := by
  simp [verticalLine, sub_eq_zero]

/-- Every vertical line is a hyperplane of the affine plane. -/
theorem isHyperplane_verticalLine (a : k) : IsHyperplane (verticalLine a) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have := congrArg (fun f : (k × k) →ₗ[k] k ↦ f (1, 0)) h
  simp at this

/-- All vertical lines have the same direction, the kernel of the first projection. -/
theorem verticalLine_direction (a : k) :
    (verticalLine a).direction = LinearMap.ker (LinearMap.fst k k k) := by
  rw [verticalLine, direction_zeroLocus (isHyperplane_verticalLine a).ne_bot]
  simp

/-- Distinct vertical lines have empty intersection. -/
theorem verticalLine_inf_eq_bot {a b : k} (h : a ≠ b) :
    verticalLine a ⊓ verticalLine b = ⊥ := by
  ext p
  simp only [AffineSubspace.mem_inf_iff, mem_verticalLine]
  constructor
  · rintro ⟨ha, hb⟩
    exact (h (ha.symm.trans hb)).elim
  · intro hp
    exact False.elim (AffineSubspace.notMem_bot k (k × k) p hp)

/-- The arrangement of the two parallel vertical lines `x = 0` and `x = 1`. -/
def parallelLines (k : Type u) [Field k] : Arrangement k (k × k) := by
  classical
  exact Arrangement.ofFinset {verticalLine (0 : k), verticalLine (1 : k)}

@[simp]
theorem mem_parallelLines (H : AffineSubspace k (k × k)) :
    H ∈ parallelLines k ↔ H = verticalLine 0 ∨ H = verticalLine 1 := by
  classical
  simp only [parallelLines, Arrangement.mem_ofFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl <;> exact isHyperplane_verticalLine _

/-- The generator label for the line `x = 0`. -/
def zeroLine (k : Type u) [Field k] : parallelLines k :=
  ⟨verticalLine 0, (mem_parallelLines _).mpr (Or.inl rfl)⟩

/-- The generator label for the line `x = 1`. -/
def oneLine (k : Type u) [Field k] : parallelLines k :=
  ⟨verticalLine 1, (mem_parallelLines _).mpr (Or.inr rfl)⟩

theorem zeroLine_ne_oneLine : zeroLine k ≠ oneLine k := by
  intro h
  have h' := congrArg
    (fun H : parallelLines k ↦ ((0 : k), (0 : k)) ∈ (H : AffineSubspace k (k × k))) h
  simp [zeroLine, oneLine] at h'

/-- The two vertical lines are pairwise disjoint over every field, including `𝔽₂`. -/
theorem parallelLines_pairwise_disjoint :
    Pairwise fun H K : parallelLines k ↦ (H : AffineSubspace k (k × k)) ⊓ K = ⊥ := by
  intro H K hne
  rcases (mem_parallelLines _).mp H.2 with hH | hH <;>
    rcases (mem_parallelLines _).mp K.2 with hK | hK
  · exact (hne (Subtype.ext (hH.trans hK.symm))).elim
  · rw [hH, hK]
    exact verticalLine_inf_eq_bot (zero_ne_one : (0 : k) ≠ 1)
  · rw [hH, hK]
    exact verticalLine_inf_eq_bot (one_ne_zero : (1 : k) ≠ 0)
  · exact (hne (Subtype.ext (hH.trans hK.symm))).elim

/-- The two parallel lines contribute two degree-one terms and no degree-two term. -/
theorem poincarePolynomial_parallelLines :
    (parallelLines k).poincarePolynomial = 1 + 2 * Polynomial.X := by
  classical
  have hne : verticalLine (0 : k) ≠ verticalLine 1 := fun h ↦
    zeroLine_ne_oneLine (Subtype.ext h)
  have hplanes : (parallelLines k).hyperplanes = {verticalLine 0, verticalLine 1} := by
    ext H
    simp only [Arrangement.mem_hyperplanes, mem_parallelLines, Finset.mem_insert,
      Finset.mem_singleton]
  exact Arrangement.poincarePolynomial_pair_disjoint _ hne hplanes
    (verticalLine_inf_eq_bot zero_ne_one)

/-- The generators of the two parallel lines have zero product. -/
theorem parallelLines_product (B : Type v) [CommRing B] :
    OSAlgebra.generator B (parallelLines k) (zeroLine k) *
      OSAlgebra.generator B (parallelLines k) (oneLine k) = 0 :=
  OSAlgebra.generator_mul_eq_zero_of_disjoint _ _ _ _
    (verticalLine_inf_eq_bot zero_ne_one)

/-- The difference of the two parallel-line generators remains nonzero over every nonzero
coefficient ring; no assumption that `2` is invertible is needed. -/
theorem parallelLines_difference (B : Type v) [CommRing B] [Nontrivial B] :
    OSAlgebra.generator B (parallelLines k) (oneLine k) -
      OSAlgebra.generator B (parallelLines k) (zeroLine k) ≠ 0 :=
  OSAlgebra.generator_sub_ne_zero_of_pairwise_disjoint _ _ parallelLines_pairwise_disjoint
    _ _ zeroLine_ne_oneLine

example : OSAlgebra.generator (ZMod 2) (parallelLines (ZMod 2)) (oneLine (ZMod 2)) -
    OSAlgebra.generator (ZMod 2) (parallelLines (ZMod 2)) (zeroLine (ZMod 2)) ≠ 0 :=
  parallelLines_difference (ZMod 2)

end OrlikSolomon.PresentationExamples
