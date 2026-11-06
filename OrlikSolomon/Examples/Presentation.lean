/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.BaseChange
public import OrlikSolomon.Presentation.Generators
public import Mathlib.Algebra.Field.ZMod

/-!
# Regressions for the affine Orlik--Solomon relations

For pairwise disjoint hyperplanes, degree-one generators remain distinct over any nonzero
coefficient ring, while products of two distinct generators vanish. A map to a trivial
square-zero extension proves nonvanishing without the cohomology structure theorem.

The explicit arrangement of `0` and `1` in the affine line detects an omitted
nonempty-intersection guard: its empty intersection has codimension conventionally equal to one,
so the unguarded test would incorrectly impose a degree-one boundary relation.

Blueprint: the regressions for `def:os` and `lem:os-basic`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]


namespace PresentationExamples

/-- The hyperplane `x = a` in the affine line. -/
def pointHyperplane (a : k) : AffineSubspace k k :=
  zeroLocus (AffineMap.id k k - AffineMap.const k k a)

@[simp]
theorem mem_pointHyperplane (a x : k) : x ∈ pointHyperplane a ↔ x = a := by
  simp [pointHyperplane, sub_eq_zero]

/-- A point of the affine line is a hyperplane over every field. -/
theorem isHyperplane_pointHyperplane (a : k) : IsHyperplane (pointHyperplane a) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have := congrArg (fun f : k →ₗ[k] k ↦ f 1) h
  simp at this

/-- The arrangement of the two rational points `0` and `1` in the affine line. -/
def twoPoints (k : Type u) [Field k] : Arrangement k k :=
  by classical exact Arrangement.ofFinset {pointHyperplane (0 : k), pointHyperplane (1 : k)}

@[simp]
theorem mem_twoPoints (H : AffineSubspace k k) :
    H ∈ twoPoints k ↔ H = pointHyperplane 0 ∨ H = pointHyperplane 1 := by
  classical
  simp only [twoPoints, Arrangement.mem_ofFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl <;> exact isHyperplane_pointHyperplane _

/-- The generator label for the point `0`. -/
def zeroPoint (k : Type u) [Field k] : twoPoints k :=
  ⟨pointHyperplane 0, (mem_twoPoints _).mpr (Or.inl rfl)⟩

/-- The generator label for the point `1`. -/
def onePoint (k : Type u) [Field k] : twoPoints k :=
  ⟨pointHyperplane 1, (mem_twoPoints _).mpr (Or.inr rfl)⟩

theorem zeroPoint_ne_onePoint : zeroPoint k ≠ onePoint k := by
  intro h
  have h' := congrArg (fun H : twoPoints k ↦ (0 : k) ∈ (H : AffineSubspace k k)) h
  simp [zeroPoint, onePoint] at h'

/-- Distinct points in the affine line have empty intersection. -/
theorem pointHyperplane_inf_eq_bot {a b : k} (h : a ≠ b) :
    pointHyperplane a ⊓ pointHyperplane b = ⊥ := by
  ext x
  simp only [AffineSubspace.mem_inf_iff, mem_pointHyperplane]
  constructor
  · rintro ⟨ha, hb⟩
    exact (h (ha.symm.trans hb)).elim
  · intro hx
    exact False.elim (AffineSubspace.notMem_bot k k x hx)

/-- The two-point arrangement is pairwise disjoint, including over `𝔽₂`. -/
theorem twoPoints_pairwise_disjoint :
    Pairwise fun H K : twoPoints k ↦ (H : AffineSubspace k k) ⊓ K = ⊥ := by
  intro H K hne
  rcases (mem_twoPoints _).mp H.2 with hH | hH <;>
    rcases (mem_twoPoints _).mp K.2 with hK | hK
  · exact (hne (Subtype.ext (hH.trans hK.symm))).elim
  · rw [hH, hK]
    exact pointHyperplane_inf_eq_bot (zero_ne_one : (0 : k) ≠ 1)
  · rw [hH, hK]
    exact pointHyperplane_inf_eq_bot (one_ne_zero : (1 : k) ≠ 0)
  · exact (hne (Subtype.ext (hH.trans hK.symm))).elim

/-- The product relation for the two points of the affine line. -/
theorem twoPoints_product (B : Type v) [CommRing B] :
    OSAlgebra.generator B (twoPoints k) (zeroPoint k) *
      OSAlgebra.generator B (twoPoints k) (onePoint k) = 0 :=
  OSAlgebra.generator_mul_eq_zero_of_disjoint _ _ _ _
    (pointHyperplane_inf_eq_bot zero_ne_one)

/-- The intersection of the two points is empty. -/
theorem twoPoints_inter_eq_bot :
    Arrangement.inter [zeroPoint k, onePoint k] = ⊥ := by
  simpa [zeroPoint, onePoint] using
    (pointHyperplane_inf_eq_bot (zero_ne_one : (0 : k) ≠ 1))

/-- The unguarded codimension test incorrectly calls the two points dependent. This regression
explains why affine boundary relators must test that the intersection is nonempty. -/
theorem twoPoints_unguarded_codim_lt :
    codim (Arrangement.inter [zeroPoint k, onePoint k]) < [zeroPoint k, onePoint k].length := by
  rw [twoPoints_inter_eq_bot, codim_bot]
  simp

/-- The guarded predicate correctly rejects a boundary relation for the two points. -/
theorem twoPoints_not_isDependent :
    ¬ Arrangement.IsDependent [zeroPoint k, onePoint k] :=
  Arrangement.not_isDependent_of_inter_eq_bot twoPoints_inter_eq_bot

/-- The degree-one boundary is nonzero for two points, even with coefficients in characteristic
two. This would fail if the empty-intersection guard were omitted. -/
theorem twoPoints_difference (B : Type v) [CommRing B] [Nontrivial B] :
    OSAlgebra.generator B (twoPoints k) (onePoint k) -
      OSAlgebra.generator B (twoPoints k) (zeroPoint k) ≠ 0 :=
  OSAlgebra.generator_sub_ne_zero_of_pairwise_disjoint _ _ twoPoints_pairwise_disjoint
    _ _ zeroPoint_ne_onePoint

example : OSAlgebra.generator (ZMod 2) (twoPoints (ZMod 2)) (onePoint (ZMod 2)) -
    OSAlgebra.generator (ZMod 2) (twoPoints (ZMod 2)) (zeroPoint (ZMod 2)) ≠ 0 :=
  twoPoints_difference (ZMod 2)

example : OSAlgebra.generator (ZMod 2) (twoPoints (ZMod 2)) (onePoint (ZMod 2)) ^ 2 = 0 :=
  OSAlgebra.generator_sq _ _ _

-- Reducing integral coefficients modulo two is allowed without a flatness hypothesis.
-- Use the module attached to the algebra to avoid the integer-scalar diamond during inference.
example : letI : Module ℤ (OSAlgebra ℤ (twoPoints k)) := Algebra.toModule
    (ZMod 2) ⊗[ℤ] OSAlgebra ℤ (twoPoints k) ≃ₐ[ZMod 2]
      OSAlgebra (ZMod 2) (twoPoints k) := by
  letI : Module ℤ (OSAlgebra ℤ (twoPoints k)) := Algebra.toModule
  exact OSAlgebra.baseChangeEquiv ℤ (ZMod 2) _

-- The zero ring is a valid coefficient ring.
example (𝒜 : Arrangement k V) : Subsingleton (OSAlgebra (ZMod 1) 𝒜) :=
  inferInstance

-- Every arrangement in a zero-dimensional vector space is empty.
example (𝒜 : Arrangement k (Fin 0 → k)) : OSAlgebra (ZMod 2) 𝒜 ≃ₐ[ZMod 2] ZMod 2 :=
  OSAlgebra.equivOfSubsingleton _ _

end PresentationExamples

end OrlikSolomon
