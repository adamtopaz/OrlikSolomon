/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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

universe u v

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

namespace OSAlgebra

variable {𝒜 : Arrangement k V}

private theorem not_isDependent_of_pairwise_disjoint
    (h𝒜 : Pairwise fun H K : 𝒜 ↦ (H : AffineSubspace k V) ⊓ K = ⊥)
    {I : List 𝒜} (hI : I.Nodup) : ¬ Arrangement.IsDependent I := by
  cases I with
  | nil => exact Arrangement.isDependent_nil 𝒜
  | cons H I =>
    cases I with
    | nil => simp [Arrangement.IsDependent, 𝒜.isHyperplane H.2 |>.codim_eq_one]
    | cons K I =>
      have hHK : H ≠ K := fun h ↦ (List.nodup_cons.mp hI).1 (by simp [h])
      apply Arrangement.not_isDependent_of_inter_eq_bot
      simp [Arrangement.inter_cons, ← inf_assoc, h𝒜 hHK]

variable (B : Type v) [CommRing B] (𝒜 : Arrangement k V)

/-- The product of generators of disjoint hyperplanes vanishes in the presentation. -/
theorem generator_mul_eq_zero_of_disjoint (H K : 𝒜)
    (hHK : (H : AffineSubspace k V) ⊓ K = ⊥) :
    generator B 𝒜 H * generator B 𝒜 K = 0 := by
  simpa using word_eq_zero_of_inter_eq_bot B 𝒜 (I := [H, K]) (by simpa using hHK)

private def disjointDetectorFamily (K : 𝒜) (L : 𝒜) : TrivSqZeroExt B B :=
  by classical exact TrivSqZeroExt.inr (if L = K then 1 else 0)

private theorem isFamily_disjointDetectorFamily
    (h𝒜 : Pairwise fun H K : 𝒜 ↦ (H : AffineSubspace k V) ⊓ K = ⊥) (K : 𝒜) :
    IsFamily 𝒜 (disjointDetectorFamily B 𝒜 K) where
  mul_self _ := by simp [disjointDetectorFamily]
  mul_add_mul_swap_of_ne _ := by simp [disjointDetectorFamily]
  word_eq_zero I _ hI := by
    cases I with
    | nil => simp at hI
    | cons H I =>
      cases I with
      | nil => exact ((𝒜.isHyperplane H.2).ne_bot (by simpa using hI)).elim
      | cons L I => simp [word_cons, disjointDetectorFamily, ← mul_assoc]
  wordBoundary_eq_zero _ hI hdep := (not_isDependent_of_pairwise_disjoint h𝒜 hI hdep).elim

/-- Distinct generators of a pairwise disjoint arrangement have nonzero difference over any
nonzero coefficient ring. In particular, empty intersections do not impose boundary relations.
No invertibility assumption on `2` is used. -/
theorem generator_sub_ne_zero_of_pairwise_disjoint [Nontrivial B]
    (h𝒜 : Pairwise fun H K : 𝒜 ↦ (H : AffineSubspace k V) ⊓ K = ⊥)
    (H K : 𝒜) (hHK : H ≠ K) : generator B 𝒜 K - generator B 𝒜 H ≠ 0 := by
  intro h
  let f : OSAlgebra B 𝒜 →ₐ[B] TrivSqZeroExt B B :=
    lift (disjointDetectorFamily B 𝒜 K) (isFamily_disjointDetectorFamily B 𝒜 h𝒜 K)
  have h' := congrArg (fun x ↦ (f x).snd) h
  simp [f, disjointDetectorFamily, hHK] at h'

end OSAlgebra

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

end PresentationExamples

end OrlikSolomon
