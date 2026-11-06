/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Grading.Basic

/-!
# Restricting an internal grading to a homogeneous submodule

A submodule closed under homogeneous components inherits the internal direct-sum decomposition
of its ambient module. A homogeneous subalgebra inherits the graded algebra structure. These
constructions are used for the boundary kernel in blueprint `lem:projective-algebra`.
-/

@[expose] public section

open DirectSum

namespace OrlikSolomon

section Submodule

variable {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [Decomposition ℳ] (S : Submodule R M)

/-- The intersections with the ambient pieces form an internal direct sum on a homogeneous
submodule. -/
theorem isInternal_comap_subtype (hS : DirectSum.SetLike.IsHomogeneous ℳ S) :
    IsInternal (fun i ↦ (ℳ i).comap S.subtype) := by
  classical
  apply isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · let e : Submodule R S ≃o Set.Iic S := S.mapIic
    have he : (e ∘ fun i ↦ (ℳ i).comap S.subtype) =
        fun i ↦ (⟨ℳ i ⊓ S, show ℳ i ⊓ S ≤ S from inf_le_right⟩ : Set.Iic S) := by
      ext i x
      change x ∈ ((ℳ i).comap S.subtype).map S.subtype ↔ x ∈ ℳ i ⊓ S
      rw [Submodule.map_comap_subtype, inf_comm]
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact .of_coe_Iic_comp ((Decomposition.isInternal ℳ).submodule_iSupIndep.mono
      fun _ ↦ inf_le_left)
  · apply top_unique
    intro x _
    let L := ⨆ i, (ℳ i).comap S.subtype
    have hx : (x : M) ∈ L.map S.subtype := by
      rw [← sum_support_decompose ℳ (x : M)]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.mem_map_of_mem <| (le_iSup (fun i ↦ (ℳ i).comap S.subtype) i)
        (show (⟨(decompose ℳ (x : M) i : M), hS i x.property⟩ : S) ∈
          (ℳ i).comap S.subtype from (decompose ℳ (x : M) i).property)
    obtain ⟨y, hy, hxy⟩ := hx
    exact (Subtype.ext hxy) ▸ hy

/-- A homogeneous submodule inherits the decomposition by intersections with the ambient pieces.
The hypothesis is explicit, so this does not introduce an instance search for homogeneity. -/
@[instance_reducible]
noncomputable def homogeneousSubmoduleDecomposition
    (hS : DirectSum.SetLike.IsHomogeneous ℳ S) :
    Decomposition (fun i ↦ (ℳ i).comap S.subtype) :=
  (isInternal_comap_subtype ℳ S hS).chooseDecomposition

end Submodule

section Subalgebra

variable {R ι A : Type*} [CommRing R] [Ring A] [Algebra R A] [DecidableEq ι]
  [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Subalgebra R A)

/-- A homogeneous subalgebra inherits its ambient internal grading, by taking intersections with
the homogeneous pieces. -/
@[instance_reducible]
noncomputable def homogeneousSubalgebraGradedAlgebra
    (hS : DirectSum.SetLike.IsHomogeneous 𝒜 S) :
    GradedAlgebra (fun i ↦ (𝒜 i).comap S.val.toLinearMap) := by
  letI : SetLike.GradedMonoid (fun i ↦ (𝒜 i).comap S.val.toLinearMap) :=
    { one_mem := SetLike.one_mem_graded 𝒜
      mul_mem i j x y hx hy := by
        change (x : A) * (y : A) ∈ 𝒜 (i + j)
        exact SetLike.mul_mem_graded (A := 𝒜) hx hy }
  have hi : IsInternal (fun i ↦ (𝒜 i).comap S.val.toLinearMap) :=
    isInternal_comap_subtype 𝒜 S.toSubmodule hS
  exact hi.gradedAlgebra

end Subalgebra

end OrlikSolomon
