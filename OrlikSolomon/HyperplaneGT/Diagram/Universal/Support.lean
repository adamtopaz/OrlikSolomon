/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import OrlikSolomon.HyperplaneGT.Algebra.QuadraticKernel
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.System

/-!
# Finite stages in the universal hyperplane module

The universal degree-one module is the literal free module `Hyperplane k n →₀ R`.
Every finite arrangement embeds by extension by zero along its existing hyperplane-label
map. The image consists exactly of vectors supported on that arrangement.

For an arbitrary chosen cofinal system, finitely many vectors have representatives in one
selected stage. Equality of representatives can be checked in a common upper stage. The
selected family is never assumed to contain unions, and no field-extension hypothesis is
needed once the cofinal system has been supplied.

Blueprint: the support and common-stage part of U01 (`def:u01`, `lem:u01`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} [Field k] {n : ℕ} (R : Type w) [CommRing R]

/-- Arrangement labels embed injectively into the type of all affine hyperplanes. -/
theorem arrangementHyperplane_injective (𝒜 : Arrangement k (Fin n → k)) :
    Function.Injective (arrangementHyperplane 𝒜) := by
  intro H K h
  exact Subtype.ext (congrArg (fun X : Hyperplane k n ↦ X.val) h)

/-- The image of the label embedding consists precisely of the arrangement's hyperplanes. -/
theorem range_arrangementHyperplane (𝒜 : Arrangement k (Fin n → k)) :
    Set.range (arrangementHyperplane 𝒜) = {H : Hyperplane k n | H.val ∈ 𝒜} := by
  ext H
  constructor
  · rintro ⟨K, rfl⟩
    exact K.property
  · intro hH
    exact ⟨⟨H.val, hH⟩, Subtype.ext rfl⟩

/-- Extension by zero includes the free module on a finite arrangement in the free module
on all hyperplanes. No base field or chosen cofinal system enters this map.

Blueprint: U01 (`def:u01`). -/
def finiteStageMap (𝒜 : Arrangement k (Fin n → k)) :
    (𝒜 →₀ R) →ₗ[R] (Hyperplane k n →₀ R) :=
  Finsupp.lmapDomain R R (arrangementHyperplane 𝒜)

/-- A single coefficient retains its geometric hyperplane label. -/
@[simp]
theorem finiteStageMap_single (𝒜 : Arrangement k (Fin n → k)) (H : 𝒜) (r : R) :
    finiteStageMap R 𝒜 (Finsupp.single H r) =
      Finsupp.single (arrangementHyperplane 𝒜 H) r := by
  simp [finiteStageMap]

/-- Extension by zero is injective, also when the coefficient ring is zero. -/
theorem finiteStageMap_injective (𝒜 : Arrangement k (Fin n → k)) :
    Function.Injective (finiteStageMap R 𝒜) :=
  Finsupp.mapDomain_injective (arrangementHyperplane_injective 𝒜)

/-- Coefficients at labels of the finite arrangement are unchanged by extension by zero. -/
@[simp]
theorem finiteStageMap_apply (𝒜 : Arrangement k (Fin n → k)) (x : 𝒜 →₀ R) (H : 𝒜) :
    finiteStageMap R 𝒜 x (arrangementHyperplane 𝒜 H) = x H :=
  Finsupp.mapDomain_apply_of_injective (arrangementHyperplane_injective 𝒜) x H

/-- Extension by zero has zero coefficient at every hyperplane outside the arrangement. -/
theorem finiteStageMap_apply_of_not_mem (𝒜 : Arrangement k (Fin n → k)) (x : 𝒜 →₀ R)
    (H : Hyperplane k n) (hH : H.val ∉ 𝒜) : finiteStageMap R 𝒜 x H = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rwa [range_arrangementHyperplane]

/-- The image of a finite stage is exactly its supported submodule in the universal module.

Blueprint: U01 (`def:u01`). -/
theorem range_finiteStageMap (𝒜 : Arrangement k (Fin n → k)) :
    LinearMap.range (finiteStageMap R 𝒜) =
      Finsupp.supported R R {H : Hyperplane k n | H.val ∈ 𝒜} := by
  rw [finiteStageMap, Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single,
    ← range_arrangementHyperplane]
  congr 1
  exact Set.range_comp (fun H : Hyperplane k n ↦ Finsupp.single H (1 : R))
    (arrangementHyperplane 𝒜)

/-- Membership in a stage image is equivalent to containment of the finite support. -/
theorem mem_range_finiteStageMap_iff (𝒜 : Arrangement k (Fin n → k))
    (x : Hyperplane k n →₀ R) :
    x ∈ LinearMap.range (finiteStageMap R 𝒜) ↔ ∀ H ∈ x.support, H.val ∈ 𝒜 := by
  rw [range_finiteStageMap, Finsupp.mem_supported]
  rfl

/-- Extending after inclusion gives the same universal vector as extending directly. -/
theorem finiteStageMap_comp_inclusion {𝒜 ℬ : Arrangement k (Fin n → k)} (h : 𝒜 ≤ ℬ) :
    (finiteStageMap R ℬ).comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
      finiteStageMap R 𝒜 := by
  apply Finsupp.lhom_ext
  intro H r
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    finiteStageMap_single]
  rfl

/-- The pointwise formula for extension by zero after a finite-stage inclusion. -/
theorem finiteStageMap_inclusion {𝒜 ℬ : Arrangement k (Fin n → k)} (h : 𝒜 ≤ ℬ)
    (x : 𝒜 →₀ R) :
    finiteStageMap R ℬ (Finsupp.lmapDomain R R (Arrangement.inclusion h) x) =
      finiteStageMap R 𝒜 x :=
  DFunLike.congr_fun (finiteStageMap_comp_inclusion R h) x

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k]

namespace CofinalSystem

variable (C : CofinalSystem k₀ k n)

/-- Every finite collection of universal vectors is supported on one selected stage.
The union of supports is only an input to cofinality, not a selected stage. -/
theorem exists_stage_vectors (s : Finset (Hyperplane k n →₀ R)) :
    ∃ 𝒜 : C.Stage, ∀ x ∈ s, ∃ a : 𝒜.val.val →₀ R,
      finiteStageMap R 𝒜.val.val a = x := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_containing (s.biUnion Finsupp.support)
  refine ⟨𝒜, fun x hx ↦ ?_⟩
  apply (mem_range_finiteStageMap_iff R 𝒜.val.val x).mpr
  intro H hH
  exact h𝒜 H (Finset.mem_biUnion.mpr ⟨x, hx, hH⟩)

/-- Every universal vector comes from a finite stage of any chosen cofinal system.

Blueprint: U01 (`lem:u01`). -/
theorem exists_stage_vector (x : Hyperplane k n →₀ R) :
    ∃ 𝒜 : C.Stage, ∃ a : 𝒜.val.val →₀ R, finiteStageMap R 𝒜.val.val a = x := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_vectors R {x}
  exact ⟨𝒜, h𝒜 x (by simp)⟩

/-- Universal representatives agree exactly when they agree after inclusion in a common
upper stage. Neither union closure nor a particular choice of common stage is required.

Blueprint: U01 (`lem:u01`). -/
theorem finiteStageMap_eq_iff (𝒜 ℬ : C.Stage) (a : 𝒜.val.val →₀ R) (b : ℬ.val.val →₀ R) :
    finiteStageMap R 𝒜.val.val a = finiteStageMap R ℬ.val.val b ↔
      ∃ (𝒟 : C.Stage) (h𝒜 : 𝒜 ≤ 𝒟) (hℬ : ℬ ≤ 𝒟),
        Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜) a =
          Finsupp.lmapDomain R R (Arrangement.inclusion hℬ) b := by
  constructor
  · intro hab
    obtain ⟨𝒟, h𝒜, hℬ⟩ := exists_ge_ge 𝒜 ℬ
    refine ⟨𝒟, h𝒜, hℬ, finiteStageMap_injective R 𝒟.val.val ?_⟩
    simpa only [finiteStageMap_inclusion] using hab
  · rintro ⟨𝒟, h𝒜, hℬ, hab⟩
    simpa only [finiteStageMap_inclusion] using congrArg (finiteStageMap R 𝒟.val.val) hab

end CofinalSystem

end OrlikSolomon.HyperplaneGT
