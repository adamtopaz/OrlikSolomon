/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import OrlikSolomon.Geometry.Arrangement
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Action

/-!
# Cofinal systems of finite stable arrangements

A stable arrangement is an existing finite arrangement invariant under the coefficient Galois
action. A `CofinalSystem` selects a family of these arrangements containing every finite set
of hyperplanes in some member. Its stages inherit the inclusion order and the corresponding
thin category.

Common upper stages are obtained solely from cofinality. The selected family need not contain
the union of two of its members. No algebraicity or perfectness hypothesis is needed for these
definitions and common-stage arguments; algebraicity supplies the full system separately.

Blueprint: G06 (`def:g06`).
-/

@[expose] public section

universe u v

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}

/-- A finite arrangement is Galois-stable if the coefficient action carries every member into
the same arrangement. Applying the inverse automorphism gives equality of supports.

Blueprint: G06 (`def:g06`). -/
def IsGaloisStable (𝒜 : Arrangement k (Fin n → k)) : Prop :=
  ∀ (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n), H.val ∈ 𝒜 → (σ • H).val ∈ 𝒜

/-- Membership in a stable arrangement is invariant in both directions under Galois action. -/
theorem IsGaloisStable.smul_mem_iff {𝒜 : Arrangement k (Fin n → k)}
    (h𝒜 : IsGaloisStable (k₀ := k₀) 𝒜) (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    (σ • H).val ∈ 𝒜 ↔ H.val ∈ 𝒜 := by
  constructor
  · intro h
    simpa using h𝒜 σ⁻¹ (σ • H) h
  · exact h𝒜 σ H

/-- The empty arrangement is stable without any assumption on the field extension. -/
theorem isGaloisStable_empty : IsGaloisStable (k₀ := k₀)
    (∅ : Arrangement k (Fin n → k)) := by
  intro σ H hH
  exact (Arrangement.notMem_empty _ hH).elim

/-- A finite stable arrangement, with the existing arrangement and label types unchanged.

Blueprint: G06 (`def:g06`). -/
abbrev StableArrangement (k₀ : Type v) (k : Type u) [Field k₀] [Field k] [Algebra k₀ k]
    (n : ℕ) :=
  {𝒜 : Arrangement k (Fin n → k) // IsGaloisStable (k₀ := k₀) 𝒜}

/-- A chosen cofinal family of finite stable arrangements. Cofinality, rather than union
closure, is the only enlargement property required of the chosen family.

Blueprint: G06 (`def:g06`). -/
structure CofinalSystem (k₀ : Type v) (k : Type u) [Field k₀] [Field k] [Algebra k₀ k]
    (n : ℕ) where
  /-- The selected finite stable arrangements. -/
  stages : Set (StableArrangement k₀ k n)
  /-- Every finite set of hyperplanes belongs to some selected stage. -/
  cofinal : ∀ s : Finset (Hyperplane k n),
    ∃ 𝒜 ∈ stages, ∀ H ∈ s, H.val ∈ 𝒜.val

namespace CofinalSystem

variable (C : CofinalSystem k₀ k n)

/-- A stage is a member of the chosen cofinal family, ordered by arrangement inclusion. -/
abbrev Stage := {𝒜 : StableArrangement k₀ k n // 𝒜 ∈ C.stages}

/-- A cofinal system is determined by its selected family; the enlargement witness is a
proposition. -/
@[ext]
theorem ext {C D : CofinalSystem k₀ k n} (h : C.stages = D.stages) : C = D := by
  cases C
  cases D
  cases h
  rfl

/-- Every finite set of hyperplanes lies in a stage of the chosen system. -/
theorem exists_stage_containing (s : Finset (Hyperplane k n)) :
    ∃ 𝒜 : C.Stage, ∀ H ∈ s, H.val ∈ 𝒜.val.val := by
  obtain ⟨𝒜, h𝒜, hs⟩ := C.cofinal s
  exact ⟨⟨𝒜, h𝒜⟩, hs⟩

/-- Every finite arrangement is contained in a selected stage, whether or not the arrangement
itself is stable or belongs to the chosen family. -/
theorem exists_ge_arrangement (𝒜 : Arrangement k (Fin n → k)) :
    ∃ ℬ : C.Stage, 𝒜 ≤ ℬ.val.val := by
  classical
  let s : Finset (Hyperplane k n) :=
    𝒜.hyperplanes.attach.image fun H ↦ ⟨H.val, 𝒜.isHyperplane H.property⟩
  obtain ⟨ℬ, hℬ⟩ := C.exists_stage_containing s
  refine ⟨ℬ, fun H hH ↦ ?_⟩
  exact hℬ ⟨H, 𝒜.isHyperplane hH⟩
    (Finset.mem_image.mpr ⟨⟨H, hH⟩, Finset.mem_attach _ _, rfl⟩)

/-- Finitely many selected stages have a common upper stage. The finite union is used only
as an input to cofinality; the selected family need not contain that union. -/
theorem exists_ge_finset (s : Finset C.Stage) : ∃ ℬ : C.Stage, ∀ 𝒜 ∈ s, 𝒜 ≤ ℬ := by
  classical
  let 𝒰 := Arrangement.ofFinset (s.biUnion fun 𝒜 ↦ 𝒜.val.val.hyperplanes)
  obtain ⟨ℬ, hℬ⟩ := C.exists_ge_arrangement 𝒰
  refine ⟨ℬ, ?_⟩
  intro 𝒜 h𝒜
  change 𝒜.val.val ≤ ℬ.val.val
  refine le_trans ?_ hℬ
  intro H hH
  exact Arrangement.mem_ofFinset.mpr
    ⟨Finset.mem_biUnion.mpr ⟨𝒜, h𝒜, hH⟩, 𝒜.val.val.isHyperplane hH⟩

/-- Every chosen cofinal family has at least one stage, also in dimension zero. -/
instance : Nonempty C.Stage := by
  obtain ⟨𝒜, -⟩ := C.exists_stage_containing ∅
  exact ⟨𝒜⟩

/-- Cofinality makes the inherited inclusion order directed, without union closure. -/
instance : IsDirectedOrder C.Stage := by
  classical
  constructor
  intro 𝒜 ℬ
  obtain ⟨𝒟, h𝒟⟩ := C.exists_ge_finset {𝒜, ℬ}
  exact ⟨𝒟, h𝒟 𝒜 (by simp), h𝒟 ℬ (by simp)⟩

end CofinalSystem

end OrlikSolomon.HyperplaneGT
