/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.CokernelData.Words

/-!
# The linear lifting map to the deletion cokernel

The restriction presentation maps linearly to the module cokernel of deletion. The map sends
a restricted word to the same old representative word preceded by the deleted generator.
Its descent kills the full two-sided relation submodule, including arbitrary left and right
contexts. It is not an algebra quotient lift.

Blueprint: `def:lift-map` and `lem:lift-surj`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (B : Type v) [CommRing B] (𝒜 : Arrangement k V) (H : 𝒜)

/-- Each restricted relator, multiplied by the deleted generator after taking old
representatives, belongs to the old image. Blueprint: `def:lift-map`. -/
theorem generator_mul_representativeMap_mem_deletionRange
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    {x : ExteriorAlgebra B (𝒜.restriction H →₀ B)} (hx : x ∈ osRelations B (𝒜.restriction H)) :
    generator B 𝒜 H * representativeMap B 𝒜 r x ∈ deletionRange B 𝒜 H := by
  obtain ⟨I, _, ⟨hI, rfl⟩ | ⟨hI, rfl⟩⟩ := (mem_osRelations B (𝒜.restriction H)).1 hx
  · rw [representativeMap_word]
    have h : generator B 𝒜 H * word (representativeGenerator B 𝒜 r) I = 0 :=
      generator_mul_word_representatives_eq_zero B 𝒜 H r hr hI
    rw [h]
    exact Submodule.zero_mem _
  · rw [representativeMap_wordBoundary]
    have h : generator B 𝒜 H * wordBoundary (representativeGenerator B 𝒜 r) I =
        word (representativeGenerator B 𝒜 r) I :=
      generator_mul_wordBoundary_representatives B 𝒜 H r hr hI
    rw [h, ← representativeMap_word]
    exact representativeMap_mem_deletionRange B 𝒜 r _

/-- With any prescribed old representatives, the preliminary linear map kills every context
of every restricted relator. Blueprint: the linear descent in `def:lift-map`. -/
theorem preRestrictionToCokernel_context
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    (u : ExteriorAlgebra B (𝒜.restriction H →₀ B))
    (x : ExteriorAlgebra B (𝒜.restriction H →₀ B)) (hx : x ∈ osRelations B (𝒜.restriction H))
    (v : ExteriorAlgebra B (𝒜.restriction H →₀ B)) :
    preRestrictionToCokernel B 𝒜 H r (u * x * v) = 0 :=
  preRestrictionToCokernel_context_eq_zero B 𝒜 H r
    (fun _ hx ↦ generator_mul_representativeMap_mem_deletionRange B 𝒜 H r hr hx) u x hx v

/-- The linear restriction lift for a specified family of old representatives. The descent is
linear and checks the entire two-sided relation submodule. Blueprint: `def:lift-map`. -/
def restrictionToCokernelOfRepresentatives
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L) :
    OSAlgebra B (𝒜.restriction H) →ₗ[B] DeletionCokernel B 𝒜 H :=
  liftLinear B (𝒜.restriction H) (preRestrictionToCokernel B 𝒜 H r)
    (preRestrictionToCokernel_context B 𝒜 H r hr)

/-- On words, the linear restriction lift prepends the deleted generator to the chosen old
representative word. -/
@[simp]
theorem restrictionToCokernelOfRepresentatives_word
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    (I : List (𝒜.restriction H)) :
    restrictionToCokernelOfRepresentatives B 𝒜 H r hr (word (generator B (𝒜.restriction H)) I) =
      cokernelMk B 𝒜 H (generator B 𝒜 H * word (representativeGenerator B 𝒜 r) I) := by
  rw [← quotient_word, restrictionToCokernelOfRepresentatives, liftLinear_quotient,
    preRestrictionToCokernel_apply, representativeMap_word]

/-- The canonical linear restriction map to the module cokernel of deletion.
Blueprint: `def:lift-map`. -/
def restrictionToCokernel :
    OSAlgebra B (𝒜.restriction H) →ₗ[B] DeletionCokernel B 𝒜 H :=
  restrictionToCokernelOfRepresentatives B 𝒜 H Arrangement.representative
    Arrangement.comap_representative

/-- The canonical restriction lift on a generator word. -/
@[simp]
theorem restrictionToCokernel_word (I : List (𝒜.restriction H)) :
    restrictionToCokernel B 𝒜 H (word (generator B (𝒜.restriction H)) I) =
      cokernelMk B 𝒜 H
        (generator B 𝒜 H * word (representativeGenerator B 𝒜 Arrangement.representative) I) :=
  restrictionToCokernelOfRepresentatives_word B 𝒜 H _ _ I

/-- The linear lifting map is independent of every chosen old representative. The proof changes
one letter at a time in each word, using the same-trace triple relation in old word contexts.
Blueprint: independence in `def:lift-map`. -/
theorem restrictionToCokernelOfRepresentatives_eq
    (r s : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    (hs : ∀ L, (s L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L) :
    restrictionToCokernelOfRepresentatives B 𝒜 H r hr =
      restrictionToCokernelOfRepresentatives B 𝒜 H s hs := by
  apply linearMap_ext
  intro I
  rw [restrictionToCokernelOfRepresentatives_word, restrictionToCokernelOfRepresentatives_word]
  have h : List.Forall₂ (fun K K' : 𝒜.deletion H ↦
      (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
          (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ∧
        (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥)
      (I.map r) (I.map s) := by
    induction I with
    | nil => exact .nil
    | cons L I ih =>
      apply List.Forall₂.cons _ ih
      exact ⟨(hr L).trans (hs L).symm, by
        rw [hr L]
        exact ((𝒜.restriction H).isHyperplane L.2).ne_bot⟩
  have hword := cokernelMk_generator_word_eq_of_forall₂ B 𝒜 H h []
  simp only [List.nil_append, word_map] at hword
  exact hword

/-- Any choice of old representatives computes the canonical restriction lift. -/
theorem restrictionToCokernelOfRepresentatives_eq_restrictionToCokernel
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L) :
    restrictionToCokernelOfRepresentatives B 𝒜 H r hr = restrictionToCokernel B 𝒜 H :=
  restrictionToCokernelOfRepresentatives_eq B 𝒜 H r Arrangement.representative hr
    Arrangement.comap_representative

end OrlikSolomon.OSAlgebra
