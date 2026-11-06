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

omit [FiniteDimensional k V] in
private theorem exists_old_list {I : List 𝒜} (hH : H ∉ I) :
    ∃ J : List (𝒜.deletion H), J.map (Arrangement.inclusion (𝒜.deletion_le H)) = I := by
  revert hH
  induction I with
  | nil => exact fun _ ↦ ⟨[], rfl⟩
  | cons K I ih =>
    intro hH
    have hK : K ≠ H := fun h ↦ hH (List.mem_cons.2 (Or.inl h.symm))
    have hI : H ∉ I := fun h ↦ hH (List.mem_cons_of_mem K h)
    obtain ⟨J, hJ⟩ := ih hI
    let K' : 𝒜.deletion H := ⟨K, Arrangement.mem_deletion.2 ⟨fun h ↦ hK (Subtype.ext h), K.2⟩⟩
    refine ⟨K' :: J, ?_⟩
    rw [List.map_cons, hJ]
    congr 1

omit [FiniteDimensional k V] in
private theorem exists_restricted_list (J : List (𝒜.deletion H))
    (h : ∀ K ∈ J, (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) :
    ∃ I : List (𝒜.restriction H), List.Forall₂
      (fun (K : 𝒜.deletion H) (L : 𝒜.restriction H) ↦
      (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L ∧
        (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) J I := by
  revert h
  induction J with
  | nil => exact fun _ ↦ ⟨[], .nil⟩
  | cons K J ih =>
    intro h
    have hK := h K (List.mem_cons_self)
    obtain ⟨I, hI⟩ := ih fun K' hK' ↦ h K' (List.mem_cons_of_mem K hK')
    let L : 𝒜.restriction H := ⟨(K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)),
      Arrangement.comap_chart_mem_restriction (𝒜.isHyperplane H.2) K.2
        ((comap_chart_eq_bot_iff (𝒜.isHyperplane H.2).ne_bot).not.1 hK)⟩
    exact ⟨L :: I, .cons ⟨rfl, hK⟩ hI⟩

/-- Every old word preceded by the deleted generator has a preimage under the restriction lift.
An empty trace kills the class; otherwise replace all old factors by the chosen representatives.
Repeated restricted labels are allowed and are already handled by the exterior presentation. -/
theorem cokernelMk_generator_old_word_mem_range (J : List (𝒜.deletion H)) :
    cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) J) ∈
      LinearMap.range (restrictionToCokernel B 𝒜 H) := by
  classical
  by_cases h : ∀ K ∈ J, (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥
  · obtain ⟨I, hI⟩ := exists_restricted_list 𝒜 H J h
    clear h
    have hrep : List.Forall₂ (fun K K' : 𝒜.deletion H ↦
        (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
            (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ∧
          (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥)
        J (I.map Arrangement.representative) := by
      induction hI with
      | nil => exact .nil
      | @cons K L J I hKL hJI ih =>
        exact .cons ⟨hKL.1.trans (Arrangement.comap_representative L).symm, hKL.2⟩ ih
    have hword := cokernelMk_generator_word_eq_of_forall₂ B 𝒜 H hrep []
    simp only [List.nil_append, word_map] at hword
    refine ⟨word (generator B (𝒜.restriction H)) I, ?_⟩
    rw [restrictionToCokernel_word]
    exact hword.symm
  · push Not at h
    obtain ⟨K, hK, hbot⟩ := h
    obtain ⟨P, T, rfl⟩ := List.append_of_mem hK
    rw [cokernelMk_generator_word_eq_zero_of_empty_trace B 𝒜 H P T K hbot]
    exact Submodule.zero_mem _

/-- The class of every generator word is in the range of the restriction lift. Words without
the deleted generator are old; repeated words vanish; the remaining words move it to the front
with their exterior sign. No basis theorem is used. -/
theorem cokernelMk_word_mem_range (I : List 𝒜) :
    cokernelMk B 𝒜 H (word (generator B 𝒜) I) ∈
      LinearMap.range (restrictionToCokernel B 𝒜 H) := by
  classical
  -- The exterior-word lemma uses the equality test induced by `DecidableEq`, also for `erase`.
  let : BEq 𝒜 := instBEqOfDecidableEq
  by_cases hI : I.Nodup
  · by_cases hH : H ∈ I
    · obtain ⟨J, hJ⟩ := exists_old_list 𝒜 H hI.not_mem_erase
      obtain ⟨x, hx⟩ := cokernelMk_generator_old_word_mem_range B 𝒜 H J
      have hw := (isExteriorFamily_generator B 𝒜).word_eq_smul_mul_word_erase hH
      have hwold : word (generator B 𝒜) (I.erase H) = word (oldGenerator B 𝒜 H) J :=
        (congrArg (word (generator B 𝒜)) hJ).symm.trans (word_map _ _ _)
      have hw' : word (generator B 𝒜) I =
          (I.idxOf H : ℤ).negOnePow • (generator B 𝒜 H * word (oldGenerator B 𝒜 H) J) :=
        hw.trans (congrArg (fun z ↦ (I.idxOf H : ℤ).negOnePow • (generator B 𝒜 H * z)) hwold)
      refine ⟨(I.idxOf H : ℤ).negOnePow • x, ?_⟩
      rw [map_zsmul_unit, hx, hw', map_zsmul_unit]
    · obtain ⟨J, hJ⟩ := exists_old_list 𝒜 H hH
      have hold : word (generator B 𝒜) I ∈ deletionRange B 𝒜 H := by
        rw [← hJ, word_map]
        exact word_mem_deletionRange B 𝒜 J
      rw [(cokernelMk_eq_zero_iff B 𝒜 H).2 hold]
      exact Submodule.zero_mem _
  · rw [(isExteriorFamily_generator B 𝒜).word_eq_zero_of_not_nodup hI, map_zero]
    exact Submodule.zero_mem _

/-- The linear lifting map from the restriction presentation to the module cokernel of deletion
is surjective, by exterior-word spanning alone. Blueprint: `lem:lift-surj`. -/
theorem restrictionToCokernel_surjective : Function.Surjective (restrictionToCokernel B 𝒜 H) := by
  intro y
  obtain ⟨x, rfl⟩ := cokernelMk_surjective B 𝒜 H y
  change cokernelMk B 𝒜 H x ∈ LinearMap.range (restrictionToCokernel B 𝒜 H)
  have hx : x ∈ Submodule.span B (Set.range (word (generator B 𝒜))) :=
    span_range_word B 𝒜 ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl⟩ := hx
    exact cokernelMk_word_mem_range B 𝒜 H I
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul b x _ hx => simpa only [map_smul] using Submodule.smul_mem _ b hx

end OrlikSolomon.OSAlgebra
