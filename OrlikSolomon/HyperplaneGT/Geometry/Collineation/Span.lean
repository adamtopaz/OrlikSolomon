/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace

/-!
# Projective collineations preserve spans

A projective permutation preserving each line as a set preserves arbitrary projective spans.
The proof uses the existing inductive projective-span construction, without a fundamental
theorem of projective geometry or finite-dimensionality assumptions.

Blueprint: `lem:c01`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

open scoped LinearAlgebra.Projectivization

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The projective span of two represented points is the projectivization of their vector span.
The points need not be distinct. -/
theorem projective_span_pair_eq (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    Projectivization.Subspace.span {Projectivization.mk k a ha, Projectivization.mk k b hb} =
      (Submodule.span k {a, b}).projectivization := by
  refine le_antisymm (Projectivization.Subspace.span_le_subspace_iff.mpr ?_) ?_
  · rintro _ (rfl | rfl) <;>
      exact Submodule.subset_span (by simp)
  · intro p hp
    induction p using Projectivization.ind with | h v hv =>
    have hle : Submodule.span k {a, b} ≤ Projectivization.Subspace.submodule
        (Projectivization.Subspace.span
          {Projectivization.mk k a ha, Projectivization.mk k b hb}) := by
      refine Submodule.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · exact (Projectivization.Subspace.mem_submodule_iff _ ha).mpr
          (Projectivization.Subspace.subset_span _ (by simp))
      · exact (Projectivization.Subspace.mem_submodule_iff _ hb).mpr
          (Projectivization.Subspace.subset_span _ (by simp))
    exact (Projectivization.Subspace.mem_submodule_iff _ hv).mp (hle hp)

/-- A singleton already is a projective subspace. -/
@[simp]
theorem projective_span_singleton_coe (p : ℙ k V) :
    (Projectivization.Subspace.span {p} : Set (ℙ k V)) = {p} := by
  induction p using Projectivization.ind with | h a ha =>
  have h := projective_span_pair_eq (k := k) a a ha ha
  simp only [Set.pair_eq_singleton] at h
  rw [h]
  ext p
  induction p using Projectivization.ind with | h v hv =>
  simp only [SetLike.mem_coe, Submodule.mk_mem_projectivization_iff,
    Set.mem_singleton_iff, Projectivization.mk_eq_mk_iff', Submodule.mem_span_singleton]

/-- A projective permutation maps every line through two distinct points onto the line through
their images. Equality of images includes line preservation in the inverse direction.

Blueprint: the hypothesis of `C01`–`C03`. -/
def PreservesProjectiveLines (F : ℙ k V ≃ ℙ k V) : Prop :=
  ∀ p q, p ≠ q →
    F '' (Projectivization.Subspace.span {p, q} : Set (ℙ k V)) =
      (Projectivization.Subspace.span {F p, F q} : Set (ℙ k V))

namespace PreservesProjectiveLines

/-- Line preservation also applies to coincident endpoints, where the span is a singleton. -/
theorem image_span_pair {F : ℙ k V ≃ ℙ k V} (hF : PreservesProjectiveLines F)
    (p q : ℙ k V) :
    F '' (Projectivization.Subspace.span {p, q} : Set (ℙ k V)) =
      (Projectivization.Subspace.span {F p, F q} : Set (ℙ k V)) := by
  by_cases h : p = q
  · subst q
    simp
  · exact hF p q h

/-- Membership of a two-point span is reflected and preserved by a collineation. -/
theorem mem_span_pair_iff {F : ℙ k V ≃ ℙ k V} (hF : PreservesProjectiveLines F)
    (p q r : ℙ k V) :
    F r ∈ Projectivization.Subspace.span {F p, F q} ↔
      r ∈ Projectivization.Subspace.span {p, q} := by
  change F r ∈ (Projectivization.Subspace.span {F p, F q} : Set (ℙ k V)) ↔ _
  rw [← hF.image_span_pair p q]
  exact F.injective.mem_set_image

/-- The identity permutation preserves projective lines. -/
theorem refl : PreservesProjectiveLines (Equiv.refl (ℙ k V)) := by
  intro p q _
  simp

/-- The inverse of a line-preserving permutation preserves lines. -/
theorem symm {F : ℙ k V ≃ ℙ k V} (hF : PreservesProjectiveLines F) :
    PreservesProjectiveLines F.symm := by
  intro p q _
  ext r
  have h : F r ∈ Projectivization.Subspace.span {p, q} ↔
      r ∈ Projectivization.Subspace.span {F.symm p, F.symm q} := by
    simpa using hF.mem_span_pair_iff (F.symm p) (F.symm q) r
  constructor
  · rintro ⟨x, hx, hxr⟩
    apply h.mp
    rwa [← hxr, F.apply_symm_apply]
  · intro hr
    exact ⟨F r, h.mpr hr, F.symm_apply_apply r⟩

/-- Composition of line-preserving permutations preserves lines. -/
theorem trans {F G : ℙ k V ≃ ℙ k V}
    (hF : PreservesProjectiveLines F) (hG : PreservesProjectiveLines G) :
    PreservesProjectiveLines (F.trans G) := by
  intro p q _
  change (G ∘ F) '' _ = _
  rw [Set.image_comp, hF.image_span_pair, hG.image_span_pair]
  rfl

end PreservesProjectiveLines

/-- A line-preserving projective permutation preserves every projective span, in particular
the spans of all finite sets. No finite-dimensionality assumption is needed.

Blueprint: `lem:c01`. -/
theorem collineation_preserves_span (F : ℙ k V ≃ ℙ k V)
    (hF : PreservesProjectiveLines F) (S : Set (ℙ k V)) :
    F '' (Projectivization.Subspace.span S : Set (ℙ k V)) =
      (Projectivization.Subspace.span (F '' S) : Set (ℙ k V)) := by
  have maps_span (E : ℙ k V ≃ ℙ k V) (hE : PreservesProjectiveLines E)
      (T : Set (ℙ k V)) :
      E '' (Projectivization.Subspace.span T : Set (ℙ k V)) ⊆
        Projectivization.Subspace.span (E '' T) := by
    rintro _ ⟨p, hp, rfl⟩
    induction hp using Projectivization.Subspace.span_induction with
    | of_mem p hp =>
      exact Projectivization.Subspace.subset_span _ ⟨p, hp, rfl⟩
    | add v w hv hw hvw _ _ ihv ihw =>
      have hadd : Projectivization.mk k (v + w) hvw ∈ Projectivization.Subspace.span
          {Projectivization.mk k v hv, Projectivization.mk k w hw} :=
        (Projectivization.Subspace.span _).mem_add _ _ hv hw hvw
          (Projectivization.Subspace.subset_span _ (by simp))
          (Projectivization.Subspace.subset_span _ (by simp))
      have hle : Projectivization.Subspace.span
          {E (Projectivization.mk k v hv), E (Projectivization.mk k w hw)} ≤
          Projectivization.Subspace.span (E '' T) := by
        refine Projectivization.Subspace.span_le_subspace_iff.mpr ?_
        rintro _ (rfl | rfl) <;> assumption
      exact hle ((hE.mem_span_pair_iff _ _ _).mpr hadd)
  apply Set.Subset.antisymm (maps_span F hF S)
  intro p hp
  have h := maps_span F.symm hF.symm (F '' S) ⟨p, hp, rfl⟩
  simp only [Set.image_image, Equiv.symm_apply_apply, Set.image_id'] at h
  exact ⟨F.symm p, h, F.apply_symm_apply p⟩

end OrlikSolomon.HyperplaneGT
