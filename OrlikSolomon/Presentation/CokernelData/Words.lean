/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.CokernelData.Basic
public import OrlikSolomon.Presentation.RepresentativeRelations

/-!
# Replacing old words inside the deletion cokernel

The old image is stable under multiplication by old elements on both sides. Moving the deleted
generator through an old prefix therefore extends the same-trace triple relation to arbitrary
old word contexts. A finite sequence of these replacements proves independence of an entire
representative word.

Blueprint: the contextual statements in `lem:representatives` and `def:lift-map`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (B : Type v) [CommRing B] (𝒜 : Arrangement k V) (H : 𝒜)

/-- The old generators, viewed in the original affine presentation. -/
abbrev oldGenerator (K : 𝒜.deletion H) : OSAlgebra B 𝒜 :=
  generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K)

/-- An old prefix moves past the deleted generator with the exterior sign of its length. -/
theorem generator_mul_old_word_comm (P : List (𝒜.deletion H)) :
    generator B 𝒜 H * word (oldGenerator B 𝒜 H) P =
      (P.length : ℤ).negOnePow • (word (oldGenerator B 𝒜 H) P * generator B 𝒜 H) := by
  have h := (isExteriorFamily_generator B 𝒜).mul_word_comm H
    (P.map (Arrangement.inclusion (𝒜.deletion_le H)))
  simp only [word_map, List.length_map] at h
  exact h

/-- Moving the deleted generator through an old prefix gives a contextual formula in the
module cokernel, with the sign recorded explicitly. -/
theorem cokernelMk_generator_word_append_cons (P : List (𝒜.deletion H))
    (K : 𝒜.deletion H) (T : List (𝒜.deletion H)) :
    cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ K :: T)) =
      (P.length : ℤ).negOnePow • cokernelMk B 𝒜 H
        (word (oldGenerator B 𝒜 H) P *
          (generator B 𝒜 H * oldGenerator B 𝒜 H K) * word (oldGenerator B 𝒜 H) T) := by
  rw [word_append, word_cons]
  calc
    _ = cokernelMk B 𝒜 H ((generator B 𝒜 H * word (oldGenerator B 𝒜 H) P) *
        oldGenerator B 𝒜 H K * word (oldGenerator B 𝒜 H) T) := by
      congr 1
      simp only [mul_assoc]
    _ = _ := by
      rw [generator_mul_old_word_comm, smul_mul_assoc, smul_mul_assoc, map_zsmul_unit]
      congr 2
      simp only [mul_assoc]

variable [FiniteDimensional k V]

/-- Replacing an old hyperplane by another with the same nonempty trace does not change a
cokernel class, even with arbitrary old word factors on either side. -/
theorem cokernelMk_generator_word_replace (P T : List (𝒜.deletion H))
    (K K' : 𝒜.deletion H)
    (htrace : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
      (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)))
    (hbot : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) :
    cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ K :: T)) =
      cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ K' :: T)) := by
  rw [cokernelMk_generator_word_append_cons, cokernelMk_generator_word_append_cons]
  apply congrArg ((P.length : ℤ).negOnePow • ·)
  apply cokernelMk_mul_mul_eq_of_sub_mem B 𝒜 H
    (word_mem_deletionRange B 𝒜 P) (word_mem_deletionRange B 𝒜 T)
  rw [generator_mul_sub_generator_mul_of_same_trace B 𝒜 H K K' htrace hbot]
  exact Submodule.neg_mem _ (mul_mem_deletionRange B 𝒜 H
    (generator_mem_deletionRange B 𝒜 K) (generator_mem_deletionRange B 𝒜 K'))

omit [FiniteDimensional k V] in
/-- A letter with empty trace kills a word preceded by the deleted generator, regardless of
its position in the old word. -/
theorem cokernelMk_generator_word_eq_zero_of_empty_trace (P T : List (𝒜.deletion H))
    (K : 𝒜.deletion H)
    (hbot : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = ⊥) :
    cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ K :: T)) = 0 := by
  have hmeet : (H : AffineSubspace k V) ⊓ K = ⊥ :=
    (comap_chart_eq_bot_iff (𝒜.isHyperplane H.2).ne_bot).1 hbot
  have hzero : generator B 𝒜 H * oldGenerator B 𝒜 H K = 0 :=
    generator_mul_eq_zero_of_disjoint B 𝒜 H _ hmeet
  rw [cokernelMk_generator_word_append_cons, hzero, mul_zero, zero_mul, map_zero, smul_zero]

/-- Replacing each letter by one with the same nonempty trace preserves the cokernel class.
The common prefix makes the finite sequence of individual replacements explicit. -/
theorem cokernelMk_generator_word_eq_of_forall₂
    {I J : List (𝒜.deletion H)}
    (h : List.Forall₂ (fun K K' : 𝒜.deletion H ↦
      (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
          (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ∧
        (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) I J)
    (P : List (𝒜.deletion H)) :
    cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ I)) =
      cokernelMk B 𝒜 H (generator B 𝒜 H * word (oldGenerator B 𝒜 H) (P ++ J)) := by
  induction h generalizing P with
  | nil => rfl
  | @cons K K' I J hKK' hIJ ih =>
    exact (cokernelMk_generator_word_replace B 𝒜 H P I K K' hKK'.1 hKK'.2).trans
      (by simpa only [List.append_assoc, List.singleton_append] using ih (P ++ [K']))

end OrlikSolomon.OSAlgebra
