/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Basic

/-!
# Relations for arbitrary restriction representatives

Any choice of old hyperplanes with the prescribed traces gives the same identities controlling
the linear restriction lift. Empty restricted intersections give zero products after adjoining
the deleted hyperplane. A nonempty dependent restricted family gives the identity
`e_H ∂e_I = e_I`. Two old hyperplanes with the same nonempty trace satisfy the boundary and
product relations for their triple with `H`.

These identities hold over every commutative coefficient ring, including the zero ring and rings
of characteristic two. No representative choice is fixed by the statements.

Blueprint: `lem:representatives`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (B : Type v) [CommRing B] (𝒜 : Arrangement k V)

private theorem comap_inter_map_of_representatives (H : 𝒜)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    (I : List (𝒜.restriction H)) :
    (Arrangement.inter (I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r))).comap
        (chart (H : AffineSubspace k V)) = Arrangement.inter I := by
  induction I with
  | nil => simp [AffineSubspace.comap_top]
  | cons L I ih =>
    simp only [List.map_cons, Arrangement.inter_cons, AffineSubspace.comap_inf,
      Function.comp_apply, Arrangement.coe_inclusion, hr, ih]

private theorem inter_cons_map_of_representatives (H : 𝒜)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    (I : List (𝒜.restriction H)) :
    Arrangement.inter (H :: I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r)) =
      (Arrangement.inter I).map (chart (H : AffineSubspace k V)) := by
  rw [Arrangement.inter_cons, ← map_chart_comap_chart (𝒜.isHyperplane H.2).ne_bot,
    comap_inter_map_of_representatives 𝒜 H r hr]

/-- Adjoining `H` to arbitrary representatives of an empty restricted intersection gives an
empty-intersection product relation. Blueprint: `lem:representatives`. -/
theorem generator_mul_word_representatives_eq_zero (H : 𝒜)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    {I : List (𝒜.restriction H)} (hI : Arrangement.inter I = ⊥) :
    generator B 𝒜 H *
        word (fun L ↦ generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) (r L))) I = 0 := by
  have hinter : Arrangement.inter
      (H :: I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r)) = ⊥ := by
    rw [inter_cons_map_of_representatives 𝒜 H r hr, hI, AffineSubspace.map_bot]
  simpa only [word_cons, word_map, Function.comp_apply] using
    word_eq_zero_of_inter_eq_bot B 𝒜 hinter

/-- Adjoining `H` to arbitrary representatives of a nonempty dependent restricted family gives
`e_H ∂e_I = e_I`. Blueprint: `lem:representatives`. -/
theorem generator_mul_wordBoundary_representatives [FiniteDimensional k V] (H : 𝒜)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L)
    {I : List (𝒜.restriction H)} (hI : Arrangement.IsDependent I) :
    generator B 𝒜 H *
        wordBoundary (fun L ↦ generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) (r L))) I =
      word (fun L ↦ generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) (r L))) I := by
  have hinter : Arrangement.inter
      (H :: I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r)) ≠ ⊥ := by
    rw [inter_cons_map_of_representatives 𝒜 H r hr]
    exact (AffineSubspace.map_eq_bot_iff _).not.mpr hI.1
  have hcodim : codim (Arrangement.inter
      (H :: I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r))) =
      codim (Arrangement.inter I) + 1 := by
    rw [inter_cons_map_of_representatives 𝒜 H r hr, codim_map_chart,
      (𝒜.isHyperplane H.2).codim_eq_one]
  have hdep : Arrangement.IsDependent
      (H :: I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r)) := by
    refine ⟨hinter, ?_⟩
    rw [hcodim, List.length_cons, List.length_map]
    exact Nat.add_lt_add_right hI.2 1
  have h := wordBoundary_eq_zero_of_isDependent B 𝒜 hdep
  simp only [wordBoundary_cons, word_map, wordBoundary_map, Function.comp_apply] at h
  exact (sub_eq_zero.mp h).symm

/-- Two old hyperplanes with the same nonempty trace satisfy the boundary relation of their
triple with `H`. The statement also allows the two old hyperplanes to agree.
Blueprint: `lem:representatives`. -/
theorem generator_boundary_triple_of_same_trace [FiniteDimensional k V] (H : 𝒜)
    (K K' : 𝒜.deletion H)
    (htrace : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
      (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)))
    (hbot : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) :
    generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) *
          generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') -
        generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') +
        generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) = 0 := by
  have hH := 𝒜.isHyperplane H.2
  have hne : (K : AffineSubspace k V) ≠ H := (Arrangement.mem_deletion.1 K.2).1
  have hmeet : (H : AffineSubspace k V) ⊓ K ≠ ⊥ :=
    (comap_chart_eq_bot_iff hH.ne_bot).not.mp hbot
  have heq : (H : AffineSubspace k V) ⊓ K = (H : AffineSubspace k V) ⊓ K' :=
    (comap_chart_eq_comap_chart_iff hH.ne_bot).mp htrace
  have hinter : (H : AffineSubspace k V) ⊓ ((K : AffineSubspace k V) ⊓ K') =
      (H : AffineSubspace k V) ⊓ K := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    refine le_inf inf_le_left (le_inf inf_le_right ?_)
    rw [heq]
    exact inf_le_right
  have hcodim : codim ((H : AffineSubspace k V) ⊓ K) = 2 :=
    hH.codim_inf_eq_two (𝒜.isHyperplane ((𝒜.deletion_le H) K.2)) hne hmeet
  have hdep : Arrangement.IsDependent
      [H, Arrangement.inclusion (𝒜.deletion_le H) K,
        Arrangement.inclusion (𝒜.deletion_le H) K'] := by
    constructor
    · simpa only [Arrangement.inter_cons, Arrangement.inter_nil, Arrangement.coe_inclusion,
        inf_top_eq, hinter] using hmeet
    · simpa only [Arrangement.inter_cons, Arrangement.inter_nil, Arrangement.coe_inclusion,
        inf_top_eq, hinter, hcodim, List.length_cons, List.length_nil] using (by decide : 2 < 3)
  simpa only [wordBoundary_triple] using wordBoundary_eq_zero_of_isDependent B 𝒜 hdep

/-- Changing a representative changes `e_H e_K` by the old product `-e_K e_K'`.
Blueprint: `lem:representatives`. -/
theorem generator_mul_sub_generator_mul_of_same_trace [FiniteDimensional k V] (H : 𝒜)
    (K K' : 𝒜.deletion H)
    (htrace : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
      (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)))
    (hbot : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) :
    generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) -
        generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') =
      -(generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) *
        generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K')) := by
  have h := generator_boundary_triple_of_same_trace B 𝒜 H K K' htrace hbot
  apply eq_neg_of_add_eq_zero_left
  calc
    _ = generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) *
          generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') -
        generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') +
        generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) := by abel
    _ = 0 := h

/-- The product of `H` and two old hyperplanes with the same nonempty trace vanishes.
Blueprint: `lem:representatives`. -/
theorem generator_mul_generator_mul_generator_of_same_trace [FiniteDimensional k V] (H : 𝒜)
    (K K' : 𝒜.deletion H)
    (htrace : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) =
      (K' : AffineSubspace k V).comap (chart (H : AffineSubspace k V)))
    (hbot : (K : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) ≠ ⊥) :
    generator B 𝒜 H * generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K) *
        generator B 𝒜 (Arrangement.inclusion (𝒜.deletion_le H) K') = 0 := by
  have h := congrArg (generator B 𝒜 H * ·)
    (generator_boundary_triple_of_same_trace B 𝒜 H K K' htrace hbot)
  simpa only [mul_add, mul_sub, ← mul_assoc, generator_mul_self, zero_mul, sub_zero,
    add_zero, mul_zero] using h

end OrlikSolomon.OSAlgebra
