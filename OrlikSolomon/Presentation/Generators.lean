/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import OrlikSolomon.Presentation.Basic

/-!
# Independence of Orlik–Solomon generators

Square-zero extension targets detect degree-one generators before the cohomology structure
theorem. Distinct generators of a pairwise disjoint arrangement have nonzero difference, even
without a finite-dimensional ambient hypothesis. In finite dimension all generators are linearly
independent.

Blueprint: the degree-one assertion in the blueprint's proof of `cor:projective-betti`.
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

/-! ### All degree-one generators in finite dimension -/

/-- A dependent list of distinct affine hyperplanes has at least three members. The
nonempty-intersection guard rules out parallel pairs. -/
theorem dependent_length_ge_three [FiniteDimensional k V] {I : List 𝒜}
    (hI : I.Nodup) (hdep : Arrangement.IsDependent I) : 3 ≤ I.length := by
  cases I with
  | nil => exact (Arrangement.isDependent_nil 𝒜 hdep).elim
  | cons H I =>
    cases I with
    | nil =>
      have hlt := hdep.2
      simp [𝒜.isHyperplane H.2 |>.codim_eq_one] at hlt
    | cons K I =>
      cases I with
      | nil =>
        have hne : (K : AffineSubspace k V) ≠ H := by
          intro h
          have hmem : H ∈ [K] := by simp [Subtype.ext h]
          exact (List.nodup_cons.1 hI).1 hmem
        have hc := (𝒜.isHyperplane H.2).codim_inf_eq_two (𝒜.isHyperplane K.2) hne
          (by simpa using hdep.1)
        have hlt := hdep.2
        simp [hc] at hlt
      | cons L I => simp

private def squareZeroGenerator (H : 𝒜) : TrivSqZeroExt B (𝒜 →₀ B) :=
  TrivSqZeroExt.inr (Finsupp.single H 1)

private theorem squareZero_word {I : List 𝒜} (hI : 2 ≤ I.length) :
    word (squareZeroGenerator B 𝒜) I = 0 := by
  cases I with
  | nil => simp at hI
  | cons H I =>
    cases I with
    | nil => simp at hI
    | cons K I => simp [word_cons, squareZeroGenerator, ← mul_assoc]

private theorem squareZero_boundary {I : List 𝒜} (hI : 3 ≤ I.length) :
    wordBoundary (squareZeroGenerator B 𝒜) I = 0 := by
  cases I with
  | nil => simp at hI
  | cons H I =>
    cases I with
    | nil => simp at hI
    | cons K I =>
      cases I with
      | nil => simp at hI
      | cons L I =>
        simp [wordBoundary_cons, word_cons, squareZeroGenerator, mul_sub, ← mul_assoc]

private theorem isFamily_squareZeroGenerator [FiniteDimensional k V] :
    IsFamily 𝒜 (squareZeroGenerator B 𝒜) where
  mul_self _ := by simp [squareZeroGenerator]
  mul_add_mul_swap_of_ne _ := by simp [squareZeroGenerator]
  word_eq_zero I _ hi := by
    cases I with
    | nil => simp at hi
    | cons H I =>
      cases I with
      | nil => exact ((𝒜.isHyperplane H.2).ne_bot (by simpa using hi)).elim
      | cons K I => exact squareZero_word B 𝒜 (by simp)
  wordBoundary_eq_zero I hi hd :=
    squareZero_boundary B 𝒜 (dependent_length_ge_three 𝒜 hi hd)

/-- The degree-one generators are linearly independent over every commutative coefficient ring.
A square-zero extension of the free module detects their coefficients, without using the
cohomology structure theorem or assuming that two is invertible.

Blueprint: the degree-one assertion in the blueprint's proof of `cor:projective-betti`. -/
theorem linearIndependent_generator [FiniteDimensional k V] :
    LinearIndependent B (generator B 𝒜) := by
  let f : OSAlgebra B 𝒜 →ₐ[B] TrivSqZeroExt B (𝒜 →₀ B) :=
    lift (squareZeroGenerator B 𝒜) (isFamily_squareZeroGenerator B 𝒜)
  let g := (TrivSqZeroExt.sndHom B (𝒜 →₀ B)).comp f.toLinearMap
  apply LinearIndependent.of_comp g
  convert Finsupp.linearIndependent_single_one (R := B) (ι := 𝒜) using 1
  ext H
  simp [g, f, squareZeroGenerator]

end OSAlgebra

end OrlikSolomon
