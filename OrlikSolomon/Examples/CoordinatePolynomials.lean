/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import OrlikSolomon.Combinatorics.Betti

/-!
# The Poincaré polynomial of a coordinate arrangement

An arrangement whose every subset meets in codimension equal to its cardinality has Poincaré
polynomial `(1 + X)^n`. The coordinate hyperplanes in `k^n` satisfy these hypotheses: the origin
belongs to every intersection, and a coordinate vector witnesses each increase of codimension.
This calculation includes dimension zero and every base field.

Blueprint: the coordinate-arrangement regression for `def:polynomials`.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u v

namespace OrlikSolomon

namespace Arrangement

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-- An arrangement with nonempty intersections of the expected codimension has Poincaré
polynomial `(1 + X)^n`, where `n` is its number of hyperplanes. -/
theorem poincarePolynomial_of_boolean (𝒜 : Arrangement k V)
    (hne : ∀ S ⊆ 𝒜.hyperplanes, sInf (S : Set (AffineSubspace k V)) ≠ ⊥)
    (hcodim : ∀ S ⊆ 𝒜.hyperplanes, codim (sInf (S : Set (AffineSubspace k V))) = S.card) :
    𝒜.poincarePolynomial = (1 + Polynomial.X) ^ 𝒜.hyperplanes.card := by
  classical
  rw [poincarePolynomial, intersectionSum]
  calc
    _ = ∑ S ∈ 𝒜.hyperplanes.powerset, (Polynomial.X : ℤ[X]) ^ S.card := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsub := Finset.mem_powerset.1 hS
      rw [poincareWeight_of_ne_bot (hne S hsub), hcodim S hsub, zsmul_eq_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_pow]
      simp
    _ = (1 + Polynomial.X) ^ 𝒜.hyperplanes.card := by
      simpa using (Finset.prod_one_add (f := fun _ : AffineSubspace k V ↦
        (Polynomial.X : ℤ[X])) 𝒜.hyperplanes).symm

end Arrangement

namespace Examples

variable (k : Type (max u v)) [Field k] {ι : Type v}

/-- The coordinate hyperplane on which the `i`th coordinate vanishes. -/
def coordinateHyperplane (i : ι) : AffineSubspace k (ι → k) :=
  zeroLocus (LinearMap.proj i : (ι → k) →ₗ[k] k).toAffineMap

@[simp]
theorem mem_coordinateHyperplane (i : ι) (x : ι → k) :
    x ∈ coordinateHyperplane k i ↔ x i = 0 := by
  simp [coordinateHyperplane]

/-- A coordinate equation has a nonzero linear part, over every field. -/
theorem isHyperplane_coordinateHyperplane (i : ι) : IsHyperplane (coordinateHyperplane k i) := by
  classical
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have := congrArg (fun f : (ι → k) →ₗ[k] k ↦ f (Pi.single i 1)) h
  simp at this

/-- Distinct coordinates determine distinct hyperplanes. -/
theorem coordinateHyperplane_injective : Function.Injective (coordinateHyperplane k (ι := ι)) := by
  classical
  intro i j h
  by_contra hij
  have hi : Pi.single i (1 : k) ∈ coordinateHyperplane k j := by simp [hij]
  rw [← h] at hi
  simp at hi

open scoped Classical in
/-- Every intersection of coordinate hyperplanes contains the origin. -/
theorem coordinateHyperplane_sInf_ne_bot (S : Finset ι) :
    sInf (↑(S.image (coordinateHyperplane k)) : Set (AffineSubspace k (ι → k))) ≠ ⊥ := by
  classical
  apply (AffineSubspace.nonempty_iff_ne_bot _).1
  refine ⟨0, ?_⟩
  simp

open scoped Classical in
/-- An intersection of distinct coordinate hyperplanes has codimension equal to the number
of coordinates constrained. -/
theorem codim_sInf_coordinateHyperplane [Finite ι] (S : Finset ι) :
    codim (sInf (↑(S.image (coordinateHyperplane k)) : Set (AffineSubspace k (ι → k)))) =
      S.card := by
  classical
  let := Fintype.ofFinite ι
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.image_insert, Finset.coe_insert, sInf_insert]
    have hnot : ¬ sInf (↑(S.image (coordinateHyperplane k)) :
        Set (AffineSubspace k (ι → k))) ≤ coordinateHyperplane k i := by
      intro hle
      have hmem : Pi.single i (1 : k) ∈ sInf (↑(S.image (coordinateHyperplane k)) :
          Set (AffineSubspace k (ι → k))) := by
        simp only [AffineSubspace.mem_sInf_iff, Finset.mem_coe, Finset.mem_image,
          forall_exists_index, and_imp]
        intro H j hj hH
        subst H
        simp [ne_of_mem_of_not_mem hj hi]
      have := hle hmem
      simp at this
    have hne : coordinateHyperplane k i ⊓
        sInf (↑(S.image (coordinateHyperplane k)) : Set (AffineSubspace k (ι → k))) ≠ ⊥ := by
      simpa only [Finset.image_insert, Finset.coe_insert, sInf_insert] using
        coordinateHyperplane_sInf_ne_bot k (insert i S)
    rw [(isHyperplane_coordinateHyperplane k i).codim_inf hne hnot, ih,
      Finset.card_insert_of_notMem hi]

open scoped Classical in
/-- All coordinate hyperplanes in the finite-dimensional affine space `k^ι`. -/
def coordinateArrangement (ι : Type v) [Fintype ι] : Arrangement k (ι → k) :=
  Arrangement.ofFinset (Finset.univ.image (coordinateHyperplane k))

open scoped Classical in
/-- Every coordinate equation contributes one hyperplane to the coordinate arrangement. -/
@[simp]
theorem hyperplanes_coordinateArrangement [Fintype ι] :
    (coordinateArrangement k ι).hyperplanes = Finset.univ.image (coordinateHyperplane k) := by
  ext H
  simp only [Arrangement.mem_hyperplanes, coordinateArrangement, Arrangement.mem_ofFinset,
    and_iff_left_iff_imp, Finset.mem_image]
  rintro ⟨i, _, rfl⟩
  exact isHyperplane_coordinateHyperplane k i

/-- The coordinate arrangement has one hyperplane for each coordinate. -/
@[simp]
theorem card_coordinateArrangement [Fintype ι] :
    (coordinateArrangement k ι).card = Fintype.card ι := by
  classical
  rw [← Arrangement.card_hyperplanes, hyperplanes_coordinateArrangement,
    Finset.card_image_of_injective _ (coordinateHyperplane_injective k), Finset.card_univ]

/-- The Poincaré polynomial of all coordinate hyperplanes in `k^ι` is `(1 + X)^|ι|`.
The formula holds in dimension zero and over every field.

Blueprint: the coordinate-arrangement regression for `def:polynomials`. -/
theorem poincarePolynomial_coordinateArrangement [Fintype ι] :
    (coordinateArrangement k ι).poincarePolynomial =
      (1 + Polynomial.X) ^ Fintype.card ι := by
  classical
  rw [← card_coordinateArrangement k, ← Arrangement.card_hyperplanes]
  apply Arrangement.poincarePolynomial_of_boolean
  · intro S hS
    rw [hyperplanes_coordinateArrangement] at hS
    obtain ⟨T, rfl⟩ := Finset.subset_univ_image_iff.1 hS
    exact coordinateHyperplane_sInf_ne_bot k T
  · intro S hS
    rw [hyperplanes_coordinateArrangement] at hS
    obtain ⟨T, rfl⟩ := Finset.subset_univ_image_iff.1 hS
    rw [codim_sInf_coordinateHyperplane,
      Finset.card_image_of_injective _ (coordinateHyperplane_injective k)]

/-- The standard coordinate arrangement in affine `n`-space has polynomial `(1 + X)^n`. -/
theorem poincarePolynomial_coordinate_fin (k : Type u) [Field k] (n : ℕ) :
    (coordinateArrangement k (Fin n)).poincarePolynomial = (1 + Polynomial.X) ^ n := by
  simpa only [Fintype.card_fin] using poincarePolynomial_coordinateArrangement k (ι := Fin n)

end Examples

end OrlikSolomon
