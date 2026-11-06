/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Nat.Choose.Sum
public import OrlikSolomon.Combinatorics.Betti

/-!
# The intersection poset and Möbius formulas

The nonempty intersections of subsets of an affine arrangement form a finite poset under reverse
inclusion, with the ambient space as its least element. Grouping the alternating subset sum by
intersection identifies its coefficients with Mathlib's incidence-algebra Möbius function.

* `Arrangement.IntersectionPoset` is the poset of nonempty intersections.
* `Arrangement.IntersectionPoset.mobius` is the integer Möbius function from the ambient space.
* `Arrangement.intersectionCoefficient_eq_mobius` identifies grouped subset coefficients.
* `Arrangement.intersectionSum_eq_sum_mobius` holds for any additive intersection weight.
* `Arrangement.characteristicPolynomial_eq_sum_mobius` and
  `Arrangement.natCast_bettiNumber_eq_sum_mobius` are the two blueprint formulas.

Blueprint: `lem:mobius`.
-/

@[expose] public section

noncomputable section

open Finset Module

universe u

namespace OrlikSolomon.Arrangement

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-- The finite set of nonempty intersections of subsets of the arrangement, including the
ambient space as the intersection of the empty subset. -/
def intersectionFlats (𝒜 : Arrangement k V) : Finset (AffineSubspace k V) := by
  classical
  exact (𝒜.hyperplanes.powerset.image
    fun S : Finset (AffineSubspace k V) => sInf (S : Set _)).erase ⊥

/-- A flat is a nonempty intersection of a subset of the arrangement. -/
theorem mem_intersectionFlats {𝒜 : Arrangement k V} {X : AffineSubspace k V} :
    X ∈ 𝒜.intersectionFlats ↔ X ≠ ⊥ ∧
      ∃ S : Finset (AffineSubspace k V), S ⊆ 𝒜.hyperplanes ∧ sInf (S : Set _) = X := by
  classical
  simp only [intersectionFlats, mem_erase, mem_image, mem_powerset]

/-- The empty affine subspace is excluded from the intersection poset. -/
@[simp]
theorem bot_notMem_intersectionFlats (𝒜 : Arrangement k V) :
    (⊥ : AffineSubspace k V) ∉ 𝒜.intersectionFlats :=
  fun h => (mem_intersectionFlats.1 h).1 rfl

/-- The ambient space is always a flat, including for the empty arrangement. -/
@[simp]
theorem top_mem_intersectionFlats (𝒜 : Arrangement k V) :
    (⊤ : AffineSubspace k V) ∈ 𝒜.intersectionFlats :=
  mem_intersectionFlats.2 ⟨top_ne_bot, ∅, empty_subset _, by simp⟩

/-- The empty arrangement has just the ambient flat, in every dimension. -/
@[simp]
theorem intersectionFlats_empty :
    (∅ : Arrangement k V).intersectionFlats = {⊤} := by
  classical
  simp [intersectionFlats]

/-- The nonempty intersection poset, ordered by reverse inclusion. Its least element is the
ambient space, not the empty affine subspace. Blueprint: `lem:mobius`. -/
def IntersectionPoset (𝒜 : Arrangement k V) :=
  {X : AffineSubspace k V // X ∈ 𝒜.intersectionFlats}ᵒᵈ

namespace IntersectionPoset

variable (𝒜 : Arrangement k V)

instance : PartialOrder 𝒜.IntersectionPoset :=
  inferInstanceAs (PartialOrder {X : AffineSubspace k V // X ∈ 𝒜.intersectionFlats}ᵒᵈ)

instance : Fintype 𝒜.IntersectionPoset := by
  classical
  exact inferInstanceAs (Fintype {X : AffineSubspace k V // X ∈ 𝒜.intersectionFlats}ᵒᵈ)

instance : LocallyFiniteOrder 𝒜.IntersectionPoset := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The affine subspace represented by an intersection-poset element. -/
def carrier (X : 𝒜.IntersectionPoset) : AffineSubspace k V := X.1

variable {𝒜}

/-- Distinct elements of the intersection poset represent distinct affine subspaces. -/
theorem carrier_injective : Function.Injective (carrier (𝒜 := 𝒜)) :=
  fun _ _ h => Subtype.ext h

/-- A flat is determined by its affine subspace. -/
@[ext]
theorem ext {X Y : 𝒜.IntersectionPoset} (h : X.carrier = Y.carrier) : X = Y :=
  carrier_injective h

/-- The represented subspace is a member of the arrangement's finite set of flats. -/
theorem carrier_mem_intersectionFlats (X : 𝒜.IntersectionPoset) :
    X.carrier ∈ 𝒜.intersectionFlats := X.2

/-- The order on flats is reverse inclusion of their affine subspaces. -/
@[simp]
theorem le_iff {X Y : 𝒜.IntersectionPoset} : X ≤ Y ↔ Y.carrier ≤ X.carrier := Iff.rfl

/-- All elements represent nonempty affine subspaces. -/
theorem carrier_ne_bot (X : 𝒜.IntersectionPoset) : X.carrier ≠ ⊥ :=
  (mem_intersectionFlats.1 X.2).1

instance : OrderBot 𝒜.IntersectionPoset where
  bot := ⟨⊤, top_mem_intersectionFlats 𝒜⟩
  bot_le X := show X.carrier ≤ ⊤ from le_top

/-- The least flat represents the ambient space. -/
@[simp]
theorem carrier_bot : (⊥ : 𝒜.IntersectionPoset).carrier = ⊤ := rfl

/-- Equality with the least flat means equality with the ambient affine space. -/
@[simp]
theorem carrier_eq_top {X : 𝒜.IntersectionPoset} : X.carrier = ⊤ ↔ X = ⊥ :=
  ⟨fun h => carrier_injective (h.trans carrier_bot.symm), fun h => h ▸ carrier_bot⟩

/-- Every flat of the empty arrangement is the ambient flat. -/
theorem empty_eq_bot (X : (∅ : Arrangement k V).IntersectionPoset) : X = ⊥ := by
  apply carrier_eq_top.1
  have h := X.carrier_mem_intersectionFlats
  simpa only [intersectionFlats_empty, mem_singleton] using h

instance : Subsingleton (∅ : Arrangement k V).IntersectionPoset :=
  ⟨fun X Y => (empty_eq_bot X).trans (empty_eq_bot Y).symm⟩

/-- A subset with nonempty intersection determines an element of the intersection poset. -/
def ofSubset (S : Finset (AffineSubspace k V)) (hS : S ⊆ 𝒜.hyperplanes)
    (hne : sInf (S : Set (AffineSubspace k V)) ≠ ⊥) : 𝒜.IntersectionPoset :=
  ⟨sInf (S : Set _), mem_intersectionFlats.2 ⟨hne, S, hS, rfl⟩⟩

@[simp]
theorem carrier_ofSubset (S : Finset (AffineSubspace k V)) (hS : S ⊆ 𝒜.hyperplanes)
    (hne : sInf (S : Set (AffineSubspace k V)) ≠ ⊥) :
    (ofSubset S hS hne).carrier = sInf (S : Set _) := rfl

/-- The integer Möbius function from the ambient space to a nonempty intersection.
Blueprint: `lem:mobius`. -/
def mobius (X : 𝒜.IntersectionPoset) : ℤ := by
  classical
  exact IncidenceAlgebra.mu ℤ ⊥ X

/-- The ambient Möbius coefficient is one. -/
@[simp]
theorem mobius_bot : mobius (⊥ : 𝒜.IntersectionPoset) = 1 := by
  classical
  exact IncidenceAlgebra.mu_self _

/-- The usual Möbius recursion on proper flats. -/
theorem mobius_eq_neg_sum_Iio {X : 𝒜.IntersectionPoset} (hX : X ≠ ⊥) :
    X.mobius = -∑ Y ∈ Iio X, Y.mobius := by
  classical
  simpa only [Ico_bot, mobius] using
    (IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (𝕜 := ℤ) hX.symm)

end IntersectionPoset

/-- The alternating coefficient of subsets having a given intersection. -/
def intersectionCoefficient (𝒜 : Arrangement k V) (X : AffineSubspace k V) : ℤ := by
  classical
  exact ∑ S ∈ 𝒜.hyperplanes.powerset,
    if sInf (S : Set (AffineSubspace k V)) = X then (-1 : ℤ) ^ S.card else 0

open scoped Classical in
private theorem powerset_filter_inter_ge (𝒜 : Arrangement k V) (X : AffineSubspace k V) :
    𝒜.hyperplanes.powerset.filter
        (fun S : Finset (AffineSubspace k V) => X ≤ sInf (S : Set _)) =
      (𝒜.hyperplanes.filter (fun H => X ≤ H)).powerset := by
  ext S
  simp only [mem_filter, mem_powerset, le_sInf_iff, mem_coe]
  constructor
  · rintro ⟨hS, hX⟩ H hH
    exact mem_filter.2 ⟨hS hH, hX H hH⟩
  · intro hS
    exact ⟨fun H hH => (mem_filter.1 (hS hH)).1,
      fun H hH => (mem_filter.1 (hS hH)).2⟩

open scoped Classical in
private theorem sum_Iic_inter_indicator (𝒜 : Arrangement k V) (X : 𝒜.IntersectionPoset)
    (S : Finset (AffineSubspace k V)) (hS : S ⊆ 𝒜.hyperplanes) (a : ℤ) :
    (∑ Y ∈ Iic X, if sInf (S : Set _) = Y.carrier then a else 0) =
      if X.carrier ≤ sInf (S : Set _) then a else 0 := by
  by_cases hle : X.carrier ≤ sInf (S : Set _)
  · have hne : sInf (S : Set (AffineSubspace k V)) ≠ ⊥ :=
      fun h => X.carrier_ne_bot (le_bot_iff.1 (h ▸ hle))
    let Y := IntersectionPoset.ofSubset S hS hne
    have hY : Y ∈ Iic X := mem_Iic.2 hle
    rw [ite_eq_left hle, sum_eq_single Y]
    · simp [Y]
    · intro Z _ hZY
      apply ite_eq_right
      intro h
      exact hZY (IntersectionPoset.carrier_injective h.symm)
    · exact fun h => (h hY).elim
  · rw [ite_eq_right hle]
    apply sum_eq_zero
    intro Y hY
    apply ite_eq_right
    intro h
    exact hle (h ▸ (IntersectionPoset.le_iff.1 (mem_Iic.1 hY)))

open scoped Classical in
private theorem containing_hyperplanes_eq_empty_iff (𝒜 : Arrangement k V)
    (X : 𝒜.IntersectionPoset) :
    𝒜.hyperplanes.filter (fun H => X.carrier ≤ H) = ∅ ↔ X = ⊥ := by
  constructor
  · intro h
    obtain ⟨S, hS, hSX⟩ := (mem_intersectionFlats.1 X.2).2
    change sInf (S : Set (AffineSubspace k V)) = X.carrier at hSX
    have hS0 : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro H hH
      have hle : X.carrier ≤ H := hSX ▸ sInf_le (show H ∈ (S : Set _) from hH)
      have := mem_filter.2 ⟨hS hH, hle⟩
      rw [h] at this
      exact notMem_empty H this
    apply IntersectionPoset.carrier_eq_top.1
    rw [← hSX, hS0]
    simp
  · rintro rfl
    apply filter_eq_empty_iff.2
    intro H hH hle
    exact (𝒜.isHyperplane hH).ne_top (top_le_iff.1 hle)

open scoped Classical in
/-- Summing the grouped coefficients over flats containing `X` gives one for the ambient flat
and zero otherwise. These are the defining Möbius equations. -/
theorem sum_Iic_intersectionCoefficient (𝒜 : Arrangement k V) (X : 𝒜.IntersectionPoset) :
    (∑ Y ∈ Iic X, 𝒜.intersectionCoefficient Y.carrier) = if X = ⊥ then 1 else 0 := by
  simp only [intersectionCoefficient]
  rw [sum_comm]
  have hsum : (∑ S ∈ 𝒜.hyperplanes.powerset,
      ∑ Y ∈ Iic X, if sInf (S : Set _) = Y.carrier then (-1 : ℤ) ^ S.card else 0) =
      ∑ S ∈ 𝒜.hyperplanes.powerset,
        if X.carrier ≤ sInf (S : Set _) then (-1 : ℤ) ^ S.card else 0 := by
    apply sum_congr rfl
    intro S hS
    exact sum_Iic_inter_indicator 𝒜 X S (mem_powerset.1 hS) _
  rw [hsum, ← sum_filter, powerset_filter_inter_ge, sum_powerset_neg_one_pow_card]
  simp only [containing_hyperplanes_eq_empty_iff]

/-- The coefficient obtained by grouping subsets by their intersection is the usual Möbius
function on the finite nonempty intersection poset. Blueprint: `lem:mobius`. -/
theorem intersectionCoefficient_eq_mobius (𝒜 : Arrangement k V) (X : 𝒜.IntersectionPoset) :
    𝒜.intersectionCoefficient X.carrier = X.mobius := by
  classical
  have h := IncidenceAlgebra.moebius_inversion_bot
    (fun Y : 𝒜.IntersectionPoset => 𝒜.intersectionCoefficient Y.carrier)
    (fun Y => if Y = ⊥ then (1 : ℤ) else 0)
    (fun Y => (sum_Iic_intersectionCoefficient 𝒜 Y).symm) X
  simpa [IntersectionPoset.mobius] using h

/-- Group an arbitrary intersection weight by its nonempty intersection. The value at the empty
affine subspace must vanish, as it does in the defining polynomial sums. -/
theorem intersectionSum_eq_sum_intersectionCoefficient {M : Type*} [AddCommGroup M]
    (𝒜 : Arrangement k V) (w : AffineSubspace k V → M) (hw : w ⊥ = 0) :
    𝒜.intersectionSum w =
      ∑ X : 𝒜.IntersectionPoset, (𝒜.intersectionCoefficient X.carrier) • w X.carrier := by
  classical
  unfold intersectionSum intersectionCoefficient
  simp_rw [Finset.sum_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  by_cases hne : sInf (S : Set (AffineSubspace k V)) = ⊥
  · rw [hne, hw, smul_zero]
    symm
    apply sum_eq_zero
    intro X _
    rw [ite_eq_right (fun h => X.carrier_ne_bot h.symm), zero_smul]
  · let X := IntersectionPoset.ofSubset S (mem_powerset.1 hS) hne
    symm
    rw [sum_eq_single X]
    · simp [X]
    · intro Y _ hYX
      rw [ite_eq_right (fun h => hYX (IntersectionPoset.carrier_injective h.symm)), zero_smul]
    · simp

/-- The intersection-weight form of the Möbius formula. It holds without finite-dimensionality
and for weights in any additive commutative group. Blueprint: `lem:mobius`. -/
theorem intersectionSum_eq_sum_mobius {M : Type*} [AddCommGroup M]
    (𝒜 : Arrangement k V) (w : AffineSubspace k V → M) (hw : w ⊥ = 0) :
    𝒜.intersectionSum w = ∑ X : 𝒜.IntersectionPoset, X.mobius • w X.carrier := by
  rw [intersectionSum_eq_sum_intersectionCoefficient 𝒜 w hw]
  simp_rw [intersectionCoefficient_eq_mobius]

/-- The characteristic polynomial is the dimension-weighted sum of the intersection-poset
Möbius coefficients. Blueprint: `lem:mobius`. -/
theorem characteristicPolynomial_eq_sum_mobius (𝒜 : Arrangement k V) :
    𝒜.characteristicPolynomial = ∑ X : 𝒜.IntersectionPoset,
      Polynomial.C X.mobius * Polynomial.X ^ finrank k X.carrier.direction := by
  rw [characteristicPolynomial, intersectionSum_eq_sum_mobius 𝒜 _ characteristicWeight_bot]
  apply sum_congr rfl
  intro X _
  simp [characteristicWeight_of_ne_bot X.carrier_ne_bot, zsmul_eq_mul]

/-- The Poincaré polynomial is the signed codimension-weighted sum of Möbius coefficients.
Blueprint: `lem:mobius`. -/
theorem poincarePolynomial_eq_sum_mobius (𝒜 : Arrangement k V) :
    𝒜.poincarePolynomial = ∑ X : 𝒜.IntersectionPoset,
      Polynomial.C X.mobius * (-Polynomial.X) ^ codim X.carrier := by
  rw [poincarePolynomial, intersectionSum_eq_sum_mobius 𝒜 _ poincareWeight_bot]
  apply sum_congr rfl
  intro X _
  simp [poincareWeight_of_ne_bot X.carrier_ne_bot, zsmul_eq_mul]

open scoped Classical in
/-- The integer Betti coefficient is the signed sum of the Möbius coefficients of flats of the
given codimension. Blueprint: `lem:mobius`. -/
theorem poincarePolynomial_coeff_eq_sum_mobius (𝒜 : Arrangement k V) (q : ℕ) :
    𝒜.poincarePolynomial.coeff q = (-1 : ℤ) ^ q *
      ∑ X : 𝒜.IntersectionPoset with codim X.carrier = q, X.mobius := by
  rw [poincarePolynomial_eq_sum_mobius, Polynomial.finsetSum_coeff, Finset.mul_sum, sum_filter]
  have hpow (n : ℕ) : (-Polynomial.X : Polynomial ℤ) ^ n =
      Polynomial.C ((-1 : ℤ) ^ n) * Polynomial.X ^ n := by
    rw [neg_pow]
    simp only [map_pow, map_neg, map_one]
  apply sum_congr rfl
  intro X _
  by_cases h : codim X.carrier = q
  · rw [hpow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    simp [h, mul_comm]
  · rw [hpow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    simp only [Ne.symm h, ite_false, h]

open scoped Classical in
/-- The natural Betti number, cast back to integers, is the signed Möbius sum. Its equality with
the integer coefficient uses the already proved nonnegativity, never a rank argument.
Blueprint: `lem:mobius`. -/
theorem natCast_bettiNumber_eq_sum_mobius [FiniteDimensional k V]
    (𝒜 : Arrangement k V) (q : ℕ) :
    (𝒜.bettiNumber q : ℤ) = (-1 : ℤ) ^ q *
      ∑ X : 𝒜.IntersectionPoset with codim X.carrier = q, X.mobius := by
  rw [natCast_bettiNumber, poincarePolynomial_coeff_eq_sum_mobius]

open scoped Classical in
/-- No flats contribute above the ambient dimension. This includes degree-positive sums in
dimension zero and does not require choosing a point in a complement. -/
theorem sum_mobius_eq_zero_of_finrank_lt [FiniteDimensional k V]
    (𝒜 : Arrangement k V) {q : ℕ} (hq : finrank k V < q) :
    (∑ X : 𝒜.IntersectionPoset with codim X.carrier = q, X.mobius) = 0 := by
  apply sum_eq_zero
  intro X hX
  have hcodim := (mem_filter.1 hX).2
  have hle := codim_le_finrank X.carrier
  omega

/-- The Möbius coefficient of the only flat in an empty arrangement is one. -/
@[simp]
theorem IntersectionPoset.mobius_empty (X : (∅ : Arrangement k V).IntersectionPoset) :
    X.mobius = 1 := by
  rw [IntersectionPoset.empty_eq_bot X, IntersectionPoset.mobius_bot]

end OrlikSolomon.Arrangement
