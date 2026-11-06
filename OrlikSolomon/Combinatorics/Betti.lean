/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import OrlikSolomon.Combinatorics.AlternatingSum
public import OrlikSolomon.Geometry.Arrangement

/-!
# Subset polynomials of affine arrangements

The characteristic and Poincaré polynomials are alternating sums over subsets with nonempty
intersection. Dimensions and codimensions are natural numbers, and empty intersections are
discarded before taking either. Both polynomials have integer coefficients.

* `Arrangement.characteristicPolynomial_eq_sum` and `Arrangement.poincarePolynomial_eq_sum` give
  the explicit subset formulas.
* `Arrangement.intersectionSum_deletion_restriction` handles arbitrary intersection weights,
  including empty and repeated traces.
* `Arrangement.characteristicPolynomial_deletion_restriction` and
  `Arrangement.poincarePolynomial_deletion_restriction` give the two polynomial recurrences.
* `Arrangement.poincarePolynomial_coeff_nonneg` proves nonnegativity before `bettiNumber` is
  defined. Comparing those coefficients with cohomology is a separate result.

Blueprint: `def:polynomials`, `lem:polynomial-recursion`.
-/

@[expose] public section

open Module Polynomial

namespace OrlikSolomon

universe u

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

open scoped Classical in
/-- Subsets containing the bottom element make no contribution to an intersection weight that
vanishes at bottom. Thus an empty trace can be discarded before taking the alternating sum. -/
theorem sum_powerset_sInf_erase_bot {L M : Type*} [CompleteLattice L] [AddCommGroup M]
    (s : Finset L) (w : L → M) (hw : w ⊥ = 0) :
    (∑ S ∈ s.powerset, ((-1 : ℤ) ^ S.card) • w (sInf (S : Set L))) =
      ∑ S ∈ (s.erase ⊥).powerset, ((-1 : ℤ) ^ S.card) • w (sInf (S : Set L)) := by
  classical
  symm
  apply Finset.sum_subset (Finset.powerset_mono.2 (Finset.erase_subset _ _))
  intro S hS hnot
  have hbot : (⊥ : L) ∈ S := by
    by_contra hbot
    exact hnot (Finset.mem_powerset.2 (Finset.subset_erase.2 ⟨Finset.mem_powerset.1 hS, hbot⟩))
  have hinter : sInf (S : Set L) = ⊥ := le_bot_iff.1 (sInf_le hbot)
  simp [hinter, hw]

namespace Arrangement

/-- The alternating sum of a weight on intersections of subsets of an arrangement. A weight
vanishing at `⊥` discards the subsets with empty intersection. -/
noncomputable def intersectionSum {M : Type*} [AddCommGroup M] (𝒜 : Arrangement k V)
    (w : AffineSubspace k V → M) : M :=
  ∑ S ∈ 𝒜.hyperplanes.powerset, ((-1 : ℤ) ^ S.card) • w (sInf (S : Set _))

/-- The empty arrangement contributes only its empty subset, whose intersection is the ambient
space. -/
@[simp]
theorem intersectionSum_empty {M : Type*} [AddCommGroup M] (w : AffineSubspace k V → M) :
    intersectionSum (∅ : Arrangement k V) w = w ⊤ := by
  classical
  change ∑ S ∈ (∅ : Finset (AffineSubspace k V)).powerset,
    ((-1 : ℤ) ^ S.card) • w (sInf (S : Set _)) = w ⊤
  simp

/-- Splitting the alternating subset sum into subsets avoiding and containing a hyperplane.
The latter subsets contribute with the opposite sign. -/
theorem intersectionSum_deletion {M : Type*} [AddCommGroup M] (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (hH : H ∈ 𝒜) (w : AffineSubspace k V → M) :
    𝒜.intersectionSum w = (𝒜.deletion H).intersectionSum w -
      ∑ S ∈ (𝒜.deletion H).hyperplanes.powerset,
        ((-1 : ℤ) ^ S.card) • w (H ⊓ sInf (S : Set _)) := by
  classical
  have heq : 𝒜.hyperplanes = insert H (𝒜.deletion H).hyperplanes :=
    (Finset.insert_erase hH).symm
  unfold intersectionSum
  rw [heq, Finset.sum_powerset_insert (by simp [deletion]), sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hnot : H ∉ S :=
    Finset.notMem_mono (Finset.mem_powerset.1 hS) (by simp [deletion])
  simp [Finset.card_insert_of_notMem hnot, pow_succ, Finset.coe_insert, sInf_insert]

open scoped Classical in
/-- The traces of the deleted hyperplanes are precisely the restriction hyperplanes together
with a possible empty trace. Erasing `⊥` removes it and `Finset.image` removes duplicates. -/
theorem hyperplanes_restriction_eq_erase_image (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (hH : IsHyperplane H) :
    (𝒜.restriction H).hyperplanes =
      ((𝒜.deletion H).hyperplanes.image (AffineSubspace.comap (chart H))).erase ⊥ := by
  classical
  ext L
  rw [mem_hyperplanes, mem_restriction hH, Finset.mem_erase]
  simp only [Finset.mem_image, mem_hyperplanes]
  constructor
  · rintro ⟨K, hK, hbot, rfl⟩
    exact ⟨(comap_chart_eq_bot_iff hH.ne_bot).not.mpr hbot, K, hK, rfl⟩
  · rintro ⟨hbot, K, hK, rfl⟩
    exact ⟨K, hK, (comap_chart_eq_bot_iff hH.ne_bot).not.mp hbot, rfl⟩

/-- The alternating sum of intersections with `H` is the corresponding sum on the restriction.
Repeated traces collapse by `sum_powerset_image`, and empty traces contribute zero. -/
theorem intersectionSum_trace {M : Type*} [AddCommGroup M] (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (hH : IsHyperplane H) (w : AffineSubspace k V → M)
    (hw : w ⊥ = 0) :
    (∑ S ∈ (𝒜.deletion H).hyperplanes.powerset,
      ((-1 : ℤ) ^ S.card) • w (H ⊓ sInf (S : Set _))) =
        (𝒜.restriction H).intersectionSum (fun X => w (X.map (chart H))) := by
  classical
  let f : AffineSubspace k V → AffineSubspace k H.direction :=
    AffineSubspace.comap (chart H)
  calc
    _ = ∑ S ∈ (𝒜.deletion H).hyperplanes.powerset,
        ((-1 : ℤ) ^ S.card) •
          w ((sInf (↑(S.image f) : Set (AffineSubspace k H.direction))).map (chart H)) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.coe_image, map_chart_sInf_image_comap_chart hH.ne_bot]
    _ = ∑ S ∈ ((𝒜.deletion H).hyperplanes.image f).powerset,
        ((-1 : ℤ) ^ S.card) •
          w ((sInf (S : Set (AffineSubspace k H.direction))).map (chart H)) :=
      sum_powerset_image _ f
        (fun S => w ((sInf (S : Set (AffineSubspace k H.direction))).map (chart H)))
    _ = ∑ S ∈ (((𝒜.deletion H).hyperplanes.image f).erase ⊥).powerset,
        ((-1 : ℤ) ^ S.card) •
          w ((sInf (S : Set (AffineSubspace k H.direction))).map (chart H)) :=
      sum_powerset_sInf_erase_bot _
        (fun X : AffineSubspace k H.direction => w (X.map (chart H))) (by simpa using hw)
    _ = _ := by
      rw [intersectionSum, hyperplanes_restriction_eq_erase_image 𝒜 hH]

/-- Deletion–restriction for any intersection weight vanishing on the empty subspace. This
identity accounts for empty and duplicate traces without any assumption about rational points. -/
theorem intersectionSum_deletion_restriction {M : Type*} [AddCommGroup M]
    (𝒜 : Arrangement k V) {H : AffineSubspace k V} (hH : H ∈ 𝒜)
    (w : AffineSubspace k V → M) (hw : w ⊥ = 0) :
    𝒜.intersectionSum w = (𝒜.deletion H).intersectionSum w -
      (𝒜.restriction H).intersectionSum (fun X => w (X.map (chart H))) := by
  rw [intersectionSum_deletion 𝒜 hH, intersectionSum_trace 𝒜 (𝒜.isHyperplane hH) w hw]

open scoped Classical in
/-- The alternating intersection sum for a singleton arrangement. -/
theorem intersectionSum_singleton {M : Type*} [AddCommGroup M] (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (h𝒜 : 𝒜.hyperplanes = {H}) (w : AffineSubspace k V → M) :
    𝒜.intersectionSum w = w ⊤ - w H := by
  classical
  rw [intersectionSum, h𝒜]
  change ∑ S ∈ (insert H (∅ : Finset (AffineSubspace k V))).powerset,
    ((-1 : ℤ) ^ S.card) • w (sInf (S : Set _)) = _
  rw [Finset.sum_powerset_insert (Finset.notMem_empty H)]
  simp [Finset.coe_insert, sInf_insert, sub_eq_add_neg]

open scoped Classical in
/-- The four terms of the alternating intersection sum for two distinct hyperplanes. This
formula keeps the intersection term separate, so empty intersections can be tested directly. -/
theorem intersectionSum_pair {M : Type*} [AddCommGroup M] (𝒜 : Arrangement k V)
    {H K : AffineSubspace k V} (hne : H ≠ K) (h𝒜 : 𝒜.hyperplanes = {H, K})
    (w : AffineSubspace k V → M) :
    𝒜.intersectionSum w = w ⊤ - w H - w K + w (H ⊓ K) := by
  classical
  rw [intersectionSum, h𝒜, Finset.sum_powerset_insert (by simp [hne])]
  change (∑ S ∈ (insert K (∅ : Finset (AffineSubspace k V))).powerset,
    ((-1 : ℤ) ^ S.card) • w (sInf (S : Set _))) +
      (∑ S ∈ (insert K (∅ : Finset (AffineSubspace k V))).powerset,
        ((-1 : ℤ) ^ (insert H S).card) •
          w (sInf (↑(insert H S) : Set (AffineSubspace k V)))) = _
  rw [Finset.sum_powerset_insert (Finset.notMem_empty K),
    Finset.sum_powerset_insert (Finset.notMem_empty K)]
  simp [hne, Finset.coe_insert, sInf_insert, sub_eq_add_neg]
  abel

/-- The weight of a nonempty affine intersection in the characteristic polynomial. -/
noncomputable def characteristicWeight (X : AffineSubspace k V) : ℤ[X] :=
  open scoped Classical in
  if X = ⊥ then 0 else Polynomial.X ^ finrank k X.direction

/-- The signed codimension weight of a nonempty affine intersection in the Poincaré polynomial. -/
noncomputable def poincareWeight (X : AffineSubspace k V) : ℤ[X] :=
  open scoped Classical in
  if X = ⊥ then 0 else (-Polynomial.X) ^ codim X

@[simp]
theorem characteristicWeight_bot : characteristicWeight (⊥ : AffineSubspace k V) = 0 := by
  simp [characteristicWeight]

@[simp]
theorem poincareWeight_bot : poincareWeight (⊥ : AffineSubspace k V) = 0 := by
  simp [poincareWeight]

/-- Passing through a chart does not change the dimension weight. -/
theorem characteristicWeight_map_chart {H : AffineSubspace k V}
    (Y : AffineSubspace k H.direction) :
    characteristicWeight (Y.map (chart H)) = characteristicWeight Y := by
  classical
  by_cases hY : Y = ⊥
  · subst Y
    simp
  · have hmap : Y.map (chart H) ≠ ⊥ := (AffineSubspace.map_eq_bot_iff _).not.mpr hY
    simp only [characteristicWeight, hY, hmap, ↓reduceIte]
    rw [finrank_direction_map_chart]

/-- Cutting by a hyperplane adds one to codimension and supplies the factor `-X`. -/
theorem poincareWeight_map_chart [FiniteDimensional k V] {H : AffineSubspace k V}
    (hH : IsHyperplane H) (Y : AffineSubspace k H.direction) :
    poincareWeight (Y.map (chart H)) = -Polynomial.X * poincareWeight Y := by
  classical
  by_cases hY : Y = ⊥
  · subst Y
    simp
  · have hmap : Y.map (chart H) ≠ ⊥ := (AffineSubspace.map_eq_bot_iff _).not.mpr hY
    simp only [poincareWeight, hY, hmap, ↓reduceIte]
    rw [codim_map_chart, hH.codim_eq_one, pow_succ, mul_comm]

/-- The characteristic polynomial, as a sum over subsets with nonempty intersection.
Blueprint: `def:polynomials`. -/
noncomputable def characteristicPolynomial (𝒜 : Arrangement k V) : ℤ[X] :=
  𝒜.intersectionSum characteristicWeight

/-- The Poincaré polynomial, as a signed codimension sum over subsets with nonempty intersection.
Blueprint: `def:polynomials`. -/
noncomputable def poincarePolynomial (𝒜 : Arrangement k V) : ℤ[X] :=
  𝒜.intersectionSum poincareWeight

open scoped Classical in
/-- The characteristic polynomial in the blueprint's explicit subset-sum form. Only subsets
whose intersection is nonempty are retained. Blueprint: `def:polynomials`. -/
theorem characteristicPolynomial_eq_sum (𝒜 : Arrangement k V) :
    𝒜.characteristicPolynomial =
      ∑ S ∈ 𝒜.hyperplanes.powerset.filter
          (fun S : Finset (AffineSubspace k V) => sInf (S : Set (AffineSubspace k V)) ≠ ⊥),
        Polynomial.C ((-1 : ℤ) ^ S.card) *
          Polynomial.X ^ finrank k (sInf (S : Set (AffineSubspace k V))).direction := by
  classical
  rw [characteristicPolynomial, intersectionSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : sInf (S : Set (AffineSubspace k V)) = ⊥
  · simp [characteristicWeight, hS]
  · simp [characteristicWeight, hS, zsmul_eq_mul]

open scoped Classical in
/-- The Poincaré polynomial in the blueprint's explicit subset-sum form, with coefficient
`(-1)^(|S| + codim (⋂ S))`. Blueprint: `def:polynomials`. -/
theorem poincarePolynomial_eq_sum (𝒜 : Arrangement k V) :
    𝒜.poincarePolynomial =
      ∑ S ∈ 𝒜.hyperplanes.powerset.filter
          (fun S : Finset (AffineSubspace k V) => sInf (S : Set (AffineSubspace k V)) ≠ ⊥),
        Polynomial.C ((-1 : ℤ) ^ (S.card + codim (sInf (S : Set (AffineSubspace k V))))) *
          Polynomial.X ^ codim (sInf (S : Set (AffineSubspace k V))) := by
  classical
  rw [poincarePolynomial, intersectionSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : sInf (S : Set (AffineSubspace k V)) = ⊥
  · simp [poincareWeight, hS]
  · simp only [poincareWeight, ne_eq, hS, not_false_eq_true, ↓reduceIte, zsmul_eq_mul]
    rw [neg_pow (Polynomial.X : ℤ[X])]
    simp only [pow_add, map_mul, map_pow, map_neg, map_one, Int.cast_pow, Int.cast_neg,
      Int.cast_one, mul_assoc]

/-- The empty arrangement in dimension `n` has characteristic polynomial `X^n`.
Blueprint: `lem:polynomial-recursion`. -/
@[simp]
theorem characteristicPolynomial_empty :
    characteristicPolynomial (∅ : Arrangement k V) = Polynomial.X ^ finrank k V := by
  simp only [characteristicPolynomial, intersectionSum_empty, characteristicWeight,
    ite_eq_right top_ne_bot]
  rw [AffineSubspace.direction_top]
  simp

/-- The empty arrangement has Poincaré polynomial one, including in dimension zero.
Blueprint: `lem:polynomial-recursion`. -/
@[simp]
theorem poincarePolynomial_empty : poincarePolynomial (∅ : Arrangement k V) = 1 := by
  simp [poincarePolynomial, poincareWeight]

/-- Characteristic polynomial deletion–restriction. Empty traces are excluded and repeated
traces counted once. Blueprint: `lem:polynomial-recursion`. -/
theorem characteristicPolynomial_deletion_restriction (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (hH : H ∈ 𝒜) :
    𝒜.characteristicPolynomial = (𝒜.deletion H).characteristicPolynomial -
      (𝒜.restriction H).characteristicPolynomial := by
  rw [characteristicPolynomial, intersectionSum_deletion_restriction 𝒜 hH _
    characteristicWeight_bot]
  simp only [characteristicWeight_map_chart, characteristicPolynomial]

/-- Poincaré polynomial deletion–restriction. The restriction term gains one in codimension.
Blueprint: `lem:polynomial-recursion`. -/
theorem poincarePolynomial_deletion_restriction [FiniteDimensional k V]
    (𝒜 : Arrangement k V) {H : AffineSubspace k V} (hH : H ∈ 𝒜) :
    𝒜.poincarePolynomial = (𝒜.deletion H).poincarePolynomial +
      Polynomial.X * (𝒜.restriction H).poincarePolynomial := by
  rw [poincarePolynomial, intersectionSum_deletion_restriction 𝒜 hH _ poincareWeight_bot]
  simp only [poincareWeight_map_chart (𝒜.isHyperplane hH), poincarePolynomial, intersectionSum]
  rw [Finset.mul_sum]
  simp only [← mul_smul_comm, neg_mul, smul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

open scoped Classical in
/-- A singleton arrangement has Poincaré polynomial `1 + X`, in every positive ambient
dimension and over every base field. -/
theorem poincarePolynomial_singleton (𝒜 : Arrangement k V)
    {H : AffineSubspace k V} (h𝒜 : 𝒜.hyperplanes = {H}) :
    𝒜.poincarePolynomial = 1 + Polynomial.X := by
  have hH : IsHyperplane H := 𝒜.isHyperplane (by rw [← mem_hyperplanes, h𝒜]; simp)
  rw [poincarePolynomial, intersectionSum_singleton 𝒜 h𝒜]
  simp [poincareWeight, hH.ne_bot, hH.codim_eq_one]

open scoped Classical in
/-- For two distinct hyperplanes, only the weight of their common intersection remains after
the two degree-one contributions. -/
theorem poincarePolynomial_pair (𝒜 : Arrangement k V)
    {H K : AffineSubspace k V} (hne : H ≠ K) (h𝒜 : 𝒜.hyperplanes = {H, K}) :
    𝒜.poincarePolynomial = 1 + 2 * Polynomial.X + poincareWeight (H ⊓ K) := by
  have hH : IsHyperplane H := 𝒜.isHyperplane (by rw [← mem_hyperplanes, h𝒜]; simp)
  have hK : IsHyperplane K := 𝒜.isHyperplane (by rw [← mem_hyperplanes, h𝒜]; simp)
  rw [poincarePolynomial, intersectionSum_pair 𝒜 hne h𝒜]
  simp only [poincareWeight, hH.ne_bot, hK.ne_bot, codim_top, hH.codim_eq_one,
    hK.codim_eq_one, ite_eq_right top_ne_bot, ↓reduceIte, pow_zero, pow_one]
  ring

open scoped Classical in
/-- Two disjoint hyperplanes have polynomial `1 + 2 X`. In particular, two points of the
affine line contribute no degree-two term. -/
theorem poincarePolynomial_pair_disjoint (𝒜 : Arrangement k V)
    {H K : AffineSubspace k V} (hne : H ≠ K) (h𝒜 : 𝒜.hyperplanes = {H, K})
    (hbot : H ⊓ K = ⊥) : 𝒜.poincarePolynomial = 1 + 2 * Polynomial.X := by
  rw [poincarePolynomial_pair 𝒜 hne h𝒜, hbot, poincareWeight_bot, add_zero]

open scoped Classical in
/-- Two distinct meeting hyperplanes have polynomial `(1 + X)^2`. -/
theorem poincarePolynomial_pair_meeting [FiniteDimensional k V] (𝒜 : Arrangement k V)
    {H K : AffineSubspace k V} (hne : H ≠ K) (h𝒜 : 𝒜.hyperplanes = {H, K})
    (hbot : H ⊓ K ≠ ⊥) : 𝒜.poincarePolynomial = 1 + 2 * Polynomial.X + Polynomial.X ^ 2 := by
  have hH : IsHyperplane H := 𝒜.isHyperplane (by rw [← mem_hyperplanes, h𝒜]; simp)
  have hK : IsHyperplane K := 𝒜.isHyperplane (by rw [← mem_hyperplanes, h𝒜]; simp)
  rw [poincarePolynomial_pair 𝒜 hne h𝒜]
  simp [poincareWeight, hbot, hH.codim_inf_eq_two hK hne.symm hbot]

/-- The positive-degree coefficient recurrence, stated over `ℤ` before any passage to natural
Betti numbers. Blueprint: `lem:polynomial-recursion`. -/
theorem poincarePolynomial_coeff_succ_deletion_restriction [FiniteDimensional k V]
    (𝒜 : Arrangement k V) {H : AffineSubspace k V} (hH : H ∈ 𝒜) (q : ℕ) :
    𝒜.poincarePolynomial.coeff (q + 1) =
      (𝒜.deletion H).poincarePolynomial.coeff (q + 1) +
        (𝒜.restriction H).poincarePolynomial.coeff q := by
  rw [poincarePolynomial_deletion_restriction 𝒜 hH, Polynomial.coeff_add,
    Polynomial.coeff_X_mul]

/-- The constant coefficient of every Poincaré polynomial is one. -/
@[simp]
theorem poincarePolynomial_coeff_zero [FiniteDimensional k V] (𝒜 : Arrangement k V) :
    𝒜.poincarePolynomial.coeff 0 = 1 := by
  refine Arrangement.induction
    (motive := fun _ _ _ _ ℬ => ℬ.poincarePolynomial.coeff 0 = 1) ?_ ?_ V 𝒜
  · intro W _ _ _
    rw [poincarePolynomial_empty, Polynomial.coeff_one]
    rfl
  · intro W _ _ _ ℬ H hH hdel _
    rw [poincarePolynomial_deletion_restriction ℬ hH, Polynomial.coeff_add,
      Polynomial.coeff_X_mul_zero, add_zero]
    exact hdel

/-- Every coefficient of the Poincaré polynomial is nonnegative. The proof uses only the subset
polynomials and deletion–restriction induction. Blueprint: `lem:polynomial-recursion`. -/
theorem poincarePolynomial_coeff_nonneg [FiniteDimensional k V] (𝒜 : Arrangement k V) (q : ℕ) :
    0 ≤ 𝒜.poincarePolynomial.coeff q := by
  refine Arrangement.induction
    (motive := fun _ _ _ _ ℬ => ∀ q, 0 ≤ ℬ.poincarePolynomial.coeff q) ?_ ?_ V 𝒜 q
  · intro W _ _ _ q
    rw [poincarePolynomial_empty, Polynomial.coeff_one]
    split_ifs <;> omega
  · intro W _ _ _ ℬ H hH hdel hres q
    rw [poincarePolynomial_deletion_restriction ℬ hH, Polynomial.coeff_add]
    cases q with
    | zero => simp
    | succ q =>
      rw [Polynomial.coeff_X_mul]
      exact add_nonneg (hdel (q + 1)) (hres q)

/-- The natural Betti coefficient of the Poincaré polynomial. For finite-dimensional ambient
spaces, nonnegativity is established above; comparison with cohomology is a later theorem. -/
noncomputable def bettiNumber (𝒜 : Arrangement k V) (q : ℕ) : ℕ :=
  (𝒜.poincarePolynomial.coeff q).toNat

/-- Casting a Betti number to `ℤ` recovers the original polynomial coefficient. -/
@[simp]
theorem natCast_bettiNumber [FiniteDimensional k V] (𝒜 : Arrangement k V) (q : ℕ) :
    (𝒜.bettiNumber q : ℤ) = 𝒜.poincarePolynomial.coeff q :=
  Int.toNat_of_nonneg (poincarePolynomial_coeff_nonneg 𝒜 q)

/-- The empty arrangement has Betti coefficient one in degree zero and zero otherwise. -/
@[simp]
theorem bettiNumber_empty (q : ℕ) :
    bettiNumber (∅ : Arrangement k V) q = if q = 0 then 1 else 0 := by
  simp only [bettiNumber, poincarePolynomial_empty, Polynomial.coeff_one]
  split_ifs <;> rfl

/-- Every arrangement has zeroth Betti number one, before any comparison with cohomology. -/
@[simp]
theorem bettiNumber_zero [FiniteDimensional k V] (𝒜 : Arrangement k V) : 𝒜.bettiNumber 0 = 1 := by
  simp only [bettiNumber, poincarePolynomial_coeff_zero]
  rfl

/-- The Betti coefficients satisfy deletion–restriction as an equality of natural numbers. -/
theorem bettiNumber_succ_deletion_restriction [FiniteDimensional k V]
    (𝒜 : Arrangement k V) {H : AffineSubspace k V} (hH : H ∈ 𝒜) (q : ℕ) :
    𝒜.bettiNumber (q + 1) = (𝒜.deletion H).bettiNumber (q + 1) +
      (𝒜.restriction H).bettiNumber q := by
  apply Int.ofNat_injective
  change (𝒜.bettiNumber (q + 1) : ℤ) =
    (((𝒜.deletion H).bettiNumber (q + 1) + (𝒜.restriction H).bettiNumber q : ℕ) : ℤ)
  rw [Nat.cast_add, natCast_bettiNumber, natCast_bettiNumber, natCast_bettiNumber]
  exact poincarePolynomial_coeff_succ_deletion_restriction 𝒜 hH q

end Arrangement

end OrlikSolomon
