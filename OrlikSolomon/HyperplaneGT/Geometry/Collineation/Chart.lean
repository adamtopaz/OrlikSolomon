/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Span
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinate charts of projective collineations

The affine chart with initial homogeneous coordinate one is invariant under a collineation
fixing all coordinate points. Its induced bijection acts separately on the coordinates.

Blueprint: `lem:c02`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k]

/-- A coordinate point of projective space. -/
def projectiveBasisPoint (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (i : ι) :
    ℙ k (ι → k) :=
  Projectivization.mk k (Pi.single i 1) (by
    intro h
    have := congrFun h i
    simp at this)

/-- A projective difference of two distinct coordinate vectors. In the marked frame, the
points involving the initial coordinate are separate from the affine direction points. -/
def projectiveDifferencePoint (k : Type*) [Field k] {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) : ℙ k (ι → k) :=
  Projectivization.mk k (Pi.single i 1 - Pi.single j 1) (by
    intro h
    have := congrFun h i
    simp [Pi.single_eq_of_ne hij] at this)

/-- The projective span of coordinate points consists exactly of points supported on the
corresponding coordinates. -/
theorem projective_mem_span_basis_iff {ι : Type*} [Finite ι] [DecidableEq ι]
    (s : Set ι) (v : ι → k) (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ Projectivization.Subspace.span
      (projectiveBasisPoint k '' s) ↔ ∀ i ∉ s, v i = 0 := by
  let _ := Fintype.ofFinite ι
  constructor
  · intro h
    have hle : Projectivization.Subspace.span (projectiveBasisPoint k '' s) ≤
        (Pi.spanSubset k s).projectivization := by
      refine Projectivization.Subspace.span_le_subspace_iff.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      change Pi.single i 1 ∈ Pi.spanSubset k s
      rw [Pi.mem_spanSubset_iff]
      intro j hj
      exact Pi.single_eq_of_ne (show j ≠ i from by
        intro h
        subst j
        exact hj hi) 1
    exact Pi.mem_spanSubset_iff.mp (hle h)
  · intro h
    apply (Projectivization.Subspace.mem_submodule_iff _ hv).mp
    rw [← LinearMap.sum_single_apply (fun _ : ι ↦ k) v]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : i ∈ s
    · have he : Pi.single i (1 : k) ∈ Projectivization.Subspace.submodule
          (Projectivization.Subspace.span (projectiveBasisPoint k '' s)) :=
        (Projectivization.Subspace.mem_submodule_iff _ _).mpr
          (Projectivization.Subspace.subset_span _ ⟨i, hi, rfl⟩)
      simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
        (Projectivization.Subspace.submodule _).smul_mem (v i) he
    · rw [h i hi, Pi.single_zero]
      exact Submodule.zero_mem _

/-- Zero of a homogeneous coordinate is independent of the representative. -/
theorem projective_rep_apply_eq_zero_iff {ι : Type*} (v : ι → k) (hv : v ≠ 0) (i : ι) :
    (Projectivization.mk k v hv).rep i = 0 ↔ v i = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← hc]
  change (c : k) * v i = 0 ↔ v i = 0
  simp [c.ne_zero]

variable {n : ℕ}

/-- The affine chart whose initial homogeneous coordinate is one. -/
def affineChartPoint (a : Fin n → k) : ℙ k (Fin (n + 1) → k) :=
  Projectivization.mk k (Fin.cons 1 a) (by
    intro h
    have := congrFun h 0
    simp at this)

/-- Equality of normalized chart representatives is equality of their coordinates. -/
@[simp]
theorem affineChartPoint_inj (a b : Fin n → k) :
    affineChartPoint a = affineChartPoint b ↔ a = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp h
    have hc1 : c = 1 := by simpa using congrFun hc 0
    subst c
    funext i
    simpa using (congrFun hc i.succ).symm
  · rintro rfl
    rfl

/-- Every chart point has nonzero initial coordinate in any representative. -/
theorem affineChartPoint_rep_zero_ne (a : Fin n → k) :
    (affineChartPoint a).rep 0 ≠ 0 := by
  intro h
  exact one_ne_zero ((projective_rep_apply_eq_zero_iff (Fin.cons (1 : k) a) _ 0).mp h)

/-- Dividing by the initial nonzero coordinate gives the normalized affine chart point. -/
theorem affineChartPoint_div_eq_mk (a : Fin (n + 1) → k) (ha : a ≠ 0) (ha0 : a 0 ≠ 0) :
    affineChartPoint (fun i ↦ a i.succ / a 0) = Projectivization.mk k a ha := by
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨(a 0)⁻¹, ?_⟩
  ext i
  cases i using Fin.cases
  · simp [ha0]
  · simp [div_eq_mul_inv, mul_comm]

/-- Normalize the representative of a point whose initial coordinate is nonzero. -/
theorem affineChartPoint_normalize (p : ℙ k (Fin (n + 1) → k)) (hp : p.rep 0 ≠ 0) :
    affineChartPoint (fun i ↦ p.rep i.succ / p.rep 0) = p :=
  (affineChartPoint_div_eq_mk p.rep p.rep_ne_zero hp).trans p.mk_rep

/-- Fixing the coordinate points makes every coordinate hyperplane invariant. -/
theorem collineation_rep_apply_eq_zero_iff
    (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
    (hF : PreservesProjectiveLines F)
    (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
    (p : ℙ k (Fin (n + 1) → k)) (j : Fin (n + 1)) :
    (F p).rep j = 0 ↔ p.rep j = 0 := by
  let S : Set (ℙ k (Fin (n + 1) → k)) :=
    projectiveBasisPoint k '' {i | i ≠ j}
  have hS : F '' S = S := by
    ext q
    simp only [S, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (hframe i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨projectiveBasisPoint k i, ⟨i, hi, rfl⟩, hframe i⟩
  have hm (q : ℙ k (Fin (n + 1) → k)) :
      q ∈ Projectivization.Subspace.span S ↔ q.rep j = 0 := by
    conv_lhs => rw [← q.mk_rep]
    rw [projective_mem_span_basis_iff]
    simp only [Set.mem_ofPred_eq, not_not, forall_eq]
  rw [← hm (F p), ← hm p]
  change F p ∈ (Projectivization.Subspace.span S : Set _) ↔ _
  have hspan := collineation_preserves_span F hF S
  rw [hS] at hspan
  rw [← hspan]
  exact F.injective.mem_set_image

/-- The normalized affine chart is equivalent to points with nonzero initial coordinate. -/
noncomputable def affineChartEquiv :
    (Fin n → k) ≃ {p : ℙ k (Fin (n + 1) → k) // p.rep 0 ≠ 0} where
  toFun a := ⟨affineChartPoint a, affineChartPoint_rep_zero_ne a⟩
  invFun p i := p.val.rep i.succ / p.val.rep 0
  left_inv a := (affineChartPoint_inj _ _).mp
    (affineChartPoint_normalize _ (affineChartPoint_rep_zero_ne a))
  right_inv p := Subtype.ext (affineChartPoint_normalize p.val p.property)

/-- The actual chart permutation induced by a collineation fixing the coordinate points. -/
noncomputable def collineationChartMap
    (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
    (hF : PreservesProjectiveLines F)
    (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i) :
    (Fin n → k) ≃ (Fin n → k) :=
  affineChartEquiv.trans ((F.subtypeEquiv fun p ↦
    not_congr (collineation_rep_apply_eq_zero_iff F hF hframe p 0).symm).trans
      affineChartEquiv.symm)

/-- The chart permutation computes the original projective map. -/
theorem affineChartPoint_collineationChartMap
    (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
    (hF : PreservesProjectiveLines F)
    (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
    (a : Fin n → k) :
    affineChartPoint (collineationChartMap F hF hframe a) = F (affineChartPoint a) := by
  exact affineChartPoint_normalize (F (affineChartPoint a))
    (fun h ↦ affineChartPoint_rep_zero_ne a
      ((collineation_rep_apply_eq_zero_iff F hF hframe _ 0).mp h))

/-- The affine origin is the initial coordinate point. -/
@[simp]
theorem affineChartPoint_zero : affineChartPoint (0 : Fin n → k) =
    projectiveBasisPoint k (0 : Fin (n + 1)) := by
  change Projectivization.mk k (Fin.cons (1 : k) (0 : Fin n → k) : Fin (n + 1) → k) _ =
    Projectivization.mk k (Pi.single 0 1) _
  congr 1
  ext i
  cases i using Fin.cases <;> simp

/-- An affine line with coordinate direction `i` changes only coordinate `i`. Its other
projective endpoint is at infinity, so the endpoints remain distinct even at the origin. -/
theorem affineChartPoint_mem_span_direction_iff (a b : Fin n → k) (i : Fin n) :
    affineChartPoint b ∈ Projectivization.Subspace.span
      {affineChartPoint a, projectiveBasisPoint k i.succ} ↔
      ∀ j, j ≠ i → b j = a j := by
  rw [affineChartPoint, projectiveBasisPoint, projective_span_pair_eq]
  change (Fin.cons (1 : k) b : Fin (n + 1) → k) ∈
    Submodule.span k {(Fin.cons (1 : k) a : Fin (n + 1) → k), Pi.single i.succ 1} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, d, h⟩
    have hc : c = 1 := by simpa [Pi.single_apply] using congrFun h 0
    subst c
    intro j hji
    simpa [Pi.single_apply, hji] using (congrFun h j.succ).symm
  · intro h
    refine ⟨1, b i - a i, ?_⟩
    ext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, h j hji]

/-- A normalized point lies on the line from the origin through `a` exactly when its affine
coordinates are a scalar multiple of `a`. This remains valid when `a` is zero. -/
theorem affineChartPoint_mem_span_origin_iff (a b : Fin n → k) :
    affineChartPoint b ∈ Projectivization.Subspace.span
      {affineChartPoint (0 : Fin n → k), affineChartPoint a} ↔
      ∃ c : k, b = c • a := by
  change Projectivization.mk k (Fin.cons (1 : k) b : Fin (n + 1) → k) _ ∈
    Projectivization.Subspace.span
      {Projectivization.mk k (Fin.cons (1 : k) (0 : Fin n → k) : Fin (n + 1) → k) _,
        Projectivization.mk k (Fin.cons (1 : k) a : Fin (n + 1) → k) _} ↔ _
  rw [projective_span_pair_eq]
  change (Fin.cons (1 : k) b : Fin (n + 1) → k) ∈
    Submodule.span k {(Fin.cons (1 : k) (0 : Fin n → k) : Fin (n + 1) → k),
      Fin.cons 1 a} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, d, h⟩
    refine ⟨d, ?_⟩
    ext i
    simpa using (congrFun h i.succ).symm
  · rintro ⟨c, rfl⟩
    refine ⟨1 - c, c, ?_⟩
    ext i
    cases i using Fin.cases <;> simp

section CoordinateFunctions

variable (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
  (hF : PreservesProjectiveLines F)
  (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)

/-- The induced chart permutation fixes its origin. -/
@[simp]
theorem collineationChartMap_zero : collineationChartMap F hF hframe 0 = 0 := by
  apply (affineChartPoint_inj _ _).mp
  rw [affineChartPoint_collineationChartMap, affineChartPoint_zero, hframe]

/-- Updating one input coordinate leaves every other output coordinate unchanged. -/
theorem collineationChartMap_update (a : Fin n → k) (i j : Fin n)
    (hji : j ≠ i) (c : k) :
    collineationChartMap F hF hframe (Function.update a i c) j =
      collineationChartMap F hF hframe a j := by
  have hmem : affineChartPoint (Function.update a i c) ∈
      Projectivization.Subspace.span {affineChartPoint a, projectiveBasisPoint k i.succ} :=
    (affineChartPoint_mem_span_direction_iff a _ i).mpr (by
      intro t hti
      exact Function.update_of_ne hti c a)
  have h := (hF.mem_span_pair_iff _ _ _).mpr hmem
  rw [← affineChartPoint_collineationChartMap F hF hframe a,
    ← affineChartPoint_collineationChartMap F hF hframe (Function.update a i c), hframe] at h
  exact (affineChartPoint_mem_span_direction_iff _ _ i).mp h j hji

/-- Each output coordinate equals the corresponding output on its own input axis. -/
theorem collineationChartMap_apply_eq_axis (a : Fin n → k) (j : Fin n) :
    collineationChartMap F hF hframe a j =
      collineationChartMap F hF hframe (Pi.single j (a j)) j := by
  have hfinite (s : Finset (Fin n)) : ∀ a b : Fin n → k,
      (∀ i ∉ s, a i = b i) → j ∉ s →
        collineationChartMap F hF hframe a j = collineationChartMap F hF hframe b j := by
    induction s using Finset.induction with
    | empty =>
      intro a b hab _
      exact congrArg (fun x ↦ collineationChartMap F hF hframe x j)
        (funext fun i ↦ hab i (by simp))
    | @insert i s _ ih =>
      intro a b hab hj
      have hji : j ≠ i := fun h ↦ hj (by simp [h])
      calc
        collineationChartMap F hF hframe a j =
            collineationChartMap F hF hframe (Function.update a i (b i)) j :=
          (collineationChartMap_update F hF hframe a i j hji (b i)).symm
        _ = collineationChartMap F hF hframe b j := by
          apply ih
          · intro t ht
            by_cases hti : t = i
            · subst t
              simp
            · rw [Function.update_of_ne hti]
              exact hab t (by simp [hti, ht])
          · exact fun h ↦ hj (Finset.mem_insert_of_mem h)
  apply hfinite (Finset.univ.erase j)
  · intro i hi
    have hij : i = j := by simpa using hi
    subst i
    simp
  · simp

/-- The restriction to each affine coordinate axis is a bijection of the field. -/
theorem collineation_axis_bijective (i : Fin n) :
    Function.Bijective (fun c : k ↦ collineationChartMap F hF hframe (Pi.single i c) i) := by
  constructor
  · intro a b hab
    have h : collineationChartMap F hF hframe (Pi.single i a) =
        collineationChartMap F hF hframe (Pi.single i b) := by
      ext j
      by_cases hji : j = i
      · subst j
        exact hab
      · rw [collineationChartMap_apply_eq_axis F hF hframe _ j,
          collineationChartMap_apply_eq_axis F hF hframe (Pi.single i b) j]
        simp [hji]
    have h' := (collineationChartMap F hF hframe).injective h
    simpa using congrFun h' i
  · intro b
    let a := (collineationChartMap F hF hframe).symm (Pi.single i b)
    refine ⟨a i, ?_⟩
    change collineationChartMap F hF hframe (Pi.single i (a i)) i = b
    rw [← collineationChartMap_apply_eq_axis F hF hframe a i]
    simp [a]

/-- The field bijection obtained by restricting a coordinate-preserving collineation to an
affine coordinate axis. No dimension bound is imposed.

Blueprint: `lem:c02`. -/
noncomputable def collineationCoordinateEquiv (i : Fin n) : k ≃ k :=
  Equiv.ofBijective (fun c ↦ collineationChartMap F hF hframe (Pi.single i c) i)
    (collineation_axis_bijective F hF hframe i)

theorem collineationCoordinateEquiv_apply (i : Fin n) (c : k) :
    collineationCoordinateEquiv F hF hframe i c =
      collineationChartMap F hF hframe (Pi.single i c) i := rfl

/-- Each coordinate bijection fixes zero. -/
@[simp]
theorem collineationCoordinateEquiv_zero (i : Fin n) :
    collineationCoordinateEquiv F hF hframe i 0 = 0 := by
  simp [collineationCoordinateEquiv_apply]

/-- The chart action is given coordinatewise by its axis restrictions. -/
theorem collineationChartMap_apply (a : Fin n → k) (i : Fin n) :
    collineationChartMap F hF hframe a i =
      collineationCoordinateEquiv F hF hframe i (a i) :=
  collineationChartMap_apply_eq_axis F hF hframe a i

/-- The chart map sends an axis point to the axis point computed by its coordinate bijection. -/
theorem collineationChartMap_single (i : Fin n) (c : k) :
    collineationChartMap F hF hframe (Pi.single i c) =
      Pi.single i (collineationCoordinateEquiv F hF hframe i c) := by
  ext j
  rw [collineationChartMap_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The chart map on a coordinate plane is given by its two coordinate bijections. -/
theorem collineationChartMap_pair (i j : Fin n) (hij : i ≠ j) (a b : k) :
    collineationChartMap F hF hframe (Pi.single i a + Pi.single j b) =
      Pi.single i (collineationCoordinateEquiv F hF hframe i a) +
        Pi.single j (collineationCoordinateEquiv F hF hframe j b) := by
  ext t
  rw [collineationChartMap_apply]
  by_cases hti : t = i
  · subst t
    simp [hij]
  · by_cases htj : t = j
    · subst t
      simp [hij.symm]
    · simp [hti, htj]

include hF hframe in
/-- A collineation fixing the coordinate points acts on the normalized affine chart by field
bijections, one for each coordinate, all fixing zero. This includes dimensions zero and one.

Blueprint: `lem:c02`. -/
theorem collineation_coordinate_functions :
    ∃ f : Fin n → (k ≃ k), (∀ i, f i 0 = 0) ∧
      ∀ a : Fin n → k, F (affineChartPoint a) =
        affineChartPoint (fun i ↦ f i (a i)) := by
  refine ⟨collineationCoordinateEquiv F hF hframe,
    collineationCoordinateEquiv_zero F hF hframe, ?_⟩
  intro a
  rw [← affineChartPoint_collineationChartMap F hF hframe]
  congr 1
  ext i
  exact collineationChartMap_apply F hF hframe a i

end CoordinateFunctions

end OrlikSolomon.HyperplaneGT
