/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Chart

/-!
# Reconstructing the field from a fixed projective frame

The extra marked points `eᵢ - e₀` fix minus one on each affine axis. The direction points
`eᵢ - eⱼ` identify the coordinate bijections and force additivity. Lines through the origin
then force multiplicativity. The homogeneous formula includes the hyperplane at infinity.

Blueprint: `thm:c03`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {n : ℕ}

/-- Interchanging the two coordinates does not change their projective difference point. -/
theorem projectiveDifferencePoint_swap {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    projectiveDifferencePoint k i j hij = projectiveDifferencePoint k j i hij.symm := by
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  exact ⟨-1, by simp⟩

/-- The extra marked point involving the initial coordinate is minus one on the affine axis.
It is separate from the fixed coordinate point at infinity on that axis. -/
theorem affineChartPoint_single_neg_one (i : Fin n) :
    affineChartPoint (Pi.single i (-1 : k)) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero := by
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨-1, ?_⟩
  ext t
  cases t using Fin.cases <;> simp [Pi.single_apply]

/-- In a coordinate plane, the projective line with direction `eᵢ - eⱼ` through `ceᵢ`
is exactly the affine sum line `a + b = c`. The point at infinity supplies a distinct
endpoint for every `c`, including zero. -/
theorem affineChartPoint_mem_sum_line_iff (i j : Fin n) (hij : i ≠ j) (a b c : k) :
    affineChartPoint (Pi.single i a + Pi.single j b) ∈ Projectivization.Subspace.span
      {affineChartPoint (Pi.single i c),
        projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))} ↔
      a + b = c := by
  rw [affineChartPoint, projectiveDifferencePoint, projective_span_pair_eq]
  change (Fin.cons (1 : k) (Pi.single i a + Pi.single j b) : Fin (n + 1) → k) ∈
    Submodule.span k {(Fin.cons (1 : k) (Pi.single i c) : Fin (n + 1) → k),
      Pi.single i.succ 1 - Pi.single j.succ 1} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨u, v, h⟩
    have hu : u = 1 := by simpa [Pi.single_apply] using congrFun h 0
    subst u
    have hi : c + v = a := by simpa [Pi.single_apply, hij] using congrFun h i.succ
    have hj : -v = b := by simpa [Pi.single_apply, hij.symm] using congrFun h j.succ
    rw [← hi, ← hj, add_assoc, add_neg_cancel, add_zero]
  · intro hab
    refine ⟨1, -b, ?_⟩
    ext t
    cases t using Fin.cases with
    | zero => simp
    | succ t =>
      by_cases hti : t = i
      · subst t
        simp [hij, ← hab]
      · by_cases htj : t = j
        · subst t
          simp [hij.symm]
        · simp [hti, htj]

section FieldIdentities

variable (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
  (hF : PreservesProjectiveLines F)
  (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)

/-- A fixed sum-line direction makes its two coordinate bijections agree. The zero argument
uses their fixed zeros; every other sum line is anchored by its point at infinity. -/
theorem collineationCoordinateEquiv_eq_of_direction (i j : Fin n) (hij : i ≠ j)
    (hdir : F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) (c : k) :
    collineationCoordinateEquiv F hF hframe i c =
      collineationCoordinateEquiv F hF hframe j c := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmem : affineChartPoint (Pi.single j c) ∈ Projectivization.Subspace.span
      {affineChartPoint (Pi.single i c),
        projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))} := by
    simpa using (affineChartPoint_mem_sum_line_iff i j hij 0 c c).mpr (zero_add c)
  have h := (hF.mem_span_pair_iff _ _ _).mpr hmem
  rw [hdir, ← affineChartPoint_collineationChartMap F hF hframe (Pi.single i c),
    ← affineChartPoint_collineationChartMap F hF hframe (Pi.single j c),
    collineationChartMap_single, collineationChartMap_single] at h
  have heq := (affineChartPoint_mem_sum_line_iff i j hij 0
    (collineationCoordinateEquiv F hF hframe j c)
    (collineationCoordinateEquiv F hF hframe i c)).mp (by simpa using h)
  simpa using heq.symm

/-- A fixed sum-line direction forces additivity of either coordinate bijection. In the
zero-sum case the image line goes through the fixed origin, so no coincident affine
endpoints are used. -/
theorem collineationCoordinateEquiv_map_add (i j : Fin n) (hij : i ≠ j)
    (hdir : F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) (a b : k) :
    collineationCoordinateEquiv F hF hframe i (a + b) =
      collineationCoordinateEquiv F hF hframe i a +
        collineationCoordinateEquiv F hF hframe i b := by
  have hmem := (affineChartPoint_mem_sum_line_iff i j hij a b (a + b)).mpr rfl
  have h := (hF.mem_span_pair_iff _ _ _).mpr hmem
  simp only [← affineChartPoint_collineationChartMap F hF hframe,
    collineationChartMap_single, collineationChartMap_pair F hF hframe i j hij, hdir] at h
  have heq := (affineChartPoint_mem_sum_line_iff i j hij _ _ _).mp h
  rw [← collineationCoordinateEquiv_eq_of_direction F hF hframe i j hij hdir b] at heq
  exact heq.symm

/-- Fixing the marked point `eᵢ - e₀` fixes minus one on its affine coordinate axis. -/
theorem collineationCoordinateEquiv_neg_one (i : Fin n)
    (hminus : F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) :
    collineationCoordinateEquiv F hF hframe i (-1) = -1 := by
  rw [← affineChartPoint_single_neg_one] at hminus
  rw [← affineChartPoint_collineationChartMap F hF hframe,
    collineationChartMap_single] at hminus
  simpa using congrFun ((affineChartPoint_inj _ _).mp hminus) i

/-- Additivity and the extra marked minus-one point force one to be fixed. -/
theorem collineationCoordinateEquiv_one (i j : Fin n) (hij : i ≠ j)
    (hdir : F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h)))
    (hminus : F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) :
    collineationCoordinateEquiv F hF hframe i 1 = 1 := by
  have h : (-1 : k) + collineationCoordinateEquiv F hF hframe i 1 = 0 := by
    simpa [collineationCoordinateEquiv_neg_one F hF hframe i hminus] using
      (collineationCoordinateEquiv_map_add F hF hframe i j hij hdir (-1) 1).symm
  exact add_left_cancel (h.trans (neg_add_cancel (1 : k)).symm)

/-- Lines through the origin force multiplicativity, after normalization at one. -/
theorem collineationCoordinateEquiv_map_mul (i j : Fin n) (hij : i ≠ j)
    (hdir : F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h)))
    (hminus : F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) (a b : k) :
    collineationCoordinateEquiv F hF hframe i (a * b) =
      collineationCoordinateEquiv F hF hframe i a *
        collineationCoordinateEquiv F hF hframe i b := by
  have hmem : affineChartPoint (Pi.single i a + Pi.single j (a * b)) ∈
      Projectivization.Subspace.span
        {affineChartPoint (0 : Fin n → k), affineChartPoint (Pi.single i 1 + Pi.single j b)} :=
    (affineChartPoint_mem_span_origin_iff _ _).mpr ⟨a, by
      simp only [smul_add, ← Pi.single_smul, smul_eq_mul, mul_one]⟩
  have h := (hF.mem_span_pair_iff _ _ _).mpr hmem
  simp only [← affineChartPoint_collineationChartMap F hF hframe,
    collineationChartMap_zero, collineationChartMap_pair F hF hframe i j hij] at h
  rw [collineationCoordinateEquiv_one F hF hframe i j hij hdir hminus,
    ← collineationCoordinateEquiv_eq_of_direction F hF hframe i j hij hdir b,
    ← collineationCoordinateEquiv_eq_of_direction F hF hframe i j hij hdir (a * b)] at h
  obtain ⟨c, hc⟩ := (affineChartPoint_mem_span_origin_iff _ _).mp h
  have hi : collineationCoordinateEquiv F hF hframe i a = c := by
    simpa [hij] using congrFun hc i
  have hj : collineationCoordinateEquiv F hF hframe i (a * b) =
      c * collineationCoordinateEquiv F hF hframe i b := by
    simpa [hij.symm] using congrFun hc j
  exact hj.trans (congrArg (· * collineationCoordinateEquiv F hF hframe i b) hi.symm)

/-- Fixing the listed increasing difference points fixes all difference points, since
interchanging their two indices changes the representative by minus one. -/
theorem fixes_projectiveDifferencePoint
    (hdiff : ∀ i j : Fin n, ∀ hij : i < j,
      F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) =
        projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h)))
    (i j : Fin n) (hij : i ≠ j) :
    F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h)) := by
  obtain h | h := lt_or_gt_of_ne hij
  · exact hdiff i j h
  · rw [projectiveDifferencePoint_swap]
    exact hdiff j i h

end FieldIdentities

section FieldEquivalence

variable (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
  (hF : PreservesProjectiveLines F)
  (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
  (hn : 2 ≤ n)
  (hminus0 : ∀ i : Fin n,
    F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero)
  (hdiff : ∀ i j : Fin n, ∀ hij : i < j,
    F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h)))

/-- The field automorphism extracted from a line-preserving projective permutation fixing
the prescribed coordinate frame. Both families of extra fixed points are explicit hypotheses.

Blueprint: `thm:c03`. -/
noncomputable def coordinateFieldEquiv : k ≃+* k := by
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let j : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hdir := fixes_projectiveDifferencePoint F hdiff i j hij
  exact { collineationCoordinateEquiv F hF hframe i with
    map_add' := collineationCoordinateEquiv_map_add F hF hframe i j hij hdir
    map_mul' := collineationCoordinateEquiv_map_mul F hF hframe i j hij hdir (hminus0 i) }

/-- The extracted field automorphism agrees with every coordinate bijection. -/
theorem coordinateFieldEquiv_apply (i : Fin n) (a : k) :
    coordinateFieldEquiv F hF hframe hn hminus0 hdiff a =
      collineationCoordinateEquiv F hF hframe i a := by
  let j : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  change collineationCoordinateEquiv F hF hframe j a = _
  by_cases hji : j = i
  · subst i
    rfl
  · exact collineationCoordinateEquiv_eq_of_direction F hF hframe j i hji
      (fixes_projectiveDifferencePoint F hdiff j i hji) a

/-- On normalized affine representatives the collineation applies its extracted field
automorphism coordinatewise. -/
theorem coordinateFieldEquiv_affineChartPoint (a : Fin n → k) :
    F (affineChartPoint a) =
      affineChartPoint (fun i ↦ coordinateFieldEquiv F hF hframe hn hminus0 hdiff (a i)) := by
  rw [← affineChartPoint_collineationChartMap F hF hframe]
  congr 1
  ext i
  rw [collineationChartMap_apply, coordinateFieldEquiv_apply]

end FieldEquivalence

/-- Coordinatewise application of a field automorphism preserves nonzero vectors. -/
theorem coordinateMap_ne_zero {ι : Type*} (σ : k ≃+* k) {a : ι → k} (ha : a ≠ 0) :
    (fun i ↦ σ (a i)) ≠ 0 := by
  intro h
  apply ha
  ext i
  exact σ.injective ((congrFun h i).trans (map_zero σ).symm)

/-- A line joining the affine origin to `a` has exactly one point at infinity. The nonzero
affine vector hypothesis makes the indicated homogeneous vector nonzero. -/
theorem projective_eq_infinity_of_mem_span (a : Fin n → k) (ha : a ≠ 0)
    (p : ℙ k (Fin (n + 1) → k)) (hp : p.rep 0 = 0)
    (hmem : p ∈ Projectivization.Subspace.span
      {affineChartPoint (0 : Fin n → k), affineChartPoint a}) :
    p = Projectivization.mk k (Fin.cons 0 a) (by
      intro h
      apply ha
      ext i
      exact congrFun h i.succ) := by
  have hmem' : Projectivization.mk k p.rep p.rep_ne_zero ∈
      Projectivization.Subspace.span
        {affineChartPoint (0 : Fin n → k), affineChartPoint a} := by
    simpa using hmem
  simp only [affineChartPoint] at hmem'
  rw [projective_span_pair_eq] at hmem'
  obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp hmem'
  rw [← p.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨v, ?_⟩
  ext i
  cases i using Fin.cases with
  | zero => simpa using hp.symm
  | succ i => simpa using congrFun huv i.succ

section HomogeneousAction

variable (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
  (hF : PreservesProjectiveLines F)
  (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
  (hn : 2 ≤ n)
  (hminus0 : ∀ i : Fin n,
    F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero)
  (hdiff : ∀ i j : Fin n, ∀ hij : i < j,
    F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h)))

/-- The field automorphism computes the collineation on every nonzero homogeneous vector,
including all points on the hyperplane at infinity.

Blueprint: `thm:c03`. -/
theorem coordinateFieldEquiv_mk (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    F (Projectivization.mk k a ha) = Projectivization.mk k
      (fun i ↦ coordinateFieldEquiv F hF hframe hn hminus0 hdiff (a i))
      (coordinateMap_ne_zero _ ha) := by
  let σ := coordinateFieldEquiv F hF hframe hn hminus0 hdiff
  by_cases ha0 : a 0 = 0
  · have ht : Fin.tail a ≠ 0 := by
      intro h
      apply ha
      ext i
      cases i using Fin.cases with
      | zero => exact ha0
      | succ i => exact congrFun h i
    have hmem : Projectivization.mk k a ha ∈ Projectivization.Subspace.span
        {affineChartPoint (0 : Fin n → k), affineChartPoint (Fin.tail a)} := by
      simp only [affineChartPoint]
      rw [projective_span_pair_eq]
      refine Submodule.mem_span_pair.mpr ⟨-1, 1, ?_⟩
      ext i
      cases i using Fin.cases <;> simp [Fin.tail, ha0]
    have h := (hF.mem_span_pair_iff _ _ _).mpr hmem
    rw [coordinateFieldEquiv_affineChartPoint F hF hframe hn hminus0 hdiff,
      coordinateFieldEquiv_affineChartPoint F hF hframe hn hminus0 hdiff] at h
    simp only [Pi.zero_apply, map_zero] at h
    have hp : (F (Projectivization.mk k a ha)).rep 0 = 0 :=
      (collineation_rep_apply_eq_zero_iff F hF hframe _ 0).mpr
        ((projective_rep_apply_eq_zero_iff a ha 0).mpr ha0)
    have hpoint := projective_eq_infinity_of_mem_span
      (fun i ↦ σ (Fin.tail a i)) (coordinateMap_ne_zero σ ht) _ hp h
    have hv : (Fin.cons 0 (fun i ↦ σ (Fin.tail a i)) : Fin (n + 1) → k) =
        fun i ↦ σ (a i) := by
      ext i
      cases i using Fin.cases <;> simp [Fin.tail, ha0]
    simpa only [hv] using hpoint
  · have hσ0 : σ (a 0) ≠ 0 := (map_ne_zero σ).mpr ha0
    calc
      F (Projectivization.mk k a ha) =
          F (affineChartPoint (fun i ↦ a i.succ / a 0)) :=
        congrArg F (affineChartPoint_div_eq_mk a ha ha0).symm
      _ = affineChartPoint (fun i ↦ σ (a i.succ / a 0)) :=
        coordinateFieldEquiv_affineChartPoint F hF hframe hn hminus0 hdiff _
      _ = affineChartPoint (fun i ↦ σ (a i.succ) / σ (a 0)) := by simp only [map_div₀]
      _ = Projectivization.mk k (fun i ↦ σ (a i)) (coordinateMap_ne_zero σ ha) :=
        affineChartPoint_div_eq_mk (fun i ↦ σ (a i)) (coordinateMap_ne_zero σ ha) hσ0

end HomogeneousAction

/-- A coordinatewise field automorphism is determined by its action on projective points.
One affine coordinate axis suffices for this uniqueness statement. -/
theorem coordinateRingEquiv_eq_of_projective_action (hn : 1 ≤ n) (σ τ : k ≃+* k)
    (h : ∀ (a : Fin (n + 1) → k) (ha : a ≠ 0),
      Projectivization.mk k (fun i ↦ σ (a i)) (coordinateMap_ne_zero σ ha) =
        Projectivization.mk k (fun i ↦ τ (a i)) (coordinateMap_ne_zero τ ha)) : σ = τ := by
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hn⟩
  ext c
  let a : Fin (n + 1) → k := Fin.cons 1 (Pi.single i c)
  have ha : a ≠ 0 := by
    intro hzero
    have := congrFun hzero 0
    simp [a] at this
  have hσ : (fun t ↦ σ (a t)) =
      (Fin.cons 1 (Pi.single i (σ c)) : Fin (n + 1) → k) := by
    ext t
    cases t using Fin.cases with
    | zero => simp [a]
    | succ t =>
      by_cases hti : t = i <;> simp [a, hti]
  have hτ : (fun t ↦ τ (a t)) =
      (Fin.cons 1 (Pi.single i (τ c)) : Fin (n + 1) → k) := by
    ext t
    cases t using Fin.cases with
    | zero => simp [a]
    | succ t =>
      by_cases hti : t = i <;> simp [a, hti]
  have hpoint := h a ha
  simp only [hσ, hτ] at hpoint
  have hcoords := (affineChartPoint_inj _ _).mp hpoint
  simpa using congrFun hcoords i

section Uniqueness

variable (F : ℙ k (Fin (n + 1) → k) ≃ ℙ k (Fin (n + 1) → k))
  (hF : PreservesProjectiveLines F)
  (hframe : ∀ i, F (projectiveBasisPoint k i) = projectiveBasisPoint k i)
  (hn : 2 ≤ n)
  (hminus0 : ∀ i : Fin n,
    F (projectiveDifferencePoint k i.succ 0 i.succ_ne_zero) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero)
  (hdiff : ∀ i j : Fin n, ∀ hij : i < j,
    F (projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h))) =
      projectiveDifferencePoint k i.succ j.succ (fun h ↦ (ne_of_lt hij) (Fin.succ_inj.mp h)))

/-- Any field automorphism giving the same homogeneous projective action is the extracted one.

Blueprint: uniqueness in `thm:c03`. -/
theorem coordinateFieldEquiv_unique (τ : k ≃+* k)
    (hτ : ∀ (a : Fin (n + 1) → k) (ha : a ≠ 0),
      F (Projectivization.mk k a ha) =
        Projectivization.mk k (fun i ↦ τ (a i)) (coordinateMap_ne_zero τ ha)) :
    τ = coordinateFieldEquiv F hF hframe hn hminus0 hdiff := by
  apply coordinateRingEquiv_eq_of_projective_action (le_trans (by decide : 1 ≤ 2) hn)
  intro a ha
  rw [← hτ a ha, coordinateFieldEquiv_mk F hF hframe hn hminus0 hdiff]

include hF hframe hn hminus0 hdiff in
/-- A line-preserving projective permutation fixing the prescribed frame is induced by a
unique field automorphism, on all homogeneous points.

Blueprint: `thm:c03`. -/
theorem existsUnique_coordinateFieldEquiv :
    ∃! σ : k ≃+* k, ∀ (a : Fin (n + 1) → k) (ha : a ≠ 0),
      F (Projectivization.mk k a ha) =
        Projectivization.mk k (fun i ↦ σ (a i)) (coordinateMap_ne_zero σ ha) := by
  exact ⟨coordinateFieldEquiv F hF hframe hn hminus0 hdiff,
    coordinateFieldEquiv_mk F hF hframe hn hminus0 hdiff,
    coordinateFieldEquiv_unique F hF hframe hn hminus0 hdiff⟩

end Uniqueness

end OrlikSolomon.HyperplaneGT
