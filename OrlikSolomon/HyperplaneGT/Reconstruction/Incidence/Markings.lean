/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Projective
public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Inertia
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Markings
public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Field
import Mathlib.Tactic.FinCases

/-!
# The marked frame and the obstruction to exchanging all fibers

The coordinate zero fibers and the ordered coordinate-difference zero fiber form a genuine
dependent triple. The corresponding three one fibers have empty common intersection.
These statements hold over arbitrary fields, including characteristic two, and use only
the actual tagged marking functions.

Blueprint: the geometric obstruction in I04 (`lem:i04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {S : Set k₀}

/-- The deliberately fixed constant coefficient point is the initial coordinate point of
the projective frame. -/
theorem constantPoint_eq_projectiveBasisPoint :
    constantPoint k n = projectiveBasisPoint k (0 : Fin (n + 1)) := by
  unfold constantPoint projectiveBasisPoint
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext t
  cases t using Fin.cases <;> simp

/-- The zero coordinate marking has the corresponding coordinate coefficient point. -/
theorem coefficientPoint_marking_coordinate_zero (hS : (0 : k₀) ∈ S) (i : Fin n) :
    coefficientPoint ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0) =
      projectiveBasisPoint k i.succ := by
  rw [coefficientPoint_eq_mk _ (Marking.isEquation_fiber _ _)]
  unfold projectiveBasisPoint
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext t
  cases t using Fin.cases <;>
    simp [affineCoefficients_zero, affineCoefficients_succ, Marking.function, Pi.single_apply,
      eq_comm]

/-- The one fiber of a zero coordinate marking gives the frame point involving the initial
coordinate. Its coefficient vector is exactly the corresponding difference vector. -/
theorem coefficientPoint_marking_coordinate_one (hS : (0 : k₀) ∈ S) (i : Fin n) :
    coefficientPoint ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 1) =
      projectiveDifferencePoint k i.succ 0 i.succ_ne_zero := by
  rw [coefficientPoint_eq_mk _ (Marking.isEquation_fiber _ _)]
  unfold projectiveDifferencePoint
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext t
  cases t using Fin.cases <;>
    simp [affineCoefficients_zero, affineCoefficients_succ, Marking.function, Pi.single_apply,
      eq_comm]

/-- The zero fiber of an ordered difference marking is the corresponding difference point
at projective infinity. -/
theorem coefficientPoint_marking_difference_zero (i j : Fin n) (hij : i < j) :
    coefficientPoint ((Marking.difference (S := S) i j hij).fiber (k := k) 0) =
      projectiveDifferencePoint k i.succ j.succ
        (fun he ↦ (ne_of_lt hij) (Fin.succ_inj.mp he)) := by
  rw [coefficientPoint_eq_mk _ (Marking.isEquation_fiber _ _)]
  unfold projectiveDifferencePoint
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext t
  cases t using Fin.cases <;>
    simp [affineCoefficients_zero, affineCoefficients_succ, Marking.function, Pi.single_apply,
      eq_comm]

private theorem marking_coordinate_zero_distinct (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    (Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.coordinate j ⟨0, hS⟩).fiber 0 ∧
      (Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.difference (S := S) i j hij).fiber 0 ∧
      (Marking.coordinate j ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.difference (S := S) i j hij).fiber 0 := by
  have hne := ne_of_lt hij
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single j (1 : k) ∈ H.val) he
    simp [hne] at hm
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single j (1 : k) ∈ H.val) he
    simp [hne] at hm
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single i (1 : k) ∈ H.val) he
    simp [hne.symm] at hm

/-- Two distinct coordinate zero fibers and their ordered difference zero fiber have the
same nonempty codimension-two trace. No assumption about the characteristic is needed. -/
theorem dependentTriple_marking_coordinate_zero (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    DependentTriple ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0)
      ((Marking.coordinate j ⟨0, hS⟩).fiber 0)
      ((Marking.difference (S := S) i j hij).fiber 0) := by
  obtain ⟨hij', hi, hj⟩ := marking_coordinate_zero_distinct (k := k) hS i j hij
  apply (dependentTriple_iff_trace_eq _ _ _ hij' hi hj).mpr
  constructor
  · intro hbot
    have hz : (0 : Fin n → k) ∈
        ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0).val ⊓
          ((Marking.coordinate j ⟨0, hS⟩).fiber 0).val := by
      constructor <;> simp
    rw [hbot] at hz
    exact AffineSubspace.notMem_bot k _ _ hz
  · ext x
    simp only [AffineSubspace.mem_inf_iff, Marking.mem_fiber, Marking.function_coordinate,
      Marking.function_difference, map_zero, sub_zero]
    constructor
    · rintro ⟨hi, hj⟩
      exact ⟨hi, by simp [hi, hj]⟩
    · rintro ⟨hi, hd⟩
      exact ⟨hi, by simpa only [hi, zero_sub, neg_eq_zero] using hd⟩

/-- The corresponding coordinate one fibers and difference one fiber have empty triple
intersection. Thus exchanging every ordered marking pair cannot preserve incidence, even
in characteristic two. -/
theorem not_dependentTriple_marking_coordinate_one (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    ¬DependentTriple ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 1)
      ((Marking.coordinate j ⟨0, hS⟩).fiber 1)
      ((Marking.difference (S := S) i j hij).fiber 1) := by
  intro hd
  apply hd.2.2.2.1
  apply le_bot_iff.mp
  intro x hx
  have hi := (Marking.mem_fiber _ _ x).mp hx.1.1
  have hj := (Marking.mem_fiber _ _ x).mp hx.1.2
  have hd := (Marking.mem_fiber _ _ x).mp hx.2
  simp only [Marking.function_coordinate, map_zero, sub_zero, map_one] at hi hj
  simp only [Marking.function_difference, map_one, hi, hj, sub_self] at hd
  exact (zero_ne_one hd).elim

variable {R : Type r} [CommRing R] {C : CofinalSystem k₀ k n}

/-- The two coefficients of the one common target determine the image of every ordered
marked basis vector. This is the actual marking square in the universal module and needs
neither reconstruction hypotheses nor a new marking-map construction. -/
theorem DiagramAut.universalEquiv_marking_single (g : DiagramAut R C S)
    (w : Marking S n) (a : Fin 2) :
    g.universalEquiv (Finsupp.single (w.fiber (k := k) (a.val : k₀)) 1) =
      (g.targetEquiv (Finsupp.single a 1)) 0 • Finsupp.single (w.fiber 0) 1 +
        (g.targetEquiv (Finsupp.single a 1)) 1 • Finsupp.single (w.fiber 1) 1 := by
  classical
  obtain ⟨A, hw⟩ := C.exists_stage_marking w
  let f := (finiteStageMap R A.val.val).comp (w.basisMap R hw)
  have hf (t : Fin 2) : f (Finsupp.single t 1) =
      Finsupp.single (w.fiber (k := k) (t.val : k₀)) 1 := by
    simp only [f, LinearMap.comp_apply, Marking.basisMap_single, finiteStageMap_single]
    congr 1
    apply Subtype.ext
    exact w.fiberLabel_val hw t
  have he := LinearMap.congr_fun (g.universalEquiv_marking A w hw) (Finsupp.single a 1)
  change g.universalEquiv (f (Finsupp.single a 1)) =
    f (g.targetEquiv (Finsupp.single a 1)) at he
  have hsplit (x : Fin 2 →₀ R) :
      x = x 0 • Finsupp.single 0 1 + x 1 • Finsupp.single 1 1 := by
    ext t
    fin_cases t <;> simp
  rw [hf, hsplit (g.targetEquiv (Finsupp.single a 1)), map_add, map_smul,
    map_smul, hf, hf] at he
  simpa only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] using he

private theorem mem_pair_of_unit_single_mem_span_pair [Nontrivial R]
    {ι : Type*} (J H K : ι) (u : Rˣ)
    (hx : (u : R) • Finsupp.single J (1 : R) ∈
      Submodule.span R {Finsupp.single H (1 : R), Finsupp.single K 1}) : J = H ∨ J = K := by
  classical
  by_cases hJH : J = H
  · exact Or.inl hJH
  by_cases hJK : J = K
  · exact Or.inr hJK
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hx
  have hv := congrArg (fun x : ι →₀ R ↦ x J) he
  exact (u.ne_zero (by simpa [hJH, hJK] using hv.symm)).elim

namespace DiagramAut

variable [IsLocalRing R]

private theorem hyperplanePerm_marking_mem_pair (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (w : Marking S n) (a : Fin 2) :
    g.hyperplanePerm hS hn (w.fiber (k := k) (a.val : k₀)) = w.fiber 0 ∨
      g.hyperplanePerm hS hn (w.fiber (k := k) (a.val : k₀)) = w.fiber 1 := by
  have he := g.universalEquiv_marking_single w a
  rw [g.universalEquiv_single hS hn] at he
  apply mem_pair_of_unit_single_mem_span_pair _ _ _
    (g.hyperplaneUnit hS hn (w.fiber (k := k) (a.val : k₀)))⁻¹
  rw [he]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem target_coordinate_zero_iff_marking_zero_fixed (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (w : Marking S n) :
    (g.targetEquiv (Finsupp.single 0 1)) 1 = 0 ↔
      g.hyperplanePerm hS hn (w.fiber (k := k) 0) = w.fiber 0 := by
  classical
  have he := g.universalEquiv_marking_single w 0
  rw [g.universalEquiv_single hS hn] at he
  have hv := congrArg (fun x : Hyperplane k n →₀ R ↦ x (w.fiber 1)) he
  have hne := (w.parallel_zero_one (k := k)).1
  rcases g.hyperplanePerm_marking_mem_pair hS hn w 0 with hp | hp
  · simp only [Fin.val_zero, Nat.cast_zero] at hp
    simp only [Fin.val_zero, Nat.cast_zero, hp, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hne.symm, Finsupp.single_eq_same,
      smul_eq_mul, mul_zero, mul_one, zero_add] at hv
    exact iff_of_true hv.symm hp
  · simp only [Fin.val_zero, Nat.cast_zero] at hp
    have hnf : g.hyperplanePerm hS hn (w.fiber (k := k) 0) ≠ w.fiber 0 := by
      rw [hp]
      exact hne.symm
    simp only [Fin.val_zero, Nat.cast_zero, hp, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hne.symm, Finsupp.single_eq_same,
      smul_eq_mul, mul_zero, mul_one, zero_add] at hv
    exact iff_of_false (fun hzero ↦ (g.hyperplaneUnit hS hn (w.fiber 0))⁻¹.ne_zero
      (hv.trans hzero)) hnf

private theorem target_coordinate_zero (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (g.targetEquiv (Finsupp.single 0 1)) 1 = 0 := by
  by_contra hzero
  have hswap (w : Marking S n) :
      g.hyperplanePerm hS hn (w.fiber (k := k) 0) = w.fiber 1 := by
    have hm := g.hyperplanePerm_marking_mem_pair hS hn w 0
    simp only [Fin.val_zero, Nat.cast_zero] at hm
    rcases hm with hp | hp
    · exact (hzero ((g.target_coordinate_zero_iff_marking_zero_fixed hS hn w).mpr hp)).elim
    · exact hp
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; decide
  have hd := (g.dependentTriple_hyperplanePerm_iff hS hn _ _ _).mpr
    (dependentTriple_marking_coordinate_zero (k := k) hS i j hij)
  rw [hswap, hswap, hswap] at hd
  exact not_dependentTriple_marking_coordinate_one hS i j hij hd

/-- Every actual zero marking fiber is individually fixed by the recovered permutation.
The one common target makes the possible exchange uniform, and the actual empty triangle
excludes it over every characteristic. Blueprint: I04 (`lem:i04`). -/
@[simp]
theorem hyperplanePerm_marking_zero (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (w : Marking S n) :
    g.hyperplanePerm hS hn (w.fiber (k := k) 0) = w.fiber 0 :=
  (g.target_coordinate_zero_iff_marking_zero_fixed hS hn w).mp
    (g.target_coordinate_zero hS hn)

/-- Every actual one marking fiber is individually fixed, since its zero partner is fixed
and the recovered label map is injective. Blueprint: I04 (`lem:i04`). -/
@[simp]
theorem hyperplanePerm_marking_one (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (w : Marking S n) :
    g.hyperplanePerm hS hn (w.fiber (k := k) 1) = w.fiber 1 := by
  have hm := g.hyperplanePerm_marking_mem_pair hS hn w 1
  simp only [Fin.val_one, Nat.cast_one] at hm
  rcases hm with hp | hp
  · have hf := g.hyperplanePerm_marking_zero hS hn w
    have he := (g.hyperplanePerm hS hn).injective (hp.trans hf.symm)
    exact ((w.parallel_zero_one (k := k)).1 he.symm).elim
  · exact hp

/-- The projective permutation fixes every coordinate point, including the constant point.
This is the full basis-point API required for the C03 field reconstruction. -/
@[simp]
theorem projectivePerm_basisPoint (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (i : Fin (n + 1)) :
    g.projectivePerm hS hn (projectiveBasisPoint k i) = projectiveBasisPoint k i := by
  cases i using Fin.cases with
  | zero => rw [← constantPoint_eq_projectiveBasisPoint]; simp
  | succ i => rw [← coefficientPoint_marking_coordinate_zero hS i]; simp

/-- The projective permutation fixes every difference of distinct coordinate points.
This includes all initial-coordinate points and both orderings of the direction points,
so no frame assumption is left to the field-reconstruction consumer. -/
@[simp]
theorem projectivePerm_differencePoint (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (i j : Fin (n + 1)) (hij : i ≠ j) :
    g.projectivePerm hS hn (projectiveDifferencePoint k i j hij) =
      projectiveDifferencePoint k i j hij := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      rw [projectiveDifferencePoint_swap]
      rw [← coefficientPoint_marking_coordinate_one hS j]
      simp
  | succ i =>
    cases j using Fin.cases with
    | zero => rw [← coefficientPoint_marking_coordinate_one hS i]; simp
    | succ j =>
      have hne : i ≠ j := fun he ↦ hij (congrArg Fin.succ he)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [← coefficientPoint_marking_difference_zero (S := S) i j hlt]
        simp
      · rw [projectiveDifferencePoint_swap]
        rw [← coefficientPoint_marking_difference_zero (S := S) j i hgt]
        simp

end DiagramAut

end OrlikSolomon.HyperplaneGT
