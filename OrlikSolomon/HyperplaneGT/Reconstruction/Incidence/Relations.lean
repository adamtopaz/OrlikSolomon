/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Permutation

/-!
# Recovering affine incidence from the actual trace kernel

A retained trace is a genuine coordinate in a free module. Over a nonzero coefficient ring,
a basis vector has zero trace precisely for a strict parallel label. A difference of two
unit-weighted basis vectors with one retained trace has zero trace precisely when the labels
form a guarded dependent triple and the two units agree.

These coefficient tests use the existing trace map and its actual kernel, with no quotient
model or additional incidence data. Blueprint: I02 (`lem:i02`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r

section TraceTests

variable {k : Type u} [Field k] {n : ℕ} (R : Type v) [Ring R] [Nontrivial R]

/-- A distinct label has zero trace exactly when it is strictly parallel to the fixed
hyperplane. Coefficient nontriviality is essential for the retained basis vector. -/
theorem single_mem_traceKernel_iff (H K : Hyperplane k n) (hKH : K ≠ H) :
    Finsupp.single K (1 : R) ∈ traceKernel R H ↔ Parallel H K := by
  classical
  let K' : {K : Hyperplane k n // K ≠ H} := ⟨K, hKH⟩
  rw [← coe_traceSingle R H K' 1, coe_mem_traceKernel_iff, traceMap_traceSingle]
  cases ht : traceLabel H K' with
  | none =>
    simp only [Option.elim_none, true_iff]
    exact (traceLabel_eq_none_iff H K').mp ht
  | some J =>
    have hn : ¬Parallel H K := by
      intro hp
      have he := (traceLabel_eq_none_iff H K').mpr hp
      rw [ht] at he
      cases he
    simp [hn]

/-- A zero trace of a unit-weighted difference with a nonempty first trace forces a common
retained trace and equal units. This detects exactly the guarded dependent triple and works
over arbitrary nonzero rings, without requiring coefficients to form a domain. -/
theorem unit_smul_single_sub_mem_traceKernel_iff (H K L : Hyperplane k n)
    (hKH : K ≠ H) (hLH : L ≠ H) (hKL : K ≠ L) (hp : ¬Parallel H K) (a b : Rˣ) :
    (a : R) • Finsupp.single K 1 - (b : R) • Finsupp.single L 1 ∈ traceKernel R H ↔
      DependentTriple H K L ∧ a = b := by
  classical
  let K' : {K : Hyperplane k n // K ≠ H} := ⟨K, hKH⟩
  let L' : {K : Hyperplane k n // K ≠ H} := ⟨L, hLH⟩
  have hK : ∃ J, traceLabel H K' = some J := by
    cases ht : traceLabel H K' with
    | none => exact (hp ((traceLabel_eq_none_iff H K').mp ht)).elim
    | some J => exact ⟨J, rfl⟩
  obtain ⟨J, hJ⟩ := hK
  let x : traceDomain R H := (a : R) • traceSingle R H K' 1 -
    (b : R) • traceSingle R H L' 1
  have hx : (x : Hyperplane k n →₀ R) =
      (a : R) • Finsupp.single K 1 - (b : R) • Finsupp.single L 1 := by
    simp [x, K', L']
  rw [← hx, coe_mem_traceKernel_iff]
  have hs : traceMap R H x =
      (a : R) • Finsupp.single J 1 -
        (b : R) • (traceLabel H L').elim 0 (fun J ↦ Finsupp.single J 1) := by
    simp only [x, map_sub, map_smul, traceMap_traceSingle, hJ, Option.elim_some]
  rw [hs, sub_eq_zero]
  constructor
  · intro he
    have hL : traceLabel H L' = some J := by
      cases ht : traceLabel H L' with
      | none =>
        have hz := congrArg (fun y : IntrinsicHyperplane H →₀ R ↦ y J) he
        simp only [ht, Option.elim_none, smul_zero, Finsupp.smul_apply,
          Finsupp.single_eq_same, smul_eq_mul, mul_one, Finsupp.zero_apply] at hz
        exact (a.ne_zero hz).elim
      | some J' =>
        by_cases heq : J' = J
        · exact congrArg some heq
        · have hz := congrArg (fun y : IntrinsicHyperplane H →₀ R ↦ y J) he
          simp only [ht, Option.elim_some, Finsupp.smul_apply, Finsupp.single_eq_same,
            Finsupp.single_eq_of_ne (Ne.symm heq), smul_eq_mul, mul_one, mul_zero] at hz
          exact (a.ne_zero hz).elim
    refine ⟨(exists_common_traceLabel_iff H K' L' hKL).mp ⟨J, hJ, hL⟩, ?_⟩
    apply Units.ext
    have hv := congrArg (fun y : IntrinsicHyperplane H →₀ R ↦ y J) he
    simpa only [hL, Option.elim_some, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] using hv
  · rintro ⟨hd, rfl⟩
    obtain ⟨J', hK', hL'⟩ := (exists_common_traceLabel_iff H K' L' hKL).mpr hd
    have heq : J' = J := Option.some.inj (hK'.symm.trans hJ)
    simp only [hL', heq, Option.elim_some]

end TraceTests

namespace DiagramAut

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {R : Type r} [CommRing R] [IsLocalRing R]
  {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The primal action carries the actual coefficient-zero trace domain onto the trace
domain of the recovered label. This is evaluation-coannihilator equivariance for inertia. -/
theorem map_traceDomain (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (traceDomain R H).map g.universalEquiv.toLinearMap =
      traceDomain R (g.hyperplanePerm hS hn H) := by
  rw [← inertia_dualCoannihilator, map_dualCoannihilator_dualAction]
  change ((inertia R H).map (dualAction g).toLinearMap).dualCoannihilator = _
  rw [g.map_inertia hS hn H, inertia_dualCoannihilator]

/-- The primal action carries the entire actual trace kernel onto that of the recovered
label. This uses the explicit decomposition coannihilator identity, not dual reflexivity.
Blueprint: the trace-kernel transport in I02 (`lem:i02`). -/
theorem map_traceKernel (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (traceKernel R H).map g.universalEquiv.toLinearMap =
      traceKernel R (g.hyperplanePerm hS hn H) := by
  rw [← decomposition_dualCoannihilator, map_dualCoannihilator_dualAction]
  change ((decomposition R H).map (dualAction g).toLinearMap).dualCoannihilator = _
  rw [g.map_decomposition hS hn H, decomposition_dualCoannihilator]

/-- A vector belongs to an actual trace kernel precisely when its primal image belongs to
the trace kernel at the recovered label. -/
@[simp]
theorem universalEquiv_mem_traceKernel_iff (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) (x : Hyperplane k n →₀ R) :
    g.universalEquiv x ∈ traceKernel R (g.hyperplanePerm hS hn H) ↔
      x ∈ traceKernel R H := by
  rw [← g.map_traceKernel hS hn H, Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply]

private theorem parallel_hyperplanePerm (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H K : Hyperplane k n) (hp : Parallel H K) :
    Parallel (g.hyperplanePerm hS hn H) (g.hyperplanePerm hS hn K) := by
  have hm := (single_mem_traceKernel_iff R H K hp.1.symm).mpr hp
  have hm' := (g.universalEquiv_mem_traceKernel_iff hS hn H _).mpr hm
  rw [g.universalEquiv_single hS hn K] at hm'
  have hs : Finsupp.single (g.hyperplanePerm hS hn K) (1 : R) ∈
      traceKernel R (g.hyperplanePerm hS hn H) := by
    exact (Submodule.smul_mem_iff_of_isUnit _ (g.hyperplaneUnit hS hn K)⁻¹.isUnit).mp hm'
  exact (single_mem_traceKernel_iff R _ _
    ((g.hyperplanePerm hS hn).injective.ne hp.1.symm)).mp hs

/-- The recovered label permutation preserves strict parallelism in both directions.
Blueprint: the parallel-pair assertion in I02 (`lem:i02`). -/
theorem parallel_hyperplanePerm_iff (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H K : Hyperplane k n) :
    Parallel (g.hyperplanePerm hS hn H) (g.hyperplanePerm hS hn K) ↔ Parallel H K := by
  constructor
  · intro hp
    simpa using parallel_hyperplanePerm g⁻¹ hS hn _ _ hp
  · exact parallel_hyperplanePerm g hS hn H K

private theorem dependentTriple_hyperplanePerm (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H K L : Hyperplane k n)
    (hd : DependentTriple H K L) :
    DependentTriple (g.hyperplanePerm hS hn H)
      (g.hyperplanePerm hS hn K) (g.hyperplanePerm hS hn L) := by
  have hp : ¬Parallel H K := by
    rintro ⟨_, hbot⟩
    exact hd.2.2.2.1 (by simp [hbot])
  have hm : Finsupp.single K (1 : R) - Finsupp.single L 1 ∈ traceKernel R H := by
    rw [traceKernel_eq_span]
    exact Submodule.subset_span (Or.inr ⟨K, L, hd, rfl⟩)
  have hm' := (g.universalEquiv_mem_traceKernel_iff hS hn H _).mpr hm
  rw [map_sub, g.universalEquiv_single hS hn K, g.universalEquiv_single hS hn L] at hm'
  exact ((unit_smul_single_sub_mem_traceKernel_iff R _ _ _
    ((g.hyperplanePerm hS hn).injective.ne hd.1.symm)
    ((g.hyperplanePerm hS hn).injective.ne hd.2.1.symm)
    ((g.hyperplanePerm hS hn).injective.ne hd.2.2.1)
    (fun hp' ↦ hp ((g.parallel_hyperplanePerm_iff hS hn H K).mp hp'))
    (g.hyperplaneUnit hS hn K)⁻¹ (g.hyperplaneUnit hS hn L)⁻¹).mp hm').1

/-- The recovered label permutation preserves guarded dependent triples in both directions,
including pairwise distinctness and nonempty codimension-two intersection.
Blueprint: the triple assertion in I02 (`lem:i02`). -/
theorem dependentTriple_hyperplanePerm_iff (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H K L : Hyperplane k n) :
    DependentTriple (g.hyperplanePerm hS hn H)
      (g.hyperplanePerm hS hn K) (g.hyperplanePerm hS hn L) ↔ DependentTriple H K L := by
  constructor
  · intro hd
    simpa using dependentTriple_hyperplanePerm g⁻¹ hS hn _ _ _ hd
  · exact dependentTriple_hyperplanePerm g hS hn H K L

end DiagramAut

end OrlikSolomon.HyperplaneGT
