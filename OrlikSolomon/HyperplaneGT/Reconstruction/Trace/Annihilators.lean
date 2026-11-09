/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Configurations
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Decomposition

/-!
# Evaluation annihilators of trace and decomposition modules

The coordinate delta separates the distinguished coefficient, while the individual trace
indicator functionals separate the coefficients of the actual trace map. These explicit
separators give the four annihilator identities over arbitrary commutative rings, including
the zero ring. No double-dual reflexivity or general exactness statement is assumed.

## Main results

* `traceDomain_dualAnnihilator` identifies the annihilator of the trace domain with inertia.
* `traceKernel_dualAnnihilator` identifies the annihilator of the trace kernel with decomposition.
* `inertia_dualCoannihilator` and `decomposition_dualCoannihilator` give the reverse identities.
* `centralizer_unit_smul_delta` identifies the actual universal-relation centralizer using
  only unit cancellation.

Blueprint: the annihilator and unit-centralizer identities in `lem:l02`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} [Field k] {n : ℕ} (R : Type v) [CommRing R]

/-- Annihilating every vector with distinguished coefficient zero means being a multiple
of its coordinate delta. Blueprint: `I_H = Ann(U_H)` in `lem:l02`. -/
theorem traceDomain_dualAnnihilator (H : Hyperplane k n) :
    (traceDomain R H).dualAnnihilator = inertia R H := by
  classical
  ext φ
  rw [Submodule.mem_dualAnnihilator, mem_inertia]
  constructor
  · intro hφ
    refine ⟨φ (Finsupp.single H 1), dualCoordinates_ext fun K ↦ ?_⟩
    by_cases hKH : K = H
    · subst K
      simp
    · have hK : Finsupp.single K (1 : R) ∈ traceDomain R H := by
        simp [hKH]
      simpa [hKH] using (hφ _ hK).symm
  · rintro ⟨a, rfl⟩ x hx
    simp [(mem_traceDomain R H x).mp hx]

/-- The inertia annihilator consists of exactly the coefficient-zero vectors.
Blueprint: `Ann(I_H) = U_H` in `lem:l02`. -/
theorem inertia_dualCoannihilator (H : Hyperplane k n) :
    (inertia R H).dualCoannihilator = traceDomain R H := by
  ext x
  rw [Submodule.mem_dualCoannihilator, mem_traceDomain]
  constructor
  · intro hx
    have hδ : (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) ∈ inertia R H :=
      Submodule.subset_span (Set.mem_singleton _)
    exact hx _ hδ
  · intro hx φ hφ
    obtain ⟨a, rfl⟩ := (mem_inertia R H φ).mp hφ
    simp [hx]

/-- The exact trace-kernel generators impose exactly the two decomposition coordinate tests.
Blueprint: `D_H = Ann(U_H¹)` in `lem:l02`. -/
theorem traceKernel_dualAnnihilator (H : Hyperplane k n) :
    (traceKernel R H).dualAnnihilator = decomposition R H := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hφ
    constructor
    · intro K hK
      apply hφ
      rw [traceKernel_eq_span]
      exact Submodule.subset_span (Or.inl ⟨K, hK, rfl⟩)
    · intro K L ht
      have hz : φ (Finsupp.single K 1 - Finsupp.single L 1) = 0 := by
        apply hφ
        rw [traceKernel_eq_span]
        exact Submodule.subset_span (Or.inr ⟨K, L, ht, rfl⟩)
      exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  · intro hφ x hx
    have hle : traceKernel R H ≤ LinearMap.ker φ := by
      rw [traceKernel_eq_span, Submodule.span_le]
      rintro y (⟨K, hK, rfl⟩ | ⟨K, L, ht, rfl⟩)
      · exact hφ.1 K hK
      · change φ (Finsupp.single K 1 - Finsupp.single L 1) = 0
        rw [map_sub, hφ.2 K L ht, sub_self]
    exact hle hx

/-- Decomposition functionals separate the quotient by the actual trace kernel. This uses
the coordinate delta and arbitrary trace functionals explicitly, rather than a reflexivity
claim over the coefficient ring. Blueprint: `Ann(D_H) = U_H¹` in `lem:l02`. -/
theorem decomposition_dualCoannihilator (H : Hyperplane k n) :
    (decomposition R H).dualCoannihilator = traceKernel R H := by
  apply le_antisymm
  · intro x hx
    have heval := (Submodule.mem_dualCoannihilator x).mp hx
    have hδ := heval _ (delta_mem_decomposition R H)
    have hxH : x ∈ traceDomain R H := (mem_traceDomain R H x).mpr hδ
    let x' : traceDomain R H := ⟨x, hxH⟩
    have hs : traceMap R H x' = 0 := by
      apply finsupp_eq_of_dual_eval_eq
      intro ψ
      have hf := heval (traceFunctional R H (0, dualCoordinates ψ))
        (traceFunctional_mem_decomposition R H 0 (dualCoordinates ψ))
      rw [show x = x'.val from rfl, traceFunctional_apply_coe,
        LinearEquiv.symm_apply_apply] at hf
      simpa only [map_zero] using hf
    exact (coe_mem_traceKernel_iff R H x').mpr hs
  · rw [← traceKernel_dualAnnihilator]
    exact Submodule.le_dualAnnihilator_dualCoannihilator _

/-- The actual universal-relation centralizer of a unit multiple of delta is the decomposition
submodule. Cancellation uses only that the scalar is a unit; neither a domain nor a nonzero
coefficient ring is assumed. Blueprint: `C(u δ_H) = D_H` in `lem:l02`. -/
theorem centralizer_unit_smul_delta (H : Hyperplane k n) (u : Rˣ) :
    centralizer (universalQuadraticRelationSpan R)
      ((u : R) • (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R))) =
      decomposition R H := by
  classical
  ext φ
  rw [mem_centralizer_universalQuadraticRelationSpan_iff]
  constructor
  · rintro ⟨hp, ht⟩
    constructor
    · intro K hK
      change dualCoordinates φ K = 0
      apply u.isUnit.mul_left_cancel
      simpa [hK.1.symm] using hp H K hK
    · intro K L hd
      change dualCoordinates φ K = dualCoordinates φ L
      apply sub_eq_zero.mp
      apply u.isUnit.mul_left_cancel
      simpa [hd.1.symm, hd.2.1.symm] using ht H K L hd
  · intro hφ
    constructor
    · intro A B hp
      by_cases hAH : A = H
      · subst A
        have hB := hφ.1 B hp
        change dualCoordinates φ B = 0 at hB
        simp [hp.1.symm, hB]
      · by_cases hBH : B = H
        · subst B
          have hA := hφ.1 A ((parallel_comm A H).mp hp)
          change dualCoordinates φ A = 0 at hA
          simp [hAH, hA]
        · simp [hAH, hBH]
    · intro A B C hd
      by_cases hAH : A = H
      · subst A
        have heq := hφ.2 B C hd
        change dualCoordinates φ B = dualCoordinates φ C at heq
        simp [hd.1.symm, hd.2.1.symm, heq]
      · by_cases hBH : B = H
        · subst B
          have heq := hφ.2 A C ((dependentTriple_swap A H C).mp hd)
          change dualCoordinates φ A = dualCoordinates φ C at heq
          simp [hAH, hd.2.2.1.symm, heq]
        · by_cases hCH : C = H
          · subst C
            have heq := hφ.2 A B ((dependentTriple_rotate B H A).mp
              ((dependentTriple_rotate A B H).mp hd))
            change dualCoordinates φ A = dualCoordinates φ B at heq
            simp [hAH, hBH, heq]
          · simp [hAH, hBH, hCH]

end OrlikSolomon.HyperplaneGT
