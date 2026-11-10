/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Geometry
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Annihilators
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Projection

/-!
# Recognizing coordinate spans by commuting functionals

Restriction to an arbitrary supported coordinate span is surjective by Mathlib's explicit
supported-function retraction. Its kernel is the evaluation annihilator. Coordinate planes
are the actual two-generator spans of their zero and one level labels. Trace functionals
give coefficient detectors outside an enlarged coordinate set.

Blueprint: P01 (`lem:p01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k : Type u} [Field k] {n : ℕ}

/-- The marking plane spanned by the zero and one levels of a single coordinate.
Blueprint: the plane `L_i` in P01 (`lem:p01`). -/
def coordinatePlane (R : Type v) [Semiring R] (i : Fin n) :
    Submodule R (Hyperplane k n →₀ R) :=
  Submodule.span R {Finsupp.single (coordinateHyperplane i 0) (1 : R),
    Finsupp.single (coordinateHyperplane i 1) 1}

section Restriction

variable (R : Type v) [CommSemiring R]

/-- Every functional on an arbitrary supported coordinate span extends to the full free
module. The extension composes with the existing supported-function retraction.
Blueprint: the restriction assertion preceding P01 (`lem:p01`). -/
theorem verticalRestriction_surjective (z : Finset (Fin n)) :
    Function.Surjective (verticalRestriction (k := k) R z) := by
  classical
  intro φ
  let s : Set (Hyperplane k n) := {H | IsVertical z H}
  refine ⟨φ.comp (Finsupp.restrictDom R R s), ?_⟩
  ext x
  change φ (Finsupp.restrictDom R R s x.val) = φ x
  have hx : Finsupp.restrictDom R R s x.val = x :=
    DFunLike.congr_fun (Finsupp.restrictDom_comp_subtype (M := R) (R := R) s) x
  exact congrArg φ hx

/-- The kernel of the actual coordinate restriction is its evaluation annihilator.
Blueprint: the kernel assertion preceding P01 (`lem:p01`). -/
theorem ker_verticalRestriction (z : Finset (Fin n)) :
    LinearMap.ker (verticalRestriction (k := k) R z) =
      (verticalModule (k := k) R z).dualAnnihilator :=
  (verticalModule (k := k) R z).dualRestrict_ker_eq_dualAnnihilator

/-- Annihilating a coordinate span is equivalent to vanishing on its actual basis labels. -/
theorem mem_verticalAnnihilator_iff (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R)) :
    φ ∈ (verticalModule R z).dualAnnihilator ↔
      ∀ H, IsVertical z H → φ (Finsupp.single H 1) = 0 := by
  rw [← ker_verticalRestriction, LinearMap.mem_ker, verticalRestriction_eq_zero_iff]

/-- A coordinate delta outside a vertical span annihilates that actual supported submodule. -/
theorem delta_mem_verticalAnnihilator (z : Finset (Fin n)) (H : Hyperplane k n)
    (hH : ¬IsVertical z H) :
    (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) ∈
      (verticalModule R z).dualAnnihilator := by
  classical
  rw [mem_verticalAnnihilator_iff]
  intro K hK
  have hKH : K ≠ H := fun h ↦ hH (h ▸ hK)
  simp [hKH]

end Restriction

variable (R : Type v) [CommRing R]

/-- A trace indicator for the coordinate-zero trace detects exactly the coefficient at an
outside hyperplane. It annihilates the old coordinate span and belongs to the actual
decomposition submodule, hence commutes with its coordinate delta.
Blueprint: the converse detector in P01 (`lem:p01`). -/
theorem exists_coordinateSpan_detector (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z)
    (H : Hyperplane k n) (hH : ¬IsVertical (insert i z) H) :
    ∃ ψ : Module.Dual R (Hyperplane k n →₀ R),
      ψ ∈ decomposition R H ∧
      ψ ∈ (verticalModule R z).dualAnnihilator ∧
      ∀ a : Hyperplane k n →₀ R,
        dualDeterminant (Finsupp.lapply H) ψ
          (exteriorPower.ιMulti R 2
            ![a, Finsupp.single (coordinateHyperplane i 0) 1]) = a H := by
  classical
  let K₀ : {K : Hyperplane k n // K ≠ H} :=
    ⟨coordinateHyperplane i 0,
      (ne_coordinateHyperplane_of_not_isVertical_insert z i H hH 0).symm⟩
  obtain ⟨J, hJ⟩ : ∃ J, traceLabel H K₀ = some J := by
    cases ht : traceLabel H K₀ with
    | none =>
      exact (not_parallel_coordinateHyperplane_of_not_isVertical_insert z i H hH 0
        ((traceLabel_eq_none_iff H K₀).mp ht)).elim
    | some J => exact ⟨J, rfl⟩
  let b : IntrinsicHyperplane H → R := Pi.single J 1
  let ψ := traceFunctional R H (0, b)
  have hψK₀ : ψ (Finsupp.single (coordinateHyperplane i 0) 1) = 1 := by
    simpa [ψ, b] using traceFunctional_of_traceLabel R H K₀ J hJ 0 b
  refine ⟨ψ, traceFunctional_mem_decomposition R H 0 b, ?_, ?_⟩
  · rw [mem_verticalAnnihilator_iff]
    intro V hV
    have hVH : V ≠ H := fun h ↦ hH ((h ▸ hV).mono (Finset.subset_insert i z))
    let V' : {K : Hyperplane k n // K ≠ H} := ⟨V, hVH⟩
    cases ht : traceLabel H V' with
    | none =>
      exact traceFunctional_of_parallel R H V ((traceLabel_eq_none_iff H V').mp ht) 0 b
    | some J' =>
      have hJJ' : J' ≠ J := by
        intro heq
        subst J'
        have hKV : K₀.val ≠ V := by
          intro h
          apply hi
          rw [← isVertical_coordinateHyperplane z i (0 : k)]
          change IsVertical z K₀.val
          rw [h]
          exact hV
        have hd := (exists_common_traceLabel_iff H K₀ V' hKV).mp ⟨J, hJ, ht⟩
        exact not_dependentTriple_coordinateHyperplane_of_not_isVertical_insert z i H hH V hV hd
      simpa [ψ, b, hJJ'] using traceFunctional_of_traceLabel R H V' J' ht 0 b
  · intro a
    have hKH : coordinateHyperplane i (0 : k) ≠ H := K₀.property
    simp [dualDeterminant_ιMulti_apply, hψK₀, hKH]

private theorem coordinate_level_determinant (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z)
    (H : Hyperplane k n) (hH : IsVertical (insert i z) H) (t : k)
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R))
    (hφ : φ ∈ (verticalModule R z).dualAnnihilator)
    (hψ : ψ ∈ (verticalModule R z).dualAnnihilator)
    (hc : Commutes (universalQuadraticRelationSpan R) φ ψ) :
    dualDeterminant φ ψ (universalExteriorPair R H (coordinateHyperplane i t)) = 0 := by
  rw [dualDeterminant_universalExteriorPair]
  have hφz := (mem_verticalAnnihilator_iff R z φ).mp hφ
  have hψz := (mem_verticalAnnihilator_iff R z ψ).mp hψ
  have hcfg := (commutes_universalQuadraticRelationSpan_iff φ ψ).mp hc
  rcases coordinate_cases_of_isVertical_insert z i hi H hH t with hOld | hEq | hp | ⟨K, hK, hd⟩
  · change φ (Finsupp.single H 1) * _ - _ * ψ (Finsupp.single H 1) = 0
    rw [hφz H hOld, hψz H hOld, zero_mul, mul_zero, sub_zero]
  · subst H
    exact sub_self _
  · exact sub_eq_zero.mpr (hcfg.1 H (coordinateHyperplane i t) hp)
  · apply sub_eq_zero.mpr
    have he := hcfg.2 H (coordinateHyperplane i t) K hd
    simpa only [dualCoordinates_apply, hφz K hK, hψz K hK, sub_zero] using he

/-- A vector uses only the enlarged coordinate set exactly when its exterior product with
every vector of the coordinate marking plane is killed by every commuting pair annihilating
the old coordinate span. The commuting relation uses the actual global quadratic kernel.
Blueprint: P01 (`lem:p01`). -/
theorem coordinateSpan_recognition (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z)
    (a : Hyperplane k n →₀ R) :
    a ∈ verticalModule R (insert i z) ↔
      ∀ b : Hyperplane k n →₀ R, b ∈ coordinatePlane R i →
      ∀ φ ψ : Module.Dual R (Hyperplane k n →₀ R),
        φ ∈ (verticalModule R z).dualAnnihilator →
        ψ ∈ (verticalModule R z).dualAnnihilator →
        Commutes (universalQuadraticRelationSpan R) φ ψ →
        dualDeterminant φ ψ (exteriorPower.ιMulti R 2 ![a, b]) = 0 := by
  constructor
  · intro ha b hb φ ψ hφ hψ hc
    have ht (t : k) : dualDeterminant φ ψ
        (exteriorPower.ιMulti R 2 ![a, Finsupp.single (coordinateHyperplane i t) 1]) = 0 := by
      let ℓ : Module.Dual R (Hyperplane k n →₀ R) :=
        ψ (Finsupp.single (coordinateHyperplane i t) 1) • φ -
          φ (Finsupp.single (coordinateHyperplane i t) 1) • ψ
      have hle : verticalModule R (insert i z) ≤ LinearMap.ker ℓ := by
        rw [verticalModule, Finsupp.supported_eq_span_single, Submodule.span_le]
        rintro _ ⟨H, hH, rfl⟩
        have hd := coordinate_level_determinant R z i hi H hH t φ ψ hφ hψ hc
        simpa [ℓ, universalExteriorPair, mul_comm] using hd
      have hz := hle ha
      change ℓ a = 0 at hz
      simpa [ℓ, mul_comm] using hz
    let ℓ : Module.Dual R (Hyperplane k n →₀ R) := φ a • ψ - ψ a • φ
    have hle : coordinatePlane R i ≤ LinearMap.ker ℓ := by
      rw [coordinatePlane, Submodule.span_le]
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl
      · simpa [ℓ, mul_comm] using ht 0
      · simpa [ℓ, mul_comm] using ht 1
    have hz := hle hb
    change ℓ b = 0 at hz
    simpa [ℓ, mul_comm] using hz
  · intro h
    rw [mem_verticalModule]
    intro H hH
    obtain ⟨ψ, hψD, hψz, hψdet⟩ := exists_coordinateSpan_detector R z i hi H hH
    have hδz := delta_mem_verticalAnnihilator R z H
      (fun hz ↦ hH (hz.mono (Finset.subset_insert i z)))
    have hc : Commutes (universalQuadraticRelationSpan R) (Finsupp.lapply H) ψ := by
      rw [← mem_centralizer_iff]
      have he : centralizer (universalQuadraticRelationSpan R)
          (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) = decomposition R H := by
        simpa using centralizer_unit_smul_delta R H 1
      rw [he]
      exact hψD
    have hb : Finsupp.single (coordinateHyperplane (k := k) i 0) (1 : R) ∈ coordinatePlane R i :=
      Submodule.subset_span (by simp)
    have hz := h _ hb _ _ hδz hψz hc
    rwa [hψdet a] at hz

end OrlikSolomon.HyperplaneGT
