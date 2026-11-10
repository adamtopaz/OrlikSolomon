/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Local.Detection
public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Invariance

/-!
# Recognizing contragredient images of coordinate inertia

Every detection hypothesis for an actual transformed delta is derived from the existing
vertical restriction, its proved equivariance square, and the common-target marking planes.
A coordinate marking or an ordered difference marking supplies a graph coordinate where
the transformed functional vanishes. Local detection then gives one unique hyperplane and
one unique unit, independently of the coordinate chosen for the proof.

Blueprint: the detection step of I01 (`prop:i01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {S : Set k₀}

private theorem difference_fiber_not_isVertical_left (z : Finset (Fin n))
    (i j : Fin n) (hij : i < j) (hi : i ∉ z) (t : k₀) :
    ¬IsVertical z ((Marking.difference (S := S) i j hij).fiber (k := k) t) := by
  rw [isVertical_iff_of_isEquation _ _ (Marking.isEquation_fiber _ _)]
  intro h
  have he := h i hi
  simp [affineCoefficients_succ, Marking.function, (ne_of_lt hij).symm] at he

private theorem difference_fiber_not_isVertical_right (z : Finset (Fin n))
    (i j : Fin n) (hij : i < j) (hj : j ∉ z) (t : k₀) :
    ¬IsVertical z ((Marking.difference (S := S) i j hij).fiber (k := k) t) := by
  rw [isVertical_iff_of_isEquation _ _ (Marking.isEquation_fiber _ _)]
  intro h
  have he := h j hj
  simp [affineCoefficients_succ, Marking.function, ne_of_lt hij] at he

/-- A marking with both fibers graph hyperplanes avoids any specified label. The coordinate
marking works unless the label is one of its fibers; an ordered coordinate difference then
uses a second coordinate. Only dimension at least two and the zero marking constant enter.
Blueprint: the zero-coordinate witness in I01 (`prop:i01`). -/
theorem exists_marking_graph_avoiding (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (i : Fin n) (H : Hyperplane k n) :
    ∃ w : Marking S n,
      ¬IsVertical (omittedCoordinates i) (w.fiber (k := k) 0) ∧
      ¬IsVertical (omittedCoordinates i) (w.fiber (k := k) 1) ∧
      H ≠ w.fiber 0 ∧ H ≠ w.fiber 1 := by
  classical
  let w₀ : Marking S n := .coordinate i ⟨0, hS⟩
  have hw₀ (t : k₀) : w₀.fiber (k := k) t = coordinateHyperplane i (algebraMap k₀ k t) := by
    apply Subtype.ext
    ext x
    simp [w₀]
  by_cases hH : H = w₀.fiber 0 ∨ H = w₀.fiber 1
  · have hHv : IsVertical ({i} : Finset (Fin n)) H := by
      rcases hH with rfl | rfl <;> rw [hw₀] <;> simp
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j, hji⟩ := exists_ne i
    rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hji'
    · refine ⟨.difference i j hij, ?_, ?_, ?_, ?_⟩
      · exact difference_fiber_not_isVertical_left _ _ _ hij (by simp) _
      · exact difference_fiber_not_isVertical_left _ _ _ hij (by simp) _
      · intro he
        exact difference_fiber_not_isVertical_right {i} i j hij (by simpa using hji) 0
          (he ▸ hHv)
      · intro he
        exact difference_fiber_not_isVertical_right {i} i j hij (by simpa using hji) 1
          (he ▸ hHv)
    · refine ⟨.difference j i hji', ?_, ?_, ?_, ?_⟩
      · exact difference_fiber_not_isVertical_right _ _ _ hji' (by simp) _
      · exact difference_fiber_not_isVertical_right _ _ _ hji' (by simp) _
      · intro he
        exact difference_fiber_not_isVertical_left {i} j i hji' (by simpa using hji) 0
          (he ▸ hHv)
      · intro he
        exact difference_fiber_not_isVertical_left {i} j i hji' (by simpa using hji) 1
          (he ▸ hHv)
  · refine ⟨w₀, ?_, ?_, ?_, ?_⟩
    · rw [hw₀]
      simp
    · rw [hw₀]
      simp
    · exact fun he ↦ hH (Or.inl he)
    · exact fun he ↦ hH (Or.inr he)

variable {R : Type w} [CommRing R] {C : CofinalSystem k₀ k n}

namespace DiagramAut

/-- The actual contragredient action transports vanishing on a supported coordinate span.
Only the proved whole-annihilator image equality is used. -/
theorem verticalRestriction_dualAction_eq_zero (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R)) (hφ : verticalRestriction R z φ = 0) :
    verticalRestriction R z (dualAction g φ) = 0 := by
  rw [← LinearMap.mem_ker, ker_verticalRestriction, ← g.map_verticalAnnihilator hS z]
  exact ⟨φ, by rw [← ker_verticalRestriction]; exact hφ, rfl⟩

/-- The actual restriction square and paired commuting invariance transport centralizer
surjectivity. No projection arrow or dual exactness hypothesis is introduced. -/
theorem centralizerVerticalRestriction_surjective (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R))
    (hs : Function.Surjective (centralizerVerticalRestriction R z φ)) :
    Function.Surjective (centralizerVerticalRestriction R z (dualAction g φ)) := by
  intro ψ
  obtain ⟨μ, hμ⟩ := hs ((g.verticalDualEquiv hS z).symm ψ)
  refine ⟨⟨dualAction g μ.val, (g.mem_centralizer_dualAction_iff φ μ.val).mpr μ.property⟩, ?_⟩
  change verticalRestriction R z (dualAction g μ.val) = ψ
  change verticalRestriction R z μ.val = (g.verticalDualEquiv hS z).symm ψ at hμ
  have he := LinearMap.congr_fun (g.verticalRestriction_dualAction hS z) μ.val
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at he
  rw [he, hμ, LinearEquiv.apply_symm_apply]

/-- Annihilating an invariant marking plane transports to both actual ordered fibers. -/
theorem dualAction_delta_fiber_eq_zero (g : DiagramAut R C S) (H : Hyperplane k n)
    (w : Marking S n) (h₀ : H ≠ w.fiber (k := k) 0) (h₁ : H ≠ w.fiber (k := k) 1)
    (t : k₀) (ht : t = 0 ∨ t = 1) :
    dualCoordinates (dualAction g (Finsupp.lapply H)) (w.fiber t) = 0 := by
  classical
  have hmem : Finsupp.single (w.fiber (k := k) t) (1 : R) ∈ w.plane R := by
    rcases ht with rfl | rfl <;> exact Submodule.subset_span (by simp)
  have hinv : g.universalEquiv.symm (Finsupp.single (w.fiber t) 1) ∈ w.plane R := by
    rw [← g.map_markingPlane w] at hmem
    obtain ⟨x, hx, he⟩ := hmem
    rw [← he]
    change g.universalEquiv.symm (g.universalEquiv x) ∈ w.plane R
    rwa [LinearEquiv.symm_apply_apply]
  have hle : w.plane R ≤ LinearMap.ker (Finsupp.lapply H) := by
    rw [Marking.plane, Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl <;> simp [Ne.symm h₀, Ne.symm h₁]
  exact hle hinv

/-- Local detection recovers a unique hyperplane and dual unit from the actual transformed
coordinate delta. All four detection hypotheses are derived, rather than assumed as diagram
data. Blueprint: the construction step of I01 (`prop:i01`). -/
theorem exists_unit_delta_dualAction [IsLocalRing R] (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) :
    ∃! p : Hyperplane k n × Rˣ,
      dualAction g (Finsupp.lapply H) = (p.2 : R) • Finsupp.lapply p.1 := by
  classical
  obtain ⟨i, hi⟩ := exists_normal_coefficient_ne_zero_of_isEquation
    (isEquation_equation H.property)
  have hH : ¬IsVertical (omittedCoordinates i) H :=
    (not_isVertical_iff_of_isEquation i H (isEquation_equation H.property)).mpr hi
  have hprimitive : Primitive (dualAction g (Finsupp.lapply H)) := by
    apply (primitive_dualAction_iff g.universalEquiv (Finsupp.lapply H)).mpr
    exact primitive_of_isUnit_coordinate _ H (by simp)
  have hvertical := g.verticalRestriction_dualAction_eq_zero hS (omittedCoordinates i)
    (Finsupp.lapply H) (verticalRestriction_delta R _ H hH)
  obtain ⟨w, hw₀, -, hH₀, hH₁⟩ := exists_marking_graph_avoiding hS hn i H
  have hzero : ∃ H' : Hyperplane k n,
      ¬IsVertical (omittedCoordinates i) H' ∧
        dualCoordinates (dualAction g (Finsupp.lapply H)) H' = 0 :=
    ⟨w.fiber 0, hw₀, g.dualAction_delta_fiber_eq_zero H w hH₀ hH₁ 0 (Or.inl rfl)⟩
  have hs : Function.Surjective (centralizerVerticalRestriction R (omittedCoordinates i)
      (Finsupp.lapply H)) := by
    change Function.Surjective ((verticalRestriction R (omittedCoordinates i)).comp
      (centralizer (universalQuadraticRelationSpan R) (Finsupp.lapply H)).subtype)
    have hc : centralizer (universalQuadraticRelationSpan R)
        (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) = decomposition R H := by
      simpa using centralizer_unit_smul_delta R H 1
    rw [hc]
    exact decompositionVerticalRestriction_surjective R _ i (mem_omittedCoordinates i) H hH
  have hsurj := g.centralizerVerticalRestriction_surjective hS _ (Finsupp.lapply H) hs
  obtain ⟨K, u, -, he⟩ := (local_detection_iff R hn (omittedCoordinates i) i
    (mem_omittedCoordinates i) (dualAction g (Finsupp.lapply H))).mpr
      ⟨hprimitive, hvertical, hzero, hsurj⟩
  refine ⟨(K, u), he, ?_⟩
  rintro ⟨L, v⟩ he'
  obtain ⟨hKL, huv⟩ := (unit_smul_lapply_eq_iff u v K L).mp (he.symm.trans he')
  exact Prod.ext hKL.symm huv.symm

end DiagramAut

/-- Coordinate inertia lines at distinct labels are distinct over a nonzero coefficient
ring. This is direct coordinate separation, with no reflexivity or domain hypothesis. -/
theorem inertia_injective [Nontrivial R] :
    Function.Injective (inertia (k := k) (n := n) R) := by
  classical
  intro H K h
  by_contra hHK
  have hδ : (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) ∈ inertia R K := by
    rw [← h]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨a, ha⟩ := (mem_inertia R K _).mp hδ
  have he := LinearMap.congr_fun ha (Finsupp.single H 1)
  simp [hHK] at he

end OrlikSolomon.HyperplaneGT
