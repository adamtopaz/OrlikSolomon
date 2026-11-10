/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Geometry

/-!
# Coordinate levels and their trace geometry

The coordinate level hyperplanes use the existing affine graph construction. Verticality
passes to larger coordinate sets and to equations in a span. These coefficient facts identify
the guarded triples used in coordinate-span recognition and exclude unwanted equal traces.

Blueprint: the geometric part of P01 (`lem:p01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The coordinate level `x_i = t`, as an existing graph hyperplane. -/
def coordinateHyperplane (i : Fin n) (t : k) : Hyperplane k n :=
  graphHyperplane i (AffineMap.const k (omittedCoordinates i → k) t)

/-- Membership in a coordinate level is the corresponding coordinate equation. -/
@[simp]
theorem mem_coordinateHyperplane (i : Fin n) (t : k) (x : Fin n → k) :
    x ∈ (coordinateHyperplane i t).val ↔ x i = t := by
  simp [coordinateHyperplane, mem_graphSubspace]

private theorem coordinate_normal (i j : Fin n) (t : k) :
    affineCoefficients (graphEquation i (AffineMap.const k (omittedCoordinates i → k) t))
      j.succ = if i = j then 1 else 0 := by
  simp [affineCoefficients_succ, graphEquation, Pi.single_apply]

/-- A coordinate level uses exactly its distinguished coordinate. -/
@[simp]
theorem isVertical_coordinateHyperplane (z : Finset (Fin n)) (i : Fin n) (t : k) :
    IsVertical z (coordinateHyperplane i t) ↔ i ∈ z := by
  rw [isVertical_iff_of_isEquation _ _
    (isEquation_graphEquation i (AffineMap.const k (omittedCoordinates i → k) t))]
  constructor
  · intro h
    by_contra hi
    have hz := h i hi
    rw [coordinate_normal] at hz
    simp at hz
  · intro hi j hj
    have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
    rw [coordinate_normal]
    simp [hij]

/-- Enlarging a set of allowed coordinates preserves verticality. -/
theorem IsVertical.mono {z z' : Finset (Fin n)} {H : Hyperplane k n}
    (hH : IsVertical z H) (hz : z ⊆ z') : IsVertical z' H := by
  intro j hj
  exact hH j (fun h ↦ hj (hz h))

/-- Equations in the span of equations using a coordinate set use that same set. -/
theorem isVertical_of_equation_mem_span (z : Finset (Fin n)) (H K L : Hyperplane k n)
    (hK : IsVertical z K) (hL : IsVertical z L)
    (hH : equation H.val ∈ Submodule.span k {equation K.val, equation L.val}) :
    IsVertical z H := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hH
  intro j hj
  change affineCoefficients (equation H.val) j.succ = 0
  rw [← hab, map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    hK j hj, hL j hj, smul_zero, smul_zero, add_zero]

/-- A hyperplane parallel to a vertical hyperplane uses the same allowed coordinates. -/
theorem isVertical_of_parallel (z : Finset (Fin n)) (H K : Hyperplane k n)
    (hK : IsVertical z K) (hHK : Parallel H K) : IsVertical z H := by
  obtain ⟨c, hc⟩ :=
    (parallel_iff_normal_proportional K H hHK.1.symm
      (isEquation_equation K.property) (isEquation_equation H.property)).mp
        ((parallel_comm H K).mp hHK)
  intro j hj
  have hz := hK j hj
  rw [affineCoefficients_succ] at hz ⊢
  rw [hc, LinearMap.smul_apply, hz, smul_zero]

/-- The third equation in a guarded dependent triple uses the coordinates of the other two.
The nonempty intersection guard justifies the equation-span criterion. -/
theorem isVertical_of_dependentTriple (z : Finset (Fin n)) (H K L : Hyperplane k n)
    (hK : IsVertical z K) (hL : IsVertical z L) (hd : DependentTriple H K L) :
    IsVertical z H := by
  have hd' := (dependentTriple_rotate H K L).mp hd
  have hnot : ¬Parallel K L := by
    intro hp
    exact hd'.2.2.2.1 (by rw [hp.2, bot_inf_eq])
  apply isVertical_of_equation_mem_span z H K L hK hL
  exact (dependentTriple_iff_equation_mem_span K L H hd'.1 hd'.2.1 hd'.2.2.1 hnot
    (isEquation_equation K.property) (isEquation_equation L.property)
    (isEquation_equation H.property)).mp hd'

/-- A label outside the enlarged coordinate set differs from every level of the added
coordinate. -/
theorem ne_coordinateHyperplane_of_not_isVertical_insert (z : Finset (Fin n)) (i : Fin n)
    (H : Hyperplane k n) (hH : ¬IsVertical (insert i z) H) (t : k) :
    H ≠ coordinateHyperplane i t := by
  intro heq
  apply hH
  rw [heq]
  simp

/-- A label outside the enlarged coordinate set is not parallel to a coordinate level. -/
theorem not_parallel_coordinateHyperplane_of_not_isVertical_insert
    (z : Finset (Fin n)) (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (insert i z) H) (t : k) : ¬Parallel H (coordinateHyperplane i t) := by
  intro hp
  exact hH (isVertical_of_parallel (insert i z) H _ (by simp) hp)

/-- The coordinate trace of a label outside the enlarged span cannot coincide with a
nonempty trace of an old vertical label. This retains the guarded dependence criterion. -/
theorem not_dependentTriple_coordinateHyperplane_of_not_isVertical_insert
    (z : Finset (Fin n)) (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (insert i z) H) (K : Hyperplane k n) (hK : IsVertical z K) :
    ¬DependentTriple H (coordinateHyperplane i 0) K := by
  intro hd
  exact hH (isVertical_of_dependentTriple (insert i z) H _ K (by simp)
    (hK.mono (Finset.subset_insert i z)) hd)

/-- A hyperplane using one added coordinate is already old-vertical, equal or parallel to
a level of that coordinate, or forms a guarded triple with an old-vertical hyperplane.
The equation-span criterion supplies the nonempty intersection in the last case.
Blueprint: the forward configuration step in P01 (`lem:p01`). -/
theorem coordinate_cases_of_isVertical_insert (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z)
    (H : Hyperplane k n) (hH : IsVertical (insert i z) H) (t : k) :
    IsVertical z H ∨ H = coordinateHyperplane i t ∨ Parallel H (coordinateHyperplane i t) ∨
      ∃ K : Hyperplane k n, IsVertical z K ∧ DependentTriple H (coordinateHyperplane i t) K := by
  by_cases hz : IsVertical z H
  · exact Or.inl hz
  refine Or.inr ?_
  by_cases hHK : H = coordinateHyperplane i t
  · exact Or.inl hHK
  refine Or.inr ?_
  let f := equation H.val
  let g := graphEquation i (AffineMap.const k (omittedCoordinates i → k) t)
  let a := affineCoefficients f i.succ
  have hf : IsEquation f H.val := isEquation_equation H.property
  have hg : IsEquation g (coordinateHyperplane i t).val := isEquation_graphEquation i _
  have ha : a ≠ 0 := by
    intro ha
    apply hz
    intro j hj
    by_cases hji : j = i
    · subst j
      exact ha
    · exact hH j (by simp [hji, hj])
  let v := f - a • g
  have hvcoeff (j : Fin n) (hj : j ∉ z) : affineCoefficients v j.succ = 0 := by
    change affineCoefficients (f - a • g) j.succ = 0
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply]
    change affineCoefficients f j.succ - a •
      affineCoefficients (graphEquation i (AffineMap.const k (omittedCoordinates i → k) t))
        j.succ = 0
    rw [coordinate_normal]
    by_cases hij : i = j
    · subst j
      simp [a]
    · have hzj := hH j (by simp [Ne.symm hij, hj])
      simp [hij, f, hzj]
  by_cases hv : v.linear = 0
  · apply Or.inl
    apply (parallel_comm (coordinateHyperplane i t) H).mp
    apply (parallel_iff_normal_proportional _ _ (Ne.symm hHK) hg hf).mpr
    change f.linear - a • g.linear = 0 at hv
    exact ⟨Units.mk0 a ha, sub_eq_zero.mp hv⟩
  · apply Or.inr
    let K : Hyperplane k n := ⟨zeroLocus v, isHyperplane_zeroLocus_iff.mpr hv⟩
    have hvK : IsEquation v K.val := ⟨hv, rfl⟩
    have hK : IsVertical z K := (isVertical_iff_of_isEquation z K hvK).mpr hvcoeff
    have hHK' : H ≠ K := fun h ↦ hz (h.symm ▸ hK)
    have hcoordK : coordinateHyperplane i t ≠ K := by
      intro h
      apply hi
      rw [← isVertical_coordinateHyperplane z i t, h]
      exact hK
    have hnot : ¬Parallel H (coordinateHyperplane i t) := by
      intro hp
      obtain ⟨c, hc⟩ := (parallel_iff_normal_proportional _ _ (Ne.symm hHK) hg hf).mp
        ((parallel_comm H (coordinateHyperplane i t)).mp hp)
      have hca : (c : k) = a := by
        dsimp [a]
        rw [affineCoefficients_succ, hc, LinearMap.smul_apply]
        simp [g, graphEquation]
      apply hv
      change f.linear - a • g.linear = 0
      rw [← hca, hc, sub_self]
    refine ⟨K, hK, (dependentTriple_iff_equation_mem_span H _ K hHK hHK' hcoordK hnot
      hf hg hvK).mpr ?_⟩
    apply Submodule.sub_mem
    · exact Submodule.subset_span (by simp)
    · exact Submodule.smul_mem _ a (Submodule.subset_span (by simp))

end OrlikSolomon.HyperplaneGT
