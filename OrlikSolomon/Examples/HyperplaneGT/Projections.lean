/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections
public import OrlikSolomon.Examples.HyperplaneGT.Dual

/-!
# Coordinate recognition and equivariant restriction consumers

An actual coordinate label over `𝔽₂` gives a nonzero nilpotent-valued detector over `ℤ/4`.
Arbitrary supported restrictions work over `ℕ`, while recognition also works over the zero
ring. Low-dimensional and full-coordinate cases use the literal supported modules. The
scalar-two marked diagram over `ℤ/5` acts on a nonzero vertical dual coordinate by three,
checking the inverse convention through the actual restriction square. Both restricted
actions retain ordinary inverse cancellation.

Blueprint: regression consumers for P01–P02 (`lem:p01`, `prop:p02`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.ProjectionExamples

universe u v w

/-- An actual outside coordinate in characteristic-two geometry is detected with nonzero
nilpotent value `2` over `ℤ/4`; the detector commutes with its delta and annihilates the old span.
-/
theorem binary_nilpotent_detector :
    ∃ ψ : Module.Dual (ZMod 4) (Hyperplane (ZMod 2) 3 →₀ ZMod 4),
      ψ ∈ (verticalModule (ZMod 4) ({0} : Finset (Fin 3))).dualAnnihilator ∧
      Commutes (universalQuadraticRelationSpan (ZMod 4))
        (Finsupp.lapply (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2))) ψ ∧
      dualDeterminant (Finsupp.lapply (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2))) ψ
        (exteriorPower.ιMulti (ZMod 4) 2
          ![Finsupp.single (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2)) 2,
            Finsupp.single (coordinateHyperplane (1 : Fin 3) (0 : ZMod 2)) 1]) = 2 ∧
      (2 : ZMod 4) ≠ 0 := by
  obtain ⟨ψ, hD, hz, he⟩ := exists_coordinateSpan_detector (ZMod 4)
    ({0} : Finset (Fin 3)) 1 (by decide)
    (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2)) (by simp)
  refine ⟨ψ, hz, ?_, ?_, by decide⟩
  · rw [← mem_centralizer_iff]
    have hc : centralizer (universalQuadraticRelationSpan (ZMod 4))
        (Finsupp.lapply (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2))) =
          decomposition (ZMod 4) (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2)) := by
      simpa using centralizer_unit_smul_delta (ZMod 4)
        (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2)) 1
    rw [hc]
    exact hD
  · simpa using he (Finsupp.single (coordinateHyperplane (2 : Fin 3) (0 : ZMod 2)) 2)

/-- Restriction to any coordinate-supported span extends functionals even over `ℕ`, where
subtraction and field-valued dual exactness are unavailable. -/
theorem natural_restriction_surjective (k : Type u) [Field k] (n : ℕ)
    (z : Finset (Fin n)) : Function.Surjective (verticalRestriction (k := k) ℕ z) :=
  verticalRestriction_surjective ℕ z

/-- Recognition includes the zero coefficient ring and imposes no dimension lower bound. -/
theorem zero_ring_recognition {k : Type u} [Field k] {n : ℕ}
    (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z) (a : Hyperplane k n →₀ ZMod 1) :
    a ∈ verticalModule (ZMod 1) (insert i z) ∧
      ∀ b : Hyperplane k n →₀ ZMod 1, b ∈ coordinatePlane (ZMod 1) i →
      ∀ φ ψ : Module.Dual (ZMod 1) (Hyperplane k n →₀ ZMod 1),
        φ ∈ (verticalModule (ZMod 1) z).dualAnnihilator →
        ψ ∈ (verticalModule (ZMod 1) z).dualAnnihilator →
        Commutes (universalQuadraticRelationSpan (ZMod 1)) φ ψ →
        dualDeterminant φ ψ (exteriorPower.ιMulti (ZMod 1) 2 ![a, b]) = 0 := by
  have ha : a ∈ verticalModule (ZMod 1) (insert i z) := by
    rw [Subsingleton.elim a 0]
    exact Submodule.zero_mem _
  exact ⟨ha, (coordinateSpan_recognition (ZMod 1) z i hi a).mp ha⟩

/-- In dimension zero there is no nonzero vector in the actual supported module. -/
theorem dimension_zero_supported {k : Type u} [Field k] (R : Type v) [CommRing R]
    (x : verticalModule (k := k) R (∅ : Finset (Fin 0))) : x = 0 := by
  apply Subtype.ext
  simpa only [verticalModule_empty, Submodule.mem_bot, Submodule.coe_zero] using x.property

/-- With all coordinates present every vector satisfies the recognition test, including
in dimension one. -/
theorem full_coordinate_test {k : Type u} [Field k] {n : ℕ}
    (R : Type v) [CommRing R] (i : Fin n) (a : Hyperplane k n →₀ R) :
    ∀ b : Hyperplane k n →₀ R, b ∈ coordinatePlane R i →
    ∀ φ ψ : Module.Dual R (Hyperplane k n →₀ R),
      φ ∈ (verticalModule R (Finset.univ.erase i)).dualAnnihilator →
      ψ ∈ (verticalModule R (Finset.univ.erase i)).dualAnnihilator →
      Commutes (universalQuadraticRelationSpan R) φ ψ →
      dualDeterminant φ ψ (exteriorPower.ιMulti R 2 ![a, b]) = 0 := by
  apply (coordinateSpan_recognition R _ i (Finset.notMem_erase i _) a).mp
  rw [mem_verticalModule]
  intro H hH
  exact (hH (by intro j hj; exact (hj (by simp)).elim)).elim

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  {R : Type w} [CommRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The two inverse-cancellation forms simplify for the actual restricted primal action. -/
theorem primal_inverse_cancellation (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) (x : verticalModule (k := k) R z) :
    (g.verticalEquiv hS z).symm (g.verticalEquiv hS z x) = x ∧
      g.verticalEquiv hS z ((g.verticalEquiv hS z).symm x) = x := by simp

/-- The two inverse-cancellation forms also simplify on the entire vertical dual. -/
theorem dual_inverse_cancellation (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) (ψ : Module.Dual R (verticalModule (k := k) R z)) :
    (g.verticalDualEquiv hS z).symm (g.verticalDualEquiv hS z ψ) = ψ ∧
      g.verticalDualEquiv hS z ((g.verticalDualEquiv hS z).symm ψ) = ψ := by simp

/-- The scalar-two diagram's induced vertical dual action evaluates as inverse scalar three,
through the actual equivariant restriction square and a nonzero vertical coordinate. -/
theorem scalar_two_vertical_inverse :
    (DualExamples.scalarTwoDiagram (fullCofinalSystem (ZMod 2) (ZMod 2) 2) {0, 1}).verticalDualEquiv
      (by simp) ({0} : Finset (Fin 2))
      (verticalRestriction (ZMod 5) {0}
        (Finsupp.lapply (coordinateHyperplane (0 : Fin 2) (0 : ZMod 2))))
      (verticalSingle (ZMod 5) {0}
        ⟨coordinateHyperplane (0 : Fin 2) (0 : ZMod 2), by simp⟩ 1) = 3 := by
  let g := DualExamples.scalarTwoDiagram (fullCofinalSystem (ZMod 2) (ZMod 2) 2) {0, 1}
  have he := LinearMap.congr_fun (g.verticalRestriction_dualAction (by simp) {0})
    (Finsupp.lapply (coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)))
  have hv := LinearMap.congr_fun he
    (verticalSingle (ZMod 5) {0}
      ⟨coordinateHyperplane (0 : Fin 2) (0 : ZMod 2), by simp⟩ 1)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, verticalRestriction_apply,
    coe_verticalSingle] at hv
  exact hv.symm.trans (DualExamples.scalarTwo_dual_coordinate _ _ _)

end OrlikSolomon.HyperplaneGT.ProjectionExamples
