/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing
public import OrlikSolomon.Examples.HyperplaneGT.GaloisReconstruction
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local quadratic-classification regressions

Strict consumers use independent geometric-field and coefficient universes, arbitrary
chosen cofinal systems, the actual common target and whole marking maps. They check both
explicit inverse equations, ordinary inverse cancellation, and the same label with inverse
primal/dual units. Concrete cases use the non-involutive unit two over `ℤ/5`, nilpotents in
the nonfield local ring `ℤ/4`, and a genuinely nontrivial complex-conjugation Galois factor.
Pure scalar boundary tests retain dimension zero and the zero coefficient ring without
applying reconstruction outside its hypotheses.

Blueprint: S03 (`thm:s03`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.LocalClassificationExamples

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {R : Type w} [CommRing R] [IsLocalRing R]
  (C : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Both explicit inverse equations retain the actual common scalar and field components. -/
theorem explicit_inverse_equations (a : Rˣ) (σ : k ≃ₐ[k₀] k) (g : DiagramAut R C S) :
    (quadraticAutEquiv R C S hS hgen hn).symm
        (scalarQuadraticAut R C S a * galoisQuadraticAut R C S σ) = (a, σ) ∧
      scalarQuadraticAut R C S (g.scalarPart hS hgen hn) *
        galoisQuadraticAut R C S (DiagramAut.toGalois R C S hS hgen hn g) = g :=
  ⟨quadraticAutEquiv_left_inv R C S hS hgen hn a σ,
    quadraticAutEquiv_right_inv R C S hS hgen hn g⟩

/-- Ordinary cancellation works for both directions of the canonical multiplicative
equivalence, including a concrete pair of components. -/
theorem inverse_cancellation (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut R C S)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    (quadraticAutEquiv R C S hS hgen hn).symm
        (quadraticAutEquiv R C S hS hgen hn p) = p ∧
      quadraticAutEquiv R C S hS hgen hn
        ((quadraticAutEquiv R C S hS hgen hn).symm g) = g ∧
      (quadraticAutEquiv R C S hS hgen hn).symm
        (quadraticAutEquiv R C S hS hgen hn (a, σ)) = (a, σ) := by simp

/-- Classification is multiplicative and inversion cancels on both sides in the actual
diagram group, without changing the order of the field action. -/
theorem group_laws (p q : Rˣ × (k ≃ₐ[k₀] k)) :
    quadraticAutEquiv R C S hS hgen hn (p * q) =
        quadraticAutEquiv R C S hS hgen hn p * quadraticAutEquiv R C S hS hgen hn q ∧
      quadraticAutEquiv R C S hS hgen hn p⁻¹ *
        quadraticAutEquiv R C S hS hgen hn p = 1 ∧
      quadraticAutEquiv R C S hS hgen hn p *
        quadraticAutEquiv R C S hS hgen hn p⁻¹ = 1 := by simp

/-- The actual primal and dual modules use opposite units and the same transformed label. -/
theorem primal_dual_components (a : Rˣ) (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).universalEquiv (Finsupp.single H 1) =
        (a : R) • Finsupp.single (σ • H) 1 ∧
      DiagramAut.dualAction (quadraticAutEquiv R C S hS hgen hn (a, σ))
        (Finsupp.lapply H) = (↑a⁻¹ : R) • Finsupp.lapply (σ • H) ∧
      (quadraticAutEquiv R C S hS hgen hn (a, σ)).hyperplaneUnit hS hn H = a⁻¹ := by
  rw [quadraticAutEquiv_universalEquiv_single, quadraticAutEquiv_dualAction_delta,
    quadraticAutEquiv_hyperplaneUnit]
  exact ⟨rfl, rfl, rfl⟩

/-- Whole finite-stage marking maps commute with the same nontrivial common-target scalar. -/
theorem whole_marking_square (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (m : Marking S n) (hm : m.Available A.val.val) (x : Fin 2 →₀ R) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).stageEquiv A (m.basisMap R hm x) =
        m.basisMap R hm ((a : R) • x) ∧
      (quadraticAutEquiv R C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x :=
  ⟨quadraticAutEquiv_marking R C S hS hgen hn a σ A m hm x,
    quadraticAutEquiv_targetEquiv_apply R C S hS hgen hn a σ x⟩

/-- The explicit inverse's scalar component has the group law on the original family. -/
theorem scalar_projection_laws (g h : DiagramAut R C S) :
    (g * h).scalarPart hS hgen hn = g.scalarPart hS hgen hn * h.scalarPart hS hgen hn ∧
      g⁻¹.scalarPart hS hgen hn = (g.scalarPart hS hgen hn)⁻¹ := by simp

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The canonical classification uses primal two and dual three over `ℤ/5`, retaining its
nontrivial common-target component. -/
theorem scalar_two_inverse_three :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let e := quadraticAutEquiv (ZMod 5) C S (by simp [S]) (Subsingleton.elim _ _) (by decide)
    let g := e (DualExamples.scalarTwoUnit, 1)
    let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
    e.symm g = (DualExamples.scalarTwoUnit, 1) ∧
      g.universalEquiv (Finsupp.single H 1) H = 2 ∧
      DiagramAut.dualAction g (Finsupp.lapply H) (Finsupp.single H 1) = 3 ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 2 ∧ (3 : ZMod 5) ≠ 2 := by
  dsimp only
  refine ⟨by simp, ?_, ?_, ?_, by decide⟩
  · rw [quadraticAutEquiv_universalEquiv_single]
    simp [DualExamples.scalarTwoUnit]
  · rw [quadraticAutEquiv_dualAction_delta]
    simp [DualExamples.scalarTwoUnit]
  · simp [DualExamples.scalarTwoUnit]

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- The canonical family is nontrivial over the nonfield local ring `ℤ/4` and preserves
the nonzero nilpotent coefficient two on the actual common target. -/
theorem mod_four_nilpotent_target :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let e := quadraticAutEquiv (ZMod 4) C S (by simp [S]) (Subsingleton.elim _ _) (by decide)
    let g := e (IncidenceExamples.scalarThreeUnit, 1)
    e.symm g = (IncidenceExamples.scalarThreeUnit, 1) ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      g.targetEquiv (Finsupp.single 0 2) 0 = 2 ∧
      (3 : ZMod 4) ≠ 1 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4)^2 = 0 := by
  dsimp only
  refine ⟨by simp, ?_, ?_, by decide, by decide, by decide⟩
  · simp [IncidenceExamples.scalarThreeUnit]
  · simp only [quadraticAutEquiv_targetEquiv_apply, Finsupp.smul_single,
      smul_eq_mul, Finsupp.single_eq_same]
    decide

/-- Complex conjugation supplies an actually nontrivial Galois coordinate, independently
of the nonfield coefficient ring. The supplied system is constructed using `ℂ/ℝ` only. -/
theorem conjugation_mod_four :
    let C := fullCofinalSystem ℝ ℂ 2
    let S : Set ℝ := Set.univ
    let e := quadraticAutEquiv (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide)
    let g := e (IncidenceExamples.scalarThreeUnit, Complex.conjAe)
    e.symm g = (IncidenceExamples.scalarThreeUnit, Complex.conjAe) ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) g
        Complex.I = -Complex.I ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) g ≠ 1 ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 := by
  dsimp only
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [toGalois_quadraticAutEquiv]
    simp
  · rw [toGalois_quadraticAutEquiv]
    intro he
    have h := congrArg (fun σ : ℂ ≃ₐ[ℝ] ℂ ↦ (σ Complex.I).im) he
    norm_num at h
  · simp [IncidenceExamples.scalarThreeUnit]

/-- Scalar embedding is still injective in dimension zero with zero coefficients and no
markings; the final local classification is not being extended to these parameters. -/
theorem zero_ring_dimension_zero (C : CofinalSystem k₀ k 0) (a b : (ZMod 1)ˣ)
    (h : scalarQuadraticAction (ZMod 1) C ∅ a = scalarQuadraticAction (ZMod 1) C ∅ b) :
    a = b ∧ (scalarQuadraticAut (ZMod 1) C ∅ a).targetEquiv (Finsupp.single 0 1) = 0 :=
  ⟨scalarQuadraticAction_injective (ZMod 1) C ∅ h, Subsingleton.elim _ _⟩

/-- In dimension zero the universal module is zero but the retained common-target scalar
is detected. Thus target data cannot be discarded by universal extensionality. -/
theorem dimension_zero_retained_target :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 0
    let g := scalarQuadraticAut (ZMod 5) C ∅ DualExamples.scalarTwoUnit
    g.universalEquiv = 1 ∧ g.targetEquiv (Finsupp.single 0 1) 0 = 2 ∧
      g ≠ 1 := by
  dsimp only
  refine ⟨?_, by simp [DualExamples.scalarTwoUnit], ?_⟩
  · apply LinearEquiv.ext
    intro x
    ext H
    exact ((CoordinateExamples.dimension_zero (k := ZMod 2)).false H).elim
  · intro he
    have h := congrArg (fun g : DiagramAut (ZMod 5)
      (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅ ↦
        g.targetEquiv (Finsupp.single 0 1) 0) he
    exact (by decide : (2 : ZMod 5) ≠ 1) (by simpa [DualExamples.scalarTwoUnit] using h)

end OrlikSolomon.HyperplaneGT.LocalClassificationExamples
