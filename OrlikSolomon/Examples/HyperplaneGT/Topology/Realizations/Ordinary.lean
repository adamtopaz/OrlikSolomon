/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.DeRhamReconstruction
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Realizations
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology

/-!
# Final ordinary de Rham topological reconstruction consumers

All thirty-two ordinary bundles retain both bare inverse cancellations. Whole-degree and
actual marked-pullback formulas retain the original common target. The constructed
characteristic-zero fixtures use genuine moved complex logarithms, both nonzero ordered
target dlogs with a nonidentity unit, a nontrivial conjugation scalar class and noncompact
groups with profinite literal scalar quotients.

This size-only leaf preserves every earlier Realizations namespace and keeps the incoming
two-realization consumers below the file-size boundary. It is not re-exported from its
parent, so the imports have no cycle. No supplied theory or new global instance is used.
Blueprint: acceptance consumers for T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u b

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham.ReconstructionTopologyExamples

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type b} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

section

open scoped GaloisPointwise

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadraticContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut C S) :
    (quadraticContinuousReconstruction C S hS hgen hn).symm (quadraticContinuousReconstruction C S
      hS hgen hn p) = p ∧
      quadraticContinuousReconstruction C S hS hgen hn ((quadraticContinuousReconstruction C S hS
        hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem gradedContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut C
    S) :
    (gradedContinuousReconstruction C S hS hgen hn).symm (gradedContinuousReconstruction C S hS
      hgen hn p) = p ∧
      gradedContinuousReconstruction C S hS hgen hn ((gradedContinuousReconstruction C S hS hgen
        hn).symm g) = g := by simp

end

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadraticKrullContinuousReconstruction_roundtrip (hK : KrullFixingCondition k₀ k) (p : kˣ
    × (k ≃ₐ[k₀] k)) (g : DiagramAut C S) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm
      (quadraticKrullContinuousReconstruction C S hS hgen hn hK p) = p ∧
      quadraticKrullContinuousReconstruction C S hS hgen hn hK
        ((quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem gradedKrullContinuousReconstruction_roundtrip (hK : KrullFixingCondition k₀ k) (p : kˣ ×
    (k ≃ₐ[k₀] k)) (g : GradedDiagramAut C S) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).symm
      (gradedKrullContinuousReconstruction C S hS hgen hn hK p) = p ∧
      gradedKrullContinuousReconstruction C S hS hgen hn hK ((gradedKrullContinuousReconstruction
        C S hS hgen hn hK).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_roundtrip [Algebra.IsAlgebraic k₀ k]
    (p : kˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut C S) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm
      (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) = p ∧
      quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn
        ((quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_roundtrip [Algebra.IsAlgebraic k₀ k] (p :
    kˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut C S) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm
      (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) = p ∧
      gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn
        ((gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g) = g := by simp

section

open scoped GaloisPointwise

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem restrictionContinuousEquiv_roundtrip (g : GradedDiagramAut C S) (q : DiagramAut C S) :
    (restrictionContinuousEquiv C S hS hgen hn).symm
      (restrictionContinuousEquiv C S hS hgen hn g) = g ∧
    restrictionContinuousEquiv C S hS hgen hn
      ((restrictionContinuousEquiv C S hS hgen hn).symm q) = q := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadratic_scalarQuotientContinuousEquiv_roundtrip (z : DiagramAut C S ⧸
    DiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn).symm
      (DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn z) = z ∧
      DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn
        ((DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn).symm σ) = σ := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem graded_scalarQuotientContinuousEquiv_roundtrip (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn z) = z ∧
      GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn
        ((GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn).symm σ) = σ := by simp

end

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadratic_scalarQuotientKrullContinuousEquiv_roundtrip (hK : KrullFixingCondition k₀ k) (z
    : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm
      (DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z ∧
      DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK
        ((DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ) = σ := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem graded_scalarQuotientKrullContinuousEquiv_roundtrip (hK : KrullFixingCondition k₀ k) (z :
    GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm
      (GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z ∧
      GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK
        ((GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ) = σ := by
        simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadratic_scalarQuotientKrullContinuousEquivOfIsAlgebraic_roundtrip [Algebra.IsAlgebraic
    k₀ k] (z : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm
      (DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) = z ∧
      DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn
        ((DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ) = σ
        := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem graded_scalarQuotientKrullContinuousEquivOfIsAlgebraic_roundtrip [Algebra.IsAlgebraic k₀
    k] (z : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) = z ∧
      GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn
        ((GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ)
        = σ := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem scalarQuotientRestrictionContinuousEquiv_roundtrip (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) (w : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm
      (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn z) = z ∧
      scalarQuotientRestrictionContinuousEquiv C S hS hgen hn
        ((scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem cofinalRestrictionContinuousEquiv_roundtrip (hC : C'.stages ⊆ C.stages) (z : DiagramAut C
    S) (w : DiagramAut C' S) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm
      (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn z) = z ∧
      cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn ((cofinalRestrictionContinuousEquiv C
        C' S hC hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem gradedCofinalRestrictionContinuousEquiv_roundtrip (hC : C'.stages ⊆ C.stages) (z :
    GradedDiagramAut C S) (w : GradedDiagramAut C' S) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn z) = z ∧
      gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn
        ((gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm w) = w := by simp

section

open scoped GaloisPointwise

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem cofinalScalarQuotientContinuousEquiv_roundtrip (hC : C'.stages ⊆ C.stages) (z : DiagramAut
    C S ⧸ DiagramAut.scalarSubgroup C S) (w : DiagramAut C' S ⧸ DiagramAut.scalarSubgroup C' S) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm
      (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z) = z ∧
      cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
        ((cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm w) = w := by simp

end

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_roundtrip (hC : C'.stages ⊆ C.stages) (z :
    GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) (w : GradedDiagramAut C' S ⧸
    GradedDiagramAut.scalarSubgroup C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm
      (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z) = z ∧
      gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
        ((gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm w) = w := by simp

section FullFamily

variable [Algebra.IsAlgebraic k₀ k]

local notation "F" => fullCofinalSystem k₀ k n

section

open scoped GaloisPointwise

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullQuadraticContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut F
    S) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn p) = p ∧
      fullQuadraticContinuousReconstruction (k := k) S hS hgen hn
      ((fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadratic_fullScalarQuotientContinuousEquiv_roundtrip (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm
      (DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z) = z ∧
      DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn
      ((DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullGradedContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut
    F S) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullGradedContinuousReconstruction (k := k) S hS hgen hn p) = p ∧
      fullGradedContinuousReconstruction (k := k) S hS hgen hn
      ((fullGradedContinuousReconstruction (k := k) S hS hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem graded_fullScalarQuotientContinuousEquiv_roundtrip (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm
      (GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z) = z ∧
      GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn
      ((GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ :=
      by simp

end

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullQuadraticKrullContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g :
    DiagramAut F S) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn p) = p ∧
      fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn
      ((fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem quadratic_fullScalarQuotientKrullContinuousEquiv_roundtrip (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm
      (DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) = z ∧
      DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn
      ((DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ := by
      simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullGradedKrullContinuousReconstruction_roundtrip (p : kˣ × (k ≃ₐ[k₀] k)) (g :
    GradedDiagramAut F S) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p) = p ∧
      fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn
      ((fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm g) = g := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem graded_fullScalarQuotientKrullContinuousEquiv_roundtrip (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm
      (GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) = z ∧
      GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn
      ((GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ
      := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullRestrictionContinuousEquiv_roundtrip (z : GradedDiagramAut F S) (w : DiagramAut F S) :
    (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm (fullRestrictionContinuousEquiv (k
      := k) S hS hgen hn z) = z ∧ fullRestrictionContinuousEquiv (k := k) S hS hgen hn
      ((fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_roundtrip (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) (w : DiagramAut F S ⧸ DiagramAut.scalarSubgroup F S) :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm
      (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn z) = z ∧
      fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn
      ((fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullCofinalRestrictionContinuousEquiv_roundtrip (z : DiagramAut F S) (w : DiagramAut C S) :
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn).symm
      (fullCofinalRestrictionContinuousEquiv C S hS hgen hn z) = z ∧
      fullCofinalRestrictionContinuousEquiv C S hS hgen hn ((fullCofinalRestrictionContinuousEquiv
      C S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_roundtrip (z : GradedDiagramAut F S) (w :
    GradedDiagramAut C S) :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm
      (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn z) = z ∧
      fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn
      ((fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullCofinalScalarQuotientContinuousEquiv_roundtrip (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) (w : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm
      (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) = z ∧
      fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn
      ((fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm w) = w := by simp

/-- Both bare inverse cancellations retain the exact original ordinary maps. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_roundtrip (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) (w : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm
      (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) = z ∧
      fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn
      ((fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm w) = w := by simp

end FullFamily

section WholeActions

open scoped GaloisPointwise

include hS hgen hn

/-- Every whole ordinary degree-zero class has scalar power one, rather than the unit. -/
theorem whole_degree_zero (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val 0) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
        Geometric.DeRham.affineEquiv A.val.val (galoisOSAlgebraEquiv k A.val σ x) := by
  simpa only [pow_zero, one_smul] using
    gradedContinuousReconstruction_stage_degree C S hS hgen hn a σ A 0 x hx

/-- Every whole ordinary degree-two class has the primal square, with covariant labels. -/
theorem whole_degree_two (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val 2) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
        (a : k)^2 • Geometric.DeRham.affineEquiv A.val.val
          (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedContinuousReconstruction_stage_degree C S hS hgen hn a σ A 2 x hx

/-- The actual marked scheme pullback uses the same whole common-target degree power. -/
theorem whole_marking_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (q : ℕ)
    (x : Geometric.DeRham.Cohomology.degree
      (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)) q) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap (Geometric.SmoothDomain.aff k) hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap (Geometric.SmoothDomain.aff k) hw)
        ((a : k)^q • (x : Geometric.DeRham.Cohomology _)) :=
  gradedContinuousReconstruction_marking_degree C S hS hgen hn a σ A w hw q x

/-- Characteristic-zero ordinary groups are locally compact and noncompact; their original
scalar quotients are compact, Hausdorff and totally separated, with no K or algebraicity. -/
theorem ordinary_topological_consequences :
    LocallyCompactSpace (DiagramAut C S) ∧ LocallyCompactSpace (GradedDiagramAut C S) ∧
      ¬ CompactSpace (DiagramAut C S) ∧ ¬ CompactSpace (GradedDiagramAut C S) ∧
      CompactSpace (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) ∧
      CompactSpace (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ∧
      T2Space (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) ∧
      T2Space (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ∧
      TotallySeparatedSpace (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) ∧
      TotallySeparatedSpace (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) :=
  ⟨DiagramAut.locallyCompactSpace C S hS hgen hn,
    GradedDiagramAut.locallyCompactSpace C S hS hgen hn,
    DiagramAut.not_compactSpace C S hS hgen hn,
    GradedDiagramAut.not_compactSpace C S hS hgen hn,
    DiagramAut.scalarQuotient_compactSpace C S hS hgen hn,
    GradedDiagramAut.scalarQuotient_compactSpace C S hS hgen hn,
    DiagramAut.scalarQuotient_t2Space C S hS hgen hn,
    GradedDiagramAut.scalarQuotient_t2Space C S hS hgen hn,
    DiagramAut.scalarQuotient_totallySeparatedSpace C S hS hgen hn,
    GradedDiagramAut.scalarQuotient_totallySeparatedSpace C S hS hgen hn⟩

end WholeActions

section Constructed

open scoped GaloisPointwise

-- The concrete logarithm crosses the inherited nested scheme/diagonal carriers,
-- exactly as its existing ordinary M8 fixture does.
set_option maxRecDepth 2000 in
/-- The new continuous full classifier acts on a genuinely moved nonzero ordinary logarithm
by the covariant complex-conjugate hyperplane label. Its coefficients remain complex-linear. -/
theorem constructed_conjugation_logarithm :
    (fullGradedContinuousReconstruction (k₀ := ℝ) (k := ℂ) (n := 2)
      Set.univ (by simp) (by simp) (by decide) (1, Complex.conjAe)).stageEquiv
        Examples.imaginaryStage (Examples.logarithm Examples.imaginaryLabel) =
          Examples.logarithm Examples.conjugateLabel :=
  Examples.conjugation_logarithm

/-- The same nonidentity primal unit scales both actual nonzero ordered target dlogs under
the new continuous full classifier, including its nontrivial conjugation coordinate. -/
theorem constructed_target_dlog_two (i : Fin 2) :
    let e := fullGradedContinuousReconstruction (k₀ := ℝ) (k := ℂ) (n := 2)
      Set.univ (by simp) (by simp) (by decide)
    let x := OrlikSolomon.DeRham.dlogClass ℂ
      (A := Geometric.globalSections
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff ℂ)).obj)
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff ℂ) i)
    (e (Examples.complexTwo, Complex.conjAe)).targetEquiv x = (2 : ℂ) • x ∧
      (e (Examples.complexTwo, Complex.conjAe)).targetEquiv x ≠ x :=
  Examples.target_two i

/-- A genuine nonidentity ordinary quotient class is read by the new full continuous map,
using all real marking constants rather than a nongenerating singleton. -/
theorem constructed_conjugation_quotient :
    let C := fullCofinalSystem ℝ ℂ 2
    let e := DiagramAut.fullScalarQuotientContinuousEquiv (k₀ := ℝ) (k := ℂ) (n := 2)
      Set.univ (by simp) (by simp) (by decide)
    e (DiagramAut.scalarQuotientSection C Set.univ Complex.conjAe) = Complex.conjAe ∧
      DiagramAut.scalarQuotientSection C Set.univ Complex.conjAe ≠ 1 :=
  ⟨DiagramAut.fullScalarQuotientContinuousEquiv_section (k₀ := ℝ) (k := ℂ) (n := 2)
      Set.univ (by simp) (by simp) (by decide) Complex.conjAe,
    TopologyExamples.ordinary_conjugation_class_ne_one⟩

/-- Actual constructed characteristic-zero ordinary groups are noncompact, while both
literal scalar quotients are compact, Hausdorff and totally separated. -/
theorem constructed_noncompact_profinite :
    let C := fullCofinalSystem ℝ ℂ 2
    ¬ CompactSpace (DiagramAut C Set.univ) ∧ ¬ CompactSpace (GradedDiagramAut C Set.univ) ∧
      CompactSpace (DiagramAut C Set.univ ⧸ DiagramAut.scalarSubgroup C Set.univ) ∧
      CompactSpace (GradedDiagramAut C Set.univ ⧸ GradedDiagramAut.scalarSubgroup C Set.univ) ∧
      T2Space (DiagramAut C Set.univ ⧸ DiagramAut.scalarSubgroup C Set.univ) ∧
      TotallySeparatedSpace (GradedDiagramAut C Set.univ ⧸
        GradedDiagramAut.scalarSubgroup C Set.univ) := by
  dsimp only
  exact ⟨DiagramAut.not_compactSpace _ _ (by simp) (by simp) (by decide),
    GradedDiagramAut.not_compactSpace _ _ (by simp) (by simp) (by decide),
    DiagramAut.scalarQuotient_compactSpace _ _ (by simp) (by simp) (by decide),
    GradedDiagramAut.scalarQuotient_compactSpace _ _ (by simp) (by simp) (by decide),
    DiagramAut.scalarQuotient_t2Space _ _ (by simp) (by simp) (by decide),
    GradedDiagramAut.scalarQuotient_totallySeparatedSpace _ _ (by simp) (by simp) (by decide)⟩

end Constructed

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham.ReconstructionTopologyExamples
