/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.Realizations
public import OrlikSolomon.Examples.HyperplaneGT.TheoryReconstruction
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main
public import OrlikSolomon.Examples.HyperplaneGT.DeRhamReconstruction
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Systems

/-!
# Actual reconstruction topology regressions

Every one of the 36 continuous reconstruction, restriction and scalar-quotient equivalences
retains both bare inverse cancellations. Independent coefficient, geometric, weight and
cohomology universes, whole common targets and actual cofinal maps remain visible. Local
nonfield and nonlocal domain examples are conditional on a supplied eligible theory;
the characteristic-zero de Rham fixture below is an existing constructed realization.

The genuine non-union-closed subsystem is reused, rather than replacing it by a closed
family. Zero-coefficient and dimension-zero tests concern the broader raw maps only.
No local/domain classification is inferred at these boundary parameters.

Blueprint: acceptance consumers for T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology.ReconstructionTopologyExamples

open Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

section Pointwise

open scoped DiscreteCoefficientUnits GaloisPointwise

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn).symm
      (localQuadraticContinuousReconstruction T C S hS hgen hn p) = p ∧
    localQuadraticContinuousReconstruction T C S hS hgen hn
      ((localQuadraticContinuousReconstruction T C S hS hgen hn).symm g) = g := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm
      (DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn z) = z ∧
    DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn
      ((DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ) = σ := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (localGradedContinuousReconstruction T C S hS hgen hn).symm
      (localGradedContinuousReconstruction T C S hS hgen hn p) = p ∧
    localGradedContinuousReconstruction T C S hS hgen hn
      ((localGradedContinuousReconstruction T C S hS hgen hn).symm g) = g := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm
      (GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn z) = z ∧
    GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn
      ((GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ) = σ := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn).symm
      (domainQuadraticContinuousReconstruction T C S hS hgen hn p) = p ∧
    domainQuadraticContinuousReconstruction T C S hS hgen hn
      ((domainQuadraticContinuousReconstruction T C S hS hgen hn).symm g) = g := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm
      (DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn z) = z ∧
    DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn
      ((DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ) = σ := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).symm
      (domainGradedContinuousReconstruction T C S hS hgen hn p) = p ∧
    domainGradedContinuousReconstruction T C S hS hgen hn
      ((domainGradedContinuousReconstruction T C S hS hgen hn).symm g) = g := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm
      (GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn z) = z ∧
    GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn
      ((GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ) = σ := by
        simp

end Pointwise

section Krull

open scoped DiscreteCoefficientUnits

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm
      (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p) = p ∧
    localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
      ((localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm g) = g := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm
      (DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK z) = z ∧
    DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK
      ((DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ) = σ := by
        simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm
      (localGradedKrullContinuousReconstruction T C S hS hgen hn hK p) = p ∧
    localGradedKrullContinuousReconstruction T C S hS hgen hn hK
      ((localGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm g) = g := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm
      (GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK z) = z ∧
    GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK
      ((GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ) = σ :=
        by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm
      (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p) = p ∧
    domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
      ((domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm g) = g := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm
      (DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK z) = z ∧
    DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK
      ((DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ) = σ := by
        simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm
      (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p) = p ∧
    domainGradedKrullContinuousReconstruction T C S hS hgen hn hK
      ((domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm g) = g := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm
      (GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK z) = z ∧
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK
      ((GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ) = σ
        := by simp

end Krull

section Algebraic

open scoped DiscreteCoefficientUnits

example [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) = p ∧
    localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
      ((localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g) = g := by
        simp

example [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm
      (DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn z) = z ∧
    DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn
      ((DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ) =
        σ := by simp

example [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) = p ∧
    localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
      ((localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g) = g := by
        simp

example [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm
      (GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn z) = z
        ∧
    GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn
      ((GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm
        σ) = σ := by simp

example [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut T C S) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) = p ∧
    domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
      ((domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g) = g :=
        by simp

example [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm
      (DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn z) = z ∧
    DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn
      ((DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ) =
        σ := by simp

example [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut T C S) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) = p ∧
    domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
      ((domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g) = g := by
        simp

example [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (z : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (σ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm
      (GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn z) =
        z ∧
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn
      ((GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen
        hn).symm σ) = σ := by simp

end Algebraic

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) (z : DiagramAut T C S) :
    (localRestrictionContinuousEquiv T C S hS hgen hn).symm
      (localRestrictionContinuousEquiv T C S hS hgen hn g) = g ∧
    localRestrictionContinuousEquiv T C S hS hgen hn
      ((localRestrictionContinuousEquiv T C S hS hgen hn).symm z) = z := by simp

example [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (z : DiagramAut T C S ⧸
      DiagramAut.scalarSubgroup T C S) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm
      (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn g) = g ∧
    localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn
      ((localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm z) = z := by simp

example [IsLocalRing R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) (z : DiagramAut T C' S) :
    (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm
      (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      ((cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsLocalRing R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (z : DiagramAut T C' S ⧸
      DiagramAut.scalarSubgroup T C' S) :
    (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      ((cofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsLocalRing R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) (z : GradedDiagramAut T C' S) :
    (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm
      (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      ((gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsLocalRing R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (z : GradedDiagramAut T C'
      S ⧸ GradedDiagramAut.scalarSubgroup T C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      ((gradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) (z : DiagramAut T C S) :
    (domainRestrictionContinuousEquiv T C S hS hgen hn).symm
      (domainRestrictionContinuousEquiv T C S hS hgen hn g) = g ∧
    domainRestrictionContinuousEquiv T C S hS hgen hn
      ((domainRestrictionContinuousEquiv T C S hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (z : DiagramAut T C S ⧸
      DiagramAut.scalarSubgroup T C S) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm
      (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn g) = g ∧
    domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn
      ((domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) (z : DiagramAut T C' S) :
    (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm
      (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      ((domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) (z : DiagramAut T C' S ⧸
      DiagramAut.scalarSubgroup T C' S) :
    (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      ((domainCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) (z : GradedDiagramAut T C' S) :
    (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm
      (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      ((domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by simp

example [IsDomain R] (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) (z : GradedDiagramAut T C'
      S ⧸ GradedDiagramAut.scalarSubgroup T C' S) :
    (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm
      (domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn g) = g ∧
    domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn
      ((domainGradedCofinalScalarQuotientContinuousEquiv T C C' S hC hS hgen hn).symm z) = z := by
        simp

/-- The whole actual ordinary component, not only its generators, retains a^q on the
common target after adding continuity. -/
theorem whole_target_degree [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (localGradedContinuousReconstruction T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  localGradedContinuousReconstruction_target_degree T C S hS hgen hn a σ q x

/-- Every actual marking square commutes on every element of the whole common target. -/
theorem whole_marking_square [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : diagonal T (schemeMarkingTarget D)) :
    (localGradedContinuousReconstruction T C S hS hgen hn p).stageEquiv A
      (diagonalPull T (w.schemeMap D hw) x) =
    diagonalPull T (w.schemeMap D hw)
      ((localGradedContinuousReconstruction T C S hS hgen hn p).targetEquiv x) :=
  localGradedContinuousReconstruction_marking_naturality T C S hS hgen hn p A w hw x

/-- The unrelated-family comparison has exactly the old two reconstruction coordinates;
there is no inclusion or arrangement-union closure premise on either supplied family. -/
theorem unrelated_family_coordinates [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (domainGradedReconstruction T C S hS hgen hn).symm.trans
        (domainGradedReconstruction T C' S hS hgen hn) :=
  domainGradedCofinalRestrictionContinuousEquiv_union_comparison T C C' S hS hgen hn

/-- The complete actual stage-and-target kernel pulls back literally under cofinal
restriction, without localness, dimension or field-extension hypotheses. -/
theorem actual_kernel_preimage (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (GradedDiagramAut.restrictStages T C C' S hC) ⁻¹'
      (GradedDiagramAut.stageKernel T C' S A : Set _) =
      (GradedDiagramAut.stageKernel T C S (CofinalSystem.stageInclusion hC A) : Set _) :=
  GradedDiagramAut.preimage_stageKernel_restrictStages T C C' S hC A

section Nonfield

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

variable {B₄ : Type b} [CommRing B₄] [Algebra (ZMod 4) B₄]
  {ℬ₄ : ℤ → Submodule (ZMod 4) B₄} [GradedAlgebra ℬ₄]
  {D₄ : Geometric.SmoothDomain (ZMod 2)}
  (T₄ : Geometric.OrdinaryTheory.{0, 0, b, h} D₄ ℬ₄)

/-- Conditional on a supplied eligible nonfield-local theory, restriction to the genuine
non-union-closed subsystem preserves the nonzero square-zero target coefficient. -/
theorem non_union_local_nilpotent :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let C' := TheoryReconstructionExamples.nonUnionSystem
    let e := cofinalRestrictionContinuousEquiv T₄ C C' Set.univ
      TheoryReconstructionExamples.nonUnionSystem_subset (by simp) (by simp) (by decide)
    let g := localQuadraticContinuousReconstruction T₄ C Set.univ
      (by simp) (by simp) (by decide) (IncidenceExamples.scalarThreeUnit, 1)
    e.symm (e g) = g ∧
      (targetDegreeOneEquiv T₄).symm
        ((e g).targetEquiv (targetDegreeOneEquiv T₄ (Finsupp.single 0 2))) 0 = 2 ∧
      (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4)^2 = 0 := by
  dsimp only
  refine ⟨by simp, ?_, by decide, by decide⟩
  rw [cofinalRestrictionContinuousEquiv_targetEquiv]
  exact (TheoryReconstructionExamples.mod_four_nilpotent T₄).1

/-- The actual graded family retains the same two parameters through the explicit
non-union-closed subsystem; no closed enlargement replaces that subsystem. -/
theorem non_union_local_coordinates
    (p : (ZMod 4)ˣ × (ZMod 2 ≃ₐ[ZMod 2] ZMod 2)) :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    gradedCofinalRestrictionContinuousEquiv T₄ C TheoryReconstructionExamples.nonUnionSystem
      Set.univ TheoryReconstructionExamples.nonUnionSystem_subset (by simp) (by simp) (by decide)
      (localGradedContinuousReconstruction T₄ C Set.univ (by simp) (by simp) (by decide) p) =
    localGradedContinuousReconstruction T₄ TheoryReconstructionExamples.nonUnionSystem Set.univ
      (by simp) (by simp) (by decide) p :=
  gradedCofinalRestrictionContinuousEquiv_pointwise_apply T₄ _ _ _ _ _ _ _ p

end Nonfield

section Integer

variable {Bℤ : Type b} [CommRing Bℤ]
  {ℬℤ : ℤ → Submodule ℤ Bℤ} [GradedAlgebra ℬℤ] {Dℤ : Geometric.SmoothDomain k}
  (Tℤ : Geometric.OrdinaryTheory.{u, 0, b, h} (R := ℤ) (B := Bℤ) Dℤ ℬℤ)

/-- A supplied integral-coefficient theory uses the genuinely nonlocal domain branch.
The negative unit acts on the actual whole common target. -/
theorem integer_negative_target (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (targetDegreeOneEquiv Tℤ).symm
      ((GradedDiagramAut.toQuadratic Tℤ C S
        (domainGradedContinuousReconstruction Tℤ C S hS hgen hn (-1, 1))).targetEquiv
        (targetDegreeOneEquiv Tℤ (Finsupp.single 0 1))) 0 = -1 := by
  rw [domainGradedContinuousReconstruction_toQuadratic,
    ← degreeOneDiagramEquiv_target Tℤ C S, LinearEquiv.symm_apply_apply,
    domainQuadraticContinuousReconstruction_comparison,
    coefficientDomainAutEquiv_targetEquiv_apply]
  simp

end Integer

/-- The constructed zero theory retains literal restriction and quotient continuity in
zero dimension; neither a nontrivial coefficient nor a local reconstruction is inferred. -/
theorem zero_dimension_raw_continuity :
    let T := TopologyExamples.actualZeroTheory k
    let C := fullCofinalSystem k k 0
    IsEmbedding (DiagramAut.restrictStages T C C {0} (Set.Subset.refl _)) ∧
    IsEmbedding (GradedDiagramAut.restrictStages T C C {0} (Set.Subset.refl _)) ∧
    Continuous (DiagramAut.restrictStagesScalarQuotient T C C {0} (Set.Subset.refl _)) ∧
    Continuous (GradedDiagramAut.restrictStagesScalarQuotient T C C {0} (Set.Subset.refl _)) :=
  ⟨DiagramAut.isEmbedding_restrictStages _ _ _ _ _,
    GradedDiagramAut.isEmbedding_restrictStages _ _ _ _ _,
    DiagramAut.continuous_restrictStagesScalarQuotient _ _ _ _ _,
    GradedDiagramAut.continuous_restrictStagesScalarQuotient _ _ _ _ _⟩

section Constructed

local notation "Tdr" => Geometric.DeRham.ordinaryTheory ℂ
local notation "Cdr" => DeRham.Examples.complexSystem

/-- In the constructed characteristic-zero theory, actual target coordinates detect the
nonidentity primal unit two, even with a nontrivial conjugation parameter. -/
theorem constructed_target_two :
    let e := localQuadraticContinuousReconstruction Tdr Cdr Set.univ
      (by simp) (by simp) (by decide)
    let g := e (DeRham.Examples.complexTwo, Complex.conjAe)
    (targetDegreeOneEquiv Tdr).symm
      (g.targetEquiv (targetDegreeOneEquiv Tdr (Finsupp.single 0 1))) 0 = 2 := by
  dsimp only
  rw [localQuadraticContinuousReconstruction_target, map_smul, LinearEquiv.symm_apply_apply]
  simp [DeRham.Examples.complexTwo, Finsupp.smul_single, smul_eq_mul]

/-- The same constructed family is complex-linear on its actual cohomology target; the
field-automorphism label does not conjugate cohomology coefficients. -/
theorem constructed_target_linear (x : degreeOne Tdr (twoPunctureArrangement ℂ)) :
    let g := localQuadraticContinuousReconstruction Tdr Cdr Set.univ
      (by simp) (by simp) (by decide) (DeRham.Examples.complexTwo, Complex.conjAe)
    g.targetEquiv (Complex.I • x) = Complex.I • g.targetEquiv x :=
  map_smul _ _ _

/-- The actual selected nonreal hyperplane moves covariantly under the new graded
classifier; the previously constructed stage and moved-label witness are reused. -/
theorem constructed_covariant_label :
    let A := DeRham.Examples.imaginaryStage
    let H := DeRham.Examples.imaginaryLabel
    let H' := DeRham.Examples.conjugateLabel
    H' ≠ H ∧
    (localGradedContinuousReconstruction Tdr Cdr Set.univ
      (by simp) (by simp) (by decide) (1, Complex.conjAe)).stageEquiv A
      ((Tdr).diagonalEquiv A.val.val (OSAlgebra.generator ℂ A.val.val H)) =
    (Tdr).diagonalEquiv A.val.val (OSAlgebra.generator ℂ A.val.val H') := by
  refine ⟨DeRham.Examples.conjugateLabel_ne, ?_⟩
  simpa only [Units.val_one, one_smul, DeRham.Examples.conjugateLabel] using
    localGradedContinuousReconstruction_stage_generator Tdr Cdr Set.univ
      (by simp) (by simp) (by decide) (1 : ℂˣ) Complex.conjAe
      DeRham.Examples.imaginaryStage DeRham.Examples.imaginaryLabel

/-- Actual scalar classes in the constructed de Rham theory see nontrivial conjugation
and retain that exact Galois coordinate under every supplied cofinal restriction. -/
theorem constructed_conjugation_quotient (C C' : CofinalSystem ℝ ℂ 2)
    (hC : C'.stages ⊆ C.stages) :
    let e := cofinalScalarQuotientContinuousEquiv Tdr C C' Set.univ hC
      (by simp) (by simp) (by decide)
    let z := DiagramAut.scalarQuotientSection Tdr C Set.univ Complex.conjAe
    e z = DiagramAut.scalarQuotientSection Tdr C' Set.univ Complex.conjAe ∧
      e z ≠ 1 ∧ e.symm (e z) = z := by
  dsimp only
  refine ⟨cofinalScalarQuotientContinuousEquiv_scalarQuotientSection _ _ _ _ _ _ _ _ _,
    ?_, by simp⟩
  intro he
  have hfield := congrArg
    (DiagramAut.localScalarQuotientEquiv Tdr C' Set.univ (by simp) (by simp) (by decide)) he
  rw [cofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    DiagramAut.localScalarQuotientEquiv_section, map_one] at hfield
  exact GaloisCompactExamples.complex_compact_nontrivial.2 hfield

end Constructed

end OrlikSolomon.HyperplaneGT.Cohomology.ReconstructionTopologyExamples
