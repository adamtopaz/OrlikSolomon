/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Full.Quotient

/-!
# Ordinary full-to-selected cofinal reconstruction

Every supplied stable cofinal family is contained in the old canonical full stable family.
That containment is proved from its definition, not supplied. The four continuous group
and scalar-quotient equivalences specialize the proved ordinary cofinal maps to this
containment. All selected stages, the single entire common target, inverse representatives,
canonical sections and classified coordinates remain literal.

Algebraicity is retained only for the full-family constructor. No union closure, additional
fixing condition or unclassified lifting input is added. Scalar quotients keep the original
ranges and literal Mathlib quotient topologies. Blueprint: T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  [Algebra.IsAlgebraic k₀ k] {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "F" => fullCofinalSystem k₀ k n

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- The exact full-to-supplied ordinary group cofinal map.
The containment is proved and algebraicity retained for the source. Blueprint: T17 (`cor:t17`). -/
def fullCofinalRestrictionContinuousEquiv : DiagramAut F S ≃ₜ* DiagramAut C S :=
  cofinalRestrictionContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- This full-to-selected bundle is the generic map at the proved canonical containment. -/
theorem fullCofinalRestrictionContinuousEquiv_eq_specialization :
    fullCofinalRestrictionContinuousEquiv C S hS hgen hn = cofinalRestrictionContinuousEquiv F C S
    (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn := rfl

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_toMulEquiv : (fullCofinalRestrictionContinuousEquiv
    C S hS hgen hn).toMulEquiv = cofinalRestrictionEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn :=
  cofinalRestrictionContinuousEquiv_toMulEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_coe : ⇑(fullCofinalRestrictionContinuousEquiv C S hS
    hgen hn) = cofinalRestrictionEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  cofinalRestrictionContinuousEquiv_coe F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_apply (g : DiagramAut F S) :
    fullCofinalRestrictionContinuousEquiv C S hS hgen hn g = DiagramAut.restrictStages F C S (fun
      A _ ↦ mem_fullCofinalSystem A) g :=
  cofinalRestrictionContinuousEquiv_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_symm_apply (g : DiagramAut C S) :
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g = (cofinalRestrictionEquiv F C S
    (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn).symm g :=
  cofinalRestrictionContinuousEquiv_symm_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_left_inv (g : DiagramAut F S) :
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn).symm
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn g) = g :=
  cofinalRestrictionContinuousEquiv_left_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_right_inv (g : DiagramAut C S) :
    fullCofinalRestrictionContinuousEquiv C S hS hgen hn ((fullCofinalRestrictionContinuousEquiv C
      S hS hgen hn).symm g) = g :=
  cofinalRestrictionContinuousEquiv_right_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_stageEquiv (g : DiagramAut F S) (A : C.Stage) :
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn g).stageEquiv A = g.stageEquiv
    (CofinalSystem.stageInclusion (fun A _ ↦ mem_fullCofinalSystem A) A) :=
  cofinalRestrictionContinuousEquiv_stageEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g A

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_targetEquiv (g : DiagramAut F S) :
    (fullCofinalRestrictionContinuousEquiv C S hS hgen hn g).targetEquiv = g.targetEquiv :=
  cofinalRestrictionContinuousEquiv_targetEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_symm_stageEquiv (g : DiagramAut C S) (A : C.Stage) :
    ((fullCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g).stageEquiv
    (CofinalSystem.stageInclusion (fun A _ ↦ mem_fullCofinalSystem A) A) = g.stageEquiv A :=
  cofinalRestrictionContinuousEquiv_symm_stageEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g A

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalRestrictionContinuousEquiv_symm_targetEquiv (g : DiagramAut C S) :
    ((fullCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g).targetEquiv = g.targetEquiv :=
  cofinalRestrictionContinuousEquiv_symm_targetEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

section Pointwise

open scoped GaloisPointwise

/-- Full-to-selected ordinary classification keeps both parameters and the original target. -/
theorem fullCofinalRestrictionContinuousEquiv_classification :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullCofinalRestrictionContinuousEquiv C S hS hgen hn) = quadraticContinuousReconstruction C
      S hS hgen hn :=
  cofinalRestrictionContinuousEquiv_trans_classification F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn

end Pointwise

/-- Full-to-selected ordinary classification keeps both parameters and the original target. -/
theorem fullCofinalRestrictionContinuousEquiv_krull_classification :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullCofinalRestrictionContinuousEquiv C S hS hgen hn) =
      quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn :=
  cofinalRestrictionContinuousEquiv_algebraic_trans_classification F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

/-- The exact full-to-supplied ordinary scalar quotient cofinal map.
The containment is proved and algebraicity retained for the source. Blueprint: T17 (`cor:t17`). -/
def fullCofinalScalarQuotientContinuousEquiv : (DiagramAut F S ⧸ DiagramAut.scalarSubgroup F S)
    ≃ₜ* (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :=
  cofinalScalarQuotientContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- This full-to-selected bundle is the generic map at the proved canonical containment. -/
theorem fullCofinalScalarQuotientContinuousEquiv_eq_specialization :
    fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn = cofinalScalarQuotientContinuousEquiv
    F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn := rfl

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_toMulEquiv :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).toMulEquiv =
    cofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  cofinalScalarQuotientContinuousEquiv_toMulEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_coe : ⇑(fullCofinalScalarQuotientContinuousEquiv
    C S hS hgen hn) = cofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn :=
  cofinalScalarQuotientContinuousEquiv_coe F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_apply (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) : fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn z =
    cofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn z :=
  cofinalScalarQuotientContinuousEquiv_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_symm_apply (z : DiagramAut C S ⧸
    DiagramAut.scalarSubgroup C S) : (fullCofinalScalarQuotientContinuousEquiv C S hS hgen
    hn).symm z = (cofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
      hn).symm z :=
  cofinalScalarQuotientContinuousEquiv_symm_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_left_inv (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) : (fullCofinalScalarQuotientContinuousEquiv C S hS hgen
    hn).symm (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) = z :=
  cofinalScalarQuotientContinuousEquiv_left_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_right_inv (z : DiagramAut C S ⧸
    DiagramAut.scalarSubgroup C S) : fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn
    ((fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm z) = z :=
  cofinalScalarQuotientContinuousEquiv_right_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_map (g : DiagramAut F S) :
    fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn (DiagramAut.scalarQuotientMap F S g) =
    DiagramAut.scalarQuotientMap C S (DiagramAut.restrictStages F C S (fun A _ ↦
      mem_fullCofinalSystem A) g) :=
  cofinalScalarQuotientContinuousEquiv_map F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_symm_map (g : DiagramAut C S) :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm (DiagramAut.scalarQuotientMap C
    S g) = DiagramAut.scalarQuotientMap F S ((cofinalRestrictionEquiv F C S (fun A _ ↦
      mem_fullCofinalSystem A) hS hgen hn).symm g)
    :=
  cofinalScalarQuotientContinuousEquiv_symm_map F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn (DiagramAut.scalarQuotientSection F S
    σ) = DiagramAut.scalarQuotientSection C S σ :=
  cofinalScalarQuotientContinuousEquiv_section F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn σ

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_galois (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) : DiagramAut.scalarQuotientEquiv C S hS hgen hn
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) = DiagramAut.scalarQuotientEquiv F
    S hS hgen hn z :=
  cofinalScalarQuotientContinuousEquiv_galois F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_toMonoidHom :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).toMonoidHom =
    DiagramAut.restrictStagesScalarQuotient F C S (fun A _ ↦ mem_fullCofinalSystem A) :=
  cofinalScalarQuotientContinuousEquiv_toMonoidHom F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullCofinalScalarQuotientContinuousEquiv_restrictStages (z : DiagramAut F S ⧸
    DiagramAut.scalarSubgroup F S) : fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn z =
    DiagramAut.restrictStagesScalarQuotient F C S (fun A _ ↦ mem_fullCofinalSystem A) z :=
  cofinalScalarQuotientContinuousEquiv_restrictStages F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn z

section Pointwise

open scoped GaloisPointwise

/-- Full-to-selected scalar quotient classification retains the same field automorphism. -/
theorem fullCofinalScalarQuotientContinuousEquiv_classification :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).trans
      (DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn) =
      DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn :=
  cofinalScalarQuotientContinuousEquiv_classification F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn

end Pointwise

/-- Full-to-selected scalar quotient classification retains the same field automorphism. -/
theorem fullCofinalScalarQuotientContinuousEquiv_krull_classification :
    (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn).trans
      (DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn) =
      DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn :=
  cofinalScalarQuotientContinuousEquiv_algebraic_classification F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

/-- The exact full-to-supplied ordinary group cofinal map.
The containment is proved and algebraicity retained for the source. Blueprint: T17 (`cor:t17`). -/
def fullGradedCofinalRestrictionContinuousEquiv : GradedDiagramAut F S ≃ₜ* GradedDiagramAut C S :=
  gradedCofinalRestrictionContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- This full-to-selected bundle is the generic map at the proved canonical containment. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_eq_specialization :
    fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn =
    gradedCofinalRestrictionContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn
      := rfl

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_toMulEquiv :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).toMulEquiv =
    gradedCofinalRestrictionEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  gradedCofinalRestrictionContinuousEquiv_toMulEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_coe :
    ⇑(fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn) = gradedCofinalRestrictionEquiv
    F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  gradedCofinalRestrictionContinuousEquiv_coe F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_apply (g : GradedDiagramAut F S) :
    fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn g = GradedDiagramAut.restrictStages
    F C S (fun A _ ↦ mem_fullCofinalSystem A) g :=
  gradedCofinalRestrictionContinuousEquiv_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_symm_apply (g : GradedDiagramAut C S) :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g =
    (gradedCofinalRestrictionEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn).symm g :=
  gradedCofinalRestrictionContinuousEquiv_symm_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_left_inv (g : GradedDiagramAut F S) :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn g) = g :=
  gradedCofinalRestrictionContinuousEquiv_left_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_right_inv (g : GradedDiagramAut C S) :
    fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn
    ((fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g) = g :=
  gradedCofinalRestrictionContinuousEquiv_right_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_stageEquiv (g : GradedDiagramAut F S) (A :
    C.Stage) : (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn g).stageEquiv A =
    g.stageEquiv (CofinalSystem.stageInclusion (fun A _ ↦ mem_fullCofinalSystem A) A) :=
  gradedCofinalRestrictionContinuousEquiv_stageEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g A

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_targetEquiv (g : GradedDiagramAut F S) :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn g).targetEquiv = g.targetEquiv :=
  gradedCofinalRestrictionContinuousEquiv_targetEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_symm_stageEquiv (g : GradedDiagramAut C S) (A
    : C.Stage) : ((fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g).stageEquiv
    (CofinalSystem.stageInclusion (fun A _ ↦ mem_fullCofinalSystem A) A) = g.stageEquiv A :=
  gradedCofinalRestrictionContinuousEquiv_symm_stageEquiv F C S (fun A _ ↦ mem_fullCofinalSystem
    A) hS hgen hn g A

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_symm_targetEquiv (g : GradedDiagramAut C S) :
    ((fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).symm g).targetEquiv =
    g.targetEquiv :=
  gradedCofinalRestrictionContinuousEquiv_symm_targetEquiv F C S (fun A _ ↦ mem_fullCofinalSystem
    A) hS hgen hn g

section Pointwise

open scoped GaloisPointwise

/-- Full-to-selected ordinary classification keeps both parameters and the original target. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_classification :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn) =
      gradedContinuousReconstruction C S hS hgen hn :=
  gradedCofinalRestrictionContinuousEquiv_trans_classification F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

end Pointwise

/-- Full-to-selected ordinary classification keeps both parameters and the original target. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_krull_classification :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn) =
      gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn :=
  gradedCofinalRestrictionContinuousEquiv_algebraic_trans_classification F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

/-- The exact full-to-supplied ordinary scalar quotient cofinal map.
The containment is proved and algebraicity retained for the source. Blueprint: T17 (`cor:t17`). -/
def fullGradedCofinalScalarQuotientContinuousEquiv : (GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) ≃ₜ* (GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) :=
  gradedCofinalScalarQuotientContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn

/-- This full-to-selected bundle is the generic map at the proved canonical containment. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_eq_specialization :
    fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn =
    gradedCofinalScalarQuotientContinuousEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
      hn := rfl

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_toMulEquiv :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).toMulEquiv =
    gradedCofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  gradedCofinalScalarQuotientContinuousEquiv_toMulEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_coe :
    ⇑(fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn) =
    gradedCofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn :=
  gradedCofinalScalarQuotientContinuousEquiv_coe F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_apply (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) : fullGradedCofinalScalarQuotientContinuousEquiv C S hS
    hgen hn z = gradedCofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
      hn z :=
  gradedCofinalScalarQuotientContinuousEquiv_apply F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_symm_apply (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) : (fullGradedCofinalScalarQuotientContinuousEquiv C S hS
    hgen hn).symm z = (gradedCofinalScalarQuotientEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A)
      hS hgen hn).symm z :=
  gradedCofinalScalarQuotientContinuousEquiv_symm_apply F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_left_inv (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) : (fullGradedCofinalScalarQuotientContinuousEquiv C S hS
    hgen hn).symm (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) = z :=
  gradedCofinalScalarQuotientContinuousEquiv_left_inv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_right_inv (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) : fullGradedCofinalScalarQuotientContinuousEquiv C S hS
    hgen hn ((fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm z) = z :=
  gradedCofinalScalarQuotientContinuousEquiv_right_inv F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_map (g : GradedDiagramAut F S) :
    fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn
    (GradedDiagramAut.scalarQuotientMap F S g) = GradedDiagramAut.scalarQuotientMap C S
    (GradedDiagramAut.restrictStages F C S (fun A _ ↦ mem_fullCofinalSystem A) g) :=
  gradedCofinalScalarQuotientContinuousEquiv_map F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen
    hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_symm_map (g : GradedDiagramAut C S) :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).symm
    (GradedDiagramAut.scalarQuotientMap C S g) = GradedDiagramAut.scalarQuotientMap F S
    ((gradedCofinalRestrictionEquiv F C S (fun A _ ↦ mem_fullCofinalSystem A) hS hgen hn).symm g) :=
  gradedCofinalScalarQuotientContinuousEquiv_symm_map F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn g

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn
    (GradedDiagramAut.scalarQuotientSection F S σ) = GradedDiagramAut.scalarQuotientSection C S σ :=
  gradedCofinalScalarQuotientContinuousEquiv_section F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn σ

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_galois (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) : GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn z) =
    GradedDiagramAut.scalarQuotientEquiv F S hS hgen hn z :=
  gradedCofinalScalarQuotientContinuousEquiv_galois F C S (fun A _ ↦ mem_fullCofinalSystem A) hS
    hgen hn z

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_toMonoidHom :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).toMonoidHom =
    GradedDiagramAut.restrictStagesScalarQuotient F C S (fun A _ ↦ mem_fullCofinalSystem A) :=
  gradedCofinalScalarQuotientContinuousEquiv_toMonoidHom F C S (fun A _ ↦ mem_fullCofinalSystem A)
    hS hgen hn

/-- Full-to-selected specialization preserves the exact original map and components. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_restrictStages (z : GradedDiagramAut F S ⧸
    GradedDiagramAut.scalarSubgroup F S) : fullGradedCofinalScalarQuotientContinuousEquiv C S hS
    hgen hn z = GradedDiagramAut.restrictStagesScalarQuotient F C S (fun A _ ↦
      mem_fullCofinalSystem A) z :=
  gradedCofinalScalarQuotientContinuousEquiv_restrictStages F C S (fun A _ ↦ mem_fullCofinalSystem
    A) hS hgen hn z

section Pointwise

open scoped GaloisPointwise

/-- Full-to-selected scalar quotient classification retains the same field automorphism. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_classification :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn) =
      GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn :=
  gradedCofinalScalarQuotientContinuousEquiv_classification F C S (fun A _ ↦ mem_fullCofinalSystem
    A) hS hgen hn

end Pointwise

/-- Full-to-selected scalar quotient classification retains the same field automorphism. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_krull_classification :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn) =
      GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn :=
  gradedCofinalScalarQuotientContinuousEquiv_algebraic_classification F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

/-- Full-to-selected restriction commutes with literal ordinary degree-one restriction. -/
theorem fullGradedCofinalRestrictionContinuousEquiv_trans_restriction :
    (fullGradedCofinalRestrictionContinuousEquiv C S hS hgen hn).trans
      (restrictionContinuousEquiv C S hS hgen hn) =
        (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).trans
          (fullCofinalRestrictionContinuousEquiv C S hS hgen hn) :=
  gradedCofinalRestrictionContinuousEquiv_trans_restriction F C S (fun A _ ↦ mem_fullCofinalSystem
    A) hS hgen hn

/-- The two full-to-selected scalar quotient restrictions commute with degree one. -/
theorem fullGradedCofinalScalarQuotientContinuousEquiv_trans_restriction :
    (fullGradedCofinalScalarQuotientContinuousEquiv C S hS hgen hn).trans
      (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn) =
        (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).trans
          (fullCofinalScalarQuotientContinuousEquiv C S hS hgen hn) :=
  gradedCofinalScalarQuotientContinuousEquiv_trans_restriction F C S (fun A _ ↦
    mem_fullCofinalSystem A) hS hgen hn

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
