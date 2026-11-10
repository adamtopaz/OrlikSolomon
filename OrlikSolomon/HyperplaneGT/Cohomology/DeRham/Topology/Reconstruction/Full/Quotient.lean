/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Full.Groups
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Quotient

/-!
# Ordinary scalar quotients on the canonical full stable family

The four quotient classifiers and quotient degree-one restriction are specializations of
proved ordinary maps with the original scalar ranges and literal Mathlib quotient topologies.
Their exact algebraic fields, canonical direct Galois sections and two inverse laws remain
unchanged. Algebraicity is explicit for the old full-family constructor, even for pointwise
statements; the Krull wrappers use it rather than an additional fixing condition.

No new quotient carrier, topology or classification is introduced. All expansions are
plain rewrite rules. Blueprint: the full-family scalar quotient clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  [Algebra.IsAlgebraic k₀ k] {n : ℕ} (S : Set k₀)

local notation "F" => fullCofinalSystem k₀ k n

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

namespace DiagramAut

section Pointwise

open scoped GaloisPointwise

/-- The exact ordinary full scalar quotient with its proved continuous Galois coordinates.
Algebraicity is retained for the family constructor. Blueprint: T17 (`cor:t17`). -/
def fullScalarQuotientContinuousEquiv :
    @ContinuousMulEquiv (DiagramAut F S ⧸ scalarSubgroup F S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology F S) _ (scalarSubgroup F S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ :=
  scalarQuotientContinuousEquiv F S hS hgen hn

/-- The full-family quotient bundle is exactly the generic specialization. -/
theorem fullScalarQuotientContinuousEquiv_eq_specialization : fullScalarQuotientContinuousEquiv (k
 := k) S
    hS hgen hn = scalarQuotientContinuousEquiv F S hS hgen hn := rfl

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_toMulEquiv :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).toMulEquiv = scalarQuotientEquiv F S
      hS hgen hn
 :=
  scalarQuotientContinuousEquiv_toMulEquiv F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_coe :
    ⇑(fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn) = scalarQuotientEquiv F S hS hgen
      hn :=
  scalarQuotientContinuousEquiv_coe F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_apply (z : DiagramAut F S ⧸ scalarSubgroup F S) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z = scalarQuotientEquiv F S hS hgen hn
      z :=
  scalarQuotientContinuousEquiv_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_symm_apply (σ : k ≃ₐ[k₀] k) :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm σ = scalarQuotientSection F S σ
 :=
  scalarQuotientContinuousEquiv_symm_apply F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_map (g : DiagramAut F S) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S g) =
      ((fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm g).2 :=
  scalarQuotientContinuousEquiv_map F S hS hgen hn g

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S
      (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ))) = σ :=
  scalarQuotientContinuousEquiv_map_reconstruction F S hS hgen hn a σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientSection F S σ) = σ :=
  scalarQuotientContinuousEquiv_section F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_section_apply (z : DiagramAut F S ⧸ scalarSubgroup F S) :
    scalarQuotientSection F S (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z) = z :=
  scalarQuotientContinuousEquiv_section_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_left_inv (z : DiagramAut F S ⧸ scalarSubgroup F S) :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm (scalarQuotientContinuousEquiv
      F S hS hgen
      hn z) = z :=
  scalarQuotientContinuousEquiv_left_inv F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_right_inv (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn ((scalarQuotientContinuousEquiv F S hS
      hgen
      hn).symm σ) = σ :=
  scalarQuotientContinuousEquiv_right_inv F S hS hgen hn σ

end Pointwise

/-- The exact ordinary full scalar quotient with its proved continuous Galois coordinates.
Algebraicity is retained for the family constructor. Blueprint: T17 (`cor:t17`). -/
def fullScalarQuotientKrullContinuousEquiv :
    @ContinuousMulEquiv (DiagramAut F S ⧸ scalarSubgroup F S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology F S) _ (scalarSubgroup F S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic F S hS hgen hn

/-- The full-family quotient bundle is exactly the generic specialization. -/
theorem fullScalarQuotientKrullContinuousEquiv_eq_specialization :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn =
    scalarQuotientKrullContinuousEquivOfIsAlgebraic F S hS hgen hn := rfl

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_toMulEquiv :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).toMulEquiv =
      scalarQuotientEquiv F S hS hgen hn :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_coe :
    ⇑(fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn) = scalarQuotientEquiv F S hS
      hgen hn :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_apply (z :
    DiagramAut F S ⧸ scalarSubgroup F S) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z = scalarQuotientEquiv F S hS
      hgen hn z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_symm_apply (σ :
    k ≃ₐ[k₀] k) :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ =
      scalarQuotientSection F S σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_map (g :
    DiagramAut F S) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S g) =
      ((fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm g).2 :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_map F S hS hgen hn g

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S
      (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ))) = σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_map_reconstruction F S hS hgen hn a σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_section (σ : k
    ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientSection F S σ) =
      σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_section F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_section_apply
    (z : DiagramAut F S ⧸ scalarSubgroup F S) :
    scalarQuotientSection F S (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) =
      z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_section_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_left_inv (z :
    DiagramAut F S ⧸ scalarSubgroup F S) :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm
      (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) = z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_left_inv F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_right_inv (σ :
    k ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn
      ((fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_right_inv F S hS hgen hn σ

end DiagramAut

namespace GradedDiagramAut

section Pointwise

open scoped GaloisPointwise

/-- The exact ordinary full scalar quotient with its proved continuous Galois coordinates.
Algebraicity is retained for the family constructor. Blueprint: T17 (`cor:t17`). -/
def fullScalarQuotientContinuousEquiv :
    @ContinuousMulEquiv (GradedDiagramAut F S ⧸ scalarSubgroup F S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology F S) _ (scalarSubgroup F S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ :=
  scalarQuotientContinuousEquiv F S hS hgen hn

/-- The full-family quotient bundle is exactly the generic specialization. -/
theorem fullScalarQuotientContinuousEquiv_eq_specialization : fullScalarQuotientContinuousEquiv (k
 := k) S
    hS hgen hn = scalarQuotientContinuousEquiv F S hS hgen hn := rfl

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_toMulEquiv :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).toMulEquiv = scalarQuotientEquiv F S
      hS hgen hn
 :=
  scalarQuotientContinuousEquiv_toMulEquiv F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_coe :
    ⇑(fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn) = scalarQuotientEquiv F S hS hgen
      hn :=
  scalarQuotientContinuousEquiv_coe F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_apply (z : GradedDiagramAut F S ⧸ scalarSubgroup F S) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z = scalarQuotientEquiv F S hS hgen hn
      z :=
  scalarQuotientContinuousEquiv_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_symm_apply (σ : k ≃ₐ[k₀] k) :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm σ = scalarQuotientSection F S σ
 :=
  scalarQuotientContinuousEquiv_symm_apply F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_map (g : GradedDiagramAut F S) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S g) =
      ((fullGradedContinuousReconstruction (k := k) S hS hgen hn).symm g).2 :=
  scalarQuotientContinuousEquiv_map F S hS hgen hn g

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S
      (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ))) = σ :=
  scalarQuotientContinuousEquiv_map_reconstruction F S hS hgen hn a σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn (scalarQuotientSection F S σ) = σ :=
  scalarQuotientContinuousEquiv_section F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_section_apply (z : GradedDiagramAut F S ⧸ scalarSubgroup F
    S) :
    scalarQuotientSection F S (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn z) = z :=
  scalarQuotientContinuousEquiv_section_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_left_inv (z : GradedDiagramAut F S ⧸ scalarSubgroup F S) :
    (fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn).symm (scalarQuotientContinuousEquiv
      F S hS hgen
      hn z) = z :=
  scalarQuotientContinuousEquiv_left_inv F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientContinuousEquiv_right_inv (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn ((scalarQuotientContinuousEquiv F S hS
      hgen
      hn).symm σ) = σ :=
  scalarQuotientContinuousEquiv_right_inv F S hS hgen hn σ

end Pointwise

/-- The exact ordinary full scalar quotient with its proved continuous Galois coordinates.
Algebraicity is retained for the family constructor. Blueprint: T17 (`cor:t17`). -/
def fullScalarQuotientKrullContinuousEquiv :
    @ContinuousMulEquiv (GradedDiagramAut F S ⧸ scalarSubgroup F S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology F S) _ (scalarSubgroup F S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic F S hS hgen hn

/-- The full-family quotient bundle is exactly the generic specialization. -/
theorem fullScalarQuotientKrullContinuousEquiv_eq_specialization :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn =
    scalarQuotientKrullContinuousEquivOfIsAlgebraic F S hS hgen hn := rfl

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_toMulEquiv :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).toMulEquiv =
      scalarQuotientEquiv F S hS hgen hn :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_coe :
    ⇑(fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn) = scalarQuotientEquiv F S hS
      hgen hn :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe F S hS hgen hn

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_apply (z :
    GradedDiagramAut F S ⧸ scalarSubgroup F S) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z = scalarQuotientEquiv F S hS
      hgen hn z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_symm_apply (σ :
    k ≃ₐ[k₀] k) :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ =
      scalarQuotientSection F S σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_map (g :
    GradedDiagramAut F S) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S g) =
      ((fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm g).2 :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_map F S hS hgen hn g

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientMap F S
      (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ))) = σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_map_reconstruction F S hS hgen hn a σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_section (σ : k
    ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn (scalarQuotientSection F S σ) =
      σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_section F S hS hgen hn σ

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_section_apply
    (z : GradedDiagramAut F S ⧸ scalarSubgroup F S) :
    scalarQuotientSection F S (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) =
      z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_section_apply F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_left_inv (z :
    GradedDiagramAut F S ⧸ scalarSubgroup F S) :
    (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm
      (fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn z) = z :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_left_inv F S hS hgen hn z

/-- Full-family specialization retains the exact original quotient map and section. -/
theorem fullScalarQuotientKrullContinuousEquiv_right_inv (σ :
    k ≃ₐ[k₀] k) :
    fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn
      ((fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn).symm σ) = σ :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_right_inv F S hS hgen hn σ

end GradedDiagramAut

/-- The literal scalar quotient of full ordinary degree-one restriction.
This specializes the proved new ordinary congruence. Blueprint: T17 (`cor:t17`). -/
def fullScalarQuotientRestrictionContinuousEquiv :
    (GradedDiagramAut F S ⧸ GradedDiagramAut.scalarSubgroup F S) ≃ₜ*
      (DiagramAut F S ⧸ DiagramAut.scalarSubgroup F S) :=
  scalarQuotientRestrictionContinuousEquiv F S hS hgen hn

/-- Full quotient restriction is exactly the generic specialization. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_eq_specialization :
    fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn =
      scalarQuotientRestrictionContinuousEquiv F S hS hgen hn := rfl

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_toMulEquiv :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).toMulEquiv =
      scalarQuotientRestrictionEquiv F S hS hgen hn :=
  scalarQuotientRestrictionContinuousEquiv_toMulEquiv F S hS hgen hn

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_coe :
    ⇑(fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn) =
      scalarQuotientRestrictionEquiv F S hS hgen hn :=
  scalarQuotientRestrictionContinuousEquiv_coe F S hS hgen hn

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_apply
    (z : GradedDiagramAut F S ⧸ GradedDiagramAut.scalarSubgroup F S) :
    fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn z =
      scalarQuotientRestrictionEquiv F S hS hgen hn z :=
  scalarQuotientRestrictionContinuousEquiv_apply F S hS hgen hn z

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_symm_apply
    (z : DiagramAut F S ⧸ DiagramAut.scalarSubgroup F S) :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm z =
      (scalarQuotientRestrictionEquiv F S hS hgen hn).symm z :=
  scalarQuotientRestrictionContinuousEquiv_symm_apply F S hS hgen hn z

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_map (g : GradedDiagramAut F S) :
    fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn
        (GradedDiagramAut.scalarQuotientMap F S g) =
      DiagramAut.scalarQuotientMap F S (GradedDiagramAut.toQuadratic F S g) :=
  scalarQuotientRestrictionContinuousEquiv_map F S hS hgen hn g

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_symm_map (g : DiagramAut F S) :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm
        (DiagramAut.scalarQuotientMap F S g) =
      GradedDiagramAut.scalarQuotientMap F S ((restrictionEquiv F S hS hgen hn).symm g) :=
  scalarQuotientRestrictionContinuousEquiv_symm_map F S hS hgen hn g

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_left_inv
    (z : GradedDiagramAut F S ⧸ GradedDiagramAut.scalarSubgroup F S) :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm
      (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn z) = z :=
  scalarQuotientRestrictionContinuousEquiv_left_inv F S hS hgen hn z

/-- Full quotient restriction retains the exact original representative and inverse. -/
theorem fullScalarQuotientRestrictionContinuousEquiv_right_inv
    (z : DiagramAut F S ⧸ DiagramAut.scalarSubgroup F S) :
    fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn
      ((fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).symm z) = z :=
  scalarQuotientRestrictionContinuousEquiv_right_inv F S hS hgen hn z

section Pointwise

open scoped GaloisPointwise

/-- The full scalar quotient restriction square has the identical Galois coordinate. -/
theorem fullScalarQuotientContinuousEquiv_trans_restriction :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).trans
      (DiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn) =
        GradedDiagramAut.fullScalarQuotientContinuousEquiv (k := k) S hS hgen hn :=
  scalarQuotientContinuousEquiv_trans_restriction F S hS hgen hn

end Pointwise

/-- The full scalar quotient restriction square has the identical Galois coordinate. -/
theorem fullScalarQuotientKrullContinuousEquiv_trans_restriction :
    (fullScalarQuotientRestrictionContinuousEquiv (k := k) S hS hgen hn).trans
      (DiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn) =
        GradedDiagramAut.fullScalarQuotientKrullContinuousEquiv (k := k) S hS hgen hn :=
  scalarQuotientKrullContinuousEquivOfIsAlgebraic_trans_restriction F S hS hgen hn

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
