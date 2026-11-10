/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Krull
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient

/-!
# Literal scalar quotients of ordinary de Rham diagrams

Both original ordinary groups use their actual scalar ranges and Mathlib quotient
topologies. The six Galois classifiers upgrade the proved ordinary algebraic wrappers,
retain their canonical direct-action sections and have continuous inverses. Pointwise
results need no field-extension hypothesis; Krull versions add precisely the fixing
condition or algebraicity.

`scalarQuotientRestrictionEquiv` is a new ordinary quotient congruence of the exact old
restriction equivalence, using a proved whole scalar-image equality. Its continuous
upgrade keeps that literal map and is identified with the old actual-theory/twist
composite. No scalar-range-equals-center or unclassified lifting assertion is used.

Blueprint: the scalar quotient clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

namespace DiagramAut

section Pointwise

open scoped GaloisPointwise

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientContinuousEquiv :
    @ContinuousMulEquiv (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen hn)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientContinuousEquiv_toMulEquiv :
    (scalarQuotientContinuousEquiv C S hS hgen hn).toMulEquiv = scalarQuotientEquiv C S hS hgen hn
      := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientContinuousEquiv_coe :
    ⇑(scalarQuotientContinuousEquiv C S hS hgen hn) = scalarQuotientEquiv C S hS hgen hn := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientContinuousEquiv_apply (z : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientContinuousEquiv C S hS hgen hn z = scalarQuotientEquiv C S hS hgen hn z := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientContinuousEquiv_symm_apply (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm σ = scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientContinuousEquiv_map (g : DiagramAut C S) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientMap C S g) =
      ((quadraticContinuousReconstruction C S hS hgen hn).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientMap C S
      (quadraticContinuousReconstruction C S hS hgen hn (a, σ))) = σ := by
  rw [scalarQuotientContinuousEquiv_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientSection C S σ) = σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientContinuousEquiv_section_apply (z : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientContinuousEquiv C S hS hgen hn z) = z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientContinuousEquiv_symm_comparison (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm σ = (scalarQuotientTwistEquiv C S).symm
      ((Cohomology.DiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen hn).symm σ) := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientContinuousEquiv_eq_domain_composite :
    scalarQuotientContinuousEquiv C S hS hgen hn = (scalarQuotientTwistContinuousEquiv C S).trans
      (Cohomology.DiagramAut.domainScalarQuotientContinuousEquiv Tdr C S hS hgen hn) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientContinuousEquiv_left_inv (z : DiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm (scalarQuotientContinuousEquiv C S hS hgen
      hn z) = z := (scalarQuotientContinuousEquiv C S hS hgen hn).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientContinuousEquiv_right_inv (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn ((scalarQuotientContinuousEquiv C S hS hgen
      hn).symm σ) = σ := (scalarQuotientContinuousEquiv C S hS hgen hn).apply_symm_apply σ

end Pointwise

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientKrullContinuousEquiv (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientKrullContinuousEquiv_toMulEquiv (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).toMulEquiv = scalarQuotientEquiv C S hS
      hgen hn := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientKrullContinuousEquiv_coe (hK : KrullFixingCondition k₀ k) :
    ⇑(scalarQuotientKrullContinuousEquiv C S hS hgen hn hK) = scalarQuotientEquiv C S hS hgen hn
      := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientKrullContinuousEquiv_apply (hK : KrullFixingCondition k₀ k) (z : DiagramAut
    C S ⧸ scalarSubgroup C S) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z = scalarQuotientEquiv C S hS hgen hn z
      := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientKrullContinuousEquiv_symm_apply (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ = scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientKrullContinuousEquiv_map (hK : KrullFixingCondition k₀ k) (g : DiagramAut C
    S) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientMap C S g) =
      ((quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientKrullContinuousEquiv_map_reconstruction (hK : KrullFixingCondition k₀ k) (a
    : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientMap C S
      (quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ))) = σ := by
  rw [scalarQuotientKrullContinuousEquiv_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientKrullContinuousEquiv_section (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀]
    k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientSection C S σ) = σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquiv_section_apply (hK : KrullFixingCondition k₀ k) (z :
    DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientKrullContinuousEquiv_symm_comparison (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ = (scalarQuotientTwistEquiv C
      S).symm ((Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn
      hK).symm σ) := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientKrullContinuousEquiv_eq_domain_composite (hK : KrullFixingCondition k₀ k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK = (scalarQuotientTwistContinuousEquiv C
      S).trans
      (Cohomology.DiagramAut.domainScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn hK) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquiv_left_inv (hK : KrullFixingCondition k₀ k) (z :
    DiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm
      (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z :=
      (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientKrullContinuousEquiv_right_inv (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK ((scalarQuotientKrullContinuousEquiv C S
      hS hgen hn hK).symm σ) = σ := (scalarQuotientKrullContinuousEquiv C S hS hgen hn
      hK).apply_symm_apply σ

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientKrullContinuousEquivOfIsAlgebraic [Algebra.IsAlgebraic k₀ k] :
    @ContinuousMulEquiv (DiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [Algebra.IsAlgebraic k₀ k] :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).toMulEquiv =
      scalarQuotientEquiv C S hS hgen hn := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [Algebra.IsAlgebraic k₀ k] :
    ⇑(scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn) = scalarQuotientEquiv C S hS
      hgen hn := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [Algebra.IsAlgebraic k₀ k] (z :
    DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z = scalarQuotientEquiv C S hS
      hgen hn z := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [Algebra.IsAlgebraic k₀ k] (σ :
    k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ =
      scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map [Algebra.IsAlgebraic k₀ k] (g :
    DiagramAut C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientMap C S g) =
      ((quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map_reconstruction [Algebra.IsAlgebraic k₀
    k] (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientMap C S
      (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ))) = σ := by
  rw [scalarQuotientKrullContinuousEquivOfIsAlgebraic_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_section [Algebra.IsAlgebraic k₀ k] (σ : k
    ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientSection C S σ) =
      σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_section_apply [Algebra.IsAlgebraic k₀ k]
    (z : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) =
      z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_comparison [Algebra.IsAlgebraic k₀ k]
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ =
      (scalarQuotientTwistEquiv C S).symm
      ((Cohomology.DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS hgen
      hn).symm σ) := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_domain_composite [Algebra.IsAlgebraic
    k₀ k] :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn =
      (scalarQuotientTwistContinuousEquiv C S).trans
      (Cohomology.DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS hgen
        hn) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_left_inv [Algebra.IsAlgebraic k₀ k] (z :
    DiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) = z :=
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_right_inv [Algebra.IsAlgebraic k₀ k] (σ :
    k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn
      ((scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ) = σ :=
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).apply_symm_apply σ

end DiagramAut

namespace GradedDiagramAut

section Pointwise

open scoped GaloisPointwise

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientContinuousEquiv :
    @ContinuousMulEquiv (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientContinuousEquiv_toMulEquiv :
    (scalarQuotientContinuousEquiv C S hS hgen hn).toMulEquiv = scalarQuotientEquiv C S hS hgen hn
      := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientContinuousEquiv_coe :
    ⇑(scalarQuotientContinuousEquiv C S hS hgen hn) = scalarQuotientEquiv C S hS hgen hn := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientContinuousEquiv_apply (z : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientContinuousEquiv C S hS hgen hn z = scalarQuotientEquiv C S hS hgen hn z := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientContinuousEquiv_symm_apply (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm σ = scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientContinuousEquiv_map (g : GradedDiagramAut C S) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientMap C S g) =
      ((gradedContinuousReconstruction C S hS hgen hn).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientContinuousEquiv_map_reconstruction (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientMap C S
      (gradedContinuousReconstruction C S hS hgen hn (a, σ))) = σ := by
  rw [scalarQuotientContinuousEquiv_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn (scalarQuotientSection C S σ) = σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientContinuousEquiv_section_apply (z : GradedDiagramAut C S ⧸ scalarSubgroup C
    S) :
    scalarQuotientSection C S (scalarQuotientContinuousEquiv C S hS hgen hn z) = z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientContinuousEquiv_symm_comparison (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm σ = (scalarQuotientTwistEquiv C S).symm
      ((Cohomology.GradedDiagramAut.localScalarQuotientContinuousEquiv Tdr C S hS hgen hn).symm σ)
      := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientContinuousEquiv_eq_domain_composite :
    scalarQuotientContinuousEquiv C S hS hgen hn = (scalarQuotientTwistContinuousEquiv C S).trans
      (Cohomology.GradedDiagramAut.domainScalarQuotientContinuousEquiv Tdr C S hS hgen hn) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientContinuousEquiv_left_inv (z : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientContinuousEquiv C S hS hgen hn).symm (scalarQuotientContinuousEquiv C S hS hgen
      hn z) = z := (scalarQuotientContinuousEquiv C S hS hgen hn).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientContinuousEquiv_right_inv (σ : k ≃ₐ[k₀] k) :
    scalarQuotientContinuousEquiv C S hS hgen hn ((scalarQuotientContinuousEquiv C S hS hgen
      hn).symm σ) = σ := (scalarQuotientContinuousEquiv C S hS hgen hn).apply_symm_apply σ

end Pointwise

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientKrullContinuousEquiv (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientKrullContinuousEquiv_toMulEquiv (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).toMulEquiv = scalarQuotientEquiv C S hS
      hgen hn := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientKrullContinuousEquiv_coe (hK : KrullFixingCondition k₀ k) :
    ⇑(scalarQuotientKrullContinuousEquiv C S hS hgen hn hK) = scalarQuotientEquiv C S hS hgen hn
      := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientKrullContinuousEquiv_apply (hK : KrullFixingCondition k₀ k) (z :
    GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z = scalarQuotientEquiv C S hS hgen hn z
      := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientKrullContinuousEquiv_symm_apply (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ = scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientKrullContinuousEquiv_map (hK : KrullFixingCondition k₀ k) (g :
    GradedDiagramAut C S) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientMap C S g) =
      ((gradedKrullContinuousReconstruction C S hS hgen hn hK).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientKrullContinuousEquiv_map_reconstruction (hK : KrullFixingCondition k₀ k) (a
    : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientMap C S
      (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ))) = σ := by
  rw [scalarQuotientKrullContinuousEquiv_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientKrullContinuousEquiv_section (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀]
    k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK (scalarQuotientSection C S σ) = σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquiv_section_apply (hK : KrullFixingCondition k₀ k) (z :
    GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientKrullContinuousEquiv_symm_comparison (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm σ = (scalarQuotientTwistEquiv C
      S).symm ((Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquiv Tdr C S hS
      hgen hn hK).symm σ) := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientKrullContinuousEquiv_eq_domain_composite (hK : KrullFixingCondition k₀ k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK = (scalarQuotientTwistContinuousEquiv C
      S).trans
      (Cohomology.GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv Tdr C S hS hgen hn hK)
        := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquiv_left_inv (hK : KrullFixingCondition k₀ k) (z :
    GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm
      (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK z) = z :=
      (scalarQuotientKrullContinuousEquiv C S hS hgen hn hK).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientKrullContinuousEquiv_right_inv (hK : KrullFixingCondition k₀ k) (σ : k
    ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquiv C S hS hgen hn hK ((scalarQuotientKrullContinuousEquiv C S
      hS hgen hn hK).symm σ) = σ := (scalarQuotientKrullContinuousEquiv C S hS hgen hn
      hK).apply_symm_apply σ

/-- The original ordinary scalar quotient with continuous canonical Galois coordinates.
Only the displayed field hypothesis is used. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientKrullContinuousEquivOfIsAlgebraic [Algebra.IsAlgebraic k₀ k] :
    @ContinuousMulEquiv (GradedDiagramAut C S ⧸ scalarSubgroup C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology C S) _ (scalarSubgroup C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv C S hS hgen hn
  continuous_toFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS
      hgen hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientTwistContinuousEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S hS
      hgen hn)).continuous_invFun

/-- Forgetting continuity retains exactly the proved ordinary algebraic wrapper. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [Algebra.IsAlgebraic k₀ k] :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).toMulEquiv =
      scalarQuotientEquiv C S hS hgen hn := rfl

/-- The original quotient extraction is the complete forward function. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [Algebra.IsAlgebraic k₀ k] :
    ⇑(scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn) = scalarQuotientEquiv C S hS
      hgen hn := rfl

/-- Evaluation is the proved algebraic extraction; this expansion is a plain rewrite. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [Algebra.IsAlgebraic k₀ k] (z :
    GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z = scalarQuotientEquiv C S hS
      hgen hn z := rfl

/-- The inverse is precisely the class of the old ordinary direct Galois action. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [Algebra.IsAlgebraic k₀ k] (σ :
    k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ =
      scalarQuotientSection C S σ :=
  scalarQuotientEquiv_symm_apply C S hS hgen hn σ

/-- A representative gives the Galois coordinate of the exact old ordinary classifier. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map [Algebra.IsAlgebraic k₀ k] (g :
    GradedDiagramAut C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientMap C S g) =
      ((gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g).2 :=
  scalarQuotientEquiv_map C S hS hgen hn g

/-- Classified representatives retain their field-automorphism coordinate. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map_reconstruction [Algebra.IsAlgebraic k₀
    k] (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientMap C S
      (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ))) = σ := by
  rw [scalarQuotientKrullContinuousEquivOfIsAlgebraic_map, ContinuousMulEquiv.symm_apply_apply]

/-- The canonical direct Galois section cancels quotient extraction. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_section [Algebra.IsAlgebraic k₀ k] (σ : k
    ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn (scalarQuotientSection C S σ) =
      σ :=
  scalarQuotientEquiv_section C S hS hgen hn σ

/-- The section recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_section_apply [Algebra.IsAlgebraic k₀ k]
    (z : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) =
      z :=
  scalarQuotientSection_equiv C S hS hgen hn z

/-- Inverse extraction is the exact actual-theory inverse followed by the inverse twist. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_comparison [Algebra.IsAlgebraic k₀ k]
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ =
      (scalarQuotientTwistEquiv C S).symm
      ((Cohomology.GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S
      hS hgen hn).symm σ) := rfl

/-- The actual domain description yields the same ordinary quotient homeomorphism. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_domain_composite [Algebra.IsAlgebraic
    k₀ k] :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn =
      (scalarQuotientTwistContinuousEquiv C S).trans
      (Cohomology.GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic Tdr C S
        hS hgen hn) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientEquiv_eq_domain_composite C S hS hgen hn) z

/-- Extraction followed by its inverse recovers every original quotient class. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_left_inv [Algebra.IsAlgebraic k₀ k] (z :
    GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn z) = z :=
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm_apply_apply z

/-- The canonical quotient section followed by extraction recovers every automorphism. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_right_inv [Algebra.IsAlgebraic k₀ k] (σ :
    k ≃ₐ[k₀] k) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn
      ((scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).symm σ) = σ :=
      (scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn).apply_symm_apply σ

end GradedDiagramAut


end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
