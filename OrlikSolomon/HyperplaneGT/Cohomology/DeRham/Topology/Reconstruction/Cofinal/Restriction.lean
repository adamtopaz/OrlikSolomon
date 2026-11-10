/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Cofinal.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Krull
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Restriction

/-!
# Cofinal equivalences of ordinary de Rham diagrams

The proved ordinary algebraic cofinal wrappers acquire continuous forward and inverse
maps for the direct topologies. The exact stage selection, original whole common target,
canonical inverse and all classified coordinates remain unchanged. Inverse existence
uses only the original marking and dimension hypotheses; no algebraicity is added.

Pointwise and Krull classifier squares retain the topology-specific field condition
only on their classifier. The cofinal equivalences themselves need none. A union of
selected families compares unrelated supplied systems, without arrangement-union closure.
Blueprint: the classified group cofinal clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

/-- The proved ordinary cofinal equivalence with both old maps continuous.
Blueprint: T17 (`cor:t17`). -/
def cofinalRestrictionContinuousEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : DiagramAut C S ≃ₜ* DiagramAut C' S where
  toMulEquiv := cofinalRestrictionEquiv C C' S hC hS hgen hn
  continuous_toFun := ((quadraticTwistContinuousEquiv C S).trans
    ((Cohomology.cofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
      (quadraticTwistContinuousEquiv C' S).symm)).continuous_toFun
  continuous_invFun := ((quadraticTwistContinuousEquiv C S).trans
    ((Cohomology.cofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
      (quadraticTwistContinuousEquiv C' S).symm)).continuous_invFun

/-- The multiplicative field is exactly the previously proved ordinary algebraic wrapper. -/
theorem cofinalRestrictionContinuousEquiv_toMulEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : (cofinalRestrictionContinuousEquiv C C' S hC hS
      hgen hn).toMulEquiv = cofinalRestrictionEquiv C C' S hC hS hgen hn := rfl

/-- The forward function is exactly the ordinary algebraic cofinal map. -/
theorem cofinalRestrictionContinuousEquiv_coe (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : ⇑(cofinalRestrictionContinuousEquiv C C' S hC
      hS hgen hn) = cofinalRestrictionEquiv C C' S hC hS hgen hn := rfl

/-- Evaluation selects the literal ordinary stages and retains the old target. -/
theorem cofinalRestrictionContinuousEquiv_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g = DiagramAut.restrictStages C C' S hC
      g := cofinalRestrictionEquiv_apply C C' S hC hS hgen hn g

/-- The inverse is exactly the proved ordinary cofinal inverse. -/
theorem cofinalRestrictionContinuousEquiv_symm_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g = (cofinalRestrictionEquiv C
      C' S hC hS hgen hn).symm g := rfl

/-- Every selected whole ordinary stage is exactly the old source stage. -/
theorem cofinalRestrictionContinuousEquiv_stageEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) (A : C'.Stage) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g).stageEquiv A = g.stageEquiv
      (CofinalSystem.stageInclusion hC A) :=
  congrArg (fun f : DiagramAut C' S ↦ f.stageEquiv A) (cofinalRestrictionEquiv_apply C C' S hC hS
    hgen hn g)

/-- Cofinal restriction keeps the one entire ordinary common target. -/
theorem cofinalRestrictionContinuousEquiv_targetEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈
    S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv :=
  congrArg (fun f : DiagramAut C' S ↦ f.targetEquiv) (cofinalRestrictionEquiv_apply C C' S hC hS
    hgen hn g)

/-- The old inverse recovers every selected whole ordinary stage. -/
theorem cofinalRestrictionContinuousEquiv_symm_stageEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) (A : C'.Stage) :
    ((cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A :=
  congrArg (fun f : DiagramAut C' S ↦ f.stageEquiv A) (cofinalRestrictionEquiv_right_inv C C' S hC
    hS hgen hn g)

/-- The old inverse keeps the same one whole ordinary common target. -/
theorem cofinalRestrictionContinuousEquiv_symm_targetEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    ((cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g).targetEquiv = g.targetEquiv :=
  cofinalRestrictionEquiv_symm_targetEquiv C C' S hC hS hgen hn g

/-- The exact constructed actual cofinal map lies between the two old ordinary twists. -/
theorem cofinalRestrictionContinuousEquiv_comparison (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn = (quadraticTwistContinuousEquiv C
      S).trans
      ((Cohomology.cofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (quadraticTwistContinuousEquiv C' S).symm) := rfl

/-- The domain actual description gives the identical ordinary cofinal equivalence. -/
theorem cofinalRestrictionContinuousEquiv_eq_domain_composite (hC : C'.stages ⊆ C.stages) (hS : (0
    : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn = (quadraticTwistContinuousEquiv C
      S).trans
      ((Cohomology.domainCofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (quadraticTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro g
  exact DFunLike.congr_fun (cofinalRestrictionEquiv_eq_domain_composite C C' S hC hS hgen hn) g

/-- Extending after restriction recovers the entire original ordinary diagram. -/
theorem cofinalRestrictionContinuousEquiv_left_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm
      (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g) = g :=
      (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm_apply_apply g

/-- Restricting the old inverse recovers the whole subsystem diagram. -/
theorem cofinalRestrictionContinuousEquiv_right_inv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C' S) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn ((cofinalRestrictionContinuousEquiv C
      C' S hC hS hgen hn).symm g) = g := (cofinalRestrictionContinuousEquiv C C' S hC hS hgen
      hn).apply_symm_apply g

/-- Restriction to the same selected family is the identity homeomorphism. -/
theorem cofinalRestrictionContinuousEquiv_refl (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤)
    (hn : 2 ≤ n) :
    cofinalRestrictionContinuousEquiv C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [cofinalRestrictionContinuousEquiv_apply]
  exact DiagramAut.restrictStages_refl C S g

/-- Successive ordinary cofinal restrictions compose as literal stage selection. -/
theorem cofinalRestrictionContinuousEquiv_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv C' C'' S hC' hS hgen hn) =
      cofinalRestrictionContinuousEquiv C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  exact (congrArg (cofinalRestrictionContinuousEquiv C' C'' S hC' hS hgen hn)
    (cofinalRestrictionContinuousEquiv_apply C C' S hC hS hgen hn g)).trans
      ((cofinalRestrictionContinuousEquiv_apply C' C'' S hC' hS hgen hn
        (DiagramAut.restrictStages C C' S hC g)).trans
          ((DiagramAut.restrictStages_trans C C' S C'' hC hC' g).trans
            (cofinalRestrictionContinuousEquiv_apply C C'' S (hC'.trans hC) hS hgen hn g).symm))

section Pointwise

open scoped GaloisPointwise

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem cofinalRestrictionContinuousEquiv_classification (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : kˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn (quadraticContinuousReconstruction C S
      hS hgen hn p) =
      quadraticContinuousReconstruction C' S hS hgen hn p :=
  cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem cofinalRestrictionContinuousEquiv_trans_classification (hC : C'.stages ⊆ C.stages) (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (quadraticContinuousReconstruction C S hS hgen hn).trans (cofinalRestrictionContinuousEquiv C
      C' S hC hS hgen hn) =
      quadraticContinuousReconstruction C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

end Pointwise

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem cofinalRestrictionContinuousEquiv_krull_classification (hC : C'.stages ⊆ C.stages) (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (p : kˣ × (k
      ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn (quadraticKrullContinuousReconstruction
      C S hS hgen hn hK p) =
      quadraticKrullContinuousReconstruction C' S hS hgen hn hK p :=
  cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem cofinalRestrictionContinuousEquiv_krull_trans_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).trans
      (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn) =
      quadraticKrullContinuousReconstruction C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  exact cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem cofinalRestrictionContinuousEquiv_algebraic_classification (hC : C'.stages ⊆ C.stages) (hS
    : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) [Algebra.IsAlgebraic k₀ k] (p : kˣ × (k ≃ₐ[k₀]
      k)) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn
      (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) =
      quadraticKrullContinuousReconstructionOfIsAlgebraic C' S hS hgen hn p :=
  cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem cofinalRestrictionContinuousEquiv_algebraic_trans_classification (hC : C'.stages ⊆
    C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) [Algebra.IsAlgebraic k₀ k] :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn) =
      quadraticKrullContinuousReconstructionOfIsAlgebraic C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact cofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The proved ordinary cofinal equivalence with both old maps continuous.
Blueprint: T17 (`cor:t17`). -/
def gradedCofinalRestrictionContinuousEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : GradedDiagramAut C S ≃ₜ* GradedDiagramAut C' S
      where
  toMulEquiv := gradedCofinalRestrictionEquiv C C' S hC hS hgen hn
  continuous_toFun := ((gradedTwistContinuousEquiv C S).trans
    ((Cohomology.gradedCofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
      (gradedTwistContinuousEquiv C' S).symm)).continuous_toFun
  continuous_invFun := ((gradedTwistContinuousEquiv C S).trans
    ((Cohomology.gradedCofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
      (gradedTwistContinuousEquiv C' S).symm)).continuous_invFun

/-- The multiplicative field is exactly the previously proved ordinary algebraic wrapper. -/
theorem gradedCofinalRestrictionContinuousEquiv_toMulEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : (gradedCofinalRestrictionContinuousEquiv C C' S
      hC hS hgen hn).toMulEquiv = gradedCofinalRestrictionEquiv C C' S hC hS hgen hn := rfl

/-- The forward function is exactly the ordinary algebraic cofinal map. -/
theorem gradedCofinalRestrictionContinuousEquiv_coe (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : ⇑(gradedCofinalRestrictionContinuousEquiv C C'
      S hC hS hgen hn) = gradedCofinalRestrictionEquiv C C' S hC hS hgen hn := rfl

/-- Evaluation selects the literal ordinary stages and retains the old target. -/
theorem gradedCofinalRestrictionContinuousEquiv_apply (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈
    S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g =
      GradedDiagramAut.restrictStages C C' S hC g := gradedCofinalRestrictionEquiv_apply C C' S hC
      hS hgen hn g

/-- The inverse is exactly the proved ordinary cofinal inverse. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_apply (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g =
      (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm g := rfl

/-- Every selected whole ordinary stage is exactly the old source stage. -/
theorem gradedCofinalRestrictionContinuousEquiv_stageEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) (A : C'.Stage) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g).stageEquiv A = g.stageEquiv
      (CofinalSystem.stageInclusion hC A) :=
  congrArg (fun f : GradedDiagramAut C' S ↦ f.stageEquiv A) (gradedCofinalRestrictionEquiv_apply C
    C' S hC hS hgen hn g)

/-- Cofinal restriction keeps the one entire ordinary common target. -/
theorem gradedCofinalRestrictionContinuousEquiv_targetEquiv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g).targetEquiv = g.targetEquiv :=
  congrArg (fun f : GradedDiagramAut C' S ↦ f.targetEquiv) (gradedCofinalRestrictionEquiv_apply C
    C' S hC hS hgen hn g)

/-- The old inverse recovers every selected whole ordinary stage. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_stageEquiv (hC : C'.stages ⊆ C.stages) (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) (A : C'.Stage) :
    ((gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g).stageEquiv
      (CofinalSystem.stageInclusion hC A) = g.stageEquiv A :=
  congrArg (fun f : GradedDiagramAut C' S ↦ f.stageEquiv A)
    (gradedCofinalRestrictionEquiv_right_inv C C' S hC hS hgen hn g)

/-- The old inverse keeps the same one whole ordinary common target. -/
theorem gradedCofinalRestrictionContinuousEquiv_symm_targetEquiv (hC : C'.stages ⊆ C.stages) (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    ((gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g).targetEquiv =
      g.targetEquiv :=
  gradedCofinalRestrictionEquiv_symm_targetEquiv C C' S hC hS hgen hn g

/-- The exact constructed actual cofinal map lies between the two old ordinary twists. -/
theorem gradedCofinalRestrictionContinuousEquiv_comparison (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn = (gradedTwistContinuousEquiv C
      S).trans
      ((Cohomology.gradedCofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (gradedTwistContinuousEquiv C' S).symm) := rfl

/-- The domain actual description gives the identical ordinary cofinal equivalence. -/
theorem gradedCofinalRestrictionContinuousEquiv_eq_domain_composite (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn = (gradedTwistContinuousEquiv C
      S).trans
      ((Cohomology.domainGradedCofinalRestrictionContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (gradedTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro g
  exact DFunLike.congr_fun (gradedCofinalRestrictionEquiv_eq_domain_composite C C' S hC hS hgen
    hn) g

/-- Extending after restriction recovers the entire original ordinary diagram. -/
theorem gradedCofinalRestrictionContinuousEquiv_left_inv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g) = g :=
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm_apply_apply g

/-- Restricting the old inverse recovers the whole subsystem diagram. -/
theorem gradedCofinalRestrictionContinuousEquiv_right_inv (hC : C'.stages ⊆ C.stages) (hS : (0 :
    k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C' S) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn
      ((gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).symm g) = g :=
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).apply_symm_apply g

/-- Restriction to the same selected family is the identity homeomorphism. -/
theorem gradedCofinalRestrictionContinuousEquiv_refl (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure
    S = ⊤) (hn : 2 ≤ n) :
    gradedCofinalRestrictionContinuousEquiv C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro g
  rw [gradedCofinalRestrictionContinuousEquiv_apply]
  exact GradedDiagramAut.restrictStages_refl C S g

/-- Successive ordinary cofinal restrictions compose as literal stage selection. -/
theorem gradedCofinalRestrictionContinuousEquiv_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).trans
      (gradedCofinalRestrictionContinuousEquiv C' C'' S hC' hS hgen hn) =
      gradedCofinalRestrictionContinuousEquiv C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro g
  exact (congrArg (gradedCofinalRestrictionContinuousEquiv C' C'' S hC' hS hgen hn)
    (gradedCofinalRestrictionContinuousEquiv_apply C C' S hC hS hgen hn g)).trans
      ((gradedCofinalRestrictionContinuousEquiv_apply C' C'' S hC' hS hgen hn
        (GradedDiagramAut.restrictStages C C' S hC g)).trans
          ((GradedDiagramAut.restrictStages_trans C C' S C'' hC hC' g).trans
            (gradedCofinalRestrictionContinuousEquiv_apply C C'' S (hC'.trans hC) hS hgen hn
              g).symm))

section Pointwise

open scoped GaloisPointwise

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_classification (hC : C'.stages ⊆ C.stages) (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : kˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn (gradedContinuousReconstruction C
      S hS hgen hn p) =
      gradedContinuousReconstruction C' S hS hgen hn p :=
  gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem gradedCofinalRestrictionContinuousEquiv_trans_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedContinuousReconstruction C S hS hgen hn).trans (gradedCofinalRestrictionContinuousEquiv
      C C' S hC hS hgen hn) =
      gradedContinuousReconstruction C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

end Pointwise

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_krull_classification (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (p : kˣ × (k
      ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn
      (gradedKrullContinuousReconstruction C S hS hgen hn hK p) =
      gradedKrullContinuousReconstruction C' S hS hgen hn hK p :=
  gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem gradedCofinalRestrictionContinuousEquiv_krull_trans_classification (hC : C'.stages ⊆
    C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).trans
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn) =
      gradedKrullContinuousReconstruction C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  exact gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- Ordinary cofinal restriction preserves the exact original classified coordinates. -/
theorem gradedCofinalRestrictionContinuousEquiv_algebraic_classification (hC : C'.stages ⊆
    C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) [Algebra.IsAlgebraic k₀ k] (p : kˣ × (k ≃ₐ[k₀]
      k)) :
    gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn
      (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) =
      gradedKrullContinuousReconstructionOfIsAlgebraic C' S hS hgen hn p :=
  gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- The bundled cofinal classifier square keeps the same primal unit and field automorphism. -/
theorem gradedCofinalRestrictionContinuousEquiv_algebraic_trans_classification (hC : C'.stages ⊆
    C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) [Algebra.IsAlgebraic k₀ k] :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).trans
      (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn) =
      gradedKrullContinuousReconstructionOfIsAlgebraic C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact gradedCofinalRestrictionEquiv_classification C C' S hC hS hgen hn p

/-- Literal ordinary degree-one restriction commutes with cofinal restriction. -/
theorem cofinalRestrictionContinuousEquiv_toQuadratic (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut C S) :
    cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn (GradedDiagramAut.toQuadratic C S g) =
      GradedDiagramAut.toQuadratic C' S
        (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn g) := by
  exact (cofinalRestrictionContinuousEquiv_apply C C' S hC hS hgen hn
    (GradedDiagramAut.toQuadratic C S g)).trans
      ((GradedDiagramAut.toQuadratic_restrictStages C C' S hC g).symm.trans
        (congrArg (GradedDiagramAut.toQuadratic C' S)
          (gradedCofinalRestrictionContinuousEquiv_apply C C' S hC hS hgen hn g).symm))

/-- The bundled ordinary cofinal square is the same literal degree-one square. -/
theorem gradedCofinalRestrictionContinuousEquiv_trans_restriction
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedCofinalRestrictionContinuousEquiv C C' S hC hS hgen hn).trans
      (restrictionContinuousEquiv C' S hS hgen hn) =
        (restrictionContinuousEquiv C S hS hgen hn).trans
          (cofinalRestrictionContinuousEquiv C C' S hC hS hgen hn) := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, restrictionContinuousEquiv_apply]
  exact (cofinalRestrictionContinuousEquiv_toQuadratic C C' S hC hS hgen hn g).symm


/-- Unrelated supplied systems compare through a union of selected families with identical
classified coordinates; no arrangement-union closure is assumed. -/
theorem cofinalRestrictionContinuousEquiv_union_comparison (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((cofinalRestrictionContinuousEquiv (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalRestrictionContinuousEquiv (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (quadraticReconstruction C S hS hgen hn).symm.trans
        (quadraticReconstruction C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  let p := (quadraticReconstruction C S hS hgen hn).symm g
  have hi := (cofinalRestrictionEquiv (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn).symm_apply_eq.mpr
      ((cofinalRestrictionEquiv_classification (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn p).trans
          ((quadraticReconstruction C S hS hgen hn).apply_symm_apply g)).symm
  exact (congrArg (cofinalRestrictionEquiv (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn) hi).trans
      (cofinalRestrictionEquiv_classification (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn p)


/-- Unrelated supplied systems compare through a union of selected families with identical
classified coordinates; no arrangement-union closure is assumed. -/
theorem gradedCofinalRestrictionContinuousEquiv_union_comparison (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((gradedCofinalRestrictionContinuousEquiv (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalRestrictionContinuousEquiv (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (gradedReconstruction C S hS hgen hn).symm.trans
        (gradedReconstruction C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  let p := (gradedReconstruction C S hS hgen hn).symm g
  have hi := (gradedCofinalRestrictionEquiv (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn).symm_apply_eq.mpr
      ((gradedCofinalRestrictionEquiv_classification (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn p).trans
          ((gradedReconstruction C S hS hgen hn).apply_symm_apply g)).symm
  exact (congrArg (gradedCofinalRestrictionEquiv (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn) hi).trans
      (gradedCofinalRestrictionEquiv_classification (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn p)


end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
