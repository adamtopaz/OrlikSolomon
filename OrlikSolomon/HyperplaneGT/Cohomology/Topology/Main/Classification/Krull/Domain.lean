/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull.Local

/-!
# Krull reconstruction of actual cohomology diagrams

The existing actual reconstruction maps retain their exact algebraic fields, now with
both continuity proofs for the literal discrete-unit times global Mathlib Krull product.
Each exact-condition wrapper assumes only `KrullFixingCondition`; each algebraic wrapper
assumes only `Algebra.IsAlgebraic`. No normality, separability or closure is required.
The whole-degree, common-target and actual arrow formulas remain those of M8.
Expansion equations are plain rewrite rules, preserving bare inverse cancellation.

Blueprint: the Krull reconstruction clauses of T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h x

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Topology
open scoped DiscreteCoefficientUnits FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def domainQuadraticKrullContinuousReconstruction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainQuadraticKrullContinuousReconstruction_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).toMulEquiv =
      domainQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainQuadraticKrullContinuousReconstruction_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    ⇑(domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK) =
      domainQuadraticReconstruction T C
      S hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainQuadraticKrullContinuousReconstruction_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p =
      domainQuadraticReconstruction T C
      S hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainQuadraticKrullContinuousReconstruction_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut T C S) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm g =
      (domainQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainQuadraticKrullContinuousReconstruction_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
      p) =
      coefficientDomainAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainQuadraticKrullContinuousReconstruction_symm_comparison [IsDomain R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : HyperplaneGT.DiagramAut R C S) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm ((degreeOneDiagramEquiv
      T C
      S).symm g) =
      (coefficientDomainAutEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainQuadraticKrullContinuousReconstruction_stage_generator [IsDomain R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  domainQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem domainQuadraticKrullContinuousReconstruction_target [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).targetEquiv x = (a :
      R) • x
      :=
  domainQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem domainQuadraticKrullContinuousReconstruction_marking [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  domainQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainQuadraticKrullContinuousReconstruction_inclusion [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A'
      (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1 ((domainQuadraticKrullContinuousReconstruction
        T C S
        hS hgen hn hK p).stageEquiv A x) :=
  LinearMap.congr_fun ((domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainQuadraticKrullContinuousReconstruction_marking_naturality [IsDomain R] (hS : (0 : k₀)
  ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A
      (componentPull T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1 ((domainQuadraticKrullContinuousReconstruction T C S hS
        hgen
        hn hK p).targetEquiv x) :=
  LinearMap.congr_fun ((domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def domainGradedKrullContinuousReconstruction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen
    hn hK).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen
    hn hK).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainGradedKrullContinuousReconstruction_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).toMulEquiv =
      domainGradedReconstruction
      T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainGradedKrullContinuousReconstruction_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    ⇑(domainGradedKrullContinuousReconstruction T C S hS hgen hn hK) = domainGradedReconstruction T
      C S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainGradedKrullContinuousReconstruction_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p = domainGradedReconstruction T
      C S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainGradedKrullContinuousReconstruction_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut T C S) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm g =
      (domainGradedReconstruction T
      C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainGradedKrullContinuousReconstruction_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p) =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainGradedKrullContinuousReconstruction_symm_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm ((gradedDiagramEquiv T C
      S).symm
      g) =
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainGradedKrullContinuousReconstruction_stage_generator [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  domainGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem domainGradedKrullContinuousReconstruction_stage_degree [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  domainGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem domainGradedKrullContinuousReconstruction_target_degree [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  domainGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainGradedKrullContinuousReconstruction_inclusion [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A' (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB) ((domainGradedKrullContinuousReconstruction T C S
        hS
        hgen hn hK p).stageEquiv A x) :=
  AlgHom.congr_fun ((domainGradedKrullContinuousReconstruction T C S hS hgen hn hK
    p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainGradedKrullContinuousReconstruction_marking_naturality [IsDomain R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((domainGradedKrullContinuousReconstruction T C S hS hgen
        hn hK
        p).targetEquiv x) :=
  AlgHom.congr_fun ((domainGradedKrullContinuousReconstruction T C S hS hgen hn hK
    p).marking_naturality A
    w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def domainQuadraticKrullContinuousReconstructionOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀
  k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      domainQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_coe [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn) =
      domainQuadraticReconstruction T C
      S hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p =
      domainQuadraticReconstruction T C
      S hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_symm_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g =
      (domainQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS
      hgen hn p) =
      coefficientDomainAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.DiagramAut R C S) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      ((degreeOneDiagramEquiv T C
      S).symm g) =
      (coefficientDomainAutEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_stage_generator [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv
      A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  domainQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_target [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).targetEquiv
      x = (a : R) • x
      :=
  domainQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_marking [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv
      A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  domainQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_inclusion [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A'
      (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1
        ((domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S
        hS hgen hn p).stageEquiv A x) :=
  LinearMap.congr_fun ((domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_marking_naturality [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A
      (componentPull T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1
        ((domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen
        hn p).targetEquiv x) :=
  LinearMap.congr_fun ((domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def domainGradedKrullContinuousReconstructionOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
  (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C
    S hS hgen
    hn).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C
    S hS hgen
    hn).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      domainGradedReconstruction
      T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_coe [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn) =
      domainGradedReconstruction T C S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p =
      domainGradedReconstruction T C S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_symm_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g =
      (domainGradedReconstruction T
      C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen
      hn p) =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      ((gradedDiagramEquiv T C S).symm
      g) =
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_stage_generator [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  domainGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_stage_degree [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  domainGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_target_degree [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  domainGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_inclusion [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A'
      (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB)
        ((domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS
        hgen hn p).stageEquiv A x) :=
  AlgHom.congr_fun ((domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_marking_naturality [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A
      (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((domainGradedKrullContinuousReconstructionOfIsAlgebraic T
        C S hS hgen hn
        p).targetEquiv x) :=
  AlgHom.congr_fun ((domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).marking_naturality A
    w hw) x

/-- The Krull classifiers keep the existing literal degree-one restriction square. -/
theorem domainGradedKrullContinuousReconstruction_toQuadratic [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (domainGradedKrullContinuousReconstruction T C S hS hgen hn
      hK p) =
      domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p :=
  toQuadratic_domainGradedReconstruction T C S hS hgen hn p

/-- The bundled Krull restriction square uses the same original actual maps. -/
theorem domainGradedKrullContinuousReconstruction_trans_restriction [IsDomain R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).trans
        (domainRestrictionContinuousEquiv T C S hS hgen hn) =
      domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, domainRestrictionContinuousEquiv_apply]
  exact domainGradedKrullContinuousReconstruction_toQuadratic T C S hS hgen hn hK p

/-- The Krull upgrades agree on the existing local/domain overlap. -/
theorem domainQuadraticKrullContinuousReconstruction_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK =
      localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change domainQuadraticReconstruction T C S hS hgen hn p =
    localQuadraticReconstruction T C S hS hgen hn p
  rw [domainQuadraticReconstruction_eq_localQuadraticReconstruction]

/-- The Krull upgrades agree on the existing local/domain overlap. -/
theorem domainGradedKrullContinuousReconstruction_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    domainGradedKrullContinuousReconstruction T C S hS hgen hn hK =
      localGradedKrullContinuousReconstruction T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change domainGradedReconstruction T C S hS hgen hn p =
    localGradedReconstruction T C S hS hgen hn p
  rw [domainGradedReconstruction_eq_localGradedReconstruction]

/-- The Krull classifiers keep the existing literal degree-one restriction square. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_toQuadratic [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C
      S hS hgen hn p) =
      domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p :=
  toQuadratic_domainGradedReconstruction T C S hS hgen hn p

/-- The bundled Krull restriction square uses the same original actual maps. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_trans_restriction [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
        (domainRestrictionContinuousEquiv T C S hS hgen hn) =
      domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, domainRestrictionContinuousEquiv_apply]
  exact domainGradedKrullContinuousReconstructionOfIsAlgebraic_toQuadratic T C S hS hgen hn p

/-- The Krull upgrades agree on the existing local/domain overlap. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_eq_local [IsDomain R]
  [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainQuadraticReconstruction T C S hS hgen hn p =
    localQuadraticReconstruction T C S hS hgen hn p
  rw [domainQuadraticReconstruction_eq_localQuadraticReconstruction]

/-- The Krull upgrades agree on the existing local/domain overlap. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_eq_local [IsDomain R] [IsLocalRing
  R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn =
      localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainGradedReconstruction T C S hS hgen hn p =
    localGradedReconstruction T C S hS hgen hn p
  rw [domainGradedReconstruction_eq_localGradedReconstruction]

end OrlikSolomon.HyperplaneGT.Cohomology
