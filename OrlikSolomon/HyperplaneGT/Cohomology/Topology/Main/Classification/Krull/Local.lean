/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Basic

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
def localQuadraticKrullContinuousReconstruction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localQuadraticKrullContinuousReconstruction_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).toMulEquiv =
      localQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localQuadraticKrullContinuousReconstruction_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    ⇑(localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK) =
      localQuadraticReconstruction T C S
      hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localQuadraticKrullContinuousReconstruction_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p =
      localQuadraticReconstruction T C S
      hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localQuadraticKrullContinuousReconstruction_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut T C S) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm g =
      (localQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localQuadraticKrullContinuousReconstruction_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p)
      =
      quadraticAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localQuadraticKrullContinuousReconstruction_symm_comparison [IsLocalRing R] (hS : (0 : k₀)
  ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : HyperplaneGT.DiagramAut R C S) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).symm ((degreeOneDiagramEquiv
      T C
      S).symm g) =
      (quadraticAutEquiv R C S hS hgen hn).symm g := by
  change (quadraticAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localQuadraticKrullContinuousReconstruction_stage_generator [IsLocalRing R] (hS : (0 : k₀)
  ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  localQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem localQuadraticKrullContinuousReconstruction_target [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).targetEquiv x = (a :
      R) • x :=
  localQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem localQuadraticKrullContinuousReconstruction_marking [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  localQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localQuadraticKrullContinuousReconstruction_inclusion [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A'
      (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1 ((localQuadraticKrullContinuousReconstruction T
        C S
        hS hgen hn hK p).stageEquiv A x) :=
  LinearMap.congr_fun ((localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localQuadraticKrullContinuousReconstruction_marking_naturality [IsLocalRing R] (hS : (0 :
  k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A (componentPull
      T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1 ((localQuadraticKrullContinuousReconstruction T C S hS
        hgen
        hn hK p).targetEquiv x) :=
  LinearMap.congr_fun ((localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def localGradedKrullContinuousReconstruction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localGradedKrullContinuousReconstruction_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).toMulEquiv =
      localGradedReconstruction T
      C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localGradedKrullContinuousReconstruction_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) :
    ⇑(localGradedKrullContinuousReconstruction T C S hS hgen hn hK) = localGradedReconstruction T C
      S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localGradedKrullContinuousReconstruction_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localGradedKrullContinuousReconstruction T C S hS hgen hn hK p = localGradedReconstruction T C
      S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localGradedKrullContinuousReconstruction_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut T C S) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm g =
      (localGradedReconstruction T C
      S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localGradedKrullContinuousReconstruction_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (localGradedKrullContinuousReconstruction T C S hS hgen hn hK p) =
      gradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localGradedKrullContinuousReconstruction_symm_comparison [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).symm ((gradedDiagramEquiv T C
      S).symm g)
      =
      (gradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (gradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localGradedKrullContinuousReconstruction_stage_generator [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  localGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem localGradedKrullContinuousReconstruction_stage_degree [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  localGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem localGradedKrullContinuousReconstruction_target_degree [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k) (a : Rˣ) (σ : k
      ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  localGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localGradedKrullContinuousReconstruction_inclusion [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A' (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB) ((localGradedKrullContinuousReconstruction T C S
        hS
        hgen hn hK p).stageEquiv A x) :=
  AlgHom.congr_fun ((localGradedKrullContinuousReconstruction T C S hS hgen hn hK
    p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localGradedKrullContinuousReconstruction_marking_naturality [IsLocalRing R] (hS : (0 : k₀)
  ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK p).stageEquiv A (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((localGradedKrullContinuousReconstruction T C S hS hgen hn
        hK
        p).targetEquiv x) :=
  AlgHom.congr_fun ((localGradedKrullContinuousReconstruction T C S hS hgen hn hK
    p).marking_naturality A w
    hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def localQuadraticKrullContinuousReconstructionOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      localQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_coe [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn) =
      localQuadraticReconstruction T C S
      hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p =
      localQuadraticReconstruction T C S
      hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_symm_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g =
      (localQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS
      hgen hn p) =
      quadraticAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.DiagramAut R C S) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      ((degreeOneDiagramEquiv T C
      S).symm g) =
      (quadraticAutEquiv R C S hS hgen hn).symm g := by
  change (quadraticAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_stage_generator [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  localQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_target [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).targetEquiv
      x = (a : R) • x :=
  localQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_marking [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  localQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_inclusion [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A'
      (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1
        ((localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S
        hS hgen hn p).stageEquiv A x) :=
  LinearMap.congr_fun ((localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_marking_naturality [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A
      (componentPull T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1
        ((localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen
        hn p).targetEquiv x) :=
  LinearMap.congr_fun ((localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The source uses the literal discrete-unit times global Krull product.
Blueprint: T15 (`thm:t15`). -/
def localGradedKrullContinuousReconstructionOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀
  k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      localGradedReconstruction T
      C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_coe [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn) =
      localGradedReconstruction T C S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p =
      localGradedReconstruction T C S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_symm_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm g =
      (localGradedReconstruction T C
      S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen
      hn p) =
      gradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).symm
      ((gradedDiagramEquiv T C S).symm g)
      =
      (gradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (gradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_stage_generator [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  localGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_stage_degree [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  localGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_target_degree [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  localGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_inclusion [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A'
      (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB)
        ((localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS
        hgen hn p).stageEquiv A x) :=
  AlgHom.congr_fun ((localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_marking_naturality [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p).stageEquiv A
      (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((localGradedKrullContinuousReconstructionOfIsAlgebraic T C
        S hS hgen hn
        p).targetEquiv x) :=
  AlgHom.congr_fun ((localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn
    p).marking_naturality A w
    hw) x

/-- The Krull classifiers keep the existing literal degree-one restriction square. -/
theorem localGradedKrullContinuousReconstruction_toQuadratic [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (localGradedKrullContinuousReconstruction T C S hS hgen hn
      hK p) =
      localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p :=
  toQuadratic_localGradedReconstruction T C S hS hgen hn p

/-- The bundled Krull restriction square uses the same original actual maps. -/
theorem localGradedKrullContinuousReconstruction_trans_restriction [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).trans
        (localRestrictionContinuousEquiv T C S hS hgen hn) =
      localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, localRestrictionContinuousEquiv_apply]
  exact localGradedKrullContinuousReconstruction_toQuadratic T C S hS hgen hn hK p

/-- The Krull classifiers keep the existing literal degree-one restriction square. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_toQuadratic [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S
      hS hgen hn p) =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p :=
  toQuadratic_localGradedReconstruction T C S hS hgen hn p

/-- The bundled Krull restriction square uses the same original actual maps. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_trans_restriction [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
        (localRestrictionContinuousEquiv T C S hS hgen hn) =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, localRestrictionContinuousEquiv_apply]
  exact localGradedKrullContinuousReconstructionOfIsAlgebraic_toQuadratic T C S hS hgen hn p

end OrlikSolomon.HyperplaneGT.Cohomology
