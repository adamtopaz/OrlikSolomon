/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification.Compatibility
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient.Local

/-!
# Actual scalar-quotient reconstruction

The literal actual scalar quotients retain Mathlib's quotient topology. Their exact M8
classifiers become topological group isomorphisms to pointwise field automorphisms,
or to the actual global Krull topology under precisely the fixing condition or
algebraicity. Continuity comes from the actual quotient adapter and pure classifier;
no scalar closedness or topology defined through classification is used.

The existing actual scalar-quotient degree-one restriction also has both continuous
directions without a field-extension hypothesis. Plain forward/inverse expansion rules
preserve bare equivalence cancellation.

Blueprint: the scalar-quotient reconstruction clauses of T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h x

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Topology
open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

section Pointwise

open scoped GaloisPointwise

namespace DiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).toMulEquiv = domainScalarQuotientEquiv T
      C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainScalarQuotientContinuousEquiv T C S hS hgen hn) = domainScalarQuotientEquiv T C S hS
      hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn q = domainScalarQuotientEquiv T C S hS
      hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = (domainScalarQuotientEquiv T C
      S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = scalarQuotientSection T C S σ
      :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientContinuousEquiv_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn q =
      HyperplaneGT.DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).toMulEquiv = domainScalarQuotientEquiv T
      C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainScalarQuotientContinuousEquiv T C S hS hgen hn) = domainScalarQuotientEquiv T C S hS
      hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn q = domainScalarQuotientEquiv T C S hS
      hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = (domainScalarQuotientEquiv T C
      S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((domainGradedReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = scalarQuotientSection T C S σ
      :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientContinuousEquiv_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    domainScalarQuotientContinuousEquiv T C S hS hgen hn q =
      HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

end Pointwise

namespace DiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).toMulEquiv =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    ⇑(domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) = domainScalarQuotientEquiv T C
      S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientKrullContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q = domainScalarQuotientEquiv T C
      S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ =
      (domainScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientKrullContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (g : DiagramAut T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK (scalarQuotientMap T C S g) =
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ = scalarQuotientSection T
      C S σ :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientKrullContinuousEquiv_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q =
      HyperplaneGT.DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).toMulEquiv =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    ⇑(domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) = domainScalarQuotientEquiv T C
      S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientKrullContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q = domainScalarQuotientEquiv T C
      S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ =
      (domainScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientKrullContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (g : GradedDiagramAut T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK (scalarQuotientMap T C S g) =
      ((domainGradedReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ = scalarQuotientSection T
      C S σ :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientKrullContinuousEquiv_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q =
      HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

namespace DiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
  (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsDomain R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      domainScalarQuotientEquiv T C S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      (domainScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsDomain R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn (scalarQuotientMap T C S
      g) =
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      HyperplaneGT.DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def domainScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
  (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS
      hgen hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS
      hgen hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsDomain R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      domainScalarQuotientEquiv T C S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      domainScalarQuotientEquiv T C S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      (domainScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsDomain R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn (scalarQuotientMap T C S
      g) =
      ((domainGradedReconstruction T C S hS hgen hn).symm g).2 :=
  domainScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ :=
  domainScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_comparison [IsDomain R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

section Restriction

open scoped GaloisPointwise

/-- The old actual quotient degree-one restriction with both continuous directions.
It needs no Krull condition or algebraicity. Blueprint: T15 (`thm:t15`). -/
def domainScalarQuotientRestrictionContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃ₜ* (DiagramAut T C S ⧸
      DiagramAut.scalarSubgroup T C S) where
  toMulEquiv := domainScalarQuotientRestrictionEquiv T C S hS hgen hn
  continuous_toFun := ((GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen
    hn).trans
    (DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen
    hn).trans
    (DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn).symm).continuous_invFun

/-- The underlying quotient restriction is exactly the existing actual M8 equivalence. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).toMulEquiv =
      domainScalarQuotientRestrictionEquiv T C S hS hgen hn := rfl

/-- The forward function is the original actual quotient restriction. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn) =
      domainScalarQuotientRestrictionEquiv T C S hS hgen hn := rfl

/-- The forward quotient value uses the exact old map, without a new normalization. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸
      GradedDiagramAut.scalarSubgroup T C S) :
    domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn q =
      domainScalarQuotientRestrictionEquiv T C S hS hgen hn q := rfl

/-- The inverse uses the exact old classified quotient extension. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup
      T C S) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm q =
      (domainScalarQuotientRestrictionEquiv T C S hS hgen hn).symm q := rfl

/-- On representatives this is literal actual degree-one restriction, including the target.
-/
theorem domainScalarQuotientRestrictionContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
      DiagramAut.scalarQuotientMap T C S (GradedDiagramAut.toQuadratic T C S g) :=
  domainScalarQuotientRestrictionEquiv_map T C S hS hgen hn g

end Restriction

set_option maxHeartbeats 600000 in
-- Elaborating this representative square compares full inherited actual quotient carriers
-- and diagonal/cohomology equivalences; the larger budget stays local to this proof.
/-- The actual quotient restriction retains the original adapter square.
The proof uses quotient representatives; the two classified definitions need not be rfl. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.scalarQuotientContinuousComparison T C S) =
      (GradedDiagramAut.scalarQuotientContinuousComparison T C S).trans
        (HyperplaneGT.domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn) := by
  apply ContinuousMulEquiv.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.scalarQuotientComparison T C S
    (domainScalarQuotientRestrictionEquiv T C S hS hgen hn (GradedDiagramAut.scalarQuotientMap T C
      S g)) =
      HyperplaneGT.domainScalarQuotientRestrictionEquiv R C S hS hgen hn
        (GradedDiagramAut.scalarQuotientComparison T C S
          (GradedDiagramAut.scalarQuotientMap T C S g))
  rw [domainScalarQuotientRestrictionEquiv_map, DiagramAut.scalarQuotientComparison_map,
    GradedDiagramAut.scalarQuotientComparison_map,
      HyperplaneGT.domainScalarQuotientRestrictionEquiv_map,
    GradedDiagramAut.toQuadratic_comparison]

section PointwiseSquares

open scoped GaloisPointwise

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem domainScalarQuotientRestrictionContinuousEquiv_pointwise [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn) =
      GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn
    (domainScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact domainScalarQuotientEquiv_restriction T C S hS hgen hn q

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem DiagramAut.domainScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn =
      DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    DiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem GradedDiagramAut.domainScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut.domainScalarQuotientContinuousEquiv T C S hS hgen hn =
      GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

end PointwiseSquares

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem domainScalarQuotientRestrictionContinuousEquiv_krull [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn
    (domainScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact domainScalarQuotientEquiv_restriction T C S hS hgen hn q

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem DiagramAut.domainScalarQuotientKrullContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    DiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK =
      DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    DiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv_eq_local [IsDomain R]
  [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  change GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem domainScalarQuotientRestrictionContinuousEquiv_algebraic [IsDomain R] [Algebra.IsAlgebraic
  k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn
    (domainScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact domainScalarQuotientEquiv_restriction T C S hS hgen hn q

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_local [IsDomain R]
  [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn =
      DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    DiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

/-- The actual quotient classifiers agree on the local/domain coefficient overlap. -/
theorem GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_local [IsDomain
  R] [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q =
    GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn q
  rw [GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv]

end OrlikSolomon.HyperplaneGT.Cohomology
