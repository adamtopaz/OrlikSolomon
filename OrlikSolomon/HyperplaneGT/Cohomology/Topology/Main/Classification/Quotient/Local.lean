/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification.Compatibility
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Quotient

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
def localScalarQuotientContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).toMulEquiv = localScalarQuotientEquiv T C
      S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localScalarQuotientContinuousEquiv T C S hS hgen hn) = localScalarQuotientEquiv T C S hS hgen
      hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn q = localScalarQuotientEquiv T C S hS hgen
      hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = (localScalarQuotientEquiv T C S
      hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((localQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = scalarQuotientSection T C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientContinuousEquiv_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn q =
      HyperplaneGT.DiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def localScalarQuotientContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientContinuousEquiv R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).toMulEquiv = localScalarQuotientEquiv T C
      S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localScalarQuotientContinuousEquiv T C S hS hgen hn) = localScalarQuotientEquiv T C S hS hgen
      hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn q = localScalarQuotientEquiv T C S hS hgen
      hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = (localScalarQuotientEquiv T C S
      hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((localGradedReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientContinuousEquiv T C S hS hgen hn).symm σ = scalarQuotientSection T C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientContinuousEquiv_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    localScalarQuotientContinuousEquiv T C S hS hgen hn q =
      HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

end Pointwise

namespace DiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def localScalarQuotientKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).toMulEquiv =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    ⇑(localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) = localScalarQuotientEquiv T C S
      hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q = localScalarQuotientEquiv T C S
      hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ =
      (localScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientKrullContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (g : DiagramAut T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK (scalarQuotientMap T C S g) =
      ((localQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientKrullContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ = scalarQuotientSection T
      C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientKrullContinuousEquiv_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q =
      HyperplaneGT.DiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def localScalarQuotientKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn
      hK)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).toMulEquiv =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    ⇑(localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) = localScalarQuotientEquiv T C S
      hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q = localScalarQuotientEquiv T C S
      hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ =
      (localScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientKrullContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (g : GradedDiagramAut T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK (scalarQuotientMap T C S g) =
      ((localGradedReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientKrullContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK).symm σ = scalarQuotientSection T
      C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientKrullContinuousEquiv_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK q =
      HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

namespace DiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def localScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
  (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      localScalarQuotientEquiv T C S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      (localScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn (scalarQuotientMap T C S
      g) =
      ((localQuadraticReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      HyperplaneGT.DiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end DiagramAut

namespace GradedDiagramAut

/-- The original actual scalar-quotient classifier with both continuity proofs.
It uses the literal quotient and named field-automorphism topology. Blueprint: T15 (`thm:t15`).
-/
def localScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
  (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut T C S ⧸ scalarSubgroup T C S)
      (@QuotientGroup.instTopologicalSpace _ (stageTopology T C S) _ (scalarSubgroup T C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := localScalarQuotientEquiv T C S hS hgen hn
  continuous_toFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_toFun
  continuous_invFun := ((scalarQuotientContinuousComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn)).continuous_invFun

/-- Forgetting continuity gives the exact original quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).toMulEquiv =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- The forward function is precisely the old quotient classifier. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      localScalarQuotientEquiv T C S hS hgen hn := rfl

/-- A quotient class has its original Galois coordinate; this is a plain rewrite rule. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      localScalarQuotientEquiv T C S hS hgen hn q := rfl

/-- The continuous inverse is exactly the old class-section inverse. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      (localScalarQuotientEquiv T C S hS hgen hn).symm σ := rfl

/-- A representative has the Galois coordinate of the old actual reconstruction. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn (scalarQuotientMap T C S
      g) =
      ((localGradedReconstruction T C S hS hgen hn).symm g).2 :=
  localScalarQuotientEquiv_map T C S hS hgen hn g

/-- The explicit inverse is the class of the same actual Galois family. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ :=
  localScalarQuotientEquiv_symm_apply T C S hS hgen hn σ

/-- The continuous classifier retains the exact actual-to-presentation quotient square. -/
theorem localScalarQuotientKrullContinuousEquivOfIsAlgebraic_comparison [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C
      S) :
    localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn q =
      HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientComparison T C S q) := rfl

end GradedDiagramAut

section Restriction

open scoped GaloisPointwise

/-- The old actual quotient degree-one restriction with both continuous directions.
It needs no Krull condition or algebraicity. Blueprint: T15 (`thm:t15`). -/
def localScalarQuotientRestrictionContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃ₜ* (DiagramAut T C S ⧸
      DiagramAut.scalarSubgroup T C S) where
  toMulEquiv := localScalarQuotientRestrictionEquiv T C S hS hgen hn
  continuous_toFun := ((GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).trans
    (DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen
    hn).trans
    (DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn).symm).continuous_invFun

/-- The underlying quotient restriction is exactly the existing actual M8 equivalence. -/
theorem localScalarQuotientRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).toMulEquiv =
      localScalarQuotientRestrictionEquiv T C S hS hgen hn := rfl

/-- The forward function is the original actual quotient restriction. -/
theorem localScalarQuotientRestrictionContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn) =
      localScalarQuotientRestrictionEquiv T C S hS hgen hn := rfl

/-- The forward quotient value uses the exact old map, without a new normalization. -/
theorem localScalarQuotientRestrictionContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T C S ⧸
      GradedDiagramAut.scalarSubgroup T C S) :
    localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn q =
      localScalarQuotientRestrictionEquiv T C S hS hgen hn q := rfl

/-- The inverse uses the exact old classified quotient extension. -/
theorem localScalarQuotientRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T C S ⧸ DiagramAut.scalarSubgroup
      T C S) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).symm q =
      (localScalarQuotientRestrictionEquiv T C S hS hgen hn).symm q := rfl

/-- On representatives this is literal actual degree-one restriction, including the target.
-/
theorem localScalarQuotientRestrictionContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
      DiagramAut.scalarQuotientMap T C S (GradedDiagramAut.toQuadratic T C S g) :=
  localScalarQuotientRestrictionEquiv_map T C S hS hgen hn g

end Restriction

set_option maxHeartbeats 600000 in
-- Elaborating this representative square compares full inherited actual quotient carriers
-- and diagonal/cohomology equivalences; the larger budget stays local to this proof.
/-- The actual quotient restriction retains the original adapter square.
The proof uses quotient representatives; the two classified definitions need not be rfl. -/
theorem localScalarQuotientRestrictionContinuousEquiv_comparison [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.scalarQuotientContinuousComparison T C S) =
      (GradedDiagramAut.scalarQuotientContinuousComparison T C S).trans
        (HyperplaneGT.scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn) := by
  apply ContinuousMulEquiv.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro g
  change DiagramAut.scalarQuotientComparison T C S
    (localScalarQuotientRestrictionEquiv T C S hS hgen hn (GradedDiagramAut.scalarQuotientMap T C S
      g)) =
      HyperplaneGT.scalarQuotientRestrictionEquiv R C S hS hgen hn
        (GradedDiagramAut.scalarQuotientComparison T C S
          (GradedDiagramAut.scalarQuotientMap T C S g))
  rw [localScalarQuotientRestrictionEquiv_map, DiagramAut.scalarQuotientComparison_map,
    GradedDiagramAut.scalarQuotientComparison_map, HyperplaneGT.scalarQuotientRestrictionEquiv_map,
    GradedDiagramAut.toQuadratic_comparison]

section PointwiseSquares

open scoped GaloisPointwise

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem localScalarQuotientRestrictionContinuousEquiv_pointwise [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn) =
      GradedDiagramAut.localScalarQuotientContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.localScalarQuotientEquiv T C S hS hgen hn
    (localScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact localScalarQuotientEquiv_restriction T C S hS hgen hn q

end PointwiseSquares

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem localScalarQuotientRestrictionContinuousEquiv_krull [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK) =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquiv T C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  change DiagramAut.localScalarQuotientEquiv T C S hS hgen hn
    (localScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact localScalarQuotientEquiv_restriction T C S hS hgen hn q

/-- Both actual quotient classifiers retain the same Galois coordinate under restriction.
-/
theorem localScalarQuotientRestrictionContinuousEquiv_algebraic [IsLocalRing R]
  [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localScalarQuotientRestrictionContinuousEquiv T C S hS hgen hn).trans
        (DiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn) =
      GradedDiagramAut.localScalarQuotientKrullContinuousEquivOfIsAlgebraic T C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  change DiagramAut.localScalarQuotientEquiv T C S hS hgen hn
    (localScalarQuotientRestrictionEquiv T C S hS hgen hn q) = _
  exact localScalarQuotientEquiv_restriction T C S hS hgen hn q

end OrlikSolomon.HyperplaneGT.Cohomology
