/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification.Compatibility
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Comparison
public import OrlikSolomon.HyperplaneGT.Topology.Classification.Graded

/-!
# Pointwise reconstruction of actual cohomology diagrams

The four existing local/domain reconstruction maps become topological group isomorphisms
for the direct actual component topologies and the literal product of discrete units with
pointwise field automorphisms. No cohomology axiom, carrier or topology is changed.

`localQuadraticContinuousReconstruction` and `localGradedContinuousReconstruction`, and
their domain counterparts, retain the exact old maps. The literal degree-one restriction
is a topological embedding before classification, and `localRestrictionContinuousEquiv`
and `domainRestrictionContinuousEquiv` upgrade its existing classified inverse.
Whole-degree, common-target, inclusion and marking formulas keep the old primal scalar
and covariant labels. Forward expansion equations are plain rewrite rules so that bare
inverse cancellation remains available to `simp`.

Blueprint: the pointwise and degree-one restriction clauses of T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h x

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Topology
open scoped DiscreteCoefficientUnits FiniteStageTopology GaloisPointwise

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The parameter topology is discrete units times pointwise field automorphisms.
Blueprint: T15 (`thm:t15`). -/
def localQuadraticContinuousReconstruction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((quadraticAutContinuousEquiv R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((quadraticAutContinuousEquiv R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localQuadraticContinuousReconstruction_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn).toMulEquiv =
      localQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localQuadraticContinuousReconstruction_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localQuadraticContinuousReconstruction T C S hS hgen hn) = localQuadraticReconstruction T C S
      hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localQuadraticContinuousReconstruction_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localQuadraticContinuousReconstruction T C S hS hgen hn p = localQuadraticReconstruction T C S
      hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localQuadraticContinuousReconstruction_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn).symm g =
      (localQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localQuadraticContinuousReconstruction_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (localQuadraticContinuousReconstruction T C S hS hgen hn p) =
      quadraticAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localQuadraticContinuousReconstruction_symm_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.DiagramAut R C S) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn).symm ((degreeOneDiagramEquiv T C
      S).symm g) =
      (quadraticAutEquiv R C S hS hgen hn).symm g := by
  change (quadraticAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localQuadraticContinuousReconstruction_stage_generator [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  localQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem localQuadraticContinuousReconstruction_target [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x :=
  localQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem localQuadraticContinuousReconstruction_marking [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  localQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localQuadraticContinuousReconstruction_inclusion [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn p).stageEquiv A' (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1 ((localQuadraticContinuousReconstruction T C S
        hS hgen hn p).stageEquiv A x) :=
  LinearMap.congr_fun ((localQuadraticContinuousReconstruction T C S hS hgen hn
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localQuadraticContinuousReconstruction_marking_naturality [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn p).stageEquiv A (componentPull T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1 ((localQuadraticContinuousReconstruction T C S hS hgen
        hn p).targetEquiv x) :=
  LinearMap.congr_fun ((localQuadraticContinuousReconstruction T C S hS hgen hn
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The parameter topology is discrete units times pointwise field automorphisms.
Blueprint: T15 (`thm:t15`). -/
def localGradedContinuousReconstruction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := localGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((gradedClassificationContinuousEquiv R C S hS hgen hn).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((gradedClassificationContinuousEquiv R C S hS hgen hn).trans
    (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem localGradedContinuousReconstruction_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedContinuousReconstruction T C S hS hgen hn).toMulEquiv = localGradedReconstruction T
      C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem localGradedContinuousReconstruction_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localGradedContinuousReconstruction T C S hS hgen hn) = localGradedReconstruction T C S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem localGradedContinuousReconstruction_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    localGradedContinuousReconstruction T C S hS hgen hn p = localGradedReconstruction T C S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem localGradedContinuousReconstruction_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (localGradedContinuousReconstruction T C S hS hgen hn).symm g = (localGradedReconstruction T C
      S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem localGradedContinuousReconstruction_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (localGradedContinuousReconstruction T C S hS hgen hn p) =
      gradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem localGradedContinuousReconstruction_symm_comparison [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (localGradedContinuousReconstruction T C S hS hgen hn).symm ((gradedDiagramEquiv T C S).symm g)
      =
      (gradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (gradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem localGradedContinuousReconstruction_stage_generator [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localGradedContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  localGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem localGradedContinuousReconstruction_stage_degree [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (localGradedContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  localGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem localGradedContinuousReconstruction_target_degree [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (localGradedContinuousReconstruction T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  localGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem localGradedContinuousReconstruction_inclusion [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (localGradedContinuousReconstruction T C S hS hgen hn p).stageEquiv A' (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB) ((localGradedContinuousReconstruction T C S hS
        hgen hn p).stageEquiv A x) :=
  AlgHom.congr_fun ((localGradedContinuousReconstruction T C S hS hgen hn p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem localGradedContinuousReconstruction_marking_naturality [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (localGradedContinuousReconstruction T C S hS hgen hn p).stageEquiv A (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((localGradedContinuousReconstruction T C S hS hgen hn
        p).targetEquiv x) :=
  AlgHom.congr_fun ((localGradedContinuousReconstruction T C S hS hgen hn p).marking_naturality A w
    hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The parameter topology is discrete units times pointwise field automorphisms.
Blueprint: T15 (`thm:t15`). -/
def domainQuadraticContinuousReconstruction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (DiagramAut T C S) (DiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainQuadraticReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).trans
    (degreeOneDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainQuadraticContinuousReconstruction_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn).toMulEquiv =
      domainQuadraticReconstruction T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainQuadraticContinuousReconstruction_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainQuadraticContinuousReconstruction T C S hS hgen hn) = domainQuadraticReconstruction T C
      S hS hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainQuadraticContinuousReconstruction_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainQuadraticContinuousReconstruction T C S hS hgen hn p = domainQuadraticReconstruction T C
      S hS hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainQuadraticContinuousReconstruction_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn).symm g =
      (domainQuadraticReconstruction T C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainQuadraticContinuousReconstruction_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (domainQuadraticContinuousReconstruction T C S hS hgen hn p) =
      coefficientDomainAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainQuadraticContinuousReconstruction_symm_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.DiagramAut R C S) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn).symm ((degreeOneDiagramEquiv T C
      S).symm g) =
      (coefficientDomainAutEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainAutEquiv R C S hS hgen hn).symm
    (degreeOneDiagramEquiv T C S ((degreeOneDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainQuadraticContinuousReconstruction_stage_generator [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  domainQuadraticReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The single whole actual degree-one target has the same scalar. -/
theorem domainQuadraticContinuousReconstruction_target [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x
      :=
  domainQuadraticReconstruction_target T C S hS hgen hn a σ x

/-- The actual marked pullback uses the same scalar on its single common target. -/
theorem domainQuadraticContinuousReconstruction_marking [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) :=
  domainQuadraticReconstruction_marking T C S hS hgen hn a σ A w hw x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainQuadraticContinuousReconstruction_inclusion [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : degreeOne T A.val.val) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn p).stageEquiv A' (componentPull T
      (D.complementInclusion hAB) 1 x) =
      componentPull T (D.complementInclusion hAB) 1 ((domainQuadraticContinuousReconstruction T C S
        hS hgen hn p).stageEquiv A x) :=
  LinearMap.congr_fun ((domainQuadraticContinuousReconstruction T C S hS hgen hn
    p).inclusion_naturality hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainQuadraticContinuousReconstruction_marking_naturality [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn p).stageEquiv A (componentPull T
      (w.schemeMap D hw) 1 x) =
      componentPull T (w.schemeMap D hw) 1 ((domainQuadraticContinuousReconstruction T C S hS hgen
        hn p).targetEquiv x) :=
  LinearMap.congr_fun ((domainQuadraticContinuousReconstruction T C S hS hgen hn
    p).marking_naturality A w hw) x

/-- The exact existing actual reconstruction with continuous forward and inverse maps.
The parameter topology is discrete units times pointwise field automorphisms.
Blueprint: T15 (`thm:t15`). -/
def domainGradedContinuousReconstruction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (GradedDiagramAut T C S) (GradedDiagramAut.stageTopology T C S) _ _ where
  toMulEquiv := domainGradedReconstruction T C S hS hgen hn
  continuous_toFun := ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen
    hn).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen
    hn).trans (gradedDiagramContinuousEquiv T C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 reconstruction. -/
theorem domainGradedContinuousReconstruction_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).toMulEquiv = domainGradedReconstruction
      T C S hS hgen hn := rfl

/-- The continuous reconstruction has precisely the original forward function. -/
theorem domainGradedContinuousReconstruction_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainGradedContinuousReconstruction T C S hS hgen hn) = domainGradedReconstruction T C S hS
      hgen hn := rfl

/-- The forward value is the old actual reconstruction, without changing its normalization.
This expansion is deliberately a plain rewrite rule. -/
theorem domainGradedContinuousReconstruction_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedContinuousReconstruction T C S hS hgen hn p = domainGradedReconstruction T C S hS
      hgen hn p := rfl

/-- The continuous inverse is exactly the original scalar-and-Galois extraction. -/
theorem domainGradedContinuousReconstruction_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).symm g = (domainGradedReconstruction T
      C S hS hgen hn).symm g := rfl

/-- The actual reconstruction agrees with the original pure classifier after its adapter.
-/
theorem domainGradedContinuousReconstruction_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (domainGradedContinuousReconstruction T C S hS hgen hn p) =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The inverse actual reconstruction reads the original pure coordinates. -/
theorem domainGradedContinuousReconstruction_symm_comparison [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : HyperplaneGT.GradedDiagramAut R C S) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).symm ((gradedDiagramEquiv T C S).symm
      g) =
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm g := by
  change (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm
    (gradedDiagramEquiv T C S ((gradedDiagramEquiv T C S).symm g)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The actual logarithmic generator has the same primal unit and covariant label. -/
theorem domainGradedContinuousReconstruction_stage_generator [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainGradedContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) :=
  domainGradedReconstruction_stage_generator T C S hS hgen hn a σ A H

/-- The whole actual ordinary degree component has scalar power a^q and covariant transport. -/
theorem domainGradedContinuousReconstruction_stage_degree [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (domainGradedContinuousReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) :=
  domainGradedReconstruction_stage_degree T C S hS hgen hn a σ A q x hx

/-- The whole common-target degree component has the same scalar power, including degree zero. -/
theorem domainGradedContinuousReconstruction_target_degree [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (domainGradedContinuousReconstruction T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) :=
  domainGradedReconstruction_target_degree T C S hS hgen hn a σ q x

/-- The entire actual inclusion square is unchanged by adjoining continuity. -/
theorem domainGradedContinuousReconstruction_inclusion [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) {A A' : C.Stage} (hAB : A ≤ A')
    (x : diagonal T (D.complement A.val.val)) :
    (domainGradedContinuousReconstruction T C S hS hgen hn p).stageEquiv A' (diagonalPull T
      (D.complementInclusion hAB) x) =
      diagonalPull T (D.complementInclusion hAB) ((domainGradedContinuousReconstruction T C S hS
        hgen hn p).stageEquiv A x) :=
  AlgHom.congr_fun ((domainGradedContinuousReconstruction T C S hS hgen hn p).inclusion_naturality
    hAB) x

/-- Every actual marking square retains the same whole common target. -/
theorem domainGradedContinuousReconstruction_marking_naturality [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : diagonal T (schemeMarkingTarget D)) :
    (domainGradedContinuousReconstruction T C S hS hgen hn p).stageEquiv A (diagonalPull T
      (w.schemeMap D hw) x) =
      diagonalPull T (w.schemeMap D hw) ((domainGradedContinuousReconstruction T C S hS hgen hn
        p).targetEquiv x) :=
  AlgHom.congr_fun ((domainGradedContinuousReconstruction T C S hS hgen hn p).marking_naturality A
    w hw) x

namespace GradedDiagramAut

/-- Literal actual degree-one restriction is a topological embedding in every dimension
and over arbitrary commutative coefficients. No classified inverse is assumed. -/
theorem isEmbedding_toQuadratic : IsEmbedding (toQuadratic T C S) :=
  (degreeOneDiagramContinuousEquiv T C S).symm.toHomeomorph.isEmbedding.comp
    ((HyperplaneGT.GradedDiagramAut.isEmbedding_toQuadratic R C S).comp
      (gradedDiagramContinuousEquiv T C S).toHomeomorph.isEmbedding)

/-- The actual degree-one restriction is continuous for the directly defined topologies. -/
theorem continuous_toQuadratic : Continuous (toQuadratic T C S) :=
  (isEmbedding_toQuadratic T C S).continuous

/-- Continuity into the actual full diagram is tested by its literal degree-one restriction.
-/
theorem continuous_iff_toQuadratic_comp {X : Type x} [TopologicalSpace X]
    (f : X → GradedDiagramAut T C S) :
    Continuous f ↔ Continuous (toQuadratic T C S ∘ f) :=
  (isEmbedding_toQuadratic T C S).continuous_iff

/-- Any actual inverse of degree-one restriction is continuous, without assuming one exists.
-/
theorem continuous_inverse_toQuadratic
    (f : DiagramAut T C S → GradedDiagramAut T C S)
    (hf : Function.RightInverse f (toQuadratic T C S)) : Continuous f := by
  apply (continuous_iff_toQuadratic_comp T C S f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

end GradedDiagramAut

/-- The exact old actual degree-one restriction with both continuous directions.
No Krull fixing or algebraicity hypothesis is required. Blueprint: T15 (`thm:t15`). -/
def localRestrictionContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃ₜ* DiagramAut T C S where
  toMulEquiv := localRestrictionEquiv T C S hS hgen hn
  continuous_toFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((gradedAutContinuousEquiv R C S hS hgen hn).trans (degreeOneDiagramContinuousEquiv T C
      S).symm)).continuous_toFun
  continuous_invFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((gradedAutContinuousEquiv R C S hS hgen hn).trans (degreeOneDiagramContinuousEquiv T C
      S).symm)).continuous_invFun

/-- Forgetting continuity gives the exact existing restriction equivalence. -/
theorem localRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localRestrictionContinuousEquiv T C S hS hgen hn).toMulEquiv = localRestrictionEquiv T C S hS
      hgen hn := rfl

/-- The forward restriction function remains exactly the existing one. -/
theorem localRestrictionContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(localRestrictionContinuousEquiv T C S hS hgen hn) = localRestrictionEquiv T C S hS hgen hn :=
      rfl

/-- The continuous restriction applies literal actual degree-one restriction.
This expansion is a plain rewrite rule, preserving inverse cancellation under simp. -/
theorem localRestrictionContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    localRestrictionContinuousEquiv T C S hS hgen hn g = GradedDiagramAut.toQuadratic T C S g :=
  localRestrictionEquiv_apply T C S hS hgen hn g

/-- The continuous inverse is exactly the old classified extension. -/
theorem localRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (localRestrictionContinuousEquiv T C S hS hgen hn).symm g = (localRestrictionEquiv T C S hS
      hgen hn).symm g := rfl

/-- The graded and quadratic classifiers commute with the literal actual restriction. -/
theorem localGradedContinuousReconstruction_toQuadratic [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S
        (localGradedContinuousReconstruction T C S hS hgen hn p) =
      localQuadraticContinuousReconstruction T C S hS hgen hn p :=
  toQuadratic_localGradedReconstruction T C S hS hgen hn p

/-- The bundled classification-restriction square is the original actual square. -/
theorem localGradedContinuousReconstruction_trans_restriction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedContinuousReconstruction T C S hS hgen hn).trans (localRestrictionContinuousEquiv T
      C S hS hgen hn) =
      localQuadraticContinuousReconstruction T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, localRestrictionContinuousEquiv_apply]
  exact localGradedContinuousReconstruction_toQuadratic T C S hS hgen hn p

/-- The exact old actual degree-one restriction with both continuous directions.
No Krull fixing or algebraicity hypothesis is required. Blueprint: T15 (`thm:t15`). -/
def domainRestrictionContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃ₜ* DiagramAut T C S where
  toMulEquiv := domainRestrictionEquiv T C S hS hgen hn
  continuous_toFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C S).symm)).continuous_toFun
  continuous_invFun := ((gradedDiagramContinuousEquiv T C S).trans
    ((coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).trans
      (degreeOneDiagramContinuousEquiv T C S).symm)).continuous_invFun

/-- Forgetting continuity gives the exact existing restriction equivalence. -/
theorem domainRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainRestrictionContinuousEquiv T C S hS hgen hn).toMulEquiv = domainRestrictionEquiv T C S
      hS hgen hn := rfl

/-- The forward restriction function remains exactly the existing one. -/
theorem domainRestrictionContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ⇑(domainRestrictionContinuousEquiv T C S hS hgen hn) = domainRestrictionEquiv T C S hS hgen hn
      := rfl

/-- The continuous restriction applies literal actual degree-one restriction.
This expansion is a plain rewrite rule, preserving inverse cancellation under simp. -/
theorem domainRestrictionContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut T C S) :
    domainRestrictionContinuousEquiv T C S hS hgen hn g = GradedDiagramAut.toQuadratic T C S g :=
  domainRestrictionEquiv_apply T C S hS hgen hn g

/-- The continuous inverse is exactly the old classified extension. -/
theorem domainRestrictionContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut T C S) :
    (domainRestrictionContinuousEquiv T C S hS hgen hn).symm g = (domainRestrictionEquiv T C S hS
      hgen hn).symm g := rfl

/-- The graded and quadratic classifiers commute with the literal actual restriction. -/
theorem domainGradedContinuousReconstruction_toQuadratic [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S
        (domainGradedContinuousReconstruction T C S hS hgen hn p) =
      domainQuadraticContinuousReconstruction T C S hS hgen hn p :=
  toQuadratic_domainGradedReconstruction T C S hS hgen hn p

/-- The bundled classification-restriction square is the original actual square. -/
theorem domainGradedContinuousReconstruction_trans_restriction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).trans (domainRestrictionContinuousEquiv
      T C S hS hgen hn) =
      domainQuadraticContinuousReconstruction T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  rw [ContinuousMulEquiv.trans_apply, domainRestrictionContinuousEquiv_apply]
  exact domainGradedContinuousReconstruction_toQuadratic T C S hS hgen hn p

/-- The topological classifiers agree on the existing local/domain overlap. -/
theorem domainQuadraticContinuousReconstruction_eq_local [IsDomain R] [IsLocalRing R] (hS : (0 :
  k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainQuadraticContinuousReconstruction T C S hS hgen hn =
      localQuadraticContinuousReconstruction T C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainQuadraticReconstruction T C S hS hgen hn p =
    localQuadraticReconstruction T C S hS hgen hn p
  rw [domainQuadraticReconstruction_eq_localQuadraticReconstruction]

/-- The topological classifiers agree on the existing local/domain overlap. -/
theorem domainGradedContinuousReconstruction_eq_local [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈
  S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedContinuousReconstruction T C S hS hgen hn = localGradedContinuousReconstruction T C
      S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainGradedReconstruction T C S hS hgen hn p =
    localGradedReconstruction T C S hS hgen hn p
  rw [domainGradedReconstruction_eq_localGradedReconstruction]

/-- The two continuous restrictions agree on the existing coefficient overlap. -/
theorem domainRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainRestrictionContinuousEquiv T C S hS hgen hn =
      localRestrictionContinuousEquiv T C S hS hgen hn := by
  apply DFunLike.ext
  intro g
  change domainRestrictionEquiv T C S hS hgen hn g =
    localRestrictionEquiv T C S hS hgen hn g
  rw [domainRestrictionEquiv_eq_localRestrictionEquiv]

end OrlikSolomon.HyperplaneGT.Cohomology
