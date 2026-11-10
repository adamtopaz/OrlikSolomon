/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Comparison
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Basic

/-!
# Pointwise reconstruction of ordinary de Rham diagrams

The constructed characteristic-zero ordinary theory gives the original full ordinary
cohomology and H¹/cup-kernel groups. Their exact M8 reconstruction maps are topological
group isomorphisms for the directly defined finite-stage topologies, from the literal
product of discrete coefficient units and pointwise field automorphisms.

`quadraticContinuousReconstruction`, `gradedContinuousReconstruction` and
`restrictionContinuousEquiv` keep the old multiplicative equivalences and both inverse
maps. The full homogeneous degree, equation-independent dlog, original common target and
actual scheme inclusion/marking equations are unchanged. All actions are coefficient-linear
with covariant geometric labels; no semilinear pullback of forms is asserted.

No supplied theory, algebraicity, Krull comparison or additional topological hypothesis
occurs. Expansions are plain rewrite rules to preserve bare inverse cancellation.

Blueprint: the pointwise and restriction clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v x

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits GaloisPointwise

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "HdRdegree" => Geometric.DeRham.Cohomology.degree

namespace GradedDiagramAut

/-- Literal ordinary degree-one restriction is a topological embedding in every dimension. -/
theorem isEmbedding_toQuadratic : IsEmbedding (toQuadratic C S) :=
  (quadraticTwistContinuousEquiv C S).symm.toHomeomorph.isEmbedding.comp
    ((Cohomology.GradedDiagramAut.isEmbedding_toQuadratic Tdr C S).comp
      (gradedTwistContinuousEquiv C S).toHomeomorph.isEmbedding)

/-- The old ordinary restriction is continuous for the directly defined topologies. -/
theorem continuous_toQuadratic : Continuous (toQuadratic C S) :=
  (isEmbedding_toQuadratic C S).continuous

/-- Continuity into the whole ordinary graded group is tested in degree one. -/
theorem continuous_iff_toQuadratic_comp {X : Type x} [TopologicalSpace X]
    (f : X → GradedDiagramAut C S) :
    Continuous f ↔ Continuous (toQuadratic C S ∘ f) :=
  (isEmbedding_toQuadratic C S).continuous_iff

/-- Any right inverse of the literal ordinary restriction is continuous. -/
theorem continuous_inverse_toQuadratic (f : DiagramAut C S → GradedDiagramAut C S)
    (hf : Function.RightInverse f (toQuadratic C S)) : Continuous f := by
  apply (continuous_iff_toQuadratic_comp C S f).mpr
  rw [hf.comp_eq_id]
  exact continuous_id

end GradedDiagramAut

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- The exact old ordinary quadratic reconstruction with continuity in both directions.
Blueprint: T17 (`cor:t17`). -/
def quadraticContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisPointwiseTopology k k₀ k)
      (DiagramAut C S) (DiagramAut.stageTopology C S) _ _ where
  toMulEquiv := quadraticReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localQuadraticContinuousReconstruction Tdr C S hS hgen hn).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localQuadraticContinuousReconstruction Tdr C S hS hgen hn).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity retains the original ordinary multiplicative equivalence. -/
theorem quadraticContinuousReconstruction_toMulEquiv :
    (quadraticContinuousReconstruction C S hS hgen hn).toMulEquiv = quadraticReconstruction C S hS
      hgen hn := rfl

/-- The continuous classifier has exactly the old forward function. -/
theorem quadraticContinuousReconstruction_coe :
    ⇑(quadraticContinuousReconstruction C S hS hgen hn) = quadraticReconstruction C S hS hgen hn
      := rfl

/-- Evaluation uses the exact old reconstruction; this is a plain rewrite rule. -/
theorem quadraticContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    quadraticContinuousReconstruction C S hS hgen hn p = quadraticReconstruction C S hS hgen hn p
      := rfl

/-- The inverse is exactly the old scalar-and-Galois extraction. -/
theorem quadraticContinuousReconstruction_symm_apply (g : DiagramAut C S) :
    (quadraticContinuousReconstruction C S hS hgen hn).symm g = (quadraticReconstruction C S hS
      hgen hn).symm g := rfl

/-- The old twist identifies reconstruction with the constructed actual-theory map. -/
theorem quadraticContinuousReconstruction_comparison (p : kˣ × (k ≃ₐ[k₀] k)) :
    quadraticTwistEquiv C S (quadraticContinuousReconstruction C S hS hgen hn p) =
      Cohomology.localQuadraticContinuousReconstruction Tdr C S hS hgen hn p :=
  quadraticTwistEquiv_quadraticReconstruction C S hS hgen hn p

/-- The inverse reads the actual-theory coordinates after the old ordinary twist. -/
theorem quadraticContinuousReconstruction_symm_comparison (g : DiagramAut C S) :
    (quadraticContinuousReconstruction C S hS hgen hn).symm g =
      (Cohomology.localQuadraticContinuousReconstruction Tdr C S hS hgen hn).symm
        (quadraticTwistEquiv C S g) := rfl

/-- The same map is the domain classifier followed by the identical inverse twist. -/
theorem quadraticContinuousReconstruction_eq_domain_composite :
    quadraticContinuousReconstruction C S hS hgen hn =
      (Cohomology.domainQuadraticContinuousReconstruction Tdr C S hS hgen hn).trans
        (quadraticTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainQuadraticContinuousReconstruction_eq_local]
  rfl

/-- Reconstruction followed by extraction recovers both original parameters. -/
theorem quadraticContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (quadraticContinuousReconstruction C S hS hgen hn).symm (quadraticContinuousReconstruction C S
      hS hgen hn p) = p :=
  (quadraticContinuousReconstruction C S hS hgen hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original ordinary diagram. -/
theorem quadraticContinuousReconstruction_right_inv (g : DiagramAut C S) :
    quadraticContinuousReconstruction C S hS hgen hn ((quadraticContinuousReconstruction C S hS
      hgen hn).symm g) = g :=
  (quadraticContinuousReconstruction C S hS hgen hn).apply_symm_apply g

/-- The exact old ordinary graded reconstruction with continuity in both directions.
Blueprint: T17 (`cor:t17`). -/
def gradedContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisPointwiseTopology k k₀ k)
      (GradedDiagramAut C S) (GradedDiagramAut.stageTopology C S) _ _ where
  toMulEquiv := gradedReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localGradedContinuousReconstruction Tdr C S hS hgen hn).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localGradedContinuousReconstruction Tdr C S hS hgen hn).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity retains the original ordinary multiplicative equivalence. -/
theorem gradedContinuousReconstruction_toMulEquiv :
    (gradedContinuousReconstruction C S hS hgen hn).toMulEquiv = gradedReconstruction C S hS hgen
      hn := rfl

/-- The continuous classifier has exactly the old forward function. -/
theorem gradedContinuousReconstruction_coe :
    ⇑(gradedContinuousReconstruction C S hS hgen hn) = gradedReconstruction C S hS hgen hn := rfl

/-- Evaluation uses the exact old reconstruction; this is a plain rewrite rule. -/
theorem gradedContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    gradedContinuousReconstruction C S hS hgen hn p = gradedReconstruction C S hS hgen hn p := rfl

/-- The inverse is exactly the old scalar-and-Galois extraction. -/
theorem gradedContinuousReconstruction_symm_apply (g : GradedDiagramAut C S) :
    (gradedContinuousReconstruction C S hS hgen hn).symm g = (gradedReconstruction C S hS hgen
      hn).symm g := rfl

/-- The old twist identifies reconstruction with the constructed actual-theory map. -/
theorem gradedContinuousReconstruction_comparison (p : kˣ × (k ≃ₐ[k₀] k)) :
    gradedTwistEquiv C S (gradedContinuousReconstruction C S hS hgen hn p) =
      Cohomology.localGradedContinuousReconstruction Tdr C S hS hgen hn p :=
  gradedTwistEquiv_gradedReconstruction C S hS hgen hn p

/-- The inverse reads the actual-theory coordinates after the old ordinary twist. -/
theorem gradedContinuousReconstruction_symm_comparison (g : GradedDiagramAut C S) :
    (gradedContinuousReconstruction C S hS hgen hn).symm g =
      (Cohomology.localGradedContinuousReconstruction Tdr C S hS hgen hn).symm (gradedTwistEquiv C
        S g) := rfl

/-- The same map is the domain classifier followed by the identical inverse twist. -/
theorem gradedContinuousReconstruction_eq_domain_composite :
    gradedContinuousReconstruction C S hS hgen hn =
      (Cohomology.domainGradedContinuousReconstruction Tdr C S hS hgen hn).trans
        (gradedTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainGradedContinuousReconstruction_eq_local]
  rfl

/-- Reconstruction followed by extraction recovers both original parameters. -/
theorem gradedContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (gradedContinuousReconstruction C S hS hgen hn).symm (gradedContinuousReconstruction C S hS
      hgen hn p) = p :=
  (gradedContinuousReconstruction C S hS hgen hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original ordinary diagram. -/
theorem gradedContinuousReconstruction_right_inv (g : GradedDiagramAut C S) :
    gradedContinuousReconstruction C S hS hgen hn ((gradedContinuousReconstruction C S hS hgen
      hn).symm g) = g :=
  (gradedContinuousReconstruction C S hS hgen hn).apply_symm_apply g

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem quadraticContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    quadraticContinuousReconstruction C S hS hgen hn (a, σ) =
      scalarQuadraticAction C S a * galoisQuadraticAction C S σ :=
  quadraticReconstruction_apply C S hS hgen hn a σ

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    gradedContinuousReconstruction C S hS hgen hn (a, σ) =
      scalarGradedAction C S a * galoisGradedAction C S σ :=
  gradedReconstruction_apply C S hS hgen hn a σ

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem quadraticContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (quadraticContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  quadraticReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem quadraticContinuousReconstruction_target (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticContinuousReconstruction C S hS hgen hn (a, σ)).targetEquiv x = (a : k) • x :=
  quadraticReconstruction_target C S hS hgen hn a σ x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_stage_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedReconstruction_stage_degree C S hS hgen hn a σ A q x hx

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_target_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).targetEquiv (x : HdR _) =
      (a : k)^q • (x : HdR _) :=
  gradedReconstruction_target_degree C S hS hgen hn a σ q x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) :=
  gradedReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  gradedReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem quadraticContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((quadraticContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  quadraticReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_dlog_fieldAffineForm (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedReconstruction_dlog_fieldAffineForm C S hS hgen hn a σ A H hf

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem quadraticContinuousReconstruction_marking (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) :=
  quadraticReconstruction_marking C S hS hgen hn a σ A w hw x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_marking_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) :=
  gradedReconstruction_marking_degree C S hS hgen hn a σ A w hw q x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_smul (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A (c • x) =
      c • (gradedContinuousReconstruction C S hS hgen hn (a, σ)).stageEquiv A x :=
  gradedReconstruction_smul C S hS hgen hn a σ A c x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_target_smul (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).targetEquiv (c • x) =
      c • (gradedContinuousReconstruction C S hS hgen hn (a, σ)).targetEquiv x :=
  gradedReconstruction_target_smul C S hS hgen hn a σ c x

/-- The continuous classifier retains the exact original ordinary action equation. -/
theorem gradedContinuousReconstruction_target_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedContinuousReconstruction C S hS hgen hn (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) :=
  gradedReconstruction_target_dlog C S hS hgen hn a σ i

/-- The actual ordinary inclusion square holds on every source class. -/
theorem quadraticContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : degreeOne A.val.val) :
    (quadraticContinuousReconstruction C S hS hgen hn p).stageEquiv A' (componentPull
      ((Daff).complementInclusion hAB) 1 x) =
      componentPull ((Daff).complementInclusion hAB) 1 ((quadraticContinuousReconstruction C S hS
        hgen hn p).stageEquiv A x) :=
  DFunLike.congr_fun ((quadraticContinuousReconstruction C S hS hgen hn p).inclusion_naturality
    hAB) x

/-- Every tagged ordinary marking uses the same whole original target. -/
theorem quadraticContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : degreeOne
      (twoPunctureArrangement k)) :
    (quadraticContinuousReconstruction C S hS hgen hn p).stageEquiv A (componentPull (w.schemeMap
      Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((quadraticContinuousReconstruction C S hS hgen hn
        p).targetEquiv x) :=
  DFunLike.congr_fun ((quadraticContinuousReconstruction C S hS hgen hn p).marking_naturality A w
    hw) x

/-- The actual ordinary inclusion square holds on every source class. -/
theorem gradedContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : HdR ((Daff).complement A.val.val)) :
    (gradedContinuousReconstruction C S hS hgen hn p).stageEquiv A'
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB) x) =
      Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB)
        ((gradedContinuousReconstruction C S hS hgen hn p).stageEquiv A x) :=
  DFunLike.congr_fun ((gradedContinuousReconstruction C S hS hgen hn p).inclusion_naturality hAB) x

/-- Every tagged ordinary marking uses the same whole original target. -/
theorem gradedContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : HdR
      (Cohomology.schemeMarkingTarget Daff)) :
    (gradedContinuousReconstruction C S hS hgen hn p).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((gradedContinuousReconstruction C S
        hS hgen hn p).targetEquiv x) :=
  DFunLike.congr_fun ((gradedContinuousReconstruction C S hS hgen hn p).marking_naturality A w hw) x

/-- The exact old ordinary restriction with its original inverse continuous.
No field-extension hypothesis is required. Blueprint: T17 (`cor:t17`). -/
def restrictionContinuousEquiv : GradedDiagramAut C S ≃ₜ* DiagramAut C S where
  toMulEquiv := restrictionEquiv C S hS hgen hn
  continuous_toFun := ((gradedTwistContinuousEquiv C S).trans
    ((Cohomology.localRestrictionContinuousEquiv Tdr C S hS hgen hn).trans
      (quadraticTwistContinuousEquiv C S).symm)).continuous_toFun
  continuous_invFun := ((gradedTwistContinuousEquiv C S).trans
    ((Cohomology.localRestrictionContinuousEquiv Tdr C S hS hgen hn).trans
      (quadraticTwistContinuousEquiv C S).symm)).continuous_invFun

/-- Forgetting continuity gives the exact old ordinary restriction equivalence. -/
theorem restrictionContinuousEquiv_toMulEquiv :
    (restrictionContinuousEquiv C S hS hgen hn).toMulEquiv = restrictionEquiv C S hS hgen hn := rfl

/-- The forward function is exactly the original restriction equivalence. -/
theorem restrictionContinuousEquiv_coe :
    ⇑(restrictionContinuousEquiv C S hS hgen hn) = restrictionEquiv C S hS hgen hn := rfl

/-- Evaluation applies literal ordinary degree-one restriction. -/
theorem restrictionContinuousEquiv_apply (g : GradedDiagramAut C S) :
    restrictionContinuousEquiv C S hS hgen hn g = GradedDiagramAut.toQuadratic C S g :=
  restrictionEquiv_apply C S hS hgen hn g

/-- The inverse is exactly the old ordinary classified extension. -/
theorem restrictionContinuousEquiv_symm_apply (g : DiagramAut C S) :
    (restrictionContinuousEquiv C S hS hgen hn).symm g =
      (restrictionEquiv C S hS hgen hn).symm g := rfl

/-- The restriction square with the old twists is the original actual restriction. -/
theorem restrictionContinuousEquiv_comparison (g : GradedDiagramAut C S) :
    quadraticTwistEquiv C S (restrictionContinuousEquiv C S hS hgen hn g) =
      Cohomology.localRestrictionContinuousEquiv Tdr C S hS hgen hn (gradedTwistEquiv C S g) :=
  (quadraticTwistEquiv C S).apply_symm_apply _

/-- The domain restriction gives the same ordinary topological equivalence. -/
theorem restrictionContinuousEquiv_eq_domain_composite :
    restrictionContinuousEquiv C S hS hgen hn = (gradedTwistContinuousEquiv C S).trans
      ((Cohomology.domainRestrictionContinuousEquiv Tdr C S hS hgen hn).trans
        (quadraticTwistContinuousEquiv C S).symm) := by
  rw [Cohomology.domainRestrictionContinuousEquiv_eq_local]
  rfl

/-- Ordinary restriction followed by its old inverse recovers the whole graded diagram. -/
theorem restrictionContinuousEquiv_left_inv (g : GradedDiagramAut C S) :
    (restrictionContinuousEquiv C S hS hgen hn).symm
      (restrictionContinuousEquiv C S hS hgen hn g) = g :=
  (restrictionContinuousEquiv C S hS hgen hn).symm_apply_apply g

/-- The old inverse followed by ordinary restriction recovers the whole quadratic diagram. -/
theorem restrictionContinuousEquiv_right_inv (g : DiagramAut C S) :
    restrictionContinuousEquiv C S hS hgen hn
      ((restrictionContinuousEquiv C S hS hgen hn).symm g) = g :=
  (restrictionContinuousEquiv C S hS hgen hn).apply_symm_apply g

/-- Both ordinary reconstruction homeomorphisms have identical classified coordinates. -/
theorem gradedContinuousReconstruction_trans_restriction :
    (gradedContinuousReconstruction C S hS hgen hn).trans
      (restrictionContinuousEquiv C S hS hgen hn) = quadraticContinuousReconstruction C S hS hgen
        hn := by
  apply DFunLike.ext
  intro p
  exact restrictionEquiv_gradedReconstruction C S hS hgen hn p

/-- Literal ordinary degree-one restriction preserves both reconstructed parameters. -/
theorem gradedContinuousReconstruction_toQuadratic (p : kˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic C S (gradedContinuousReconstruction C S hS hgen hn p) =
      quadraticContinuousReconstruction C S hS hgen hn p := by
  rw [← restrictionContinuousEquiv_apply C S hS hgen hn]
  exact restrictionEquiv_gradedReconstruction C S hS hgen hn p

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
