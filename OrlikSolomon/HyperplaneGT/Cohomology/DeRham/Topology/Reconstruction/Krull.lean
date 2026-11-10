/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull

/-!
# Krull reconstruction of ordinary de Rham diagrams

The exact original ordinary reconstruction maps have continuous forward and inverse maps
for Mathlib's Krull topology under the explicit fixing condition, or under algebraicity.
The coefficient-unit factor remains discrete, and the original diagram topology is direct.

The four wrappers preserve every old multiplicative field, whole-degree and dlog formula,
original common target and actual scheme arrow. They add no normality or separability.
Ordinary degree-one restriction itself retains no field-extension hypothesis. All expansion
equations are plain rewrites, preserving both bare inverse cancellations.

Blueprint: the Krull clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "HdRdegree" => Geometric.DeRham.Cohomology.degree

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- The exact ordinary quadratic reconstruction for the Krull topology.
The field hypothesis is precisely the displayed condition. Blueprint: T17 (`cor:t17`). -/
def quadraticKrullContinuousReconstruction (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (DiagramAut C S) (DiagramAut.stageTopology C S) _ _ where
  toMulEquiv := quadraticReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localQuadraticKrullContinuousReconstruction Tdr C S hS hgen hn
    hK).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localQuadraticKrullContinuousReconstruction Tdr C S hS hgen hn
    hK).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original ordinary classifier. -/
theorem quadraticKrullContinuousReconstruction_toMulEquiv (hK : KrullFixingCondition k₀ k) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).toMulEquiv =
      quadraticReconstruction C S hS hgen hn := rfl

/-- The forward function is the original ordinary classifier. -/
theorem quadraticKrullContinuousReconstruction_coe (hK : KrullFixingCondition k₀ k) :
    ⇑(quadraticKrullContinuousReconstruction C S hS hgen hn hK) = quadraticReconstruction C S hS
      hgen hn := rfl

/-- Evaluation keeps the old map; this expansion is a plain rewrite rule. -/
theorem quadraticKrullContinuousReconstruction_apply (hK : KrullFixingCondition k₀ k) (p : kˣ × (k
    ≃ₐ[k₀] k)) :
    quadraticKrullContinuousReconstruction C S hS hgen hn hK p = quadraticReconstruction C S hS
      hgen hn p := rfl

/-- The inverse is exactly the original extraction of both coordinates. -/
theorem quadraticKrullContinuousReconstruction_symm_apply (hK : KrullFixingCondition k₀ k) (g :
    DiagramAut C S) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm g = (quadraticReconstruction C
      S hS hgen hn).symm g := rfl

/-- The old twist identifies this map with the constructed actual Krull classifier. -/
theorem quadraticKrullContinuousReconstruction_comparison (hK : KrullFixingCondition k₀ k) (p : kˣ
    × (k ≃ₐ[k₀] k)) :
    quadraticTwistEquiv C S (quadraticKrullContinuousReconstruction C S hS hgen hn hK p) =
      Cohomology.localQuadraticKrullContinuousReconstruction Tdr C S hS hgen hn hK p :=
  quadraticTwistEquiv_quadraticReconstruction C S hS hgen hn p

/-- The inverse reads the constructed actual coordinates after ordinary twisting. -/
theorem quadraticKrullContinuousReconstruction_symm_comparison (hK : KrullFixingCondition k₀ k) (g
    : DiagramAut C S) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm g =
      (Cohomology.localQuadraticKrullContinuousReconstruction Tdr C S hS hgen hn hK).symm
      (quadraticTwistEquiv C S g) := rfl

/-- The domain classifier gives the identical ordinary topological equivalence. -/
theorem quadraticKrullContinuousReconstruction_eq_domain_composite (hK : KrullFixingCondition k₀
    k) :
    quadraticKrullContinuousReconstruction C S hS hgen hn hK =
      (Cohomology.domainQuadraticKrullContinuousReconstruction Tdr C S hS hgen hn hK).trans
      (quadraticTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainQuadraticKrullContinuousReconstruction_eq_local]
  rfl

/-- Extraction after reconstruction recovers both original parameters. -/
theorem quadraticKrullContinuousReconstruction_left_inv (hK : KrullFixingCondition k₀ k) (p : kˣ ×
    (k ≃ₐ[k₀] k)) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm
      (quadraticKrullContinuousReconstruction C S hS hgen hn hK p) = p :=
  (quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm_apply_apply p

/-- Reconstruction after extraction recovers the entire original ordinary diagram. -/
theorem quadraticKrullContinuousReconstruction_right_inv (hK : KrullFixingCondition k₀ k) (g :
    DiagramAut C S) :
    quadraticKrullContinuousReconstruction C S hS hgen hn hK
      ((quadraticKrullContinuousReconstruction C S hS hgen hn hK).symm g) = g :=
      (quadraticKrullContinuousReconstruction C S hS hgen hn hK).apply_symm_apply g

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_scalar_galois (hK : KrullFixingCondition k₀ k) (a :
    kˣ) (σ : k ≃ₐ[k₀] k) :
    quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ) =
      scalarQuadraticAction C S a * galoisQuadraticAction C S σ :=
  quadraticContinuousReconstruction_scalar_galois C S hS hgen hn a σ

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_stage_generator (hK : KrullFixingCondition k₀ k) (a
    : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  quadraticContinuousReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_target (hK : KrullFixingCondition k₀ k) (a : kˣ) (σ
    : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).targetEquiv x = (a : k) • x :=
  quadraticContinuousReconstruction_target C S hS hgen hn a σ x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_dlog (hK : KrullFixingCondition k₀ k) (a : kˣ) (σ :
    k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  quadraticContinuousReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_marking (hK : KrullFixingCondition k₀ k) (a : kˣ)
    (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) :=
  quadraticContinuousReconstruction_marking C S hS hgen hn a σ A w hw x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_inclusion (hK : KrullFixingCondition k₀ k) (p : kˣ
    × (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : degreeOne A.val.val) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK p).stageEquiv A' (componentPull
      ((Daff).complementInclusion hAB) 1 x) =
      componentPull ((Daff).complementInclusion hAB) 1 ((quadraticKrullContinuousReconstruction C
        S hS hgen hn hK p).stageEquiv A x) :=
  quadraticContinuousReconstruction_inclusion C S hS hgen hn p hAB x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstruction_marking_naturality (hK : KrullFixingCondition k₀ k)
    (p : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : degreeOne
      (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstruction C S hS hgen hn hK p).stageEquiv A (componentPull
      (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((quadraticKrullContinuousReconstruction C S hS hgen
        hn hK p).targetEquiv x) :=
  quadraticContinuousReconstruction_marking_naturality C S hS hgen hn p A w hw x

/-- The exact ordinary graded reconstruction for the Krull topology.
The field hypothesis is precisely the displayed condition. Blueprint: T17 (`cor:t17`). -/
def gradedKrullContinuousReconstruction (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (GradedDiagramAut C S) (GradedDiagramAut.stageTopology C S) _ _ where
  toMulEquiv := gradedReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localGradedKrullContinuousReconstruction Tdr C S hS hgen hn
    hK).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localGradedKrullContinuousReconstruction Tdr C S hS hgen hn
    hK).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original ordinary classifier. -/
theorem gradedKrullContinuousReconstruction_toMulEquiv (hK : KrullFixingCondition k₀ k) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).toMulEquiv = gradedReconstruction C S
      hS hgen hn := rfl

/-- The forward function is the original ordinary classifier. -/
theorem gradedKrullContinuousReconstruction_coe (hK : KrullFixingCondition k₀ k) :
    ⇑(gradedKrullContinuousReconstruction C S hS hgen hn hK) = gradedReconstruction C S hS hgen hn
      := rfl

/-- Evaluation keeps the old map; this expansion is a plain rewrite rule. -/
theorem gradedKrullContinuousReconstruction_apply (hK : KrullFixingCondition k₀ k) (p : kˣ × (k
    ≃ₐ[k₀] k)) :
    gradedKrullContinuousReconstruction C S hS hgen hn hK p = gradedReconstruction C S hS hgen hn
      p := rfl

/-- The inverse is exactly the original extraction of both coordinates. -/
theorem gradedKrullContinuousReconstruction_symm_apply (hK : KrullFixingCondition k₀ k) (g :
    GradedDiagramAut C S) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).symm g = (gradedReconstruction C S hS
      hgen hn).symm g := rfl

/-- The old twist identifies this map with the constructed actual Krull classifier. -/
theorem gradedKrullContinuousReconstruction_comparison (hK : KrullFixingCondition k₀ k) (p : kˣ ×
    (k ≃ₐ[k₀] k)) :
    gradedTwistEquiv C S (gradedKrullContinuousReconstruction C S hS hgen hn hK p) =
      Cohomology.localGradedKrullContinuousReconstruction Tdr C S hS hgen hn hK p :=
  gradedTwistEquiv_gradedReconstruction C S hS hgen hn p

/-- The inverse reads the constructed actual coordinates after ordinary twisting. -/
theorem gradedKrullContinuousReconstruction_symm_comparison (hK : KrullFixingCondition k₀ k) (g :
    GradedDiagramAut C S) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).symm g =
      (Cohomology.localGradedKrullContinuousReconstruction Tdr C S hS hgen hn hK).symm
      (gradedTwistEquiv C S g) := rfl

/-- The domain classifier gives the identical ordinary topological equivalence. -/
theorem gradedKrullContinuousReconstruction_eq_domain_composite (hK : KrullFixingCondition k₀ k) :
    gradedKrullContinuousReconstruction C S hS hgen hn hK =
      (Cohomology.domainGradedKrullContinuousReconstruction Tdr C S hS hgen hn hK).trans
      (gradedTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainGradedKrullContinuousReconstruction_eq_local]
  rfl

/-- Extraction after reconstruction recovers both original parameters. -/
theorem gradedKrullContinuousReconstruction_left_inv (hK : KrullFixingCondition k₀ k) (p : kˣ × (k
    ≃ₐ[k₀] k)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).symm
      (gradedKrullContinuousReconstruction C S hS hgen hn hK p) = p :=
  (gradedKrullContinuousReconstruction C S hS hgen hn hK).symm_apply_apply p

/-- Reconstruction after extraction recovers the entire original ordinary diagram. -/
theorem gradedKrullContinuousReconstruction_right_inv (hK : KrullFixingCondition k₀ k) (g :
    GradedDiagramAut C S) :
    gradedKrullContinuousReconstruction C S hS hgen hn hK ((gradedKrullContinuousReconstruction C
      S hS hgen hn hK).symm g) = g := (gradedKrullContinuousReconstruction C S hS hgen hn
      hK).apply_symm_apply g

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_scalar_galois (hK : KrullFixingCondition k₀ k) (a :
    kˣ) (σ : k ≃ₐ[k₀] k) :
    gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ) =
      scalarGradedAction C S a * galoisGradedAction C S σ :=
  gradedContinuousReconstruction_scalar_galois C S hS hgen hn a σ

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_stage_generator (hK : KrullFixingCondition k₀ k) (a :
    kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) :=
  gradedContinuousReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_stage_degree (hK : KrullFixingCondition k₀ k) (a : kˣ)
    (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedContinuousReconstruction_stage_degree C S hS hgen hn a σ A q x hx

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_target_degree (hK : KrullFixingCondition k₀ k) (a :
    kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).targetEquiv (x : HdR _) =
      (a : k)^q • (x : HdR _) :=
  gradedContinuousReconstruction_target_degree C S hS hgen hn a σ q x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_dlog (hK : KrullFixingCondition k₀ k) (a : kˣ) (σ : k
    ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_dlog_fieldAffineForm (hK : KrullFixingCondition k₀ k)
    (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog_fieldAffineForm C S hS hgen hn a σ A H hf

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_marking_degree (hK : KrullFixingCondition k₀ k) (a :
    kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) :=
  gradedContinuousReconstruction_marking_degree C S hS hgen hn a σ A w hw q x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_inclusion (hK : KrullFixingCondition k₀ k) (p : kˣ ×
    (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : HdR ((Daff).complement A.val.val)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK p).stageEquiv A'
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB) x) =
      Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB)
        ((gradedKrullContinuousReconstruction C S hS hgen hn hK p).stageEquiv A x) :=
  gradedContinuousReconstruction_inclusion C S hS hgen hn p hAB x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_marking_naturality (hK : KrullFixingCondition k₀ k) (p
    : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : HdR
      (Cohomology.schemeMarkingTarget Daff)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK p).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((gradedKrullContinuousReconstruction
        C S hS hgen hn hK p).targetEquiv x) :=
  gradedContinuousReconstruction_marking_naturality C S hS hgen hn p A w hw x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_smul (hK : KrullFixingCondition k₀ k) (a : kˣ) (σ : k
    ≃ₐ[k₀] k) (A : C.Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A (c • x) =
      c • (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).stageEquiv A x :=
  gradedContinuousReconstruction_smul C S hS hgen hn a σ A c x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_target_smul (hK : KrullFixingCondition k₀ k) (a : kˣ)
    (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).targetEquiv (c • x) =
      c • (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).targetEquiv x :=
  gradedContinuousReconstruction_target_smul C S hS hgen hn a σ c x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstruction_target_dlog (hK : KrullFixingCondition k₀ k) (a : kˣ)
    (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) :=
  gradedContinuousReconstruction_target_dlog C S hS hgen hn a σ i

/-- The bundled ordinary restriction square keeps exactly the same two coordinates. -/
theorem gradedKrullContinuousReconstruction_trans_restriction (hK : KrullFixingCondition k₀ k) :
    (gradedKrullContinuousReconstruction C S hS hgen hn hK).trans (restrictionContinuousEquiv C S
      hS hgen hn) = quadraticKrullContinuousReconstruction C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  exact restrictionEquiv_gradedReconstruction C S hS hgen hn p

/-- Literal degree-one restriction preserves both Krull-classified parameters. -/
theorem gradedKrullContinuousReconstruction_toQuadratic (hK : KrullFixingCondition k₀ k) (p : kˣ ×
    (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic C S (gradedKrullContinuousReconstruction C S hS hgen hn hK p) =
      quadraticKrullContinuousReconstruction C S hS hgen hn hK p :=
  gradedContinuousReconstruction_toQuadratic C S hS hgen hn p

/-- The exact ordinary quadratic reconstruction for the Krull topology.
The field hypothesis is precisely the displayed condition. Blueprint: T17 (`cor:t17`). -/
def quadraticKrullContinuousReconstructionOfIsAlgebraic [Algebra.IsAlgebraic k₀ k] :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (DiagramAut C S) (DiagramAut.stageTopology C S) _ _ where
  toMulEquiv := quadraticReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localQuadraticKrullContinuousReconstructionOfIsAlgebraic Tdr C
    S hS hgen hn).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localQuadraticKrullContinuousReconstructionOfIsAlgebraic Tdr C
    S hS hgen hn).trans
    (quadraticTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original ordinary classifier. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [Algebra.IsAlgebraic k₀ k] :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).toMulEquiv =
      quadraticReconstruction C S hS hgen hn := rfl

/-- The forward function is the original ordinary classifier. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_coe [Algebra.IsAlgebraic k₀ k] :
    ⇑(quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn) =
      quadraticReconstruction C S hS hgen hn := rfl

/-- Evaluation keeps the old map; this expansion is a plain rewrite rule. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_apply [Algebra.IsAlgebraic k₀ k] (p :
    kˣ × (k ≃ₐ[k₀] k)) :
    quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p = quadraticReconstruction
      C S hS hgen hn p := rfl

/-- The inverse is exactly the original extraction of both coordinates. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_symm_apply [Algebra.IsAlgebraic k₀ k]
    (g : DiagramAut C S) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g =
      (quadraticReconstruction C S hS hgen hn).symm g := rfl

/-- The old twist identifies this map with the constructed actual Krull classifier. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_comparison [Algebra.IsAlgebraic k₀ k]
    (p : kˣ × (k ≃ₐ[k₀] k)) :
    quadraticTwistEquiv C S (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p)
      = Cohomology.localQuadraticKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen hn p :=
  quadraticTwistEquiv_quadraticReconstruction C S hS hgen hn p

/-- The inverse reads the constructed actual coordinates after ordinary twisting. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [Algebra.IsAlgebraic
    k₀ k] (g : DiagramAut C S) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g =
      (Cohomology.localQuadraticKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen
      hn).symm (quadraticTwistEquiv C S g) := rfl

/-- The domain classifier gives the identical ordinary topological equivalence. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_eq_domain_composite
    [Algebra.IsAlgebraic k₀ k] :
    quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn =
      (Cohomology.domainQuadraticKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen
      hn).trans
      (quadraticTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_eq_local]
  rfl

/-- Extraction after reconstruction recovers both original parameters. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_left_inv [Algebra.IsAlgebraic k₀ k] (p
    : kˣ × (k ≃ₐ[k₀] k)) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm
      (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) = p :=
  (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm_apply_apply p

/-- Reconstruction after extraction recovers the entire original ordinary diagram. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_right_inv [Algebra.IsAlgebraic k₀ k]
    (g : DiagramAut C S) :
    quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn
      ((quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g) = g :=
      (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).apply_symm_apply g

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_scalar_galois [Algebra.IsAlgebraic k₀
    k] (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ) =
      scalarQuadraticAction C S a * galoisQuadraticAction C S σ :=
  quadraticContinuousReconstruction_scalar_galois C S hS hgen hn a σ

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_stage_generator [Algebra.IsAlgebraic
    k₀ k] (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  quadraticContinuousReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_target [Algebra.IsAlgebraic k₀ k] (a :
    kˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).targetEquiv x = (a
      : k) • x :=
  quadraticContinuousReconstruction_target C S hS hgen hn a σ x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_dlog [Algebra.IsAlgebraic k₀ k] (a :
    kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  quadraticContinuousReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_marking [Algebra.IsAlgebraic k₀ k] (a
    : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) :=
  quadraticContinuousReconstruction_marking C S hS hgen hn a σ A w hw x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_inclusion [Algebra.IsAlgebraic k₀ k]
    (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : degreeOne A.val.val) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A'
      (componentPull ((Daff).complementInclusion hAB) 1 x) =
      componentPull ((Daff).complementInclusion hAB) 1
        ((quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A x) :=
  quadraticContinuousReconstruction_inclusion C S hS hgen hn p hAB x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem quadraticKrullContinuousReconstructionOfIsAlgebraic_marking_naturality
    [Algebra.IsAlgebraic k₀ k] (p : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : degreeOne
      (twoPunctureArrangement k)) :
    (quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((quadraticKrullContinuousReconstructionOfIsAlgebraic
        C S hS hgen hn p).targetEquiv x) :=
  quadraticContinuousReconstruction_marking_naturality C S hS hgen hn p A w hw x

/-- The exact ordinary graded reconstruction for the Krull topology.
The field hypothesis is precisely the displayed condition. Blueprint: T17 (`cor:t17`). -/
def gradedKrullContinuousReconstructionOfIsAlgebraic [Algebra.IsAlgebraic k₀ k] :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (GradedDiagramAut C S) (GradedDiagramAut.stageTopology C S) _ _ where
  toMulEquiv := gradedReconstruction C S hS hgen hn
  continuous_toFun := ((Cohomology.localGradedKrullContinuousReconstructionOfIsAlgebraic Tdr C S
    hS hgen hn).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_toFun
  continuous_invFun := ((Cohomology.localGradedKrullContinuousReconstructionOfIsAlgebraic Tdr C S
    hS hgen hn).trans
    (gradedTwistContinuousEquiv C S).symm).continuous_invFun

/-- Forgetting continuity recovers exactly the original ordinary classifier. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_toMulEquiv [Algebra.IsAlgebraic k₀ k] :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).toMulEquiv =
      gradedReconstruction C S hS hgen hn := rfl

/-- The forward function is the original ordinary classifier. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_coe [Algebra.IsAlgebraic k₀ k] :
    ⇑(gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn) = gradedReconstruction C S
      hS hgen hn := rfl

/-- Evaluation keeps the old map; this expansion is a plain rewrite rule. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_apply [Algebra.IsAlgebraic k₀ k] (p : kˣ
    × (k ≃ₐ[k₀] k)) :
    gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p = gradedReconstruction C S
      hS hgen hn p := rfl

/-- The inverse is exactly the original extraction of both coordinates. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_symm_apply [Algebra.IsAlgebraic k₀ k] (g
    : GradedDiagramAut C S) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g =
      (gradedReconstruction C S hS hgen hn).symm g := rfl

/-- The old twist identifies this map with the constructed actual Krull classifier. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_comparison [Algebra.IsAlgebraic k₀ k] (p
    : kˣ × (k ≃ₐ[k₀] k)) :
    gradedTwistEquiv C S (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) =
      Cohomology.localGradedKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen hn p :=
  gradedTwistEquiv_gradedReconstruction C S hS hgen hn p

/-- The inverse reads the constructed actual coordinates after ordinary twisting. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_symm_comparison [Algebra.IsAlgebraic k₀
    k] (g : GradedDiagramAut C S) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g =
      (Cohomology.localGradedKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen hn).symm
      (gradedTwistEquiv C S g) := rfl

/-- The domain classifier gives the identical ordinary topological equivalence. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_eq_domain_composite [Algebra.IsAlgebraic
    k₀ k] :
    gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn =
      (Cohomology.domainGradedKrullContinuousReconstructionOfIsAlgebraic Tdr C S hS hgen hn).trans
      (gradedTwistContinuousEquiv C S).symm := by
  rw [Cohomology.domainGradedKrullContinuousReconstructionOfIsAlgebraic_eq_local]
  rfl

/-- Extraction after reconstruction recovers both original parameters. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_left_inv [Algebra.IsAlgebraic k₀ k] (p :
    kˣ × (k ≃ₐ[k₀] k)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm
      (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p) = p :=
  (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm_apply_apply p

/-- Reconstruction after extraction recovers the entire original ordinary diagram. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_right_inv [Algebra.IsAlgebraic k₀ k] (g :
    GradedDiagramAut C S) :
    gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn
      ((gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).symm g) = g :=
      (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).apply_symm_apply g

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_scalar_galois [Algebra.IsAlgebraic k₀ k]
    (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ) =
      scalarGradedAction C S a * galoisGradedAction C S σ :=
  gradedContinuousReconstruction_scalar_galois C S hS hgen hn a σ

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_stage_generator [Algebra.IsAlgebraic k₀
    k] (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) :=
  gradedContinuousReconstruction_stage_generator C S hS hgen hn a σ A H

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_stage_degree [Algebra.IsAlgebraic k₀ k]
    (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedContinuousReconstruction_stage_degree C S hS hgen hn a σ A q x hx

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_target_degree [Algebra.IsAlgebraic k₀ k]
    (a : kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).targetEquiv (x : HdR
      _) =
      (a : k)^q • (x : HdR _) :=
  gradedContinuousReconstruction_target_degree C S hS hgen hn a σ q x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_dlog [Algebra.IsAlgebraic k₀ k] (a : kˣ)
    (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog C S hS hgen hn a σ A H hf hf'

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_dlog_fieldAffineForm [Algebra.IsAlgebraic
    k₀ k] (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog_fieldAffineForm C S hS hgen hn a σ A H hf

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_marking_degree [Algebra.IsAlgebraic k₀ k]
    (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) :=
  gradedContinuousReconstruction_marking_degree C S hS hgen hn a σ A w hw q x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_inclusion [Algebra.IsAlgebraic k₀ k] (p :
    kˣ × (k ≃ₐ[k₀] k))
    {A A' : C.Stage} (hAB : A ≤ A') (x : HdR ((Daff).complement A.val.val)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A'
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB) x) =
      Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB)
        ((gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A x) :=
  gradedContinuousReconstruction_inclusion C S hS hgen hn p hAB x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_marking_naturality [Algebra.IsAlgebraic
    k₀ k] (p : kˣ × (k ≃ₐ[k₀] k))
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : HdR
      (Cohomology.schemeMarkingTarget Daff)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)
        ((gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p).targetEquiv x) :=
  gradedContinuousReconstruction_marking_naturality C S hS hgen hn p A w hw x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_smul [Algebra.IsAlgebraic k₀ k] (a : kˣ)
    (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A (c • x) =
      c • (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).stageEquiv A x :=
  gradedContinuousReconstruction_smul C S hS hgen hn a σ A c x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_target_smul [Algebra.IsAlgebraic k₀ k] (a
    : kˣ) (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).targetEquiv (c • x) =
      c • (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).targetEquiv x :=
  gradedContinuousReconstruction_target_smul C S hS hgen hn a σ c x

/-- The Krull wrapper preserves the exact whole ordinary action equation. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_target_dlog [Algebra.IsAlgebraic k₀ k] (a
    : kˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) :=
  gradedContinuousReconstruction_target_dlog C S hS hgen hn a σ i

/-- The bundled ordinary restriction square keeps exactly the same two coordinates. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_trans_restriction [Algebra.IsAlgebraic k₀
    k] :
    (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn).trans
      (restrictionContinuousEquiv C S hS hgen hn) =
      quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact restrictionEquiv_gradedReconstruction C S hS hgen hn p

/-- Literal degree-one restriction preserves both Krull-classified parameters. -/
theorem gradedKrullContinuousReconstructionOfIsAlgebraic_toQuadratic [Algebra.IsAlgebraic k₀ k] (p
    : kˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic C S (gradedKrullContinuousReconstructionOfIsAlgebraic C S hS hgen
      hn p) = quadraticKrullContinuousReconstructionOfIsAlgebraic C S hS hgen hn p :=
  gradedContinuousReconstruction_toQuadratic C S hS hgen hn p

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
