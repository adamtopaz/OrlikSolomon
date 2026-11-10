/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Krull

/-!
# Ordinary reconstruction on the canonical full stable family

The four product classifiers and degree-one restriction are exact specializations of
proved ordinary homeomorphisms. Algebraicity remains explicit solely because the old
canonical full stable family uses it; no supplied family or additional fixing condition
replaces that constructor input. The original full ordinary algebra, complete H¹/cup
kernel and single common target are unchanged.

All whole-degree, coefficient-linear dlog and actual inclusion/marking equations retain
their original carriers, primal scalar and covariant label action. Degree zero is included.
Expansion equations are plain rewrites, so both bare inverse cancellations remain available.
Blueprint: the full-family clauses of T17 (`cor:t17`).
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
local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "HdRdegree" => Geometric.DeRham.Cohomology.degree

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

section Pointwise

open scoped GaloisPointwise

/-- The exact old full ordinary quadratic classifier, with its proved two-way continuity.
Algebraicity is retained for the canonical family constructor. Blueprint: T17 (`cor:t17`). -/
def fullQuadraticContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisPointwiseTopology k k₀ k)
      (DiagramAut F S) (DiagramAut.stageTopology F S) _ _ :=
  quadraticContinuousReconstruction F S hS hgen hn

/-- This full-family bundle is exactly the indicated supplied-family specialization. -/
theorem fullQuadraticContinuousReconstruction_eq_specialization :
    fullQuadraticContinuousReconstruction (k := k) S hS hgen hn =
      quadraticContinuousReconstruction F S hS
    hgen hn := rfl

/-- Forgetting continuity retains the exact old full-family ordinary reconstruction. -/
theorem fullQuadraticContinuousReconstruction_toMulEquiv : (fullQuadraticContinuousReconstruction
    S hS hgen hn).toMulEquiv = fullQuadraticReconstruction (k := k) S hS hgen hn := rfl

/-- The entire forward function is the exact old full ordinary classifier. -/
theorem fullQuadraticContinuousReconstruction_coe : ⇑(fullQuadraticContinuousReconstruction (k :=
    k) S hS
    hgen hn) = fullQuadraticReconstruction (k := k) S hS hgen hn := rfl

/-- Every full-family value uses the original ordinary reconstruction. -/
theorem fullQuadraticContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    fullQuadraticContinuousReconstruction (k := k) S hS hgen hn p = fullQuadraticReconstruction (k
      := k) S hS hgen
      hn p := rfl

/-- The inverse extracts the exact old full ordinary scalar and Galois coordinates. -/
theorem fullQuadraticContinuousReconstruction_symm_apply (g : DiagramAut F S) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm g =
      (fullQuadraticReconstruction (k := k) S
      hS hgen hn).symm g := rfl

/-- Reconstruction followed by extraction recovers both parameters. -/
theorem fullQuadraticContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn p) = p :=
      (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original diagram. -/
theorem fullQuadraticContinuousReconstruction_right_inv (g : DiagramAut F S) :
    fullQuadraticContinuousReconstruction (k := k) S hS hgen hn
      ((fullQuadraticContinuousReconstruction (k := k) S
      hS hgen hn).symm g) = g := (fullQuadraticContinuousReconstruction (k := k) S hS hgen
      hn).apply_symm_apply g

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ) =
      scalarQuadraticAction F S a * galoisQuadraticAction F S σ :=
  quadraticContinuousReconstruction_scalar_galois F S hS hgen hn a σ

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  quadraticContinuousReconstruction_stage_generator F S hS hgen hn a σ A H

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_target (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv x = (a : k) •
      x :=
  quadraticContinuousReconstruction_target F S hS hgen hn a σ x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  quadraticContinuousReconstruction_dlog F S hS hgen hn a σ A H hf hf'

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_marking (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) :=
  quadraticContinuousReconstruction_marking F S hS hgen hn a σ A w hw x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : (F).Stage} (hAB : A ≤ A') (x : degreeOne A.val.val) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A' (componentPull
      ((Daff).complementInclusion hAB) 1 x) =
      componentPull ((Daff).complementInclusion hAB) 1 ((quadraticContinuousReconstruction F S hS
        hgen hn p).stageEquiv A x) :=
  quadraticContinuousReconstruction_inclusion F S hS hgen hn p hAB x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : (F).Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : degreeOne
      (twoPunctureArrangement k)) :
    (fullQuadraticContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A (componentPull
      (w.schemeMap
      Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((fullQuadraticContinuousReconstruction (k := k) S hS
        hgen hn
        p).targetEquiv x) :=
  quadraticContinuousReconstruction_marking_naturality F S hS hgen hn p A w hw x

/-- The exact old full ordinary graded classifier, with its proved two-way continuity.
Algebraicity is retained for the canonical family constructor. Blueprint: T17 (`cor:t17`). -/
def fullGradedContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisPointwiseTopology k k₀ k)
      (GradedDiagramAut F S) (GradedDiagramAut.stageTopology F S) _ _ :=
  gradedContinuousReconstruction F S hS hgen hn

/-- This full-family bundle is exactly the indicated supplied-family specialization. -/
theorem fullGradedContinuousReconstruction_eq_specialization : fullGradedContinuousReconstruction
    S hS hgen hn = gradedContinuousReconstruction F S hS hgen hn := rfl

/-- Forgetting continuity retains the exact old full-family ordinary reconstruction. -/
theorem fullGradedContinuousReconstruction_toMulEquiv : (fullGradedContinuousReconstruction (k :=
    k) S hS
    hgen hn).toMulEquiv = fullGradedReconstruction (k := k) S hS hgen hn := rfl

/-- The entire forward function is the exact old full ordinary classifier. -/
theorem fullGradedContinuousReconstruction_coe : ⇑(fullGradedContinuousReconstruction (k := k) S
    hS hgen
    hn) = fullGradedReconstruction (k := k) S hS hgen hn := rfl

/-- Every full-family value uses the original ordinary reconstruction. -/
theorem fullGradedContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    fullGradedContinuousReconstruction (k := k) S hS hgen hn p = fullGradedReconstruction (k := k)
      S hS hgen hn p :=
      rfl

/-- The inverse extracts the exact old full ordinary scalar and Galois coordinates. -/
theorem fullGradedContinuousReconstruction_symm_apply (g : GradedDiagramAut F S) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn).symm g = (fullGradedReconstruction
      (k := k) S hS hgen
      hn).symm g := rfl

/-- Reconstruction followed by extraction recovers both parameters. -/
theorem fullGradedContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullGradedContinuousReconstruction (k := k) S
      hS hgen hn p) = p := (fullGradedContinuousReconstruction (k := k) S hS hgen
        hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original diagram. -/
theorem fullGradedContinuousReconstruction_right_inv (g : GradedDiagramAut F S) :
    fullGradedContinuousReconstruction (k := k) S hS hgen hn ((fullGradedContinuousReconstruction
      (k := k) S hS hgen
      hn).symm g) = g := (fullGradedContinuousReconstruction (k := k) S hS hgen
        hn).apply_symm_apply g

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ) =
      scalarGradedAction F S a * galoisGradedAction F S σ :=
  gradedContinuousReconstruction_scalar_galois F S hS hgen hn a σ

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) :=
  gradedContinuousReconstruction_stage_generator F S hS hgen hn a σ A H

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_stage_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedContinuousReconstruction_stage_degree F S hS hgen hn a σ A q x hx

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_target_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv (x : HdR _) =
      (a : k)^q • (x : HdR _) :=
  gradedContinuousReconstruction_target_degree F S hS hgen hn a σ q x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage) (H :
    A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog F S hS hgen hn a σ A H hf hf'

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_dlog_fieldAffineForm (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog_fieldAffineForm F S hS hgen hn a σ A H hf

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_marking_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) :=
  gradedContinuousReconstruction_marking_degree F S hS hgen hn a σ A w hw q x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : (F).Stage} (hAB : A ≤ A') (x : HdR ((Daff).complement A.val.val)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A'
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB) x) =
      Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB)
        ((fullGradedContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A x) :=
  gradedContinuousReconstruction_inclusion F S hS hgen hn p hAB x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : (F).Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : HdR
      (Cohomology.schemeMarkingTarget Daff)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((gradedContinuousReconstruction F S
        hS hgen hn p).targetEquiv x) :=
  gradedContinuousReconstruction_marking_naturality F S hS hgen hn p A w hw x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_smul (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A (c • x) =
      c • (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A x :=
  gradedContinuousReconstruction_smul F S hS hgen hn a σ A c x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_target_smul (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv (c • x) =
      c • (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv x :=
  gradedContinuousReconstruction_target_smul F S hS hgen hn a σ c x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedContinuousReconstruction_target_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) :=
  gradedContinuousReconstruction_target_dlog F S hS hgen hn a σ i

end Pointwise

/-- The exact old full ordinary quadratic classifier, with its proved two-way continuity.
Algebraicity is retained for the canonical family constructor. Blueprint: T17 (`cor:t17`). -/
def fullQuadraticKrullContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (DiagramAut F S) (DiagramAut.stageTopology F S) _ _ :=
  quadraticKrullContinuousReconstructionOfIsAlgebraic F S hS hgen hn

/-- This full-family bundle is exactly the indicated supplied-family specialization. -/
theorem fullQuadraticKrullContinuousReconstruction_eq_specialization :
    fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn =
    quadraticKrullContinuousReconstructionOfIsAlgebraic F S hS hgen hn := rfl

/-- Forgetting continuity retains the exact old full-family ordinary reconstruction. -/
theorem fullQuadraticKrullContinuousReconstruction_toMulEquiv :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).toMulEquiv =
    fullQuadraticReconstruction (k := k) S hS hgen hn := rfl

/-- The entire forward function is the exact old full ordinary classifier. -/
theorem fullQuadraticKrullContinuousReconstruction_coe :
    ⇑(fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn) =
      fullQuadraticReconstruction (k := k) S hS
    hgen hn := rfl

/-- Every full-family value uses the original ordinary reconstruction. -/
theorem fullQuadraticKrullContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn p =
      fullQuadraticReconstruction (k := k) S hS
      hgen hn p := rfl

/-- The inverse extracts the exact old full ordinary scalar and Galois coordinates. -/
theorem fullQuadraticKrullContinuousReconstruction_symm_apply (g : DiagramAut F S) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm g =
      (fullQuadraticReconstruction (k := k) S hS hgen hn).symm g := rfl

/-- Reconstruction followed by extraction recovers both parameters. -/
theorem fullQuadraticKrullContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn p) = p :=
      (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original diagram. -/
theorem fullQuadraticKrullContinuousReconstruction_right_inv (g : DiagramAut F S) :
    fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn
      ((fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).symm g) = g :=
      (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn).apply_symm_apply g

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ) =
      scalarQuadraticAction F S a * galoisQuadraticAction F S σ :=
  quadraticContinuousReconstruction_scalar_galois F S hS hgen hn a σ

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) :=
  quadraticContinuousReconstruction_stage_generator F S hS hgen hn a σ A H

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_target (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv x = (a :
      k) • x :=
  quadraticContinuousReconstruction_target F S hS hgen hn a σ x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  quadraticContinuousReconstruction_dlog F S hS hgen hn a σ A H hf hf'

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_marking (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) :=
  quadraticContinuousReconstruction_marking F S hS hgen hn a σ A w hw x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : (F).Stage} (hAB : A ≤ A') (x : degreeOne A.val.val) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A'
      (componentPull
      ((Daff).complementInclusion hAB) 1 x) =
      componentPull ((Daff).complementInclusion hAB) 1 ((quadraticContinuousReconstruction F S hS
        hgen hn p).stageEquiv A x) :=
  quadraticContinuousReconstruction_inclusion F S hS hgen hn p hAB x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullQuadraticKrullContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : (F).Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : degreeOne
      (twoPunctureArrangement k)) :
    (fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A (componentPull
      (w.schemeMap
      Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((fullQuadraticKrullContinuousReconstruction (k := k)
        S hS hgen
        hn
        p).targetEquiv x) :=
  quadraticContinuousReconstruction_marking_naturality F S hS hgen hn p A w hw x

/-- The exact old full ordinary graded classifier, with its proved two-way continuity.
Algebraicity is retained for the canonical family constructor. Blueprint: T17 (`cor:t17`). -/
def fullGradedKrullContinuousReconstruction :
    @ContinuousMulEquiv (kˣ × (k ≃ₐ[k₀] k)) (coefficientGaloisKrullTopology k k₀ k)
      (GradedDiagramAut F S) (GradedDiagramAut.stageTopology F S) _ _ :=
  gradedKrullContinuousReconstructionOfIsAlgebraic F S hS hgen hn

/-- This full-family bundle is exactly the indicated supplied-family specialization. -/
theorem fullGradedKrullContinuousReconstruction_eq_specialization :
    fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn =
    gradedKrullContinuousReconstructionOfIsAlgebraic F S hS hgen hn := rfl

/-- Forgetting continuity retains the exact old full-family ordinary reconstruction. -/
theorem fullGradedKrullContinuousReconstruction_toMulEquiv :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).toMulEquiv =
      fullGradedReconstruction (k := k) S
    hS hgen hn := rfl

/-- The entire forward function is the exact old full ordinary classifier. -/
theorem fullGradedKrullContinuousReconstruction_coe : ⇑(fullGradedKrullContinuousReconstruction (k
    := k) S
    hS hgen hn) = fullGradedReconstruction (k := k) S hS hgen hn := rfl

/-- Every full-family value uses the original ordinary reconstruction. -/
theorem fullGradedKrullContinuousReconstruction_apply (p : kˣ × (k ≃ₐ[k₀] k)) :
    fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p = fullGradedReconstruction (k
      := k) S hS hgen hn
      p := rfl

/-- The inverse extracts the exact old full ordinary scalar and Galois coordinates. -/
theorem fullGradedKrullContinuousReconstruction_symm_apply (g : GradedDiagramAut F S) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm g =
      (fullGradedReconstruction (k := k) S hS
      hgen hn).symm g := rfl

/-- Reconstruction followed by extraction recovers both parameters. -/
theorem fullGradedKrullContinuousReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm
      (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p) = p :=
      (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).symm_apply_apply p

/-- Extraction followed by reconstruction recovers the entire original diagram. -/
theorem fullGradedKrullContinuousReconstruction_right_inv (g : GradedDiagramAut F S) :
    fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn
      ((fullGradedKrullContinuousReconstruction
      S hS hgen hn).symm g) = g := (fullGradedKrullContinuousReconstruction (k := k) S hS hgen
      hn).apply_symm_apply g

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_scalar_galois (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ) =
      scalarGradedAction F S a * galoisGradedAction F S σ :=
  gradedContinuousReconstruction_scalar_galois F S hS hgen hn a σ

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) :=
  gradedContinuousReconstruction_stage_generator F S hS hgen hn a σ A H

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_stage_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A :
    (F).Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  gradedContinuousReconstruction_stage_degree F S hS hgen hn a σ A q x hx

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_target_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv (x : HdR _) =
      (a : k)^q • (x : HdR _) :=
  gradedContinuousReconstruction_target_degree F S hS hgen hn a σ q x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage) (H :
    A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog F S hS hgen hn a σ A H hf hf'

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_dlog_fieldAffineForm (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : (F).Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedContinuousReconstruction_dlog_fieldAffineForm F S hS hgen hn a σ A H hf

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_marking_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A :
    (F).Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) :=
  gradedContinuousReconstruction_marking_degree F S hS hgen hn a σ A w hw q x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_inclusion (p : kˣ × (k ≃ₐ[k₀] k))
    {A A' : (F).Stage} (hAB : A ≤ A') (x : HdR ((Daff).complement A.val.val)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A'
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB) x) =
      Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hAB)
        ((fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A x) :=
  gradedContinuousReconstruction_inclusion F S hS hgen hn p hAB x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_marking_naturality (p : kˣ × (k ≃ₐ[k₀] k))
    (A : (F).Stage) (w : Marking S n) (hw : w.Available A.val.val) (x : HdR
      (Cohomology.schemeMarkingTarget Daff)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn p).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((gradedContinuousReconstruction F S
        hS hgen hn p).targetEquiv x) :=
  gradedContinuousReconstruction_marking_naturality F S hS hgen hn p A w hw x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_smul (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : (F).Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A (c • x) =
      c • (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).stageEquiv A x :=
  gradedContinuousReconstruction_smul F S hS hgen hn a σ A c x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_target_smul (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv (c • x) =
      c • (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv x :=
  gradedContinuousReconstruction_target_smul F S hS hgen hn a σ c x

/-- Full-family specialization preserves the exact whole ordinary action equation. -/
theorem fullGradedKrullContinuousReconstruction_target_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) :=
  gradedContinuousReconstruction_target_dlog F S hS hgen hn a σ i

/-- Literal ordinary degree-one restriction on the canonical full stable family.
Algebraicity is used solely to construct that family. Blueprint: T17 (`cor:t17`). -/
def fullRestrictionContinuousEquiv : GradedDiagramAut F S ≃ₜ* DiagramAut F S :=
  restrictionContinuousEquiv F S hS hgen hn

/-- Full-family restriction is exactly the generic ordinary specialization. -/
theorem fullRestrictionContinuousEquiv_eq_specialization :
    fullRestrictionContinuousEquiv (k := k) S hS hgen hn = restrictionContinuousEquiv F S hS hgen
      hn := rfl

/-- The multiplicative field is the exact old full-family ordinary restriction. -/
theorem fullRestrictionContinuousEquiv_toMulEquiv :
    (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).toMulEquiv = restrictionEquiv F S hS
      hgen hn :=
      rfl

/-- The complete function is the old ordinary degree-one equivalence. -/
theorem fullRestrictionContinuousEquiv_coe :
    ⇑(fullRestrictionContinuousEquiv (k := k) S hS hgen hn) = restrictionEquiv F S hS hgen hn := rfl

/-- The forward map is the original literal ordinary degree-one restriction. -/
theorem fullRestrictionContinuousEquiv_apply (g : GradedDiagramAut F S) :
    fullRestrictionContinuousEquiv (k := k) S hS hgen hn g = GradedDiagramAut.toQuadratic F S g :=
  restrictionContinuousEquiv_apply F S hS hgen hn g

/-- The inverse is the exact old ordinary full-family inverse. -/
theorem fullRestrictionContinuousEquiv_symm_apply (g : DiagramAut F S) :
    (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm g =
      (restrictionEquiv F S hS hgen hn).symm g := rfl

/-- Restriction followed by its inverse recovers every whole ordinary diagram. -/
theorem fullRestrictionContinuousEquiv_left_inv (g : GradedDiagramAut F S) :
    (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm
      (fullRestrictionContinuousEquiv (k := k) S hS hgen hn g) = g :=
  (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm_apply_apply g

/-- The inverse followed by restriction recovers every original quadratic diagram. -/
theorem fullRestrictionContinuousEquiv_right_inv (g : DiagramAut F S) :
    fullRestrictionContinuousEquiv (k := k) S hS hgen hn
      ((fullRestrictionContinuousEquiv (k := k) S hS hgen hn).symm g) = g :=
  (fullRestrictionContinuousEquiv (k := k) S hS hgen hn).apply_symm_apply g

section Pointwise

open scoped GaloisPointwise

/-- The full-family pointwise classification and literal restriction square commutes. -/
theorem fullGradedContinuousReconstruction_trans_restriction :
    (fullGradedContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullRestrictionContinuousEquiv (k := k) S hS hgen hn) =
        fullQuadraticContinuousReconstruction (k := k) S hS hgen hn :=
  gradedContinuousReconstruction_trans_restriction F S hS hgen hn

end Pointwise

/-- The full-family Krull classification and literal restriction square commutes. -/
theorem fullGradedKrullContinuousReconstruction_trans_restriction :
    (fullGradedKrullContinuousReconstruction (k := k) S hS hgen hn).trans
      (fullRestrictionContinuousEquiv (k := k) S hS hgen hn) =
        fullQuadraticKrullContinuousReconstruction (k := k) S hS hgen hn :=
  gradedKrullContinuousReconstructionOfIsAlgebraic_trans_restriction F S hS hgen hn

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
