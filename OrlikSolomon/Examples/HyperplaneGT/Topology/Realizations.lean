/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Coefficients
public import OrlikSolomon.Examples.Sanity
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Realization.Compatibility
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits

/-!
# Actual-theory finite-stage topology consumers

The actual diagram and scalar quotient comparisons retain arbitrary supplied theories and
the original common target. The existing zero theory supplies concrete zero-coefficient
and dimension-zero consumers, without a nontriviality hypothesis. This is a consistency
fixture, not a test of the substantive cohomology axioms or a new nonzero realization.

The default field-automorphism topology remains Mathlib's actual Krull topology, also
when the deliberate finite-stage scope and an unrelated geometric-field topology are used.

## Main results

* `actualZeroTheory`, `zero_quadratic_eq_one`, `zero_graded_eq_one` and
  `zero_stageKernel_eq_top`: actual zero-coefficient and dimension-zero fixtures.
* `zero_quotient_roundtrip`, `zero_graded_quotient_roundtrip` and `preserves_global_krull`:
  public inverse and scope-isolation consumers.
* `exists_target_detected_at_dimension_zero`: a supplied characteristic-two theory
  retains a target action invisible at every stage in dimension zero.

The realization consumers retain independent theories and all four bare inverse pairs,
whole-stage/common-target formulas and the three-theory cocycle. A conditional binary
example proves that target detection survives comparison in dimension zero; the concrete
zero theory supplies the separate zero-coefficient boundary case.

Blueprint: acceptance consumers for T01–T02, T14 and T16
(`def:t01`, `lem:t02`, `thm:t14`, `thm:t16`).
-/

@[expose] public section

noncomputable section

universe u b h

namespace OrlikSolomon.HyperplaneGT.Cohomology.TopologyExamples

open scoped FiniteStageTopology

variable (k : Type u) [Field k]

/-- For a supplied characteristic-two theory, the dimension-zero diagram has an element
acting identically at every stage but excluded from every stage-and-target kernel.
This transports the existing target swap; it does not construct a nonzero mod-two theory. -/
theorem exists_target_detected_at_dimension_zero
    {B : Type b} [CommRing B] [Algebra (ZMod 2) B]
    {ℬ : ℤ → Submodule (ZMod 2) B} [GradedAlgebra ℬ]
    {D : Geometric.SmoothDomain (ZMod 2)}
    (T : Geometric.OrdinaryTheory.{0, 0, b, h} D ℬ) :
    ∃ g : DiagramAut T (DiagramExamples.binarySystem 0) ({0} : Set (ZMod 2)),
      (∀ A, g.stageEquiv A = 1) ∧
        ∀ A, g ∉ DiagramAut.stageKernel T (DiagramExamples.binarySystem 0)
          ({0} : Set (ZMod 2)) A := by
  let e := degreeOneDiagramContinuousEquiv T (DiagramExamples.binarySystem 0)
    ({0} : Set (ZMod 2))
  let swap := DiagramExamples.zeroDimensionSwap (ZMod 2)
  refine ⟨e.symm swap, ?_, ?_⟩
  · intro A
    apply (degreeOneDiagramEquiv_stage_eq_iff T (DiagramExamples.binarySystem 0)
      ({0} : Set (ZMod 2)) _ 1 A).mp
    change (e (e.symm swap)).stageEquiv A = (e 1).stageEquiv A
    simpa only [e.apply_symm_apply, map_one, HyperplaneGT.DiagramAut.stageEquiv_one,
      LinearEquiv.one_eq_refl] using DiagramExamples.zeroDimensionSwap_stage (ZMod 2) A
  · intro A hmem
    have htarget := (DiagramAut.mem_stageKernel _ _ _ _ _).mp hmem |>.2
    have htarget' := (degreeOneDiagramEquiv_target_eq_iff T
      (DiagramExamples.binarySystem 0) ({0} : Set (ZMod 2)) (e.symm swap) 1).mpr htarget
    change (e (e.symm swap)).targetEquiv = (e 1).targetEquiv at htarget'
    have hswap : swap.targetEquiv = 1 := by
      simpa only [e.apply_symm_apply, map_one, HyperplaneGT.DiagramAut.targetEquiv_one,
        LinearEquiv.one_eq_refl] using htarget'
    apply DiagramExamples.zeroDimensionSwap_ne_one
    exact HyperplaneGT.DiagramAut.ext
      (fun A ↦ DiagramExamples.zeroDimensionSwap_stage (ZMod 2) A) hswap

/-- The existing algebraic zero theory evaluated on affine global sections. -/
def actualZeroTheory : Geometric.OrdinaryTheory.{u, 0, 0, 0}
    (Geometric.SmoothDomain.aff k) Sanity.zeroWeight.{0, 0} :=
  Geometric.OrdinaryTheory.ofAlgebraic (Sanity.zeroTheory k)

/-- The actual quadratic diagram is trivial over zero coefficients, in dimension zero. -/
theorem zero_quadratic_eq_one
    (g : DiagramAut (actualZeroTheory k) (fullCofinalSystem k k 0) {0}) : g = 1 := by
  apply (degreeOneDiagramContinuousEquiv (actualZeroTheory k)
    (fullCofinalSystem k k 0) {0}).injective
  exact Subsingleton.elim _ _

/-- The complete actual graded diagram is likewise trivial over zero coefficients. -/
theorem zero_graded_eq_one
    (g : GradedDiagramAut (actualZeroTheory k) (fullCofinalSystem k k 0) {0}) : g = 1 := by
  apply (gradedDiagramContinuousEquiv (actualZeroTheory k)
    (fullCofinalSystem k k 0) {0}).injective
  exact Subsingleton.elim _ _

/-- The actual stage-and-target kernel is the whole zero-coefficient group. -/
theorem zero_stageKernel_eq_top (A : (fullCofinalSystem k k 0).Stage) :
    DiagramAut.stageKernel (actualZeroTheory k) (fullCofinalSystem k k 0) {0} A = ⊤ := by
  ext g
  simp only [DiagramAut.mem_stageKernel, Subgroup.mem_top, iff_true]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Bare quotient inverse cancellation works on the actual zero-coefficient quotient. -/
theorem zero_quotient_roundtrip
    (x : DiagramAut (actualZeroTheory k) (fullCofinalSystem k k 0) {0} ⧸
      DiagramAut.scalarSubgroup (actualZeroTheory k) (fullCofinalSystem k k 0) {0}) :
    (DiagramAut.scalarQuotientContinuousComparison (actualZeroTheory k)
      (fullCofinalSystem k k 0) {0}).symm
        (DiagramAut.scalarQuotientContinuousComparison (actualZeroTheory k)
          (fullCofinalSystem k k 0) {0} x) = x := by simp

/-- Bare inverse cancellation also works for the full graded scalar quotient. -/
theorem zero_graded_quotient_roundtrip
    (x : GradedDiagramAut (actualZeroTheory k) (fullCofinalSystem k k 0) {0} ⧸
      GradedDiagramAut.scalarSubgroup (actualZeroTheory k) (fullCofinalSystem k k 0) {0}) :
    (GradedDiagramAut.scalarQuotientContinuousComparison (actualZeroTheory k)
      (fullCofinalSystem k k 0) {0}).symm
        (GradedDiagramAut.scalarQuotientContinuousComparison (actualZeroTheory k)
          (fullCofinalSystem k k 0) {0} x) = x := by simp

/-- A deliberate diagram scope and an unrelated field topology do not replace global Krull. -/
theorem preserves_global_krull (k₀ : Type*) [Field k₀] [Algebra k₀ k]
    [t : TopologicalSpace k] :
    (inferInstance : TopologicalSpace k) = t ∧
      (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := ⟨rfl, rfl⟩

end OrlikSolomon.HyperplaneGT.Cohomology.TopologyExamples

universe v r b₁ b₂ b₃ h₁ h₂ h₃

namespace OrlikSolomon.HyperplaneGT.Cohomology.RealizationTopologyExamples

open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R]
  {B₁ : Type b₁} [CommRing B₁] [Algebra R B₁]
  {ℬ₁ : ℤ → Submodule R B₁} [GradedAlgebra ℬ₁] {D₁ : Geometric.SmoothDomain k}
  {B₂ : Type b₂} [CommRing B₂] [Algebra R B₂]
  {ℬ₂ : ℤ → Submodule R B₂} [GradedAlgebra ℬ₂] {D₂ : Geometric.SmoothDomain k}
  {B₃ : Type b₃} [CommRing B₃] [Algebra R B₃]
  {ℬ₃ : ℤ → Submodule R B₃} [GradedAlgebra ℬ₃] {D₃ : Geometric.SmoothDomain k}
  (T₁ : Geometric.OrdinaryTheory.{u, r, b₁, h₁} D₁ ℬ₁)
  (T₂ : Geometric.OrdinaryTheory.{u, r, b₂, h₂} D₂ ℬ₂)
  (T₃ : Geometric.OrdinaryTheory.{u, r, b₃, h₃} D₃ ℬ₃)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)


/-- Both bare quadratic inverse cancellations retain independently sized realizations. -/
theorem quadratic_realization_roundtrips (x : DiagramAut T₁ C S) (y : DiagramAut T₂ C S) :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).symm (realizationQuadraticContinuousEquiv T₁
      T₂ C S x) = x ∧
      realizationQuadraticContinuousEquiv T₁ T₂ C S ((realizationQuadraticContinuousEquiv T₁ T₂ C
        S).symm y) = y := by
  simp

/-- Both bare graded inverse cancellations retain independently sized realizations. -/
theorem graded_realization_roundtrips (x : GradedDiagramAut T₁ C S) (y : GradedDiagramAut T₂ C S) :
    (realizationGradedContinuousEquiv T₁ T₂ C S).symm (realizationGradedContinuousEquiv T₁ T₂ C S
      x) = x ∧
      realizationGradedContinuousEquiv T₁ T₂ C S ((realizationGradedContinuousEquiv T₁ T₂ C
        S).symm y) = y := by
  simp

/-- Both bare quadratic quotient inverse cancellations retain independently sized realizations. -/
theorem quadratic_quotient_realization_roundtrips (x : DiagramAut T₁ C S ⧸
  DiagramAut.scalarSubgroup T₁ C S) (y : DiagramAut T₂ C S ⧸ DiagramAut.scalarSubgroup T₂ C S) :
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).symm
      (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S x) = x ∧
      realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S
        ((realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).symm y) = y := by
  simp

/-- Both bare graded quotient inverse cancellations retain independently sized realizations. -/
theorem graded_quotient_realization_roundtrips (x : GradedDiagramAut T₁ C S ⧸
  GradedDiagramAut.scalarSubgroup T₁ C S) (y : GradedDiagramAut T₂ C S ⧸
  GradedDiagramAut.scalarSubgroup T₂ C S) :
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).symm
      (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S x) = x ∧
      realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S
        ((realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).symm y) = y := by
  simp

/-- All four maps satisfy the same cocycle for three independent eligible realizations. -/
theorem independent_realization_cocycles :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S).trans
        (realizationQuadraticContinuousEquiv T₂ T₃ C S) =
      realizationQuadraticContinuousEquiv T₁ T₃ C S ∧
    (realizationGradedContinuousEquiv T₁ T₂ C S).trans
        (realizationGradedContinuousEquiv T₂ T₃ C S) =
      realizationGradedContinuousEquiv T₁ T₃ C S ∧
    (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S).trans
        (realizationQuadraticScalarQuotientContinuousEquiv T₂ T₃ C S) =
      realizationQuadraticScalarQuotientContinuousEquiv T₁ T₃ C S ∧
    (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S).trans
        (realizationGradedScalarQuotientContinuousEquiv T₂ T₃ C S) =
      realizationGradedScalarQuotientContinuousEquiv T₁ T₃ C S :=
  ⟨realizationQuadraticContinuousEquiv_trans T₁ T₂ T₃ C S,
    realizationGradedContinuousEquiv_trans T₁ T₂ T₃ C S,
    realizationQuadraticScalarQuotientContinuousEquiv_trans T₁ T₂ T₃ C S,
    realizationGradedScalarQuotientContinuousEquiv_trans T₁ T₂ T₃ C S⟩

/-- Entire actual stage and common-target actions are conjugated, not only generators. -/
theorem whole_realization_components (g : DiagramAut T₁ C S)
    (f : GradedDiagramAut T₁ C S) (A : C.Stage)
    (x : degreeOne T₁ A.val.val) (t : degreeOne T₁ (twoPunctureArrangement k))
    (y : diagonal T₁ (D₁.complement A.val.val))
    (z : diagonal T₁ (schemeMarkingTarget D₁)) :
    (realizationQuadraticContinuousEquiv T₁ T₂ C S g).stageEquiv A
        (realizationDegreeOneEquiv T₁ T₂ A.val.val x) =
      realizationDegreeOneEquiv T₁ T₂ A.val.val (g.stageEquiv A x) ∧
    (realizationQuadraticContinuousEquiv T₁ T₂ C S g).targetEquiv
        (realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) t) =
      realizationDegreeOneEquiv T₁ T₂ (twoPunctureArrangement k) (g.targetEquiv t) ∧
    (realizationGradedContinuousEquiv T₁ T₂ C S f).stageEquiv A
        (realizationStageEquiv T₁ T₂ A.val.val y) =
      realizationStageEquiv T₁ T₂ A.val.val (f.stageEquiv A y) ∧
    (realizationGradedContinuousEquiv T₁ T₂ C S f).targetEquiv
        (realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) z) =
      realizationStageEquiv T₁ T₂ (twoPunctureArrangement k) (f.targetEquiv z) :=
  ⟨realizationQuadraticContinuousEquiv_stage T₁ T₂ C S g A x,
    realizationQuadraticContinuousEquiv_target T₁ T₂ C S g t,
    realizationGradedContinuousEquiv_stage T₁ T₂ C S f A y,
    realizationGradedContinuousEquiv_target T₁ T₂ C S f z⟩

/-- The actual zero theory realizes all four comparisons in dimension zero, with no
nonzero-theory claim or classification hypothesis. -/
theorem actual_zero_theory_comparisons (k : Type u) [Field k] :
    let T := TopologyExamples.actualZeroTheory k
    let C := fullCofinalSystem k k 0
    realizationQuadraticContinuousEquiv T T C {0} = ContinuousMulEquiv.refl _ ∧
      realizationGradedContinuousEquiv T T C {0} = ContinuousMulEquiv.refl _ ∧
      realizationQuadraticScalarQuotientContinuousEquiv T T C {0} =
        ContinuousMulEquiv.refl _ ∧
      realizationGradedScalarQuotientContinuousEquiv T T C {0} =
        ContinuousMulEquiv.refl _ :=
  ⟨realizationQuadraticContinuousEquiv_refl _ _ _,
    realizationGradedContinuousEquiv_refl _ _ _,
    realizationQuadraticScalarQuotientContinuousEquiv_refl _ _ _,
    realizationGradedScalarQuotientContinuousEquiv_refl _ _ _⟩

/-- For two supplied binary theories, canonical realization comparison preserves the
nonidentity common target invisible at every dimension-zero stage. This is conditional on
both eligible theories; it constructs no nonzero characteristic-two cohomology theory. -/
theorem target_swap_survives_realization
    {W₁ : Type b₁} [CommRing W₁] [Algebra (ZMod 2) W₁]
    {𝒲₁ : ℤ → Submodule (ZMod 2) W₁} [GradedAlgebra 𝒲₁]
    {E₁ : Geometric.SmoothDomain (ZMod 2)}
    {W₂ : Type b₂} [CommRing W₂] [Algebra (ZMod 2) W₂]
    {𝒲₂ : ℤ → Submodule (ZMod 2) W₂} [GradedAlgebra 𝒲₂]
    {E₂ : Geometric.SmoothDomain (ZMod 2)}
    (U₁ : Geometric.OrdinaryTheory.{0, 0, b₁, h₁} E₁ 𝒲₁)
    (U₂ : Geometric.OrdinaryTheory.{0, 0, b₂, h₂} E₂ 𝒲₂) :
    let C := DiagramExamples.binarySystem 0
    let S : Set (ZMod 2) := {0}
    let e := realizationQuadraticContinuousEquiv U₁ U₂ C S
    ∃ g : DiagramAut U₁ C S,
      (∀ A, g.stageEquiv A = 1) ∧ (∀ A, (e g).stageEquiv A = 1) ∧
      (∀ A, g ∉ DiagramAut.stageKernel U₁ C S A) ∧
      (∀ A, e g ∉ DiagramAut.stageKernel U₂ C S A) := by
  dsimp only
  let C := DiagramExamples.binarySystem 0
  let S : Set (ZMod 2) := {0}
  obtain ⟨g, hg, hk⟩ := TopologyExamples.exists_target_detected_at_dimension_zero U₁
  refine ⟨g, hg, ?_, hk, ?_⟩
  · intro A
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (realizationDegreeOneEquiv U₁ U₂ A.val.val).surjective y
    rw [realizationQuadraticContinuousEquiv_stage, hg A]
    rfl
  · intro A hmem
    have ht := ((DiagramAut.mem_stageKernel U₂ C S A
      (realizationQuadraticContinuousEquiv U₁ U₂ C S g)).mp hmem).2
    apply hk A
    rw [DiagramAut.mem_stageKernel]
    refine ⟨hg A, ?_⟩
    apply LinearEquiv.ext
    intro x
    apply (realizationDegreeOneEquiv U₁ U₂ (twoPunctureArrangement (ZMod 2))).injective
    have h := realizationQuadraticContinuousEquiv_target U₁ U₂ C S g x
    rw [ht] at h
    exact h.symm

end OrlikSolomon.HyperplaneGT.Cohomology.RealizationTopologyExamples
