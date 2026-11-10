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

Blueprint: acceptance consumers for T01–T02 and T14 (`def:t01`, `lem:t02`, `thm:t14`).
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
