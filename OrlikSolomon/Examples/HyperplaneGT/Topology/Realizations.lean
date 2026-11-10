/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Coefficients
public import OrlikSolomon.Examples.Sanity
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Comparison
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Cofinal
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
import Mathlib.Tactic.NormNum

/-!
# Actual-theory finite-stage topology consumers

The actual diagram and scalar quotient comparisons retain arbitrary supplied theories and
the original common target. The existing zero theory supplies concrete zero-coefficient
and dimension-zero consumers, without a nontriviality hypothesis. This is a consistency
fixture, not a test of the substantive cohomology axioms or a new nonzero realization.

The default field-automorphism topology remains Mathlib's actual Krull topology, also
when the deliberate finite-stage scope and an unrelated geometric-field topology are used.

The appended ordinary consumers use the constructed characteristic-zero de Rham theory.
They retain a genuinely nontrivial target action in dimension zero, both twist and quotient
inverses, literal cofinal restriction, and a nontrivial complex-conjugation quotient class.
They do not assert the final T17 topological classification.

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

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham.TopologyExamples

open Filter Topology
open scoped FiniteStageTopology

universe v

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

/-- Both ordinary twists retain bare inverse cancellation on every original group. -/
theorem ordinary_twist_cancellations (g : DiagramAut C S) (h : GradedDiagramAut C S)
    (g' : Cohomology.DiagramAut Tdr C S) (h' : Cohomology.GradedDiagramAut Tdr C S) :
    (quadraticTwistContinuousEquiv C S).symm (quadraticTwistContinuousEquiv C S g) = g ∧
      quadraticTwistContinuousEquiv C S ((quadraticTwistContinuousEquiv C S).symm g') = g' ∧
      (gradedTwistContinuousEquiv C S).symm (gradedTwistContinuousEquiv C S h) = h ∧
      gradedTwistContinuousEquiv C S ((gradedTwistContinuousEquiv C S).symm h') = h' := by simp

/-- Both literal Mathlib quotient twists retain bare cancellation, in both directions. -/
theorem ordinary_quotient_twist_cancellations
    (g : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S)
    (h : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S)
    (g' : Cohomology.DiagramAut Tdr C S ⧸ Cohomology.DiagramAut.scalarSubgroup Tdr C S)
    (h' : Cohomology.GradedDiagramAut Tdr C S ⧸
      Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S) :
    (DiagramAut.scalarQuotientTwistContinuousEquiv C S).symm
        (DiagramAut.scalarQuotientTwistContinuousEquiv C S g) = g ∧
      DiagramAut.scalarQuotientTwistContinuousEquiv C S
        ((DiagramAut.scalarQuotientTwistContinuousEquiv C S).symm g') = g' ∧
      (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).symm
        (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S h) = h ∧
      GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S
        ((GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).symm h') = h' := by simp

/-- The new quotient twists send representatives through the exact old ordinary twists. -/
theorem ordinary_quotient_representatives (g : DiagramAut C S) (h : GradedDiagramAut C S) :
    DiagramAut.scalarQuotientTwistContinuousEquiv C S (DiagramAut.scalarQuotientMap C S g) =
        Cohomology.DiagramAut.scalarQuotientMap Tdr C S (quadraticTwistEquiv C S g) ∧
      GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S
        (GradedDiagramAut.scalarQuotientMap C S h) =
          Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S (gradedTwistEquiv C S h) :=
  ⟨DiagramAut.scalarQuotientTwistContinuousEquiv_map C S g,
    GradedDiagramAut.scalarQuotientTwistContinuousEquiv_map C S h⟩

/-- Literal ordinary restriction chooses complete selected stages and preserves the target,
without any marking, dimension or algebraicity hypothesis. -/
theorem ordinary_cofinal_components (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut C S) (h : GradedDiagramAut C S) (A : C'.Stage) :
    (DiagramAut.restrictStages C C' S hC g).stageEquiv A =
        g.stageEquiv (CofinalSystem.stageInclusion hC A) ∧
      (DiagramAut.restrictStages C C' S hC g).targetEquiv = g.targetEquiv ∧
      (GradedDiagramAut.restrictStages C C' S hC h).stageEquiv A =
        h.stageEquiv (CofinalSystem.stageInclusion hC A) ∧
      (GradedDiagramAut.restrictStages C C' S hC h).targetEquiv = h.targetEquiv :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The new algebraic cofinal wrappers retain both cancellation laws with precisely the
old hypotheses; this is not a claim about a final ordinary cofinal homeomorphism. -/
theorem ordinary_cofinal_cancellations (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut C S) (g' : DiagramAut C' S)
    (h : GradedDiagramAut C S) (h' : GradedDiagramAut C' S) :
    (cofinalRestrictionEquiv C C' S hC hS hgen hn).symm
        (cofinalRestrictionEquiv C C' S hC hS hgen hn g) = g ∧
      cofinalRestrictionEquiv C C' S hC hS hgen hn
        ((cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g') = g' ∧
      (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm
        (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn h) = h ∧
      gradedCofinalRestrictionEquiv C C' S hC hS hgen hn
        ((gradedCofinalRestrictionEquiv C C' S hC hS hgen hn).symm h') = h' := by simp

omit [Field k₀] [Algebra k₀ k] in
private def pureZeroTargetSwap : HyperplaneGT.DiagramAut k (fullCofinalSystem k k 0) {0} :=
  HyperplaneGT.DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.refl k _)
    (Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1))
    (by intro A; simp) (by intro A B hAB; rfl)
    (by intro A w hw; exact (IsEmpty.false w).elim)

omit [Field k₀] [Algebra k₀ k] in
/-- The constructed ordinary characteristic-zero theory has a dimension-zero diagram
whose original target is invisible at every stage and detected by every actual kernel.
No supplied cohomology theory or out-of-range reconstruction theorem is used. -/
theorem ordinary_zero_target_detected :
    ∃ g : DiagramAut (fullCofinalSystem k k 0) ({0} : Set k),
      (∀ A, g.stageEquiv A = 1) ∧
        ∀ A, g ∉ DiagramAut.stageKernel (fullCofinalSystem k k 0) ({0} : Set k) A := by
  let C₀ := fullCofinalSystem k k 0
  let S₀ : Set k := {0}
  let e := (quadraticTwistContinuousEquiv C₀ S₀).trans
    (Cohomology.degreeOneDiagramContinuousEquiv Tdr C₀ S₀)
  let swap := pureZeroTargetSwap (k := k)
  have hstage (A : C₀.Stage) : swap.stageEquiv A = 1 := rfl
  have hne : swap.targetEquiv ≠ 1 := by
    intro heq
    have hz := congrArg (fun f : (Fin 2 →₀ k) ≃ₗ[k] (Fin 2 →₀ k) ↦
      f (Finsupp.single 0 1) 1) heq
    change (Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1)
      (Finsupp.single 0 (1 : k))) 1 = (Finsupp.single 0 (1 : k)) 1 at hz
    simp at hz
  refine ⟨e.symm swap, ?_, ?_⟩
  · intro A
    apply (quadraticTwistEquiv_stage_eq_iff C₀ S₀ _ 1 A).mp
    rw [map_one]
    apply (Cohomology.degreeOneDiagramEquiv_stage_eq_iff Tdr C₀ S₀ _ 1 A).mp
    rw [map_one]
    change (e (e.symm swap)).stageEquiv A = 1
    simpa only [e.apply_symm_apply] using hstage A
  · intro A hmem
    have ha := (Set.ext_iff.mp (quadraticTwistEquiv_preimage_stageKernel C₀ S₀ A)
      (e.symm swap)).mpr hmem
    have hb := (Set.ext_iff.mp
      (Cohomology.degreeOneDiagramEquiv_preimage_stageKernel Tdr C₀ S₀ A)
        (quadraticTwistEquiv C₀ S₀ (e.symm swap))).mpr ha
    change e (e.symm swap) ∈ HyperplaneGT.DiagramAut.stageKernel k C₀ S₀ A at hb
    have hs : swap ∈ HyperplaneGT.DiagramAut.stageKernel k C₀ S₀ A :=
      (e.apply_symm_apply swap) ▸ hb
    exact hne ((HyperplaneGT.DiagramAut.mem_stageKernel k C₀ S₀ A swap).mp hs).2

/-- Complex conjugation supplies a genuine nontrivial ordinary scalar-quotient class.
The fixture uses all real markings, their true field generation and dimension two. -/
theorem ordinary_conjugation_class_ne_one :
    DiagramAut.scalarQuotientSection (fullCofinalSystem ℝ ℂ 2) Set.univ Complex.conjAe ≠ 1 := by
  let C := fullCofinalSystem ℝ ℂ 2
  have hS : (0 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ _
  have hgen : Subfield.closure (Set.univ : Set ℝ) = ⊤ := by simp
  let e := DiagramAut.scalarQuotientEquiv C Set.univ hS hgen (by decide)
  have hs : e (DiagramAut.scalarQuotientSection C Set.univ Complex.conjAe) =
      Complex.conjAe := DiagramAut.scalarQuotientEquiv_section C Set.univ hS hgen
        (by decide) Complex.conjAe
  intro heq
  have hc : Complex.conjAe = (1 : ℂ ≃ₐ[ℝ] ℂ) := hs.symm.trans
    ((congrArg e heq).trans (map_one e))
  have hi := congrArg (fun f : ℂ ≃ₐ[ℝ] ℂ ↦ (f Complex.I).im) hc
  norm_num at hi

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham.TopologyExamples
