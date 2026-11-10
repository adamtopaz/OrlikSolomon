/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Diagram
public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Topology.Classification.Quadratic
public import OrlikSolomon.Examples.HyperplaneGT.LocalClassification
public import OrlikSolomon.Examples.HyperplaneGT.DomainClassification
public import Mathlib.FieldTheory.KrullTopology

/-!
# Coefficients and the common target in finite-stage topology

The binary dimension-zero fixture has identity at every stage and a nonidentity common
target. The stage-and-target neighborhood basis excludes this automorphism, so a topology
that silently discarded the target would fail this consumer. Over the zero coefficient
ring, both actual pure diagram kernel families are the full subgroups.

The quadratic reconstruction consumers retain the exact local/domain maps and test both
continuity directions, cancellation, scope isolation, the kernel preimage and whole marking
squares. Existing actual scalar-two/dual-three, nilpotent-local, complex-conjugation and
integer-domain fixtures are consumed through the new continuous equivalences. Pure
zero-coefficient and dimension-zero checks do not extend classification beyond its hypotheses.

Blueprint: T01 (`def:t01`), T02 (`lem:t02`) and T09 (`thm:t09`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.TopologyExamples

open Filter Topology DiagramExamples
open scoped FiniteStageTopology

/-- All stage components of the binary dimension-zero fixture are identity. The common
component is still nontrivial, even though no markings exist in that dimension. -/
theorem binary_zeroDimension_all_stages :
    (∀ 𝒜 : (binarySystem 0).Stage,
      (zeroDimensionSwap (ZMod 2)).stageEquiv 𝒜 = 1) ∧
      zeroDimensionSwap (ZMod 2) ≠ 1 :=
  ⟨fun 𝒜 ↦ zeroDimensionSwap_stage (ZMod 2) 𝒜, zeroDimensionSwap_ne_one⟩

/-- A genuine identity neighborhood excludes a nonidentity target swap even when it acts as
identity at every selected stage. In particular the target test cannot be removed. -/
theorem binary_zeroDimension_target_neighborhood (𝒜 : (binarySystem 0).Stage) :
    (DiagramAut.stageKernel (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2)) 𝒜 : Set _) ∈
        𝓝 (1 : DiagramAut (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2))) ∧
      zeroDimensionSwap (ZMod 2) ∉
        DiagramAut.stageKernel (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2)) 𝒜 := by
  refine ⟨(DiagramAut.nhds_one_stageBasis _ _ _).mem_of_mem trivial, ?_⟩
  intro hmem
  have ht := (DiagramAut.mem_stageKernel _ _ _ _ _).mp hmem |>.2
  apply zeroDimensionSwap_ne_one
  exact DiagramAut.ext (fun ℬ ↦ zeroDimensionSwap_stage (ZMod 2) ℬ) ht

/-- Both pure kernel families retain the zero coefficient ring and its original carriers. -/
theorem zeroRing_stageKernels (𝒜 : (binarySystem 1).Stage) :
    DiagramAut.stageKernel (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2)) 𝒜 = ⊤ ∧
      GradedDiagramAut.stageKernel (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2)) 𝒜 = ⊤ := by
  constructor
  · apply top_unique
    intro g _
    rw [zeroRing_aut_eq_one g]
    exact Subgroup.one_mem _
  · apply top_unique
    intro g _
    rw [zeroRing_graded_aut_eq_one g]
    exact Subgroup.one_mem _

/-- Opening the finite-stage scope does not replace the existing global Galois topology. -/
theorem finiteStageScope_krull (k₀ k : Type*) [Field k₀] [Field k] [Algebra k₀ k] :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

end OrlikSolomon.HyperplaneGT.TopologyExamples

namespace OrlikSolomon.HyperplaneGT.QuadraticTopologyExamples

open Filter Topology
open scoped DiscreteCoefficientUnits FiniteStageTopology

universe u v r

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} {R : Type r} [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Importing the classifiers and selecting discrete units leaves global Krull unchanged. -/
theorem global_krull_preserved :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

section Pointwise

open scoped GaloisPointwise

/-- A competing coefficient topology is retained, while the parameter units are explicitly
and deliberately discrete. The product topology is literal and independent of C. -/
theorem competing_coefficient_topology [t : TopologicalSpace R] :
    (inferInstance : TopologicalSpace R) = t ∧
      (inferInstance : TopologicalSpace Rˣ) = discreteUnitsTopology R ∧
      (inferInstance : TopologicalSpace (Rˣ × (k ≃ₐ[k₀] k))) =
        coefficientGaloisPointwiseTopology R k₀ k := ⟨rfl, rfl, rfl⟩

/-- Both bare local inverse cancellations survive the explicit forward and inverse APIs. -/
theorem local_cancellation [IsLocalRing R] (p : Rˣ × (k ≃ₐ[k₀] k))
    (g : DiagramAut R C S) :
    (quadraticAutContinuousEquiv R C S hS hgen hn).symm
        (quadraticAutContinuousEquiv R C S hS hgen hn p) = p ∧
      quadraticAutContinuousEquiv R C S hS hgen hn
        ((quadraticAutContinuousEquiv R C S hS hgen hn).symm g) = g := by simp

/-- Both domain cancellations hold without a localness assumption. -/
theorem domain_cancellation [IsDomain R] (p : Rˣ × (k ≃ₐ[k₀] k))
    (g : DiagramAut R C S) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn).symm
        (coefficientDomainAutContinuousEquiv R C S hS hgen hn p) = p ∧
      coefficientDomainAutContinuousEquiv R C S hS hgen hn
        ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).symm g) = g := by simp

/-- The public preimage equation includes the actual common-target identity test. -/
theorem local_kernel_membership [IsLocalRing R] (u : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) :
    quadraticAutContinuousEquiv R C S hS hgen hn (u, σ) ∈
        DiagramAut.stageKernel R C S A ↔ u = 1 ∧ σ ∈ C.galoisStageKernel A := by
  change (u, σ) ∈ (quadraticAutEquiv R C S hS hgen hn) ⁻¹'
    (DiagramAut.stageKernel R C S A : Set _) ↔ _
  rw [quadraticAutEquiv_preimage_stageKernel]
  rfl

/-- The upgraded family still commutes with every actual whole marking map, using the
single common target and its primal scalar. -/
theorem whole_marking_square [IsLocalRing R] (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (m : Marking S n) (hm : m.Available A.val.val) (x : Fin 2 →₀ R) :
    (quadraticAutContinuousEquiv R C S hS hgen hn (u, σ)).stageEquiv A
        (m.basisMap R hm x) = m.basisMap R hm ((u : R) • x) := by
  rw [quadraticAutContinuousEquiv_apply]
  exact quadraticAutEquiv_marking R C S hS hgen hn u σ A m hm x

/-- Actual local/domain continuous equivalences agree on the overlap. -/
theorem local_domain_overlap [IsLocalRing R] [IsDomain R] :
    coefficientDomainAutContinuousEquiv R C S hS hgen hn =
      quadraticAutContinuousEquiv R C S hS hgen hn := by
  rw [coefficientDomainAutContinuousEquiv_eq_local]

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- The genuine scalar-two/dual-three fixture uses the exact topological classifier. -/
theorem scalar_two_inverse_three :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let e := quadraticAutContinuousEquiv (ZMod 5) C S
      (by simp [S]) (Subsingleton.elim _ _) (by decide)
    let g := e (DualExamples.scalarTwoUnit, 1)
    let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
    e.symm g = (DualExamples.scalarTwoUnit, 1) ∧
      g.universalEquiv (Finsupp.single H 1) H = 2 ∧
      DiagramAut.dualAction g (Finsupp.lapply H) (Finsupp.single H 1) = 3 ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 2 ∧ (3 : ZMod 5) ≠ 2 :=
  LocalClassificationExamples.scalar_two_inverse_three

/-- A nonfield local coefficient ring retains its nonzero nilpotent in the common target. -/
theorem mod_four_nilpotent_target :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let e := quadraticAutContinuousEquiv (ZMod 4) C S
      (by simp [S]) (Subsingleton.elim _ _) (by decide)
    let g := e (IncidenceExamples.scalarThreeUnit, 1)
    e.symm g = (IncidenceExamples.scalarThreeUnit, 1) ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      g.targetEquiv (Finsupp.single 0 2) 0 = 2 ∧
      (3 : ZMod 4) ≠ 1 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4)^2 = 0 :=
  LocalClassificationExamples.mod_four_nilpotent_target

/-- A genuinely nonidentity geometric field automorphism occurs independently of the
nonfield coefficient ring, with the original scalar target component. -/
theorem conjugation_mod_four :
    let C := fullCofinalSystem ℝ ℂ 2
    let S : Set ℝ := Set.univ
    let e := quadraticAutContinuousEquiv (ZMod 4) C S
      (by simp [S]) (by simp [S]) (by decide)
    let g := e (IncidenceExamples.scalarThreeUnit, Complex.conjAe)
    e.symm g = (IncidenceExamples.scalarThreeUnit, Complex.conjAe) ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) g
        Complex.I = -Complex.I ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) g ≠ 1 ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 :=
  LocalClassificationExamples.conjugation_mod_four

/-- Integer coefficients use the domain upgrade without a local coefficient assumption. -/
theorem integer_scalar_nonidentity :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    let g := coefficientDomainAutContinuousEquiv ℤ C S (by simp [S]) hgen (by decide)
      (-1, 1)
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 = -1 ∧ g ≠ 1 :=
  DomainClassificationExamples.integer_scalar_nonidentity

/-- The parameter topology still exists for zero coefficients and arbitrary geometry;
this does not apply classification outside its nonzero coefficient hypothesis. -/
theorem zero_ring_parameter_topology :
    (inferInstance : TopologicalSpace ((ZMod 1)ˣ × (k ≃ₐ[k₀] k))) =
      coefficientGaloisPointwiseTopology (ZMod 1) k₀ k := rfl

/-- In dimension zero, the raw kernel equation still detects a nonidentity target scalar. -/
theorem dimension_zero_retained_target
    (A : (fullCofinalSystem (ZMod 2) (ZMod 2) 0).Stage) :
    scalarQuadraticAut (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅
          DualExamples.scalarTwoUnit *
        galoisQuadraticAut (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅ 1 ∉
      DiagramAut.stageKernel (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅ A := by
  intro h
  change (DualExamples.scalarTwoUnit, 1) ∈
    (fun p : (ZMod 5)ˣ × ((ZMod 2) ≃ₐ[ZMod 2] ZMod 2) ↦
      scalarQuadraticAut _ _ ∅ p.1 * galoisQuadraticAut _ _ ∅ p.2) ⁻¹'
        (DiagramAut.stageKernel (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅ A :
          Set (DiagramAut (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅)) at h
  rw [scalarGalois_preimage_stageKernel] at h
  have he := congrArg (fun u : (ZMod 5)ˣ ↦ (u : ZMod 5)) h.1
  exact (by decide : (2 : ZMod 5) ≠ 1) (by simpa [DualExamples.scalarTwoUnit] using he)

end Pointwise

/-- The explicit-K local wrapper preserves both bare inverse cancellations. -/
theorem local_krull_cancellation [IsLocalRing R] (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut R C S) :
    (quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).symm
        (quadraticAutKrullContinuousEquiv R C S hS hgen hn hK p) = p ∧
      quadraticAutKrullContinuousEquiv R C S hS hgen hn hK
        ((quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).symm g) = g := by simp

/-- The explicit-K domain wrapper preserves both cancellations without localness. -/
theorem domain_krull_cancellation [IsDomain R] (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut R C S) :
    (coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).symm
        (coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK p) = p ∧
      coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK
        ((coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).symm g) = g := by simp

/-- The algebraic local wrapper has both actual inverse laws without a supplied K witness. -/
theorem local_algebraic_cancellation [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut R C S) :
    (quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm
        (quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p) = p ∧
      quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
        ((quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g) = g := by simp

/-- The algebraic domain wrapper has both inverse laws without a local coefficient assumption. -/
theorem domain_algebraic_cancellation [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut R C S) :
    (coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm
        (coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p) = p ∧
      coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
        ((coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g) = g := by
  simp

end OrlikSolomon.HyperplaneGT.QuadraticTopologyExamples
