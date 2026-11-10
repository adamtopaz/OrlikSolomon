/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Diagram
public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Topology.Classification
public import OrlikSolomon.Examples.HyperplaneGT.LocalClassification
public import OrlikSolomon.Examples.HyperplaneGT.DomainClassification
public import OrlikSolomon.Examples.HyperplaneGT.GradedClassification
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

The graded consumers retain all sixteen bare inverse cancellations, whole-degree actions,
literal restriction and actual full marking/inclusion squares. Concrete fixtures use the
same original scalar and Galois families through the full-algebra homeomorphisms.

Blueprint: T01 (`def:t01`), T02 (`lem:t02`), T09 (`thm:t09`) and T10 (`cor:t10`).
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

namespace OrlikSolomon.HyperplaneGT.GradedTopologyExamples

open scoped DiscreteCoefficientUnits FiniteStageTopology

universe u v r

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} {R : Type r} [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Importing the optional classification facade keeps actual global Krull inference. -/
theorem global_krull_preserved :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

/-- The exact local restriction retains both bare cancellations without any field condition.
-/
theorem local_restriction_cancellation [IsLocalRing R]
    (g : GradedDiagramAut R C S) (q : DiagramAut R C S) :
    (gradedAutContinuousEquiv R C S hS hgen hn).symm
        (gradedAutContinuousEquiv R C S hS hgen hn g) = g ∧
      gradedAutContinuousEquiv R C S hS hgen hn
        ((gradedAutContinuousEquiv R C S hS hgen hn).symm q) = q := by simp

/-- The exact domain restriction retains both bare cancellations without any field condition.
-/
theorem domain_restriction_cancellation [IsDomain R]
    (g : GradedDiagramAut R C S) (q : DiagramAut R C S) :
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm
        (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn g) = g ∧
      coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn
        ((coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm q) = q := by simp

section Pointwise

open scoped GaloisPointwise

/-- The local product classifier retains both ordinary inverse cancellations. -/
theorem local_classification_cancellation [IsLocalRing R]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn).symm
        (gradedClassificationContinuousEquiv R C S hS hgen hn p) = p ∧
      gradedClassificationContinuousEquiv R C S hS hgen hn
        ((gradedClassificationContinuousEquiv R C S hS hgen hn).symm g) = g := by simp

/-- The domain product classifier retains both ordinary inverse cancellations. -/
theorem domain_classification_cancellation [IsDomain R]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).symm
        (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn p) = p ∧
      coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn
        ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).symm g) = g := by
          simp

/-- Whole homogeneous components use the scalar degree power at a covariant Galois label;
the common target uses the same power, including degree zero. -/
theorem whole_degree_and_target [IsLocalRing R] (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q)
    (y : OSAlgebra R (twoPunctureArrangement k))
    (hy : y ∈ OSAlgebra.degree R (twoPunctureArrangement k) q) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A x =
        (a : R) ^ q • galoisOSAlgebraEquiv R A.val σ x ∧
      (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv y =
        (a : R) ^ q • y :=
  ⟨gradedClassificationContinuousEquiv_stage_apply_of_mem_degree R C S hS hgen hn a σ A q x hx,
    gradedClassificationContinuousEquiv_target_apply_of_mem_degree R C S hS hgen hn a σ q y hy⟩

/-- The actual whole-algebra marking and inclusion equations retain the same single target.
-/
theorem full_arrow_squares [IsDomain R] (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    {A B : C.Stage} (h : A ≤ B) (w : Marking S n) (hw : w.Available A.val.val) :
    let e := coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)
    (e.stageEquiv B).toAlgHom.comp (OSAlgebra.map R h) =
        (OSAlgebra.map R h).comp (e.stageEquiv A).toAlgHom ∧
      (e.stageEquiv A).toAlgHom.comp (w.osMap R hw) =
        (w.osMap R hw).comp e.targetEquiv.toAlgHom :=
  ⟨GradedDiagramAut.inclusion_naturality _ h, GradedDiagramAut.marking_naturality _ A w hw⟩

/-- The topological restriction square is an equality of bundled maps, including both targets.
-/
theorem literal_restriction_square [IsDomain R] :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).trans
        (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn) =
      coefficientDomainAutContinuousEquiv R C S hS hgen hn :=
  coefficientDomainGradedClassificationContinuousEquiv_trans_restriction R C S hS hgen hn

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- A genuine full scalar-two family restricts to the existing primal-two/dual-three
fixture, with the same common target and exact product inverse. -/
theorem scalar_two_inverse_three :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let e := gradedClassificationContinuousEquiv (ZMod 5) C S
      (by simp [S]) (Subsingleton.elim _ _) (by decide)
    let g := e (DualExamples.scalarTwoUnit, 1)
    let q := GradedDiagramAut.toQuadratic (ZMod 5) C S g
    let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
    e.symm g = (DualExamples.scalarTwoUnit, 1) ∧
      q.universalEquiv (Finsupp.single H 1) H = 2 ∧
      DiagramAut.dualAction q (Finsupp.lapply H) (Finsupp.single H 1) = 3 ∧
      q.targetEquiv (Finsupp.single 0 1) 0 = 2 := by
  dsimp only
  refine ⟨by simp, ?_⟩
  rw [toQuadratic_gradedClassificationContinuousEquiv]
  exact ⟨QuadraticTopologyExamples.scalar_two_inverse_three.2.1,
    QuadraticTopologyExamples.scalar_two_inverse_three.2.2.1,
    QuadraticTopologyExamples.scalar_two_inverse_three.2.2.2.1⟩

/-- Over nonfield local ZMod4, the exact topological restriction inverse retains the full
scalar extension and the nonzero nilpotent coefficient from the original fixture. -/
theorem mod_four_full_extension :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    let g := (gradedAutContinuousEquiv (ZMod 4) C S (by simp [S]) hgen (by decide)).symm
      (scalarQuadraticAut (ZMod 4) C S LocalExamples.modFourUnit)
    g = scalarGradedAut (ZMod 4) C S LocalExamples.modFourUnit ∧
      (GradedDiagramAut.toQuadratic (ZMod 4) C S g).targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      g ≠ 1 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 :=
  GradedClassificationExamples.mod_four_full_extension

/-- The integral-domain full classifier is genuinely nonidentity over the nonlocal ring ℤ.
Its target restriction has the original negative scalar. -/
theorem integer_full_nonidentity :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    let g := coefficientDomainGradedClassificationContinuousEquiv ℤ C S
      (by simp [S]) hgen (by decide) (-1, 1)
    (GradedDiagramAut.toQuadratic ℤ C S g).targetEquiv (Finsupp.single 0 1) 0 = -1 ∧
      g ≠ 1 := by
  dsimp only
  constructor
  · rw [toQuadratic_coefficientDomainGradedClassificationContinuousEquiv]
    exact QuadraticTopologyExamples.integer_scalar_nonidentity.1
  · intro hg
    have hq := congrArg (GradedDiagramAut.toQuadratic _ _ _) hg
    rw [toQuadratic_coefficientDomainGradedClassificationContinuousEquiv, map_one] at hq
    exact QuadraticTopologyExamples.integer_scalar_nonidentity.2 hq

/-- A genuine full graded family has a nonidentity complex-conjugation field coordinate,
independent of its nonfield ZMod4 coefficients and with the original scalar target. -/
theorem conjugation_mod_four :
    let C := fullCofinalSystem ℝ ℂ 2
    let S : Set ℝ := Set.univ
    let e := gradedClassificationContinuousEquiv (ZMod 4) C S
      (by simp [S]) (by simp [S]) (by decide)
    let g := e (IncidenceExamples.scalarThreeUnit, Complex.conjAe)
    let q := GradedDiagramAut.toQuadratic (ZMod 4) C S g
    e.symm g = (IncidenceExamples.scalarThreeUnit, Complex.conjAe) ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) q
        Complex.I = -Complex.I ∧
      DiagramAut.toGalois (ZMod 4) C S (by simp [S]) (by simp [S]) (by decide) q ≠ 1 ∧
      q.targetEquiv (Finsupp.single 0 1) 0 = 3 := by
  dsimp only
  refine ⟨by simp, ?_⟩
  rw [toQuadratic_gradedClassificationContinuousEquiv]
  exact QuadraticTopologyExamples.conjugation_mod_four.2

end Pointwise

/-- The local krull wrapper retains both bare cancellations with its exact named topology.
-/
theorem local_krull_cancellation [IsLocalRing R] (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm
        (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p) = p ∧
      gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK
        ((gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm g) = g := by simp

/-- The domain krull wrapper retains both bare cancellations with its exact named topology.
-/
theorem domain_krull_cancellation [IsDomain R] (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm
        (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p) = p ∧
      coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK
        ((coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm g) =
          g := by simp

/-- The local algebraic wrapper retains both bare cancellations with its exact named topology.
-/
theorem local_algebraic_cancellation [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm
        (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p) = p ∧
      gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
        ((gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g) = g :=
          by simp

/-- The domain algebraic wrapper retains both bare cancellations with its exact named topology.
-/
theorem domain_algebraic_cancellation [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm
        (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
          p) = p ∧
      coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
        ((coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen
          hn).symm g) = g := by simp

/-- The literal Krull classifier obeys the original all-degree formula and actual marking
square; the scalar and covariant label action are independent of the topology wrapper. -/
theorem krull_degree_and_marking [IsLocalRing R] (hK : KrullFixingCondition k₀ k)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) (w : Marking S n)
    (hw : w.Available A.val.val) (y : OSAlgebra R (twoPunctureArrangement k)) :
    let g := gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK (a, σ)
    g.stageEquiv A x = (a : R) ^ q • galoisOSAlgebraEquiv R A.val σ x ∧
      g.stageEquiv A (w.osMap R hw y) = w.osMap R hw (g.targetEquiv y) := by
  dsimp only
  rw [gradedClassificationKrullContinuousEquiv_apply]
  exact ⟨gradedClassificationEquiv_stage_apply_of_mem_degree R C S hS hgen hn a σ A q x hx,
    gradedClassificationEquiv_marking R C S hS hgen hn a σ A w hw y⟩

end OrlikSolomon.HyperplaneGT.GradedTopologyExamples
