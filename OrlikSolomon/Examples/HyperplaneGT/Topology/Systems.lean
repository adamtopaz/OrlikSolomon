/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.FieldTheory.KrullTopology
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact
public import OrlikSolomon.HyperplaneGT.Topology.Cofinal
public import OrlikSolomon.Examples.HyperplaneGT.TheoryReconstruction
public import OrlikSolomon.HyperplaneGT.Topology.Krull
import Mathlib.Tactic.NormNum

/-!
# Pointwise topology and geometric finite-test consumers

The consumers keep Mathlib's global Krull topology and an independently supplied field
topology intact, while exercising the deliberate pointwise scope. The finite scalar and
stage-kernel bases work in independent field universes. Actual geometric fibers distinguish
complex conjugation at a nonreal scalar and the two binary scalars. Dimension zero retains
the field-group topology but every stage permutation kernel is the whole group.

The Krull consumers retain finite-dimensional intermediate fields and use (K) as an ordinary
proposition. Actual normalized coefficient fields detect nonreal geometry, while dimension
zero and trivial automorphism groups expose the hypothesis boundaries.

Finite scalar orbits, a chosen positive-dimensional stable system, and algebraicity give
separate compactness consumers. The concrete complex fixture has a nonidentity
automorphism; the genuine infinite-group example is separate from these consumers.

Cofinal restriction consumers use the existing genuinely non-union-closed subsystem,
retain the original target over nonfield coefficients, and check both cancellations for
every group and scalar-quotient homeomorphism. Generic zero-ring and dimension-zero
continuity does not assert a classified inverse.

Blueprint: T05–T07 (`lem:t05`, `thm:t06`, `prop:t07`) and T12 (`thm:t12`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT.PointwiseExamples

open Filter Topology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]

/-- Importing the pointwise modules leaves the existing global Krull instance unchanged. -/
theorem global_krull_preserved :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

/-- An independently supplied field topology is irrelevant to the explicitly discrete
codomains in the pointwise continuity criterion. -/
theorem competing_field_topology [t : TopologicalSpace k] {X : Type w} [TopologicalSpace X]
    (f : X → (k ≃ₐ[k₀] k)) :
    (inferInstance : TopologicalSpace k) = t ∧
      (Continuous[_, galoisPointwiseTopology k₀ k] f ↔
        ∀ a : k, Continuous[_, ⊥] (fun x ↦ f x a)) :=
  ⟨rfl, continuous_galoisPointwise_iff k₀ k f⟩

open scoped GaloisPointwise

/-- The deliberate scope selects exactly the named pointwise topology. -/
theorem scoped_pointwise :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = galoisPointwiseTopology k₀ k := rfl

/-- Group and separation instances infer together from the deliberate pointwise scope. -/
theorem scoped_group_separation : IsTopologicalGroup (k ≃ₐ[k₀] k) ∧
    T2Space (k ≃ₐ[k₀] k) ∧ TotallySeparatedSpace (k ≃ₐ[k₀] k) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A pointwise neighborhood is detected by a finite fixing subgroup, without arrangements
or an algebraicity assumption. -/
theorem finite_scalar_test (U : Set (k ≃ₐ[k₀] k)) :
    U ∈ 𝓝 (1 : k ≃ₐ[k₀] k) ↔
      ∃ s : Finset k, (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) ⊆ U :=
  galoisPointwise_mem_nhds_one_iff k₀ k U

/-- The exact finite coefficient test uses the hyperplane itself, not a supplied equation. -/
theorem hyperplane_test {n : ℕ} (H : Hyperplane k n) (σ : k ≃ₐ[k₀] k) :
    σ • H = H ↔ ∀ a ∈ hyperplaneCoefficientTests H, σ a = a := by
  rw [galois_smul_eq_iff_fixingCoefficients]

/-- The affine constant survives normalization: for `x₀-a`, its value is `-a`. -/
theorem normalized_constant (a : k) :
    normalizedAffineCoefficients
      (coefficientForm (Fin.cons (-a) (fun _ : Fin 1 ↦ (1 : k)))) 0 0 = -a := by
  simp only [normalizedAffineCoefficients, affineCoefficients_coefficientForm,
    Fin.cons_zero, Fin.cons_succ, div_one]

/-- Multiplying the full affine equation, including its constant, does not change its
fixed-pivot normalized coefficient vector. -/
theorem rescaled_equation (a : k) (c : kˣ) :
    normalizedAffineCoefficients
      ((c : k) • coefficientForm (Fin.cons (-a) (fun _ : Fin 1 ↦ (1 : k)))) 0 =
      normalizedAffineCoefficients
        (coefficientForm (Fin.cons (-a) (fun _ : Fin 1 ↦ (1 : k)))) 0 := by
  simp

/-- All geometric scalars, in an independent universe from the base, give equivariant fibers. -/
theorem geometric_fiber {n : ℕ} (i : Fin n) (a : k) (σ : k ≃ₐ[k₀] k) :
    σ • coordinateFiber i a = coordinateFiber i (σ a) := by
  simp

/-- The actual stage permutation applies to exactly the existing M8 label carrier and API. -/
theorem actual_stage_permutation {n : ℕ} (C : CofinalSystem k₀ k n) (A : C.Stage)
    (σ : k ≃ₐ[k₀] k) (H : A.val.val) :
    galoisStagePermutation A.val σ H = galoisLabelEquiv A.val σ H := by
  rw [galoisStagePermutation_apply]

/-- Bare simplification preserves left inverse cancellation for the actual stage action. -/
theorem stage_left_inverse {n : ℕ} (A : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (H : A.val) :
    (galoisStagePermutation A σ).symm (galoisStagePermutation A σ H) = H := by
  simp

/-- Bare simplification preserves right inverse cancellation for the actual stage action. -/
theorem stage_right_inverse {n : ℕ} (A : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (H : A.val) :
    galoisStagePermutation A σ ((galoisStagePermutation A σ).symm H) = H := by
  simp

/-- A stage kernel is tested on all its actual geometric hyperplanes. -/
theorem actual_stage_kernel {n : ℕ} (C : CofinalSystem k₀ k n) (A : C.Stage)
    (σ : k ≃ₐ[k₀] k) :
    σ ∈ C.galoisStageKernel A ↔
      ∀ H : Hyperplane k n, H.val ∈ A.val.val → σ • H = H := by
  rw [C.mem_galoisStageKernel_iff]

/-- Any chosen cofinal family gives the stage-kernel basis; no closure under unions is used. -/
theorem chosen_stage_basis {n : ℕ} (C : CofinalSystem k₀ k n) (hn : 1 ≤ n) :
    (𝓝 (1 : k ≃ₐ[k₀] k)).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ (C.galoisStageKernel A : Set _)) :=
  C.galoisPointwise_nhds_one_stageKernelBasis hn

/-- The topology of whole finite-stage permutations is pointwise convergence already in
dimension one, without the classification dimension bound. -/
theorem dimension_one_comparison (C : CofinalSystem k₀ k 1) :
    C.galoisStagePermutationTopology = galoisPointwiseTopology k₀ k := by
  rw [C.galoisStagePermutationTopology_eq_pointwise (by decide)]

/-- With no hyperplanes in dimension zero, each stage permutation kernel is the whole group.
The positive-dimension hypothesis in the topology comparison is therefore material. -/
theorem dimension_zero_kernel (C : CofinalSystem k₀ k 0) (A : C.Stage) :
    C.galoisStageKernel A = ⊤ := by
  apply top_unique
  intro σ _
  rw [C.mem_galoisStageKernel_iff]
  intro H _
  exact (not_isHyperplane_of_subsingleton H.val H.property).elim

/-- The two distinct geometric scalar fibers remain distinct in characteristic two. -/
theorem binary_fibers :
    coordinateFiber (0 : Fin 1) (0 : ZMod 2) ≠ coordinateFiber 0 1 := by
  intro h
  exact zero_ne_one (coordinateFiber_injective 0 h)

/-- A genuinely non-base-field fiber is moved by complex conjugation. This detects the
arbitrary geometric scalar required in T05, beyond the base-field marking fibers. -/
theorem conjugation_moves_geometric_fiber :
    Complex.conjAe • coordinateFiber (0 : Fin 1) Complex.I ≠ coordinateFiber 0 Complex.I := by
  rw [galois_smul_coordinateFiber]
  intro h
  have hi := congrArg Complex.im (coordinateFiber_injective 0 h)
  norm_num [Complex.conjAe] at hi

/-- A finite selected complex stage has a kernel excluding conjugation, without selecting
any special union-closed cofinal family. -/
theorem conjugation_excluded_at_stage :
    ∃ A : (fullCofinalSystem ℝ ℂ 1).Stage,
      Complex.conjAe ∉ (fullCofinalSystem ℝ ℂ 1).galoisStageKernel A := by
  classical
  obtain ⟨A, hA⟩ := (fullCofinalSystem ℝ ℂ 1).exists_stage_containing
    {coordinateFiber 0 Complex.I}
  refine ⟨A, fun h ↦ conjugation_moves_geometric_fiber ?_⟩
  exact ((fullCofinalSystem ℝ ℂ 1).mem_galoisStageKernel_iff A Complex.conjAe).mp h
    _ (hA _ (by simp))

end OrlikSolomon.HyperplaneGT.PointwiseExamples

namespace OrlikSolomon.HyperplaneGT.KrullExamples

open Filter Topology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]

/-- The optional facade preserves inference of Mathlib's actual global Krull topology. -/
theorem facade_preserves_global_krull :
    (inferInstance : TopologicalSpace (k ≃ₐ[k₀] k)) = krullTopology k₀ k := rfl

/-- The comparison iff is usable as an ordinary proposition, with no inferred condition or
algebraicity premise. -/
theorem criterion_from_equality
    (h : krullTopology k₀ k = galoisPointwiseTopology k₀ k) :
    KrullFixingCondition k₀ k := by
  rw [← krull_eq_pointwise_iff]
  exact h

/-- Trivial automorphism groups satisfy (K) without any algebraicity hypothesis. The finite
intermediate field can be the base field. -/
theorem criterion_of_trivial_galois [Subsingleton (k ≃ₐ[k₀] k)] :
    KrullFixingCondition k₀ k := by
  intro a
  refine ⟨⊥, inferInstance, ?_⟩
  intro σ _
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ]
  exact Subgroup.one_mem _

/-- Equality of the two topologies follows from a trivial group without assuming the
ambient extension algebraic. This does not claim an algebraicity converse. -/
theorem equality_of_trivial_galois [Subsingleton (k ≃ₐ[k₀] k)] :
    krullTopology k₀ k = galoisPointwiseTopology k₀ k :=
  (krull_eq_pointwise_iff k₀ k).mpr criterion_of_trivial_galois

/-- The actual identity maps are continuous in both directions over an algebraic extension.
The geometric and base fields may inhabit independent universes. -/
theorem algebraic_identity_both [Algebra.IsAlgebraic k₀ k] :
    Continuous[galoisPointwiseTopology k₀ k, krullTopology k₀ k]
      (id : (k ≃ₐ[k₀] k) → (k ≃ₐ[k₀] k)) ∧
    Continuous[krullTopology k₀ k, galoisPointwiseTopology k₀ k]
      (id : (k ≃ₐ[k₀] k) → (k ≃ₐ[k₀] k)) := by
  rw [krull_eq_pointwise_of_isAlgebraic]
  exact ⟨@continuous_id _ (galoisPointwiseTopology k₀ k),
    @continuous_id _ (galoisPointwiseTopology k₀ k)⟩

/-- A finite intermediate field has an exact finite scalar test even if it is not known
stable under any of the ambient automorphisms. -/
theorem finite_field_test (E : IntermediateField k₀ k) [FiniteDimensional k₀ E] :
    ∃ s : Finset k, (s : Set k) ⊆ (E : Set k) ∧
      fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) = E.fixingSubgroup :=
  exists_finset_fixingIntermediateField k₀ k E

/-- A chosen stage controls every given finite intermediate field already in dimension one;
the ambient extension need not be algebraic and (K) is not a hypothesis. -/
theorem finite_field_stage (C : CofinalSystem k₀ k 1) (E : IntermediateField k₀ k)
    [FiniteDimensional k₀ E] :
    ∃ A : C.Stage, C.galoisStageKernel A ≤ E.fixingSubgroup :=
  C.exists_stageKernel_le_fixingSubgroup (by decide) E

/-- The literal selected-stage topology agrees with Krull under the explicit criterion,
without replacing it by an algebraicity assumption. -/
theorem chosen_stage_krull (C : CofinalSystem k₀ k 1) (hK : KrullFixingCondition k₀ k) :
    C.galoisStagePermutationTopology = krullTopology k₀ k := by
  rw [C.galoisStagePermutationTopology_eq_krull (by decide) hK]

/-- The exact coefficient-field fixer equality is available without ambient algebraicity. -/
theorem coefficient_fixer {n : ℕ} (s : Finset (Hyperplane k n)) :
    (hyperplaneCoefficientField k₀ s).fixingSubgroup =
      fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n)) := by
  rw [fixingHyperplanes_eq_coefficientField]

/-- Dimension zero produces the base coefficient field, for arbitrary extensions. -/
theorem dimension_zero_field (s : Finset (Hyperplane k 0)) :
    hyperplaneCoefficientField k₀ s = ⊥ := by
  have hs : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro H _
    exact not_isHyperplane_of_subsingleton H.val H.property
  rw [hs, hyperplaneCoefficientField_empty]

/-- The empty collection has a finite coefficient field without any ambient algebraicity. -/
theorem empty_field_finite {n : ℕ} :
    FiniteDimensional k₀
      (hyperplaneCoefficientField k₀ (∅ : Finset (Hyperplane k n))) := by
  rw [hyperplaneCoefficientField_empty]
  infer_instance

/-- The nonreal geometric fiber gives a genuine finite coefficient field over the reals. -/
theorem nonreal_coefficient_field_finite :
    FiniteDimensional ℝ
      (hyperplaneCoefficientField ℝ {coordinateFiber (0 : Fin 1) Complex.I}) :=
  finiteDimensional_hyperplaneCoefficientField ℝ _

/-- The coefficient field really sees a scalar moved by conjugation; the affine constant
has not disappeared from the normalized equation test. -/
theorem conjugation_not_in_coefficient_fixer :
    Complex.conjAe ∉
      (hyperplaneCoefficientField ℝ {coordinateFiber (0 : Fin 1) Complex.I}).fixingSubgroup := by
  classical
  rw [← fixingHyperplanes_eq_coefficientField]
  intro h
  exact PointwiseExamples.conjugation_moves_geometric_fiber
    ((mem_fixingSubgroup_iff (ℂ ≃ₐ[ℝ] ℂ)).mp h _ (by simp))

end OrlikSolomon.HyperplaneGT.KrullExamples

namespace OrlikSolomon.HyperplaneGT.GaloisCompactExamples

open Topology
open scoped GaloisPointwise

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]

/-- Finite actual scalar orbits combine with the existing group and separation API to give
a profinite topological group, with no arrangements or algebraicity assumption. -/
theorem finite_orbit_profinite
    (hfinite : ∀ a : k, (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite) :
    CompactSpace (k ≃ₐ[k₀] k) ∧ IsTopologicalGroup (k ≃ₐ[k₀] k) ∧
      T2Space (k ≃ₐ[k₀] k) ∧ TotallySeparatedSpace (k ≃ₐ[k₀] k) :=
  ⟨galoisPointwise_compactSpace_of_finite_orbits k₀ k hfinite,
    inferInstance, inferInstance, inferInstance⟩

/-- A finite automorphism group is enough for compactness; ambient algebraicity and a
cofinal system are not prerequisites of the general finite-orbit theorem. -/
theorem finite_group_compact [Finite (k ≃ₐ[k₀] k)] :
    @CompactSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) :=
  galoisPointwise_compactSpace_of_finite_orbits k₀ k (fun _ ↦ Set.finite_range _)

/-- Any chosen positive-dimensional system has compact actual stage-permutation topology.
This combines the finite-orbit proof with T05's direct topology equality, using no union
closure or algebraicity. -/
theorem chosen_stage_compact {n : ℕ} (C : CofinalSystem k₀ k n) (hn : 1 ≤ n) :
    @CompactSpace (k ≃ₐ[k₀] k) C.galoisStagePermutationTopology := by
  rw [C.galoisStagePermutationTopology_eq_pointwise hn]
  exact C.galoisPointwise_compactSpace hn

/-- An independently supplied geometric-field topology remains intact when the algebraic
corollary provides compactness for the separately named pointwise automorphism topology. -/
theorem algebraic_compact_with_field_topology [t : TopologicalSpace k]
    [Algebra.IsAlgebraic k₀ k] :
    (inferInstance : TopologicalSpace k) = t ∧
      @CompactSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) :=
  ⟨rfl, galoisPointwise_compactSpace_of_isAlgebraic k₀ k⟩

/-- The constructed binary stable system gives a compact stage-permutation group already
in dimension one. -/
theorem binary_stage_compact :
    @CompactSpace (ZMod 2 ≃ₐ[ZMod 2] ZMod 2)
      (fullCofinalSystem (ZMod 2) (ZMod 2) 1).galoisStagePermutationTopology :=
  chosen_stage_compact (fullCofinalSystem (ZMod 2) (ZMod 2) 1) (by decide)

/-- The constructed complex stable system has compact stage-permutation topology. -/
theorem complex_stage_compact :
    @CompactSpace (ℂ ≃ₐ[ℝ] ℂ)
      (fullCofinalSystem ℝ ℂ 1).galoisStagePermutationTopology :=
  chosen_stage_compact (fullCofinalSystem ℝ ℂ 1) (by decide)

/-- The actual compact complex pointwise group is nontrivial: conjugation moves the
geometric fiber at `I`. This is a finite-group fixture, not an infinite-group claim. -/
theorem complex_compact_nontrivial :
    @CompactSpace (ℂ ≃ₐ[ℝ] ℂ) (galoisPointwiseTopology ℝ ℂ) ∧
      Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) := by
  refine ⟨galoisPointwise_compactSpace_of_isAlgebraic ℝ ℂ, ?_⟩
  intro h
  apply PointwiseExamples.conjugation_moves_geometric_fiber
  rw [h, one_smul]

end OrlikSolomon.HyperplaneGT.GaloisCompactExamples

namespace OrlikSolomon.HyperplaneGT.CofinalTopologyExamples

open Topology
open scoped FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} {R : Type w} [CommRing R] (C C' : CofinalSystem k₀ k n) (S : Set k₀)
  (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
  (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- All four local homeomorphisms retain both ordinary inverse simplifications. -/
theorem local_cancellation [IsLocalRing R]
    (g : DiagramAut R C S) (g' : DiagramAut R C' S)
    (f : GradedDiagramAut R C S) (f' : GradedDiagramAut R C' S)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
    (q' : DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S)
    (z : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
    (z' : GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) :
    (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm
        (cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g) = g ∧
    cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn
        ((cofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g') = g' ∧
    (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm
        (gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn f) = f ∧
    gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn
        ((gradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm f') = f' ∧
    (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
        (cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) = q ∧
    cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
        ((cofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q') = q' ∧
    (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
        (gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn z) = z ∧
    gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
        ((gradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm z') = z' := by
          simp

/-- All four domain homeomorphisms retain both ordinary inverse simplifications. -/
theorem domain_cancellation [IsDomain R]
    (g : DiagramAut R C S) (g' : DiagramAut R C' S)
    (f : GradedDiagramAut R C S) (f' : GradedDiagramAut R C' S)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
    (q' : DiagramAut R C' S ⧸ DiagramAut.scalarSubgroup R C' S)
    (z : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
    (z' : GradedDiagramAut R C' S ⧸ GradedDiagramAut.scalarSubgroup R C' S) :
    (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm
        (domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn g) = g ∧
    domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn
        ((domainCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm g') = g' ∧
    (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm
        (domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn f) = f ∧
    domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn
        ((domainGradedCofinalRestrictionContinuousEquiv R C C' S hC hS hgen hn).symm f') = f' ∧
    (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
        (domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn q) = q ∧
    domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
        ((domainCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm q') = q' ∧
    (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm
        (domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn z) = z ∧
    domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn
        ((domainGradedCofinalScalarQuotientContinuousEquiv R C C' S hC hS hgen hn).symm z') = z'
          := by simp

/-- Actual restriction to the supplied non-union-closed subsystem is faithful and keeps
its original target, without any coefficient or classification restriction. -/
theorem non_union_closed_restriction (R : Type w) [CommRing R]
    (g : DiagramAut R (fullCofinalSystem (ZMod 2) (ZMod 2) 2) Set.univ) :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let D := TheoryReconstructionExamples.nonUnionSystem
    let r := DiagramAut.restrictStages R C D Set.univ
      TheoryReconstructionExamples.nonUnionSystem_subset
    IsEmbedding r ∧ (r g).targetEquiv = g.targetEquiv :=
  ⟨DiagramAut.isEmbedding_restrictStages _ _ _ _ _,
    DiagramAut.restrictStages_targetEquiv _ _ _ _ _ _⟩

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- The actual nonfield local scalar family restricts through a cofinal family that is not
union-closed, with its nonidentity target unchanged and an actual two-sided inverse. -/
theorem non_union_mod_four :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let D := TheoryReconstructionExamples.nonUnionSystem
    let e := cofinalRestrictionContinuousEquiv (ZMod 4) C D Set.univ
      TheoryReconstructionExamples.nonUnionSystem_subset (by simp) (by simp) (by decide)
    let g := scalarQuadraticAut (ZMod 4) C Set.univ IncidenceExamples.scalarThreeUnit
    e g = scalarQuadraticAut (ZMod 4) D Set.univ IncidenceExamples.scalarThreeUnit ∧
      e.symm (e g) = g ∧ (e g).targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 = 3 := by
  dsimp only
  refine ⟨?_, by simp, ?_⟩
  · rw [cofinalRestrictionContinuousEquiv_apply, DiagramAut.restrictStages_scalarQuadraticAut]
  · rw [cofinalRestrictionContinuousEquiv_targetEquiv, scalarQuadraticAut_targetEquiv_apply]
    simp [IncidenceExamples.scalarThreeUnit]

/-- The nonlocal integral domain ℤ uses the domain graded inverse, still through the actual
non-union-closed subsystem and with the original negative scalar on the common target. -/
theorem non_union_integer_graded :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let D := TheoryReconstructionExamples.nonUnionSystem
    let e := domainGradedCofinalRestrictionContinuousEquiv ℤ C D Set.univ
      TheoryReconstructionExamples.nonUnionSystem_subset (by simp) (by simp) (by decide)
    let g := scalarGradedAut ℤ C Set.univ (-1)
    e.symm (e g) = g ∧
      (GradedDiagramAut.toQuadratic ℤ D Set.univ (e g)).targetEquiv
        (Finsupp.single (0 : Fin 2) 1) 0 = -1 := by
  dsimp only
  refine ⟨by simp, ?_⟩
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply,
    GradedDiagramAut.restrictStages_scalarGradedAut, toQuadratic_scalarGradedAut,
    scalarQuadraticAut_targetEquiv_apply]
  simp

/-- Literal restriction and its scalar quotients remain continuous for zero coefficients
and dimension zero. This does not claim classified invertibility in those boundary cases. -/
theorem zero_ring_dimension_zero (C : CofinalSystem k₀ k 0) (S : Set k₀) :
    IsEmbedding (DiagramAut.restrictStages (ZMod 1) C C S (Set.Subset.refl _)) ∧
    IsEmbedding (GradedDiagramAut.restrictStages (ZMod 1) C C S (Set.Subset.refl _)) ∧
    Continuous (DiagramAut.restrictStagesScalarQuotient (ZMod 1) C C S (Set.Subset.refl _)) ∧
    Continuous (GradedDiagramAut.restrictStagesScalarQuotient (ZMod 1) C C S
      (Set.Subset.refl _)) :=
  ⟨DiagramAut.isEmbedding_restrictStages _ _ _ _ _,
    GradedDiagramAut.isEmbedding_restrictStages _ _ _ _ _,
    DiagramAut.continuous_restrictStagesScalarQuotient _ _ _ _ _,
    GradedDiagramAut.continuous_restrictStagesScalarQuotient _ _ _ _ _⟩

/-- An actual nonidentity Galois class over the nonlocal domain ℤ is unchanged by
cofinal quotient restriction; its inverse is the existing classified extension. -/
theorem complex_conjugation_quotient (C C' : CofinalSystem ℝ ℂ 2)
    (hC : C'.stages ⊆ C.stages) :
    let e := domainCofinalScalarQuotientContinuousEquiv ℤ C C' Set.univ hC
      (by simp) (by simp) (by decide)
    let q := DiagramAut.scalarQuotientSection ℤ C Set.univ Complex.conjAe
    e q = DiagramAut.scalarQuotientSection ℤ C' Set.univ Complex.conjAe ∧
      e q ≠ 1 ∧ e.symm (e q) = q := by
  dsimp only
  refine ⟨domainCofinalScalarQuotientContinuousEquiv_scalarQuotientSection _ _ _ _ _ _ _ _ _,
    ?_, by simp⟩
  intro he
  have hfield := congrArg
    (DiagramAut.domainScalarQuotientEquiv ℤ C' Set.univ (by simp) (by simp) (by decide)) he
  rw [domainCofinalScalarQuotientContinuousEquiv_scalarQuotientSection,
    DiagramAut.domainScalarQuotientEquiv_section, map_one] at hfield
  exact GaloisCompactExamples.complex_compact_nontrivial.2 hfield

end OrlikSolomon.HyperplaneGT.CofinalTopologyExamples
