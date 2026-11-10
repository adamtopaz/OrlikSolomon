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

Blueprint: T05–T06 (`lem:t05`, `thm:t06`).
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
