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
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Hyperplanes
import Mathlib.Tactic.NormNum

/-!
# Pointwise topology and geometric finite-test consumers

The consumers keep Mathlib's global Krull topology and an independently supplied field
topology intact, while exercising the deliberate pointwise scope. The finite scalar and
stage-kernel bases work in independent field universes. Actual geometric fibers distinguish
complex conjugation at a nonreal scalar and the two binary scalars. Dimension zero retains
the field-group topology but every stage permutation kernel is the whole group.

Finite scalar orbits, a chosen positive-dimensional stable system, and algebraicity give
separate compactness consumers. The concrete complex fixture has a nonidentity
automorphism; the genuine infinite-group example is separate from these consumers.

Blueprint: T05 (`lem:t05`) and T07 (`prop:t07`).
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
