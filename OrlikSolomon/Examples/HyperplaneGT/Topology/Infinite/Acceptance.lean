/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.Infinite.Frobenius
public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Comparison

/-!
# A genuine infinite compact nondiscrete Galois example

For every prime `p`, the actual automorphism group of `AlgebraicClosure (ZMod p)` is
infinite by its distinct Frobenius powers, compact by T07, and nondiscrete. T06 identifies
the named pointwise topology with Mathlib's existing global Krull topology. The direct
permutation topology of the actual full stable system agrees with both in positive
dimension.

The selected stage `scalarStage p a` is the stable orbit closure of an actual geometric
coordinate fiber in dimension two. Its actual permutation kernel is clopen, and a proved
Frobenius-moved scalar gives a proper such kernel. No infinite group, selected system,
topology comparison or relabelled carrier is assumed. No instance is installed.

Blueprint: the required infinite-Galois regression for T02, T05–T07.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT.PrimeClosureExamples

open Filter Topology

variable (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure (ZMod p)
local notation "G" => K ≃ₐ[ZMod p] K

/-- T07 makes the actual prime-closure pointwise group compact. -/
theorem pointwise_compact :
    @CompactSpace G (galoisPointwiseTopology (ZMod p) K) :=
  galoisPointwise_compactSpace_of_isAlgebraic (ZMod p) K

/-- The infinite compact pointwise prime-closure group is not discrete. -/
theorem pointwise_not_discrete :
    ¬ @DiscreteTopology G (galoisPointwiseTopology (ZMod p) K) := by
  let : TopologicalSpace G := galoisPointwiseTopology (ZMod p) K
  let : CompactSpace G := pointwise_compact p
  let : Infinite G := galois_infinite p
  intro h
  let : DiscreteTopology G := h
  let : Finite G := finite_of_compact_of_discrete
  exact not_finite G

/-- T06 identifies the actual Krull topology with the named pointwise topology. -/
theorem krull_eq_pointwise :
    krullTopology (ZMod p) K = galoisPointwiseTopology (ZMod p) K :=
  krull_eq_pointwise_of_isAlgebraic (ZMod p) K

/-- The existing Krull topology on the actual prime-closure group is compact. -/
theorem krull_compact : @CompactSpace G (krullTopology (ZMod p) K) := by
  rw [krull_eq_pointwise p]
  exact pointwise_compact p

/-- The existing Krull topology on the actual infinite group is not discrete. -/
theorem krull_not_discrete : ¬ @DiscreteTopology G (krullTopology (ZMod p) K) := by
  rw [krull_eq_pointwise p]
  exact pointwise_not_discrete p

/-- The literal full stable system gives the actual pointwise permutation topology. -/
theorem full_stage_eq_pointwise (n : ℕ) (hn : 1 ≤ n) :
    (fullCofinalSystem (ZMod p) K n).galoisStagePermutationTopology =
      galoisPointwiseTopology (ZMod p) K :=
  (fullCofinalSystem (ZMod p) K n).galoisStagePermutationTopology_eq_pointwise hn

/-- The same full system gives the actual Krull topology in positive dimension. -/
theorem full_stage_eq_krull (n : ℕ) (hn : 1 ≤ n) :
    (fullCofinalSystem (ZMod p) K n).galoisStagePermutationTopology =
      krullTopology (ZMod p) K :=
  (fullCofinalSystem (ZMod p) K n).galoisStagePermutationTopology_eq_krull_of_isAlgebraic hn

/-- The actual selected stage is the stable orbit closure of the scalar's coordinate fiber. -/
noncomputable def scalarStage (a : K) : (fullCofinalSystem (ZMod p) K 2).Stage :=
  ⟨⟨stableClosure (k₀ := ZMod p) {coordinateFiber (0 : Fin 2) a},
    isGaloisStable_stableClosure _⟩, Set.mem_univ _⟩

/-- The original geometric fiber really occurs in the selected stable stage. -/
theorem coordinateFiber_mem_scalarStage (a : K) :
    (coordinateFiber (0 : Fin 2) a).val ∈ (scalarStage p a).val.val := by
  change (coordinateFiber (0 : Fin 2) a).val ∈
    stableClosure (k₀ := ZMod p) {coordinateFiber (0 : Fin 2) a}
  rw [mem_stableClosure]
  exact subset_galoisClosure _ (Finset.mem_singleton_self _)

/-- Each selected actual stage kernel is clopen for the named pointwise topology. -/
theorem scalarStageKernel_isClopen_pointwise (a : K) :
    @IsClopen G (galoisPointwiseTopology (ZMod p) K)
      ((fullCofinalSystem (ZMod p) K 2).galoisStageKernel (scalarStage p a) : Set G) :=
  (fullCofinalSystem (ZMod p) K 2).galoisPointwise_isClopen_stageKernel (scalarStage p a)

/-- The same actual stage kernel is clopen for Mathlib's existing Krull topology. -/
theorem scalarStageKernel_isClopen_krull (a : K) :
    @IsClopen G (krullTopology (ZMod p) K)
      ((fullCofinalSystem (ZMod p) K 2).galoisStageKernel (scalarStage p a) : Set G) := by
  rw [krull_eq_pointwise p]
  exact scalarStageKernel_isClopen_pointwise p a

/-- A proved Frobenius-moved scalar makes its selected actual stage kernel proper. -/
theorem exists_frobenius_not_mem_scalarStageKernel :
    ∃ a : K, frobenius p ∉
      (fullCofinalSystem (ZMod p) K 2).galoisStageKernel (scalarStage p a) := by
  obtain ⟨a, ha⟩ := exists_frobenius_moved_scalar p
  refine ⟨a, ?_⟩
  intro h
  have hfix := ((fullCofinalSystem (ZMod p) K 2).mem_galoisStageKernel_iff
    (scalarStage p a) (frobenius p)).mp h (coordinateFiber (0 : Fin 2) a)
      (coordinateFiber_mem_scalarStage p a)
  apply ha
  apply coordinateFiber_injective (0 : Fin 2)
  simpa only [galois_smul_coordinateFiber] using hfix

/-- The full system's actual stage kernels form the existing Krull identity basis. -/
theorem full_stage_kernel_krull_basis (n : ℕ) (hn : 1 ≤ n) :
    (@nhds G (krullTopology (ZMod p) K) 1).HasBasis
      (fun _ : (fullCofinalSystem (ZMod p) K n).Stage ↦ True)
      (fun A ↦ ((fullCofinalSystem (ZMod p) K n).galoisStageKernel A : Set G)) := by
  rw [krull_eq_pointwise p]
  exact (fullCofinalSystem (ZMod p) K n).galoisPointwise_nhds_one_stageKernelBasis hn

/-- Finite actual scalar tests give the same Krull identity neighborhoods. -/
theorem krull_scalar_test_basis :
    (@nhds G (krullTopology (ZMod p) K) 1).HasBasis
      (fun _ : Finset K ↦ True)
      (fun s ↦ (fixingSubgroup G (s : Set K) : Set G)) := by
  rw [krull_eq_pointwise p]
  exact galoisPointwise_nhds_one_basis (ZMod p) K

/-- The actual base-field equivalence fixes every element of the embedded prime field. -/
theorem frobenius_fixes_primeField (a : ZMod p) :
    frobenius p (algebraMap (ZMod p) K a) = algebraMap (ZMod p) K a :=
  (frobenius p).commutes a

/-- Both inverse cancellations retain the actual Frobenius equivalence. -/
theorem frobenius_inverse_cancellations (a : K) :
    (frobenius p).symm (frobenius p a) = a ∧
      frobenius p ((frobenius p).symm a) = a := by
  simp

/-- The example imports preserve inference of the existing global Krull topology. -/
theorem preserves_global_krull :
    (inferInstance : TopologicalSpace G) = krullTopology (ZMod p) K := rfl

/-- Characteristic two gives a genuine infinite actual automorphism group. -/
theorem binary_galois_infinite :
    Infinite (AlgebraicClosure (ZMod 2) ≃ₐ[ZMod 2] AlgebraicClosure (ZMod 2)) :=
  galois_infinite 2

/-- Characteristic three gives a second genuine infinite actual automorphism group. -/
theorem ternary_galois_infinite :
    Infinite (AlgebraicClosure (ZMod 3) ≃ₐ[ZMod 3] AlgebraicClosure (ZMod 3)) :=
  galois_infinite 3

end OrlikSolomon.HyperplaneGT.PrimeClosureExamples
