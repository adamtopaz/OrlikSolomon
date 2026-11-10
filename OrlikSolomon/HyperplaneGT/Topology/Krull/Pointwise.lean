/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Constructions

/-!
# Pointwise convergence of field automorphisms

The existing group of field automorphisms over a base field has a named topology induced
by evaluation into the product of discrete copies of the geometric field. No topology on
the field is assumed or installed. The choice is available through the deliberate
`GaloisPointwise` scope; it does not replace Mathlib's Krull topology.

## Main definitions and results

* `galoisPointwiseTopology` is the explicit induced topology.
* `continuous_galoisPointwise_iff` characterizes maps into it by scalar evaluations.
* `galoisPointwise_nhds_basis` and `galoisPointwise_nhds_one_basis` give finite tests.
* `galoisPointwise_isTopologicalGroup`, `galoisPointwise_t2Space` and
  `galoisPointwise_totallySeparatedSpace` give the group and separation properties.

No arrangement, cofinal system, dimension or algebraicity is involved.
Blueprint: the field-group part of T05 (`lem:t05`).
-/

@[expose] public section

universe u v w

namespace OrlikSolomon.HyperplaneGT

open Filter Topology
open scoped Topology

variable (k₀ : Type u) (k : Type v) [Field k₀] [Field k] [Algebra k₀ k]

/-- Pointwise convergence of field automorphisms, with every evaluated scalar discrete.
This is a named choice on the existing carrier, without a topology on the field itself.
Blueprint: T05 (`lem:t05`). -/
@[instance_reducible]
def galoisPointwiseTopology : TopologicalSpace (k ≃ₐ[k₀] k) :=
  TopologicalSpace.induced (fun (σ : k ≃ₐ[k₀] k) (a : k) ↦ σ a)
    (@Pi.topologicalSpace k (fun _ : k ↦ k) (fun _ ↦ ⊥))

/-- The pointwise topology is induced by the actual scalar evaluation tuple. -/
theorem galoisPointwiseTopology_eq_induced :
    galoisPointwiseTopology k₀ k =
      TopologicalSpace.induced (fun (σ : k ≃ₐ[k₀] k) (a : k) ↦ σ a)
        (@Pi.topologicalSpace k (fun _ : k ↦ k) (fun _ ↦ ⊥)) := rfl

namespace GaloisPointwise

/-- Activate only the named pointwise topology on the existing field automorphism group. -/
scoped instance instTopologicalSpace : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k

end GaloisPointwise

open scoped GaloisPointwise

/-- Evaluating an automorphism at every scalar embeds the pointwise group into a product
of discrete scalar spaces. -/
theorem galoisPointwise_isEmbedding_coe :
    @IsEmbedding (k ≃ₐ[k₀] k) (k → k) (galoisPointwiseTopology k₀ k)
      (@Pi.topologicalSpace k (fun _ : k ↦ k) (fun _ ↦ ⊥))
      (fun σ a ↦ σ a) := by
  let : TopologicalSpace k := ⊥
  exact DFunLike.coe_injective.isEmbedding_induced

/-- Each fixed scalar evaluation is continuous into the explicitly discrete field. -/
theorem continuous_galoisPointwise_apply (a : k) :
    Continuous[galoisPointwiseTopology k₀ k, ⊥] (fun σ : k ≃ₐ[k₀] k ↦ σ a) := by
  let : TopologicalSpace k := ⊥
  exact (continuous_apply a).comp (galoisPointwise_isEmbedding_coe k₀ k).continuous

/-- A map into the pointwise automorphism group is continuous exactly when every scalar
evaluation is continuous into the discrete field. -/
theorem continuous_galoisPointwise_iff {X : Type w} [TopologicalSpace X]
    (f : X → (k ≃ₐ[k₀] k)) :
    Continuous[_, galoisPointwiseTopology k₀ k] f ↔
      ∀ a : k, Continuous[_, ⊥] (fun x ↦ f x a) := by
  let : TopologicalSpace k := ⊥
  rw [(galoisPointwise_isEmbedding_coe k₀ k).isInducing.continuous_iff]
  exact continuous_pi_iff

/-- Finite equality tests on scalars form a neighborhood basis at any field automorphism.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_nhds_basis (σ : k ≃ₐ[k₀] k) :
    (@nhds _ (galoisPointwiseTopology k₀ k) σ).HasBasis
      (fun _ : Finset k ↦ True) (fun s ↦ {τ | ∀ a ∈ s, τ a = σ a}) := by
  classical
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  have hs : (𝓝 σ).HasBasis Set.Finite
      (fun s : Set k ↦ {τ : k ≃ₐ[k₀] k | ∀ a ∈ s, τ a = σ a}) := by
    rw [(galoisPointwise_isEmbedding_coe k₀ k).isInducing.nhds_eq_comap σ, nhds_pi]
    simp_rw [nhds_discrete]
    exact (hasBasis_pi_pure (fun a ↦ σ a)).comap (fun (τ : k ≃ₐ[k₀] k) a ↦ τ a)
  refine hs.to_hasBasis (fun s hs ↦ ⟨hs.toFinset, trivial, ?_⟩)
    (fun s _ ↦ ⟨(s : Set k), s.finite_toSet, subset_rfl⟩)
  intro τ hτ a ha
  exact hτ a (hs.mem_toFinset.mpr ha)

/-- Identity neighborhoods are precisely sets containing a finite scalar fixing subgroup.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_nhds_one_basis :
    (@nhds _ (galoisPointwiseTopology k₀ k) 1).HasBasis
      (fun _ : Finset k ↦ True)
      (fun s ↦ (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set (k ≃ₐ[k₀] k))) := by
  convert galoisPointwise_nhds_basis k₀ k 1 using 1
  ext s σ
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixingSubgroup_iff,
    AlgEquiv.smul_def, AlgEquiv.one_apply]

/-- Membership in an identity neighborhood is detected by a finite scalar fixing test. -/
theorem galoisPointwise_mem_nhds_one_iff (U : Set (k ≃ₐ[k₀] k)) :
    U ∈ @nhds _ (galoisPointwiseTopology k₀ k) 1 ↔
      ∃ s : Finset k, (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) ⊆ U := by
  simpa only [true_and] using (galoisPointwise_nhds_one_basis k₀ k).mem_iff

/-- Every finite scalar fixing subgroup is clopen in the explicit pointwise topology. -/
theorem galoisPointwise_isClopen_fixing (s : Finset k) :
    @IsClopen (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k)
      (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  have hs : (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) =
      ⋂ a ∈ s, {σ : k ≃ₐ[k₀] k | σ a = a} := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixingSubgroup_iff,
      AlgEquiv.smul_def, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hs]
  exact isClopen_biInter_finset (fun a _ ↦
    (isClopen_discrete {a}).preimage (continuous_galoisPointwise_apply k₀ k a))

/-- Pointwise convergence makes the existing field automorphism group a topological group.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_isTopologicalGroup :
    @IsTopologicalGroup (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  have heval : Continuous (fun p : (k ≃ₐ[k₀] k) × k ↦ p.1 p.2) :=
    continuous_prod_of_discrete_right.mpr (continuous_galoisPointwise_apply k₀ k)
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply (continuous_galoisPointwise_iff k₀ k _).mpr
    intro a
    exact heval.comp (continuous_fst.prodMk
      ((continuous_galoisPointwise_apply k₀ k a).comp continuous_snd))
  · apply (continuous_galoisPointwise_iff k₀ k _).mpr
    intro a
    apply continuous_iff_continuousAt.mpr
    intro σ
    have h : ∀ᶠ τ : k ≃ₐ[k₀] k in 𝓝 σ, τ (σ.symm a) = a := by
      have hc := (continuous_galoisPointwise_apply k₀ k (σ.symm a)).continuousAt (x := σ)
      change Tendsto (fun τ : k ≃ₐ[k₀] k ↦ τ (σ.symm a)) (𝓝 σ)
        (𝓝 (σ (σ.symm a))) at hc
      simpa only [AlgEquiv.apply_symm_apply, nhds_discrete, tendsto_pure] using hc
    change Tendsto (fun τ : k ≃ₐ[k₀] k ↦ τ.symm a) (𝓝 σ) (𝓝 (σ.symm a))
    rw [show (𝓝 (σ.symm a) : Filter k) = pure (σ.symm a) from congrFun (nhds_discrete k) _,
      tendsto_pure]
    filter_upwards [h] with τ hτ
    exact (τ.symm_apply_eq).mpr hτ.symm

/-- Distinct field automorphisms are separated by a discrete scalar evaluation.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_t2Space : @T2Space (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  exact (galoisPointwise_isEmbedding_coe k₀ k).t2Space

/-- Scalar evaluations separate automorphisms by complementary clopen cylinders.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_totallySeparatedSpace :
    @TotallySeparatedSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ hστ
  obtain ⟨a, ha⟩ := DFunLike.exists_ne hστ
  refine ⟨{ρ | ρ a = σ a}, (isClopen_discrete {σ a}).preimage
    (continuous_galoisPointwise_apply k₀ k a), rfl, ?_⟩
  exact fun h ↦ ha h.symm

namespace GaloisPointwise

/-- Topological group structure for the deliberate pointwise scope. -/
scoped instance instIsTopologicalGroup : IsTopologicalGroup (k ≃ₐ[k₀] k) :=
  galoisPointwise_isTopologicalGroup k₀ k

/-- Hausdorff separation for the deliberate pointwise scope. -/
scoped instance instT2Space : T2Space (k ≃ₐ[k₀] k) := galoisPointwise_t2Space k₀ k

/-- Total separation for the deliberate pointwise scope. -/
scoped instance instTotallySeparatedSpace : TotallySeparatedSpace (k ≃ₐ[k₀] k) :=
  galoisPointwise_totallySeparatedSpace k₀ k

end GaloisPointwise

end OrlikSolomon.HyperplaneGT
