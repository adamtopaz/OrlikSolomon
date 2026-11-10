/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Krull.Pointwise
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.SimpleRing.DivisionRing

/-!
# Compactness from finite scalar orbits

The existing pointwise field-automorphism group is compact whenever every scalar has finite
orbit under that group. Evaluation embeds it into the product of the discrete orbit
subtypes. The equations preserving the field operations and base scalars are closed. An
orbit-compatible field endomorphism is surjective on each finite orbit, so those equations
describe exactly the automorphisms, rather than an enlarged endomorphism space.

Together with the topological-group and separation results in T05, compactness gives a
profinite group. No arrangement, cofinal system, dimension, algebraicity or normality enters
this argument. No global topology or compactness instance is installed.

Blueprint: the finite-orbit compactness assertion of T07 (`prop:t07`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open Topology
open scoped GaloisPointwise

variable (k₀ : Type u) (k : Type v) [Field k₀] [Field k] [Algebra k₀ k]

/-- An orbit-compatible field endomorphism is surjective when the actual automorphism
orbits are finite: its restriction to each orbit is an injective finite self-map. -/
theorem surjective_of_mem_galoisOrbit
    (hfinite : ∀ a : k, (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite)
    (f : k →ₐ[k₀] k)
    (hf : ∀ a : k, f a ∈ MulAction.orbit (k ≃ₐ[k₀] k) a) :
    Function.Surjective f := by
  intro a
  let : Finite (MulAction.orbit (k ≃ₐ[k₀] k) a) := (hfinite a).to_subtype
  let F : MulAction.orbit (k ≃ₐ[k₀] k) a → MulAction.orbit (k ≃ₐ[k₀] k) a := fun b ↦
    ⟨f b, by
      have hsame : MulAction.orbit (k ≃ₐ[k₀] k) b.val =
          MulAction.orbit (k ≃ₐ[k₀] k) a := MulAction.orbit_eq_iff.mpr b.property
      exact hsame.le (hf b)⟩
  have hi : Function.Injective F := by
    intro b c h
    exact Subtype.ext (f.toRingHom.injective (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hi ⟨a, MulAction.mem_orbit_self a⟩
  exact ⟨b.val, congrArg Subtype.val hb⟩

private def orbitEvaluation (σ : k ≃ₐ[k₀] k) (a : k) :
    MulAction.orbit (k ≃ₐ[k₀] k) a :=
  ⟨σ a, ⟨σ, rfl⟩⟩

/-- The product of the discrete orbit subtypes, with the topology inherited from a discrete
field in each factor. This is only an ambient space, not a new automorphism carrier. -/
@[instance_reducible]
private def orbitProductTopology :
    TopologicalSpace (∀ a : k, MulAction.orbit (k ≃ₐ[k₀] k) a) :=
  letI : TopologicalSpace k := ⊥
  inferInstance

private def orbitEquations (x : ∀ a : k, MulAction.orbit (k ≃ₐ[k₀] k) a) : Prop :=
  (x 0 : k) = 0 ∧ (x 1 : k) = 1 ∧
    (∀ a b : k, (x (a + b) : k) = (x a : k) + (x b : k)) ∧
    (∀ a b : k, (x (a * b) : k) = (x a : k) * (x b : k)) ∧
    ∀ c : k₀, (x (algebraMap k₀ k c) : k) = algebraMap k₀ k c

private theorem range_orbitEvaluation
    (hfinite : ∀ a : k, (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite) :
    Set.range (orbitEvaluation k₀ k) = {x | orbitEquations k₀ k x} := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨map_zero σ, map_one σ, map_add σ, map_mul σ, σ.commutes⟩
  · rintro ⟨hzero, hone, hadd, hmul, hbase⟩
    let f : k →ₐ[k₀] k :=
      { toFun := fun a ↦ (x a : k)
        map_zero' := hzero
        map_one' := hone
        map_add' := hadd
        map_mul' := hmul
        commutes' := hbase }
    refine ⟨AlgEquiv.ofBijective f ⟨f.toRingHom.injective,
      surjective_of_mem_galoisOrbit k₀ k hfinite f (fun a ↦ (x a).property)⟩, ?_⟩
    funext a
    exact Subtype.ext rfl

private theorem orbitEquations_isClosed :
    @IsClosed _ (orbitProductTopology k₀ k) {x | orbitEquations k₀ k x} := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  have heval (a : k) : Continuous
      (fun x : ∀ b : k, MulAction.orbit (k ≃ₐ[k₀] k) b ↦ (x a : k)) :=
    continuous_subtype_val.comp (continuous_apply a)
  simpa only [orbitEquations, orbitProductTopology, Set.ofPred_and, Set.ofPred_forall,
    Pi.add_apply, Pi.mul_apply] using
    (isClosed_eq (heval 0) continuous_const).inter
      ((isClosed_eq (heval 1) continuous_const).inter
        ((isClosed_iInter (fun a ↦ isClosed_iInter (fun b ↦
          isClosed_eq (heval (a + b)) ((heval a).add (heval b))))).inter
          ((isClosed_iInter (fun a ↦ isClosed_iInter (fun b ↦
            isClosed_eq (heval (a * b)) ((heval a).mul (heval b))))).inter
            (isClosed_iInter (fun c : k₀ ↦
              isClosed_eq (heval (algebraMap k₀ k c)) continuous_const)))))

private theorem orbitEvaluation_isEmbedding :
    @IsEmbedding _ _ (galoisPointwiseTopology k₀ k) (orbitProductTopology k₀ k)
      (orbitEvaluation k₀ k) := by
  let : TopologicalSpace k := ⊥
  have hcoe : IsEmbedding (fun (x : ∀ a : k, MulAction.orbit (k ≃ₐ[k₀] k) a) a ↦
      (x a : k)) := IsEmbedding.piMap (fun _ ↦ IsEmbedding.subtypeVal)
  exact hcoe.of_comp_iff.mp (galoisPointwise_isEmbedding_coe k₀ k)

/-- The actual pointwise field-automorphism group is compact if every scalar has finite
orbit. With T05's group and separation properties it is profinite. Blueprint: T07 (`prop:t07`).
-/
theorem galoisPointwise_compactSpace_of_finite_orbits
    (hfinite : ∀ a : k, (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite) :
    @CompactSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) := by
  let : TopologicalSpace k := ⊥
  let : ∀ a : k, Finite (MulAction.orbit (k ≃ₐ[k₀] k) a) :=
    fun a ↦ (hfinite a).to_subtype
  have hclosed : IsClosed (Set.range (orbitEvaluation k₀ k)) := by
    rw [range_orbitEvaluation k₀ k hfinite]
    exact orbitEquations_isClosed k₀ k
  exact (⟨orbitEvaluation_isEmbedding k₀ k, hclosed⟩ :
    IsClosedEmbedding (orbitEvaluation k₀ k)).compactSpace

end OrlikSolomon.HyperplaneGT
