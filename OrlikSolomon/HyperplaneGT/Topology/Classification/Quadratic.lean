/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions.SumProd
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Descent
public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Topology.Krull
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Quadratic reconstruction with the finite-stage topology

The coefficient units are discrete, independently of a topology on the coefficient ring.
`coefficientGaloisPointwiseTopology` and `coefficientGaloisKrullTopology` are literal product
values on the existing parameter carrier. All three named topology values are
`instance_reducible` so inherited discrete/product instances see their representations;
only the deliberate `DiscreteCoefficientUnits` scope registers unit topology instances.
No topology is defined through a reconstruction map, and global Krull and field topologies
remain unchanged on import.

The exact simultaneous stage-and-target kernel preimage retains the common target even
when the selected stage is empty. It upgrades the original local/domain multiplicative
equivalences by adjoining both continuity proofs, without redoing reconstruction or descent.
Forward and inverse expansions are plain rewrites, preserving bare inverse cancellation.

## Main definitions and results

* `scalarGalois_preimage_stageKernel` is the exact target-retaining kernel equation.
* `quadraticAutContinuousEquiv` and `coefficientDomainAutContinuousEquiv` adjoin pointwise
  continuity to the exact existing local and domain classifiers.
* `quadraticAutKrullContinuousEquiv` and `coefficientDomainAutKrullContinuousEquiv` use the
  explicit fixing condition; their `OfIsAlgebraic` wrappers require only algebraicity.
* The `toMulEquiv`, function and inverse equations preserve the original scalar/Galois maps.

Blueprint: T09 (`thm:t09`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Filter Topology

/-- The discrete topology on units, without choosing any topology on the underlying monoid. -/
@[instance_reducible]
def discreteUnitsTopology (M : Type r) [Monoid M] : TopologicalSpace Mˣ := ⊥

namespace DiscreteCoefficientUnits

/-- Deliberately select discrete units without changing a topology on their coefficient type. -/
scoped instance instTopologicalSpace (M : Type r) [Monoid M] :
    TopologicalSpace Mˣ := discreteUnitsTopology M

/-- The deliberate unit topology is discrete. -/
scoped instance instDiscreteTopology (M : Type r) [Monoid M] :
    DiscreteTopology Mˣ := discreteTopology_bot _

end DiscreteCoefficientUnits

/-- The literal product of discrete units and pointwise field automorphisms.
This topology has no arrangement or reconstruction input. Blueprint: T09 (`thm:t09`). -/
@[instance_reducible]
def coefficientGaloisPointwiseTopology (M : Type r) [Monoid M]
    (k₀ : Type u) (k : Type v) [Field k₀] [Field k] [Algebra k₀ k] :
    TopologicalSpace (Mˣ × (k ≃ₐ[k₀] k)) :=
  @instTopologicalSpaceProd Mˣ (k ≃ₐ[k₀] k)
    (discreteUnitsTopology M) (galoisPointwiseTopology k₀ k)

/-- The literal product of discrete units and Mathlib's actual Krull topology.
This named value uses Krull even inside the pointwise scope. Blueprint: T09 (`thm:t09`). -/
@[instance_reducible]
def coefficientGaloisKrullTopology (M : Type r) [Monoid M]
    (k₀ : Type u) (k : Type v) [Field k₀] [Field k] [Algebra k₀ k] :
    TopologicalSpace (Mˣ × (k ≃ₐ[k₀] k)) :=
  @instTopologicalSpaceProd Mˣ (k ≃ₐ[k₀] k)
    (discreteUnitsTopology M) (krullTopology k₀ k)

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]

/-- The exact fixing condition identifies the two independently defined parameter topologies. -/
theorem coefficientGaloisKrullTopology_eq_pointwise (M : Type r) [Monoid M]
    (hK : KrullFixingCondition k₀ k) :
    coefficientGaloisKrullTopology M k₀ k = coefficientGaloisPointwiseTopology M k₀ k := by
  rw [coefficientGaloisKrullTopology, (krull_eq_pointwise_iff k₀ k).mpr hK]
  rfl

/-- Algebraicity supplies the parameter-topology comparison without normality or separability. -/
theorem coefficientGaloisKrullTopology_eq_pointwise_of_isAlgebraic (M : Type r) [Monoid M]
    [Algebra.IsAlgebraic k₀ k] :
    coefficientGaloisKrullTopology M k₀ k = coefficientGaloisPointwiseTopology M k₀ k :=
  coefficientGaloisKrullTopology_eq_pointwise M (krullFixingCondition_of_isAlgebraic k₀ k)

variable {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The raw scalar/Galois family fixes a stage and the original common target exactly when
its unit is one and its field automorphism fixes every stage label. No classification or
dimension hypothesis is used. Blueprint: equation (P) of T09 (`thm:t09`). -/
theorem scalarGalois_preimage_stageKernel [Nontrivial R] (A : C.Stage) :
    (fun p : Rˣ × (k ≃ₐ[k₀] k) ↦
      scalarQuadraticAut R C S p.1 * galoisQuadraticAut R C S p.2) ⁻¹'
        (DiagramAut.stageKernel R C S A : Set (DiagramAut R C S)) =
      ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel A : Set (k ≃ₐ[k₀] k)) := by
  ext ⟨a, σ⟩
  change (scalarQuadraticAut R C S a * galoisQuadraticAut R C S σ) ∈
      DiagramAut.stageKernel R C S A ↔ a = 1 ∧ σ ∈ C.galoisStageKernel A
  rw [DiagramAut.mem_stageKernel]
  constructor
  · rintro ⟨hA, hT⟩
    have ha : a = 1 := by
      apply Units.ext
      have he := congrArg (fun f : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R) ↦
        f (Finsupp.single (0 : Fin 2) 1) 0) hT
      simpa using he
    refine ⟨ha, ?_⟩
    simp only [ha, scalarQuadraticAut_one, one_mul] at hA
    change galoisLabelEquiv A.val σ = 1
    apply Equiv.ext
    intro H
    apply Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
    change Finsupp.single (galoisLabelEquiv A.val σ H) (1 : R) = Finsupp.single H 1
    rw [← galoisQuadraticAut_stageEquiv_single R C S σ A H, hA]
    rfl
  · rintro ⟨rfl, hσ⟩
    simp only [scalarQuadraticAut_one, one_mul]
    refine ⟨?_, galoisQuadraticAut_targetEquiv R C S σ⟩
    have hlabel : galoisLabelEquiv A.val σ = 1 := hσ
    apply LinearEquiv.toLinearMap_injective
    apply (Finsupp.basisSingleOne (ι := A.val.val) (R := R)).ext
    intro H
    change (galoisQuadraticAut R C S σ).stageEquiv A (Finsupp.single H 1) = _
    rw [galoisQuadraticAut_stageEquiv_single, Equiv.congr_fun hlabel H]
    rfl

/-- The exact local-ring classifier pulls a complete-stage-and-target kernel back to the
unit identity times the actual geometric stage kernel. Blueprint: T09 (`thm:t09`). -/
theorem quadraticAutEquiv_preimage_stageKernel [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (A : C.Stage) :
    (quadraticAutEquiv R C S hS hgen hn) ⁻¹'
        (DiagramAut.stageKernel R C S A : Set (DiagramAut R C S)) =
      ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel A : Set (k ≃ₐ[k₀] k)) :=
  scalarGalois_preimage_stageKernel R C S A

/-- The exact integral-domain classifier has the same complete kernel preimage.
Blueprint: T09 (`thm:t09`). -/
theorem coefficientDomainAutEquiv_preimage_stageKernel [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (A : C.Stage) :
    (coefficientDomainAutEquiv R C S hS hgen hn) ⁻¹'
        (DiagramAut.stageKernel R C S A : Set (DiagramAut R C S)) =
      ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel A : Set (k ≃ₐ[k₀] k)) :=
  scalarGalois_preimage_stageKernel R C S A

open scoped DiscreteCoefficientUnits FiniteStageTopology

section Pointwise

open scoped GaloisPointwise

private theorem parameter_nhds_one_stageBasis (hn : 1 ≤ n) :
    (𝓝 (1 : Rˣ × (k ≃ₐ[k₀] k))).HasBasis (fun _ : C.Stage ↦ True)
      (fun A ↦ ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel A : Set (k ≃ₐ[k₀] k))) := by
  have hb : (𝓝 (1 : Rˣ × (k ≃ₐ[k₀] k))).HasBasis
      (fun _ : Unit × C.Stage ↦ True ∧ True)
      (fun i ↦ ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel i.2 : Set (k ≃ₐ[k₀] k))) := by
    rw [nhds_prod_eq, nhds_discrete]
    exact (hasBasis_pure (1 : Rˣ)).prod (C.galoisPointwise_nhds_one_stageKernelBasis hn)
  exact hb.to_hasBasis (fun i _ ↦ ⟨i.2, trivial, subset_rfl⟩)
    (fun A _ ↦ ⟨((), A), ⟨trivial, trivial⟩, subset_rfl⟩)

private theorem continuous_of_stageKernels
    (e : (Rˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut R C S) (hn : 1 ≤ n)
    (he : ∀ A : C.Stage,
      e ⁻¹' (DiagramAut.stageKernel R C S A : Set (DiagramAut R C S)) =
        ({1} : Set Rˣ) ×ˢ (C.galoisStageKernel A : Set (k ≃ₐ[k₀] k))) :
    Continuous[coefficientGaloisPointwiseTopology R k₀ k, DiagramAut.stageTopology R C S] e ∧
      Continuous[DiagramAut.stageTopology R C S, coefficientGaloisPointwiseTopology R k₀ k]
        e.symm := by
  constructor
  · apply continuous_of_tendsto_nhds_one e
    apply ((parameter_nhds_one_stageBasis R C hn).tendsto_iff
      (DiagramAut.nhds_one_stageBasis R C S)).mpr
    intro A _
    refine ⟨A, trivial, ?_⟩
    intro p hp
    change p ∈ e ⁻¹' (DiagramAut.stageKernel R C S A : Set _)
    rw [he A]
    exact hp
  · apply continuous_of_tendsto_nhds_one e.symm
    apply ((DiagramAut.nhds_one_stageBasis R C S).tendsto_iff
      (parameter_nhds_one_stageBasis R C hn)).mpr
    intro A _
    refine ⟨A, trivial, ?_⟩
    intro g hg
    rw [← he A]
    simpa only [Set.mem_preimage, e.apply_symm_apply] using hg

/-- The existing local-ring quadratic classifier with both pointwise continuity proofs.
No algebraicity is required. Blueprint: T09 (`thm:t09`). -/
def quadraticAutContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := quadraticAutEquiv R C S hS hgen hn
  continuous_toFun := by
    exact (continuous_of_stageKernels R C S (quadraticAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (quadraticAutEquiv_preimage_stageKernel R C S hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_of_stageKernels R C S (quadraticAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (quadraticAutEquiv_preimage_stageKernel R C S hS hgen hn)).2

/-- Forgetting continuity recovers the exact existing multiplicative equivalence. -/
theorem quadraticAutContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (quadraticAutContinuousEquiv R C S hS hgen hn).toMulEquiv =
      quadraticAutEquiv R C S hS hgen hn := rfl

/-- The underlying function is exactly the existing classifier; this is a plain rewrite. -/
theorem quadraticAutContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (quadraticAutContinuousEquiv R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = quadraticAutEquiv R C S hS hgen hn := rfl

/-- Pointwise comparison with the existing classifier, preserving inverse cancellation. -/
theorem quadraticAutContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    quadraticAutContinuousEquiv R C S hS hgen hn p = quadraticAutEquiv R C S hS hgen hn p := rfl

/-- The inverse returns the original primal unit and original recovered field automorphism. -/
theorem quadraticAutContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (quadraticAutContinuousEquiv R C S hS hgen hn).symm g =
      (g.scalarPart hS hgen hn, DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- The finite-stage generator retains the primal unit and the covariant geometric label. -/
theorem quadraticAutContinuousEquiv_stageEquiv_single [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (u : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val) :
    (quadraticAutContinuousEquiv R C S hS hgen hn (u, σ)).stageEquiv A
        (Finsupp.single H 1) =
      (u : R) • Finsupp.single (galoisLabelEquiv A.val σ H) 1 :=
  quadraticAutEquiv_stageEquiv_single R C S hS hgen hn u σ A H

/-- The single original common target acts by the same primal scalar on every vector. -/
theorem quadraticAutContinuousEquiv_targetEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (u : Rˣ) (σ : k ≃ₐ[k₀] k) (x : Fin 2 →₀ R) :
    (quadraticAutContinuousEquiv R C S hS hgen hn (u, σ)).targetEquiv x = (u : R) • x :=
  quadraticAutEquiv_targetEquiv_apply R C S hS hgen hn u σ x

/-- The existing integral-domain quadratic classifier with both pointwise continuity proofs.
No algebraicity is required. Blueprint: T09 (`thm:t09`). -/
def coefficientDomainAutContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainAutEquiv R C S hS hgen hn
  continuous_toFun := by
    exact (continuous_of_stageKernels R C S (coefficientDomainAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (coefficientDomainAutEquiv_preimage_stageKernel R C S hS hgen hn)).1
  continuous_invFun := by
    exact (continuous_of_stageKernels R C S (coefficientDomainAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (coefficientDomainAutEquiv_preimage_stageKernel R C S hS hgen hn)).2

/-- Forgetting continuity recovers the exact existing multiplicative equivalence. -/
theorem coefficientDomainAutContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn).toMulEquiv =
      coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- The underlying function is exactly the existing classifier; this is a plain rewrite. -/
theorem coefficientDomainAutContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- Pointwise comparison with the existing classifier, preserving inverse cancellation. -/
theorem coefficientDomainAutContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainAutContinuousEquiv R C S hS hgen hn p =
      coefficientDomainAutEquiv R C S hS hgen hn p := rfl

/-- The inverse returns the original primal unit and original recovered field automorphism. -/
theorem coefficientDomainAutContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn).symm g =
      (g.domainScalarPart hS hgen hn, DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- The finite-stage generator retains the primal unit and the covariant geometric label. -/
theorem coefficientDomainAutContinuousEquiv_stageEquiv_single [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (u : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn (u, σ)).stageEquiv A
        (Finsupp.single H 1) =
      (u : R) • Finsupp.single (galoisLabelEquiv A.val σ H) 1 :=
  coefficientDomainAutEquiv_stageEquiv_single R C S hS hgen hn u σ A H

/-- The single original common target acts by the same primal scalar on every vector. -/
theorem coefficientDomainAutContinuousEquiv_targetEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (u : Rˣ) (σ : k ≃ₐ[k₀] k) (x : Fin 2 →₀ R) :
    (coefficientDomainAutContinuousEquiv R C S hS hgen hn (u, σ)).targetEquiv x = (u : R) • x :=
  coefficientDomainAutEquiv_targetEquiv_apply R C S hS hgen hn u σ x

/-- The local and domain topological classifiers agree on their overlap, as actual maps. -/
theorem coefficientDomainAutContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainAutContinuousEquiv R C S hS hgen hn =
      quadraticAutContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change coefficientDomainAutEquiv R C S hS hgen hn p =
    quadraticAutEquiv R C S hS hgen hn p
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv]

end Pointwise

/-- The exact local-ring quadratic classifier with Mathlib's existing Krull topology
under the explicit finite-field fixing condition (K). Blueprint: T09 (`thm:t09`). -/
def quadraticAutKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := quadraticAutEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [coefficientGaloisKrullTopology_eq_pointwise R hK]
    exact (continuous_of_stageKernels R C S (quadraticAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (quadraticAutEquiv_preimage_stageKernel R C S hS hgen hn)).1
  continuous_invFun := by
    rw [coefficientGaloisKrullTopology_eq_pointwise R hK]
    exact (continuous_of_stageKernels R C S (quadraticAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (quadraticAutEquiv_preimage_stageKernel R C S hS hgen hn)).2

/-- Forgetting Krull continuity recovers the exact existing multiplicative equivalence. -/
theorem quadraticAutKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
      quadraticAutEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper has the original underlying function; this is a plain rewrite. -/
theorem quadraticAutKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (quadraticAutKrullContinuousEquiv R C S hS hgen hn hK :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = quadraticAutEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the unchanged existing classifier. -/
theorem quadraticAutKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    quadraticAutKrullContinuousEquiv R C S hS hgen hn hK p =
      quadraticAutEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse has the exact original scalar and Galois coordinates. -/
theorem quadraticAutKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut R C S) :
    (quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).symm g =
      (g.scalarPart hS hgen hn, DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- The exact local-ring quadratic classifier with Mathlib's existing Krull topology
under algebraicity, without normality or separability. Blueprint: T09 (`thm:t09`). -/
def quadraticAutKrullContinuousEquivOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ :=
  quadraticAutKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting Krull continuity recovers the exact existing multiplicative equivalence. -/
theorem quadraticAutKrullContinuousEquivOfIsAlgebraic_toMulEquiv
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
      quadraticAutEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper has the original underlying function; this is a plain rewrite. -/
theorem quadraticAutKrullContinuousEquivOfIsAlgebraic_coe [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = quadraticAutEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the unchanged existing classifier. -/
theorem quadraticAutKrullContinuousEquivOfIsAlgebraic_apply
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p =
      quadraticAutEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse has the exact original scalar and Galois coordinates. -/
theorem quadraticAutKrullContinuousEquivOfIsAlgebraic_symm_apply
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g =
      (g.scalarPart hS hgen hn, DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- The exact domain quadratic classifier with Mathlib's existing Krull topology
under the explicit finite-field fixing condition (K). Blueprint: T09 (`thm:t09`). -/
def coefficientDomainAutKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainAutEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [coefficientGaloisKrullTopology_eq_pointwise R hK]
    exact (continuous_of_stageKernels R C S (coefficientDomainAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (coefficientDomainAutEquiv_preimage_stageKernel R C S hS hgen hn)).1
  continuous_invFun := by
    rw [coefficientGaloisKrullTopology_eq_pointwise R hK]
    exact (continuous_of_stageKernels R C S (coefficientDomainAutEquiv R C S hS hgen hn)
      (le_trans (by decide : 1 ≤ 2) hn)
      (coefficientDomainAutEquiv_preimage_stageKernel R C S hS hgen hn)).2

/-- Forgetting Krull continuity recovers the exact existing multiplicative equivalence. -/
theorem coefficientDomainAutKrullContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
      coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper has the original underlying function; this is a plain rewrite. -/
theorem coefficientDomainAutKrullContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the unchanged existing classifier. -/
theorem coefficientDomainAutKrullContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK p =
      coefficientDomainAutEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse has the exact original scalar and Galois coordinates. -/
theorem coefficientDomainAutKrullContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut R C S) :
    (coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).symm g =
      (g.domainScalarPart hS hgen hn, DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- The exact domain quadratic classifier with Mathlib's existing Krull topology
under algebraicity, without normality or separability. Blueprint: T09 (`thm:t09`). -/
def coefficientDomainAutKrullContinuousEquivOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ :=
  coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting Krull continuity recovers the exact existing multiplicative equivalence. -/
theorem coefficientDomainAutKrullContinuousEquivOfIsAlgebraic_toMulEquiv
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
      coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper has the original underlying function; this is a plain rewrite. -/
theorem coefficientDomainAutKrullContinuousEquivOfIsAlgebraic_coe
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → DiagramAut R C S) = coefficientDomainAutEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the unchanged existing classifier. -/
theorem coefficientDomainAutKrullContinuousEquivOfIsAlgebraic_apply
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p =
      coefficientDomainAutEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse has the exact original scalar and Galois coordinates. -/
theorem coefficientDomainAutKrullContinuousEquivOfIsAlgebraic_symm_apply
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g =
      (g.domainScalarPart hS hgen hn, DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- The local and domain topological classifiers agree on their overlap, as actual maps. -/
theorem coefficientDomainAutKrullContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK =
      quadraticAutKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change coefficientDomainAutEquiv R C S hS hgen hn p =
    quadraticAutEquiv R C S hS hgen hn p
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv]

/-- The local and domain topological classifiers agree on their overlap, as actual maps. -/
theorem coefficientDomainAutKrullContinuousEquivOfIsAlgebraic_eq_local
    [IsDomain R] [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn =
      quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change coefficientDomainAutEquiv R C S hS hgen hn p =
    quadraticAutEquiv R C S hS hgen hn p
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv]

end OrlikSolomon.HyperplaneGT
