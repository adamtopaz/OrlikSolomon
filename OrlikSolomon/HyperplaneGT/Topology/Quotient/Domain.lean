/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Quotient.Local

/-!
# Domain scalar quotients with their actual quotient topology

The old quadratic and graded scalar quotients carry Mathlib's quotient topology of the
direct finite-stage diagram topology. The existing domain Galois equivalences gain both
continuity proofs. Their inverse sections are the old direct Galois families modulo the
literal scalar ranges. Krull versions require the exact fixing condition or algebraicity.

Scalar ranges are closed, and both quotients are compact, Hausdorff and totally separated
under the original classification hypotheses alone. Compactness uses the supplied stable
system in positive dimension, not algebraicity or finite coefficient units. These structure
proofs are theorems rather than global instances. No quotient topology is defined through
classification, no global topology instance is added, and the old groups are unchanged.

## Main definitions and results

* `DiagramAut.domainScalarQuotientContinuousEquiv` and the graded version retain the exact old maps.
* Their Krull and algebraic wrappers retain Mathlib's actual Krull topology.
* The scalar closedness and quotient separation/compactness theorems give profiniteness.
* `domainScalarQuotientRestrictionContinuousEquiv` retains the old degree-one quotient restriction.

Blueprint: T11 (`thm:t11`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Topology
open scoped DiscreteCoefficientUnits FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

section Pointwise

open scoped GaloisPointwise

namespace DiagramAut

/-- The recovered Galois coordinate is continuous for the pointwise field topology. -/
theorem continuous_domainToGalois [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @Continuous (DiagramAut R C S) (k ≃ₐ[k₀] k)
      (DiagramAut.stageTopology R C S) (galoisPointwiseTopology k₀ k)
      (domainToGalois R C S hS hgen hn) := by
  change Continuous (fun g : DiagramAut R C S ↦
    ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).symm g).2)
  exact continuous_snd.comp (coefficientDomainAutContinuousEquiv R C S hS hgen hn).symm.continuous

/-- The exact old domain scalar quotient equivalence with both quotient-topology
continuity proofs. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut R C S ↦
      domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g))
    simp only [domainScalarQuotientEquiv_map]
    exact continuous_domainToGalois R C S hS hgen hn
  continuous_invFun := by
    change Continuous (fun σ : k ≃ₐ[k₀] k ↦ (domainScalarQuotientEquiv R C S hS hgen hn).symm σ)
    simp only [domainScalarQuotientEquiv_symm_apply, scalarQuotientSection_apply]
    have hpair : Continuous (fun σ : k ≃ₐ[k₀] k ↦ ((1 : Rˣ), σ)) :=
      continuous_const.prodMk continuous_id
    have hsection : Continuous (fun σ : k ≃ₐ[k₀] k ↦ scalarQuotientMap R C S
        (coefficientDomainAutContinuousEquiv R C S hS hgen hn (1, σ))) :=
      (continuous_scalarQuotientMap R C S).comp
        ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).continuous.comp hpair)
    simpa only [coefficientDomainAutContinuousEquiv_apply, coefficientDomainAutEquiv_apply,
    scalarQuadraticAut_one, one_mul] using hsection

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).toMulEquiv = domainScalarQuotientEquiv
    R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientContinuousEquiv R C S hS hgen hn q = domainScalarQuotientEquiv R C S hS
    hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    domainScalarQuotientContinuousEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
    domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientMap R C S
    (galoisQuadraticAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The literal scalar range is closed, without identifying it with the full center.
Blueprint: T11 (`thm:t11`). -/
theorem isClosed_scalarSubgroup_of_isDomain [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    IsClosed (scalarSubgroup R C S : Set (DiagramAut R C S)) := by
  rw [← ker_domainToGalois R C S hS hgen hn]
  change IsClosed ((domainToGalois R C S hS hgen hn) ⁻¹' ({1} : Set (k ≃ₐ[k₀] k)))
  exact isClosed_singleton.preimage (continuous_domainToGalois R C S hS hgen hn)

/-- The actual scalar quotient is Hausdorff under the original classification hypotheses. -/
theorem domainScalarQuotient_t2Space [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    T2Space (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The actual scalar quotient is compact from the supplied stable system; algebraicity
and finiteness of coefficient units are not required. Blueprint: T11 (`thm:t11`). -/
theorem domainScalarQuotient_compactSpace [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    CompactSpace (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The actual scalar quotient is totally separated, completing its profinite properties. -/
theorem domainScalarQuotient_totallySeparatedSpace [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    TotallySeparatedSpace (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  let e := domainScalarQuotientContinuousEquiv R C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

end DiagramAut

namespace GradedDiagramAut

/-- The recovered Galois coordinate is continuous for the pointwise field topology. -/
theorem continuous_domainToGalois [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @Continuous (GradedDiagramAut R C S) (k ≃ₐ[k₀] k)
      (GradedDiagramAut.stageTopology R C S) (galoisPointwiseTopology k₀ k)
      (domainToGalois R C S hS hgen hn) := by
  change Continuous (fun g : GradedDiagramAut R C S ↦
    ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).symm g).2)
  exact continuous_snd.comp (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen
    hn).symm.continuous

/-- The exact old domain scalar quotient equivalence with both quotient-topology
continuity proofs. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut R C S ↦
      domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g))
    simp only [domainScalarQuotientEquiv_map]
    exact continuous_domainToGalois R C S hS hgen hn
  continuous_invFun := by
    change Continuous (fun σ : k ≃ₐ[k₀] k ↦ (domainScalarQuotientEquiv R C S hS hgen hn).symm σ)
    simp only [domainScalarQuotientEquiv_symm_apply, scalarQuotientSection_apply]
    have hpair : Continuous (fun σ : k ≃ₐ[k₀] k ↦ ((1 : Rˣ), σ)) :=
      continuous_const.prodMk continuous_id
    have hsection : Continuous (fun σ : k ≃ₐ[k₀] k ↦ scalarQuotientMap R C S
        (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (1, σ))) :=
      (continuous_scalarQuotientMap R C S).comp
        ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).continuous.comp
    hpair)
    simpa only [coefficientDomainGradedClassificationContinuousEquiv_apply,
    coefficientDomainGradedClassificationEquiv_apply, scalarGradedAut_one, one_mul] using hsection

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).toMulEquiv = domainScalarQuotientEquiv
    R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn : (GradedDiagramAut R C S ⧸
    GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientContinuousEquiv R C S hS hgen hn q = domainScalarQuotientEquiv R C S hS
    hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    domainScalarQuotientContinuousEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
    domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientMap R C S
    (galoisGradedAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The literal scalar range is closed, without identifying it with the full center.
Blueprint: T11 (`thm:t11`). -/
theorem isClosed_scalarSubgroup_of_isDomain [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    IsClosed (scalarSubgroup R C S : Set (GradedDiagramAut R C S)) := by
  rw [← ker_domainToGalois R C S hS hgen hn]
  change IsClosed ((domainToGalois R C S hS hgen hn) ⁻¹' ({1} : Set (k ≃ₐ[k₀] k)))
  exact isClosed_singleton.preimage (continuous_domainToGalois R C S hS hgen hn)

/-- The actual scalar quotient is Hausdorff under the original classification hypotheses. -/
theorem domainScalarQuotient_t2Space [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    T2Space (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :=
  (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The actual scalar quotient is compact from the supplied stable system; algebraicity
and finiteness of coefficient units are not required. Blueprint: T11 (`thm:t11`). -/
theorem domainScalarQuotient_compactSpace [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    CompactSpace (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The actual scalar quotient is totally separated, completing its profinite properties. -/
theorem domainScalarQuotient_totallySeparatedSpace [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    TotallySeparatedSpace (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  let e := domainScalarQuotientContinuousEquiv R C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

end GradedDiagramAut

end Pointwise

namespace DiagramAut

/-- The exact old domain scalar quotient equivalence with Mathlib's actual Krull
topology, under the explicit fixing condition. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
    domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q = domainScalarQuotientEquiv R C
    S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientSection
    R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientKrullContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut R C S) :
    domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK (scalarQuotientMap R C S g) =
    domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientMap R C
    S (galoisQuadraticAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The exact old domain scalar quotient equivalence with Mathlib's actual Krull
topology, under algebraicity. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
    domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q =
    domainScalarQuotientEquiv R C S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientSection R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn (scalarQuotientMap R C
    S g) = domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientMap R C S (galoisQuadraticAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

end DiagramAut

namespace GradedDiagramAut

/-- The exact old domain scalar quotient equivalence with Mathlib's actual Krull
topology, under the explicit fixing condition. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := domainScalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (domainScalarQuotientContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
    domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK : (GradedDiagramAut R C S ⧸
    GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q = domainScalarQuotientEquiv R C
    S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientSection
    R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientKrullContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut R C S) :
    domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK (scalarQuotientMap R C S g) =
    domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientKrullContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientMap R C
    S (galoisGradedAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The exact old domain scalar quotient equivalence with Mathlib's actual Krull
topology, under algebraicity. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientKrullContinuousEquivOfIsAlgebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
    domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn : (GradedDiagramAut R
    C S ⧸ GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      domainScalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q =
    domainScalarQuotientEquiv R C S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientSection R C S σ :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn (scalarQuotientMap R C
    S g) = domainToGalois R C S hS hgen hn g :=
  domainScalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientMap R C S (galoisGradedAut R C S σ) :=
  domainScalarQuotientEquiv_symm_apply R C S hS hgen hn σ

end GradedDiagramAut

/-- The old quotient restriction's inverse retains the old inverse graded representative. -/
theorem domainScalarQuotientRestrictionEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (domainScalarQuotientRestrictionEquiv R C S hS hgen hn).symm (DiagramAut.scalarQuotientMap R C
    S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((coefficientDomainGradedAutEquiv R C S hS hgen
    hn).symm g) := by
  apply (domainScalarQuotientRestrictionEquiv R C S hS hgen hn).injective
  rw [MulEquiv.apply_symm_apply, domainScalarQuotientRestrictionEquiv_map]
  change DiagramAut.scalarQuotientMap R C S g = DiagramAut.scalarQuotientMap R C S
    (coefficientDomainGradedAutEquiv R C S hS hgen hn ((coefficientDomainGradedAutEquiv R C S hS
    hgen hn).symm g))
  rw [MulEquiv.apply_symm_apply]

/-- The original domain degree-one quotient restriction with both continuity proofs.
No K or algebraicity is required. Blueprint: T11 (`thm:t11`). -/
def domainScalarQuotientRestrictionContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S)) _ _ where
  toMulEquiv := domainScalarQuotientRestrictionEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (GradedDiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut R C S ↦
      domainScalarQuotientRestrictionEquiv R C S hS hgen hn (GradedDiagramAut.scalarQuotientMap R
    C S g))
    simp only [domainScalarQuotientRestrictionEquiv_map]
    exact (DiagramAut.continuous_scalarQuotientMap R C S).comp
      (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (DiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut R C S ↦
      (domainScalarQuotientRestrictionEquiv R C S hS hgen hn).symm (DiagramAut.scalarQuotientMap R
    C S g))
    simp only [domainScalarQuotientRestrictionEquiv_symm_map]
    exact (GradedDiagramAut.continuous_scalarQuotientMap R C S).comp
      (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting quotient continuity recovers the original degree-one quotient restriction. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).toMulEquiv =
      domainScalarQuotientRestrictionEquiv R C S hS hgen hn := rfl

/-- The topological quotient restriction has the original underlying function. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn :
      (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) → (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S)) =
        domainScalarQuotientRestrictionEquiv R C S hS hgen hn := rfl

/-- Applying the wrapper is the original quotient restriction. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q =
      domainScalarQuotientRestrictionEquiv R C S hS hgen hn q := rfl

/-- Its inverse is the original inverse quotient restriction. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).symm q =
      (domainScalarQuotientRestrictionEquiv R C S hS hgen hn).symm q := rfl

/-- On representatives the quotient map is the literal degree-one restriction. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn
    (GradedDiagramAut.scalarQuotientMap R C S g) =
      DiagramAut.scalarQuotientMap R C S (GradedDiagramAut.toQuadratic R C S g) :=
  domainScalarQuotientRestrictionEquiv_map R C S hS hgen hn g

/-- Inverse representatives use the original graded extension. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_symm_map [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).symm
    (DiagramAut.scalarQuotientMap R C S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((coefficientDomainGradedAutEquiv R C S hS hgen
    hn).symm g) :=
  domainScalarQuotientRestrictionEquiv_symm_map R C S hS hgen hn g

section PointwiseRestriction

open scoped GaloisPointwise

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem domainScalarQuotientContinuousEquiv_restriction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen hn
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen hn q :=
  domainScalarQuotientEquiv_restriction R C S hS hgen hn q

end PointwiseRestriction

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem domainScalarQuotientKrullContinuousEquiv_restriction [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q :=
  domainScalarQuotientEquiv_restriction R C S hS hgen hn q

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_restriction [IsDomain R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
    (domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q :=
  domainScalarQuotientEquiv_restriction R C S hS hgen hn q

section PointwiseOverlap

open scoped GaloisPointwise

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem DiagramAut.domainScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R] (hS :
    (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen hn =
    DiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

end PointwiseOverlap

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem DiagramAut.domainScalarQuotientKrullContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    DiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK =
    DiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_local [IsDomain R]
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn =
    DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

section PointwiseOverlap

open scoped GaloisPointwise

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainScalarQuotientContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut.domainScalarQuotientContinuousEquiv R C S hS hgen hn =
    GradedDiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

end PointwiseOverlap

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv_eq_local [IsDomain R]
    [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquiv R C S hS hgen hn hK =
    GradedDiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

/-- The quotient homeomorphisms agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic_eq_local [IsDomain
    R] [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut.domainScalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn =
    GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn) q

/-- Degree-one quotient restriction agrees on the local/domain overlap. -/
theorem domainScalarQuotientRestrictionContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientRestrictionContinuousEquiv R C S hS hgen hn =
      scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro q
  exact DFunLike.congr_fun
    (domainScalarQuotientRestrictionEquiv_eq_scalarQuotientRestrictionEquiv R C S hS hgen hn) q

end OrlikSolomon.HyperplaneGT
