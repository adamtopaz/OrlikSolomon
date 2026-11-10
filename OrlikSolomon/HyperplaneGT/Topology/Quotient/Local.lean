/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Classification.Graded
public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact

/-!
# Local-ring scalar quotients with their actual quotient topology

The old quadratic and graded scalar quotients carry Mathlib's quotient topology of the
direct finite-stage diagram topology. The existing local-ring Galois equivalences gain both
continuity proofs. Their inverse sections are the old direct Galois families modulo the
literal scalar ranges. Krull versions require the exact fixing condition or algebraicity.

Scalar ranges are closed, and both quotients are compact, Hausdorff and totally separated
under the original classification hypotheses alone. Compactness uses the supplied stable
system in positive dimension, not algebraicity or finite coefficient units. These structure
proofs are theorems rather than global instances. No quotient topology is defined through
classification, no global topology instance is added, and the old groups are unchanged.

## Main definitions and results

* `DiagramAut.scalarQuotientContinuousEquiv` and the graded version retain the exact old maps.
* Their Krull and algebraic wrappers retain Mathlib's actual Krull topology.
* The scalar closedness and quotient separation/compactness theorems give profiniteness.
* `scalarQuotientRestrictionContinuousEquiv` retains the old degree-one quotient restriction.

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

/-- The actual scalar quotient projection is continuous over every commutative ring,
in every dimension and without classification. -/
theorem DiagramAut.continuous_scalarQuotientMap :
    Continuous (DiagramAut.scalarQuotientMap R C S) :=
  QuotientGroup.continuous_mk

/-- The actual scalar quotient projection is continuous over every commutative ring,
in every dimension and without classification. -/
theorem GradedDiagramAut.continuous_scalarQuotientMap :
    Continuous (GradedDiagramAut.scalarQuotientMap R C S) :=
  QuotientGroup.continuous_mk

section Pointwise

open scoped GaloisPointwise

namespace DiagramAut

/-- The recovered Galois coordinate is continuous for the pointwise field topology. -/
theorem continuous_toGalois [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @Continuous (DiagramAut R C S) (k ≃ₐ[k₀] k)
      (DiagramAut.stageTopology R C S) (galoisPointwiseTopology k₀ k)
      (toGalois R C S hS hgen hn) := by
  change Continuous (fun g : DiagramAut R C S ↦
    ((quadraticAutContinuousEquiv R C S hS hgen hn).symm g).2)
  exact continuous_snd.comp (quadraticAutContinuousEquiv R C S hS hgen hn).symm.continuous

/-- The exact old local-ring scalar quotient equivalence with both quotient-topology
continuity proofs. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut R C S ↦
      scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g))
    simp only [scalarQuotientEquiv_map]
    exact continuous_toGalois R C S hS hgen hn
  continuous_invFun := by
    change Continuous (fun σ : k ≃ₐ[k₀] k ↦ (scalarQuotientEquiv R C S hS hgen hn).symm σ)
    simp only [scalarQuotientEquiv_symm_apply, scalarQuotientSection_apply]
    have hpair : Continuous (fun σ : k ≃ₐ[k₀] k ↦ ((1 : Rˣ), σ)) :=
      continuous_const.prodMk continuous_id
    have hsection : Continuous (fun σ : k ≃ₐ[k₀] k ↦ scalarQuotientMap R C S
        (quadraticAutContinuousEquiv R C S hS hgen hn (1, σ))) :=
      (continuous_scalarQuotientMap R C S).comp
        ((quadraticAutContinuousEquiv R C S hS hgen hn).continuous.comp hpair)
    simpa only [quadraticAutContinuousEquiv_apply, quadraticAutEquiv_apply,
    scalarQuadraticAut_one, one_mul] using hsection

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).toMulEquiv = scalarQuotientEquiv R C S hS
    hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    scalarQuotientContinuousEquiv R C S hS hgen hn q = scalarQuotientEquiv R C S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    scalarQuotientContinuousEquiv R C S hS hgen hn (scalarQuotientMap R C S g) = toGalois R C S hS
    hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientMap R C S
    (galoisQuadraticAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The literal scalar range is closed, without identifying it with the full center.
Blueprint: T11 (`thm:t11`). -/
theorem isClosed_scalarSubgroup [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    IsClosed (scalarSubgroup R C S : Set (DiagramAut R C S)) := by
  rw [← ker_toGalois R C S hS hgen hn]
  change IsClosed ((toGalois R C S hS hgen hn) ⁻¹' ({1} : Set (k ≃ₐ[k₀] k)))
  exact isClosed_singleton.preimage (continuous_toGalois R C S hS hgen hn)

/-- The actual scalar quotient is Hausdorff under the original classification hypotheses. -/
theorem scalarQuotient_t2Space [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    T2Space (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  (scalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The actual scalar quotient is compact from the supplied stable system; algebraicity
and finiteness of coefficient units are not required. Blueprint: T11 (`thm:t11`). -/
theorem scalarQuotient_compactSpace [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    CompactSpace (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (scalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The actual scalar quotient is totally separated, completing its profinite properties. -/
theorem scalarQuotient_totallySeparatedSpace [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    TotallySeparatedSpace (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) := by
  let e := scalarQuotientContinuousEquiv R C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

end DiagramAut

namespace GradedDiagramAut

/-- The recovered Galois coordinate is continuous for the pointwise field topology. -/
theorem continuous_toGalois [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @Continuous (GradedDiagramAut R C S) (k ≃ₐ[k₀] k)
      (GradedDiagramAut.stageTopology R C S) (galoisPointwiseTopology k₀ k)
      (toGalois R C S hS hgen hn) := by
  change Continuous (fun g : GradedDiagramAut R C S ↦
    ((gradedClassificationContinuousEquiv R C S hS hgen hn).symm g).2)
  exact continuous_snd.comp (gradedClassificationContinuousEquiv R C S hS hgen hn).symm.continuous

/-- The exact old local-ring scalar quotient equivalence with both quotient-topology
continuity proofs. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut R C S ↦
      scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g))
    simp only [scalarQuotientEquiv_map]
    exact continuous_toGalois R C S hS hgen hn
  continuous_invFun := by
    change Continuous (fun σ : k ≃ₐ[k₀] k ↦ (scalarQuotientEquiv R C S hS hgen hn).symm σ)
    simp only [scalarQuotientEquiv_symm_apply, scalarQuotientSection_apply]
    have hpair : Continuous (fun σ : k ≃ₐ[k₀] k ↦ ((1 : Rˣ), σ)) :=
      continuous_const.prodMk continuous_id
    have hsection : Continuous (fun σ : k ≃ₐ[k₀] k ↦ scalarQuotientMap R C S
        (gradedClassificationContinuousEquiv R C S hS hgen hn (1, σ))) :=
      (continuous_scalarQuotientMap R C S).comp
        ((gradedClassificationContinuousEquiv R C S hS hgen hn).continuous.comp hpair)
    simpa only [gradedClassificationContinuousEquiv_apply, gradedClassificationEquiv_apply,
    scalarGradedAut_one, one_mul] using hsection

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).toMulEquiv = scalarQuotientEquiv R C S hS
    hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn : (GradedDiagramAut R C S ⧸
    GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    scalarQuotientContinuousEquiv R C S hS hgen hn q = scalarQuotientEquiv R C S hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    scalarQuotientContinuousEquiv R C S hS hgen hn (scalarQuotientMap R C S g) = toGalois R C S hS
    hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientContinuousEquiv R C S hS hgen hn).symm σ = scalarQuotientMap R C S
    (galoisGradedAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The literal scalar range is closed, without identifying it with the full center.
Blueprint: T11 (`thm:t11`). -/
theorem isClosed_scalarSubgroup [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    IsClosed (scalarSubgroup R C S : Set (GradedDiagramAut R C S)) := by
  rw [← ker_toGalois R C S hS hgen hn]
  change IsClosed ((toGalois R C S hS hgen hn) ⁻¹' ({1} : Set (k ≃ₐ[k₀] k)))
  exact isClosed_singleton.preimage (continuous_toGalois R C S hS hgen hn)

/-- The actual scalar quotient is Hausdorff under the original classification hypotheses. -/
theorem scalarQuotient_t2Space [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    T2Space (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :=
  (scalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.t2Space

/-- The actual scalar quotient is compact from the supplied stable system; algebraicity
and finiteness of coefficient units are not required. Blueprint: T11 (`thm:t11`). -/
theorem scalarQuotient_compactSpace [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    CompactSpace (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  let := C.galoisPointwise_compactSpace (le_trans (by decide : 1 ≤ 2) hn)
  exact (scalarQuotientContinuousEquiv R C S hS hgen hn).symm.toHomeomorph.compactSpace

/-- The actual scalar quotient is totally separated, completing its profinite properties. -/
theorem scalarQuotient_totallySeparatedSpace [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    TotallySeparatedSpace (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) := by
  let e := scalarQuotientContinuousEquiv R C S hS hgen hn
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hxy' : e x ≠ e y := fun he ↦ hxy (e.injective he)
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hxy'
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, hy⟩

end GradedDiagramAut

end Pointwise

namespace DiagramAut

/-- The exact old local-ring scalar quotient equivalence with Mathlib's actual Krull
topology, under the explicit fixing condition. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (scalarQuotientContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (scalarQuotientContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv = scalarQuotientEquiv R C
    S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q = scalarQuotientEquiv R C S hS hgen
    hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientSection R C S
    σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : DiagramAut R C S) :
    scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK (scalarQuotientMap R C S g) = toGalois
    R C S hS hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientKrullContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientMap R C S
    (galoisQuadraticAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The exact old local-ring scalar quotient equivalence with Mathlib's actual Krull
topology, under algebraicity. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientKrullContinuousEquivOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS
    : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  scalarQuotientKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
    scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn : (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q = scalarQuotientEquiv R C S
    hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientSection R C S σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn (scalarQuotientMap R C S g) =
    toGalois R C S hS hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ = scalarQuotientMap
    R C S (galoisQuadraticAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

end DiagramAut

namespace GradedDiagramAut

/-- The exact old local-ring scalar quotient equivalence with Mathlib's actual Krull
topology, under the explicit fixing condition. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ where
  toMulEquiv := scalarQuotientEquiv R C S hS hgen hn
  continuous_toFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (scalarQuotientContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    rw [(krull_eq_pointwise_iff k₀ k).mpr hK]
    let _ : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    exact (scalarQuotientContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv = scalarQuotientEquiv R C
    S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK : (GradedDiagramAut R C S ⧸
    GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q = scalarQuotientEquiv R C S hS hgen
    hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientSection R C S
    σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut R C S) :
    scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK (scalarQuotientMap R C S g) = toGalois
    R C S hS hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientKrullContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK).symm σ = scalarQuotientMap R C S
    (galoisGradedAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- The exact old local-ring scalar quotient equivalence with Mathlib's actual Krull
topology, under algebraicity. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientKrullContinuousEquivOfIsAlgebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS
    : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ _ :=
  scalarQuotientKrullContinuousEquiv R C S hS hgen hn
    (krullFixingCondition_of_isAlgebraic k₀ k)

/-- Forgetting continuity recovers exactly the original M8 quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_toMulEquiv [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
    scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The underlying forward function is the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_coe [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn : (GradedDiagramAut R C S ⧸
    GradedDiagramAut.scalarSubgroup R C S) → (k ≃ₐ[k₀] k)) =
      scalarQuotientEquiv R C S hS hgen hn := rfl

/-- The topological wrapper evaluates by the original quotient equivalence. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_apply [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q = scalarQuotientEquiv R C S
    hS hgen hn q := rfl

/-- The inverse is the existing direct Galois class section. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_apply [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ =
    scalarQuotientSection R C S σ :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

/-- On actual representatives the forward map is exactly the recovered Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_map [IsLocalRing R] [Algebra.IsAlgebraic
    k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn (scalarQuotientMap R C S g) =
    toGalois R C S hS hgen hn g :=
  scalarQuotientEquiv_map R C S hS hgen hn g

/-- The inverse class has the existing direct Galois family as its representative. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_symm_map [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm σ = scalarQuotientMap
    R C S (galoisGradedAut R C S σ) :=
  scalarQuotientEquiv_symm_apply R C S hS hgen hn σ

end GradedDiagramAut

/-- The old quotient restriction's inverse retains the old inverse graded representative. -/
theorem scalarQuotientRestrictionEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (scalarQuotientRestrictionEquiv R C S hS hgen hn).symm (DiagramAut.scalarQuotientMap R C S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((gradedAutEquiv R C S hS hgen hn).symm g) := by
  apply (scalarQuotientRestrictionEquiv R C S hS hgen hn).injective
  rw [MulEquiv.apply_symm_apply, scalarQuotientRestrictionEquiv_map]
  change DiagramAut.scalarQuotientMap R C S g = DiagramAut.scalarQuotientMap R C S
    (gradedAutEquiv R C S hS hgen hn ((gradedAutEquiv R C S hS hgen hn).symm g))
  rw [MulEquiv.apply_symm_apply]

/-- The original local-ring degree-one quotient restriction with both continuity proofs.
No K or algebraicity is required. Blueprint: T11 (`thm:t11`). -/
def scalarQuotientRestrictionContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (GradedDiagramAut R C S)
        (GradedDiagramAut.stageTopology R C S) _ (GradedDiagramAut.scalarSubgroup R C S))
      (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
      (@QuotientGroup.instTopologicalSpace (DiagramAut R C S)
        (DiagramAut.stageTopology R C S) _ (DiagramAut.scalarSubgroup R C S)) _ _ where
  toMulEquiv := scalarQuotientRestrictionEquiv R C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (GradedDiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut R C S ↦
      scalarQuotientRestrictionEquiv R C S hS hgen hn (GradedDiagramAut.scalarQuotientMap R C S g))
    simp only [scalarQuotientRestrictionEquiv_map]
    exact (DiagramAut.continuous_scalarQuotientMap R C S).comp
      (gradedAutContinuousEquiv R C S hS hgen hn).continuous_toFun
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (DiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut R C S ↦
      (scalarQuotientRestrictionEquiv R C S hS hgen hn).symm (DiagramAut.scalarQuotientMap R C S g))
    simp only [scalarQuotientRestrictionEquiv_symm_map]
    exact (GradedDiagramAut.continuous_scalarQuotientMap R C S).comp
      (gradedAutContinuousEquiv R C S hS hgen hn).continuous_invFun

/-- Forgetting quotient continuity recovers the original degree-one quotient restriction. -/
theorem scalarQuotientRestrictionContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).toMulEquiv =
      scalarQuotientRestrictionEquiv R C S hS hgen hn := rfl

/-- The topological quotient restriction has the original underlying function. -/
theorem scalarQuotientRestrictionContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn :
      (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) → (DiagramAut R C S ⧸
    DiagramAut.scalarSubgroup R C S)) =
        scalarQuotientRestrictionEquiv R C S hS hgen hn := rfl

/-- Applying the wrapper is the original quotient restriction. -/
theorem scalarQuotientRestrictionContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q =
      scalarQuotientRestrictionEquiv R C S hS hgen hn q := rfl

/-- Its inverse is the original inverse quotient restriction. -/
theorem scalarQuotientRestrictionContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)) :
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).symm q =
      (scalarQuotientRestrictionEquiv R C S hS hgen hn).symm q := rfl

/-- On representatives the quotient map is the literal degree-one restriction. -/
theorem scalarQuotientRestrictionContinuousEquiv_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn (GradedDiagramAut.scalarQuotientMap
    R C S g) =
      DiagramAut.scalarQuotientMap R C S (GradedDiagramAut.toQuadratic R C S g) :=
  scalarQuotientRestrictionEquiv_map R C S hS hgen hn g

/-- Inverse representatives use the original graded extension. -/
theorem scalarQuotientRestrictionContinuousEquiv_symm_map [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn).symm (DiagramAut.scalarQuotientMap
    R C S g) =
      GradedDiagramAut.scalarQuotientMap R C S ((gradedAutEquiv R C S hS hgen hn).symm g) :=
  scalarQuotientRestrictionEquiv_symm_map R C S hS hgen hn g

section PointwiseRestriction

open scoped GaloisPointwise

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem scalarQuotientContinuousEquiv_restriction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.scalarQuotientContinuousEquiv R C S hS hgen hn q :=
  scalarQuotientEquiv_restriction R C S hS hgen hn q

end PointwiseRestriction

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem scalarQuotientKrullContinuousEquiv_restriction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.scalarQuotientKrullContinuousEquiv R C S hS hgen hn hK q :=
  scalarQuotientEquiv_restriction R C S hS hgen hn q

/-- Both Galois quotient coordinates commute with the original degree-one restriction. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_restriction [IsLocalRing R]
    [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S)) :
    DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn
    (scalarQuotientRestrictionContinuousEquiv R C S hS hgen hn q) =
      GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn q :=
  scalarQuotientEquiv_restriction R C S hS hgen hn q

end OrlikSolomon.HyperplaneGT
