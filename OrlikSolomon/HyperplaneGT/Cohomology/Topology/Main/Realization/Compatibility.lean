/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Realization.Basic

/-!
# Classification coordinates and realization comparison

The canonical realization homeomorphisms preserve the original unit and Galois
coordinates and commute with the actual classified cofinal restrictions. These identities
retain exactly the old local/domain, dimension and generating-marking hypotheses.
The realization homeomorphisms themselves need none of those additional hypotheses.

Pointwise and exact-K/algebraic classifier compatibility holds as equality of the actual
continuous multiplicative equivalences, retaining their original parameters. The Krull
comparisons alone use the corresponding fixing condition or algebraicity.

Expansion equations are plain rewrite rules, preserving ordinary inverse cancellation.
Blueprint: the classification compatibility clauses of T16 (`thm:t16`).
-/

@[expose] public section

noncomputable section

universe u v r b₁ b₂ h₁ h₂

namespace OrlikSolomon.HyperplaneGT.Cohomology

open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R]
  {B₁ : Type b₁} [CommRing B₁] [Algebra R B₁]
  {ℬ₁ : ℤ → Submodule R B₁} [GradedAlgebra ℬ₁] {D₁ : Geometric.SmoothDomain k}
  {B₂ : Type b₂} [CommRing B₂] [Algebra R B₂]
  {ℬ₂ : ℤ → Submodule R B₂} [GradedAlgebra ℬ₂] {D₂ : Geometric.SmoothDomain k}
  (T₁ : Geometric.OrdinaryTheory.{u, r, b₁, h₁} D₁ ℬ₁)
  (T₂ : Geometric.OrdinaryTheory.{u, r, b₂, h₂} D₂ ℬ₂)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)


/-- Realization comparison preserves the same local unit and Galois parameters. -/
theorem realizationQuadraticContinuousEquiv_localQuadraticReconstruction [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S (localQuadraticReconstruction T₁ C S hS hgen hn
      p) =
      localQuadraticReconstruction T₂ C S hS hgen hn p :=
  realizationQuadraticAutEquiv_localQuadraticReconstruction T₁ T₂ C S hS hgen hn p

/-- The original inverse classifier recovers the same parameters after changing realization. -/
theorem realizationQuadraticContinuousEquiv_localQuadraticReconstruction_symm [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T₁ C S) :
    (localQuadraticReconstruction T₂ C S hS hgen hn).symm (realizationQuadraticContinuousEquiv T₁
      T₂ C S g) =
      (localQuadraticReconstruction T₁ C S hS hgen hn).symm g := by
  obtain ⟨p, rfl⟩ := (localQuadraticReconstruction T₁ C S hS hgen hn).surjective g
  rw [realizationQuadraticContinuousEquiv_localQuadraticReconstruction,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- The same local Galois coordinate is recovered from either actual scalar quotient. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_localScalarQuotientEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T₁ C S ⧸
      DiagramAut.scalarSubgroup T₁ C S) :
    DiagramAut.localScalarQuotientEquiv T₂ C S hS hgen hn
      (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S q) =
      DiagramAut.localScalarQuotientEquiv T₁ C S hS hgen hn q :=
  realizationQuadraticScalarQuotientEquiv_localScalarQuotientEquiv T₁ T₂ C S hS hgen hn q

/-- The original local cofinal equivalence commutes with canonical realization comparison. -/
theorem realizationQuadraticContinuousEquiv_cofinalRestrictionEquiv [IsLocalRing R]
    (C' : CofinalSystem k₀ k n) (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T₁ C S) :
    realizationQuadraticContinuousEquiv T₁ T₂ C' S (cofinalRestrictionEquiv T₁ C C' S hC hS hgen
      hn g) =
      cofinalRestrictionEquiv T₂ C C' S hC hS hgen hn (realizationQuadraticContinuousEquiv T₁ T₂
        C S g) := by
  rw [cofinalRestrictionEquiv_apply, cofinalRestrictionEquiv_apply]
  exact realizationQuadraticContinuousEquiv_restrictStages T₁ T₂ C S C' hC g

/-- Realization comparison preserves the same domain unit and Galois parameters. -/
theorem realizationQuadraticContinuousEquiv_domainQuadraticReconstruction [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    realizationQuadraticContinuousEquiv T₁ T₂ C S (domainQuadraticReconstruction T₁ C S hS hgen
      hn p) =
      domainQuadraticReconstruction T₂ C S hS hgen hn p :=
  realizationQuadraticAutEquiv_domainQuadraticReconstruction T₁ T₂ C S hS hgen hn p

/-- The original inverse classifier recovers the same parameters after changing realization. -/
theorem realizationQuadraticContinuousEquiv_domainQuadraticReconstruction_symm [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T₁ C S) :
    (domainQuadraticReconstruction T₂ C S hS hgen hn).symm (realizationQuadraticContinuousEquiv
      T₁ T₂ C S g) =
      (domainQuadraticReconstruction T₁ C S hS hgen hn).symm g := by
  obtain ⟨p, rfl⟩ := (domainQuadraticReconstruction T₁ C S hS hgen hn).surjective g
  rw [realizationQuadraticContinuousEquiv_domainQuadraticReconstruction,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- The same domain Galois coordinate is recovered from either actual scalar quotient. -/
theorem realizationQuadraticScalarQuotientContinuousEquiv_domainScalarQuotientEquiv [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut T₁ C S ⧸
      DiagramAut.scalarSubgroup T₁ C S) :
    DiagramAut.domainScalarQuotientEquiv T₂ C S hS hgen hn
      (realizationQuadraticScalarQuotientContinuousEquiv T₁ T₂ C S q) =
      DiagramAut.domainScalarQuotientEquiv T₁ C S hS hgen hn q :=
  realizationQuadraticScalarQuotientEquiv_domainScalarQuotientEquiv T₁ T₂ C S hS hgen hn q

/-- The original domain cofinal equivalence commutes with canonical realization comparison. -/
theorem realizationQuadraticContinuousEquiv_domainCofinalRestrictionEquiv [IsDomain R]
    (C' : CofinalSystem k₀ k n) (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T₁ C S) :
    realizationQuadraticContinuousEquiv T₁ T₂ C' S (domainCofinalRestrictionEquiv T₁ C C' S hC hS
      hgen hn g) =
      domainCofinalRestrictionEquiv T₂ C C' S hC hS hgen hn (realizationQuadraticContinuousEquiv
        T₁ T₂ C S g) := by
  rw [domainCofinalRestrictionEquiv_apply, domainCofinalRestrictionEquiv_apply]
  exact realizationQuadraticContinuousEquiv_restrictStages T₁ T₂ C S C' hC g

/-- Realization comparison preserves the same local unit and Galois parameters. -/
theorem realizationGradedContinuousEquiv_localGradedReconstruction [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    realizationGradedContinuousEquiv T₁ T₂ C S (localGradedReconstruction T₁ C S hS hgen hn p) =
      localGradedReconstruction T₂ C S hS hgen hn p :=
  realizationGradedAutEquiv_localGradedReconstruction T₁ T₂ C S hS hgen hn p

/-- The original inverse classifier recovers the same parameters after changing realization. -/
theorem realizationGradedContinuousEquiv_localGradedReconstruction_symm [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T₁ C S) :
    (localGradedReconstruction T₂ C S hS hgen hn).symm (realizationGradedContinuousEquiv T₁ T₂ C
      S g) =
      (localGradedReconstruction T₁ C S hS hgen hn).symm g := by
  obtain ⟨p, rfl⟩ := (localGradedReconstruction T₁ C S hS hgen hn).surjective g
  rw [realizationGradedContinuousEquiv_localGradedReconstruction, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

/-- The same local Galois coordinate is recovered from either actual scalar quotient. -/
theorem realizationGradedScalarQuotientContinuousEquiv_localScalarQuotientEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T₁ C S
      ⧸ GradedDiagramAut.scalarSubgroup T₁ C S) :
    GradedDiagramAut.localScalarQuotientEquiv T₂ C S hS hgen hn
      (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S q) =
      GradedDiagramAut.localScalarQuotientEquiv T₁ C S hS hgen hn q :=
  realizationGradedScalarQuotientEquiv_localScalarQuotientEquiv T₁ T₂ C S hS hgen hn q

/-- The original local cofinal equivalence commutes with canonical realization comparison. -/
theorem realizationGradedContinuousEquiv_gradedCofinalRestrictionEquiv [IsLocalRing R]
    (C' : CofinalSystem k₀ k n) (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T₁ C S) :
    realizationGradedContinuousEquiv T₁ T₂ C' S (gradedCofinalRestrictionEquiv T₁ C C' S hC hS
      hgen hn g) =
      gradedCofinalRestrictionEquiv T₂ C C' S hC hS hgen hn (realizationGradedContinuousEquiv T₁
        T₂ C S g) := by
  rw [gradedCofinalRestrictionEquiv_apply, gradedCofinalRestrictionEquiv_apply]
  exact realizationGradedContinuousEquiv_restrictStages T₁ T₂ C S C' hC g

/-- Realization comparison preserves the same domain unit and Galois parameters. -/
theorem realizationGradedContinuousEquiv_domainGradedReconstruction [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    realizationGradedContinuousEquiv T₁ T₂ C S (domainGradedReconstruction T₁ C S hS hgen hn p) =
      domainGradedReconstruction T₂ C S hS hgen hn p :=
  realizationGradedAutEquiv_domainGradedReconstruction T₁ T₂ C S hS hgen hn p

/-- The original inverse classifier recovers the same parameters after changing realization. -/
theorem realizationGradedContinuousEquiv_domainGradedReconstruction_symm [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T₁ C S) :
    (domainGradedReconstruction T₂ C S hS hgen hn).symm (realizationGradedContinuousEquiv T₁ T₂ C
      S g) =
      (domainGradedReconstruction T₁ C S hS hgen hn).symm g := by
  obtain ⟨p, rfl⟩ := (domainGradedReconstruction T₁ C S hS hgen hn).surjective g
  rw [realizationGradedContinuousEquiv_domainGradedReconstruction, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

/-- The same domain Galois coordinate is recovered from either actual scalar quotient. -/
theorem realizationGradedScalarQuotientContinuousEquiv_domainScalarQuotientEquiv [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut T₁ C S
      ⧸ GradedDiagramAut.scalarSubgroup T₁ C S) :
    GradedDiagramAut.domainScalarQuotientEquiv T₂ C S hS hgen hn
      (realizationGradedScalarQuotientContinuousEquiv T₁ T₂ C S q) =
      GradedDiagramAut.domainScalarQuotientEquiv T₁ C S hS hgen hn q :=
  realizationGradedScalarQuotientEquiv_domainScalarQuotientEquiv T₁ T₂ C S hS hgen hn q

/-- The original domain cofinal equivalence commutes with canonical realization comparison. -/
theorem realizationGradedContinuousEquiv_domainGradedCofinalRestrictionEquiv [IsDomain R]
    (C' : CofinalSystem k₀ k n) (hC : C'.stages ⊆ C.stages)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T₁ C S) :
    realizationGradedContinuousEquiv T₁ T₂ C' S (domainGradedCofinalRestrictionEquiv T₁ C C' S hC
      hS hgen hn g) =
      domainGradedCofinalRestrictionEquiv T₂ C C' S hC hS hgen hn
        (realizationGradedContinuousEquiv T₁ T₂ C S g) := by
  rw [domainGradedCofinalRestrictionEquiv_apply, domainGradedCofinalRestrictionEquiv_apply]
  exact realizationGradedContinuousEquiv_restrictStages T₁ T₂ C S C' hC g


section PointwiseRealizationCompatibility

open scoped DiscreteCoefficientUnits GaloisPointwise

/-- The pointwise classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localQuadraticContinuousReconstruction_realization
    [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticContinuousReconstruction T₁ C S hS hgen hn).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      localQuadraticContinuousReconstruction T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (localQuadraticReconstruction T₁ C S hS hgen hn x) =
    localQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_localQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The pointwise classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localGradedContinuousReconstruction_realization
    [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedContinuousReconstruction T₁ C S hS hgen hn).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      localGradedContinuousReconstruction T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (localGradedReconstruction T₁ C S hS hgen hn x) =
    localGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_localGradedReconstruction T₁ T₂ C S hS hgen hn x

/-- The pointwise classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainQuadraticContinuousReconstruction_realization
    [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticContinuousReconstruction T₁ C S hS hgen hn).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      domainQuadraticContinuousReconstruction T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (domainQuadraticReconstruction T₁ C S hS hgen hn x) =
    domainQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_domainQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The pointwise classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainGradedContinuousReconstruction_realization
    [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedContinuousReconstruction T₁ C S hS hgen hn).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      domainGradedContinuousReconstruction T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (domainGradedReconstruction T₁ C S hS hgen hn x) =
    domainGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_domainGradedReconstruction T₁ T₂ C S hS hgen hn x

end PointwiseRealizationCompatibility


section KrullRealizationCompatibility

open scoped DiscreteCoefficientUnits

/-- The krull classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localQuadraticKrullContinuousReconstruction_realization
    [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localQuadraticKrullContinuousReconstruction T₁ C S hS hgen hn hK).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      localQuadraticKrullContinuousReconstruction T₂ C S hS hgen hn hK := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (localQuadraticReconstruction T₁ C S hS hgen hn x) =
    localQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_localQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The krull classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localGradedKrullContinuousReconstruction_realization
    [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localGradedKrullContinuousReconstruction T₁ C S hS hgen hn hK).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      localGradedKrullContinuousReconstruction T₂ C S hS hgen hn hK := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (localGradedReconstruction T₁ C S hS hgen hn x) =
    localGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_localGradedReconstruction T₁ T₂ C S hS hgen hn x

/-- The krull classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainQuadraticKrullContinuousReconstruction_realization
    [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainQuadraticKrullContinuousReconstruction T₁ C S hS hgen hn hK).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      domainQuadraticKrullContinuousReconstruction T₂ C S hS hgen hn hK := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (domainQuadraticReconstruction T₁ C S hS hgen hn x) =
    domainQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_domainQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The krull classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainGradedKrullContinuousReconstruction_realization
    [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainGradedKrullContinuousReconstruction T₁ C S hS hgen hn hK).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      domainGradedKrullContinuousReconstruction T₂ C S hS hgen hn hK := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (domainGradedReconstruction T₁ C S hS hgen hn x) =
    domainGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_domainGradedReconstruction T₁ T₂ C S hS hgen hn x

end KrullRealizationCompatibility


section AlgebraicRealizationCompatibility

open scoped DiscreteCoefficientUnits

/-- The algebraic classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localQuadraticKrullContinuousReconstructionOfIsAlgebraic_realization
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T₁ C S hS hgen hn).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (localQuadraticReconstruction T₁ C S hS hgen hn x) =
    localQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_localQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The algebraic classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem localGradedKrullContinuousReconstructionOfIsAlgebraic_realization
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T₁ C S hS hgen hn).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      localGradedKrullContinuousReconstructionOfIsAlgebraic T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (localGradedReconstruction T₁ C S hS hgen hn x) =
    localGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_localGradedReconstruction T₁ T₂ C S hS hgen hn x

/-- The algebraic classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainQuadraticKrullContinuousReconstructionOfIsAlgebraic_realization
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T₁ C S hS hgen hn).trans
        (realizationQuadraticContinuousEquiv T₁ T₂ C S) =
      domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationQuadraticContinuousEquiv T₁ T₂ C S
      (domainQuadraticReconstruction T₁ C S hS hgen hn x) =
    domainQuadraticReconstruction T₂ C S hS hgen hn x
  exact realizationQuadraticContinuousEquiv_domainQuadraticReconstruction T₁ T₂ C S hS hgen hn x

/-- The algebraic classifier preserves its unit and Galois parameters under realization
comparison, as an equality of the original continuous group equivalences. -/
theorem domainGradedKrullContinuousReconstructionOfIsAlgebraic_realization
    [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T₁ C S hS hgen hn).trans
        (realizationGradedContinuousEquiv T₁ T₂ C S) =
      domainGradedKrullContinuousReconstructionOfIsAlgebraic T₂ C S hS hgen hn := by
  apply ContinuousMulEquiv.ext
  intro x
  change realizationGradedContinuousEquiv T₁ T₂ C S
      (domainGradedReconstruction T₁ C S hS hgen hn x) =
    domainGradedReconstruction T₂ C S hS hgen hn x
  exact realizationGradedContinuousEquiv_domainGradedReconstruction T₁ T₂ C S hS hgen hn x

end AlgebraicRealizationCompatibility

end OrlikSolomon.HyperplaneGT.Cohomology
