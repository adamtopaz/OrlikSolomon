/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Restriction

/-!
# Actual cofinal reconstruction squares

The four actual cofinal homeomorphisms commute with every existing pointwise or Krull
classifier, literal degree-one restriction and coefficient-overlap comparison. Comparing
unrelated chosen families through their union retains exactly the old reconstruction
coordinates; this does not assume closure of either arrangement family under unions.

Main results are the `cofinalRestrictionContinuousEquiv_pointwise`, `_krull`, `_algebraic`
and `_union_comparison` equations and their graded/domain counterparts. All forward
expansions are plain rewrites and preserve bare inverse cancellation.

Blueprint: the classified group and cofinal compatibility clauses of T15 (`thm:t15`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open scoped FiniteStageTopology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

section Pointwise

open scoped DiscreteCoefficientUnits GaloisPointwise

/-- Cofinal restriction commutes with the exact pointwise reconstruction classifier. -/
theorem cofinalRestrictionContinuousEquiv_pointwise [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticContinuousReconstruction T C S hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localQuadraticContinuousReconstruction T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localQuadraticReconstruction T C S hS hgen hn p) = localQuadraticReconstruction T C' S hS hgen
      hn p
  exact cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem cofinalRestrictionContinuousEquiv_pointwise_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localQuadraticContinuousReconstruction T C S hS hgen hn p) =
      localQuadraticContinuousReconstruction T C' S hS hgen hn p :=
  cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact pointwise reconstruction classifier. -/
theorem gradedCofinalRestrictionContinuousEquiv_pointwise [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedContinuousReconstruction T C S hS hgen hn).trans
      (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localGradedContinuousReconstruction T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localGradedReconstruction T C S hS hgen hn p) = localGradedReconstruction T C' S hS hgen hn p
  exact gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem gradedCofinalRestrictionContinuousEquiv_pointwise_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localGradedContinuousReconstruction T C S hS hgen hn p) =
      localGradedContinuousReconstruction T C' S hS hgen hn p :=
  gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact pointwise reconstruction classifier. -/
theorem domainCofinalRestrictionContinuousEquiv_pointwise [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticContinuousReconstruction T C S hS hgen hn).trans
      (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainQuadraticContinuousReconstruction T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainQuadraticReconstruction T C S hS hgen hn p) = domainQuadraticReconstruction T C' S hS
      hgen hn p
  exact domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainCofinalRestrictionContinuousEquiv_pointwise_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainQuadraticContinuousReconstruction T C S hS hgen hn p) =
      domainQuadraticContinuousReconstruction T C' S hS hgen hn p :=
  domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact pointwise reconstruction classifier. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_pointwise [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedContinuousReconstruction T C S hS hgen hn).trans
      (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainGradedContinuousReconstruction T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainGradedReconstruction T C S hS hgen hn p) = domainGradedReconstruction T C' S hS hgen hn p
  exact domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_pointwise_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainGradedContinuousReconstruction T C S hS hgen hn p) =
      domainGradedContinuousReconstruction T C' S hS hgen hn p :=
  domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

end Pointwise

section Krull

open scoped DiscreteCoefficientUnits

/-- Cofinal restriction commutes with the exact krull reconstruction classifier. -/
theorem cofinalRestrictionContinuousEquiv_krull [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).trans
      (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localQuadraticKrullContinuousReconstruction T C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localQuadraticReconstruction T C S hS hgen hn p) = localQuadraticReconstruction T C' S hS hgen
      hn p
  exact cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem cofinalRestrictionContinuousEquiv_krull_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p) =
      localQuadraticKrullContinuousReconstruction T C' S hS hgen hn hK p :=
  cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact krull reconstruction classifier. -/
theorem gradedCofinalRestrictionContinuousEquiv_krull [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (localGradedKrullContinuousReconstruction T C S hS hgen hn hK).trans
      (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localGradedKrullContinuousReconstruction T C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localGradedReconstruction T C S hS hgen hn p) = localGradedReconstruction T C' S hS hgen hn p
  exact gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem gradedCofinalRestrictionContinuousEquiv_krull_apply [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localGradedKrullContinuousReconstruction T C S hS hgen hn hK p) =
      localGradedKrullContinuousReconstruction T C' S hS hgen hn hK p :=
  gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact krull reconstruction classifier. -/
theorem domainCofinalRestrictionContinuousEquiv_krull [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK).trans
      (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainQuadraticKrullContinuousReconstruction T C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainQuadraticReconstruction T C S hS hgen hn p) = domainQuadraticReconstruction T C' S hS
      hgen hn p
  exact domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainCofinalRestrictionContinuousEquiv_krull_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainQuadraticKrullContinuousReconstruction T C S hS hgen hn hK p) =
      domainQuadraticKrullContinuousReconstruction T C' S hS hgen hn hK p :=
  domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact krull reconstruction classifier. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_krull [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK).trans
      (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainGradedKrullContinuousReconstruction T C' S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  change domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainGradedReconstruction T C S hS hgen hn p) = domainGradedReconstruction T C' S hS hgen hn p
  exact domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_krull_apply [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainGradedKrullContinuousReconstruction T C S hS hgen hn hK p) =
      domainGradedKrullContinuousReconstruction T C' S hS hgen hn hK p :=
  domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

end Krull

section Algebraic

open scoped DiscreteCoefficientUnits

/-- Cofinal restriction commutes with the exact algebraic reconstruction classifier. -/
theorem cofinalRestrictionContinuousEquiv_algebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localQuadraticReconstruction T C S hS hgen hn p) = localQuadraticReconstruction T C' S hS hgen
      hn p
  exact cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem cofinalRestrictionContinuousEquiv_algebraic_apply [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) =
      localQuadraticKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn p :=
  cofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact algebraic reconstruction classifier. -/
theorem gradedCofinalRestrictionContinuousEquiv_algebraic [IsLocalRing R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
      (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      localGradedKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (localGradedReconstruction T C S hS hgen hn p) = localGradedReconstruction T C' S hS hgen hn p
  exact gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem gradedCofinalRestrictionContinuousEquiv_algebraic_apply [IsLocalRing R] [Algebra.IsAlgebraic
  k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (localGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) =
      localGradedKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn p :=
  gradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact algebraic reconstruction classifier. -/
theorem domainCofinalRestrictionContinuousEquiv_algebraic [IsDomain R] [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
      (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainQuadraticReconstruction T C S hS hgen hn p) = domainQuadraticReconstruction T C' S hS
      hgen hn p
  exact domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainCofinalRestrictionContinuousEquiv_algebraic_apply [IsDomain R] [Algebra.IsAlgebraic k₀
  k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) =
      domainQuadraticKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn p :=
  domainCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- Cofinal restriction commutes with the exact algebraic reconstruction classifier. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_algebraic [IsDomain R] [Algebra.IsAlgebraic k₀
  k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn).trans
      (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      domainGradedKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn := by
  apply DFunLike.ext
  intro p
  change domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
    (domainGradedReconstruction T C S hS hgen hn p) = domainGradedReconstruction T C' S hS hgen hn p
  exact domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

/-- The entire reconstructed family restricts with both parameters unchanged. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_algebraic_apply [IsDomain R]
  [Algebra.IsAlgebraic k₀ k]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (domainGradedKrullContinuousReconstructionOfIsAlgebraic T C S hS hgen hn p) =
      domainGradedKrullContinuousReconstructionOfIsAlgebraic T C' S hS hgen hn p :=
  domainGradedCofinalRestrictionContinuousEquiv_classification T C C' S hC hS hgen hn p

end Algebraic

/-- The union of selected families gives the old coordinate comparison between unrelated
systems, without closure of either family under arrangement unions. -/
theorem cofinalRestrictionContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((cofinalRestrictionContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (localQuadraticReconstruction T C S hS hgen hn).symm.trans
        (localQuadraticReconstruction T C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change cofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn
    ((cofinalRestrictionContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm g) = _
  rw [cofinalRestrictionContinuousEquiv_symm_apply, cofinalRestrictionEquiv_symm_apply]
  exact cofinalRestrictionContinuousEquiv_classification T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn _

/-- The union of selected families gives the old coordinate comparison between unrelated
systems, without closure of either family under arrangement unions. -/
theorem gradedCofinalRestrictionContinuousEquiv_union_comparison [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((gradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (localGradedReconstruction T C S hS hgen hn).symm.trans
        (localGradedReconstruction T C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change gradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn
    ((gradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm g) = _
  rw [gradedCofinalRestrictionContinuousEquiv_symm_apply, gradedCofinalRestrictionEquiv_symm_apply]
  exact gradedCofinalRestrictionContinuousEquiv_classification T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn _

/-- The union of selected families gives the old coordinate comparison between unrelated
systems, without closure of either family under arrangement unions. -/
theorem domainCofinalRestrictionContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (domainQuadraticReconstruction T C S hS hgen hn).symm.trans
        (domainQuadraticReconstruction T C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change domainCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn
    ((domainCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm g) = _
  rw [domainCofinalRestrictionContinuousEquiv_symm_apply, domainCofinalRestrictionEquiv_symm_apply]
  exact domainCofinalRestrictionContinuousEquiv_classification T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn _

/-- The union of selected families gives the old coordinate comparison between unrelated
systems, without closure of either family under arrangement unions. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_union_comparison [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    ((domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
        (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
      (domainGradedReconstruction T C S hS hgen hn).symm.trans
        (domainGradedReconstruction T C' S hS hgen hn) := by
  apply MulEquiv.ext
  intro g
  change domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn
    ((domainGradedCofinalRestrictionContinuousEquiv T (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm g) = _
  rw [domainGradedCofinalRestrictionContinuousEquiv_symm_apply,
    domainGradedCofinalRestrictionEquiv_symm_apply]
  exact domainGradedCofinalRestrictionContinuousEquiv_classification T (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn _

/-- Actual degree-one restriction commutes with actual cofinal restriction. -/
theorem cofinalRestrictionContinuousEquiv_toQuadratic [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.toQuadratic T C S g) =
      GradedDiagramAut.toQuadratic T C' S
        (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) := by
  rw [cofinalRestrictionContinuousEquiv_apply,
    gradedCofinalRestrictionContinuousEquiv_apply, GradedDiagramAut.toQuadratic_restrictStages]

/-- The bundled degree-one and cofinal homeomorphisms form the original square. -/
theorem cofinalRestrictionContinuousEquiv_restriction [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (localRestrictionContinuousEquiv T C S hS hgen hn).trans
      (cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      (gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
        (localRestrictionContinuousEquiv T C' S hS hgen hn) := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, localRestrictionContinuousEquiv_apply]
  exact cofinalRestrictionContinuousEquiv_toQuadratic T C C' S hC hS hgen hn g

/-- Actual degree-one restriction commutes with actual cofinal restriction. -/
theorem domainCofinalRestrictionContinuousEquiv_toQuadratic [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn
      (GradedDiagramAut.toQuadratic T C S g) =
      GradedDiagramAut.toQuadratic T C' S
        (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn g) := by
  rw [domainCofinalRestrictionContinuousEquiv_apply,
    domainGradedCofinalRestrictionContinuousEquiv_apply,
      GradedDiagramAut.toQuadratic_restrictStages]

/-- The bundled degree-one and cofinal homeomorphisms form the original square. -/
theorem domainCofinalRestrictionContinuousEquiv_restriction [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainRestrictionContinuousEquiv T C S hS hgen hn).trans
      (domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn) =
      (domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn).trans
        (domainRestrictionContinuousEquiv T C' S hS hgen hn) := by
  apply DFunLike.ext
  intro g
  simp only [ContinuousMulEquiv.trans_apply, domainRestrictionContinuousEquiv_apply]
  exact domainCofinalRestrictionContinuousEquiv_toQuadratic T C C' S hC hS hgen hn g

/-- Domain and local cofinal maps agree on their coefficient overlap. -/
theorem domainCofinalRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn =
      cofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [domainCofinalRestrictionContinuousEquiv_apply,
    cofinalRestrictionContinuousEquiv_apply]

/-- Domain and local cofinal maps agree on their coefficient overlap. -/
theorem domainGradedCofinalRestrictionContinuousEquiv_eq_local [IsDomain R] [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn =
      gradedCofinalRestrictionContinuousEquiv T C C' S hC hS hgen hn := by
  apply DFunLike.ext
  intro g
  rw [domainGradedCofinalRestrictionContinuousEquiv_apply,
    gradedCofinalRestrictionContinuousEquiv_apply]

end OrlikSolomon.HyperplaneGT.Cohomology
