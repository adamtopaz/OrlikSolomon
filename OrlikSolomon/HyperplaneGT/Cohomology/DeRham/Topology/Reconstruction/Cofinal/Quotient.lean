/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Cofinal.Restriction
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Quotient

/-!
# Cofinal scalar quotient equivalences for ordinary diagrams

The new ordinary quotient congruences use the exact proved ordinary group restrictions
and their whole scalar-image equalities. Their continuous upgrades retain literal Mathlib
quotient topologies, explicit old inverse representatives and the canonical Galois section.
Actual-theory/twist, classifier and degree-one squares commute on the original carriers.

The old marking and dimension hypotheses are explicit. No field-extension, scalar
closedness, unclassified bijectivity or arrangement-union-closure assumption is added.
Blueprint: the cofinal scalar quotient clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

variable (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
  (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- The exact ordinary cofinal group equivalence maps onto the entire scalar range. -/
theorem map_scalarSubgroup_cofinalRestrictionEquiv :
    (DiagramAut.scalarSubgroup C S).map (cofinalRestrictionEquiv C C' S hC hS hgen hn).toMonoidHom
      = DiagramAut.scalarSubgroup C' S := by
  rw [cofinalRestrictionEquiv_toMonoidHom C C' S hC hS hgen hn]
  exact DiagramAut.map_scalarSubgroup_restrictStages C C' S hC

/-- The new ordinary cofinal quotient is the congruence of the proved old group wrapper.
Its scalar-image condition is proved, rather than supplied. Blueprint: T17 (`cor:t17`). -/
def cofinalScalarQuotientEquiv :
    (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) ≃*
      (DiagramAut C' S ⧸ DiagramAut.scalarSubgroup C' S) :=
  QuotientGroup.congr (DiagramAut.scalarSubgroup C S) (DiagramAut.scalarSubgroup C' S)
    (cofinalRestrictionEquiv C C' S hC hS hgen hn) (map_scalarSubgroup_cofinalRestrictionEquiv C
      C' S hC hS hgen hn)

/-- A representative uses literal ordinary stage selection and the unchanged common target. -/
theorem cofinalScalarQuotientEquiv_map (g : DiagramAut C S) :
    cofinalScalarQuotientEquiv C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap C S g) =
      DiagramAut.scalarQuotientMap C' S (DiagramAut.restrictStages C C' S hC g) :=
  congrArg (DiagramAut.scalarQuotientMap C' S) (cofinalRestrictionEquiv_apply C C' S hC hS hgen hn
    g)

/-- The inverse representative uses the exact proved ordinary inverse. -/
theorem cofinalScalarQuotientEquiv_symm_map (g : DiagramAut C' S) :
    (cofinalScalarQuotientEquiv C C' S hC hS hgen hn).symm (DiagramAut.scalarQuotientMap C' S g) =
      DiagramAut.scalarQuotientMap C S ((cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g) :=
        rfl

/-- The new ordinary cofinal quotient congruence has continuous forward and inverse maps. -/
def cofinalScalarQuotientContinuousEquiv :
    (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) ≃ₜ*
      (DiagramAut C' S ⧸ DiagramAut.scalarSubgroup C' S) where
  toMulEquiv := cofinalScalarQuotientEquiv C C' S hC hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut C S ↦ cofinalScalarQuotientEquiv C C' S hC hS hgen hn
      (DiagramAut.scalarQuotientMap C S g))
    simp only [cofinalScalarQuotientEquiv_map]
    exact QuotientGroup.continuous_mk.comp (DiagramAut.continuous_restrictStages C C' S hC)
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup C' S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut C' S ↦ (cofinalScalarQuotientEquiv C C' S hC hS hgen
      hn).symm (DiagramAut.scalarQuotientMap C' S g))
    simp only [cofinalScalarQuotientEquiv_symm_map]
    exact QuotientGroup.continuous_mk.comp (cofinalRestrictionContinuousEquiv C C' S hC hS hgen
      hn).continuous_invFun

/-- Forgetting continuity retains exactly the new ordinary quotient congruence. -/
theorem cofinalScalarQuotientContinuousEquiv_toMulEquiv : (cofinalScalarQuotientContinuousEquiv C
    C' S hC hS hgen hn).toMulEquiv = cofinalScalarQuotientEquiv C C' S hC hS hgen hn := rfl

/-- The complete forward function remains the new algebraic congruence. -/
theorem cofinalScalarQuotientContinuousEquiv_coe : ⇑(cofinalScalarQuotientContinuousEquiv C C' S
    hC hS hgen hn) = cofinalScalarQuotientEquiv C C' S hC hS hgen hn := rfl

/-- Evaluation uses the identical new algebraic quotient map. -/
theorem cofinalScalarQuotientContinuousEquiv_apply (z : DiagramAut C S ⧸ DiagramAut.scalarSubgroup
    C S) : cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z =
    cofinalScalarQuotientEquiv C C' S hC hS hgen hn z := rfl

/-- The inverse is exactly the inverse of the disclosed ordinary congruence. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_apply (z : DiagramAut C' S ⧸
    DiagramAut.scalarSubgroup C' S) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm z =
      (cofinalScalarQuotientEquiv C C' S hC hS hgen hn).symm z := rfl

/-- Every forward representative selects the literal old stages and unchanged target. -/
theorem cofinalScalarQuotientContinuousEquiv_map (g : DiagramAut C S) :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap C S g) =
      DiagramAut.scalarQuotientMap C' S (DiagramAut.restrictStages C C' S hC g) :=
        cofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g

/-- The complete ordinary quotient homomorphism is literal cofinal stage selection. -/
theorem cofinalScalarQuotientContinuousEquiv_toMonoidHom :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).toMonoidHom =
      DiagramAut.restrictStagesScalarQuotient C C' S hC := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  exact cofinalScalarQuotientContinuousEquiv_map C C' S hC hS hgen hn g

/-- Every quotient class is restricted by the same original stage-selection quotient map. -/
theorem cofinalScalarQuotientContinuousEquiv_restrictStages
    (z : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z =
      DiagramAut.restrictStagesScalarQuotient C C' S hC z :=
  DFunLike.congr_fun (cofinalScalarQuotientContinuousEquiv_toMonoidHom C C' S hC hS hgen hn) z

/-- Every inverse representative uses the exact old ordinary cofinal inverse. -/
theorem cofinalScalarQuotientContinuousEquiv_symm_map (g : DiagramAut C' S) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm (DiagramAut.scalarQuotientMap
      C' S g) =
      DiagramAut.scalarQuotientMap C S ((cofinalRestrictionEquiv C C' S hC hS hgen hn).symm g) :=
        rfl

/-- The ordinary congruence is the exact local actual quotient map between ordinary twists. -/
theorem cofinalScalarQuotientEquiv_eq_composite :
    cofinalScalarQuotientEquiv C C' S hC hS hgen hn = (DiagramAut.scalarQuotientTwistEquiv C
      S).trans
      ((Cohomology.cofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn).toMulEquiv.trans
        (DiagramAut.scalarQuotientTwistEquiv C' S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change cofinalScalarQuotientEquiv C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap C S g) = _
  apply (DiagramAut.scalarQuotientTwistEquiv C' S).injective
  have h := (congrArg (DiagramAut.scalarQuotientTwistEquiv C' S)
    (cofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g)).trans
      ((DiagramAut.scalarQuotientTwistEquiv_map C' S (DiagramAut.restrictStages C C' S hC g)).trans
        ((congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C' S)
          (quadraticTwistEquiv_restrictStages C C' S hC g)).trans
            ((Cohomology.cofinalScalarQuotientContinuousEquiv_map Tdr C C' S hC hS hgen hn
              (quadraticTwistEquiv C S g)).symm.trans
                (congrArg (Cohomology.cofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn)
                  (DiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((DiagramAut.scalarQuotientTwistEquiv C' S).apply_symm_apply _).symm

/-- The continuous ordinary quotient map keeps the exact local actual/twist composite. -/
theorem cofinalScalarQuotientContinuousEquiv_comparison :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn =
      (DiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
      ((Cohomology.cofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (DiagramAut.scalarQuotientTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (cofinalScalarQuotientEquiv_eq_composite C C' S hC hS hgen hn) z

/-- The ordinary congruence is the exact domain actual quotient map between ordinary twists. -/
theorem cofinalScalarQuotientEquiv_eq_domain_composite :
    cofinalScalarQuotientEquiv C C' S hC hS hgen hn = (DiagramAut.scalarQuotientTwistEquiv C
      S).trans
      ((Cohomology.domainCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen
        hn).toMulEquiv.trans
        (DiagramAut.scalarQuotientTwistEquiv C' S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change cofinalScalarQuotientEquiv C C' S hC hS hgen hn (DiagramAut.scalarQuotientMap C S g) = _
  apply (DiagramAut.scalarQuotientTwistEquiv C' S).injective
  have h := (congrArg (DiagramAut.scalarQuotientTwistEquiv C' S)
    (cofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g)).trans
      ((DiagramAut.scalarQuotientTwistEquiv_map C' S (DiagramAut.restrictStages C C' S hC g)).trans
        ((congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C' S)
          (quadraticTwistEquiv_restrictStages C C' S hC g)).trans
            ((Cohomology.domainCofinalScalarQuotientContinuousEquiv_map Tdr C C' S hC hS hgen hn
              (quadraticTwistEquiv C S g)).symm.trans
                (congrArg (Cohomology.domainCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS
                  hgen hn)
                  (DiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((DiagramAut.scalarQuotientTwistEquiv C' S).apply_symm_apply _).symm

/-- The continuous ordinary quotient map keeps the exact domain actual/twist composite. -/
theorem cofinalScalarQuotientContinuousEquiv_eq_domain_composite :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn =
      (DiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
      ((Cohomology.domainCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (DiagramAut.scalarQuotientTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (cofinalScalarQuotientEquiv_eq_domain_composite C C' S hC hS hgen hn) z

/-- Cofinal quotient restriction preserves the exact canonical Galois coordinate. -/
theorem cofinalScalarQuotientContinuousEquiv_galois (z : DiagramAut C S ⧸
    DiagramAut.scalarSubgroup C S) :
    DiagramAut.scalarQuotientEquiv C' S hS hgen hn (cofinalScalarQuotientContinuousEquiv C C' S hC
      hS hgen hn z) =
      DiagramAut.scalarQuotientEquiv C S hS hgen hn z := by
  have h := congrArg (DiagramAut.scalarQuotientTwistEquiv C' S)
    (DFunLike.congr_fun (cofinalScalarQuotientEquiv_eq_composite C C' S hC hS hgen hn) z)
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  exact (congrArg (Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C' S hS hgen hn) h).trans
    (Cohomology.cofinalScalarQuotientContinuousEquiv_galois Tdr C C' S hC hS hgen hn _)

/-- The new congruence is exactly extraction followed by the canonical subsystem section. -/
theorem cofinalScalarQuotientEquiv_classification :
    cofinalScalarQuotientEquiv C C' S hC hS hgen hn = (DiagramAut.scalarQuotientEquiv C S hS hgen
      hn).trans
      (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  exact (cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z).trans
    ((DiagramAut.scalarQuotientEquiv C' S hS hgen hn).apply_symm_apply _).symm

/-- The same direct ordinary Galois family represents the canonical class after restriction. -/
theorem cofinalScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn (DiagramAut.scalarQuotientSection C
      S σ) = DiagramAut.scalarQuotientSection C' S σ := by
  apply (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  exact ((cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn _).trans
    (DiagramAut.scalarQuotientEquiv_section C S hS hgen hn σ)).trans
      (DiagramAut.scalarQuotientEquiv_section C' S hS hgen hn σ).symm

/-- Forward restriction followed by its inverse recovers every original scalar class. -/
theorem cofinalScalarQuotientContinuousEquiv_left_inv (z : DiagramAut C S ⧸
    DiagramAut.scalarSubgroup C S) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm
      (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z) = z :=
      (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm_apply_apply z

/-- The inverse followed by restriction recovers every subsystem scalar class. -/
theorem cofinalScalarQuotientContinuousEquiv_right_inv (z : DiagramAut C' S ⧸
    DiagramAut.scalarSubgroup C' S) :
    cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
      ((cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm z) = z :=
      (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).apply_symm_apply z

/-- Quotient restriction to the same supplied family is the identity. -/
theorem cofinalScalarQuotientContinuousEquiv_refl :
    cofinalScalarQuotientContinuousEquiv C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.scalarQuotientEquiv C S hS hgen hn).injective
  exact cofinalScalarQuotientContinuousEquiv_galois C C S (Set.Subset.refl _) hS hgen hn z

/-- Successive ordinary scalar-quotient restrictions compose on the original classes. -/
theorem cofinalScalarQuotientContinuousEquiv_trans (C'' : CofinalSystem k₀ k n)
    (hC' : C''.stages ⊆ C'.stages) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (cofinalScalarQuotientContinuousEquiv C' C'' S hC' hS hgen hn) =
      cofinalScalarQuotientContinuousEquiv C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.scalarQuotientEquiv C'' S hS hgen hn).injective
  exact ((cofinalScalarQuotientContinuousEquiv_galois C' C'' S hC' hS hgen hn _).trans
    (cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z)).trans
      (cofinalScalarQuotientContinuousEquiv_galois C C'' S (hC'.trans hC) hS hgen hn z).symm

section Pointwise

open scoped GaloisPointwise

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_classification :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (DiagramAut.scalarQuotientContinuousEquiv C' S hS hgen hn) =
      DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

end Pointwise

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_krull_classification (hK : KrullFixingCondition k₀ k) :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (DiagramAut.scalarQuotientKrullContinuousEquiv C' S hS hgen hn hK) =
      DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  exact cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem cofinalScalarQuotientContinuousEquiv_algebraic_classification [Algebra.IsAlgebraic k₀ k] :
    (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C' S hS hgen hn) =
      DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

/-- The exact ordinary cofinal group equivalence maps onto the entire scalar range. -/
theorem map_scalarSubgroup_gradedCofinalRestrictionEquiv :
    (GradedDiagramAut.scalarSubgroup C S).map (gradedCofinalRestrictionEquiv C C' S hC hS hgen
      hn).toMonoidHom = GradedDiagramAut.scalarSubgroup C' S := by
  rw [gradedCofinalRestrictionEquiv_toMonoidHom C C' S hC hS hgen hn]
  exact GradedDiagramAut.map_scalarSubgroup_restrictStages C C' S hC

/-- The new ordinary cofinal quotient is the congruence of the proved old group wrapper.
Its scalar-image condition is proved, rather than supplied. Blueprint: T17 (`cor:t17`). -/
def gradedCofinalScalarQuotientEquiv :
    (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ≃*
      (GradedDiagramAut C' S ⧸ GradedDiagramAut.scalarSubgroup C' S) :=
  QuotientGroup.congr (GradedDiagramAut.scalarSubgroup C S) (GradedDiagramAut.scalarSubgroup C' S)
    (gradedCofinalRestrictionEquiv C C' S hC hS hgen hn)
      (map_scalarSubgroup_gradedCofinalRestrictionEquiv C C' S hC hS hgen hn)

/-- A representative uses literal ordinary stage selection and the unchanged common target. -/
theorem gradedCofinalScalarQuotientEquiv_map (g : GradedDiagramAut C S) :
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn (GradedDiagramAut.scalarQuotientMap C S
      g) =
      GradedDiagramAut.scalarQuotientMap C' S (GradedDiagramAut.restrictStages C C' S hC g) :=
  congrArg (GradedDiagramAut.scalarQuotientMap C' S) (gradedCofinalRestrictionEquiv_apply C C' S
    hC hS hgen hn g)

/-- The inverse representative uses the exact proved ordinary inverse. -/
theorem gradedCofinalScalarQuotientEquiv_symm_map (g : GradedDiagramAut C' S) :
    (gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap C' S g) =
      GradedDiagramAut.scalarQuotientMap C S ((gradedCofinalRestrictionEquiv C C' S hC hS hgen
        hn).symm g) := rfl

/-- The new ordinary cofinal quotient congruence has continuous forward and inverse maps. -/
def gradedCofinalScalarQuotientContinuousEquiv :
    (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ≃ₜ*
      (GradedDiagramAut C' S ⧸ GradedDiagramAut.scalarSubgroup C' S) where
  toMulEquiv := gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut C S ↦ gradedCofinalScalarQuotientEquiv C C' S hC
      hS hgen hn (GradedDiagramAut.scalarQuotientMap C S g))
    simp only [gradedCofinalScalarQuotientEquiv_map]
    exact QuotientGroup.continuous_mk.comp (GradedDiagramAut.continuous_restrictStages C C' S hC)
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup C' S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut C' S ↦ (gradedCofinalScalarQuotientEquiv C C' S hC
      hS hgen hn).symm (GradedDiagramAut.scalarQuotientMap C' S g))
    simp only [gradedCofinalScalarQuotientEquiv_symm_map]
    exact QuotientGroup.continuous_mk.comp (gradedCofinalRestrictionContinuousEquiv C C' S hC hS
      hgen hn).continuous_invFun

/-- Forgetting continuity retains exactly the new ordinary quotient congruence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_toMulEquiv :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).toMulEquiv =
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn := rfl

/-- The complete forward function remains the new algebraic congruence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_coe :
    ⇑(gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn) =
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn := rfl

/-- Evaluation uses the identical new algebraic quotient map. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_apply (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) : gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS
    hgen hn z = gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn z := rfl

/-- The inverse is exactly the inverse of the disclosed ordinary congruence. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_apply (z : GradedDiagramAut C' S ⧸
    GradedDiagramAut.scalarSubgroup C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm z =
      (gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn).symm z := rfl

/-- Every forward representative selects the literal old stages and unchanged target. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_map (g : GradedDiagramAut C S) :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientMap C S g) =
      GradedDiagramAut.scalarQuotientMap C' S (GradedDiagramAut.restrictStages C C' S hC g) :=
        gradedCofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g

/-- The complete ordinary quotient homomorphism is literal cofinal stage selection. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_toMonoidHom :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).toMonoidHom =
      GradedDiagramAut.restrictStagesScalarQuotient C C' S hC := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  exact gradedCofinalScalarQuotientContinuousEquiv_map C C' S hC hS hgen hn g

/-- Every quotient class is restricted by the same original stage-selection quotient map. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_restrictStages
    (z : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z =
      GradedDiagramAut.restrictStagesScalarQuotient C C' S hC z :=
  DFunLike.congr_fun (gradedCofinalScalarQuotientContinuousEquiv_toMonoidHom C C' S hC hS hgen hn) z

/-- Every inverse representative uses the exact old ordinary cofinal inverse. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_symm_map (g : GradedDiagramAut C' S) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm
      (GradedDiagramAut.scalarQuotientMap C' S g) =
      GradedDiagramAut.scalarQuotientMap C S ((gradedCofinalRestrictionEquiv C C' S hC hS hgen
        hn).symm g) := rfl

/-- The ordinary congruence is the exact local actual quotient map between ordinary twists. -/
theorem gradedCofinalScalarQuotientEquiv_eq_composite :
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistEquiv C S).trans
      ((Cohomology.gradedCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen
        hn).toMulEquiv.trans
        (GradedDiagramAut.scalarQuotientTwistEquiv C' S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn (GradedDiagramAut.scalarQuotientMap
    C S g) = _
  apply (GradedDiagramAut.scalarQuotientTwistEquiv C' S).injective
  have h := (congrArg (GradedDiagramAut.scalarQuotientTwistEquiv C' S)
    (gradedCofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g)).trans
      ((GradedDiagramAut.scalarQuotientTwistEquiv_map C' S (GradedDiagramAut.restrictStages C C' S
        hC g)).trans
        ((congrArg (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C' S)
          (gradedTwistEquiv_restrictStages C C' S hC g)).trans
            ((Cohomology.gradedCofinalScalarQuotientContinuousEquiv_map Tdr C C' S hC hS hgen hn
              (gradedTwistEquiv C S g)).symm.trans
                (congrArg (Cohomology.gradedCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS
                  hgen hn)
                  (GradedDiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((GradedDiagramAut.scalarQuotientTwistEquiv C' S).apply_symm_apply _).symm

/-- The continuous ordinary quotient map keeps the exact local actual/twist composite. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_comparison :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
      ((Cohomology.gradedCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (gradedCofinalScalarQuotientEquiv_eq_composite C C' S hC hS hgen hn) z

/-- The ordinary congruence is the exact domain actual quotient map between ordinary twists. -/
theorem gradedCofinalScalarQuotientEquiv_eq_domain_composite :
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistEquiv C S).trans
      ((Cohomology.domainGradedCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen
        hn).toMulEquiv.trans
        (GradedDiagramAut.scalarQuotientTwistEquiv C' S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn (GradedDiagramAut.scalarQuotientMap
    C S g) = _
  apply (GradedDiagramAut.scalarQuotientTwistEquiv C' S).injective
  have h := (congrArg (GradedDiagramAut.scalarQuotientTwistEquiv C' S)
    (gradedCofinalScalarQuotientEquiv_map C C' S hC hS hgen hn g)).trans
      ((GradedDiagramAut.scalarQuotientTwistEquiv_map C' S (GradedDiagramAut.restrictStages C C' S
        hC g)).trans
        ((congrArg (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C' S)
          (gradedTwistEquiv_restrictStages C C' S hC g)).trans
            ((Cohomology.domainGradedCofinalScalarQuotientContinuousEquiv_map Tdr C C' S hC hS
              hgen hn
              (gradedTwistEquiv C S g)).symm.trans
                (congrArg (Cohomology.domainGradedCofinalScalarQuotientContinuousEquiv Tdr C C' S
                  hC hS hgen hn)
                  (GradedDiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((GradedDiagramAut.scalarQuotientTwistEquiv C' S).apply_symm_apply _).symm

/-- The continuous ordinary quotient map keeps the exact domain actual/twist composite. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_eq_domain_composite :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
      ((Cohomology.domainGradedCofinalScalarQuotientContinuousEquiv Tdr C C' S hC hS hgen hn).trans
        (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C' S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (gradedCofinalScalarQuotientEquiv_eq_domain_composite C C' S hC hS hgen
    hn) z

/-- Cofinal quotient restriction preserves the exact canonical Galois coordinate. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_galois (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) :
    GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn
      (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z) =
      GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn z := by
  have h := congrArg (GradedDiagramAut.scalarQuotientTwistEquiv C' S)
    (DFunLike.congr_fun (gradedCofinalScalarQuotientEquiv_eq_composite C C' S hC hS hgen hn) z)
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  exact (congrArg (Cohomology.GradedDiagramAut.localScalarQuotientEquiv Tdr C' S hS hgen hn)
    h).trans
    (Cohomology.gradedCofinalScalarQuotientContinuousEquiv_galois Tdr C C' S hC hS hgen hn _)

/-- The new congruence is exactly extraction followed by the canonical subsystem section. -/
theorem gradedCofinalScalarQuotientEquiv_classification :
    gradedCofinalScalarQuotientEquiv C C' S hC hS hgen hn = (GradedDiagramAut.scalarQuotientEquiv
      C S hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  exact (gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z).trans
    ((GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).apply_symm_apply _).symm

/-- The same direct ordinary Galois family represents the canonical class after restriction. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_section (σ : k ≃ₐ[k₀] k) :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
      (GradedDiagramAut.scalarQuotientSection C S σ) = GradedDiagramAut.scalarQuotientSection C' S
      σ := by
  apply (GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  exact ((gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn _).trans
    (GradedDiagramAut.scalarQuotientEquiv_section C S hS hgen hn σ)).trans
      (GradedDiagramAut.scalarQuotientEquiv_section C' S hS hgen hn σ).symm

/-- Forward restriction followed by its inverse recovers every original scalar class. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_left_inv (z : GradedDiagramAut C S ⧸
    GradedDiagramAut.scalarSubgroup C S) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm
      (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn z) = z :=
      (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm_apply_apply z

/-- The inverse followed by restriction recovers every subsystem scalar class. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_right_inv (z : GradedDiagramAut C' S ⧸
    GradedDiagramAut.scalarSubgroup C' S) :
    gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn
      ((gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).symm z) = z :=
      (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).apply_symm_apply z

/-- Quotient restriction to the same supplied family is the identity. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_refl :
    gradedCofinalScalarQuotientContinuousEquiv C C S (Set.Subset.refl _) hS hgen hn =
      ContinuousMulEquiv.refl _ := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn).injective
  exact gradedCofinalScalarQuotientContinuousEquiv_galois C C S (Set.Subset.refl _) hS hgen hn z

/-- Successive ordinary scalar-quotient restrictions compose on the original classes. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_trans (C'' : CofinalSystem k₀ k n)
    (hC' : C''.stages ⊆ C'.stages) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (gradedCofinalScalarQuotientContinuousEquiv C' C'' S hC' hS hgen hn) =
      gradedCofinalScalarQuotientContinuousEquiv C C'' S (hC'.trans hC) hS hgen hn := by
  apply DFunLike.ext
  intro z
  apply (GradedDiagramAut.scalarQuotientEquiv C'' S hS hgen hn).injective
  exact ((gradedCofinalScalarQuotientContinuousEquiv_galois C' C'' S hC' hS hgen hn _).trans
    (gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z)).trans
      (gradedCofinalScalarQuotientContinuousEquiv_galois C C'' S (hC'.trans hC) hS hgen hn z).symm

section Pointwise

open scoped GaloisPointwise

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_classification :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientContinuousEquiv C' S hS hgen hn) =
      GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

end Pointwise

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_krull_classification (hK : KrullFixingCondition
    k₀ k) :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientKrullContinuousEquiv C' S hS hgen hn hK) =
      GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  exact gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

/-- The bundled cofinal quotient classifier square keeps the same field automorphism. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_algebraic_classification [Algebra.IsAlgebraic
    k₀ k] :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C' S hS hgen hn) =
      GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z

/-- Cofinal restriction and degree-one restriction commute on both literal ordinary quotients. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_trans_restriction :
    (gradedCofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn).trans
      (scalarQuotientRestrictionContinuousEquiv C' S hS hgen hn) =
        (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).trans
          (cofinalScalarQuotientContinuousEquiv C C' S hC hS hgen hn) := by
  apply DFunLike.ext
  intro z
  apply (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  exact ((scalarQuotientEquiv_restriction C' S hS hgen hn _).trans
    (gradedCofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn z)).trans
      ((cofinalScalarQuotientContinuousEquiv_galois C C' S hC hS hgen hn _).trans
        (scalarQuotientEquiv_restriction C S hS hgen hn z)).symm

/-- Two unrelated supplied families are compared through their union of selected families,
with exactly the same canonical Galois coordinate on the original scalar quotients. -/
theorem cofinalScalarQuotientContinuousEquiv_union :
    ((cofinalScalarQuotientContinuousEquiv (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (cofinalScalarQuotientContinuousEquiv (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
        (DiagramAut.scalarQuotientEquiv C S hS hgen hn).trans
          (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (DiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  let e := cofinalScalarQuotientContinuousEquiv (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
  have hi := cofinalScalarQuotientContinuousEquiv_galois (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn (e.symm z)
  have hc := congrArg (DiagramAut.scalarQuotientEquiv C S hS hgen hn) (e.apply_symm_apply z)
  exact (cofinalScalarQuotientContinuousEquiv_galois (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn (e.symm z)).trans
      ((hc.symm.trans hi).symm.trans
        ((DiagramAut.scalarQuotientEquiv C' S hS hgen hn).apply_symm_apply _).symm)

/-- Two unrelated supplied families are compared through their union of selected families,
with exactly the same canonical Galois coordinate on the original scalar quotients. -/
theorem gradedCofinalScalarQuotientContinuousEquiv_union :
    ((gradedCofinalScalarQuotientContinuousEquiv (C.unionStages C') C S
      (C.stages_subset_unionStages_left C') hS hgen hn).symm.trans
      (gradedCofinalScalarQuotientContinuousEquiv (C.unionStages C') C' S
        (C.stages_subset_unionStages_right C') hS hgen hn)).toMulEquiv =
        (GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn).trans
          (GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).symm := by
  apply MulEquiv.ext
  intro z
  apply (GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).injective
  let e := gradedCofinalScalarQuotientContinuousEquiv (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn
  have hi := gradedCofinalScalarQuotientContinuousEquiv_galois (C.unionStages C') C S
    (C.stages_subset_unionStages_left C') hS hgen hn (e.symm z)
  have hc := congrArg (GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn) (e.apply_symm_apply z)
  exact (gradedCofinalScalarQuotientContinuousEquiv_galois (C.unionStages C') C' S
    (C.stages_subset_unionStages_right C') hS hgen hn (e.symm z)).trans
      ((hc.symm.trans hi).symm.trans
        ((GradedDiagramAut.scalarQuotientEquiv C' S hS hgen hn).apply_symm_apply _).symm)

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
