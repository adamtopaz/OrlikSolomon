/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Quotient.Basic

/-!
# Ordinary scalar quotient degree-one restriction

The exact old ordinary restriction sends the whole scalar range onto the quadratic
scalar range. Its new Mathlib quotient congruence and continuous upgrade preserve both
literal quotient topologies and the canonical Galois coordinate. They agree with the
exact actual-theory restriction between the old ordinary quotient twists.

This size-only leaf separates the ordinary restriction API from its six scalar quotient
classifiers. No additional hypothesis, instance or mathematical scope is introduced.
Blueprint: the scalar quotient restriction clauses of T17 (`cor:t17`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

open Topology
open scoped FiniteStageTopology DiscreteCoefficientUnits

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- The exact old ordinary restriction sends every uniform scalar to the same scalar. -/
theorem restrictionEquiv_scalarGradedAction (a : kˣ) :
    restrictionEquiv C S hS hgen hn (scalarGradedAction C S a) = scalarQuadraticAction C S a := by
  apply (quadraticTwistEquiv C S).injective
  exact (congrArg (quadraticTwistEquiv C S)
    (restrictionEquiv_apply C S hS hgen hn (scalarGradedAction C S a))).trans
      ((GradedDiagramAut.toQuadratic_comparison C S (scalarGradedAction C S a)).trans
        ((congrArg (Cohomology.GradedDiagramAut.toQuadratic Tdr C S)
          (gradedTwistEquiv_scalarGradedAction C S a)).trans
            ((Cohomology.toQuadratic_scalarGradedAction Tdr C S a).trans
              (quadraticTwistEquiv_scalarQuadraticAction C S a).symm)))

/-- The entire original scalar range maps onto the quadratic scalar range under restriction. -/
theorem map_scalarSubgroup_restrictionEquiv :
    (GradedDiagramAut.scalarSubgroup C S).map
      (restrictionEquiv C S hS hgen hn).toMonoidHom = DiagramAut.scalarSubgroup C S := by
  ext g
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (restrictionEquiv_scalarGradedAction C S hS hgen hn a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAction C S a, ⟨a, rfl⟩,
      restrictionEquiv_scalarGradedAction C S hS hgen hn a⟩

/-- The new ordinary quotient restriction is Mathlib congruence of the exact old restriction.
Its required scalar-image equality is proved above. Blueprint: T17 (`cor:t17`). -/
def scalarQuotientRestrictionEquiv :
    (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ≃*
      (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :=
  QuotientGroup.congr (GradedDiagramAut.scalarSubgroup C S) (DiagramAut.scalarSubgroup C S)
    (restrictionEquiv C S hS hgen hn) (map_scalarSubgroup_restrictionEquiv C S hS hgen hn)

/-- A representative uses the literal old ordinary degree-one restriction, including target. -/
theorem scalarQuotientRestrictionEquiv_map (g : GradedDiagramAut C S) :
    scalarQuotientRestrictionEquiv C S hS hgen hn (GradedDiagramAut.scalarQuotientMap C S g) =
      DiagramAut.scalarQuotientMap C S (GradedDiagramAut.toQuadratic C S g) :=
  congrArg (DiagramAut.scalarQuotientMap C S) (restrictionEquiv_apply C S hS hgen hn g)

/-- The quotient inverse uses the exact old ordinary inverse on every representative. -/
theorem scalarQuotientRestrictionEquiv_symm_map (g : DiagramAut C S) :
    (scalarQuotientRestrictionEquiv C S hS hgen hn).symm (DiagramAut.scalarQuotientMap C S g) =
      GradedDiagramAut.scalarQuotientMap C S ((restrictionEquiv C S hS hgen hn).symm g) := rfl

/-- The literal ordinary quotient restriction is continuous in both directions. -/
def scalarQuotientRestrictionContinuousEquiv :
    (GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) ≃ₜ*
      (DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) where
  toMulEquiv := scalarQuotientRestrictionEquiv C S hS hgen hn
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (GradedDiagramAut.scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut C S ↦
      scalarQuotientRestrictionEquiv C S hS hgen hn (GradedDiagramAut.scalarQuotientMap C S g))
    simp only [scalarQuotientRestrictionEquiv_map]
    exact QuotientGroup.continuous_mk.comp (GradedDiagramAut.continuous_toQuadratic C S)
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk (DiagramAut.scalarSubgroup C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut C S ↦
      (scalarQuotientRestrictionEquiv C S hS hgen hn).symm (DiagramAut.scalarQuotientMap C S g))
    simp only [scalarQuotientRestrictionEquiv_symm_map]
    exact QuotientGroup.continuous_mk.comp
      (restrictionContinuousEquiv C S hS hgen hn).continuous_invFun

/-- The topological restriction retains exactly the new literal quotient congruence. -/
theorem scalarQuotientRestrictionContinuousEquiv_toMulEquiv :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).toMulEquiv =
      scalarQuotientRestrictionEquiv C S hS hgen hn := rfl

/-- The forward function is exactly the new quotient congruence. -/
theorem scalarQuotientRestrictionContinuousEquiv_coe :
    ⇑(scalarQuotientRestrictionContinuousEquiv C S hS hgen hn) =
      scalarQuotientRestrictionEquiv C S hS hgen hn := rfl

/-- The whole quotient value uses the new literal algebraic congruence. -/
theorem scalarQuotientRestrictionContinuousEquiv_apply
    (z : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) :
    scalarQuotientRestrictionContinuousEquiv C S hS hgen hn z =
      scalarQuotientRestrictionEquiv C S hS hgen hn z := rfl

/-- The inverse is exactly the inverse of the new literal algebraic congruence. -/
theorem scalarQuotientRestrictionContinuousEquiv_symm_apply
    (z : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm z =
      (scalarQuotientRestrictionEquiv C S hS hgen hn).symm z := rfl

/-- The continuous restriction has the literal ordinary representative formula. -/
theorem scalarQuotientRestrictionContinuousEquiv_map (g : GradedDiagramAut C S) :
    scalarQuotientRestrictionContinuousEquiv C S hS hgen hn
        (GradedDiagramAut.scalarQuotientMap C S g) =
      DiagramAut.scalarQuotientMap C S (GradedDiagramAut.toQuadratic C S g) :=
  scalarQuotientRestrictionEquiv_map C S hS hgen hn g

/-- The continuous inverse retains the exact old ordinary inverse on representatives. -/
theorem scalarQuotientRestrictionContinuousEquiv_symm_map (g : DiagramAut C S) :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm
        (DiagramAut.scalarQuotientMap C S g) =
      GradedDiagramAut.scalarQuotientMap C S ((restrictionEquiv C S hS hgen hn).symm g) :=
  scalarQuotientRestrictionEquiv_symm_map C S hS hgen hn g

/-- Restriction followed by its inverse recovers the original graded quotient class. -/
theorem scalarQuotientRestrictionContinuousEquiv_left_inv
    (z : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm
      (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn z) = z :=
  (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm_apply_apply z

/-- The inverse followed by restriction recovers the original quadratic quotient class. -/
theorem scalarQuotientRestrictionContinuousEquiv_right_inv
    (z : DiagramAut C S ⧸ DiagramAut.scalarSubgroup C S) :
    scalarQuotientRestrictionContinuousEquiv C S hS hgen hn
      ((scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).symm z) = z :=
  (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).apply_symm_apply z

/-- The new ordinary quotient congruence is the exact local actual restriction between twists. -/
theorem scalarQuotientRestrictionEquiv_eq_composite :
    scalarQuotientRestrictionEquiv C S hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistEquiv C S).trans
        ((Cohomology.localScalarQuotientRestrictionEquiv Tdr C S hS hgen hn).trans
          (DiagramAut.scalarQuotientTwistEquiv C S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change scalarQuotientRestrictionEquiv C S hS hgen hn
    (GradedDiagramAut.scalarQuotientMap C S g) = _
  apply (DiagramAut.scalarQuotientTwistEquiv C S).injective
  have h := (congrArg (DiagramAut.scalarQuotientTwistEquiv C S)
    (scalarQuotientRestrictionEquiv_map C S hS hgen hn g)).trans
      ((DiagramAut.scalarQuotientTwistEquiv_map C S
        (GradedDiagramAut.toQuadratic C S g)).trans
          ((congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C S)
            (GradedDiagramAut.toQuadratic_comparison C S g)).trans
              ((Cohomology.localScalarQuotientRestrictionEquiv_map Tdr C S hS hgen hn
                (gradedTwistEquiv C S g)).symm.trans
                  (congrArg (Cohomology.localScalarQuotientRestrictionEquiv Tdr C S hS hgen hn)
                    (GradedDiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((DiagramAut.scalarQuotientTwistEquiv C S).apply_symm_apply _).symm

/-- The topological ordinary quotient restriction retains the exact local actual composite. -/
theorem scalarQuotientRestrictionContinuousEquiv_comparison :
    scalarQuotientRestrictionContinuousEquiv C S hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
        ((Cohomology.localScalarQuotientRestrictionContinuousEquiv Tdr C S hS hgen hn).trans
          (DiagramAut.scalarQuotientTwistContinuousEquiv C S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientRestrictionEquiv_eq_composite C S hS hgen hn) z

/-- The new ordinary quotient congruence is the exact domain actual restriction between twists. -/
theorem scalarQuotientRestrictionEquiv_eq_domain_composite :
    scalarQuotientRestrictionEquiv C S hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistEquiv C S).trans
        ((Cohomology.domainScalarQuotientRestrictionEquiv Tdr C S hS hgen hn).trans
          (DiagramAut.scalarQuotientTwistEquiv C S).symm) := by
  apply MulEquiv.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change scalarQuotientRestrictionEquiv C S hS hgen hn
    (GradedDiagramAut.scalarQuotientMap C S g) = _
  apply (DiagramAut.scalarQuotientTwistEquiv C S).injective
  have h := (congrArg (DiagramAut.scalarQuotientTwistEquiv C S)
    (scalarQuotientRestrictionEquiv_map C S hS hgen hn g)).trans
      ((DiagramAut.scalarQuotientTwistEquiv_map C S
        (GradedDiagramAut.toQuadratic C S g)).trans
          ((congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C S)
            (GradedDiagramAut.toQuadratic_comparison C S g)).trans
              ((Cohomology.domainScalarQuotientRestrictionEquiv_map Tdr C S hS hgen hn
                (gradedTwistEquiv C S g)).symm.trans
                  (congrArg (Cohomology.domainScalarQuotientRestrictionEquiv Tdr C S hS hgen hn)
                    (GradedDiagramAut.scalarQuotientTwistEquiv_map C S g).symm))))
  exact h.trans ((DiagramAut.scalarQuotientTwistEquiv C S).apply_symm_apply _).symm

/-- The topological ordinary quotient restriction retains the exact domain actual composite. -/
theorem scalarQuotientRestrictionContinuousEquiv_eq_domain_composite :
    scalarQuotientRestrictionContinuousEquiv C S hS hgen hn =
      (GradedDiagramAut.scalarQuotientTwistContinuousEquiv C S).trans
        ((Cohomology.domainScalarQuotientRestrictionContinuousEquiv Tdr C S hS hgen hn).trans
          (DiagramAut.scalarQuotientTwistContinuousEquiv C S).symm) := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (scalarQuotientRestrictionEquiv_eq_domain_composite C S hS hgen hn) z

/-- Both ordinary algebraic quotient classifiers read the same coordinate under restriction. -/
theorem scalarQuotientEquiv_restriction
    (z : GradedDiagramAut C S ⧸ GradedDiagramAut.scalarSubgroup C S) :
    DiagramAut.scalarQuotientEquiv C S hS hgen hn
      (scalarQuotientRestrictionEquiv C S hS hgen hn z) =
        GradedDiagramAut.scalarQuotientEquiv C S hS hgen hn z := by
  have h := (congrArg (DiagramAut.scalarQuotientTwistEquiv C S)
    (DFunLike.congr_fun (scalarQuotientRestrictionEquiv_eq_composite C S hS hgen hn) z))
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  exact (congrArg (Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn) h).trans
    (Cohomology.localScalarQuotientEquiv_restriction Tdr C S hS hgen hn _)

section Pointwise

open scoped GaloisPointwise

/-- The ordinary quotient restriction retains the same Galois coordinate. -/
theorem scalarQuotientContinuousEquiv_trans_restriction :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).trans
      (DiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn) =
        GradedDiagramAut.scalarQuotientContinuousEquiv C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact scalarQuotientEquiv_restriction C S hS hgen hn z

end Pointwise

/-- The ordinary quotient restriction retains the same Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquiv_trans_restriction (hK : KrullFixingCondition k₀ k) :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).trans
      (DiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK) =
        GradedDiagramAut.scalarQuotientKrullContinuousEquiv C S hS hgen hn hK := by
  apply DFunLike.ext
  intro z
  exact scalarQuotientEquiv_restriction C S hS hgen hn z

/-- The ordinary quotient restriction retains the same Galois coordinate. -/
theorem scalarQuotientKrullContinuousEquivOfIsAlgebraic_trans_restriction [Algebra.IsAlgebraic k₀
    k] :
    (scalarQuotientRestrictionContinuousEquiv C S hS hgen hn).trans
      (DiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn) =
        GradedDiagramAut.scalarQuotientKrullContinuousEquivOfIsAlgebraic C S hS hgen hn := by
  apply DFunLike.ext
  intro z
  exact scalarQuotientEquiv_restriction C S hS hgen hn z

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
