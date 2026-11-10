/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Comparison

/-!
# The actual scalar quotient comparisons are homeomorphisms

Both old actual-to-presentation scalar quotient maps are topological group isomorphisms
for Mathlib's quotient topologies of the directly defined diagram topologies. Continuity
in both directions descends along the quotient maps from the old adapter representatives.
No classification, scalar closedness or field-extension hypothesis is needed.

The main definitions are `DiagramAut.scalarQuotientContinuousComparison` and
`GradedDiagramAut.scalarQuotientContinuousComparison`; their underlying maps, inverses and
representative formulas are the existing algebraic comparisons.

Blueprint: the scalar quotient clauses of T14 (`thm:t14`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open scoped FiniteStageTopology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- The inverse old quotient comparison retains the opposite adapter representative. -/
theorem scalarQuotientComparison_symm_map (g : HyperplaneGT.DiagramAut R C S) :
    (scalarQuotientComparison T C S).symm
        (HyperplaneGT.DiagramAut.scalarQuotientMap R C S g) =
      scalarQuotientMap T C S ((degreeOneDiagramEquiv T C S).symm g) := by
  apply (scalarQuotientComparison T C S).injective
  rw [MulEquiv.apply_symm_apply, scalarQuotientComparison_map, MulEquiv.apply_symm_apply]

/-- The exact old scalar quotient comparison with both quotient-topology continuity proofs.
Blueprint: the scalar quotient clause of T14 (`thm:t14`). -/
def scalarQuotientContinuousComparison :
    (DiagramAut T C S ⧸ scalarSubgroup T C S) ≃ₜ*
      (HyperplaneGT.DiagramAut R C S ⧸ HyperplaneGT.DiagramAut.scalarSubgroup R C S) where
  __ := scalarQuotientComparison T C S
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup T C S)).continuous_iff.mpr
    change Continuous (fun g : DiagramAut T C S ↦
      scalarQuotientComparison T C S (scalarQuotientMap T C S g))
    simp only [scalarQuotientComparison_map]
    change Continuous (QuotientGroup.mk ∘
      ⇑(degreeOneDiagramContinuousEquiv T C S).toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (degreeOneDiagramContinuousEquiv T C S).continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (HyperplaneGT.DiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : HyperplaneGT.DiagramAut R C S ↦
      (scalarQuotientComparison T C S).symm
        (HyperplaneGT.DiagramAut.scalarQuotientMap R C S g))
    simp only [scalarQuotientComparison_symm_map]
    change Continuous (QuotientGroup.mk ∘
      ⇑(degreeOneDiagramContinuousEquiv T C S).symm.toHomeomorph)
    exact QuotientGroup.continuous_mk.comp
      (degreeOneDiagramContinuousEquiv T C S).symm.continuous

/-- The quotient topological upgrade keeps the old multiplicative equivalence exactly. -/
theorem scalarQuotientContinuousComparison_toMulEquiv :
    (scalarQuotientContinuousComparison T C S).toMulEquiv =
      scalarQuotientComparison T C S := rfl

/-- The quotient topological upgrade keeps the old forward function. -/
theorem coe_scalarQuotientContinuousComparison :
    ⇑(scalarQuotientContinuousComparison T C S) = scalarQuotientComparison T C S := rfl

/-- The quotient upgrade evaluates by the old quotient comparison. -/
theorem scalarQuotientContinuousComparison_apply
    (x : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientContinuousComparison T C S x = scalarQuotientComparison T C S x := rfl

/-- The inverse quotient upgrade evaluates by the old inverse comparison. -/
theorem scalarQuotientContinuousComparison_symm_apply
    (x : HyperplaneGT.DiagramAut R C S ⧸ HyperplaneGT.DiagramAut.scalarSubgroup R C S) :
    (scalarQuotientContinuousComparison T C S).symm x =
      (scalarQuotientComparison T C S).symm x := rfl

/-- The topological quotient comparison preserves the actual adapter representative. -/
theorem scalarQuotientContinuousComparison_map (g : DiagramAut T C S) :
    scalarQuotientContinuousComparison T C S (scalarQuotientMap T C S g) =
      HyperplaneGT.DiagramAut.scalarQuotientMap R C S (degreeOneDiagramEquiv T C S g) :=
  scalarQuotientComparison_map T C S g

/-- The inverse topological quotient comparison preserves the opposite representative. -/
theorem scalarQuotientContinuousComparison_symm_map (g : HyperplaneGT.DiagramAut R C S) :
    (scalarQuotientContinuousComparison T C S).symm
        (HyperplaneGT.DiagramAut.scalarQuotientMap R C S g) =
      scalarQuotientMap T C S ((degreeOneDiagramEquiv T C S).symm g) :=
  scalarQuotientComparison_symm_map T C S g

end DiagramAut

namespace GradedDiagramAut

/-- The inverse old quotient comparison retains the opposite adapter representative. -/
theorem scalarQuotientComparison_symm_map (g : HyperplaneGT.GradedDiagramAut R C S) :
    (scalarQuotientComparison T C S).symm
        (HyperplaneGT.GradedDiagramAut.scalarQuotientMap R C S g) =
      scalarQuotientMap T C S ((gradedDiagramEquiv T C S).symm g) := by
  apply (scalarQuotientComparison T C S).injective
  rw [MulEquiv.apply_symm_apply, scalarQuotientComparison_map, MulEquiv.apply_symm_apply]

/-- The exact old scalar quotient comparison with both quotient-topology continuity proofs.
Blueprint: the scalar quotient clause of T14 (`thm:t14`). -/
def scalarQuotientContinuousComparison :
    (GradedDiagramAut T C S ⧸ scalarSubgroup T C S) ≃ₜ*
      (HyperplaneGT.GradedDiagramAut R C S ⧸
        HyperplaneGT.GradedDiagramAut.scalarSubgroup R C S) where
  __ := scalarQuotientComparison T C S
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (scalarSubgroup T C S)).continuous_iff.mpr
    change Continuous (fun g : GradedDiagramAut T C S ↦
      scalarQuotientComparison T C S (scalarQuotientMap T C S g))
    simp only [scalarQuotientComparison_map]
    change Continuous (QuotientGroup.mk ∘
      ⇑(gradedDiagramContinuousEquiv T C S).toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (gradedDiagramContinuousEquiv T C S).continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk
      (HyperplaneGT.GradedDiagramAut.scalarSubgroup R C S)).continuous_iff.mpr
    change Continuous (fun g : HyperplaneGT.GradedDiagramAut R C S ↦
      (scalarQuotientComparison T C S).symm
        (HyperplaneGT.GradedDiagramAut.scalarQuotientMap R C S g))
    simp only [scalarQuotientComparison_symm_map]
    change Continuous (QuotientGroup.mk ∘
      ⇑(gradedDiagramContinuousEquiv T C S).symm.toHomeomorph)
    exact QuotientGroup.continuous_mk.comp (gradedDiagramContinuousEquiv T C S).symm.continuous

/-- The quotient topological upgrade keeps the old multiplicative equivalence exactly. -/
theorem scalarQuotientContinuousComparison_toMulEquiv :
    (scalarQuotientContinuousComparison T C S).toMulEquiv =
      scalarQuotientComparison T C S := rfl

/-- The quotient topological upgrade keeps the old forward function. -/
theorem coe_scalarQuotientContinuousComparison :
    ⇑(scalarQuotientContinuousComparison T C S) = scalarQuotientComparison T C S := rfl

/-- The quotient upgrade evaluates by the old quotient comparison. -/
theorem scalarQuotientContinuousComparison_apply
    (x : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientContinuousComparison T C S x = scalarQuotientComparison T C S x := rfl

/-- The inverse quotient upgrade evaluates by the old inverse comparison. -/
theorem scalarQuotientContinuousComparison_symm_apply
    (x : HyperplaneGT.GradedDiagramAut R C S ⧸ HyperplaneGT.GradedDiagramAut.scalarSubgroup R C S) :
    (scalarQuotientContinuousComparison T C S).symm x =
      (scalarQuotientComparison T C S).symm x := rfl

/-- The topological quotient comparison preserves the actual adapter representative. -/
theorem scalarQuotientContinuousComparison_map (g : GradedDiagramAut T C S) :
    scalarQuotientContinuousComparison T C S (scalarQuotientMap T C S g) =
      HyperplaneGT.GradedDiagramAut.scalarQuotientMap R C S (gradedDiagramEquiv T C S g) :=
  scalarQuotientComparison_map T C S g

/-- The inverse topological quotient comparison preserves the opposite representative. -/
theorem scalarQuotientContinuousComparison_symm_map (g : HyperplaneGT.GradedDiagramAut R C S) :
    (scalarQuotientContinuousComparison T C S).symm
        (HyperplaneGT.GradedDiagramAut.scalarQuotientMap R C S g) =
      scalarQuotientMap T C S ((gradedDiagramEquiv T C S).symm g) :=
  scalarQuotientComparison_symm_map T C S g

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology
