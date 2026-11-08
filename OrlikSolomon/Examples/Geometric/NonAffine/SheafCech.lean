/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.CechZero
public import OrlikSolomon.Examples.Geometric.NonAffine.ChartForms
public import OrlikSolomon.Examples.Geometric.NonAffine.ChartSum
public import OrlikSolomon.Examples.Geometric.NonAffine.GlobalForms

/-!
# The actual projective-line Čech–de Rham complex

The total complex here uses the actual sheaves of relative forms on the standard chart
cover of `ℙ¹`. The chart and overlap comparisons identify it with the concrete polynomial
and Laurent model, including the two restriction maps and the total differential.
Over a characteristic-zero field it has cohomology `k` in degrees zero and two and zero
in all other degrees.
The degree-two generator comes from `[dT/T]` on the overlap.

This computes precisely the two-open complex required by Mayer–Vietoris descent. It makes
no assertion of a non-affine de Rham instance or independence of arbitrary Čech covers.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.DeRham
open scoped Polynomial LaurentPolynomial

universe u

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u) [Field k]

/-- The restriction difference of the actual forms sheaves on the standard two-chart cover. -/
def projectiveLineSheafRestrictionDifference :=
  chartSumDifference (projectiveLineFormsRestriction k 0) (projectiveLineFormsRestriction k 1)

/-- The total Čech–de Rham complex of the actual standard cover, with differential
`δ + (-1)^a d` in Čech degree `a`. -/
def projectiveLineSheafCechComplex : CochainComplex (ModuleCat k) ℕ :=
  twoChartFiber (projectiveLineSheafRestrictionDifference k)

/-- The two chart comparisons together identify the source complexes of the difference maps. -/
def projectiveLineChartSumComparison : projectiveLineChartComplex k ≅
    chartSumComplex (projectiveLineFormsOn k (projectiveLineChart k 0))
      (projectiveLineFormsOn k (projectiveLineChart k 1)) :=
  (eqToIso (by rfl : projectiveLineChartComplex k =
    chartSumComplex (complex k k[X]) (complex k k[X]))) ≪≫
      chartSumIso (projectiveLineChartFormsComplexIso k 0) (projectiveLineChartFormsComplexIso k 1)

/-- The chart sum and overlap comparisons intertwine both actual restrictions. -/
lemma projectiveLineChartSumComparison_difference :
    (projectiveLineChartSumComparison k).hom ≫ projectiveLineSheafRestrictionDifference k =
      projectiveLineRestrictionDifference k ≫ (projectiveLineOverlapFormsComplexIso k).hom := by
  change (chartSumIso (projectiveLineChartFormsComplexIso k 0)
    (projectiveLineChartFormsComplexIso k 1)).hom ≫
      chartSumDifference (projectiveLineFormsRestriction k 0) (projectiveLineFormsRestriction k 1) =
    chartSumDifference (complexMap (projectiveLineFirstRestriction k))
      (complexMap (projectiveLineSecondRestriction k)) ≫
        (projectiveLineOverlapFormsComplexIso k).hom
  exact chartSumIso_difference _ _ _ _ _ _ _
    (projectiveLineChartFormsComplexIso_restrict_zero k)
    (projectiveLineChartFormsComplexIso_restrict_one k)

/-- The polynomial/Laurent model is the total complex of the actual scheme cover. -/
def projectiveLineSheafCechIso : projectiveLineCechComplex k ≅
    projectiveLineSheafCechComplex k :=
  twoChartFiberIso _ _ (projectiveLineChartSumComparison k)
    (projectiveLineOverlapFormsComplexIso k) (projectiveLineChartSumComparison_difference k)

/-- The actual two-chart Čech complex has `H⁰ = k`. -/
def projectiveLineSheafCechHomologyZeroEquiv :
    (projectiveLineSheafCechComplex k).homology 0 ≃ₗ[k] k :=
  ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) 0).symm.toLinearEquiv).trans
      (projectiveLineCechHomologyZeroEquiv k)

section CharacteristicZero
variable [CharZero k]

/-- The actual two-chart Čech complex has `H² = k`. -/
def projectiveLineSheafCechHomologyTwoEquiv :
    (projectiveLineSheafCechComplex k).homology 2 ≃ₗ[k] k :=
  ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) 2).symm.toLinearEquiv).trans
      (projectiveLineCechHomologyTwoEquiv k)

/-- The logarithmic overlap class in the actual cover's second cohomology. -/
def projectiveLineSheafCechLogClass : (projectiveLineSheafCechComplex k).homology 2 :=
  (HomologicalComplex.homologyMapIso
      (projectiveLineSheafCechIso k) 2).hom (projectiveLineCechLogClass k)

/-- The actual logarithmic overlap class has coefficient one. -/
@[simp]
lemma projectiveLineSheafCechHomologyTwoEquiv_logClass :
    projectiveLineSheafCechHomologyTwoEquiv k (projectiveLineSheafCechLogClass k) = 1 := by
  change projectiveLineCechHomologyTwoEquiv k
    ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) 2).inv
      ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) 2).hom
        (projectiveLineCechLogClass k))) = 1
  rw [Iso.hom_inv_id_apply, projectiveLineCechHomologyTwoEquiv_logClass]

/-- The actual cover has a nonzero degree-two logarithmic class. -/
lemma projectiveLineSheafCechLogClass_ne_zero : projectiveLineSheafCechLogClass k ≠ 0 := by
  intro h
  have hh := projectiveLineSheafCechHomologyTwoEquiv_logClass k
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- The actual cover's first cohomology vanishes. -/
theorem projectiveLineSheafCechComplex_isZero_homology_one :
    Limits.IsZero ((projectiveLineSheafCechComplex k).homology 1) :=
  Limits.IsZero.of_iso (projectiveLineCechComplex_isZero_homology_one k)
    ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) 1).symm)

/-- The actual cover has no cohomology above degree two. -/
theorem projectiveLineSheafCechComplex_isZero_homology_succ_succ_succ (n : ℕ) :
    Limits.IsZero ((projectiveLineSheafCechComplex k).homology (n + 3)) :=
  Limits.IsZero.of_iso (projectiveLineCechComplex_isZero_homology_succ_succ_succ k n)
    ((HomologicalComplex.homologyMapIso (projectiveLineSheafCechIso k) (n + 3)).symm)

/-- No map from the global-forms complex to the actual cover complex is a quasi-isomorphism.
Thus the global-forms definition cannot satisfy the two-open descent required of an extension
of the affine realization. -/
theorem projectiveLineGlobalForms_not_quasiIso
    (f : Geometric.DeRham.globalFormsComplex k (projectiveLine k) ⟶
      projectiveLineSheafCechComplex k) : ¬ QuasiIso f := by
  intro hf
  let := hf
  have hz : Limits.IsZero ((projectiveLineSheafCechComplex k).homology 2) :=
    (projectiveLineGlobalFormsHomologyPositive_isZero k 1).of_iso
      (asIso (HomologicalComplex.homologyMap f 2)).symm
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  exact projectiveLineSheafCechLogClass_ne_zero k (hs.elim _ _)

end CharacteristicZero

end OrlikSolomon.Geometric.Examples
