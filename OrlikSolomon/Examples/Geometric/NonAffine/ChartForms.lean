/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Sections

/-!
# Differential forms on the projective-line cover

Polynomial and Laurent polynomial forms identify with the actual sheaf forms on the two
standard charts and their intersection. These identifications preserve differentials and
restriction maps, so they compare the actual cover complex with its algebraic model.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Module Polynomial TopologicalSpace
open scoped LaurentPolynomial

namespace OrlikSolomon.Geometric.Examples

open Geometric.DeRham OrlikSolomon.DeRham

universe u

variable (k : Type u) [Field k]

/-- Polynomial forms are the actual sheaf forms on a standard projective-line chart. -/
def projectiveLineChartFormsEquiv (i : Fin 2) (n : ℕ) :
    (⋀[k[X]]^n Ω[k[X]⁄k]) ≃ₗ[k]
      (formsSheaf k (projectiveLine k) n).obj.obj (op (projectiveLineChart k i)) :=
  ({ Forms.mapPower (projectiveLineChartSectionsEquiv k i).symm.toAlgHom n with
    invFun := Forms.mapPower (projectiveLineChartSectionsEquiv k i).toAlgHom n
    left_inv a :=
      Subtype.ext ((Forms.mapEquiv (projectiveLineChartSectionsEquiv k i).symm).left_inv a.val)
    right_inv a :=
      Subtype.ext ((Forms.mapEquiv (projectiveLineChartSectionsEquiv k i).symm).right_inv a.val) } :
      _ ≃ₗ[k] _).trans
    (affineOpenFormsComparison _ _ (isAffineOpen_projectiveLineChart k i) n)

/-- The intersection of the two standard projective-line charts is affine. -/
lemma isAffineOpen_projectiveLineOverlap : IsAffineOpen (projectiveLineOverlap k) := by
  rw [← projectiveLineOverlapMap_opensRange]
  exact isAffineOpen_opensRange (projectiveLineOverlapMap k).left

/-- Laurent polynomial forms are the actual sheaf forms on the chart intersection. -/
def projectiveLineOverlapFormsEquiv (n : ℕ) :
    (⋀[LaurentPolynomial k]^n Ω[LaurentPolynomial k⁄k]) ≃ₗ[k]
      (formsSheaf k (projectiveLine k) n).obj.obj (op (projectiveLineOverlap k)) :=
  ({ Forms.mapPower (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom n with
    invFun := Forms.mapPower (projectiveLineOverlapSectionsEquiv k).toAlgHom n
    left_inv a :=
      Subtype.ext ((Forms.mapEquiv (projectiveLineOverlapSectionsEquiv k).symm).left_inv a.val)
    right_inv a :=
      Subtype.ext ((Forms.mapEquiv (projectiveLineOverlapSectionsEquiv k).symm).right_inv a.val) } :
      _ ≃ₗ[k] _).trans
    (affineOpenFormsComparison _ _ (isAffineOpen_projectiveLineOverlap k) n)

/-- The chart comparison sends a polynomial form to its sheafification. -/
lemma projectiveLineChartFormsEquiv_apply (i : Fin 2) (n : ℕ) (a : ⋀[k[X]]^n Ω[k[X]⁄k]) :
    projectiveLineChartFormsEquiv k i n a =
      (formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineChart k i))
        (Forms.mapPower (projectiveLineChartSectionsEquiv k i).symm.toAlgHom n a) := rfl

/-- The overlap comparison sends a Laurent form to its sheafification. -/
lemma projectiveLineOverlapFormsEquiv_apply (n : ℕ)
    (a : ⋀[LaurentPolynomial k]^n Ω[LaurentPolynomial k⁄k]) :
    projectiveLineOverlapFormsEquiv k n a =
      (formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineOverlap k))
        (Forms.mapPower (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom n a) := rfl

private lemma restrict_zero_ring :
    (sectionRestriction k (projectiveLine k) (homOfLE (projectiveLineOverlap_le_chart k 0))).comp
        (projectiveLineChartSectionsEquiv k 0).symm.toAlgHom =
      (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom.comp
        (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) := by
  apply AlgHom.ext
  intro a
  apply (projectiveLineOverlapSectionsEquiv k).injective
  have h := AlgHom.congr_fun (projectiveLineChartSectionsEquiv_restrict_zero k)
    ((projectiveLineChartSectionsEquiv k 0).symm a)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using h

private lemma restrict_one_ring :
    (sectionRestriction k (projectiveLine k) (homOfLE (projectiveLineOverlap_le_chart k 1))).comp
        (projectiveLineChartSectionsEquiv k 1).symm.toAlgHom =
      (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom.comp
        (LaurentPolynomial.invert.toAlgHom.comp
          (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)) := by
  apply AlgHom.ext
  intro a
  apply (projectiveLineOverlapSectionsEquiv k).injective
  have h := AlgHom.congr_fun (projectiveLineChartSectionsEquiv_restrict_one k)
    ((projectiveLineChartSectionsEquiv k 1).symm a)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using h

/-- Restriction from the first chart is the Laurent inclusion on forms. -/
lemma projectiveLineChartFormsEquiv_restrict_zero (n : ℕ) (a : ⋀[k[X]]^n Ω[k[X]⁄k]) :
    (formsSheaf k (projectiveLine k) n).obj.map
        (homOfLE (projectiveLineOverlap_le_chart k 0)).op (projectiveLineChartFormsEquiv k 0 n a) =
      projectiveLineOverlapFormsEquiv k n
        (Forms.mapPower (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) n a) := by
  rw [projectiveLineChartFormsEquiv_apply, projectiveLineOverlapFormsEquiv_apply]
  have h := ConcreteCategory.congr_hom
    ((formsSheafUnit k (projectiveLine k) n).naturality
      (homOfLE (projectiveLineOverlap_le_chart k 0)).op)
    (Forms.mapPower (projectiveLineChartSectionsEquiv k 0).symm.toAlgHom n a)
  change (formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineOverlap k))
    (Forms.mapPower (sectionRestriction k (projectiveLine k)
        (homOfLE (projectiveLineOverlap_le_chart k 0))) n
      (Forms.mapPower (projectiveLineChartSectionsEquiv k 0).symm.toAlgHom n a)) = _ at h
  apply h.symm.trans
  apply congrArg ((formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineOverlap k)))
  exact (LinearMap.congr_fun (Forms.mapPower_comp
    (sectionRestriction k (projectiveLine k) (homOfLE (projectiveLineOverlap_le_chart k 0)))
    (projectiveLineChartSectionsEquiv k 0).symm.toAlgHom n) a).symm.trans
      ((congrArg (fun f => Forms.mapPower f n a) (restrict_zero_ring k)).trans
        (LinearMap.congr_fun (Forms.mapPower_comp
          (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom
          (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) n) a))

/-- Restriction from the second chart is Laurent inversion on forms. -/
lemma projectiveLineChartFormsEquiv_restrict_one (n : ℕ) (a : ⋀[k[X]]^n Ω[k[X]⁄k]) :
    (formsSheaf k (projectiveLine k) n).obj.map
        (homOfLE (projectiveLineOverlap_le_chart k 1)).op (projectiveLineChartFormsEquiv k 1 n a) =
      projectiveLineOverlapFormsEquiv k n
        (Forms.mapPower (LaurentPolynomial.invert.toAlgHom.comp
          (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)) n a) := by
  rw [projectiveLineChartFormsEquiv_apply, projectiveLineOverlapFormsEquiv_apply]
  have h := ConcreteCategory.congr_hom
    ((formsSheafUnit k (projectiveLine k) n).naturality
      (homOfLE (projectiveLineOverlap_le_chart k 1)).op)
    (Forms.mapPower (projectiveLineChartSectionsEquiv k 1).symm.toAlgHom n a)
  change (formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineOverlap k))
    (Forms.mapPower (sectionRestriction k (projectiveLine k)
        (homOfLE (projectiveLineOverlap_le_chart k 1))) n
      (Forms.mapPower (projectiveLineChartSectionsEquiv k 1).symm.toAlgHom n a)) = _ at h
  apply h.symm.trans
  apply congrArg ((formsSheafUnit k (projectiveLine k) n).app (op (projectiveLineOverlap k)))
  exact (LinearMap.congr_fun (Forms.mapPower_comp
    (sectionRestriction k (projectiveLine k) (homOfLE (projectiveLineOverlap_le_chart k 1)))
    (projectiveLineChartSectionsEquiv k 1).symm.toAlgHom n) a).symm.trans
      ((congrArg (fun f => Forms.mapPower f n a) (restrict_one_ring k)).trans
        (LinearMap.congr_fun (Forms.mapPower_comp
          (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom
          (LaurentPolynomial.invert.toAlgHom.comp
            (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)) n) a))

/-- The actual de Rham sheaf complex evaluated on an open of the projective line. -/
def projectiveLineFormsOn (U : (projectiveLine k).left.Opens) :
    CochainComplex (ModuleCat k) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology (projectiveLine k).left) (ModuleCat k) ⋙
    (evaluation _ _).obj (op U)).mapHomologicalComplex _).obj
      (formsComplexNat k (projectiveLine k))

/-- Evaluation on an open has the expected sheaf-form terms. -/
@[simp]
lemma projectiveLineFormsOn_X (U : (projectiveLine k).left.Opens) (n : ℕ) :
    (projectiveLineFormsOn k U).X n = (formsSheaf k (projectiveLine k) n).obj.obj (op U) := rfl

/-- Evaluation on an open has the actual sheaf differential. -/
@[simp]
lemma projectiveLineFormsOn_d (U : (projectiveLine k).left.Opens) (n : ℕ) :
    (projectiveLineFormsOn k U).d n (n + 1) =
      (formsSheafD k (projectiveLine k) n).hom.app (op U) := by
  simp [projectiveLineFormsOn]

/-- The standard-chart form comparison preserves the de Rham differential. -/
lemma projectiveLineChartFormsEquiv_d (i : Fin 2) (n : ℕ)
    (a : ⋀[k[X]]^n Ω[k[X]⁄k]) :
    (formsSheafD k (projectiveLine k) n).hom.app (op (projectiveLineChart k i))
        (projectiveLineChartFormsEquiv k i n a) =
      projectiveLineChartFormsEquiv k i (n + 1) (powerD k k[X] n a) := by
  change (formsSheafD k (projectiveLine k) n).hom.app (op (projectiveLineChart k i))
      (affineOpenFormsComparison _ _ _ n
        (Forms.mapPower (projectiveLineChartSectionsEquiv k i).symm.toAlgHom n a)) =
    affineOpenFormsComparison _ _ _ (n + 1)
      (Forms.mapPower (projectiveLineChartSectionsEquiv k i).symm.toAlgHom (n + 1)
        (powerD k k[X] n a))
  rw [affineOpenFormsComparison_d, Forms.mapPower_powerD]

/-- The overlap form comparison preserves the de Rham differential. -/
lemma projectiveLineOverlapFormsEquiv_d (n : ℕ)
    (a : ⋀[LaurentPolynomial k]^n Ω[LaurentPolynomial k⁄k]) :
    (formsSheafD k (projectiveLine k) n).hom.app (op (projectiveLineOverlap k))
        (projectiveLineOverlapFormsEquiv k n a) =
      projectiveLineOverlapFormsEquiv k (n + 1) (powerD k (LaurentPolynomial k) n a) := by
  change (formsSheafD k (projectiveLine k) n).hom.app (op (projectiveLineOverlap k))
      (affineOpenFormsComparison _ _ _ n
        (Forms.mapPower (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom n a)) =
    affineOpenFormsComparison _ _ _ (n + 1)
      (Forms.mapPower (projectiveLineOverlapSectionsEquiv k).symm.toAlgHom (n + 1)
        (powerD k (LaurentPolynomial k) n a))
  rw [affineOpenFormsComparison_d, Forms.mapPower_powerD]

/-- Polynomial de Rham forms are the actual complex on each standard chart. -/
def projectiveLineChartFormsComplexIso (i : Fin 2) :
    complex k k[X] ≅ projectiveLineFormsOn k (projectiveLineChart k i) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (projectiveLineChartFormsEquiv k i n).toModuleIso) (by
      rintro n _ rfl
      rw [projectiveLineFormsOn_d, complex_d]
      ext a
      exact projectiveLineChartFormsEquiv_d k i n a)

/-- Laurent de Rham forms are the actual complex on the chart intersection. -/
def projectiveLineOverlapFormsComplexIso :
    complex k (LaurentPolynomial k) ≅ projectiveLineFormsOn k (projectiveLineOverlap k) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (projectiveLineOverlapFormsEquiv k n).toModuleIso) (by
      rintro n _ rfl
      rw [projectiveLineFormsOn_d, complex_d]
      ext a
      exact projectiveLineOverlapFormsEquiv_d k n a)

/-- The actual sheaf restriction from a standard chart to the intersection. -/
def projectiveLineFormsRestriction (i : Fin 2) :
    projectiveLineFormsOn k (projectiveLineChart k i) ⟶
      projectiveLineFormsOn k (projectiveLineOverlap k) :=
  CochainComplex.ofHom (fun n => (formsSheaf k (projectiveLine k) n).obj.map
    (homOfLE (projectiveLineOverlap_le_chart k i)).op) (by
      intro n
      rw [projectiveLineFormsOn_d, projectiveLineFormsOn_d]
      exact (formsSheafD k (projectiveLine k) n).hom.naturality _)

/-- The first-chart complex comparison intertwines actual restriction and Laurent inclusion. -/
lemma projectiveLineChartFormsComplexIso_restrict_zero :
    (projectiveLineChartFormsComplexIso k 0).hom ≫ projectiveLineFormsRestriction k 0 =
      complexMap (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k) ≫
        (projectiveLineOverlapFormsComplexIso k).hom := by
  ext n a
  exact projectiveLineChartFormsEquiv_restrict_zero k n a

/-- The second-chart complex comparison intertwines actual restriction and Laurent inversion. -/
lemma projectiveLineChartFormsComplexIso_restrict_one :
    (projectiveLineChartFormsComplexIso k 1).hom ≫ projectiveLineFormsRestriction k 1 =
      complexMap (LaurentPolynomial.invert.toAlgHom.comp
        (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)) ≫
          (projectiveLineOverlapFormsComplexIso k).hom := by
  ext n a
  exact projectiveLineChartFormsEquiv_restrict_one k n a

end OrlikSolomon.Geometric.Examples
