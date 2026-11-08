/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Overlap
public import OrlikSolomon.DeRham.Schemes.GlobalSections

/-!
# Functions on the projective-line charts

The actual affine chart maps identify functions on the two standard opens with polynomial
rings and functions on their intersection with the Laurent polynomial ring. Their restriction
maps are respectively the Laurent inclusion and its composite with inversion.

Blueprint: the global-sections computation in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Module Polynomial
open scoped LaurentPolynomial

namespace OrlikSolomon.Geometric.Examples

open Geometric.DeRham

universe u
variable {k : Type u} [CommRing k]

private def specSectionsEquiv (A : CommAlgCat.{u} k) :
    sectionAlgebra k (spec A) ⊤ ≃ₐ[k] A :=
  (globalSectionsAlgEquiv (spec A)).symm.trans (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A))

private lemma specSectionsEquiv_apply (A : CommAlgCat.{u} k)
    (a : sectionAlgebra k (spec A) ⊤) :
    specSectionsEquiv A a = (Scheme.ΓSpecIso (.of A)).hom a := rfl

private def openSectionMap {X : Over (Spec (.of k))} {A : CommAlgCat.{u} k}
    (f : spec A ⟶ X) (U : X.left.Opens) (h : ⊤ ≤ f.left ⁻¹ᵁ U) :
    sectionAlgebra k X U →ₐ[k] A :=
  (specSectionsEquiv A).toAlgHom.comp
    ((sectionRestriction k (spec A) (homOfLE h)).comp (sectionPullback f U))

private lemma openSectionMap_apply {X : Over (Spec (.of k))} {A : CommAlgCat.{u} k}
    (f : spec A ⟶ X) (U : X.left.Opens) (h : ⊤ ≤ f.left ⁻¹ᵁ U)
    (a : sectionAlgebra k X U) :
    openSectionMap f U h a = (Scheme.ΓSpecIso (.of A)).hom (f.left.appLE U ⊤ h a) := rfl

private lemma openSectionMap_bijective {X : Over (Spec (.of k))} {A : CommAlgCat.{u} k}
    (f : spec A ⟶ X) [IsOpenImmersion f.left] (U : X.left.Opens)
    (h : ⊤ ≤ f.left ⁻¹ᵁ U) (hU : U ≤ f.left.opensRange) :
    Function.Bijective (openSectionMap f U h) := by
  have : IsIso (f.left.app U) := f.left.isIso_app U hU
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h (top_le_iff.mp h).symm
  exact (specSectionsEquiv A).bijective.comp
    ((ConcreteCategory.bijective_of_isIso ((spec A).left.presheaf.map (homOfLE h).op)).comp
      (ConcreteCategory.bijective_of_isIso (f.left.app U)))

private def openSectionsEquiv {X : Over (Spec (.of k))} {A : CommAlgCat.{u} k}
    (f : spec A ⟶ X) [IsOpenImmersion f.left] (U : X.left.Opens)
    (h : ⊤ ≤ f.left ⁻¹ᵁ U) (hU : U ≤ f.left.opensRange) :
    sectionAlgebra k X U ≃ₐ[k] A :=
  AlgEquiv.ofBijective (openSectionMap f U h) (openSectionMap_bijective f U h hU)

private lemma openSectionMap_restrict
    {X : Over (Spec (.of k))} {A B : CommAlgCat.{u} k}
    (f : spec A ⟶ X) (g : spec B ⟶ X) (φ : A ⟶ B)
    (U V : X.left.Opens) (hVU : V ≤ U)
    (ha : ⊤ ≤ f.left ⁻¹ᵁ U) (hb : ⊤ ≤ g.left ⁻¹ᵁ V)
    (hfg : specMap φ ≫ f = g) (a : sectionAlgebra k X U) :
    openSectionMap g V hb (sectionRestriction k X (homOfLE hVU) a) =
      φ.hom (openSectionMap f U ha a) := by
  subst g
  have hc : f.left.appLE U ⊤ ha ≫ (specMap φ).left.appTop =
      X.left.presheaf.map (homOfLE hVU).op ≫ (specMap φ ≫ f).left.appLE V ⊤ hb := by
    have hq : (⊤ : (spec B).left.Opens) ≤ (specMap φ).left ⁻¹ᵁ ⊤ := by
      intro x _
      trivial
    change f.left.appLE U ⊤ ha ≫ (specMap φ).left.appLE ⊤ ⊤ hq = _
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.map_appLE]
    rfl
  -- Evaluate the structural square before using the affine spectrum comparison.
  have hraw := ConcreteCategory.congr_hom hc a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hraw
  rw [openSectionMap_apply, openSectionMap_apply]
  change (Scheme.ΓSpecIso (.of B)).hom
    ((specMap φ ≫ f).left.appLE V ⊤ hb (X.left.presheaf.map (homOfLE hVU).op a)) = _
  rw [← hraw]
  have hmap : (specMap φ).left.appTop
      ((Scheme.ΓSpecIso (.of A)).inv ((Scheme.ΓSpecIso (.of A)).hom
        (f.left.appLE U ⊤ ha a))) =
      (Scheme.ΓSpecIso (.of B)).inv
        (φ.hom ((Scheme.ΓSpecIso (.of A)).hom (f.left.appLE U ⊤ ha a))) :=
    specMap_left_appTop_ΓSpecIso_inv _ _
  rw [Iso.hom_inv_id_apply] at hmap
  exact (congrArg (Scheme.ΓSpecIso (.of B)).hom hmap).trans (Iso.inv_hom_id_apply _ _)

section ProjectiveLine

variable (k : Type u) [Field k]

/-- The chart overlap is contained in either standard chart. -/
theorem projectiveLineOverlap_le_chart (i : Fin 2) :
    projectiveLineOverlap k ≤ projectiveLineChart k i := by
  rw [projectiveLineOverlap_eq_inf]
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

private lemma chart_top_preimage (i : Fin 2) :
    (⊤ : (spec (CommAlgCat.of k k[X])).left.Opens) ≤
      (projectiveLineChartMap k i).left ⁻¹ᵁ projectiveLineChart k i := by
  rw [← projectiveLineChartMap_opensRange, Scheme.Hom.preimage_opensRange]

private lemma overlap_top_preimage :
    (⊤ : (spec (CommAlgCat.of k (LaurentPolynomial k))).left.Opens) ≤
      (projectiveLineOverlapMap k).left ⁻¹ᵁ projectiveLineOverlap k := by
  rw [← projectiveLineOverlapMap_opensRange, Scheme.Hom.preimage_opensRange]

/-- Regular functions on the `i`th standard open, in its affine-line coordinate. -/
@[no_expose]
def projectiveLineChartSectionsEquiv (i : Fin 2) :
    sectionAlgebra k (projectiveLine k) (projectiveLineChart k i) ≃ₐ[k] k[X] :=
  openSectionsEquiv (projectiveLineChartMap k i) _ (chart_top_preimage k i)
    (projectiveLineChartMap_opensRange k i).ge

/-- Regular functions on the actual chart intersection, in its Laurent coordinate. -/
@[no_expose]
def projectiveLineOverlapSectionsEquiv :
    sectionAlgebra k (projectiveLine k) (projectiveLineOverlap k) ≃ₐ[k] LaurentPolynomial k :=
  openSectionsEquiv (projectiveLineOverlapMap k) _ (overlap_top_preimage k)
    (projectiveLineOverlapMap_opensRange k).ge

/-- The first chart restriction, as a map of section algebras, is the Laurent inclusion. -/
theorem projectiveLineChartSectionsEquiv_restrict_zero :
    (projectiveLineOverlapSectionsEquiv k).toAlgHom.comp
        (sectionRestriction k (projectiveLine k)
          (homOfLE (projectiveLineOverlap_le_chart k 0))) =
      (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k).comp
        (projectiveLineChartSectionsEquiv k 0).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact openSectionMap_restrict (projectiveLineChartMap k 0) (projectiveLineOverlapMap k)
    (CommAlgCat.ofHom Polynomial.toLaurentAlg) _ _ (projectiveLineOverlap_le_chart k 0)
    (chart_top_preimage k 0) (overlap_top_preimage k) (projectiveLineChartMap_zero_overlap k) a

/-- The second chart restriction, as a map of section algebras, inverts the Laurent coordinate. -/
theorem projectiveLineChartSectionsEquiv_restrict_one :
    (projectiveLineOverlapSectionsEquiv k).toAlgHom.comp
        (sectionRestriction k (projectiveLine k)
          (homOfLE (projectiveLineOverlap_le_chart k 1))) =
      (LaurentPolynomial.invert.toAlgHom.comp
        (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)).comp
          (projectiveLineChartSectionsEquiv k 1).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact openSectionMap_restrict (projectiveLineChartMap k 1) (projectiveLineOverlapMap k)
    (CommAlgCat.ofHom (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg))
    _ _ (projectiveLineOverlap_le_chart k 1) (chart_top_preimage k 1) (overlap_top_preimage k)
    (projectiveLineChartMap_one_overlap k) a

end ProjectiveLine

end OrlikSolomon.Geometric.Examples
