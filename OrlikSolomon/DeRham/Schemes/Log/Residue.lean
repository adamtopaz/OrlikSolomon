/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Affine
public import OrlikSolomon.DeRham.Schemes.Log.Basic
public import OrlikSolomon.DeRham.Log
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Residue and exactness of logarithmic forms on schemes

Regular forms inject into complement forms and hence into the logarithmic image sheaves.
The affine-local argument works over every commutative base ring, with no hypothesis on
characteristic, nontriviality, points, or the ambient domain beyond `SmoothDomain`.

## Main results

* `formsSheafPullback_injective_affineOpen`: injectivity on each affine neighborhood.
* `formsSheafPullback_mono`: the regular-form map to the complement is a monomorphism.
* `regularToLogSheaf_mono`: the left inclusion into logarithmic forms is a monomorphism.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k] {D : SmoothDomain k}

/-- Regular forms of each degree inject into the forms on the principal complement. -/
lemma algebraicRegularForms_injective (Q : OrlikSolomon.DivisorPair k) (n : ℕ) :
    Function.Injective (Forms.mapPower (SmoothAlg.algHom Q.j) n) := by
  intro x y h
  apply Subtype.ext
  exact Q.isSmoothPrincipalPair.map_injective Q.compl
    (congrArg Subtype.val h)

/-- Sections on an open and global sections of its open subscheme have the same base action. -/
def openSectionAlgebraEquiv (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    sectionAlgebra k X U ≃ₐ[k] globalSections (Over.mk (U.ι ≫ X.hom)) :=
  { U.topIso.symm.commRingCatIsoToRingEquiv with
    commutes' r := by
      change U.topIso.inv ((X.left.presheaf.map U.leTop.op)
        (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) =
          (U.ι ≫ X.hom).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)
      rw [Scheme.Hom.comp_appTop]
      have h : X.left.presheaf.map U.leTop.op ≫ U.topIso.inv = U.ι.appTop := by
        change X.left.presheaf.map U.leTop.op ≫
          X.left.presheaf.map (eqToHom U.ι_image_top).op = _
        rw [← Functor.map_comp]
        rfl
      exact ConcreteCategory.congr_hom h _ }

variable {X Y : Over (Spec (CommRingCat.of k))}

-- The restriction appTop presents its codomain using a preimage of the top open.
set_option backward.isDefEq.respectTransparency false in
/-- The section-ring comparison intertwines pullback and the restricted scheme morphism. -/
lemma openSectionAlgebraEquiv_comp (g : X ⟶ Y) (U : Y.left.Opens) :
    (openSectionAlgebraEquiv X (g.left ⁻¹ᵁ U)).toAlgHom.comp (sectionPullback g U) =
      (globalSectionsMap (Over.homMk (g.left ∣_ U) (by
        dsimp
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))).hom.comp
          (openSectionAlgebraEquiv Y U).toAlgHom := by
  have h : U.topIso.inv ≫ (g.left ∣_ U).appTop =
      g.left.app U ≫ (g.left ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    change U.topIso.inv ≫ (g.left.resLE U (g.left ⁻¹ᵁ U) le_rfl).app ⊤ = _
    rw [Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
    congr 1
    simp [Scheme.Hom.appLE]
  ext a
  exact (ConcreteCategory.congr_hom h a).symm

/-- The algebraic pullback of degreewise forms is injective on an affine neighborhood. -/
lemma affineNeighborhoodForms_injective (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Injective (Forms.mapPower (sectionPullback P.j.hom V.1) n) := by
  let Q := affineNeighborhoodAlgebraicPair P V
  let eA := openSectionAlgebraEquiv P.ambient.obj V.1
  let eB := openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1)
  have hj : eB.toAlgHom.comp (sectionPullback P.j.hom V.1) =
      (SmoothAlg.algHom Q.j).comp eA.toAlgHom :=
    openSectionAlgebraEquiv_comp P.j.hom V.1
  intro x y hxy
  have he : Forms.mapPower eA.toAlgHom n x = Forms.mapPower eA.toAlgHom n y := by
    apply algebraicRegularForms_injective Q n
    change (Forms.mapPower (SmoothAlg.algHom Q.j) n ∘ₗ Forms.mapPower eA.toAlgHom n) x =
      (Forms.mapPower (SmoothAlg.algHom Q.j) n ∘ₗ Forms.mapPower eA.toAlgHom n) y
    rw [← Forms.mapPower_comp, ← hj, Forms.mapPower_comp]
    exact congrArg (Forms.mapPower eB.toAlgHom n) hxy
  exact Subtype.ext ((Forms.mapEquiv eA).injective (congrArg Subtype.val he))

/-- Regular sheaf forms inject into complement forms on every affine open of the ambient. -/
lemma formsSheafPullback_injective_affineOpen (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Injective ((formsSheafPullback P.j.hom n).hom.app (op V.1)) := by
  have hV : IsAffineOpen (P.j.hom.left ⁻¹ᵁ V.1) := by
    exact inferInstanceAs (IsAffine (affineNeighborhoodPair P V).compl.obj.left)
  intro x y hxy
  obtain ⟨x, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective x
  obtain ⟨y, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective y
  apply (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).congr_arg
  apply affineNeighborhoodForms_injective P V n
  apply (affineOpenFormsComparison P.compl.obj _ hV n).injective
  change (formsSheafPullback P.j.hom n).hom.app (op V.1)
      ((formsSheafUnit k P.ambient.obj n).app (op V.1) x) =
    (formsSheafPullback P.j.hom n).hom.app (op V.1)
      ((formsSheafUnit k P.ambient.obj n).app (op V.1) y) at hxy
  exact (formsSheafPullback_unit_apply P.j.hom n (op V.1) x).symm.trans
    (hxy.trans (formsSheafPullback_unit_apply P.j.hom n (op V.1) y))

/-- Restricting regular forms to the principal complement is a monomorphism of sheaves. -/
lemma formsSheafPullback_mono (P : DivisorPair D) (n : ℕ) :
    Mono (formsSheafPullback P.j.hom n) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono _).2
  intro x
  apply ConcreteCategory.mono_of_injective
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    P.ambient.obj.left.isBasis_affineOpens
  intro U hU
  exact formsSheafPullback_injective_affineOpen P ⟨U, hU⟩ n

/-- The regular-form inclusion into logarithmic forms is a monomorphism of sheaves. -/
instance regularToLogSheaf_mono (P : DivisorPair D) (n : ℕ) :
    Mono (regularToLogSheaf P n) := by
  have := formsSheafPullback_mono P n
  exact mono_of_mono_fac (regularToLogSheaf_comp_logToOpenSheaf P n)

/-- Pullback of algebraic forms to the smooth divisor is surjective on every affine neighborhood. -/
lemma affineNeighborhoodClosedForms_surjective (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Surjective (Forms.mapPower (sectionPullback P.i.hom V.1) n) := by
  let Q := affineNeighborhoodAlgebraicPair P V
  let eA := openSectionAlgebraEquiv P.ambient.obj V.1
  let eB := openSectionAlgebraEquiv P.closed.obj (P.i.hom.left ⁻¹ᵁ V.1)
  have hi : eB.toAlgHom.comp (sectionPullback P.i.hom V.1) =
      (SmoothAlg.algHom Q.i).comp eA.toAlgHom :=
    openSectionAlgebraEquiv_comp P.i.hom V.1
  intro x
  obtain ⟨z, hz⟩ := Forms.mapPower_surjective Q.surjective_i n
    (Forms.mapPower eB.toAlgHom n x)
  refine ⟨Forms.mapPower eA.symm.toAlgHom n z, ?_⟩
  apply Subtype.ext
  apply (Forms.mapEquiv eB).injective
  change Forms.map eB.toAlgHom
      (Forms.map (sectionPullback P.i.hom V.1)
        (Forms.map eA.symm.toAlgHom z.val)) = Forms.map eB.toAlgHom x.val
  rw [Forms.map_map, hi, ← Forms.map_map]
  rw [show Forms.map eA.toAlgHom (Forms.map eA.symm.toAlgHom z.val) = z.val from
    (Forms.mapEquiv eA).apply_symm_apply z.val]
  exact congrArg Subtype.val hz

/-- Forms on the divisor lift to regular ambient forms on every affine open of the ambient. -/
lemma formsSheafPullback_surjective_affineOpen (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Surjective ((formsSheafPullback P.i.hom n).hom.app (op V.1)) := by
  have hV : IsAffineOpen (P.i.hom.left ⁻¹ᵁ V.1) := by
    exact inferInstanceAs (IsAffine (affineNeighborhoodPair P V).closed.obj.left)
  intro x
  obtain ⟨x, rfl⟩ := (affineOpenFormsComparison P.closed.obj _ hV n).surjective x
  obtain ⟨y, hy⟩ := affineNeighborhoodClosedForms_surjective P V n x
  refine ⟨affineOpenFormsComparison P.ambient.obj V.1 V.2 n y, ?_⟩
  exact (formsSheafPullback_unit_apply P.i.hom n (op V.1) y).trans
    (congrArg ((formsSheafUnit k P.closed.obj n).app
      (op (P.i.hom.left ⁻¹ᵁ V.1))) hy)

/-- Restricting forms to the smooth principal divisor is an epimorphism of sheaves.
This is a local assertion, with no global-section exactness claim on a non-affine ambient. -/
lemma formsSheafPullback_epi (P : DivisorPair D) (n : ℕ) :
    Epi (formsSheafPullback P.i.hom n) := by
  constructor
  intro F g h hgh
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _
    (show TopologicalSpace.Opens.IsBasis
        (Set.range (fun V : P.ambient.obj.left.affineOpens => V.1)) by
      simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
        P.ambient.obj.left.isBasis_affineOpens)
  intro U
  ext x
  obtain ⟨y, rfl⟩ := formsSheafPullback_surjective_affineOpen P U n x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) hgh) (op U.1)) y


end OrlikSolomon.Geometric.DeRham
