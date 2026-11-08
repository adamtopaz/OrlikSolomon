/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Affine
public import OrlikSolomon.DeRham.Schemes.Log.RestrictionImage
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
/-!
# Logarithmic complexes on affine neighborhoods

Restriction to an open subscheme preserves monomorphisms and epimorphisms of module
sheaves. Relative forms and the ordinary direct image from the complement commute
with the actual open-restriction square. Their regular, logarithmic-product, and
differential maps therefore identify the restricted logarithmic image complex with
the logarithmic complex of `affineNeighborhoodPair`.

After evaluating at the top open and applying the affine comparison, this gives
`affineNeighborhoodLogComplexIso` and `affineNeighborhoodOpenComplexIso`. Their
inclusions commute by `affineNeighborhoodLogComplexIso_toOpen`, providing the affine
basis comparison without a claim that global sections preserve arbitrary images.

Blueprint: the affine-local step of `thm:geo-log-sheaves`.
-/

@[expose] public section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
noncomputable section
namespace OrlikSolomon.Geometric.DeRham
open OrlikSolomon.DeRham
variable {k : Type u} [CommRing k] {D : SmoothDomain k}
/-- Mathlib’s open restriction functor, with its codomain displayed as sheaves on the open scheme.
-/
def schemeSheafRestrict (X : Scheme.{u}) (U : X.Opens) :
    TopCat.Sheaf (ModuleCat.{u} k) X ⥤ TopCat.Sheaf (ModuleCat.{u} k) U.toScheme :=
  U.sheafRestrict

/-- Open restriction is additive on module sheaves. -/
instance schemeSheafRestrict_additive (X : Scheme.{u}) (U : X.Opens) :
    (schemeSheafRestrict (k := k) X U).Additive where
  map_add := by intros; rfl

/-- Open restriction preserves epimorphisms, by preservation of local surjectivity. -/
instance schemeSheafRestrict_preservesEpis (X : Scheme.{u}) (U : X.Opens) :
    (schemeSheafRestrict (k := k) X U).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    have : U.ι.opensFunctor.IsCocontinuous
        (_root_.Opens.grothendieckTopology U.toScheme)
        (_root_.Opens.grothendieckTopology X) :=
      (U.ι.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving _ _).2
        (coverPreserving_opens_map _)
    have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} k)
      φ).2 hφ
    have : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X)
        φ.hom := inferInstance
    have := Presheaf.isLocallySurjective_whisker
      (_root_.Opens.grothendieckTopology U.toScheme)
      (_root_.Opens.grothendieckTopology X) U.ι.opensFunctor φ.hom
    have : Sheaf.IsLocallySurjective ((schemeSheafRestrict (k := k) X U).map φ) :=
      inferInstanceAs (Presheaf.IsLocallySurjective
        (_root_.Opens.grothendieckTopology U.toScheme)
        (Functor.whiskerLeft U.ι.opensFunctor.op φ.hom))
    exact Sheaf.epi_of_isLocallySurjective _


/-- Open restriction preserves monomorphisms. -/
instance schemeSheafRestrict_preservesMonos (X : Scheme.{u}) (U : X.Opens) :
    (schemeSheafRestrict (k := k) X U).PreservesMonomorphisms :=
  inferInstanceAs ((U.sheafRestrict (C := ModuleCat.{u} k)).PreservesMonomorphisms)

variable (P : DivisorPair D) (V : P.ambient.obj.left.affineOpens)

/-- Restriction to the actual ambient scheme of an affine-neighborhood pair. -/
def affineNeighborhoodSheafRestrict :
    TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left ⥤
      TopCat.Sheaf (ModuleCat.{u} k) (affineNeighborhoodPair P V).ambient.obj.left :=
  schemeSheafRestrict (k := k) P.ambient.obj.left V.1

/-- Affine-neighborhood restriction is additive. -/
instance affineNeighborhoodSheafRestrict_additive : (affineNeighborhoodSheafRestrict P V).Additive
  :=
  schemeSheafRestrict_additive P.ambient.obj.left V.1

/-- Affine-neighborhood restriction preserves monomorphisms. -/
instance affineNeighborhoodSheafRestrict_monos :
    (affineNeighborhoodSheafRestrict P V).PreservesMonomorphisms :=
  schemeSheafRestrict_preservesMonos P.ambient.obj.left V.1

/-- Affine-neighborhood restriction preserves epimorphisms. -/
instance affineNeighborhoodSheafRestrict_epis :
    (affineNeighborhoodSheafRestrict P V).PreservesEpimorphisms :=
  schemeSheafRestrict_preservesEpis P.ambient.obj.left V.1

private def restrictPushforwardOpensIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    U.ι.opensFunctor.op ⋙ (TopologicalSpace.Opens.map f.base).op ≅
      (TopologicalSpace.Opens.map (f ∣_ U).base).op ⋙ (f ⁻¹ᵁ U).ι.opensFunctor.op :=
  NatIso.ofComponents (fun W => (eqToIso (image_morphismRestrict_preimage f U W.unop)).op)
    (by intros; apply Subsingleton.elim)

private def restrictPushforwardIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    TopCat.Sheaf.pushforward (ModuleCat.{u} k) f.base ⋙ schemeSheafRestrict (k := k) X U ≅
      schemeSheafRestrict (k := k) Y (f ⁻¹ᵁ U) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ∣_ U).base :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (restrictPushforwardOpensIso f U) F.obj)) (by
      intro F G m
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext W
      exact (m.hom.naturality ((restrictPushforwardOpensIso f U).hom.app W)).symm)

private abbrev openOver (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ X.hom)

private def schemeFormsRestrictionIso (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).obj (formsSheaf k X n) ≅
      formsSheaf k (openOver X U) n := formsSheafRestrictionIso X U n

private lemma schemeFormsRestrictionIso_unit (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (n : ℕ) (W : U.toScheme.Opens)
    (a : (formsPresheaf k X n).obj (op (U.ι ''ᵁ W))) :
    (schemeFormsRestrictionIso X U n).hom.hom.app (op W)
      ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W)) a) =
    (formsSheafUnit k (openOver X U) n).app (op W)
      (Forms.mapPower (sectionAlgebraRestrictEquiv X U W).toAlgHom n a) :=
  formsSheafRestrictionIso_unit X U n W a

private abbrev restrictedOverMap {X Y : Over (Spec (CommRingCat.of k))} (g : Y ⟶ X)
    (U : X.left.Opens) : openOver Y (g.left ⁻¹ᵁ U) ⟶ openOver X U :=
  Over.homMk (g.left ∣_ U) (by
    dsimp [openOver]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])

private lemma restrictedForms_hom_ext (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (n : ℕ) {F : TopCat.Sheaf (ModuleCat.{u} k) U.toScheme}
    (φ ψ : (schemeSheafRestrict (k := k) X.left U).obj (formsSheaf k X n) ⟶ F)
    (h : ∀ (W : U.toScheme.affineOpens)
      (a : (formsPresheaf k X n).obj (op (U.ι ''ᵁ W.1))),
      φ.hom.app (op W.1) ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a) =
        ψ.hom.app (op W.1) ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a)) : φ = ψ := by
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (B := fun W : U.toScheme.affineOpens => W.1)
    (by simpa only [Subtype.range_coe] using U.toScheme.isBasis_affineOpens)
  intro W
  have := formsSheafUnit_isIso_of_isAffineOpen X (U.ι ''ᵁ W.1)
    (W.2.image_of_isOpenImmersion U.ι) n
  apply (cancel_epi ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)))).1
  ext a
  exact h W a

private lemma formsRestriction_d (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).map (formsSheafD k X n) ≫
        (schemeFormsRestrictionIso X U (n + 1)).hom =
      (schemeFormsRestrictionIso X U n).hom ≫ formsSheafD k (openOver X U) n := by
  apply restrictedForms_hom_ext X U n
  intro W a
  change (schemeFormsRestrictionIso X U (n + 1)).hom.hom.app (op W.1)
      ((formsSheafD k X n).hom.app (op (U.ι ''ᵁ W.1))
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a)) =
    (formsSheafD k (openOver X U) n).hom.app (op W.1)
      ((schemeFormsRestrictionIso X U n).hom.hom.app (op W.1)
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a))
  rw [formsSheafD_unit, schemeFormsRestrictionIso_unit,
    schemeFormsRestrictionIso_unit, formsSheafD_unit k (openOver X U) n (op W.1)
      (Forms.mapPower (sectionAlgebraRestrictEquiv X U W.1).toAlgHom n a)]
  congr 1
  exact Forms.mapPower_powerD (sectionAlgebraRestrictEquiv X U W.1).toAlgHom n a

private lemma restrictPushforwardIso_unit {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) (W : U.toScheme.Opens)
    (a : (formsPresheaf k Y n).obj (op (g.left ⁻¹ᵁ (U.ι ''ᵁ W)))) :
    ((restrictPushforwardIso (k := k) g.left U).hom.app (formsSheaf k Y n)).hom.app (op W)
      ((formsSheafUnit k Y n).app (op (g.left ⁻¹ᵁ (U.ι ''ᵁ W))) a) =
    (formsSheafUnit k Y n).app (op ((g.left ⁻¹ᵁ U).ι ''ᵁ ((g.left ∣_ U) ⁻¹ᵁ W)))
      (Forms.mapPower (sectionRestriction k Y
        (eqToHom (image_morphismRestrict_preimage g.left U W))) n a) := by
  exact (ConcreteCategory.congr_hom
    ((formsSheafUnit k Y n).naturality
      (eqToHom (image_morphismRestrict_preimage g.left U W)).op) a).symm

private lemma sectionRestriction_pullback_square {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (W : U.toScheme.Opens) :
    (sectionPullback (restrictedOverMap (k := k) g U) W).comp
        (sectionAlgebraRestrictEquiv X U W).toAlgHom =
      ((sectionAlgebraRestrictEquiv Y (g.left ⁻¹ᵁ U) ((g.left ∣_ U) ⁻¹ᵁ W)).toAlgHom).comp
        ((sectionRestriction k Y (eqToHom (image_morphismRestrict_preimage g.left U W))).comp
          (sectionPullback g (U.ι ''ᵁ W))) := by
  apply AlgHom.ext
  intro a
  exact ConcreteCategory.congr_hom (morphismRestrict_app g.left U W) a

private def formsPushforwardRestrictionIso {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).obj
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).obj (formsSheaf k Y n)) ≅
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base).obj
      (formsSheaf k (openOver Y (g.left ⁻¹ᵁ U)) n) :=
  (restrictPushforwardIso (k := k) g.left U).app (formsSheaf k Y n) ≪≫
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base).mapIso
      (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) n)

private def restrictedFormsPullback {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) :
    formsSheaf k (openOver X U) n ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base).obj
        (formsSheaf k (openOver Y (g.left ⁻¹ᵁ U)) n) :=
  formsSheafPullback (restrictedOverMap (k := k) g U) n

private lemma formsPushforwardRestrictionIso_unit {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) (W : U.toScheme.Opens)
    (a : (formsPresheaf k Y n).obj (op (g.left ⁻¹ᵁ (U.ι ''ᵁ W)))) :
    (formsPushforwardRestrictionIso (k := k) g U n).hom.hom.app (op W)
      ((formsSheafUnit k Y n).app (op (g.left ⁻¹ᵁ (U.ι ''ᵁ W))) a) =
      (formsSheafUnit k (openOver Y (g.left ⁻¹ᵁ U)) n).app
        (op ((g.left ∣_ U) ⁻¹ᵁ W))
        (Forms.mapPower (sectionAlgebraRestrictEquiv Y (g.left ⁻¹ᵁ U)
          ((g.left ∣_ U) ⁻¹ᵁ W)).toAlgHom n
          (Forms.mapPower (sectionRestriction k Y
            (eqToHom (image_morphismRestrict_preimage g.left U W))) n a)) := by
  exact (congrArg (fun z =>
    (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) n).hom.hom.app
      (op ((g.left ∣_ U) ⁻¹ᵁ W)) z) (restrictPushforwardIso_unit g U n W a)).trans
        (schemeFormsRestrictionIso_unit Y (g.left ⁻¹ᵁ U) n ((g.left ∣_ U) ⁻¹ᵁ W)
          (Forms.mapPower (sectionRestriction k Y
            (eqToHom (image_morphismRestrict_preimage g.left U W))) n a))

private lemma formsRestriction_pullback_power {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) (W : U.toScheme.Opens)
    (a : (formsPresheaf k X n).obj (op (U.ι ''ᵁ W))) :
    Forms.mapPower (sectionPullback (restrictedOverMap (k := k) g U) W) n
        (Forms.mapPower (sectionAlgebraRestrictEquiv X U W).toAlgHom n a) =
      Forms.mapPower (sectionAlgebraRestrictEquiv Y (g.left ⁻¹ᵁ U)
          ((g.left ∣_ U) ⁻¹ᵁ W)).toAlgHom n
        (Forms.mapPower (sectionRestriction k Y
          (eqToHom (image_morphismRestrict_preimage g.left U W))) n
          (Forms.mapPower (sectionPullback g (U.ι ''ᵁ W)) n a)) := by
  let α := (sectionAlgebraRestrictEquiv X U W).toAlgHom
  let β := sectionPullback (restrictedOverMap (k := k) g U) W
  let γ := (sectionAlgebraRestrictEquiv Y (g.left ⁻¹ᵁ U) ((g.left ∣_ U) ⁻¹ᵁ W)).toAlgHom
  let δ := sectionRestriction k Y (eqToHom (image_morphismRestrict_preimage g.left U W))
  let ε := sectionPullback g (U.ι ''ᵁ W)
  exact (LinearMap.congr_fun (Forms.mapPower_comp β α n) a).symm.trans
    ((congrArg (fun q => Forms.mapPower q n a) (sectionRestriction_pullback_square g U W)).trans
      ((LinearMap.congr_fun (Forms.mapPower_comp γ (δ.comp ε) n) a).trans
        (congrArg (Forms.mapPower γ n)
          (LinearMap.congr_fun (Forms.mapPower_comp δ ε n) a))))

private lemma formsRestriction_pullback {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) :
    (schemeFormsRestrictionIso X U n).hom ≫
        restrictedFormsPullback (k := k) g U n =
      (schemeSheafRestrict (k := k) X.left U).map (formsSheafPullback g n) ≫
        (formsPushforwardRestrictionIso (k := k) g U n).hom := by
  apply restrictedForms_hom_ext X U n
  intro W a
  let a' := Forms.mapPower (sectionAlgebraRestrictEquiv X U W.1).toAlgHom n a
  let b := Forms.mapPower (sectionPullback g (U.ι ''ᵁ W.1)) n a
  have hL := (congrArg (fun z =>
    (formsSheafPullback (restrictedOverMap (k := k) g U) n).hom.app (op W.1) z)
      (schemeFormsRestrictionIso_unit X U n W.1 a)).trans
        (formsSheafPullback_unit_apply (restrictedOverMap (k := k) g U) n (op W.1) a')
  have hR := (congrArg (fun z =>
    (formsPushforwardRestrictionIso (k := k) g U n).hom.hom.app (op W.1) z)
      (formsSheafPullback_unit_apply g n (op (U.ι ''ᵁ W.1)) a)).trans
        (formsPushforwardRestrictionIso_unit (k := k) g U n W.1 b)
  have hAlg := formsRestriction_pullback_power (k := k) g U n W.1 a
  exact hL.trans ((congrArg (fun z =>
    (formsSheafUnit k (openOver Y (g.left ⁻¹ᵁ U)) n).app
      (op ((g.left ∣_ U) ⁻¹ᵁ W.1)) z) hAlg).trans hR.symm)

private abbrev openInclusion (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    openOver X U ⟶ X := Over.homMk U.ι rfl

private lemma sectionRestriction_unit (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (v : (sectionAlgebra k X ⊤)ˣ) (W : U.toScheme.Opens) :
    Units.map (sectionAlgebraRestrictEquiv X U W).toAlgHom.toMonoidHom
        (Units.map (sectionRestriction k X (U.ι ''ᵁ W).leTop).toMonoidHom v) =
      Units.map (sectionRestriction k (openOver X U) W.leTop).toMonoidHom
        (Units.map (sectionPullbackTop (openInclusion X U)).toMonoidHom v) := by
  apply Units.ext
  change X.left.presheaf.map (U.ι ''ᵁ W).leTop.op (v : sectionAlgebra k X ⊤) =
    U.toScheme.presheaf.map W.leTop.op (U.ι.appTop (v : sectionAlgebra k X ⊤))
  have h : X.left.presheaf.map (U.ι ''ᵁ W).leTop.op =
      U.ι.appTop ≫ U.toScheme.presheaf.map W.leTop.op := by
    change X.left.presheaf.map (U.ι ''ᵁ W).leTop.op =
      X.left.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op ≫
        X.left.presheaf.map (U.ι.opensFunctor.map W.leTop).op
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h (v : sectionAlgebra k X ⊤)

private def dlogWedgePower {A : Type u} [CommRing A] [Algebra k A]
    (v : Aˣ) (n : ℕ) (a : ⋀[A]^n Ω[A⁄k]) : ⋀[A]^(n + 1) Ω[A⁄k] :=
  ⟨dlog k v * a.val, by simpa only [Nat.add_comm 1 n] using
    SetLike.mul_mem_graded (dlog_mem_exteriorPower_one k v) a.property⟩

private lemma formsRestriction_theta (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (v : (sectionAlgebra k X ⊤)ˣ) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).map (thetaWedgeSheaf X v n) ≫
        (schemeFormsRestrictionIso X U (n + 1)).hom =
      (schemeFormsRestrictionIso X U n).hom ≫
        thetaWedgeSheaf (openOver X U)
          (Units.map (sectionPullbackTop (openInclusion X U)).toMonoidHom v) n := by
  apply restrictedForms_hom_ext X U n
  intro W a
  change (schemeFormsRestrictionIso X U (n + 1)).hom.hom.app (op W.1)
      ((thetaWedgeSheaf X v n).hom.app (op (U.ι ''ᵁ W.1))
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a)) =
    (thetaWedgeSheaf (openOver X U)
        (Units.map (sectionPullbackTop (openInclusion X U)).toMonoidHom v) n).hom.app (op W.1)
      ((schemeFormsRestrictionIso X U n).hom.hom.app (op W.1)
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a))
  let v₁ := Units.map (sectionRestriction k X (U.ι ''ᵁ W.1).leTop).toMonoidHom v
  let w := Units.map (sectionPullbackTop (openInclusion X U)).toMonoidHom v
  let v₂ := Units.map (sectionRestriction k (openOver X U) W.1.leTop).toMonoidHom w
  let a' := Forms.mapPower (sectionAlgebraRestrictEquiv X U W.1).toAlgHom n a
  let b := dlogWedgePower v₁ n a
  let b' := dlogWedgePower v₂ n a'
  have hL : (schemeFormsRestrictionIso X U (n + 1)).hom.hom.app (op W.1)
      ((thetaWedgeSheaf X v n).hom.app (op (U.ι ''ᵁ W.1))
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a)) =
      (formsSheafUnit k (openOver X U) (n + 1)).app (op W.1)
        (Forms.mapPower (sectionAlgebraRestrictEquiv X U W.1).toAlgHom (n + 1) b) :=
    (congrArg (fun z => (schemeFormsRestrictionIso X U (n + 1)).hom.hom.app (op W.1) z)
      (thetaWedgeSheaf_unit X v n (op (U.ι ''ᵁ W.1)) a)).trans
        (schemeFormsRestrictionIso_unit X U (n + 1) W.1 b)
  have hR : (thetaWedgeSheaf (openOver X U) w n).hom.app (op W.1)
      ((schemeFormsRestrictionIso X U n).hom.hom.app (op W.1)
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ W.1)) a)) =
      (formsSheafUnit k (openOver X U) (n + 1)).app (op W.1) b' :=
    (congrArg (fun z => (thetaWedgeSheaf (openOver X U) w n).hom.app (op W.1) z)
      (schemeFormsRestrictionIso_unit X U n W.1 a)).trans
        (thetaWedgeSheaf_unit (openOver X U) w n (op W.1) a')
  have hb : Forms.mapPower (sectionAlgebraRestrictEquiv X U W.1).toAlgHom (n + 1) b = b' := by
    apply Subtype.ext
    change Forms.map (sectionAlgebraRestrictEquiv X U W.1).toAlgHom (dlog k v₁ * a.val) = _
    rw [map_mul, Forms.map_dlog]
    exact congrArg (fun v => dlog k v * Forms.map (sectionAlgebraRestrictEquiv X U W.1).toAlgHom
      a.val)
      (sectionRestriction_unit X U v W.1)
  exact hL.trans ((congrArg (fun z =>
    (formsSheafUnit k (openOver X U) (n + 1)).app (op W.1) z) hb).trans hR.symm)

private lemma formsPushforwardRestriction_d {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (formsSheafD k Y n)) ≫
        (formsPushforwardRestrictionIso (k := k) g U (n + 1)).hom =
      (formsPushforwardRestrictionIso (k := k) g U n).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base).map
          (formsSheafD k (openOver Y (g.left ⁻¹ᵁ U)) n) := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base
  let e := (restrictPushforwardIso (k := k) g.left U).hom
  change (schemeSheafRestrict (k := k) X.left U).map
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (formsSheafD k Y n)) ≫
      (e.app (formsSheaf k Y (n + 1)) ≫ F.map (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) (n +
        1)).hom) =
    (e.app (formsSheaf k Y n) ≫ F.map (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) n).hom) ≫
      F.map (formsSheafD k (openOver Y (g.left ⁻¹ᵁ U)) n)
  have he : (schemeSheafRestrict (k := k) X.left U).map
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (formsSheafD k Y n)) ≫
      e.app (formsSheaf k Y (n + 1)) =
    e.app (formsSheaf k Y n) ≫
      F.map ((schemeSheafRestrict (k := k) Y.left (g.left ⁻¹ᵁ U)).map (formsSheafD k Y n)) :=
    e.naturality (formsSheafD k Y n)
  rw [← Category.assoc, he, Category.assoc, ← F.map_comp,
    formsRestriction_d, F.map_comp, ← Category.assoc]

private lemma formsPushforwardRestriction_theta {X Y : Over (Spec (CommRingCat.of k))}
    (g : Y ⟶ X) (U : X.left.Opens) (v : (sectionAlgebra k Y ⊤)ˣ) (n : ℕ) :
    (schemeSheafRestrict (k := k) X.left U).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (thetaWedgeSheaf Y v n)) ≫
        (formsPushforwardRestrictionIso (k := k) g U (n + 1)).hom =
      (formsPushforwardRestrictionIso (k := k) g U n).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base).map
          (thetaWedgeSheaf (openOver Y (g.left ⁻¹ᵁ U))
            (Units.map (sectionPullbackTop (openInclusion Y (g.left ⁻¹ᵁ U))).toMonoidHom v) n) := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{u} k) (g.left ∣_ U).base
  let e := (restrictPushforwardIso (k := k) g.left U).hom
  change (schemeSheafRestrict (k := k) X.left U).map
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (thetaWedgeSheaf Y v n)) ≫
      (e.app (formsSheaf k Y (n + 1)) ≫ F.map (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) (n +
        1)).hom) =
    (e.app (formsSheaf k Y n) ≫ F.map (schemeFormsRestrictionIso Y (g.left ⁻¹ᵁ U) n).hom) ≫
      F.map (thetaWedgeSheaf (openOver Y (g.left ⁻¹ᵁ U))
        (Units.map (sectionPullbackTop (openInclusion Y (g.left ⁻¹ᵁ U))).toMonoidHom v) n)
  have he : (schemeSheafRestrict (k := k) X.left U).map
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) g.left.base).map (thetaWedgeSheaf Y v n)) ≫
      e.app (formsSheaf k Y (n + 1)) =
    e.app (formsSheaf k Y n) ≫
      F.map ((schemeSheafRestrict (k := k) Y.left (g.left ⁻¹ᵁ U)).map (thetaWedgeSheaf Y v n)) :=
    e.naturality (thetaWedgeSheaf Y v n)
  rw [← Category.assoc, he, Category.assoc, ← F.map_comp,
    formsRestriction_theta, F.map_comp, ← Category.assoc]

/-- Ambient forms restricted to the affine neighborhood are its relative forms. -/
@[no_expose] def regularFormsSheafRestrictionIso (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).obj
      (formsSheaf k P.ambient.obj n) ≅ formsSheaf k (affineNeighborhoodPair P V).ambient.obj n :=
  schemeFormsRestrictionIso P.ambient.obj V.1 n

/-- Complement forms commute with restriction through the actual Cartesian open square. -/
@[no_expose] def openFormsSheafRestrictionIso (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).obj (openFormsSheaf P n) ≅
      openFormsSheaf (affineNeighborhoodPair P V) n :=
  formsPushforwardRestrictionIso (k := k) P.j.hom V.1 n

/-- The affine-neighborhood comparisons preserve regular-form pullback to the complement. -/
lemma regularFormsSheafRestrictionIso_square (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).map
        (formsSheafPullback P.j.hom n) ≫ (openFormsSheafRestrictionIso P V n).hom =
      (regularFormsSheafRestrictionIso P V n).hom ≫
        formsSheafPullback (affineNeighborhoodPair P V).j.hom n :=
  (formsRestriction_pullback (k := k) P.j.hom V.1 n).symm

private lemma neighborhood_eqnUnit :
    Units.map (sectionPullbackTop
      (openInclusion P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1))).toMonoidHom P.eqnUnit =
      (affineNeighborhoodPair P V).eqnUnit := by
  apply Units.ext
  change (P.j.hom.left ⁻¹ᵁ V.1).ι.appTop (P.j.hom.left.appTop P.eqn) =
    (P.j.hom.left ∣_ V.1).appTop (V.1.ι.appTop P.eqn)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, morphismRestrict_ι]

/-- Complement restriction preserves left multiplication by the logarithmic form. -/
lemma openFormsSheafRestrictionIso_theta (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).map (openThetaWedgeSheaf P n) ≫
        (openFormsSheafRestrictionIso P V (n + 1)).hom =
      (openFormsSheafRestrictionIso P V n).hom ≫ openThetaWedgeSheaf (affineNeighborhoodPair P V) n
        := by
  have h := formsPushforwardRestriction_theta (k := k) P.j.hom V.1 P.eqnUnit n
  rw [neighborhood_eqnUnit P V] at h
  exact h

/-- Complement restriction commutes with the differential. -/
lemma openFormsSheafRestrictionIso_d (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) P.j.hom.left.base).map
          (formsSheafD k P.compl.obj n)) ≫ (openFormsSheafRestrictionIso P V (n + 1)).hom =
      (openFormsSheafRestrictionIso P V n).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (affineNeighborhoodPair P
          V).j.hom.left.base).map
          (formsSheafD k (affineNeighborhoodPair P V).compl.obj n) :=
  formsPushforwardRestriction_d (k := k) P.j.hom V.1 n

/-- Restriction of a logarithmic sheaf is the logarithmic sheaf of the affine-neighborhood pair. -/
@[no_expose] def logSheafRestrictionIso (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).obj (logSheaf P n) ≅
      logSheaf (affineNeighborhoodPair P V) n :=
  restrictionLogIso P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V) n

/-- Logarithmic restriction preserves the inclusion in complement forms. -/
lemma logSheafRestrictionIso_toOpen (n : ℕ) :
    (logSheafRestrictionIso P V n).hom ≫ logToOpenSheaf (affineNeighborhoodPair P V) n =
      (affineNeighborhoodSheafRestrict P V).map (logToOpenSheaf P n) ≫
        (openFormsSheafRestrictionIso P V n).hom :=
  restrictionLogIso_hom_comp P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V) n

/-- Logarithmic restriction preserves regular forms. -/
lemma logSheafRestrictionIso_regular (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).map (regularToLogSheaf P n) ≫
        (logSheafRestrictionIso P V n).hom =
      (regularFormsSheafRestrictionIso P V n).hom ≫ regularToLogSheaf (affineNeighborhoodPair P V)
        n :=
  restrictionLogIso_regular P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V) n

/-- Logarithmic restriction commutes with the differential. -/
lemma logSheafRestrictionIso_d (n : ℕ) :
    (logSheafRestrictionIso P V n).hom ≫ logSheafD (affineNeighborhoodPair P V) n =
      (affineNeighborhoodSheafRestrict P V).map (logSheafD P n) ≫
        (logSheafRestrictionIso P V (n + 1)).hom :=
  restrictionLogIso_d P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V)
    (openFormsSheafRestrictionIso_d P V) n

/-- Restriction identifies the logarithmic complexes on the actual open schemes. -/
@[no_expose] def logComplexRestrictionIso :
    ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).obj
      (logComplexNat P) ≅ logComplexNat (affineNeighborhoodPair P V) :=
  restrictionLogComplexIso P (affineNeighborhoodPair P V) (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V)
    (openFormsSheafRestrictionIso_d P V)

/-- Restriction identifies the ordinary complement-form complexes. -/
@[no_expose] def openComplexRestrictionIso :
    ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).obj
      (openFormsComplexNat P) ≅ openFormsComplexNat (affineNeighborhoodPair P V) :=
  restrictionOpenComplexIso P (affineNeighborhoodPair P V) (affineNeighborhoodSheafRestrict P V)
    (openFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso_d P V)

/-- The logarithmic and complement restriction isomorphisms preserve inclusion. -/
lemma logComplexRestrictionIso_toOpen :
    (logComplexRestrictionIso P V).hom ≫ logToOpenComplexNat (affineNeighborhoodPair P V) =
      ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).map
        (logToOpenComplexNat P) ≫ (openComplexRestrictionIso P V).hom :=
  restrictionLogComplexIso_toOpen P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V)
    (openFormsSheafRestrictionIso_d P V)

/-- The sections of a module sheaf on a specified open. -/
def sheafSectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    TopCat.Sheaf (ModuleCat.{u} k) X ⥤ ModuleCat.{u} k :=
  sheafToPresheaf (_root_.Opens.grothendieckTopology X) (ModuleCat k) ⋙
    (evaluation _ _).obj (op U)

/-- Evaluation of module sheaves preserves zero morphisms. -/
instance sheafSectionsFunctor_preservesZero (X : Scheme.{u}) (U : X.Opens) :
    (sheafSectionsFunctor (k := k) X U).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- The complex of sections of a sheaf complex on a specified open. -/
@[implicit_reducible] def sheafComplexSections (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  ((sheafSectionsFunctor (k := k) X U).mapHomologicalComplex (.up ℕ)).obj K

private def restrictionSectionsIso :
    affineNeighborhoodSheafRestrict P V ⋙
        sheafSectionsFunctor (k := k) (affineNeighborhoodPair P V).ambient.obj.left ⊤ ≅
      sheafSectionsFunctor (k := k) P.ambient.obj.left V.1 :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (eqToIso (congrArg op (Scheme.Opens.ι_image_top V.1)))) (by
      intro F G m
      exact (m.hom.naturality
        (eqToHom (congrArg op (Scheme.Opens.ι_image_top V.1)))).symm)

/-- Sections on the top of the restricted open scheme are sections on the original open. -/
@[no_expose] def restrictionSectionsComplexIso :
    (affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ) ⋙
        (sheafSectionsFunctor (k := k)
          (affineNeighborhoodPair P V).ambient.obj.left ⊤).mapHomologicalComplex (.up ℕ) ≅
      (sheafSectionsFunctor (k := k) P.ambient.obj.left V.1).mapHomologicalComplex (.up ℕ) :=
  Functor.mapHomologicalComplexCompIso (restrictionSectionsIso P V) (.up ℕ)

private def localAlgebraicLogIso :
    logComplex k (affineNeighborhoodAlgebraicPair P V).eqn
      (affineNeighborhoodAlgebraicPair P V).compl ≅
      ((sheafSectionsFunctor (k := k) (affineNeighborhoodPair P V).ambient.obj.left
        ⊤).mapHomologicalComplex
         (.up ℕ)).obj (logComplexNat (affineNeighborhoodPair P V)) :=
  affineLogComplexIso (affineNeighborhoodPair P V)

private def localAlgebraicOpenIso :
    complex k (affineNeighborhoodAlgebraicPair P V).compl ≅
      ((sheafSectionsFunctor (k := k) (affineNeighborhoodPair P V).ambient.obj.left
        ⊤).mapHomologicalComplex
         (.up ℕ)).obj (openFormsComplexNat (affineNeighborhoodPair P V)) :=
  complexIsoGlobalFormsComplex (affineNeighborhoodPair P V).compl.obj

/-- Algebraic logarithmic forms on an affine-neighborhood pair compute the logarithmic sections
  there. -/
@[no_expose] def affineNeighborhoodLogComplexIso :
    logComplex k (affineNeighborhoodAlgebraicPair P V).eqn
      (affineNeighborhoodAlgebraicPair P V).compl ≅
      sheafComplexSections P.ambient.obj.left V.1 (logComplexNat P) :=
  localAlgebraicLogIso P V ≪≫
    ((sheafSectionsFunctor (k := k)
      (affineNeighborhoodPair P V).ambient.obj.left ⊤).mapHomologicalComplex (.up ℕ)).mapIso
        (logComplexRestrictionIso P V).symm ≪≫
    (restrictionSectionsComplexIso P V).app (logComplexNat P)

/-- Algebraic forms on the affine-neighborhood complement compute the complement-form sections
  there. -/
@[no_expose] def affineNeighborhoodOpenComplexIso :
    complex k (affineNeighborhoodAlgebraicPair P V).compl ≅
      sheafComplexSections P.ambient.obj.left V.1 (openFormsComplexNat P) :=
  localAlgebraicOpenIso P V ≪≫
    ((sheafSectionsFunctor (k := k)
      (affineNeighborhoodPair P V).ambient.obj.left ⊤).mapHomologicalComplex (.up ℕ)).mapIso
        (openComplexRestrictionIso P V).symm ≪≫
    (restrictionSectionsComplexIso P V).app (openFormsComplexNat P)

/-- On an affine pair, the algebraic and sheaf-global inclusions form a commuting square. -/
lemma affineLogComplexIso_toOpen (Q : DivisorPair (SmoothDomain.aff k)) :
    (affineLogComplexIso Q).hom ≫
        ((sheafSectionsFunctor (k := k) Q.ambient.obj.left ⊤).mapHomologicalComplex (.up ℕ)).map
          (logToOpenComplexNat Q) =
      logToLocalization k Q.globalSections.eqn Q.globalSections.compl ≫
        (complexIsoGlobalFormsComplex Q.compl.obj).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change logPower k Q.globalSections.eqn Q.globalSections.compl n at x
  change (logToOpenSheaf Q n).hom.app (op ⊤)
      ((affineLogComplexIso Q).hom.f n x) =
    (complexIsoGlobalFormsComplex Q.compl.obj).hom.f n
      (logPowerToPower k Q.globalSections.eqn Q.globalSections.compl n x)
  rw [affineLogComplexIso_hom_f]
  exact affineLogComparison_toOpen Q n x

private lemma localAlgebraicLogIso_toOpen :
    (localAlgebraicLogIso P V).hom ≫
        ((sheafSectionsFunctor (k := k) (affineNeighborhoodPair P V).ambient.obj.left
          ⊤).mapHomologicalComplex
           (.up ℕ)).map
            (logToOpenComplexNat (affineNeighborhoodPair P V)) =
      logToLocalization k (affineNeighborhoodAlgebraicPair P V).eqn
        (affineNeighborhoodAlgebraicPair P V).compl ≫ (localAlgebraicOpenIso P V).hom :=
  affineLogComplexIso_toOpen (affineNeighborhoodPair P V)

private lemma logComplexRestrictionIso_inv_toOpen :
    (logComplexRestrictionIso P V).inv ≫
        ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).map
          (logToOpenComplexNat P) =
      logToOpenComplexNat (affineNeighborhoodPair P V) ≫ (openComplexRestrictionIso P V).inv := by
  apply (cancel_mono (openComplexRestrictionIso P V).hom).1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← logComplexRestrictionIso_toOpen, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The affine-neighborhood algebraic and geometric inclusions form a commuting square of
  complexes. -/
lemma affineNeighborhoodLogComplexIso_toOpen :
    (affineNeighborhoodLogComplexIso P V).hom ≫
        ((sheafSectionsFunctor (k := k) P.ambient.obj.left V.1).mapHomologicalComplex (.up ℕ)).map
          (logToOpenComplexNat P) =
      logToLocalization k (affineNeighborhoodAlgebraicPair P V).eqn
        (affineNeighborhoodAlgebraicPair P V).compl ≫
          (affineNeighborhoodOpenComplexIso P V).hom := by
  let E := (sheafSectionsFunctor (k := k)
    (affineNeighborhoodPair P V).ambient.obj.left ⊤).mapHomologicalComplex (.up ℕ)
  let R := (affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)
  let T := (sheafSectionsFunctor (k := k) P.ambient.obj.left V.1).mapHomologicalComplex (.up ℕ)
  let u := restrictionSectionsComplexIso P V
  have hu : E.map (R.map (logToOpenComplexNat P)) ≫ (u.app (openFormsComplexNat P)).hom =
      (u.app (logComplexNat P)).hom ≫ T.map (logToOpenComplexNat P) :=
    u.hom.naturality (logToOpenComplexNat P)
  change (localAlgebraicLogIso P V).hom ≫
      E.map (logComplexRestrictionIso P V).inv ≫ (u.app (logComplexNat P)).hom ≫
        T.map (logToOpenComplexNat P) =
    logToLocalization k (affineNeighborhoodAlgebraicPair P V).eqn
      (affineNeighborhoodAlgebraicPair P V).compl ≫
      (localAlgebraicOpenIso P V).hom ≫
        E.map (openComplexRestrictionIso P V).inv ≫ (u.app (openFormsComplexNat P)).hom
  rw [← hu, ← Category.assoc (E.map (logComplexRestrictionIso P V).inv),
    ← E.map_comp, logComplexRestrictionIso_inv_toOpen, E.map_comp]
  simp only [← Category.assoc]
  rw [localAlgebraicLogIso_toOpen P V]

/-- Ambient-form restriction commutes with the differential. -/
lemma regularFormsSheafRestrictionIso_d (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).map (formsSheafD k P.ambient.obj n) ≫
        (regularFormsSheafRestrictionIso P V (n + 1)).hom =
      (regularFormsSheafRestrictionIso P V n).hom ≫
        formsSheafD k (affineNeighborhoodPair P V).ambient.obj n :=
  formsRestriction_d P.ambient.obj V.1 n

/-- Restriction identifies the ambient regular-form complexes. -/
def regularComplexRestrictionIso :
    ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).obj
      (formsComplexNat k P.ambient.obj) ≅ formsComplexNat k (affineNeighborhoodPair P
        V).ambient.obj :=
  HomologicalComplex.Hom.isoOfComponents (regularFormsSheafRestrictionIso P V) (by
    rintro n _ rfl
    simp only [Functor.mapHomologicalComplex_obj_d, formsComplexNat_d]
    exact (regularFormsSheafRestrictionIso_d P V n).symm)

/-- The logarithmic complex restriction has the specified sheaf comparisons as its components. -/
lemma logComplexRestrictionIso_hom_f (n : ℕ) :
    (logComplexRestrictionIso P V).hom.f n = (logSheafRestrictionIso P V n).hom :=
  restrictionLogComplexIso_hom_f P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V)
    (openFormsSheafRestrictionIso_d P V) n

/-- The complement complex restriction has the specified sheaf comparisons as its components. -/
lemma openComplexRestrictionIso_hom_f (n : ℕ) :
    (openComplexRestrictionIso P V).hom.f n = (openFormsSheafRestrictionIso P V n).hom :=
  restrictionOpenComplexIso_hom_f P (affineNeighborhoodPair P V)
    (affineNeighborhoodSheafRestrict P V)
    (openFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso_d P V) n

/-- Restriction of logarithmic complexes preserves regular inclusion. -/
lemma logComplexRestrictionIso_regular :
    ((affineNeighborhoodSheafRestrict P V).mapHomologicalComplex (.up ℕ)).map
        (regularToLogComplexNat P) ≫ (logComplexRestrictionIso P V).hom =
      (regularComplexRestrictionIso P V).hom ≫ regularToLogComplexNat (affineNeighborhoodPair P V)
        := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, logComplexRestrictionIso_hom_f]
  exact logSheafRestrictionIso_regular P V n

/-- Restriction identifies the regular-plus-logarithmic generator sources. -/
def normalSourceRestrictionIso (n : ℕ) :
    (affineNeighborhoodSheafRestrict P V).obj
      (formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n) ≅
        formsSheaf k (affineNeighborhoodPair P V).ambient.obj (n + 1) ⊞
          formsSheaf k (affineNeighborhoodPair P V).ambient.obj n :=
  restrictionNormalSourceIso P (affineNeighborhoodPair P V) (affineNeighborhoodSheafRestrict P V)
    (regularFormsSheafRestrictionIso P V) n

/-- Restriction preserves the regular-plus-logarithmic normal-form map. -/
lemma normalSourceRestrictionIso_normal (n : ℕ) :
    (normalSourceRestrictionIso P V n).hom ≫ logNormalFormSheaf (affineNeighborhoodPair P V) n =
      (affineNeighborhoodSheafRestrict P V).map (logNormalFormSheaf P n) ≫
        (openFormsSheafRestrictionIso P V (n + 1)).hom :=
  restrictionNormalSourceIso_normal P (affineNeighborhoodPair P V) (affineNeighborhoodSheafRestrict
    P V)
    (regularFormsSheafRestrictionIso P V) (openFormsSheafRestrictionIso P V)
    (regularFormsSheafRestrictionIso_square P V) (openFormsSheafRestrictionIso_theta P V) n

/-- The terms of a section complex are the sections of its terms. -/
@[simp] lemma sheafComplexSections_X (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℕ) :
    (sheafComplexSections X U K).X n = (K.X n).obj.obj (op U) := rfl

/-- The differential of a section complex is the map on sections induced by its differential. -/
@[simp] lemma sheafComplexSections_d (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (i j : ℕ) :
    (sheafComplexSections X U K).d i j = (K.d i j).hom.app (op U) := rfl

end OrlikSolomon.Geometric.DeRham
