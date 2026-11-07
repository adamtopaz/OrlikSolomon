/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module
public import OrlikSolomon.DeRham.Schemes.Forms.Sheaf
public import Mathlib.Topology.Sheaves.Functors
/-!
# Pullback of relative differential forms

A map of schemes over `Spec k` induces a map of forms on each open and its inverse image.
Sheafification gives the adjoint pushforward formulation of pullback of sheaf forms. These maps
commute with the differential without any flatness hypothesis.

## Main definitions and results

* `sectionPullback`: the base-linear map of functions on an open to its inverse image.
* `formsPresheafPullback` and `formsSheafPullback`: pullback before and after sheafification.
* `formsSheafPullback_unit`: agreement on forms represented by presheaf sections.
* `formsSheafPullback_d`: compatibility with the relative de Rham differential.
* `formsSheafInverseImage`: the equivalent map from the inverse-image sheaf.

The base ring is arbitrary, and neither scheme is required to be smooth or affine.

Blueprint: the pullback construction in `thm:geo-forms-comparison`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k]
variable {X Y : Over (Spec (CommRingCat.of k))}

/-- Pullback of functions along a map over `Spec k`, as a base-linear algebra map. -/
def sectionPullback (g : X ⟶ Y) (U : Y.left.Opens) :
    sectionAlgebra k Y U →ₐ[k] sectionAlgebra k X (g.left ⁻¹ᵁ U) where
  toRingHom := (g.left.app U).hom
  commutes' r := by
    have h : Y.hom.appTop ≫ Y.left.presheaf.map U.leTop.op ≫ g.left.app U =
        X.hom.appTop ≫ X.left.presheaf.map (g.left ⁻¹ᵁ U).leTop.op := by
      rw [g.left.naturality, ← Category.assoc]
      change (Y.hom.appTop ≫ g.left.appTop) ≫ _ = _
      rw [← Scheme.Hom.comp_appTop, g.w]
      rfl
    exact congrArg (fun φ => φ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) h

@[simp] theorem sectionPullback_id (U : X.left.Opens) :
    sectionPullback (𝟙 X) U = AlgHom.id k (sectionAlgebra k X U) := by
  ext r
  rfl

/-- Pullback of functions is contravariantly compatible with composition. -/
theorem sectionPullback_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.left.Opens) :
    sectionPullback (f ≫ g) U =
      (sectionPullback f (g.left ⁻¹ᵁ U)).comp (sectionPullback g U) := by
  ext r
  rfl

/-- Pullback of functions commutes with restriction of opens. -/
theorem sectionPullback_restrict (g : X ⟶ Y) {U V : Y.left.Opens} (i : U ⟶ V) :
    (sectionPullback g U).comp (sectionRestriction k Y i) =
      (sectionRestriction k X ((TopologicalSpace.Opens.map g.left.base).map i)).comp
        (sectionPullback g V) := by
  ext r
  exact ConcreteCategory.congr_hom (g.left.naturality i.op) r

/-- Pullback of algebraic forms on each open to its inverse image. -/
def formsPresheafPullback (g : X ⟶ Y) (n : ℕ) : formsPresheaf k Y n ⟶
    (TopologicalSpace.Opens.map g.left.base).op ⋙ formsPresheaf k X n where
  app U := ModuleCat.ofHom (Forms.mapPower (sectionPullback g U.unop) n)
  naturality U V i := by
    apply ModuleCat.hom_ext
    change Forms.mapPower (sectionPullback g V.unop) n ∘ₗ
      Forms.mapPower (sectionRestriction k Y i.unop) n =
      Forms.mapPower (sectionRestriction k X
        ((TopologicalSpace.Opens.map g.left.base).map i.unop)) n ∘ₗ
          Forms.mapPower (sectionPullback g U.unop) n
    rw [← Forms.mapPower_comp, ← Forms.mapPower_comp, sectionPullback_restrict]

@[simp] theorem formsPresheafPullback_id (n : ℕ) :
    formsPresheafPullback (𝟙 X) n = 𝟙 (formsPresheaf k X n) := by
  ext U x
  change Forms.mapPower (sectionPullback (𝟙 X) U.unop) n x = x
  rw [sectionPullback_id]
  exact LinearMap.congr_fun (Forms.mapPower_id n) x

/-- Pullback of presheaf forms is contravariantly compatible with composition. -/
theorem formsPresheafPullback_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    formsPresheafPullback (f ≫ g) n = formsPresheafPullback g n ≫
      Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
        (formsPresheafPullback f n) := by
  ext U x
  change Forms.mapPower (sectionPullback (f ≫ g) U.unop) n x =
    Forms.mapPower (sectionPullback f (g.left ⁻¹ᵁ U.unop)) n
      (Forms.mapPower (sectionPullback g U.unop) n x)
  rw [sectionPullback_comp]
  exact LinearMap.congr_fun (Forms.mapPower_comp _ _ n) x

/-- Presheaf pullback commutes with the differential. -/
theorem formsPresheafPullback_d (g : X ⟶ Y) (n : ℕ) :
    formsPresheafPullback g n ≫
      Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
        (formsPresheafD k X n) =
      formsPresheafD k Y n ≫ formsPresheafPullback g (n + 1) := by
  ext U x
  exact (Forms.mapPower_powerD (sectionPullback g U.unop) n x).symm
/-- Pullback of sheaf forms, expressed by its adjoint map into the pushforward. -/
def formsSheafPullback (g : X ⟶ Y) (n : ℕ) : formsSheaf k Y n ⟶
    (TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).obj (formsSheaf k X n) where
  hom := sheafifyLift (_root_.Opens.grothendieckTopology Y.left)
    (formsPresheafPullback g n ≫
      Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op (formsSheafUnit k X n))
    ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).obj (formsSheaf k X n)).property

/-- Sheaf pullback agrees with algebraic pullback on presheaf representatives. -/
theorem formsSheafPullback_unit (g : X ⟶ Y) (n : ℕ) :
    formsSheafUnit k Y n ≫ (formsSheafPullback g n).hom =
      formsPresheafPullback g n ≫
        Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
          (formsSheafUnit k X n) :=
  toSheafify_sheafifyLift _ _ _

/-- The representative formula for pullback on an individual open. -/
@[simp] theorem formsSheafPullback_unit_apply (g : X ⟶ Y) (n : ℕ)
    (U : Y.left.Opensᵒᵖ) (x : (formsPresheaf k Y n).obj U) :
    (formsSheafPullback g n).hom.app U ((formsSheafUnit k Y n).app U x) =
      (formsSheafUnit k X n).app (op (g.left ⁻¹ᵁ U.unop))
        ((formsPresheafPullback g n).app U x) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafPullback_unit g n) U) x

@[simp] theorem formsSheafPullback_id (n : ℕ) :
    formsSheafPullback (𝟙 X) n = 𝟙 (formsSheaf k X n) := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (_root_.Opens.grothendieckTopology X.left) _ _
    (formsSheaf k X n).property
  ext U x
  change (formsSheafPullback (𝟙 X) n).hom.app U ((formsSheafUnit k X n).app U x) =
    (formsSheafUnit k X n).app U x
  rw [formsSheafPullback_unit_apply]
  exact congrArg ((formsSheafUnit k X n).app U)
    (ConcreteCategory.congr_hom (NatTrans.congr_app (formsPresheafPullback_id n) U) x)

/-- Pullback of sheaf forms is contravariantly compatible with composition. -/
theorem formsSheafPullback_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    formsSheafPullback (f ≫ g) n = formsSheafPullback g n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).map (formsSheafPullback f n) := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (_root_.Opens.grothendieckTopology Z.left) _ _
    ((TopCat.Sheaf.pushforward (ModuleCat k) (f ≫ g).left.base).obj
      (formsSheaf k X n)).property
  ext U x
  change (formsSheafPullback (f ≫ g) n).hom.app U ((formsSheafUnit k Z n).app U x) =
    (formsSheafPullback f n).hom.app (op (g.left ⁻¹ᵁ U.unop))
      ((formsSheafPullback g n).hom.app U ((formsSheafUnit k Z n).app U x))
  simp only [formsSheafPullback_unit_apply]
  exact congrArg ((formsSheafUnit k X n).app (op ((f ≫ g).left ⁻¹ᵁ U.unop)))
    (ConcreteCategory.congr_hom
      (NatTrans.congr_app (formsPresheafPullback_comp f g n) U) x)

/-- Sheaf pullback commutes with the relative de Rham differential. -/
theorem formsSheafPullback_d (g : X ⟶ Y) (n : ℕ) :
    formsSheafPullback g n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).map (formsSheafD k X n) =
      formsSheafD k Y n ≫ formsSheafPullback g (n + 1) := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (_root_.Opens.grothendieckTopology Y.left) _ _
    ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).obj
      (formsSheaf k X (n + 1))).property
  ext U x
  change (formsSheafD k X n).hom.app
      (op (g.left ⁻¹ᵁ U.unop))
      ((formsSheafPullback g n).hom.app U ((formsSheafUnit k Y n).app U x)) =
    (formsSheafPullback g (n + 1)).hom.app U
      ((formsSheafD k Y n).hom.app U ((formsSheafUnit k Y n).app U x))
  have hu (m : ℕ) (z : (formsPresheaf k Y m).obj U) :
      (formsSheafPullback g m).hom.app U ((formsSheafUnit k Y m).app U z) =
        (formsSheafUnit k X m).app (op (g.left ⁻¹ᵁ U.unop))
          ((formsPresheafPullback g m).app U z) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafPullback_unit g m) U) z
  have hd (Z : Over (Spec (CommRingCat.of k))) (V : Z.left.Opensᵒᵖ)
      (z : (formsPresheaf k Z n).obj V) :
      (formsSheafD k Z n).hom.app V ((formsSheafUnit k Z n).app V z) =
        (formsSheafUnit k Z (n + 1)).app V ((formsPresheafD k Z n).app V z) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafUnit_d k Z n) V) z
  rw [hu, hd, hd, hu]
  exact congrArg ((formsSheafUnit k X (n + 1)).app (op (g.left ⁻¹ᵁ U.unop)))
    (ConcreteCategory.congr_hom (NatTrans.congr_app (formsPresheafPullback_d g n) U) x)

/-- Pullback of relative forms in the inverse-image formulation, as a map of sheaves of
`k`-modules. It is adjoint to `formsSheafPullback`, and needs no flatness hypothesis. -/
def formsSheafInverseImage (g : X ⟶ Y) (n : ℕ) :
    (TopCat.Sheaf.pullback (ModuleCat k) g.left.base).obj (formsSheaf k Y n) ⟶
      formsSheaf k X n :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).homEquiv _ _).symm
    (formsSheafPullback g n)

/-- The inverse-image and pushforward formulations of form pullback are adjoint. -/
@[simp] theorem formsSheafInverseImage_adjunction (g : X ⟶ Y) (n : ℕ) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).homEquiv _ _
      (formsSheafInverseImage g n) = formsSheafPullback g n :=
  Equiv.apply_symm_apply _ _

/-- Inverse-image pullback commutes with the relative de Rham differential. -/
theorem formsSheafInverseImage_d (g : X ⟶ Y) (n : ℕ) :
    formsSheafInverseImage g n ≫ formsSheafD k X n =
      (TopCat.Sheaf.pullback (ModuleCat k) g.left.base).map (formsSheafD k Y n) ≫
        formsSheafInverseImage g (n + 1) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k)
    g.left.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    formsSheafInverseImage_adjunction, formsSheafInverseImage_adjunction]
  exact formsSheafPullback_d g n

end OrlikSolomon.Geometric.DeRham
