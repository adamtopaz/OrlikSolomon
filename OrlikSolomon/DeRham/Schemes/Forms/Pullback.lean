/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms.Sheaf
public import OrlikSolomon.Geometry.Schemes.ModuleGluing
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
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
* `formsSheafInverseImage`: the equivalent map from the inverse-image sheaf of base modules.
* `OrlikSolomon.Geometric.sheafPullbackId` and `OrlikSolomon.Geometric.sheafPullbackComp`:
  canonical coherence isomorphisms for inverse images.
* `formsSheafInverseImage_id`, `formsSheafInverseImage_comp`: inverse-image functoriality.
* `formsSheafInverseImage_wedge`: wedge compatibility on sections represented by
  the adjunction unit.
* `formsModuleSheafPullback` and `formsModuleSheafInverseImage`: the structure-sheaf-linear
  pushforward and inverse-image formulations on the same additive carriers.
* `formsSheafPullback_isIso`: pullback along an isomorphism is invertible.
* `formsComplexNatPullback` and `formsComplexNatInverseImage`: the corresponding maps of
  nonnegative de Rham complexes, with component and functoriality formulas.

The base ring is arbitrary, and neither scheme is required to be smooth or affine.

Blueprint: the pullback construction in `thm:geo-forms-comparison`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open MonoidalCategory
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

/-- Pullback along an isomorphism identifies the algebras of functions on corresponding opens. -/
def sectionPullbackEquiv (g : X ⟶ Y) [IsIso g] (U : Y.left.Opens) :
    sectionAlgebra k Y U ≃ₐ[k] sectionAlgebra k X (g.left ⁻¹ᵁ U) := by
  have : IsIso g.left := (Over.forget _).map_isIso g
  exact AlgEquiv.ofBijective (sectionPullback g U)
    (ConcreteCategory.bijective_of_isIso (g.left.app U))

/-- The equivalence of functions acts by the original pullback of sections. -/
@[simp] theorem sectionPullbackEquiv_apply (g : X ⟶ Y) [IsIso g] (U : Y.left.Opens)
    (a : sectionAlgebra k Y U) :
    sectionPullbackEquiv g U a = sectionPullback g U a := rfl

private def formsPowerEquiv {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra k A] [Algebra k A'] (e : A ≃ₐ[k] A') (n : ℕ) :
    (⋀[A]^n Ω[A⁄k]) ≃ₗ[k] (⋀[A']^n Ω[A'⁄k]) where
  __ := Forms.mapPower e.toAlgHom n
  invFun := Forms.mapPower e.symm.toAlgHom n
  left_inv a := Subtype.ext ((Forms.mapEquiv e).left_inv a.val)
  right_inv a := Subtype.ext ((Forms.mapEquiv e).right_inv a.val)

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

/-- Pullback along an isomorphism is an isomorphism on presheaves of forms. -/
instance formsPresheafPullback_isIso (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    IsIso (formsPresheafPullback g n) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact (formsPowerEquiv (sectionPullbackEquiv g U.unop) n).bijective

/-- Presheaf pullback commutes with the differential. -/
theorem formsPresheafPullback_d (g : X ⟶ Y) (n : ℕ) :
    formsPresheafPullback g n ≫
      Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
        (formsPresheafD k X n) =
      formsPresheafD k Y n ≫ formsPresheafPullback g (n + 1) := by
  ext U x
  exact (Forms.mapPower_powerD (sectionPullback g U.unop) n x).symm

/-- Pullback of sheaf forms, expressed by its adjoint map into the pushforward.
Blueprint: `thm:geo-forms-comparison`. -/
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
theorem formsSheafPullback_unit_apply (g : X ⟶ Y) (n : ℕ)
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

private theorem opensMap_isCocontinuous (g : X ⟶ Y) [IsIso g] :
    (TopologicalSpace.Opens.map g.left.base).IsCocontinuous
      (_root_.Opens.grothendieckTopology Y.left) (_root_.Opens.grothendieckTopology X.left) := by
  let e := asIso g
  let E := TopologicalSpace.Opens.mapMapIso
    ((Over.forget _ ⋙ Scheme.forgetToTop).mapIso e)
  exact (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (coverPreserving_opens_map e.inv.left.base)

/-- Pullback along an isomorphism is an isomorphism on sheaves of forms. -/
instance formsSheafPullback_isIso (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    IsIso (formsSheafPullback g n) := by
  let JX := _root_.Opens.grothendieckTopology X.left
  let JY := _root_.Opens.grothendieckTopology Y.left
  have := opensMap_isCocontinuous g
  have : Presheaf.IsLocallyInjective JX (formsSheafUnit k X n) := by
    change Presheaf.IsLocallyInjective JX (toSheafify JX (formsPresheaf k X n))
    infer_instance
  have : Presheaf.IsLocallySurjective JX (formsSheafUnit k X n) := by
    change Presheaf.IsLocallySurjective JX (toSheafify JX (formsPresheaf k X n))
    infer_instance
  have := Presheaf.isLocallyInjective_whisker JY JX
    (TopologicalSpace.Opens.map g.left.base) (formsSheafUnit k X n)
  have := Presheaf.isLocallySurjective_whisker JY JX
    (TopologicalSpace.Opens.map g.left.base) (formsSheafUnit k X n)
  have hw : JY.W (formsPresheafPullback g n ≫
      Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
        (formsSheafUnit k X n)) :=
    JY.W.comp_mem _ _ (ObjectProperty.isLocal_of_isIso _ _)
      (JY.W_of_isLocallyBijective _)
  rw [← formsSheafPullback_unit] at hw
  exact (JY.W_sheafToPresheaf_map_iff_isIso _).1
    ((JY.W.precomp_iff _ _ (JY.W_toSheafify (formsPresheaf k Y n))).1 hw)

/-- Pullback preserves wedge products, without a flatness hypothesis. -/
theorem formsSheafPullback_mul (g : X ⟶ Y) (p q : ℕ) :
    formsSheafMul k Y p q ≫ (formsSheafPullback g (p + q)).hom =
      ((formsSheafPullback g p).hom ⊗ₘ (formsSheafPullback g q).hom) ≫
        Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
          (formsSheafMul k X p q) := by
  apply formsSheaf_tensor_hom_ext k Y p q
    ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).obj (formsSheaf k X (p + q)))
  intro U a b
  change (formsSheafPullback g (p + q)).hom.app U
      (formsSheafWedge k Y p q U ((formsSheafUnit k Y p).app U a)
        ((formsSheafUnit k Y q).app U b)) =
    formsSheafWedge k X p q (op (g.left ⁻¹ᵁ U.unop))
      ((formsSheafPullback g p).hom.app U ((formsSheafUnit k Y p).app U a))
      ((formsSheafPullback g q).hom.app U ((formsSheafUnit k Y q).app U b))
  rw [formsSheafWedge_unit, formsSheafPullback_unit_apply,
    formsSheafPullback_unit_apply, formsSheafPullback_unit_apply, formsSheafWedge_unit]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k Y U.unop]^p Ω[sectionAlgebra k Y U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k Y U.unop]^q Ω[sectionAlgebra k Y U.unop⁄k] := b
  exact (Forms.map (sectionPullback g U.unop)).map_mul a'.val b'.val

/-- The section-level wedge formula for pullback. -/
theorem formsSheafPullback_wedge (g : X ⟶ Y) (p q : ℕ) (U : Y.left.Opensᵒᵖ)
    (a : (formsSheaf k Y p).obj.obj U) (b : (formsSheaf k Y q).obj.obj U) :
    (formsSheafPullback g (p + q)).hom.app U (formsSheafWedge k Y p q U a b) =
      formsSheafWedge k X p q (op (g.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback g p).hom.app U a) ((formsSheafPullback g q).hom.app U b) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafPullback_mul g p q) U) (a ⊗ₜ[k] b)

/-- On degree zero, pullback is the usual pullback of regular functions. -/
theorem formsSheafPullback_zero (g : X ⟶ Y) (U : Y.left.Opensᵒᵖ)
    (r : sectionAlgebra k Y U.unop) :
    (formsSheafPullback g 0).hom.app U ((formsSheafZeroIso k Y).hom.hom.app U r) =
      (formsSheafZeroIso k X).hom.hom.app (op (g.left ⁻¹ᵁ U.unop))
        (sectionPullback g U.unop r) := by
  change (formsSheafPullback g 0).hom.app U
      ((formsSheafUnit k Y 0).app U ((formsPresheafZero k Y).app U r)) =
    (formsSheafUnit k X 0).app (op (g.left ⁻¹ᵁ U.unop))
      ((formsPresheafZero k X).app (op (g.left ⁻¹ᵁ U.unop)) (sectionPullback g U.unop r))
  rw [formsSheafPullback_unit_apply]
  congr 1
  apply Subtype.ext
  exact Forms.map_algebraMap (sectionPullback g U.unop) r

/-- Pullback is semilinear for the natural structure-sheaf actions on the same carriers. -/
theorem formsSheafPullback_smul (g : X ⟶ Y) (n : ℕ) (U : Y.left.Opens)
    (r : sectionAlgebra k Y U) (a : (formsSheaf k Y n).obj.obj (op U)) :
    (formsSheafPullback g n).hom.app (op U) (formsSheafSMul k Y n U r a) =
      formsSheafSMul k X n (g.left ⁻¹ᵁ U) (sectionPullback g U r)
        ((formsSheafPullback g n).hom.app (op U) a) := by
  rw [← formsSheafWedge_zero_eq_smul]
  refine (formsSheafPullback_wedge g n 0 (op U) a
    ((formsSheafZeroIso k Y).hom.hom.app (op U) r)).trans ?_
  rw [formsSheafPullback_zero]
  exact formsSheafWedge_zero_eq_smul k X n (g.left ⁻¹ᵁ U) (sectionPullback g U r)
    ((formsSheafPullback g n).hom.app (op U) a)

/-- The additive pullback conjugated by the public comparisons with module-valued forms. -/
def formsModuleSheafPullbackPresheaf (g : X ⟶ Y) (n : ℕ) :
    (formsModuleSheaf k Y n).presheaf ⟶
      ((Scheme.Modules.pushforward g.left).obj (formsModuleSheaf k X n)).presheaf :=
  eqToHom (formsModuleSheaf_presheaf k Y n) ≫
    Functor.whiskerRight (formsSheafPullback g n).hom
      (forget₂ (ModuleCat k) AddCommGrpCat) ≫
    Functor.whiskerLeft (TopologicalSpace.Opens.map g.left.base).op
      (eqToHom (formsModuleSheaf_presheaf k X n).symm)

/-- The additive module pullback is the original base-linear pullback between carriers. -/
theorem formsModuleSheafPullbackPresheaf_app (g : X ⟶ Y) (n : ℕ) (U : Y.left.Opens)
    (a : Γ(formsModuleSheaf k Y n, U)) :
    (formsModuleSheafPullbackPresheaf g n).app (op U) a =
      (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U)).inv
        ((formsSheafPullback g n).hom.app (op U)
          ((formsModuleSheafBaseIso k Y n U).hom a)) := by
  change (eqToHom (formsModuleSheaf_presheaf k X n).symm).app
      (op (g.left ⁻¹ᵁ U))
      ((formsSheafPullback g n).hom.app (op U)
        ((eqToHom (formsModuleSheaf_presheaf k Y n)).app (op U) a)) = _
  rw [formsModuleSheaf_presheaf_hom_app]
  exact formsModuleSheaf_presheaf_inv_app k X n (g.left ⁻¹ᵁ U) _

/-- Under the carrier comparison, additive pullback agrees with base-linear pullback. -/
theorem formsModuleSheafPullbackPresheaf_compare (g : X ⟶ Y) (n : ℕ) (U : Y.left.Opens)
    (a : Γ(formsModuleSheaf k Y n, U)) :
    (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U)).hom
      ((formsModuleSheafPullbackPresheaf g n).app (op U) a) =
      (formsSheafPullback g n).hom.app (op U)
        ((formsModuleSheafBaseIso k Y n U).hom a) := by
  rw [formsModuleSheafPullbackPresheaf_app]
  exact Iso.inv_hom_id_apply _ _

/-- Pullback of forms as a morphism of structure-sheaf modules into the pushforward. -/
def formsModuleSheafPullback (g : X ⟶ Y) (n : ℕ) : formsModuleSheaf k Y n ⟶
    (Scheme.Modules.pushforward g.left).obj (formsModuleSheaf k X n) where
  val := PresheafOfModules.homMk (formsModuleSheafPullbackPresheaf g n) (by
    intro U r₀ a₀
    let r : Γ(Y.left, U.unop) := r₀
    let a : Γ(formsModuleSheaf k Y n, U.unop) := a₀
    change (formsModuleSheafPullbackPresheaf g n).app (op U.unop) (r • a) =
      r • (formsModuleSheafPullbackPresheaf g n).app (op U.unop) a
    apply (ConcreteCategory.bijective_of_isIso
      (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U.unop)).hom).injective
    change (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U.unop)).hom
        ((formsModuleSheafPullbackPresheaf g n).app (op U.unop) (r • a)) =
      (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U.unop)).hom
        ((show Γ(X.left, g.left ⁻¹ᵁ U.unop) from sectionPullback g U.unop r) •
          (show Γ(formsModuleSheaf k X n, g.left ⁻¹ᵁ U.unop) from
            (formsModuleSheafPullbackPresheaf g n).app (op U.unop) a))
    refine (formsModuleSheafPullbackPresheaf_compare g n U.unop (r • a)).trans ?_
    refine (congrArg ((formsSheafPullback g n).hom.app (op U.unop))
      (formsModuleSheafBaseIso_smul k Y n U.unop r a)).trans ?_
    refine (formsSheafPullback_smul g n U.unop r
      ((formsModuleSheafBaseIso k Y n U.unop).hom a)).trans ?_
    refine Eq.trans ?_ (formsModuleSheafBaseIso_smul k X n (g.left ⁻¹ᵁ U.unop)
      (sectionPullback g U.unop r) ((formsModuleSheafPullbackPresheaf g n).app (op U.unop) a)).symm
    exact congrArg (formsSheafSMul k X n (g.left ⁻¹ᵁ U.unop) (sectionPullback g U.unop r))
      (formsModuleSheafPullbackPresheaf_compare g n U.unop a).symm)

/-- The structure-sheaf-linear pullback has the prescribed underlying additive map. -/
@[simp] theorem formsModuleSheafPullback_presheaf (g : X ⟶ Y) (n : ℕ) :
    (formsModuleSheafPullback g n).mapPresheaf = formsModuleSheafPullbackPresheaf g n := by
  rfl

/-- The module-valued and base-linear pullbacks agree under the carrier comparisons. -/
theorem formsModuleSheafPullback_app (g : X ⟶ Y) (n : ℕ) (U : Y.left.Opens)
    (a : Γ(formsModuleSheaf k Y n, U)) :
    (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U)).hom
      ((formsModuleSheafPullback g n).app U a) =
      (formsSheafPullback g n).hom.app (op U)
        ((formsModuleSheafBaseIso k Y n U).hom a) := by
  change (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U)).hom
    ((formsModuleSheafPullbackPresheaf g n).app (op U) a) = _
  exact formsModuleSheafPullbackPresheaf_compare g n U a

/-- Pullback of forms in Mathlib's structure-sheaf-linear inverse-image formulation. -/
def formsModuleSheafInverseImage (g : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback g.left).obj (formsModuleSheaf k Y n) ⟶ formsModuleSheaf k X n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv _ _).symm
    (formsModuleSheafPullback g n)

/-- The inverse-image module map is adjoint to the same structure-sheaf-linear pullback. -/
@[simp] theorem formsModuleSheafInverseImage_adjunction (g : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv _ _
      (formsModuleSheafInverseImage g n) = formsModuleSheafPullback g n :=
  Equiv.apply_symm_apply _ _

/-- On sections, the adjoint inverse-image module map is the original pullback of forms. -/
theorem formsModuleSheafInverseImage_adjunction_app (g : X ⟶ Y) (n : ℕ)
    (U : Y.left.Opens) (a : Γ(formsModuleSheaf k Y n, U)) :
    (formsModuleSheafBaseIso k X n (g.left ⁻¹ᵁ U)).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv _ _
        (formsModuleSheafInverseImage g n)).app U a) =
      (formsSheafPullback g n).hom.app (op U)
        ((formsModuleSheafBaseIso k Y n U).hom a) := by
  rw [formsModuleSheafInverseImage_adjunction]
  exact formsModuleSheafPullback_app g n U a

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

section PullbackCoherence

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

private theorem homEquiv_pullbackId {F : C ⥤ C} (adj : F ⊣ 𝟭 C) (A : C) :
    adj.homEquiv _ _ ((adj.leftAdjointIdIso (Iso.refl _)).hom.app A) = 𝟙 A := by
  rw [Adjunction.leftAdjointIdIso_hom_app]
  dsimp only [Iso.refl_inv, NatTrans.id_app, Functor.id_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, ← Adjunction.homEquiv_symm_id]
  exact Equiv.apply_symm_apply _ _

private theorem homEquiv_pullbackComp {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E}
    {I : E ⥤ D} {J : C ⥤ E} (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (adj₃ : J ⊣ I ⋙ G)
    (A : C) :
    (adj₁.comp adj₂).homEquiv _ _
      ((adj₁.leftAdjointCompIso adj₂ adj₃ (Iso.refl _)).hom.app A) =
        adj₃.unit.app A := by
  rw [Adjunction.leftAdjointCompIso_hom_app]
  simp only [Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Adjunction.comp_counit_app]
  change (adj₁.comp adj₂).homEquiv _ _
    ((F ⋙ H).map (adj₃.unit.app A) ≫ (adj₁.comp adj₂).counit.app (J.obj A)) = _
  rw [Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_symm_id]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.apply_symm_apply, Category.comp_id]

end PullbackCoherence

@[deprecated (since := "2026-11-07")]
alias sheafPullbackId := OrlikSolomon.Geometric.sheafPullbackId

@[deprecated (since := "2026-11-07")]
alias sheafPullbackComp := OrlikSolomon.Geometric.sheafPullbackComp

@[deprecated (since := "2026-11-07")]
alias sheafPullbackComp_id_comp := OrlikSolomon.Geometric.sheafPullbackComp_id_comp

@[deprecated (since := "2026-11-07")]
alias sheafPullbackComp_comp_id := OrlikSolomon.Geometric.sheafPullbackComp_comp_id

@[deprecated (since := "2026-11-07")]
alias sheafPullbackComp_assoc := OrlikSolomon.Geometric.sheafPullbackComp_assoc

/-- Pullback of forms by the identity agrees with the canonical inverse-image identity
isomorphism. -/
@[simp] theorem formsSheafInverseImage_id (n : ℕ) :
    formsSheafInverseImage (𝟙 X) n =
      (Geometric.sheafPullbackId k X.left).hom.app (formsSheaf k X n) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k)
    (Over.Hom.left (𝟙 X)).base).homEquiv _ _).injective
  rw [formsSheafInverseImage_adjunction, formsSheafPullback_id]
  exact (homEquiv_pullbackId _ _).symm

-- Scheme composition and composition of the underlying continuous maps have the same
-- carriers; allow the adjunction lemmas to identify their displayed source types.
set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse-image pullback of forms is contravariantly functorial under the canonical
composition isomorphism, without any flatness hypothesis. -/
theorem formsSheafInverseImage_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (Geometric.sheafPullbackComp k f.left.base g.left.base).hom.app (formsSheaf k Z n) ≫
        formsSheafInverseImage (f ≫ g) n =
      (TopCat.Sheaf.pullback (ModuleCat k) f.left.base).map
        (formsSheafInverseImage g n) ≫ formsSheafInverseImage f n := by
  apply (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) f.left.base)).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  conv_rhs => rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, formsSheafInverseImage_adjunction,
    Adjunction.homEquiv_naturality_right, formsSheafInverseImage_adjunction,
    ← formsSheafPullback_comp]
  rw [show (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) f.left.base)).homEquiv _ _
      ((Geometric.sheafPullbackComp k f.left.base g.left.base).hom.app (formsSheaf k Z n))) =
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) (f ≫ g).left.base).unit.app
          (formsSheaf k Z n) from homEquiv_pullbackComp _ _ _ _]
  exact formsSheafInverseImage_adjunction (f ≫ g) n

/-- On a section represented by the adjunction unit, inverse-image pullback acts by the
original pullback on that open. -/
@[simp] theorem formsSheafInverseImage_unit_app (g : X ⟶ Y) (n : ℕ)
    (U : Y.left.Opensᵒᵖ) (a : (formsSheaf k Y n).obj.obj U) :
    dsimp% (formsSheafInverseImage g n).hom.app (op (g.left ⁻¹ᵁ U.unop))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).unit.app
          (formsSheaf k Y n)).hom.app U a) =
      (formsSheafPullback g n).hom.app U a := by
  have h := formsSheafInverseImage_adjunction g n
  rw [Adjunction.homEquiv_apply] at h
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun h => h.hom) h) U) a

/-- Inverse-image pullback preserves wedge products on sections represented by the
adjunction unit. Both sides are sections on the same inverse-image open. -/
theorem formsSheafInverseImage_wedge (g : X ⟶ Y) (p q : ℕ)
    (U : Y.left.Opensᵒᵖ) (a : (formsSheaf k Y p).obj.obj U)
    (b : (formsSheaf k Y q).obj.obj U) :
    dsimp% (formsSheafInverseImage g (p + q)).hom.app (op (g.left ⁻¹ᵁ U.unop))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).unit.app
          (formsSheaf k Y (p + q))).hom.app U (formsSheafWedge k Y p q U a b)) =
      formsSheafWedge k X p q (op (g.left ⁻¹ᵁ U.unop))
        ((formsSheafInverseImage g p).hom.app (op (g.left ⁻¹ᵁ U.unop))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).unit.app
            (formsSheaf k Y p)).hom.app U a))
        ((formsSheafInverseImage g q).hom.app (op (g.left ⁻¹ᵁ U.unop))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) g.left.base).unit.app
            (formsSheaf k Y q)).hom.app U b)) := by
  simp only [formsSheafInverseImage_unit_app]
  exact formsSheafPullback_wedge g p q U a b

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

/-- Pullback on the nonnegative de Rham complexes, in the pushforward formulation. -/
def formsComplexNatPullback (g : X ⟶ Y) : formsComplexNat k Y ⟶
    ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).mapHomologicalComplex (.up ℕ)).obj
      (formsComplexNat k X) :=
  CochainComplex.ofHom (fun n ↦ formsSheafPullback g n) (fun n ↦ by
    simpa only [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X,
      formsComplexNat_X, formsComplexNat_d]
      using formsSheafPullback_d g n)

/-- The component of complex pullback is the original sheaf pullback in that degree. -/
@[simp] theorem formsComplexNatPullback_f (g : X ⟶ Y) (n : ℕ) :
    (formsComplexNatPullback g).f n = formsSheafPullback g n := rfl

/-- Pullback by the identity is the identity on the nonnegative de Rham complex. -/
@[simp] theorem formsComplexNatPullback_id : formsComplexNatPullback (𝟙 X) =
    𝟙 (formsComplexNat k X) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact formsSheafPullback_id (k := k) (X := X) n

/-- Pullback of nonnegative de Rham complexes is contravariantly compatible with composition. -/
theorem formsComplexNatPullback_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    formsComplexNatPullback (f ≫ g) = formsComplexNatPullback g ≫
      ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).mapHomologicalComplex (.up ℕ)).map
        (formsComplexNatPullback f) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact formsSheafPullback_comp f g n

/-- An isomorphism of schemes induces an isomorphism of nonnegative de Rham complexes. -/
instance formsComplexNatPullback_isIso (g : X ⟶ Y) [IsIso g] :
    IsIso (formsComplexNatPullback g) := by
  have (n : ℕ) : IsIso ((formsComplexNatPullback g).f n) := by
    change IsIso (formsSheafPullback g n)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The base-linear inverse-image formulation of pullback on nonnegative de Rham complexes. -/
def formsComplexNatInverseImage (g : X ⟶ Y) :
    ((TopCat.Sheaf.pullback (ModuleCat k) g.left.base).mapHomologicalComplex (.up ℕ)).obj
      (formsComplexNat k Y) ⟶ formsComplexNat k X :=
  CochainComplex.ofHom (fun n ↦ formsSheafInverseImage g n) (fun n ↦ by
    simpa only [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X,
      formsComplexNat_X, formsComplexNat_d]
      using formsSheafInverseImage_d g n)

/-- In each degree, inverse-image complex pullback is the original sheaf inverse-image map. -/
@[simp] theorem formsComplexNatInverseImage_f (g : X ⟶ Y) (n : ℕ) :
    (formsComplexNatInverseImage g).f n = formsSheafInverseImage g n := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse-image pullback by the identity on the de Rham complex agrees with the canonical
identity comparison induced from the sheaf pullback functor. -/
@[simp] theorem formsComplexNatInverseImage_id :
    formsComplexNatInverseImage (𝟙 X) =
      ((NatIso.mapHomologicalComplex (Geometric.sheafPullbackId k X.left) (.up ℕ)) ≪≫
        CategoryTheory.Functor.mapHomologicalComplexIdIso _ (.up ℕ)).hom.app
          (formsComplexNat k X) := by
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [formsComplexNatInverseImage_f, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_X, formsComplexNat_X,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.id_obj,
    CategoryTheory.Functor.mapHomologicalComplexIdIso_hom_app_f]
    using (formsSheafInverseImage_id (k := k) (X := X) n).trans
      (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse-image pullback of de Rham complexes is functorial under the canonical
composition comparison induced from sheaf pullback. -/
theorem formsComplexNatInverseImage_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.Functor.mapHomologicalComplexCompIso
      (Geometric.sheafPullbackComp k f.left.base g.left.base) (.up ℕ)).hom.app
        (formsComplexNat k Z) ≫ formsComplexNatInverseImage (f ≫ g) =
      ((TopCat.Sheaf.pullback (ModuleCat k) f.left.base).mapHomologicalComplex (.up ℕ)).map
        (formsComplexNatInverseImage g) ≫ formsComplexNatInverseImage f := by
  apply HomologicalComplex.hom_ext
  intro n
  simpa using formsSheafInverseImage_comp f g n

/-- Pullback of global functions, typed at the displayed top opens. -/
def sectionPullbackTop (g : X ⟶ Y) : sectionAlgebra k Y ⊤ →ₐ[k] sectionAlgebra k X ⊤ :=
  sectionPullback g ⊤

/-- Global function pullback is the pullback on the top open. -/
@[simp] theorem sectionPullback_top_apply (g : X ⟶ Y) (r : sectionAlgebra k Y ⊤) :
    dsimp% sectionPullback g ⊤ r = sectionPullbackTop g r := rfl

@[simp] theorem sectionPullbackTop_id :
    sectionPullbackTop (𝟙 X) = AlgHom.id k (sectionAlgebra k X ⊤) := by
  ext r
  rfl

/-- Pullback of global functions is contravariantly functorial. -/
theorem sectionPullbackTop_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sectionPullbackTop (f ≫ g) = (sectionPullbackTop f).comp (sectionPullbackTop g) := by
  ext r
  rfl

/-- Pullback of global sheaf forms, typed at the displayed top opens. -/
def formsSheafPullbackTop (g : X ⟶ Y) (n : ℕ) :
    (formsSheaf k Y n).obj.obj (op ⊤) →ₗ[k] (formsSheaf k X n).obj.obj (op ⊤) :=
  ((formsSheafPullback g n).hom.app (op ⊤)).hom

/-- Pullback on the top open agrees with the typed global map. -/
@[simp] theorem formsSheafPullback_app_top (g : X ⟶ Y) (n : ℕ)
    (x : (formsSheaf k Y n).obj.obj (op ⊤)) :
    dsimp% (formsSheafPullback g n).hom.app (op ⊤) x = formsSheafPullbackTop g n x := rfl

@[simp] theorem formsSheafPullbackTop_id (n : ℕ) :
    formsSheafPullbackTop (𝟙 X) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (formsSheafPullback_id n)) (op ⊤)) x

/-- Pullback of global forms is contravariantly functorial. -/
theorem formsSheafPullbackTop_comp {Z : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    formsSheafPullbackTop (f ≫ g) n =
      (formsSheafPullbackTop f n).comp (formsSheafPullbackTop g n) := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun h => h.hom) (formsSheafPullback_comp f g n)) (op ⊤)) x

/-- Global pullback preserves wedge products on the displayed carriers. -/
theorem formsSheafPullbackTop_wedge (g : X ⟶ Y) (p q : ℕ)
    (a : (formsSheaf k Y p).obj.obj (op ⊤)) (b : (formsSheaf k Y q).obj.obj (op ⊤)) :
    formsSheafPullbackTop g (p + q) (formsSheafWedge k Y p q (op ⊤) a b) =
      formsSheafWedge k X p q (op ⊤)
        (formsSheafPullbackTop g p a) (formsSheafPullbackTop g q b) :=
  formsSheafPullback_wedge g p q (op ⊤) a b

/-- Global pullback commutes with the differential on the displayed carriers. -/
theorem formsSheafPullbackTop_d (g : X ⟶ Y) (n : ℕ)
    (a : (formsSheaf k Y n).obj.obj (op ⊤)) :
    (formsSheafD k X n).hom.app (op ⊤) (formsSheafPullbackTop g n a) =
      formsSheafPullbackTop g (n + 1) ((formsSheafD k Y n).hom.app (op ⊤) a) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun h => h.hom) (formsSheafPullback_d g n)) (op ⊤)) a

/-- Pullback preserves the degree-zero unit section on every open. -/
@[simp] theorem formsSheafPullback_one (g : X ⟶ Y) (U : Y.left.Opensᵒᵖ) :
    dsimp% (formsSheafPullback g 0).hom.app U (formsSheafOneSection k Y U) =
      formsSheafOneSection k X (op (g.left ⁻¹ᵁ U.unop)) := by
  change (formsSheafPullback g 0).hom.app U
      ((formsSheafUnit k Y 0).app U ((formsPresheafOne k Y).app U (1 : k))) = _
  rw [formsSheafPullback_unit_apply]
  change (formsSheafUnit k X 0).app (op (g.left ⁻¹ᵁ U.unop)) _ =
    (formsSheafUnit k X 0).app (op (g.left ⁻¹ᵁ U.unop)) _
  congr 1
  apply Subtype.ext
  change Forms.map (sectionPullback g U.unop) ((1 : k) • 1) = (1 : k) • 1
  simp only [one_smul, map_one]

/-- Pullback preserves the global unit on the displayed top-open carriers. -/
@[simp] theorem formsSheafPullbackTop_one (g : X ⟶ Y) :
    formsSheafPullbackTop g 0 (formsSheafOneSection k Y (op ⊤)) =
      formsSheafOneSection k X (op ⊤) :=
  formsSheafPullback_one g (op ⊤)

end OrlikSolomon.Geometric.DeRham
