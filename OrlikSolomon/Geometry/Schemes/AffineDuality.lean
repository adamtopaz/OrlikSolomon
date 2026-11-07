/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Basic

/-!
# Affine duality over the base

This file proves `thm:geo-affine-duality` of the geometric refactor blueprint: `Spec` and global
sections are inverse equivalences between smooth `k`-algebras and smooth affine `S`-schemes, with
`S = Spec k`, for any commutative ring `k`.

## Main definitions

* `Geometric.specHomEquiv X A`: for **every** `S`-scheme `X` and `k`-algebra `A`, the bijection
  between `S`-morphisms `X ⟶ Spec A` and `k`-algebra maps `A ⟶ Γ(X, 𝒪_X)`. This is the
  `Γ`-`Spec` adjunction over `S`.
* `Geometric.affineHomEquiv X Y`: for affine `Y`, pullback of global sections
  `(X ⟶ Y) ≃ (Γ(Y) ⟶ Γ(X))`.
* `Geometric.globalSectionsSpecIso A`: the isomorphism `η_A : Γ(Spec A, 𝒪) ≅ A`, from `ΓSpecIso`.
* `Geometric.specGlobalSectionsIso X`: the isomorphism `ε_X : Spec Γ(X, 𝒪_X) ≅ X` of `S`-schemes,
  for affine `X`, from `Scheme.isoSpec`.
* `Geometric.affineGlobalSectionsFunctor k`: global sections `(Sm_k^aff)ᵒᵖ ⥤ SmoothAlg k`.
* `Geometric.smoothAffineEquivalence k`: the equivalence `SmoothAlg k ≌ (Sm_k^aff)ᵒᵖ`, with functor
  `(SmoothDomain.aff k).specFunctor`, unit `η⁻¹` and counit `ε`.

## Main results

* `smooth_hom_iff`: an affine `S`-scheme is smooth exactly when its ring of global sections is a
  smooth `k`-algebra.
* `globalSectionsSpecIso_naturality`, `specGlobalSectionsIso_naturality`: naturality of `η` and
  `ε`.
* `specGlobalSectionsIso_hom_spec`, `globalSectionsMap_specGlobalSectionsIso_hom`: the triangle
  identities.

The empty scheme `Spec 0` is included throughout, and no nontriviality, separatedness or choice of
coordinates is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### The adjunction over `S` -/

/-- Two morphisms into `Spec R` agree when they induce the same map `R → Γ(X, ⊤)`. This is
Mathlib's `ext_to_Spec`, stated with `appTop`. -/
lemma ext_to_Spec' {Y : Scheme.{u}} {R : CommRingCat.{u}} {f g : Y ⟶ Spec R}
    (h : (Scheme.ΓSpecIso R).inv ≫ f.appTop = (Scheme.ΓSpecIso R).inv ≫ g.appTop) : f = g :=
  ext_to_Spec (R := R) h

section HomEquiv

variable (X : Over (Spec (.of k))) (A : CommAlgCat.{u} k)

/-- The map `A → Γ(X, 𝒪_X)` of an `S`-morphism `g : X ⟶ Spec A`, the isomorphism
`A ≅ Γ(Spec A, 𝒪)` followed by pullback along `g`, is a map of `k`-algebras. -/
lemma specHomEquiv_commutes (g : X ⟶ spec A) (c : k) :
    g.left.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap k A c)) =
      algebraMap k (globalSections X) c := by
  rw [algebraMap_globalSections, ← Over.w g, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 1
  exact (CommRingCat.comp_apply _ _ _).symm.trans
    (congrArg (fun f ↦ f c) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap k A))))

/-- The ring map `A → Γ(X.left, ⊤)` underlying a `k`-algebra map `A ⟶ Γ(X, 𝒪_X)`. -/
abbrev toΓ (φ : A ⟶ globalSections X) : CommRingCat.of A ⟶ Γ(X.left, ⊤) :=
  ConcreteCategory.ofHom (C := CommRingCat) (X := .of A) (Y := Γ(X.left, ⊤)) φ.hom.toRingHom

lemma ΓSpecIso_inv_toSpecΓ_Spec_map_appTop {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (ψ : R ⟶ Γ(Y, ⊤)) : (Scheme.ΓSpecIso R).inv ≫ (Y.toSpecΓ ≫ Spec.map ψ).appTop = ψ := by
  simp

lemma specHomEquiv_symm_aux (φ : A ⟶ globalSections X) :
    (X.left.toSpecΓ ≫ Spec.map (toΓ X A φ)) ≫ (spec A).hom = X.hom := by
  apply ext_to_Spec'
  rw [Category.assoc, spec_hom, ← Spec.map_comp, ΓSpecIso_inv_toSpecΓ_Spec_map_appTop]
  ext c
  exact φ.hom.commutes c

/-- For every `S`-scheme `X` and `k`-algebra `A`, the `S`-morphisms `X ⟶ Spec A` correspond to the
`k`-algebra maps `A ⟶ Γ(X, 𝒪_X)`. This is the `Γ`-`Spec` adjunction relative to `S`; it needs no
affineness of `X`.

Blueprint: `thm:geo-affine-duality`, used for `thm:geo-units`. -/
def specHomEquiv : (X ⟶ spec A) ≃ (A ⟶ globalSections X) where
  toFun g := ConcreteCategory.ofHom (C := CommAlgCat k)
    (({ toRingHom := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.left.appTop).hom
        commutes' := specHomEquiv_commutes X A g } : A →ₐ[k] globalSections X))
  invFun φ := Over.homMk _ (specHomEquiv_symm_aux X A φ)
  left_inv g := by
    ext1
    exact ext_to_Spec' (ΓSpecIso_inv_toSpecΓ_Spec_map_appTop _)
  right_inv φ := by
    ext a
    exact congrArg (fun f ↦ f a) (ΓSpecIso_inv_toSpecΓ_Spec_map_appTop (toΓ X A φ))

@[simp] lemma specHomEquiv_symm_left (φ : A ⟶ globalSections X) :
    ((specHomEquiv X A).symm φ).left = X.left.toSpecΓ ≫ Spec.map (toΓ X A φ) := rfl

variable {X A}

@[simp] lemma specHomEquiv_apply_apply (g : X ⟶ spec A) (a : A) :
    specHomEquiv X A g a = g.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) := rfl

/-- Two `S`-morphisms into `Spec A` agree when they pull back each element of `A` to the same
global section. -/
lemma hom_ext_spec {f g : X ⟶ spec A}
    (h : ∀ a : A, f.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      g.left.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) : f = g :=
  (specHomEquiv X A).injective (by ext a; exact h a)

/-- Naturality of `specHomEquiv` in the scheme. -/
lemma specHomEquiv_comp {X' : Over (Spec (.of k))} (f : X' ⟶ X)
    (g : X ⟶ spec A) :
    specHomEquiv X' A (f ≫ g) = specHomEquiv X A g ≫ globalSectionsMap f := rfl

/-- Pullback along `Spec φ` of the function of `a` is the function of `φ a`. -/
lemma specMap_left_appTop_ΓSpecIso_inv {B : CommAlgCat.{u} k} (φ : B ⟶ A) (b : B) :
    (specMap φ).left.appTop ((Scheme.ΓSpecIso (.of B)).inv b) =
      (Scheme.ΓSpecIso (.of A)).inv (φ b) :=
  (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.hom.toRingHom)) b).symm

/-- Naturality of `specHomEquiv` in the algebra. -/
lemma specHomEquiv_comp_specMap {B : CommAlgCat.{u} k} (ψ : B ⟶ A) (g : X ⟶ spec A) :
    specHomEquiv X B (g ≫ specMap ψ) = ψ ≫ specHomEquiv X A g := by
  ext b
  rw [specHomEquiv_apply_apply, CommAlgCat.hom_comp, AlgHom.comp_apply, specHomEquiv_apply_apply,
    Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    specMap_left_appTop_ΓSpecIso_inv]

lemma specHomEquiv_symm_comp {X' : Over (Spec (.of k))} (f : X' ⟶ X) (φ : A ⟶ globalSections X) :
    (specHomEquiv X' A).symm (φ ≫ globalSectionsMap f) = f ≫ (specHomEquiv X A).symm φ := by
  rw [Equiv.symm_apply_eq, specHomEquiv_comp, Equiv.apply_symm_apply]

end HomEquiv

/-! ### The unit and counit -/

section UnitCounit

/-- The isomorphism `η_A⁻¹ : Γ(Spec A, 𝒪) ≅ A` of `k`-algebras, from Mathlib's `ΓSpecIso`.

Blueprint: `thm:geo-affine-duality`. -/
def globalSectionsSpecIso (A : CommAlgCat.{u} k) : globalSections (spec A) ≅ A :=
  let e : A ≃ₐ[k] globalSections (spec A) :=
    { toRingEquiv := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
      commutes' c := specHomEquiv_commutes _ A (𝟙 _) c }
  { hom := ConcreteCategory.ofHom (C := CommAlgCat k) (e.symm : _ →ₐ[k] A)
    inv := ConcreteCategory.ofHom (C := CommAlgCat k) (e : A →ₐ[k] _)
    hom_inv_id := by ext x; exact e.apply_symm_apply x
    inv_hom_id := by ext x; exact e.symm_apply_apply x }

variable {A B : CommAlgCat.{u} k}

@[simp] lemma globalSectionsSpecIso_hom_apply (x : globalSections (spec A)) :
    (globalSectionsSpecIso A).hom x = (Scheme.ΓSpecIso (.of A)).hom x := rfl

@[simp] lemma globalSectionsSpecIso_inv_apply (a : A) :
    (globalSectionsSpecIso A).inv a = (Scheme.ΓSpecIso (.of A)).inv a := rfl

/-- `η_A` is the adjunct of the identity of `Spec A`. -/
lemma globalSectionsSpecIso_inv : (globalSectionsSpecIso A).inv = specHomEquiv _ A (𝟙 _) := rfl

/-- Naturality of `η`. -/
@[reassoc]
lemma globalSectionsSpecIso_inv_naturality (φ : A ⟶ B) :
    φ ≫ (globalSectionsSpecIso B).inv =
      (globalSectionsSpecIso A).inv ≫ globalSectionsMap (specMap φ) := by
  rw [globalSectionsSpecIso_inv, globalSectionsSpecIso_inv, ← specHomEquiv_comp,
    ← specHomEquiv_comp_specMap, Category.id_comp, Category.comp_id]

/-- Naturality of `η`. -/
@[reassoc]
lemma globalSectionsSpecIso_naturality (φ : A ⟶ B) :
    globalSectionsMap (specMap φ) ≫ (globalSectionsSpecIso B).hom =
      (globalSectionsSpecIso A).hom ≫ φ := by
  rw [← cancel_epi (globalSectionsSpecIso A).inv, Iso.inv_hom_id_assoc,
    ← globalSectionsSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

variable (X : Over (Spec (.of k))) [IsAffine X.left]

/-- Pullback along `X.isoSpec.inv` is the inverse of `ΓSpecIso`. -/
lemma isoSpec_inv_appTop (Y : Scheme.{u}) [IsAffine Y] :
    Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ, Scheme.Hom.id_appTop]

lemma specGlobalSectionsIso_w :
    X.left.isoSpec.inv ≫ X.hom = (spec (globalSections X)).hom := by
  rw [Iso.inv_comp_eq, spec_hom]
  change X.hom = X.left.toSpecΓ ≫ _
  have : CommRingCat.ofHom (algebraMap k (globalSections X)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop := rfl
  rw [this, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The isomorphism `ε_X : Spec Γ(X, 𝒪_X) ≅ X` of `S`-schemes, for affine `X`, from Mathlib's
`Scheme.isoSpec`.

Blueprint: `thm:geo-affine-duality`. -/
def specGlobalSectionsIso : spec (globalSections X) ≅ X :=
  Over.isoMk X.left.isoSpec.symm (specGlobalSectionsIso_w X)

@[simp] lemma specGlobalSectionsIso_hom_left :
    (specGlobalSectionsIso X).hom.left = X.left.isoSpec.inv := rfl

@[simp] lemma specGlobalSectionsIso_inv_left :
    (specGlobalSectionsIso X).inv.left = X.left.isoSpec.hom := rfl

/-- `ε_X⁻¹ : X → Spec Γ(X, 𝒪_X)` is the adjunct of the identity of `Γ(X, 𝒪_X)`. -/
lemma specHomEquiv_symm_id :
    (specHomEquiv X (globalSections X)).symm (𝟙 _) = (specGlobalSectionsIso X).inv := by
  ext1
  rw [specHomEquiv_symm_left, specGlobalSectionsIso_inv_left]
  change _ = X.left.toSpecΓ
  exact (congrArg (X.left.toSpecΓ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

lemma specHomEquiv_specGlobalSectionsIso_inv :
    specHomEquiv X (globalSections X) (specGlobalSectionsIso X).inv = 𝟙 _ := by
  rw [← specHomEquiv_symm_id, Equiv.apply_symm_apply]

variable {X} {Y : Over (Spec (.of k))} [IsAffine Y.left]

/-- Naturality of `ε`. -/
@[reassoc]
lemma specGlobalSectionsIso_inv_naturality (f : X ⟶ Y) :
    f ≫ (specGlobalSectionsIso Y).inv =
      (specGlobalSectionsIso X).inv ≫ specMap (globalSectionsMap f) := by
  ext1
  exact (Scheme.isoSpec_hom_naturality f.left).symm

/-- Naturality of `ε`. -/
@[reassoc]
lemma specGlobalSectionsIso_naturality (f : X ⟶ Y) :
    specMap (globalSectionsMap f) ≫ (specGlobalSectionsIso Y).hom =
      (specGlobalSectionsIso X).hom ≫ f := by
  rw [← cancel_epi (specGlobalSectionsIso X).inv, Iso.inv_hom_id_assoc,
    ← specGlobalSectionsIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The first triangle identity: `ε_{Spec A}` is `Spec` of `η_A`. -/
lemma specGlobalSectionsIso_hom_spec (A : CommAlgCat.{u} k) :
    (specGlobalSectionsIso (spec A)).hom = specMap (globalSectionsSpecIso A).inv := by
  ext1
  exact Scheme.isoSpec_Spec_inv _

/-- The second triangle identity: pulling back along `ε_X` is `η_{Γ(X)}`. -/
lemma globalSectionsMap_specGlobalSectionsIso_hom :
    globalSectionsMap (specGlobalSectionsIso X).hom =
      (globalSectionsSpecIso (globalSections X)).inv := by
  ext x
  exact congrArg (fun f ↦ f x) (isoSpec_inv_appTop X.left)

end UnitCounit

/-! ### Smoothness -/

/-- An affine `S`-scheme is smooth over `S` exactly when its global sections form a smooth
`k`-algebra.

Blueprint: `thm:geo-affine-duality`. -/
lemma smooth_hom_iff (X : Over (Spec (.of k))) [IsAffine X.left] :
    Smooth X.hom ↔ Algebra.Smooth k (globalSections X) := by
  rw [← smooth_spec_hom_iff]
  constructor <;> intro
  · rw [← Over.w (specGlobalSectionsIso X).hom]
    infer_instance
  · rw [← Over.w (specGlobalSectionsIso X).inv]
    infer_instance

instance (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom] :
    Algebra.Smooth k (globalSections X) :=
  (smooth_hom_iff X).1 ‹_›

/-! ### Morphisms into affine schemes -/

/-- For affine `Y`, the `S`-morphisms `X ⟶ Y` correspond to the `k`-algebra maps
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`, by pullback of global sections (`affineHomEquiv_apply`). The scheme `X`
need not be affine.

Blueprint: `thm:geo-affine-duality`. -/
def affineHomEquiv (X Y : Over (Spec (.of k))) [IsAffine Y.left] :
    (X ⟶ Y) ≃ (globalSections Y ⟶ globalSections X) :=
  ((specGlobalSectionsIso Y).homToEquiv).symm.trans (specHomEquiv X (globalSections Y))

@[simp] lemma affineHomEquiv_apply {X Y : Over (Spec (.of k))} [IsAffine Y.left] (f : X ⟶ Y) :
    affineHomEquiv X Y f = globalSectionsMap f := by
  change specHomEquiv X _ (f ≫ (specGlobalSectionsIso Y).inv) = _
  rw [specHomEquiv_comp, specHomEquiv_specGlobalSectionsIso_inv, Category.id_comp]

/-! ### The equivalence -/

variable (k)

/-- Global sections, as a functor from smooth affine `S`-schemes to smooth `k`-algebras. -/
@[simps, implicit_reducible]
def affineGlobalSectionsFunctor : (SmoothDomain.aff k).Objᵒᵖ ⥤ SmoothAlg.{u} k where
  obj X := ⟨globalSections X.unop.obj, inferInstance⟩
  map g := ObjectProperty.homMk (globalSectionsMap g.unop.hom)

/-- The unit `η⁻¹ : A ≅ Γ(Spec A, 𝒪)` of smooth affine duality, as a natural isomorphism. -/
def smoothAffineUnitIso :
    𝟭 (SmoothAlg.{u} k) ≅ (SmoothDomain.aff k).specFunctor ⋙ affineGlobalSectionsFunctor k :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (globalSectionsSpecIso A.obj).symm)
    fun φ ↦ ObjectProperty.hom_ext _ (globalSectionsSpecIso_inv_naturality φ.hom)

@[simp] lemma smoothAffineUnitIso_hom_app_hom (A : SmoothAlg.{u} k) :
    ((smoothAffineUnitIso k).hom.app A).hom = (globalSectionsSpecIso A.obj).inv := rfl

@[simp] lemma smoothAffineUnitIso_inv_app_hom (A : SmoothAlg.{u} k) :
    ((smoothAffineUnitIso k).inv.app A).hom = (globalSectionsSpecIso A.obj).hom := rfl

/-- The counit `ε : Spec Γ(X, 𝒪_X) ≅ X` of smooth affine duality, as a natural isomorphism. -/
def smoothAffineCounitIso :
    affineGlobalSectionsFunctor k ⋙ (SmoothDomain.aff k).specFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ (ObjectProperty.isoMk _ (specGlobalSectionsIso X.unop.obj)).symm.op)
    fun g ↦ by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      dsimp
      simp only [Iso.op_inv, Quiver.Hom.unop_op, ObjectProperty.isoMk_inv,
        ObjectProperty.homMk_hom]
      exact (specGlobalSectionsIso_inv_naturality g.unop.hom).symm

@[simp] lemma smoothAffineCounitIso_hom_app_unop_hom (X : (SmoothDomain.aff k).Objᵒᵖ) :
    ((smoothAffineCounitIso k).hom.app X).unop.hom = (specGlobalSectionsIso X.unop.obj).inv := rfl

@[simp] lemma smoothAffineCounitIso_inv_app_unop_hom (X : (SmoothDomain.aff k).Objᵒᵖ) :
    ((smoothAffineCounitIso k).inv.app X).unop.hom = (specGlobalSectionsIso X.unop.obj).hom := rfl

variable {k} in
/-- The triangle identity of smooth affine duality, in the form needed for the equivalence. -/
lemma specGlobalSectionsIso_inv_comp_specMap (A : CommAlgCat.{u} k) :
    (specGlobalSectionsIso (spec A)).inv ≫ specMap (globalSectionsSpecIso A).inv = 𝟙 _ := by
  rw [← specGlobalSectionsIso_hom_spec, Iso.inv_hom_id]

/-- Smooth affine duality over `S = Spec k`: `A ↦ Spec A` and `X ↦ Γ(X, 𝒪_X)` are inverse
equivalences `SmoothAlg k ≌ (Sm_k^aff)ᵒᵖ`. The unit is `η⁻¹` (`globalSectionsSpecIso`) and the
counit is `ε` (`specGlobalSectionsIso`); naturality and the triangle identities are
`globalSectionsSpecIso_naturality`, `specGlobalSectionsIso_naturality`,
`specGlobalSectionsIso_hom_spec` and `globalSectionsMap_specGlobalSectionsIso_hom`.

Blueprint: `thm:geo-affine-duality`. -/
def smoothAffineEquivalence : SmoothAlg.{u} k ≌ (SmoothDomain.aff k).Objᵒᵖ where
  functor := (SmoothDomain.aff k).specFunctor
  inverse := affineGlobalSectionsFunctor k
  unitIso := smoothAffineUnitIso k
  counitIso := smoothAffineCounitIso k
  functor_unitIso_comp A := Quiver.Hom.unop_inj (ObjectProperty.hom_ext _
    (specGlobalSectionsIso_inv_comp_specMap A.obj))

@[simp] lemma smoothAffineEquivalence_functor :
    (smoothAffineEquivalence k).functor = (SmoothDomain.aff k).specFunctor := rfl

@[simp] lemma smoothAffineEquivalence_inverse :
    (smoothAffineEquivalence k).inverse = affineGlobalSectionsFunctor k := rfl

@[simp] lemma smoothAffineEquivalence_unitIso :
    (smoothAffineEquivalence k).unitIso = smoothAffineUnitIso k := rfl

@[simp] lemma smoothAffineEquivalence_counitIso :
    (smoothAffineEquivalence k).counitIso = smoothAffineCounitIso k := rfl

end OrlikSolomon.Geometric
