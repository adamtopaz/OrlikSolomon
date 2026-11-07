/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Units

/-!
# Products with the affine line and the multiplicative group

This file proves `lem:geo-products` of the geometric refactor blueprint: for a `k`-algebra `A`,
`Spec A[z] ≅ Spec A ×_S 𝔸¹_S` and `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, compatibly with the first
projections, the sections `z = 0` and `z = 1`, the open immersion `𝔾ₘ → 𝔸¹` and naturality in `A`.
It also writes the standard pair in geometric form, `X → X ×_S 𝔸¹ ← X ×_S 𝔾ₘ`, for every `S`-scheme
`X`.

## Main definitions

* `Geometric.gmToAffineLine k`: the open immersion `𝔾ₘ → 𝔸¹_S`, the map of the function `z`.
* `Geometric.prodCoord X`: the coordinate `z` on `X ×_S 𝔸¹_S`.
* `Geometric.zeroSection X`, `Geometric.oneSection X`: the sections `z = 0` of `X ×_S 𝔸¹ → X` and
  `z = 1` of `X ×_S 𝔾ₘ → X`.
* `Geometric.specPolynomialIso A`, `Geometric.specLaurentIso A`: the isomorphisms
  `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` and `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ` of `S`-schemes.
* `SmoothDomain.specPolynomialIso`, `SmoothDomain.specLaurentIso`: the same isomorphisms in a
  domain.

## Main results

* `specPolynomialIso_hom_fst`, `specLaurentIso_hom_fst`: the inclusions of constants are the first
  projections.
* `specMap_polynomialLift_zero_comp_specPolynomialIso_hom`: evaluation at `0` is the zero section.
* `specMap_laurentSection_comp_specLaurentIso_hom`: evaluation at `1` is the section `z = 1`.
* `specMap_polynomialToLaurent_comp_specPolynomialIso_hom`: `A[z] → A[z, z⁻¹]` is the open
  immersion.
* `specPolynomialIso_hom_appTop_prodCoord`: the coordinate of `X ×_S 𝔸¹` is the variable of `A[z]`.

So `Spec` of the standard pair `(A[z], A, A[z, z⁻¹], z)` is the geometric standard pair of
`Spec A`. Nothing here needs smoothness, and `A = 0` is allowed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial MonObj

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### The standard pair in geometric form -/

variable (k) in
/-- The open immersion `𝔾ₘ → 𝔸¹_S`: the `S`-morphism of the function `z` on `𝔾ₘ`. -/
def gmToAffineLine : gm k ⟶ affineLine k := (homAffineLineEquiv _).symm (gmCoord k : _)

@[simp] lemma gmToAffineLine_appTop_affineLineCoord :
    (gmToAffineLine k).left.appTop (affineLineCoord k) = gmCoord k :=
  (homAffineLineEquiv _).apply_symm_apply _

section StandardPair

variable (X : Over (Spec (.of k)))

/-- The coordinate `z` on `X ×_S 𝔸¹_S`, the pullback of the coordinate of `𝔸¹_S`. It is the equation
of the zero section, the divisor of the geometric standard pair.

Blueprint: `lem:geo-products`. -/
def prodCoord : Γ((X ⊗ affineLine k).left, ⊤) := homAffineLineEquiv _ (snd X (affineLine k))

/-- The section `z = 0` of the projection `X ×_S 𝔸¹_S → X`, the closed immersion of the geometric
standard pair.

Blueprint: `lem:geo-products`. -/
def zeroSection : X ⟶ X ⊗ affineLine k := lift (𝟙 X) ((homAffineLineEquiv X).symm 0)

/-- The section `z = 1` of the projection `X ×_S 𝔾ₘ → X`.

Blueprint: `lem:geo-products`. -/
def oneSection : X ⟶ X ⊗ gm k := lift (𝟙 X) (unitsEquivHomGm X 1)

@[reassoc (attr := simp)] lemma zeroSection_fst : zeroSection X ≫ fst _ _ = 𝟙 X := lift_fst _ _

@[reassoc (attr := simp)] lemma oneSection_fst : oneSection X ≫ fst _ _ = 𝟙 X := lift_fst _ _

/-- The coordinate vanishes on the zero section. -/
lemma zeroSection_appTop_prodCoord : (zeroSection X).left.appTop (prodCoord X) = 0 := by
  rw [prodCoord, ← homAffineLineEquiv_comp, zeroSection, lift_snd, Equiv.apply_symm_apply]

/-- The open immersion `X ×_S 𝔾ₘ → X ×_S 𝔸¹_S` pulls the coordinate back to the coordinate unit. -/
lemma whiskerLeft_gmToAffineLine_appTop_prodCoord :
    (X ◁ gmToAffineLine k).left.appTop (prodCoord X) =
      (snd X (gm k)).left.appTop (gmCoord k) := by
  rw [prodCoord, ← homAffineLineEquiv_comp, whiskerLeft_snd, homAffineLineEquiv_comp,
    homAffineLineEquiv_apply, gmToAffineLine_appTop_affineLineCoord]

end StandardPair

section Spec

/-! ### `Spec A[z]` -/

variable (A : SmoothAlg.{u} k)

/-- The `k`-algebra map `A[z] → Γ(P, 𝒪)` for an `S`-morphism `P → Spec A ×_S 𝔸¹`. -/
def polynomialToGlobalSections {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ affineLine k) :
    (SmoothAlg.polynomial A).obj ⟶ globalSections P :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := (SmoothAlg.polynomial A).obj)
    (Y := globalSections P)
    (Polynomial.eval₂AlgHom (specHomEquiv P A.obj (g ≫ fst _ _)).hom
      (homAffineLineEquiv P (g ≫ snd _ _)) fun _ ↦ Commute.all _ _)

variable {A} in
/-- `k`-algebra maps out of `A[z]` agree when they agree on constants and on `z`. -/
lemma polynomial_commAlgCat_hom_ext {B : CommAlgCat.{u} k} {f g : (SmoothAlg.polynomial A).obj ⟶ B}
    (hC : ∀ a, f (SmoothAlg.polynomialC A a) = g (SmoothAlg.polynomialC A a))
    (hX : f (SmoothAlg.polynomialX A) = g (SmoothAlg.polynomialX A)) : f = g := by
  ext1
  exact Polynomial.algHom_ext' (AlgHom.ext hC) hX

lemma polynomialToGlobalSections_C {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ affineLine k)
    (a : A) :
    polynomialToGlobalSections A g (SmoothAlg.polynomialC A a) =
      specHomEquiv P A.obj (g ≫ fst _ _) a :=
  Polynomial.eval₂_C _ _

lemma polynomialToGlobalSections_X {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ affineLine k) :
    polynomialToGlobalSections A g (SmoothAlg.polynomialX A) =
      homAffineLineEquiv P (g ≫ snd _ _) :=
  Polynomial.eval₂_X _ _

lemma polynomialToGlobalSections_comp {P Q : Over (Spec (.of k))} (h : Q ⟶ P)
    (g : P ⟶ spec A.obj ⊗ affineLine k) :
    polynomialToGlobalSections A g ≫ globalSectionsMap h =
      polynomialToGlobalSections A (h ≫ g) := by
  apply polynomial_commAlgCat_hom_ext
  · intro a
    rw [CategoryTheory.comp_apply, polynomialToGlobalSections_C,
      polynomialToGlobalSections_C, Category.assoc, specHomEquiv_comp]
    rfl
  · rw [CategoryTheory.comp_apply, polynomialToGlobalSections_X,
      polynomialToGlobalSections_X, Category.assoc, homAffineLineEquiv_comp]
    rfl

/-- The variable `z` of `A[z]`, as a global function on `Spec A[z]`. -/
abbrev polynomialVar : Γ((spec (SmoothAlg.polynomial A).obj).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (SmoothAlg.polynomial A))).inv (SmoothAlg.polynomialX A)

/-- The isomorphism `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` of `S`-schemes. Its components are `Spec` of the
inclusion of constants and the map of the variable `z`.

Blueprint: `lem:geo-products`. -/
def specPolynomialIso : spec (SmoothAlg.polynomial A).obj ≅ spec A.obj ⊗ affineLine k where
  hom := lift (specMap (SmoothAlg.polynomialC A).hom)
    ((homAffineLineEquiv _).symm (polynomialVar A))
  inv := (specHomEquiv _ _).symm (polynomialToGlobalSections A (𝟙 _))
  hom_inv_id := by
    apply (specHomEquiv _ (SmoothAlg.polynomial A).obj).injective
    rw [specHomEquiv_comp, Equiv.apply_symm_apply, polynomialToGlobalSections_comp,
      Category.comp_id]
    apply polynomial_commAlgCat_hom_ext
    · intro a
      rw [polynomialToGlobalSections_C, lift_fst, ← Category.id_comp (specMap _),
        specHomEquiv_comp_specMap]
      rfl
    · rw [polynomialToGlobalSections_X, lift_snd, Equiv.apply_symm_apply]
      rfl
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (specHomEquiv _ A.obj).injective
      rw [Category.assoc, lift_fst, specHomEquiv_comp_specMap, Equiv.apply_symm_apply,
        Category.id_comp]
      ext a
      exact polynomialToGlobalSections_C A (𝟙 _) a
    · apply (homAffineLineEquiv _).injective
      rw [Category.assoc, lift_snd, homAffineLineEquiv_comp, Equiv.apply_symm_apply,
        Category.id_comp]
      change specHomEquiv _ _ ((specHomEquiv _ _).symm _) (SmoothAlg.polynomialX A) = _
      rw [Equiv.apply_symm_apply, polynomialToGlobalSections_X, Category.id_comp]

@[reassoc (attr := simp)]
lemma specPolynomialIso_hom_fst :
    (specPolynomialIso A).hom ≫ fst _ _ = specMap (SmoothAlg.polynomialC A).hom :=
  lift_fst _ _

lemma specPolynomialIso_hom_snd :
    (specPolynomialIso A).hom ≫ snd _ _ = (homAffineLineEquiv _).symm (polynomialVar A) :=
  lift_snd _ _

/-- The coordinate of `Spec A ×_S 𝔸¹_S` is the variable of `A[z]`. -/
lemma specPolynomialIso_hom_appTop_prodCoord :
    (specPolynomialIso A).hom.left.appTop (prodCoord _) = polynomialVar A := by
  rw [prodCoord, ← homAffineLineEquiv_comp, specPolynomialIso_hom_snd, Equiv.apply_symm_apply]

/-- Evaluation at `z = 0` is the zero section: `Spec` of the closed map of the standard pair of `A`.

Blueprint: `lem:geo-products`. -/
lemma specMap_polynomialLift_zero_comp_specPolynomialIso_hom :
    specMap (SmoothAlg.polynomialLift (𝟙 A) 0).hom ≫ (specPolynomialIso A).hom =
      zeroSection (spec A.obj) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, specPolynomialIso_hom_fst, ← specMap_comp, zeroSection_fst,
      ← ObjectProperty.FullSubcategory.comp_hom, SmoothAlg.polynomialC_comp_polynomialLift]
    exact specMap_id _
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, homAffineLineEquiv_comp, specPolynomialIso_hom_snd,
      Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv, zeroSection, lift_snd,
      Equiv.apply_symm_apply]
    exact (congrArg _ (SmoothAlg.polynomialLift_polynomialX _ _)).trans (map_zero _)

/-- Naturality of `specPolynomialIso` in `A`. -/
@[reassoc]
lemma specMap_polynomialMap_comp_specPolynomialIso_hom {B : SmoothAlg.{u} k} (φ : A ⟶ B) :
    specMap (SmoothAlg.polynomialLift (φ ≫ SmoothAlg.polynomialC B)
        (SmoothAlg.polynomialX B)).hom ≫ (specPolynomialIso A).hom =
      (specPolynomialIso B).hom ≫ (specMap φ.hom ▷ affineLine k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specPolynomialIso_hom_fst, whiskerRight_fst,
      specPolynomialIso_hom_fst_assoc, ← specMap_comp, ← specMap_comp,
      ← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      SmoothAlg.polynomialC_comp_polynomialLift]
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, Category.assoc, whiskerRight_snd, homAffineLineEquiv_comp,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply]
    exact congrArg _ (SmoothAlg.polynomialLift_polynomialX _ _)

/-! ### `Spec A[z, z⁻¹]` -/

/-- The `k`-algebra map `A[z, z⁻¹] → Γ(P, 𝒪)` for an `S`-morphism `P → Spec A ×_S 𝔾ₘ`. -/
def laurentToGlobalSections {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ gm k) :
    (SmoothAlg.laurent A).obj ⟶ globalSections P :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := (SmoothAlg.laurent A).obj)
    (Y := globalSections P)
    (laurentPolynomialLift (k := k) (R := A) (S := globalSections P)
      (specHomEquiv P A.obj (g ≫ fst _ _)).hom (homGmEquiv P (g ≫ snd _ _)))

variable {A} in
/-- `k`-algebra maps out of `A[z, z⁻¹]` agree when they agree on constants and on `z`. -/
lemma laurent_commAlgCat_hom_ext {B : CommAlgCat.{u} k} {f g : (SmoothAlg.laurent A).obj ⟶ B}
    (hC : ∀ a, f (SmoothAlg.laurentC A a) = g (SmoothAlg.laurentC A a))
    (hT : f (SmoothAlg.laurentT A : SmoothAlg.laurent A) =
      g (SmoothAlg.laurentT A : SmoothAlg.laurent A)) : f = g := by
  ext1
  exact laurentPolynomial_algHom_ext hC hT

lemma laurentToGlobalSections_C {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ gm k) (a : A) :
    laurentToGlobalSections A g (SmoothAlg.laurentC A a) = specHomEquiv P A.obj (g ≫ fst _ _) a :=
  laurentPolynomialLift_C _ _ _

lemma laurentToGlobalSections_T {P : Over (Spec (.of k))} (g : P ⟶ spec A.obj ⊗ gm k) :
    laurentToGlobalSections A g (SmoothAlg.laurentT A : SmoothAlg.laurent A) =
      (homGmEquiv P (g ≫ snd _ _) : Γ(P.left, ⊤)) :=
  laurentPolynomialLift_T _ _

lemma laurentToGlobalSections_comp {P Q : Over (Spec (.of k))} (h : Q ⟶ P)
    (g : P ⟶ spec A.obj ⊗ gm k) :
    laurentToGlobalSections A g ≫ globalSectionsMap h = laurentToGlobalSections A (h ≫ g) := by
  apply laurent_commAlgCat_hom_ext
  · intro a
    rw [CategoryTheory.comp_apply, laurentToGlobalSections_C, laurentToGlobalSections_C,
      Category.assoc, specHomEquiv_comp]
    rfl
  · rw [CategoryTheory.comp_apply, laurentToGlobalSections_T, laurentToGlobalSections_T,
      Category.assoc, homGmEquiv_comp]
    rfl

/-- The variable `z` of `A[z, z⁻¹]`, as a global unit on `Spec A[z, z⁻¹]`. -/
abbrev laurentVar : Γ((spec (SmoothAlg.laurent A).obj).left, ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (.of (SmoothAlg.laurent A))).inv.hom.toMonoidHom :
    SmoothAlg.laurent A →* Γ((spec (SmoothAlg.laurent A).obj).left, ⊤)) (SmoothAlg.laurentT A)

/-- The isomorphism `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ` of `S`-schemes. Its components are `Spec` of
the inclusion of constants and the map of the unit `z`.

Blueprint: `lem:geo-products`. -/
def specLaurentIso : spec (SmoothAlg.laurent A).obj ≅ spec A.obj ⊗ gm k where
  hom := lift (specMap (SmoothAlg.laurentC A).hom) (unitsEquivHomGm _ (laurentVar A))
  inv := (specHomEquiv _ _).symm (laurentToGlobalSections A (𝟙 _))
  hom_inv_id := by
    apply (specHomEquiv _ (SmoothAlg.laurent A).obj).injective
    rw [specHomEquiv_comp, Equiv.apply_symm_apply, laurentToGlobalSections_comp,
      Category.comp_id]
    apply laurent_commAlgCat_hom_ext
    · intro a
      rw [laurentToGlobalSections_C, lift_fst, ← Category.id_comp (specMap _),
        specHomEquiv_comp_specMap]
      rfl
    · rw [laurentToGlobalSections_T, lift_snd, ← unitsEquivHomGm_symm_apply,
        MulEquiv.symm_apply_apply]
      rfl
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (specHomEquiv _ A.obj).injective
      rw [Category.assoc, lift_fst, specHomEquiv_comp_specMap, Equiv.apply_symm_apply,
        Category.id_comp]
      ext a
      exact laurentToGlobalSections_C A (𝟙 _) a
    · apply hom_ext_gm
      rw [Category.assoc, lift_snd, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        unitsEquivHomGm_appTop_gmCoord, Category.id_comp]
      change specHomEquiv _ _ ((specHomEquiv _ _).symm _)
        (SmoothAlg.laurentT A : SmoothAlg.laurent A) = _
      rw [Equiv.apply_symm_apply, laurentToGlobalSections_T, Category.id_comp]
      rfl

@[reassoc (attr := simp)]
lemma specLaurentIso_hom_fst :
    (specLaurentIso A).hom ≫ fst _ _ = specMap (SmoothAlg.laurentC A).hom :=
  lift_fst _ _

lemma specLaurentIso_hom_snd :
    (specLaurentIso A).hom ≫ snd _ _ = unitsEquivHomGm _ (laurentVar A) :=
  lift_snd _ _

/-- The coordinate unit of `Spec A ×_S 𝔾ₘ` is the variable of `A[z, z⁻¹]`. -/
lemma specLaurentIso_hom_appTop_snd_gmCoord :
    (specLaurentIso A).hom.left.appTop ((snd (spec A.obj) (gm k)).left.appTop (gmCoord k)) =
      laurentVar A := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, specLaurentIso_hom_snd,
    unitsEquivHomGm_appTop_gmCoord]

/-- Evaluation at `z = 1` is the section `z = 1`.

Blueprint: `lem:geo-products`. -/
lemma specMap_laurentSection_comp_specLaurentIso_hom :
    specMap (SmoothAlg.laurentSection A).hom ≫ (specLaurentIso A).hom =
      oneSection (spec A.obj) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, specLaurentIso_hom_fst, ← specMap_comp, oneSection_fst,
      ← ObjectProperty.FullSubcategory.comp_hom, SmoothAlg.laurentC_comp_laurentSection]
    exact specMap_id _
  · apply hom_ext_gm
    rw [Category.assoc, specLaurentIso_hom_snd, oneSection, lift_snd, Over.comp_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, unitsEquivHomGm_appTop_gmCoord,
      unitsEquivHomGm_appTop_gmCoord, Units.coe_map, Units.val_one]
    change (specMap _).left.appTop ((Scheme.ΓSpecIso _).inv _) = 1
    rw [specMap_left_appTop_ΓSpecIso_inv]
    exact (congrArg _ (SmoothAlg.laurentLift_laurentT _ _)).trans (map_one _)

/-- The inclusion `A[z] → A[z, z⁻¹]` is the open immersion `Spec A ×_S 𝔾ₘ → Spec A ×_S 𝔸¹`:
`Spec` of the open map of the standard pair of `A`.

Blueprint: `lem:geo-products`. -/
@[reassoc]
lemma specMap_polynomialToLaurent_comp_specPolynomialIso_hom :
    specMap (SmoothAlg.polynomialToLaurent A).hom ≫ (specPolynomialIso A).hom =
      (specLaurentIso A).hom ≫ (spec A.obj ◁ gmToAffineLine k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specPolynomialIso_hom_fst, whiskerLeft_fst,
      specLaurentIso_hom_fst, ← specMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      SmoothAlg.polynomialC_comp_polynomialToLaurent]
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, Category.assoc, whiskerLeft_snd, homAffineLineEquiv_comp,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv,
      ← Category.assoc, homAffineLineEquiv_comp, gmToAffineLine, Equiv.apply_symm_apply,
      specLaurentIso_hom_snd, unitsEquivHomGm_appTop_gmCoord]
    exact congrArg _ (SmoothAlg.polynomialToLaurent_polynomialX A)

/-- Naturality of `specLaurentIso` in `A`. -/
@[reassoc]
lemma specMap_laurentMap_comp_specLaurentIso_hom {B : SmoothAlg.{u} k} (φ : A ⟶ B) :
    specMap (SmoothAlg.laurentLift (φ ≫ SmoothAlg.laurentC B) (SmoothAlg.laurentT B)).hom ≫
        (specLaurentIso A).hom =
      (specLaurentIso B).hom ≫ (specMap φ.hom ▷ gm k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specLaurentIso_hom_fst, whiskerRight_fst,
      specLaurentIso_hom_fst_assoc, ← specMap_comp, ← specMap_comp,
      ← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      SmoothAlg.laurentC_comp_laurentLift]
  · apply hom_ext_gm
    rw [Category.assoc, Category.assoc, whiskerRight_snd, specLaurentIso_hom_snd,
      specLaurentIso_hom_snd, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      unitsEquivHomGm_appTop_gmCoord, unitsEquivHomGm_appTop_gmCoord]
    change (specMap _).left.appTop ((Scheme.ΓSpecIso _).inv _) = _
    rw [specMap_left_appTop_ΓSpecIso_inv]
    exact congrArg _ (SmoothAlg.laurentLift_laurentT _ _)

end Spec

/-! ### In a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k) (A : SmoothAlg.{u} k)

/-- `Spec A[z] ≅ Spec A ×_S 𝔸¹_S`, in a domain `D`.

Blueprint: `lem:geo-products`. -/
def specPolynomialIso : D.spec (SmoothAlg.polynomial A) ≅ D.prodAffineLine (D.spec A) :=
  ObjectProperty.isoMk _ (Geometric.specPolynomialIso A)

/-- `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, in a domain `D`.

Blueprint: `lem:geo-products`. -/
def specLaurentIso : D.spec (SmoothAlg.laurent A) ≅ D.prodGm (D.spec A) :=
  ObjectProperty.isoMk _ (Geometric.specLaurentIso A)

@[simp] lemma specPolynomialIso_hom_hom :
    (D.specPolynomialIso A).hom.hom = (Geometric.specPolynomialIso A).hom := rfl

@[simp] lemma specLaurentIso_hom_hom :
    (D.specLaurentIso A).hom.hom = (Geometric.specLaurentIso A).hom := rfl

/-- Under `Spec A[z] ≅ Spec A ×_S 𝔸¹_S`, the projection is `Spec` of the inclusion of constants:
the polynomial axiom of an algebraic theory is the affine-line axiom of a geometric one. -/
@[reassoc (attr := simp)]
lemma specPolynomialIso_hom_prodAffineLineFst :
    (D.specPolynomialIso A).hom ≫ D.prodAffineLineFst (D.spec A) =
      (D.specFunctor.map (SmoothAlg.polynomialC A)).unop :=
  ObjectProperty.hom_ext _ (Geometric.specPolynomialIso_hom_fst A)

/-- Under `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, the projection is `Spec` of the inclusion of
constants. -/
@[reassoc (attr := simp)]
lemma specLaurentIso_hom_prodGmFst :
    (D.specLaurentIso A).hom ≫ D.prodGmFst (D.spec A) =
      (D.specFunctor.map (SmoothAlg.laurentC A)).unop :=
  ObjectProperty.hom_ext _ (Geometric.specLaurentIso_hom_fst A)

end SmoothDomain

end OrlikSolomon.Geometric
