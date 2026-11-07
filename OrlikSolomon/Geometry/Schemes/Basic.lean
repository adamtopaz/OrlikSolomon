/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import OrlikSolomon.Geometry.SmoothAlg

/-!
# Smooth schemes over a base and admissible domains

This file starts the geometric layer of the library: schemes over `S = Spec k` for a commutative
ring `k`, with no hypothesis on `k`. It realizes `def:geo-domain` of the geometric refactor
blueprint.

## Main definitions

* `Geometric.globalSections X`: the `k`-algebra `Γ(X, 𝒪_X)` of an `S`-scheme `X`, with its
  structure map `k → Γ(S, 𝒪_S) → Γ(X, 𝒪_X)`, and its contravariant functoriality
  `globalSectionsMap`.
* `Geometric.affineLine k` and `Geometric.gm k`: the `S`-schemes `𝔸¹_S = Spec k[z]` and
  `𝔾ₘ = Spec k[z, z⁻¹]`. The latter is a commutative group object, by Mathlib's Hopf algebra
  structure on Laurent polynomials.
* `Geometric.SmoothDomain k`: an admissible domain, a full isomorphism-closed subcategory of smooth
  `S`-schemes that contains every smooth affine `S`-scheme and is closed under `X ↦ X ×_S 𝔸¹` and
  `X ↦ X ×_S 𝔾ₘ`. Its category of objects is `D.Obj`, and its morphisms are all `S`-morphisms.
* `SmoothDomain.all k`, `SmoothDomain.aff k`, `SmoothDomain.sft k`: the domains of all smooth
  `S`-schemes, of smooth affine ones, and of smooth separated ones of finite type.
* `SmoothDomain.ofAffine`, `SmoothDomain.spec`: smooth affine schemes as objects of any domain,
  with membership found by instances.
* `SmoothDomain.point`, `SmoothDomain.prodAffineLine`, `SmoothDomain.prodGm`: the base `S` and the
  products `X ×_S 𝔸¹` and `X ×_S 𝔾ₘ`, with their first projections.

## Implementation notes

`S`-schemes are objects of `Over (Spec (.of k))`, products are its cartesian monoidal product `⊗`,
which is `Limits.pullback`, and `Spec` of a `k`-algebra is `spec`, which is Mathlib's `algSpec`
(`specFunctor_eq_algSpec`).

The `k`-algebra structure of `Γ(X, 𝒪_X)` is bundled in `globalSections X` and is not an instance on
`Γ(X.left, ⊤)`. Mathlib has an instance for affine `X` built differently, through `X.isoSpec`; the
two agree only propositionally, so a second instance would be a diamond.

Named objects and object-valued functors, such as `spec`, `globalSections`, `affineLine`, `gm` and
`SmoothDomain.spec`, are `@[implicit_reducible] def`s. Lean compares the objects of a morphism,
which are implicit arguments, at implicit transparency, so `(spec A).left` must unfold to `Spec A`
there for `rw` and `simp` to work under a composite such as `g ≫ (spec A).hom`. They are not
`abbrev`s, since `simp` indexes lemmas at reducible transparency, where they stay folded, as
`Geometry/SmoothAlg` explains. Mathlib's `algSpec` does not unfold at implicit transparency, which
is why `spec` restates it. For the same reason, equations between objects, such as `spec_left`, are
not `simp` lemmas: `simp` would rewrite inside the types of morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### `Spec` of a `k`-algebra -/

/-- `Spec A`, for a `k`-algebra `A`, as a scheme over `S = Spec k`. It is Mathlib's `algSpec`
(`specFunctor_eq_algSpec`), stated so that its components unfold at implicit transparency. -/
@[implicit_reducible]
def spec (A : CommAlgCat.{u} k) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

lemma spec_left (A : CommAlgCat.{u} k) : (spec A).left = Spec (.of A) := rfl

lemma spec_hom (A : CommAlgCat.{u} k) :
    (spec A).hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) := rfl

lemma specMap_w {A B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ (spec A).hom = (spec B).hom := by
  rw [spec_hom, spec_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.hom.comp_algebraMap

/-- `Spec` of a map of `k`-algebras, as an `S`-morphism. -/
def specMap {A B : CommAlgCat.{u} k} (φ : A ⟶ B) : spec B ⟶ spec A :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)) (specMap_w φ)

@[simp] lemma specMap_left {A B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    (specMap φ).left = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) := rfl

@[simp] lemma specMap_id (A : CommAlgCat.{u} k) : specMap (𝟙 A) = 𝟙 (spec A) := by
  ext1
  exact Spec.map_id _

@[simp, reassoc] lemma specMap_comp {A B C : CommAlgCat.{u} k} (φ : A ⟶ B) (ψ : B ⟶ C) :
    specMap (φ ≫ ψ) = specMap ψ ≫ specMap φ := by
  ext1
  exact Spec.map_comp (CommRingCat.ofHom φ.hom.toRingHom) (CommRingCat.ofHom ψ.hom.toRingHom)

variable (k) in
/-- `Spec`, as a functor from `k`-algebras to the opposite of `S`-schemes. -/
@[simps, implicit_reducible]
def specFunctor : (CommAlgCat.{u} k)ᵒᵖ ⥤ Over (Spec (.of k)) where
  obj A := spec A.unop
  map φ := specMap φ.unop

variable (k) in
/-- `specFunctor` is Mathlib's `algSpec`. -/
lemma specFunctor_eq_algSpec : specFunctor k = algSpec (.of k) := rfl

variable (k) in
/-- `Spec` is fully faithful on `k`-algebras. -/
def specFunctorFullyFaithful : (specFunctor k).FullyFaithful := algSpec.fullyFaithful (R := .of k)

instance : (specFunctor k).Full := (specFunctorFullyFaithful k).full
instance : (specFunctor k).Faithful := (specFunctorFullyFaithful k).faithful

instance (A : CommAlgCat.{u} k) : IsAffine (spec A).left := inferInstanceAs (IsAffine (Spec _))

/-- `Spec A → Spec k` is smooth exactly when `A` is a smooth `k`-algebra. -/
lemma smooth_spec_hom_iff (A : CommAlgCat.{u} k) : Smooth (spec A).hom ↔ Algebra.Smooth k A := by
  rw [spec_hom, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap

instance smooth_spec_hom (A : CommAlgCat.{u} k) [Algebra.Smooth k A] : Smooth (spec A).hom :=
  (smooth_spec_hom_iff A).2 ‹_›

/-! ### Global sections as a `k`-algebra -/

variable (X : Over (Spec (.of k)))

/-- The structure map `k → Γ(X, 𝒪_X)` of an `S`-scheme: `k ≅ Γ(S, 𝒪_S)`, followed by pullback along
the structure morphism. -/
def structureRingHom : k →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The `k`-algebra `Γ(X, 𝒪_X)` of global sections of a scheme over `Spec k`. Its underlying ring
is `Γ(X.left, ⊤)`, and its structure map is `structureRingHom X`.

Blueprint: `thm:geo-affine-duality`. -/
@[implicit_reducible]
def globalSections : CommAlgCat.{u} k :=
  letI : Algebra k Γ(X.left, ⊤) := (structureRingHom X).toAlgebra
  CommAlgCat.of k Γ(X.left, ⊤)

lemma algebraMap_globalSections (c : k) :
    algebraMap k (globalSections X) c = X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c) := rfl

variable {X} {Y Z : Over (Spec (.of k))}

/-- Pullback of global sections along an `S`-morphism is a `k`-algebra map. -/
lemma globalSections_commutes (g : X ⟶ Y) (c : k) :
    g.left.appTop (algebraMap k (globalSections Y) c) = algebraMap k (globalSections X) c := by
  simp only [algebraMap_globalSections, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Over.w g]

/-- The pullback `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` along an `S`-morphism `g : X ⟶ Y`, as a map of
`k`-algebras. -/
def globalSectionsMap (g : X ⟶ Y) : globalSections Y ⟶ globalSections X :=
  ConcreteCategory.ofHom (C := CommAlgCat k)
    (({ toRingHom := g.left.appTop.hom
        commutes' := globalSections_commutes g } : globalSections Y →ₐ[k] globalSections X))

@[simp] lemma globalSectionsMap_apply (g : X ⟶ Y) (x : globalSections Y) :
    globalSectionsMap g x = g.left.appTop x := rfl

@[simp] lemma globalSectionsMap_id : globalSectionsMap (𝟙 X) = 𝟙 _ := rfl

@[simp, reassoc] lemma globalSectionsMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    globalSectionsMap (f ≫ g) = globalSectionsMap g ≫ globalSectionsMap f := rfl

variable (k) in
/-- Global sections, as a contravariant functor from `S`-schemes to `k`-algebras. -/
@[simps, implicit_reducible]
def globalSectionsFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ CommAlgCat.{u} k where
  obj X := globalSections X.unop
  map g := globalSectionsMap g.unop

/-! ### The affine line and the multiplicative group -/

variable (k) in
/-- The affine line `𝔸¹_S = Spec k[z]` over `S = Spec k`.

Blueprint: `lem:geo-products`. -/
@[implicit_reducible]
def affineLine : Over (Spec (.of k)) := spec (CommAlgCat.of k k[X])

variable (k) in
/-- The multiplicative group `𝔾ₘ = Spec k[z, z⁻¹]` over `S = Spec k`.

Blueprint: `lem:geo-products`, `thm:geo-units`. -/
@[implicit_reducible]
def gm : Over (Spec (.of k)) := spec (CommAlgCat.of k k[T;T⁻¹])

lemma affineLine_eq : affineLine k = spec (CommAlgCat.of k k[X]) := rfl

lemma gm_eq : gm k = spec (CommAlgCat.of k k[T;T⁻¹]) := rfl

lemma affineLine_left : (affineLine k).left = Spec (.of k[X]) := rfl

lemma gm_left : (gm k).left = Spec (.of k[T;T⁻¹]) := rfl

instance : IsAffine (affineLine k).left := inferInstanceAs (IsAffine (Spec _))
instance : IsAffine (gm k).left := inferInstanceAs (IsAffine (Spec _))
instance : Smooth (affineLine k).hom := smooth_spec_hom _
instance : Smooth (gm k).hom := smooth_spec_hom _

/-- `𝔾ₘ` is a group object over `S`, through the Hopf algebra structure of `k[z, z⁻¹]`, whose
comultiplication sends `z` to `z ⊗ z`. -/
instance : GrpObj (gm k) :=
  inferInstanceAs (GrpObj ((Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))))

instance : IsCommMonObj (gm k) :=
  inferInstanceAs (IsCommMonObj ((Spec (.of k[T;T⁻¹])).asOver (Spec (.of k))))

/-! ### Admissible domains -/

variable (k) in
/-- An admissible domain of smooth schemes over `S = Spec k`: a full, isomorphism-closed
subcategory of the smooth `S`-schemes that contains every smooth affine `S`-scheme and is closed
under `X ↦ X ×_S 𝔸¹_S` and `X ↦ X ×_S 𝔾ₘ`. Its morphisms are all `S`-morphisms between its
objects; they need not be smooth, flat or dominant. No nonemptiness or irreducibility is asked of
objects, so the empty scheme belongs to every domain.

Blueprint: `def:geo-domain`. -/
structure SmoothDomain where
  /-- Membership in the domain, a property of `S`-schemes. -/
  property : ObjectProperty (Over (Spec (.of k)))
  /-- The domain is closed under isomorphisms of `S`-schemes. -/
  [isClosedUnderIsomorphisms : property.IsClosedUnderIsomorphisms]
  /-- Objects of the domain are smooth over `S`. -/
  smooth_hom ⦃X : Over (Spec (.of k))⦄ : property X → Smooth X.hom
  /-- Every smooth affine `S`-scheme belongs to the domain. -/
  of_isAffine (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom] : property X
  /-- The domain is closed under `X ↦ X ×_S 𝔸¹_S`. -/
  tensor_affineLine ⦃X : Over (Spec (.of k))⦄ : property X → property (X ⊗ affineLine k)
  /-- The domain is closed under `X ↦ X ×_S 𝔾ₘ`. -/
  tensor_gm ⦃X : Over (Spec (.of k))⦄ : property X → property (X ⊗ gm k)

namespace SmoothDomain

attribute [instance] isClosedUnderIsomorphisms

lemma property_injective : Function.Injective (property : SmoothDomain k → _) := by
  intro D₁ D₂ h
  cases D₁
  cases D₂
  subst h
  rfl

/-- Domains are ordered by inclusion. -/
instance : PartialOrder (SmoothDomain k) := PartialOrder.lift _ property_injective

lemma le_iff {D₁ D₂ : SmoothDomain k} : D₁ ≤ D₂ ↔ D₁.property ≤ D₂.property := .rfl

variable (D : SmoothDomain k)

/-- The category of objects of a domain `D`, a full subcategory of `Over (Spec k)`. -/
abbrev Obj : Type (u + 1) := D.property.FullSubcategory

instance (X : D.Obj) : Smooth X.obj.hom := D.smooth_hom X.property

/-- A smooth affine `S`-scheme as an object of `D`. Membership is found by instances. -/
@[implicit_reducible]
def ofAffine (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom] : D.Obj :=
  ⟨X, D.of_isAffine X⟩

lemma ofAffine_obj (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom] :
    (D.ofAffine X).obj = X := rfl

instance (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom] :
    IsAffine (D.ofAffine X).obj.left := ‹_›

/-- `Spec A`, for a smooth `k`-algebra `A`, as an object of `D`. -/
@[implicit_reducible]
def spec (A : SmoothAlg.{u} k) : D.Obj := D.ofAffine (Geometric.spec A.obj)

lemma spec_obj (A : SmoothAlg.{u} k) : (D.spec A).obj = Geometric.spec A.obj := rfl

instance (A : SmoothAlg.{u} k) : IsAffine (D.spec A).obj.left :=
  inferInstanceAs (IsAffine (Spec _))

/-- `Spec` as a functor from smooth `k`-algebras to the opposite of `D`. -/
@[simps, implicit_reducible]
def specFunctor : SmoothAlg.{u} k ⥤ D.Objᵒᵖ where
  obj A := op (D.spec A)
  map φ := (ObjectProperty.homMk (specMap φ.hom)).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    ext1
    exact specMap_id _
  map_comp φ ψ := by
    apply Quiver.Hom.unop_inj
    ext1
    exact specMap_comp _ _

/-- `Spec` is fully faithful on smooth `k`-algebras, into any domain. -/
def specFunctorFullyFaithful : D.specFunctor.FullyFaithful where
  preimage {A B} f := ObjectProperty.homMk
    ((Geometric.specFunctorFullyFaithful k).preimage (X := op B.obj) (Y := op A.obj)
      f.unop.hom).unop
  map_preimage {A B} f := by
    apply Quiver.Hom.unop_inj
    ext1
    exact (Geometric.specFunctorFullyFaithful k).map_preimage (X := op B.obj) (Y := op A.obj)
      f.unop.hom
  preimage_map {A B} f := by
    apply ObjectProperty.hom_ext
    exact congrArg Quiver.Hom.unop
      ((Geometric.specFunctorFullyFaithful k).preimage_map (X := op B.obj) (Y := op A.obj) f.hom.op)

instance : D.specFunctor.Full := D.specFunctorFullyFaithful.full
instance : D.specFunctor.Faithful := D.specFunctorFullyFaithful.faithful

/-! ### The base, the affine line and the multiplicative group -/

instance : IsAffine (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (IsAffine (Spec _))
instance : Smooth (𝟙_ (Over (Spec (.of k)))).hom := inferInstanceAs (Smooth (𝟙 _))

/-- The base `S = Spec k` itself, as an object of `D`. It is terminal (`isTerminalPoint`), and its
cohomology is the coefficient algebra. -/
@[implicit_reducible]
def point : D.Obj := D.ofAffine (𝟙_ (Over (Spec (.of k))))

lemma point_obj : D.point.obj = 𝟙_ (Over (Spec (.of k))) := rfl

/-- The base is terminal in every domain. -/
def isTerminalPoint : IsTerminal D.point :=
  IsTerminal.ofUniqueHom (fun X ↦ ObjectProperty.homMk (toUnit X.obj))
    fun _ _ ↦ by ext1; exact toUnit_unique _ _

/-- `Spec` of the point `k` of `SmoothAlg k` is the base `S`. -/
def specPointIso : D.spec (SmoothAlg.point k) ≅ D.point :=
  ObjectProperty.isoMk _ <| Over.isoMk (Iso.refl (Spec (.of k))) <| by
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id k))
    rw [Category.comp_id, CommRingCat.ofHom_id, Spec.map_id]

@[simp] lemma specPointIso_hom_hom_left : (D.specPointIso).hom.hom.left = 𝟙 (Spec (.of k)) := rfl

@[simp] lemma specPointIso_inv_hom_left : (D.specPointIso).inv.hom.left = 𝟙 (Spec (.of k)) := rfl

/-- The affine line `𝔸¹_S`, as an object of `D`. -/
@[implicit_reducible]
def affineLine : D.Obj := D.ofAffine (Geometric.affineLine k)

/-- The multiplicative group `𝔾ₘ`, as an object of `D`. -/
@[implicit_reducible]
def gm : D.Obj := D.ofAffine (Geometric.gm k)

lemma affineLine_obj : D.affineLine.obj = Geometric.affineLine k := rfl
lemma gm_obj : D.gm.obj = Geometric.gm k := rfl

/-- The product `X ×_S 𝔸¹_S`, as an object of `D`.

Blueprint: `def:geo-domain`, `lem:geo-products`. -/
@[implicit_reducible]
def prodAffineLine (X : D.Obj) : D.Obj :=
  ⟨X.obj ⊗ Geometric.affineLine k, D.tensor_affineLine X.2⟩

/-- The product `X ×_S 𝔾ₘ`, as an object of `D`.

Blueprint: `def:geo-domain`, `lem:geo-products`. -/
@[implicit_reducible]
def prodGm (X : D.Obj) : D.Obj := ⟨X.obj ⊗ Geometric.gm k, D.tensor_gm X.2⟩

lemma prodAffineLine_obj (X : D.Obj) :
    (D.prodAffineLine X).obj = X.obj ⊗ Geometric.affineLine k := rfl

lemma prodGm_obj (X : D.Obj) : (D.prodGm X).obj = X.obj ⊗ Geometric.gm k := rfl

/-- The first projection `X ×_S 𝔸¹_S → X`, along which pullback is bijective in an ordinary
theory. -/
def prodAffineLineFst (X : D.Obj) : D.prodAffineLine X ⟶ X := ObjectProperty.homMk (fst _ _)

/-- The first projection `X ×_S 𝔾ₘ → X`. -/
def prodGmFst (X : D.Obj) : D.prodGm X ⟶ X := ObjectProperty.homMk (fst _ _)

@[simp] lemma prodAffineLineFst_hom (X : D.Obj) : (D.prodAffineLineFst X).hom = fst _ _ := rfl
@[simp] lemma prodGmFst_hom (X : D.Obj) : (D.prodGmFst X).hom = fst _ _ := rfl

/-! ### The canonical domains -/

variable (k)

/-- The domain of all smooth `S`-schemes.

Blueprint: `def:geo-domain`. -/
def all : SmoothDomain k where
  property X := Smooth X.hom
  isClosedUnderIsomorphisms := ⟨fun e (_ : Smooth _) ↦ by
    rw [← Over.w e.inv]
    infer_instance⟩
  smooth_hom _ h := h
  of_isAffine _ _ h := h
  tensor_affineLine X (_ : Smooth X.hom) := by
    change Smooth (pullback.fst _ _ ≫ X.hom)
    infer_instance
  tensor_gm X (_ : Smooth X.hom) := by
    change Smooth (pullback.fst _ _ ≫ X.hom)
    infer_instance

/-- The domain of smooth affine `S`-schemes, the category `Sm_k^aff` of the blueprint.

Blueprint: `def:geo-domain`, `thm:geo-affine-duality`. -/
def aff : SmoothDomain k where
  property X := IsAffine X.left ∧ Smooth X.hom
  isClosedUnderIsomorphisms := ⟨fun e ⟨_, _⟩ ↦ by
    have : IsIso e.inv.left := inferInstance
    refine ⟨.of_isIso e.inv.left, ?_⟩
    rw [← Over.w e.inv]
    infer_instance⟩
  smooth_hom _ h := h.2
  of_isAffine _ h₁ h₂ := ⟨h₁, h₂⟩
  tensor_affineLine X := fun ⟨_, _⟩ ↦ ⟨inferInstanceAs (IsAffine (pullback _ _)), by
    change Smooth (pullback.fst _ _ ≫ X.hom)
    infer_instance⟩
  tensor_gm X := fun ⟨_, _⟩ ↦ ⟨inferInstanceAs (IsAffine (pullback _ _)), by
    change Smooth (pullback.fst _ _ ≫ X.hom)
    infer_instance⟩

/-- The domain of smooth separated `S`-schemes of finite type. Since a smooth morphism is locally of
finite presentation, finite type amounts to quasi-compactness here.

Blueprint: `def:geo-domain`. -/
def sft : SmoothDomain k where
  property X := Smooth X.hom ∧ IsSeparated X.hom ∧ QuasiCompact X.hom
  isClosedUnderIsomorphisms := ⟨fun e ⟨_, _, _⟩ ↦ by
    rw [← Over.w e.inv]
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩
  smooth_hom _ h := h.1
  of_isAffine _ _ _ := ⟨inferInstance, inferInstance, inferInstance⟩
  tensor_affineLine X := fun ⟨_, _, _⟩ ↦ by
    change Smooth (pullback.fst _ _ ≫ X.hom) ∧ IsSeparated (pullback.fst _ _ ≫ X.hom) ∧
      QuasiCompact (pullback.fst _ _ ≫ X.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  tensor_gm X := fun ⟨_, _, _⟩ ↦ by
    change Smooth (pullback.fst _ _ ≫ X.hom) ∧ IsSeparated (pullback.fst _ _ ≫ X.hom) ∧
      QuasiCompact (pullback.fst _ _ ≫ X.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩

variable {k}

/-- The affine domain is the smallest domain. -/
lemma aff_le (D : SmoothDomain k) : aff k ≤ D := fun X ⟨_, _⟩ ↦ D.of_isAffine X

/-- The domain of all smooth schemes is the largest domain. -/
lemma le_all (D : SmoothDomain k) : D ≤ all k := fun _ h ↦ D.smooth_hom h

lemma sft_le_all : sft k ≤ all k := le_all _

lemma aff_le_sft : aff k ≤ sft k := aff_le _

instance (X : (aff k).Obj) : IsAffine X.obj.left := X.property.1

end SmoothDomain

end OrlikSolomon.Geometric
