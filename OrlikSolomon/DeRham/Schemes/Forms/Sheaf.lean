/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Abelian
/-!
# Sheaves of relative forms

For every scheme over `Spec k`, sheafify the presheaves of relative forms in `k`-modules.
Mathlib's sheafification of presheaves of modules equips these same additive sheaves with their
natural structure-sheaf actions. The differential remains only `k`-linear.

## Main definitions and results

* `formsSheaf` and `formsModuleSheaf`: relative forms as sheaves of `k`-modules and as
  structure-sheaf modules, with the same underlying additive presheaf.
* `formsSheafUnit`: the canonical map from algebraic forms on opens to the sheaf.
* `formsSheafD` and `formsSheafD_comp`: the differential and its square-zero identity.
* `formsSheafMul`, `formsSheafWedge`: natural wedge products on the same sheafified carriers.
* `formsSheafMul_unit`, `formsSheaf_tensor_hom_ext` and its ternary version: products and identities
  are determined on algebraic representatives.
* `formsSheafMul_assoc`, `formsSheafMul_comm`, `formsSheafMul_leibniz`: the dg algebra identities.
* `formsSheafZeroIso`: degree zero is the usual structure sheaf, preserving multiplication and one.
* `formsComplex`: the de Rham complex indexed by integers and zero in negative degrees.
* `formsComplexNat_X`, `formsComplexNat_d`, `formsComplexXIso` and `formsComplex_d`: the
  public comparisons of complex terms and differentials with the sheaves of forms.

These constructions require only a commutative base ring. No smoothness, affineness,
separatedness or nonemptiness assumption is used.

Blueprint: the sheafification and complex in `def:geo-forms-sheaf`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped TensorProduct
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable (k : Type u) [CommRing k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Relative forms with the semilinear restriction maps of a structure-sheaf module. -/
def formsModulePresheaf (n : ℕ) : X.left.PresheafOfModules := by
  let F := formsPresheaf k X n ⋙ forget₂ (ModuleCat k) AddCommGrpCat
  letI (U : X.left.Opensᵒᵖ) : Module (X.left.ringCatSheaf.obj.obj U) (F.obj U) :=
    inferInstanceAs (Module (sectionAlgebra k X U.unop)
      (⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k]))
  exact PresheafOfModules.ofPresheaf F fun {U V} i r x =>
    Forms.mapPower_smul (sectionRestriction k X i.unop) n r x

/-- The sheafification of relative forms in the category of `k`-modules.
Blueprint: `def:geo-forms-sheaf`. -/
def formsSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat k) X.left :=
  (presheafToSheaf (_root_.Opens.grothendieckTopology X.left) (ModuleCat k)).obj
    (formsPresheaf k X n)

/-- The canonical map from algebraic forms on opens to their sheafification. -/
def formsSheafUnit (n : ℕ) : formsPresheaf k X n ⟶ (formsSheaf k X n).obj :=
  CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
    (formsPresheaf k X n)

private def formsAdditiveSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat X.left :=
  (sheafCompose (_root_.Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat k) AddCommGrpCat)).obj (formsSheaf k X n)

private def formsModuleUnit (n : ℕ) :
    (formsModulePresheaf k X n).presheaf ⟶ (formsAdditiveSheaf k X n).obj :=
  Functor.whiskerRight (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
    (formsPresheaf k X n)) (forget₂ (ModuleCat k) AddCommGrpCat)

private instance formsModuleUnit_locallyInjective (n : ℕ) :
    Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X.left)
      (formsModuleUnit k X n) where
  equalizerSieve_mem a b h := Presheaf.equalizerSieve_mem _
    (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
      (formsPresheaf k X n)) a b h

private instance formsModuleUnit_locallySurjective (n : ℕ) :
    Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X.left)
      (formsModuleUnit k X n) where
  imageSieve_mem a := Presheaf.imageSieve_mem _
    (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
      (formsPresheaf k X n)) a

/-- The natural structure-sheaf module on the additive sheaf underlying `formsSheaf`.
Blueprint: `def:geo-forms-sheaf`. -/
@[no_expose] def formsModuleSheaf (n : ℕ) : X.left.Modules :=
  PresheafOfModules.sheafify (A := formsAdditiveSheaf k X n)
    (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)

/-- The two versions of forms have the same underlying additive presheaf. -/
theorem formsModuleSheaf_presheaf (n : ℕ) :
    (formsModuleSheaf k X n).presheaf =
      (formsSheaf k X n).obj ⋙ forget₂ (ModuleCat k) AddCommGrpCat := by
  rfl

/-- The sheafification map with its structure-sheaf linearity. -/
@[no_expose] def formsModuleSheafUnit (n : ℕ) :
    formsModulePresheaf k X n ⟶ (formsModuleSheaf k X n).val :=
  PresheafOfModules.toSheafify (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)

/-- The module-valued and base-linear sheafification maps agree under the carrier comparison. -/
theorem formsModuleSheafUnit_presheaf (n : ℕ) :
    (PresheafOfModules.toPresheaf _).map (formsModuleSheafUnit k X n) ≫
      eqToHom (formsModuleSheaf_presheaf k X n) =
      Functor.whiskerRight (formsSheafUnit k X n) (forget₂ (ModuleCat k) AddCommGrpCat) := by
  ext U x
  rfl

/-- Restricting the structure-sheaf action gives the base-ring action on module-valued forms. -/
instance formsModuleSheafBaseModule (n : ℕ) (U : X.left.Opens) :
    Module k Γ(formsModuleSheaf k X n, U) :=
  Module.compHom (R := Γ(X.left, U)) _
    (show k →+* Γ(X.left, U) from algebraMap k (sectionAlgebra k X U))

private theorem formsSheaf_algebraMap_smul (n : ℕ) (U : X.left.Opensᵒᵖ)
    (r : k) (x : (formsSheaf k X n).obj.obj U) :
    PresheafOfModules.Sheafify.smul (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)
      (show X.left.ringCatSheaf.obj.obj U from algebraMap k (sectionAlgebra k X U.unop) r) x =
        r • x := by
  apply (formsAdditiveSheaf k X n).isSeparated _ _
    (Presheaf.imageSieve_mem _ (formsModuleUnit k X n) x)
  rintro V f ⟨z, hz⟩
  rw [PresheafOfModules.Sheafify.map_smul_eq _ _ _ _ f.op
    (algebraMap k (sectionAlgebra k X V) r)
    (by exact (sectionRestriction k X f).commutes r |>.symm) z hz]
  let z' : ⋀[sectionAlgebra k X V]^n Ω[sectionAlgebra k X V⁄k] := z
  change (formsSheafUnit k X n).app (op V)
    (algebraMap k (sectionAlgebra k X V) r • z') =
      (formsSheaf k X n).obj.map f.op (r • x)
  rw [algebraMap_smul]
  have hz' : (formsSheafUnit k X n).app (op V) z' =
      (formsSheaf k X n).obj.map f.op x := hz
  exact (((formsSheafUnit k X n).app (op V)).hom.map_smul r z').trans
    ((congrArg (fun t : (formsSheaf k X n).obj.obj (op V) => r • t) hz').trans
      (((formsSheaf k X n).obj.map f.op).hom.map_smul r x).symm)

/-- The natural structure-sheaf action restricts to the original action on sheafified forms. -/
@[no_expose] def formsModuleSheafBaseIso (n : ℕ) (U : X.left.Opens) :
    ModuleCat.of k Γ(formsModuleSheaf k X n, U) ≅ (formsSheaf k X n).obj.obj (op U) :=
  LinearEquiv.toModuleIso
    { __ := AddEquiv.refl _,
      map_smul' r x := formsSheaf_algebraMap_smul k X n (op U) r x }

/-- The public additive carrier comparison agrees with the base-linear comparison on sections. -/
theorem formsModuleSheaf_presheaf_hom_app (n : ℕ) (U : X.left.Opens)
    (a : Γ(formsModuleSheaf k X n, U)) :
    (eqToHom (formsModuleSheaf_presheaf k X n)).app (op U) a =
      (formsModuleSheafBaseIso k X n U).hom a := by
  rfl

/-- The inverse additive carrier comparison agrees with the inverse base-linear comparison. -/
theorem formsModuleSheaf_presheaf_inv_app (n : ℕ) (U : X.left.Opens)
    (a : (formsSheaf k X n).obj.obj (op U)) :
    (eqToHom (formsModuleSheaf_presheaf k X n).symm).app (op U) a =
      (formsModuleSheafBaseIso k X n U).inv a := by
  rfl

/-- The sheaf differential, obtained from the existing algebraic differential.
Blueprint: `def:geo-forms-sheaf`. -/
def formsSheafD (n : ℕ) : formsSheaf k X n ⟶ formsSheaf k X (n + 1) :=
  (presheafToSheaf (_root_.Opens.grothendieckTopology X.left) (ModuleCat k)).map
    (formsPresheafD k X n)

/-- The sheaf differential squares to zero. -/
theorem formsSheafD_comp (n : ℕ) : formsSheafD k X n ≫ formsSheafD k X (n + 1) = 0 := by
  change (presheafToSheaf _ (ModuleCat k)).map (formsPresheafD k X n) ≫
    (presheafToSheaf _ (ModuleCat k)).map (formsPresheafD k X (n + 1)) = _
  rw [← Functor.map_comp, formsPresheafD_comp, Functor.map_zero]
  rfl

/-- Sheafification of algebraic forms commutes with the differential. -/
theorem formsSheafUnit_d (n : ℕ) :
    formsSheafUnit k X n ≫ (formsSheafD k X n).hom =
      formsPresheafD k X n ≫ formsSheafUnit k X (n + 1) := by
  exact (CategoryTheory.toSheafify_naturality _ (formsPresheafD k X n)).symm

/-- Tensoring two sheafification maps is a local equivalence. -/
theorem formsSheaf_tensor_unit_W (p q : ℕ) :
    (_root_.Opens.grothendieckTopology X.left).W
      (formsSheafUnit k X p ⊗ₘ formsSheafUnit k X q) :=
  ((_root_.Opens.grothendieckTopology X.left).W (A := ModuleCat k)).tensorHom_mem _ _
    ((_root_.Opens.grothendieckTopology X.left).W_toSheafify _)
    ((_root_.Opens.grothendieckTopology X.left).W_toSheafify _)

/-- Natural bilinear operations from two sheaves of forms are determined by algebraic
representatives. The target can be any sheaf of base-ring modules. -/
theorem formsSheaf_tensor_hom_ext (p q : ℕ) (H : TopCat.Sheaf (ModuleCat k) X.left)
    {f g : (formsSheaf k X p).obj ⊗ (formsSheaf k X q).obj ⟶ H.obj}
    (h : ∀ (U : X.left.Opensᵒᵖ) (a : (formsPresheaf k X p).obj U)
      (b : (formsPresheaf k X q).obj U),
      f.app U ((formsSheafUnit k X p).app U a ⊗ₜ[k] (formsSheafUnit k X q).app U b) =
        g.app U ((formsSheafUnit k X p).app U a ⊗ₜ[k] (formsSheafUnit k X q).app U b)) : f = g := by
  apply (formsSheaf_tensor_unit_W k X p q H.obj H.property).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  exact h U a b

/-- The exterior product on the existing sheafified degree carriers. It is the unique extension
of algebraic wedge multiplication through the two sheafification maps. -/
def formsSheafMul (p q : ℕ) :
    (formsSheaf k X p).obj ⊗ (formsSheaf k X q).obj ⟶ (formsSheaf k X (p + q)).obj :=
  ((formsSheaf_tensor_unit_W k X p q _ (formsSheaf k X (p + q)).property).surjective
    (formsPresheafMul k X p q ≫ formsSheafUnit k X (p + q))).choose

/-- Sheaf wedge multiplication agrees with algebraic multiplication on representatives. -/
theorem formsSheafMul_unit (p q : ℕ) :
    (formsSheafUnit k X p ⊗ₘ formsSheafUnit k X q) ≫ formsSheafMul k X p q =
      formsPresheafMul k X p q ≫ formsSheafUnit k X (p + q) :=
  ((formsSheaf_tensor_unit_W k X p q _ (formsSheaf k X (p + q)).property).surjective
    (formsPresheafMul k X p q ≫ formsSheafUnit k X (p + q))).choose_spec

/-- Wedge multiplication on sections over an open. -/
def formsSheafWedge (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U) :
    (formsSheaf k X (p + q)).obj.obj U :=
  (formsSheafMul k X p q).app U (a ⊗ₜ[k] b)

/-- The section product is bilinear over the base ring. -/
def formsSheafWedgeLinear (p q : ℕ) (U : X.left.Opensᵒᵖ) :
    (formsSheaf k X p).obj.obj U →ₗ[k]
      (formsSheaf k X q).obj.obj U →ₗ[k] (formsSheaf k X (p + q)).obj.obj U :=
  LinearMap.compr₂ (TensorProduct.mk k _ _) ((formsSheafMul k X p q).app U).hom

@[simp] theorem formsSheafWedgeLinear_apply (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U) :
    formsSheafWedgeLinear k X p q U a b = formsSheafWedge k X p q U a b := rfl

/-- On algebraic representatives the section product is exterior multiplication. -/
@[simp] theorem formsSheafWedge_unit (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsPresheaf k X p).obj U) (b : (formsPresheaf k X q).obj U) :
    formsSheafWedge k X p q U ((formsSheafUnit k X p).app U a)
        ((formsSheafUnit k X q).app U b) =
      (formsSheafUnit k X (p + q)).app U ((formsPresheafMul k X p q).app U (a ⊗ₜ[k] b)) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafMul_unit k X p q) U) (a ⊗ₜ[k] b)

/-- Wedge products commute with restriction of sections. -/
theorem formsSheafWedge_naturality (p q : ℕ) {U V : X.left.Opensᵒᵖ} (i : U ⟶ V)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U) :
    (formsSheaf k X (p + q)).obj.map i (formsSheafWedge k X p q U a b) =
      formsSheafWedge k X p q V ((formsSheaf k X p).obj.map i a)
        ((formsSheaf k X q).obj.map i b) :=
  (ConcreteCategory.congr_hom ((formsSheafMul k X p q).naturality i) (a ⊗ₜ[k] b)).symm

/-- The structure sheaf, viewed as sheaves of base-ring modules. -/
@[implicit_reducible] def functionsSheaf : TopCat.Sheaf (ModuleCat k) X.left :=
  ⟨functionsPresheaf k X, by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat k))).2
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)).1
      X.left.sheaf.property⟩

/-- Degree-zero forms are the usual structure sheaf. This compares the existing degree-zero
carrier with functions and sends a function to its algebraic degree-zero form. -/
def formsSheafZeroIso : functionsSheaf k X ≅ formsSheaf k X 0 :=
  ObjectProperty.isoMk _ (formsPresheafZeroIso k X ≪≫
    isoSheafify (_root_.Opens.grothendieckTopology X.left)
      ((Presheaf.isSheaf_of_iso_iff (formsPresheafZeroIso k X)).1
        (functionsSheaf k X).property))

/-- The degree-zero comparison is induced by the canonical sheafification map. -/
theorem formsSheafZeroIso_hom :
    (formsSheafZeroIso k X).hom.hom = formsPresheafZero k X ≫ formsSheafUnit k X 0 := rfl

/-- Change the displayed degree along an equality of indices. -/
def formsSheafCast {p q : ℕ} (h : p = q) : formsSheaf k X p ⟶ formsSheaf k X q :=
  eqToHom (congrArg (formsSheaf k X) h)

/-- Degree casts commute with sheafification. -/
theorem formsSheafCast_unit {p q : ℕ} (h : p = q) :
    formsSheafUnit k X p ≫ (formsSheafCast k X h).hom =
      formsPresheafCast k X h ≫ formsSheafUnit k X q := by
  subst q
  simp [formsSheafCast, formsPresheafCast]

/-- Degree casts act on algebraic representatives without changing the total form. -/
@[simp] theorem formsSheafCast_unit_apply {p q : ℕ} (h : p = q) (U : X.left.Opensᵒᵖ)
    (a : (formsPresheaf k X p).obj U) :
    (formsSheafCast k X h).hom.app U ((formsSheafUnit k X p).app U a) =
      (formsSheafUnit k X q).app U ((formsPresheafCast k X h).app U a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafCast_unit k X h) U) a

/-- Sheaf differential on an algebraic representative. -/
@[simp] theorem formsSheafD_unit (n : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsPresheaf k X n).obj U) :
    (formsSheafD k X n).hom.app U ((formsSheafUnit k X n).app U a) =
      (formsSheafUnit k X (n + 1)).app U ((formsPresheafD k X n).app U a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafUnit_d k X n) U) a

/-- Natural trilinear operations on sheafified forms are determined by algebraic representatives. -/
theorem formsSheaf_tensor_hom_ext₃ (p q r : ℕ) (H : TopCat.Sheaf (ModuleCat k) X.left)
    {f g : ((formsSheaf k X p).obj ⊗ (formsSheaf k X q).obj) ⊗
      (formsSheaf k X r).obj ⟶ H.obj}
    (h : ∀ (U : X.left.Opensᵒᵖ) (a : (formsPresheaf k X p).obj U)
      (b : (formsPresheaf k X q).obj U) (c : (formsPresheaf k X r).obj U),
      f.app U (((formsSheafUnit k X p).app U a ⊗ₜ[k]
        (formsSheafUnit k X q).app U b) ⊗ₜ[k] (formsSheafUnit k X r).app U c) =
      g.app U (((formsSheafUnit k X p).app U a ⊗ₜ[k]
        (formsSheafUnit k X q).app U b) ⊗ₜ[k] (formsSheafUnit k X r).app U c)) : f = g := by
  have hw := ((_root_.Opens.grothendieckTopology X.left).W (A := ModuleCat k)).tensorHom_mem
    _ _ (formsSheaf_tensor_unit_W k X p q)
    ((_root_.Opens.grothendieckTopology X.left).W_toSheafify (formsPresheaf k X r))
  apply (hw H.obj H.property).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro a b c
  exact h U a b c

/-- The degree-zero unit of the sheafified algebra of relative forms. -/
def formsSheafOne : 𝟙_ (X.left.Opensᵒᵖ ⥤ ModuleCat k) ⟶ (formsSheaf k X 0).obj :=
  formsPresheafOne k X ≫ formsSheafUnit k X 0

/-- The unit section in degree zero over an open. -/
def formsSheafOneSection (U : X.left.Opensᵒᵖ) : (formsSheaf k X 0).obj.obj U :=
  (formsSheafOne k X).app U (1 : k)

/-- Wedge multiplication is associative, with the canonical reindexing of degrees. -/
theorem formsSheafMul_assoc (p q r : ℕ) :
    (formsSheafMul k X p q ⊗ₘ 𝟙 (formsSheaf k X r).obj) ≫
        formsSheafMul k X (p + q) r ≫ (formsSheafCast k X (Nat.add_assoc p q r)).hom =
      (α_ (formsSheaf k X p).obj (formsSheaf k X q).obj (formsSheaf k X r).obj).hom ≫
        (𝟙 (formsSheaf k X p).obj ⊗ₘ formsSheafMul k X q r) ≫
          formsSheafMul k X p (q + r) := by
  apply formsSheaf_tensor_hom_ext₃ k X p q r (formsSheaf k X (p + (q + r)))
  intro U a b c
  change (formsSheafCast k X (Nat.add_assoc p q r)).hom.app U
      (formsSheafWedge k X (p + q) r U
        (formsSheafWedge k X p q U ((formsSheafUnit k X p).app U a)
          ((formsSheafUnit k X q).app U b)) ((formsSheafUnit k X r).app U c)) =
    formsSheafWedge k X p (q + r) U ((formsSheafUnit k X p).app U a)
      (formsSheafWedge k X q r U ((formsSheafUnit k X q).app U b)
        ((formsSheafUnit k X r).app U c))
  rw [formsSheafWedge_unit, formsSheafWedge_unit, formsSheafWedge_unit,
    formsSheafWedge_unit, formsSheafCast_unit_apply]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k] := b
  let c' : ⋀[sectionAlgebra k X U.unop]^r Ω[sectionAlgebra k X U.unop⁄k] := c
  change ((formsPresheafCast k X (Nat.add_assoc p q r)).app U
    ⟨(a'.val * b'.val) * c'.val, _⟩ :
      ⋀[sectionAlgebra k X U.unop]^(p + (q + r)) Ω[sectionAlgebra k X U.unop⁄k]).val =
    a'.val * (b'.val * c'.val)
  rw [formsPresheafCast_val]
  exact mul_assoc _ _ _

/-- Graded commutativity uses the cohomological degrees, over any base ring. -/
theorem formsSheafMul_comm (p q : ℕ) :
    formsSheafMul k X p q ≫ (formsSheafCast k X (Nat.add_comm p q)).hom =
      ((p : ℤ) * q).negOnePow •
        ((β_ (formsSheaf k X p).obj (formsSheaf k X q).obj).hom ≫ formsSheafMul k X q p) := by
  apply formsSheaf_tensor_hom_ext k X p q (formsSheaf k X (q + p))
  intro U a b
  change (formsSheafCast k X (Nat.add_comm p q)).hom.app U
      (formsSheafWedge k X p q U ((formsSheafUnit k X p).app U a)
        ((formsSheafUnit k X q).app U b)) =
    ((p : ℤ) * q).negOnePow • formsSheafWedge k X q p U
      ((formsSheafUnit k X q).app U b) ((formsSheafUnit k X p).app U a)
  rw [formsSheafWedge_unit, formsSheafWedge_unit, formsSheafCast_unit_apply, ← map_zsmul_unit]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k] := b
  change ((formsPresheafCast k X (Nat.add_comm p q)).app U
    ⟨a'.val * b'.val, _⟩ :
      ⋀[sectionAlgebra k X U.unop]^(q + p) Ω[sectionAlgebra k X U.unop⁄k]).val =
    ((p : ℤ) * q).negOnePow • (b'.val * a'.val)
  rw [formsPresheafCast_val]
  exact mul_comm_of_mem_exteriorPower a'.2 b'.2

/-- Signed Leibniz for the sheafified differential, with the first factor's degree determining
its sign. The differential is only base-ring linear. -/
theorem formsSheafMul_leibniz (p q : ℕ) :
    formsSheafMul k X p q ≫ (formsSheafD k X (p + q)).hom ≫
        (formsSheafCast k X (by omega : p + q + 1 = p + (q + 1))).hom =
      ((formsSheafD k X p).hom ⊗ₘ 𝟙 (formsSheaf k X q).obj) ≫
          formsSheafMul k X (p + 1) q ≫
            (formsSheafCast k X (by omega : p + 1 + q = p + (q + 1))).hom +
        (p : ℤ).negOnePow •
          ((𝟙 (formsSheaf k X p).obj ⊗ₘ (formsSheafD k X q).hom) ≫
            formsSheafMul k X p (q + 1)) := by
  apply formsSheaf_tensor_hom_ext k X p q (formsSheaf k X (p + (q + 1)))
  intro U a b
  change (formsSheafCast k X (by omega : p + q + 1 = p + (q + 1))).hom.app U
      ((formsSheafD k X (p + q)).hom.app U
        (formsSheafWedge k X p q U ((formsSheafUnit k X p).app U a)
          ((formsSheafUnit k X q).app U b))) =
    (formsSheafCast k X (by omega : p + 1 + q = p + (q + 1))).hom.app U
      (formsSheafWedge k X (p + 1) q U
        ((formsSheafD k X p).hom.app U ((formsSheafUnit k X p).app U a))
        ((formsSheafUnit k X q).app U b)) +
      (p : ℤ).negOnePow • formsSheafWedge k X p (q + 1) U
        ((formsSheafUnit k X p).app U a)
        ((formsSheafD k X q).hom.app U ((formsSheafUnit k X q).app U b))
  rw [formsSheafWedge_unit, formsSheafD_unit, formsSheafD_unit, formsSheafD_unit,
    formsSheafWedge_unit, formsSheafWedge_unit, formsSheafCast_unit_apply,
    formsSheafCast_unit_apply, ← map_zsmul_unit, ← map_add]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k] := b
  change ((formsPresheafCast k X (by omega : p + q + 1 = p + (q + 1))).app U
      ⟨d k (a'.val * b'.val), _⟩ :
      ⋀[sectionAlgebra k X U.unop]^(p + (q + 1)) Ω[sectionAlgebra k X U.unop⁄k]).val =
    ((formsPresheafCast k X (by omega : p + 1 + q = p + (q + 1))).app U
      ⟨d k a'.val * b'.val, _⟩ :
      ⋀[sectionAlgebra k X U.unop]^(p + (q + 1)) Ω[sectionAlgebra k X U.unop⁄k]).val +
      (p : ℤ).negOnePow • (a'.val * d k b'.val)
  rw [formsPresheafCast_val, formsPresheafCast_val]
  exact d_mul_of_mem_exteriorPower k a'.2 b'.val

/-- Wedge multiplication has the degree-zero unit on its left. -/
theorem formsSheafMul_one_left (n : ℕ) :
    (formsSheafOne k X ⊗ₘ 𝟙 (formsSheaf k X n).obj) ≫ formsSheafMul k X 0 n ≫
        (formsSheafCast k X (Nat.zero_add n)).hom =
      (λ_ (formsSheaf k X n).obj).hom := by
  have hw := ((_root_.Opens.grothendieckTopology X.left).W (A := ModuleCat k)).tensorHom_mem
    (𝟙 (𝟙_ (X.left.Opensᵒᵖ ⥤ ModuleCat k))) (formsSheafUnit k X n)
    ((_root_.Opens.grothendieckTopology X.left).W.id_mem _)
    ((_root_.Opens.grothendieckTopology X.left).W_toSheafify (formsPresheaf k X n))
  apply (hw (formsSheaf k X n).obj (formsSheaf k X n).property).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro c a
  let r : k := c
  change (formsSheafCast k X (Nat.zero_add n)).hom.app U
      (formsSheafWedge k X 0 n U
        ((formsSheafUnit k X 0).app U ((formsPresheafOne k X).app U r))
        ((formsSheafUnit k X n).app U a)) =
      r • (formsSheafUnit k X n).app U a
  rw [formsSheafWedge_unit, formsSheafCast_unit_apply, ← map_smul]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k] := a
  change ((formsPresheafCast k X (Nat.zero_add n)).app U
      ⟨(r • (1 : Forms k (sectionAlgebra k X U.unop))) * a'.val, _⟩ :
      ⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k]).val = r • a'.val
  rw [formsPresheafCast_val]
  change (r • (1 : Forms k (sectionAlgebra k X U.unop))) * a'.val = r • a'.val
  rw [smul_mul_assoc, one_mul]

/-- Wedge multiplication has the degree-zero unit on its right. -/
theorem formsSheafMul_one_right (n : ℕ) :
    (𝟙 (formsSheaf k X n).obj ⊗ₘ formsSheafOne k X) ≫ formsSheafMul k X n 0 =
      (ρ_ (formsSheaf k X n).obj).hom := by
  have hw := ((_root_.Opens.grothendieckTopology X.left).W (A := ModuleCat k)).tensorHom_mem
    (formsSheafUnit k X n) (𝟙 (𝟙_ (X.left.Opensᵒᵖ ⥤ ModuleCat k)))
    ((_root_.Opens.grothendieckTopology X.left).W_toSheafify (formsPresheaf k X n))
    ((_root_.Opens.grothendieckTopology X.left).W.id_mem _)
  apply (hw (formsSheaf k X n).obj (formsSheaf k X n).property).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a c
  let r : k := c
  change formsSheafWedge k X n 0 U ((formsSheafUnit k X n).app U a)
      ((formsSheafUnit k X 0).app U ((formsPresheafOne k X).app U r)) =
    r • (formsSheafUnit k X n).app U a
  rw [formsSheafWedge_unit, ← map_smul]
  congr 1
  apply Subtype.ext
  let a' : ⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k] := a
  change a'.val * (r • (1 : Forms k (sectionAlgebra k X U.unop))) = r • a'.val
  rw [mul_smul_comm, mul_one]

/-- Associativity of wedge products of sections. -/
theorem formsSheafWedge_assoc (p q r : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U)
    (c : (formsSheaf k X r).obj.obj U) :
    (formsSheafCast k X (Nat.add_assoc p q r)).hom.app U
        (formsSheafWedge k X (p + q) r U (formsSheafWedge k X p q U a b) c) =
      formsSheafWedge k X p (q + r) U a (formsSheafWedge k X q r U b c) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafMul_assoc k X p q r) U)
    ((a ⊗ₜ[k] b) ⊗ₜ[k] c)

/-- Graded commutativity of wedge products of sections. -/
theorem formsSheafWedge_comm (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U) :
    (formsSheafCast k X (Nat.add_comm p q)).hom.app U
        (formsSheafWedge k X p q U a b) =
      ((p : ℤ) * q).negOnePow • formsSheafWedge k X q p U b a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafMul_comm k X p q) U) (a ⊗ₜ[k] b)

/-- Signed Leibniz on sections of the sheaves of forms. -/
theorem formsSheafWedge_leibniz (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X p).obj.obj U) (b : (formsSheaf k X q).obj.obj U) :
    (formsSheafCast k X (by omega : p + q + 1 = p + (q + 1))).hom.app U
        ((formsSheafD k X (p + q)).hom.app U (formsSheafWedge k X p q U a b)) =
      (formsSheafCast k X (by omega : p + 1 + q = p + (q + 1))).hom.app U
          (formsSheafWedge k X (p + 1) q U ((formsSheafD k X p).hom.app U a) b) +
        (p : ℤ).negOnePow •
          formsSheafWedge k X p (q + 1) U a ((formsSheafD k X q).hom.app U b) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafMul_leibniz k X p q) U) (a ⊗ₜ[k] b)

/-- The degree-zero unit section is a left unit for section products. -/
@[simp] theorem formsSheafWedge_one_left (n : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X n).obj.obj U) :
    (formsSheafCast k X (Nat.zero_add n)).hom.app U
      (formsSheafWedge k X 0 n U (formsSheafOneSection k X U) a) = a := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (formsSheafMul_one_left k X n) U) ((1 : k) ⊗ₜ[k] a)
  change (formsSheafCast k X (Nat.zero_add n)).hom.app U
      (formsSheafWedge k X 0 n U (formsSheafOneSection k X U) a) = (1 : k) • a at h
  simpa only [one_smul] using h

/-- The degree-zero unit section is a right unit for section products. -/
@[simp] theorem formsSheafWedge_one_right (n : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsSheaf k X n).obj.obj U) :
    formsSheafWedge k X n 0 U a (formsSheafOneSection k X U) = a := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (formsSheafMul_one_right k X n) U) (a ⊗ₜ[k] (1 : k))
  change formsSheafWedge k X n 0 U a (formsSheafOneSection k X U) = (1 : k) • a at h
  simpa only [one_smul] using h

/-- The degree-zero comparison preserves multiplication of regular functions. -/
@[simp] theorem formsSheafZeroIso_mul (U : X.left.Opensᵒᵖ)
    (a b : sectionAlgebra k X U.unop) :
    formsSheafWedge k X 0 0 U ((formsSheafZeroIso k X).hom.hom.app U a)
        ((formsSheafZeroIso k X).hom.hom.app U b) =
      (formsSheafZeroIso k X).hom.hom.app U (a * b) := by
  change formsSheafWedge k X 0 0 U
      ((formsSheafUnit k X 0).app U ((formsPresheafZero k X).app U a))
      ((formsSheafUnit k X 0).app U ((formsPresheafZero k X).app U b)) =
    (formsSheafUnit k X 0).app U ((formsPresheafZero k X).app U (a * b))
  rw [formsSheafWedge_unit]
  congr 1
  apply Subtype.ext
  exact (algebraMap (sectionAlgebra k X U.unop) (Forms k (sectionAlgebra k X U.unop))).map_mul a b
    |>.symm

/-- The degree-zero comparison preserves the unit of the structure sheaf. -/
@[simp] theorem formsSheafZeroIso_one (U : X.left.Opensᵒᵖ) :
    (formsSheafZeroIso k X).hom.hom.app U (1 : sectionAlgebra k X U.unop) =
      formsSheafOneSection k X U := by
  change (formsSheafUnit k X 0).app U
      ((formsPresheafZero k X).app U (1 : sectionAlgebra k X U.unop)) =
    (formsSheafUnit k X 0).app U ((formsPresheafOne k X).app U (1 : k))
  congr 1
  rw [formsPresheafOne_one]
  apply Subtype.ext
  exact map_one _

/-- The unit of the sheafified dg algebra has zero differential. -/
theorem formsSheafOne_d : formsSheafOne k X ≫ (formsSheafD k X 0).hom = 0 := by
  have h : formsPresheafOne k X ≫ formsPresheafD k X 0 = 0 := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    let r : k := a
    change d k (r • (1 : Forms k (sectionAlgebra k X U.unop))) = 0
    simp
  rw [formsSheafOne, Category.assoc, formsSheafUnit_d, ← Category.assoc, h, Limits.zero_comp]

/-- The unit sections commute with restriction to smaller opens. -/
@[simp] theorem formsSheafOneSection_naturality {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (formsSheaf k X 0).obj.map i (formsSheafOneSection k X U) =
      formsSheafOneSection k X V := by
  exact (ConcreteCategory.congr_hom ((formsSheafOne k X).naturality i) (1 : k)).symm

/-- Every unit section has zero differential. -/
@[simp] theorem formsSheafOneSection_d (U : X.left.Opensᵒᵖ) :
    (formsSheafD k X 0).hom.app U (formsSheafOneSection k X U) = 0 := by
  change ((formsSheafOne k X ≫ (formsSheafD k X 0).hom).app U) (1 : k) = 0
  rw [formsSheafOne_d]
  rfl

/-- The existing structure-sheaf action, expressed on the base-linear sheaf carrier. -/
def formsSheafSMul (n : ℕ) (U : X.left.Opens) (r : Γ(X.left, U))
    (a : (formsSheaf k X n).obj.obj (op U)) : (formsSheaf k X n).obj.obj (op U) :=
  (formsModuleSheafBaseIso k X n U).hom
    (r • (formsModuleSheafBaseIso k X n U).inv a)

/-- The carrier comparison intertwines the actual module action with the section action. -/
@[simp] theorem formsModuleSheafBaseIso_smul (n : ℕ) (U : X.left.Opens)
    (r : Γ(X.left, U)) (a : Γ(formsModuleSheaf k X n, U)) :
    (formsModuleSheafBaseIso k X n U).hom (r • a) =
      formsSheafSMul k X n U r ((formsModuleSheafBaseIso k X n U).hom a) := by
  simp only [formsSheafSMul, Iso.hom_inv_id_apply]

/-- The structure-sheaf action on an algebraic representative is the original scalar action. -/
theorem formsSheafSMul_unit (n : ℕ) (U : X.left.Opens) (r : sectionAlgebra k X U)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    formsSheafSMul k X n U r ((formsSheafUnit k X n).app (op U) a) =
      (formsSheafUnit k X n).app (op U) (r • a) := by
  exact (((formsModuleSheafUnit k X n).app (op U)).hom.map_smul r a).symm

/-- The structure-sheaf action commutes with restriction of sections. -/
theorem formsSheafSMul_naturality (n : ℕ) {U V : X.left.Opens} (i : V ⟶ U)
    (r : Γ(X.left, U)) (a : (formsSheaf k X n).obj.obj (op U)) :
    (formsSheaf k X n).obj.map i.op (formsSheafSMul k X n U r a) =
      formsSheafSMul k X n V ((sectionRestriction k X i) r)
        ((formsSheaf k X n).obj.map i.op a) :=
  (formsModuleSheaf k X n).val.map_smul i.op r a

/-- Multiplication by a degree-zero function is the existing structure-sheaf scalar action.
Thus the product and the retained module structures agree on the same additive carrier. -/
theorem formsSheafWedge_zero_eq_smul (n : ℕ) (U : X.left.Opens)
    (r : sectionAlgebra k X U) (a : (formsSheaf k X n).obj.obj (op U)) :
    formsSheafWedge k X n 0 (op U) a ((formsSheafZeroIso k X).hom.hom.app (op U) r) =
      formsSheafSMul k X n U r a := by
  apply (formsAdditiveSheaf k X n).isSeparated _ _
    (Presheaf.imageSieve_mem _ (formsModuleUnit k X n) a)
  rintro V f ⟨b, hb⟩
  change (formsSheaf k X n).obj.map f.op
      (formsSheafWedge k X n 0 (op U) a ((formsSheafZeroIso k X).hom.hom.app (op U) r)) =
    (formsSheaf k X n).obj.map f.op (formsSheafSMul k X n U r a)
  refine (formsSheafWedge_naturality k X n 0 f.op a
    ((formsSheafZeroIso k X).hom.hom.app (op U) r)).trans ?_
  rw [formsSheafSMul_naturality]
  have hr := ConcreteCategory.congr_hom ((formsSheafZeroIso k X).hom.hom.naturality f.op) r
  change (formsSheafZeroIso k X).hom.hom.app (op V) (sectionRestriction k X f r) =
    (formsSheaf k X 0).obj.map f.op ((formsSheafZeroIso k X).hom.hom.app (op U) r) at hr
  have hb' : (formsSheafUnit k X n).app (op V) b = (formsSheaf k X n).obj.map f.op a := hb
  rw [← hr, ← hb']
  let c : (formsPresheaf k X n).obj (op V) := b
  change formsSheafWedge k X n 0 (op V) ((formsSheafUnit k X n).app (op V) c)
      ((formsSheafUnit k X 0).app (op V)
        ((formsPresheafZero k X).app (op V) (sectionRestriction k X f r))) =
    formsSheafSMul k X n V (sectionRestriction k X f r)
      ((formsSheafUnit k X n).app (op V) c)
  refine (formsSheafWedge_unit k X n 0 (op V) c _).trans ?_
  refine Eq.trans ?_ (formsSheafSMul_unit k X n V (sectionRestriction k X f r) c).symm
  congr 1
  apply Subtype.ext
  let b' : ⋀[sectionAlgebra k X V]^n Ω[sectionAlgebra k X V⁄k] := c
  change b'.val * algebraMap (sectionAlgebra k X V) _ (sectionRestriction k X f r) =
    (sectionRestriction k X f r) • b'.val
  rw [Algebra.smul_def]
  exact (Algebra.commutes (sectionRestriction k X f r) b'.val).symm

/-- The relative de Rham complex in nonnegative degrees. Blueprint: `def:geo-forms-sheaf`. -/
def formsComplexNat : CochainComplex (TopCat.Sheaf (ModuleCat k) X.left) ℕ :=
  CochainComplex.of (formsSheaf k X) (formsSheafD k X) (formsSheafD_comp k X)

/-- The nonnegative de Rham complex has the sheaf of forms as its term in each degree. -/
@[simp] theorem formsComplexNat_X (n : ℕ) :
    (formsComplexNat k X).X n = formsSheaf k X n := rfl

/-- The differential of the nonnegative complex is the sheaf differential. -/
@[simp] theorem formsComplexNat_d (n : ℕ) :
    (formsComplexNat k X).d n (n + 1) = formsSheafD k X n :=
  CochainComplex.of_d _ _ n

/-- The relative de Rham complex, extended by zero in negative degrees.
Blueprint: `def:geo-forms-sheaf`. -/
def formsComplex : CochainComplex (TopCat.Sheaf (ModuleCat k) X.left) ℤ :=
  (formsComplexNat k X).extend ComplexShape.embeddingUpNat

/-- In a nonnegative degree, the extended complex has the original sheaf of forms. -/
def formsComplexXIso (n : ℕ) :
    (formsComplex k X).X (n : ℤ) ≅ formsSheaf k X n :=
  (formsComplexNat k X).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

/-- The nonnegative differentials of the extended complex are the sheaf differentials,
through the canonical term isomorphisms. -/
theorem formsComplex_d (n : ℕ) :
    (formsComplex k X).d (n : ℤ) ((n : ℤ) + 1) =
      (formsComplexXIso k X n).hom ≫ formsSheafD k X n ≫
        (formsComplexXIso k X (n + 1)).inv := by
  have h := (formsComplexNat k X).extend_d_eq ComplexShape.embeddingUpNat
    (i := n) (j := n + 1) (i' := (n : ℤ)) (j' := ((n : ℤ) + 1)) rfl (by simp)
  rw [formsComplexNat_d] at h
  exact h

/-- The canonical nonnegative term comparisons commute with the differential. -/
@[reassoc (attr := simp)] theorem formsComplex_d_XIso_hom (n : ℕ) :
    (formsComplex k X).d (n : ℤ) ((n : ℤ) + 1) ≫
        (formsComplexXIso k X (n + 1)).hom =
      (formsComplexXIso k X n).hom ≫ formsSheafD k X n := by
  rw [formsComplex_d]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse nonnegative term comparisons commute with the differential. -/
@[reassoc (attr := simp)] theorem formsComplexXIso_inv_d (n : ℕ) :
    (formsComplexXIso k X n).inv ≫
        (formsComplex k X).d (n : ℤ) ((n : ℤ) + 1) =
      formsSheafD k X n ≫ (formsComplexXIso k X (n + 1)).inv := by
  rw [formsComplex_d]
  simp only [Iso.inv_hom_id_assoc]

instance formsComplex_isStrictlyGE : (formsComplex k X).IsStrictlyGE 0 := by
  dsimp only [formsComplex]
  infer_instance

/-- The relative de Rham complex has zero terms in every negative degree. -/
theorem formsComplex_isZero_of_neg (i : ℤ) (hi : i < 0) :
    CategoryTheory.Limits.IsZero ((formsComplex k X).X i) :=
  (formsComplex k X).isZero_of_isStrictlyGE 0 i hi

end OrlikSolomon.Geometric.DeRham
