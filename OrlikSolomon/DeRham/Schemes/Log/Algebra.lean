/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Basic

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Wedge products of logarithmic sheaves

The image sheaves of logarithmic forms inherit wedge multiplication from forms on the
complement. The construction descends products of local regular-plus-left-theta normal forms
through their sheaf epimorphisms. It does not assert normal forms for sections on arbitrary opens.

The canonical inclusion into complement forms characterizes multiplication and its differential,
unit, associativity, and graded sign identities. No flatness hypothesis or invertibility of `2`
is used.

The main constructions and results are:

* `logSheafMul` and `logSheafWedge`: logarithmic multiplication and its section operation;
* `logSheafWedge_logToOpenSheaf`: compatibility with the actual inclusion on the complement;
* `logSheafWedge_regular`, `logSheafWedge_theta_regular`, `logSheafWedge_regular_theta`, and
  `logSheafWedge_theta_theta`: the products of local normal-form generators;
* `logSheafWedge_assoc`, `logSheafWedge_comm`, and `logSheafWedge_leibniz`: the differential
  graded algebra identities, together with the closed unit `logSheafOneSection`.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory
open Opposite AlgebraicGeometry
open scoped MonoidalClosed.FunctorCategory
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

attribute [local instance] strongEpi_of_epi
  CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.symmetricCategory

variable {k : Type u} [CommRing k] (T : TopCat.{u})

local instance : MonoidalClosed (TopCat.Sheaf (ModuleCat.{u} k) T) :=
  Monoidal.Reflective.monoidalClosed
    (sheafificationAdjunction (_root_.Opens.grothendieckTopology T) (ModuleCat k))

local instance :
    (sheafToPresheaf (_root_.Opens.grothendieckTopology T) (ModuleCat.{u} k)).LaxMonoidal :=
  (sheafificationAdjunction (_root_.Opens.grothendieckTopology T)
    (ModuleCat k)).rightAdjointLaxMonoidal

private def tensorIso (A B : TopCat.Sheaf (ModuleCat.{u} k) T) :
    (presheafToSheaf (_root_.Opens.grothendieckTopology T) (ModuleCat k)).obj
      (A.obj ⊗ B.obj) ≅ A ⊗ B :=
  (Functor.Monoidal.μIso _ A.obj B.obj).symm ≪≫
    MonoidalCategory.tensorIso
      (asIso ((sheafificationAdjunction _ _).counit.app A))
      (asIso ((sheafificationAdjunction _ _).counit.app B))

private def tensorEquiv (A B C : TopCat.Sheaf (ModuleCat.{u} k) T) :
    (A ⊗ B ⟶ C) ≃ (A.obj ⊗ B.obj ⟶ C.obj) :=
  ((tensorIso T A B).symm.homCongr (Iso.refl C)).trans
    ((sheafificationAdjunction _ _).homEquiv _ _)

private theorem tensorEquiv_apply (A B C : TopCat.Sheaf (ModuleCat.{u} k) T) (f : A ⊗ B ⟶ C) :
    tensorEquiv T A B C f =
      Functor.LaxMonoidal.μ (sheafToPresheaf (_root_.Opens.grothendieckTopology T)
        (ModuleCat k)) A B ≫ f.hom := by
  change (sheafificationAdjunction _ _).homEquiv _ _ ((tensorIso T A B).hom ≫ f) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

local instance (A : TopCat.Sheaf (ModuleCat.{u} k) T) : (tensorRight A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight A)

private theorem tensorBiprod_hom_ext_left
    {A B C D : TopCat.Sheaf (ModuleCat.{u} k) T} {f g : (A ⊞ B) ⊗ C ⟶ D}
    (hl : (biprod.inl ⊗ₘ 𝟙 C) ≫ f = (biprod.inl ⊗ₘ 𝟙 C) ≫ g)
    (hr : (biprod.inr ⊗ₘ 𝟙 C) ≫ f = (biprod.inr ⊗ₘ 𝟙 C) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorRight C) (BinaryBiproduct.isColimit A B)).hom_ext
  rintro ⟨j⟩
  cases j with
  | left => simpa using hl
  | right => simpa using hr

private theorem tensorBiprod_hom_ext_right
    {A B C D : TopCat.Sheaf (ModuleCat.{u} k) T} {f g : A ⊗ (B ⊞ C) ⟶ D}
    (hl : (𝟙 A ⊗ₘ biprod.inl) ≫ f = (𝟙 A ⊗ₘ biprod.inl) ≫ g)
    (hr : (𝟙 A ⊗ₘ biprod.inr) ≫ f = (𝟙 A ⊗ₘ biprod.inr) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorLeft A) (BinaryBiproduct.isColimit B C)).hom_ext
  rintro ⟨j⟩
  cases j with
  | left => simpa using hl
  | right => simpa using hr

local instance (A : TopCat.Sheaf (ModuleCat.{u} k) T) : (tensorLeft A).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
  exact Functor.additive_of_preservesBinaryBiproducts _

local instance (A : TopCat.Sheaf (ModuleCat.{u} k) T) : (tensorRight A).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight A)
  exact Functor.additive_of_preservesBinaryBiproducts _

local instance : MonoidalPreadditive (TopCat.Sheaf (ModuleCat.{u} k) T) where
  whiskerLeft_zero := by intro A B C; exact (tensorLeft A).map_zero B C
  zero_whiskerRight := by intro A B C; exact (tensorRight A).map_zero B C
  whiskerLeft_add := by intro A B C f g; exact (tensorLeft A).map_add
  add_whiskerRight := by intro A B C f g; exact (tensorRight A).map_add

local instance {A B C D : TopCat.Sheaf (ModuleCat.{u} k) T} (f : A ⟶ B) (g : C ⟶ D)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  have : Epi ((tensorLeft B).map g) := (tensorLeft B).map_epi g
  have : Epi ((tensorRight C).map f) := (tensorRight C).map_epi f
  change Epi ((tensorRight C).map f ≫ (tensorLeft B).map g)
  infer_instance

variable {D : SmoothDomain k} (P : Geometric.DivisorPair D)

/-- Change the displayed degree of a logarithmic sheaf along an equality. -/
def logSheafCast {p q : ℕ} (h : p = q) : logSheaf P p ⟶ logSheaf P q :=
  eqToHom (congrArg (logSheaf P) h)

/-- Degree casts agree with the corresponding casts of forms on the complement. -/
@[reassoc] theorem logSheafCast_comp_logToOpenSheaf {p q : ℕ} (h : p = q) :
    logSheafCast P h ≫ logToOpenSheaf P q =
      logToOpenSheaf P p ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
          (formsSheafCast k P.compl.obj h) := by
  subst q
  simp only [logSheafCast, formsSheafCast, eqToHom_refl, Category.id_comp,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- Logarithmic inclusion is injective on sections of every open. -/
theorem logToOpenSheaf_app_injective (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    Function.Injective ((logToOpenSheaf P n).hom.app U) := by
  have : Mono ((sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left)
      (ModuleCat k)).map (logToOpenSheaf P n)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1
    (inferInstance : Mono (((sheafToPresheaf _ _).map (logToOpenSheaf P n)).app U))

/-- The left logarithmic summand of the local normal-form epimorphism. -/
def thetaToLogSheaf (n : ℕ) : formsSheaf k P.ambient.obj n ⟶ logSheaf P (n + 1) :=
  biprod.inr ≫ logMkSheaf P n

/-- The logarithmic summand includes as left multiplication by `df/f` after restriction. -/
@[reassoc (attr := simp)] theorem thetaToLogSheaf_comp_logToOpenSheaf (n : ℕ) :
    thetaToLogSheaf P n ≫ logToOpenSheaf P (n + 1) =
      formsSheafPullback P.j.hom n ≫ openThetaWedgeSheaf P n := by
  rw [thetaToLogSheaf, Category.assoc, logMkSheaf_comp_logToOpenSheaf,
    inr_logNormalFormSheaf]
  rfl

private def formsMulSheaf (X : Over (Spec (CommRingCat.of k))) (p q : ℕ) :
    formsSheaf k X p ⊗ formsSheaf k X q ⟶ formsSheaf k X (p + q) :=
  (tensorEquiv X.left _ _ _).symm (formsSheafMul k X p q)

private def openMulSheaf (p q : ℕ) :
    openFormsSheaf P p ⊗ openFormsSheaf P q ⟶ openFormsSheaf P (p + q) :=
  (tensorEquiv P.ambient.obj.left _ _ _).symm
    (Functor.whiskerLeft (TopologicalSpace.Opens.map P.j.hom.left.base).op
      (formsSheafMul k P.compl.obj p q))

private theorem tensorEquiv_comp_right {A B C E : TopCat.Sheaf (ModuleCat.{u} k) T}
    (f : A ⊗ B ⟶ C) (g : C ⟶ E) :
    tensorEquiv T A B E (f ≫ g) = tensorEquiv T A B C f ≫ g.hom := by
  simp only [tensorEquiv_apply]
  rfl

private theorem tensorEquiv_precomp {A B A' B' C : TopCat.Sheaf (ModuleCat.{u} k) T}
    (f : A ⟶ A') (g : B ⟶ B') (h : A' ⊗ B' ⟶ C) :
    tensorEquiv T A B C ((f ⊗ₘ g) ≫ h) =
      (f.hom ⊗ₘ g.hom) ≫ tensorEquiv T A' B' C h := by
  simp only [tensorEquiv_apply]
  change _ ≫ ((sheafToPresheaf _ _).map (f ⊗ₘ g) ≫ h.hom) = _
  exact (Functor.LaxMonoidal.μ_natural_assoc
    (sheafToPresheaf (_root_.Opens.grothendieckTopology T) (ModuleCat k)) f g _).symm

private theorem tensorEquiv_zsmul {A B C : TopCat.Sheaf (ModuleCat.{u} k) T}
    (n : ℤ) (f : A ⊗ B ⟶ C) :
    tensorEquiv T A B C (n • f) = n • tensorEquiv T A B C f := by
  simp only [tensorEquiv_apply]
  exact comp_zsmul _ _ _

private theorem tensorEquiv_zero (A B C : TopCat.Sheaf (ModuleCat.{u} k) T) :
    tensorEquiv T A B C 0 = 0 := by
  rw [tensorEquiv_apply]
  exact comp_zero

private theorem tensorEquiv_formsMulSheaf (X : Over (Spec (CommRingCat.of k))) (p q : ℕ) :
    tensorEquiv X.left _ _ _ (formsMulSheaf X p q) = formsSheafMul k X p q :=
  Equiv.apply_symm_apply _ _

private theorem tensorEquiv_openMulSheaf (p q : ℕ) :
    tensorEquiv P.ambient.obj.left
      ((TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).obj
        (formsSheaf k P.compl.obj p))
      ((TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).obj
        (formsSheaf k P.compl.obj q))
      ((TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).obj
        (formsSheaf k P.compl.obj (p + q))) (openMulSheaf P p q) =
      Functor.whiskerLeft (TopologicalSpace.Opens.map P.j.hom.left.base).op
        (formsSheafMul k P.compl.obj p q) :=
  Equiv.apply_symm_apply _ _

private def regularProduct (p q : ℕ) :
    formsSheaf k P.ambient.obj p ⊗ formsSheaf k P.ambient.obj q ⟶ logSheaf P (p + q) :=
  formsMulSheaf P.ambient.obj p q ≫ regularToLogSheaf P (p + q)

private def thetaRegularProduct (p q : ℕ) :
    formsSheaf k P.ambient.obj p ⊗ formsSheaf k P.ambient.obj q ⟶ logSheaf P (p + 1 + q) :=
  formsMulSheaf P.ambient.obj p q ≫ thetaToLogSheaf P (p + q) ≫
    logSheafCast P (by omega)

private def regularThetaProduct (p q : ℕ) :
    formsSheaf k P.ambient.obj p ⊗ formsSheaf k P.ambient.obj q ⟶ logSheaf P (p + (q + 1)) :=
  (p : ℤ).negOnePow • (formsMulSheaf P.ambient.obj p q ≫ thetaToLogSheaf P (p + q) ≫
    logSheafCast P (by omega))

set_option backward.isDefEq.respectTransparency false in
private theorem regularProduct_inclusion (p q : ℕ) :
    regularProduct P p q ≫ logToOpenSheaf P (p + q) =
      (formsSheafPullback P.j.hom p ⊗ₘ formsSheafPullback P.j.hom q) ≫
        openMulSheaf P p q := by
  apply (tensorEquiv P.ambient.obj.left _ _ _).injective
  rw [regularProduct, Category.assoc, regularToLogSheaf_comp_logToOpenSheaf,
    tensorEquiv_precomp]
  dsimp only [openFormsSheaf]
  rw [tensorEquiv_openMulSheaf (P := P) p q, tensorEquiv_comp_right,
    tensorEquiv_formsMulSheaf]
  exact formsSheafPullback_mul P.j.hom p q

set_option backward.isDefEq.respectTransparency false in
private theorem thetaRegularProduct_inclusion (p q : ℕ) :
    thetaRegularProduct P p q ≫ logToOpenSheaf P (p + 1 + q) =
      ((formsSheafPullback P.j.hom p ≫ openThetaWedgeSheaf P p) ⊗ₘ
        formsSheafPullback P.j.hom q) ≫ openMulSheaf P (p + 1) q := by
  apply (tensorEquiv P.ambient.obj.left _ _ _).injective
  simp only [thetaRegularProduct, Category.assoc, logSheafCast_comp_logToOpenSheaf,
    thetaToLogSheaf_comp_logToOpenSheaf_assoc]
  rw [tensorEquiv_precomp]
  dsimp only [openFormsSheaf]
  rw [tensorEquiv_openMulSheaf (P := P) (p + 1) q, tensorEquiv_comp_right,
    tensorEquiv_formsMulSheaf]
  apply formsSheaf_tensor_hom_ext k P.ambient.obj p q (openFormsSheaf P (p + 1 + q))
  intro U a b
  change (formsSheafCast k P.compl.obj (by omega : p + q + 1 = p + 1 + q)).hom.app
      (op (P.j.hom.left ⁻¹ᵁ U.unop))
      ((thetaWedgeSheaf P.compl.obj P.eqnUnit (p + q)).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom (p + q)).hom.app U
          (formsSheafWedge k P.ambient.obj p q U ((formsSheafUnit k P.ambient.obj p).app U a)
            ((formsSheafUnit k P.ambient.obj q).app U b)))) =
    formsSheafWedge k P.compl.obj (p + 1) q (op (P.j.hom.left ⁻¹ᵁ U.unop))
      ((thetaWedgeSheaf P.compl.obj P.eqnUnit p).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom p).hom.app U ((formsSheafUnit k P.ambient.obj p).app U a)))
      ((formsSheafPullback P.j.hom q).hom.app U ((formsSheafUnit k P.ambient.obj q).app U b))
  rw [formsSheafWedge_unit, formsSheafPullback_unit_apply, formsSheafPullback_unit_apply,
    formsSheafPullback_unit_apply, thetaWedgeSheaf_unit, thetaWedgeSheaf_unit,
    formsSheafWedge_unit, formsSheafCast_unit_apply]
  congr 1
  apply Subtype.ext
  let φ := sectionPullback P.j.hom U.unop
  let v := Units.map
    (sectionRestriction k P.compl.obj (P.j.hom.left ⁻¹ᵁ U.unop).leTop).toMonoidHom P.eqnUnit
  let a' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^p
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^q
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := b
  change ((formsPresheafCast k P.compl.obj (by omega : p + q + 1 = p + 1 + q)).app _
    ⟨dlog k v * Forms.map φ (a'.val * b'.val), _⟩).val =
      (dlog k v * Forms.map φ a'.val) * Forms.map φ b'.val
  rw [formsPresheafCast_val]
  change dlog k v * Forms.map φ (a'.val * b'.val) =
    (dlog k v * Forms.map φ a'.val) * Forms.map φ b'.val
  rw [map_mul, mul_assoc]

private theorem mul_dlog {A : Type u} [CommRing A] [Algebra k A]
    (v : Aˣ) (x : Forms k A) : x * dlog k v = dlog k v * CliffordAlgebra.involute x := by
  rw [dlog_apply, smul_mul_assoc, mul_smul_comm, diff_apply,
    ι_mul_eq_involute_mul _ (CliffordAlgebra.involute x),
    CliffordAlgebra.involute_involute]

set_option backward.isDefEq.respectTransparency false in
private theorem regularThetaProduct_inclusion (p q : ℕ) :
    regularThetaProduct P p q ≫ logToOpenSheaf P (p + (q + 1)) =
      (formsSheafPullback P.j.hom p ⊗ₘ
        (formsSheafPullback P.j.hom q ≫ openThetaWedgeSheaf P q)) ≫
          openMulSheaf P p (q + 1) := by
  apply (tensorEquiv P.ambient.obj.left _ _ _).injective
  simp only [regularThetaProduct, Units.smul_def, zsmul_comp, Category.assoc,
    logSheafCast_comp_logToOpenSheaf, thetaToLogSheaf_comp_logToOpenSheaf_assoc]
  rw [tensorEquiv_zsmul, tensorEquiv_precomp]
  dsimp only [openFormsSheaf]
  rw [tensorEquiv_openMulSheaf (P := P) p (q + 1), tensorEquiv_comp_right,
    tensorEquiv_formsMulSheaf]
  apply formsSheaf_tensor_hom_ext k P.ambient.obj p q (openFormsSheaf P (p + (q + 1)))
  intro U a b
  change (p : ℤ).negOnePow •
      (formsSheafCast k P.compl.obj (by omega : p + q + 1 = p + (q + 1))).hom.app
        (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((thetaWedgeSheaf P.compl.obj P.eqnUnit (p + q)).hom.app
          (op (P.j.hom.left ⁻¹ᵁ U.unop))
          ((formsSheafPullback P.j.hom (p + q)).hom.app U
            (formsSheafWedge k P.ambient.obj p q U
              ((formsSheafUnit k P.ambient.obj p).app U a)
              ((formsSheafUnit k P.ambient.obj q).app U b)))) =
    formsSheafWedge k P.compl.obj p (q + 1) (op (P.j.hom.left ⁻¹ᵁ U.unop))
      ((formsSheafPullback P.j.hom p).hom.app U ((formsSheafUnit k P.ambient.obj p).app U a))
      ((thetaWedgeSheaf P.compl.obj P.eqnUnit q).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom q).hom.app U ((formsSheafUnit k P.ambient.obj q).app U b)))
  rw [formsSheafWedge_unit, formsSheafPullback_unit_apply, formsSheafPullback_unit_apply,
    formsSheafPullback_unit_apply, thetaWedgeSheaf_unit, thetaWedgeSheaf_unit,
    formsSheafWedge_unit, formsSheafCast_unit_apply, ← map_zsmul_unit]
  congr 1
  apply Subtype.ext
  let φ := sectionPullback P.j.hom U.unop
  let v := Units.map
    (sectionRestriction k P.compl.obj (P.j.hom.left ⁻¹ᵁ U.unop).leTop).toMonoidHom P.eqnUnit
  let a' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^p
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^q
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := b
  change (p : ℤ).negOnePow •
      ((formsPresheafCast k P.compl.obj (by omega : p + q + 1 = p + (q + 1))).app _
        ⟨dlog k v * Forms.map φ (a'.val * b'.val), _⟩).val =
    Forms.map φ a'.val * (dlog k v * Forms.map φ b'.val)
  rw [formsPresheafCast_val]
  change (p : ℤ).negOnePow • (dlog k v * Forms.map φ (a'.val * b'.val)) =
    Forms.map φ a'.val * (dlog k v * Forms.map φ b'.val)
  rw [map_mul]
  symm
  rw [← mul_assoc, mul_dlog,
    involute_of_mem_exteriorPower (Forms.map_mem_exteriorPower φ a'.property),
    mul_smul_comm, smul_mul_assoc, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem thetaThetaProduct_zero (p q : ℕ) :
    ((formsSheafPullback P.j.hom p ≫ openThetaWedgeSheaf P p) ⊗ₘ
        (formsSheafPullback P.j.hom q ≫ openThetaWedgeSheaf P q)) ≫
      openMulSheaf P (p + 1) (q + 1) = 0 := by
  apply (tensorEquiv P.ambient.obj.left _ _ _).injective
  rw [tensorEquiv_precomp, tensorEquiv_zero]
  dsimp only [openFormsSheaf]
  rw [tensorEquiv_openMulSheaf (P := P) (p + 1) (q + 1)]
  apply formsSheaf_tensor_hom_ext k P.ambient.obj p q
    (openFormsSheaf P (p + 1 + (q + 1)))
  intro U a b
  change formsSheafWedge k P.compl.obj (p + 1) (q + 1) (op (P.j.hom.left ⁻¹ᵁ U.unop))
      ((thetaWedgeSheaf P.compl.obj P.eqnUnit p).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom p).hom.app U ((formsSheafUnit k P.ambient.obj p).app U a)))
      ((thetaWedgeSheaf P.compl.obj P.eqnUnit q).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom q).hom.app U ((formsSheafUnit k P.ambient.obj q).app U b))) = 0
  rw [formsSheafPullback_unit_apply, formsSheafPullback_unit_apply,
    thetaWedgeSheaf_unit, thetaWedgeSheaf_unit, formsSheafWedge_unit]
  rw [← map_zero ((formsSheafUnit k P.compl.obj (p + 1 + (q + 1))).app
    (op (P.j.hom.left ⁻¹ᵁ U.unop))).hom]
  congr 1
  apply Subtype.ext
  let φ := sectionPullback P.j.hom U.unop
  let v := Units.map
    (sectionRestriction k P.compl.obj (P.j.hom.left ⁻¹ᵁ U.unop).leTop).toMonoidHom P.eqnUnit
  let a' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^p
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := a
  let b' : ⋀[sectionAlgebra k P.ambient.obj U.unop]^q
      Ω[sectionAlgebra k P.ambient.obj U.unop⁄k] := b
  change (dlog k v * Forms.map φ a'.val) * (dlog k v * Forms.map φ b'.val) = 0
  rw [mul_assoc, ← mul_assoc (Forms.map φ a'.val), mul_dlog, mul_assoc,
    ← mul_assoc (dlog k v), dlog_mul_self, zero_mul]

private def logCoverSheaf : ℕ → TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left
  | 0 => formsSheaf k P.ambient.obj 0
  | n + 1 => formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n

private def logCoverToLog : (n : ℕ) → logCoverSheaf P n ⟶ logSheaf P n
  | 0 => regularToLogSheaf P 0
  | n + 1 => logMkSheaf P n

private instance logCoverToLog_epi (n : ℕ) : Epi (logCoverToLog P n) := by
  cases n with
  | zero => exact regularToLogSheaf_zero_epi (P := P)
  | succ n => exact logMkSheaf_epi (P := P) n

private def logCoverToOpen (n : ℕ) : logCoverSheaf P n ⟶ openFormsSheaf P n :=
  logCoverToLog P n ≫ logToOpenSheaf P n

private def normalProduct : (p q : ℕ) →
    logCoverSheaf P p ⊗ logCoverSheaf P q ⟶ logSheaf P (p + q)
  | 0, 0 => regularProduct P 0 0
  | 0, q + 1 =>
      (𝟙 _ ⊗ₘ biprod.fst) ≫ regularProduct P 0 (q + 1) +
        (𝟙 _ ⊗ₘ biprod.snd) ≫ regularThetaProduct P 0 q
  | p + 1, 0 =>
      (biprod.fst ⊗ₘ 𝟙 _) ≫ regularProduct P (p + 1) 0 +
        (biprod.snd ⊗ₘ 𝟙 _) ≫ thetaRegularProduct P p 0
  | p + 1, q + 1 =>
      (biprod.fst ⊗ₘ biprod.fst) ≫ regularProduct P (p + 1) (q + 1) +
        (biprod.snd ⊗ₘ biprod.fst) ≫ thetaRegularProduct P p (q + 1) +
          (biprod.fst ⊗ₘ biprod.snd) ≫ regularThetaProduct P (p + 1) q

set_option backward.isDefEq.respectTransparency false in
private theorem normalProduct_inclusion (p q : ℕ) :
    normalProduct P p q ≫ logToOpenSheaf P (p + q) =
      (logCoverToOpen P p ⊗ₘ logCoverToOpen P q) ≫ openMulSheaf P p q := by
  cases p with
  | zero =>
    cases q with
    | zero =>
        simpa [normalProduct, logCoverToOpen, logCoverToLog]
          using regularProduct_inclusion (P := P) 0 0
    | succ q =>
      apply tensorBiprod_hom_ext_right
      · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
          using regularProduct_inclusion (P := P) 0 (q + 1)
      · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
          using regularThetaProduct_inclusion (P := P) 0 q
  | succ p =>
    cases q with
    | zero =>
      apply tensorBiprod_hom_ext_left
      · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
          using regularProduct_inclusion (P := P) (p + 1) 0
      · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
          using thetaRegularProduct_inclusion (P := P) p 0
    | succ q =>
      apply tensorBiprod_hom_ext_left
      · apply tensorBiprod_hom_ext_right
        · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
            using regularProduct_inclusion (P := P) (p + 1) (q + 1)
        · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
            using regularThetaProduct_inclusion (P := P) (p + 1) q
      · apply tensorBiprod_hom_ext_right
        · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
            using thetaRegularProduct_inclusion (P := P) p (q + 1)
        · simpa [normalProduct, logCoverSheaf, logCoverToOpen, logCoverToLog, Category.assoc,
          -id_tensorHom, -tensorHom_id, id_tensorHom_id, openThetaWedgeSheaf]
            using (thetaThetaProduct_zero (P := P) p q).symm

private theorem logProductSquare (p q : ℕ) :
    CommSq (normalProduct P p q) (logCoverToLog P p ⊗ₘ logCoverToLog P q)
      (logToOpenSheaf P (p + q))
      ((logToOpenSheaf P p ⊗ₘ logToOpenSheaf P q) ≫ openMulSheaf P p q) where
  w := by
    simpa only [logCoverToOpen, tensorHom_comp_tensorHom_assoc] using
      normalProduct_inclusion (P := P) p q

private def logMulSheaf (p q : ℕ) : logSheaf P p ⊗ logSheaf P q ⟶ logSheaf P (p + q) :=
  (logProductSquare P p q).lift

/-- Wedge multiplication on the existing logarithmic sheaves. The construction descends local
normal forms through sheaf epimorphisms; it does not choose normal forms on arbitrary opens.

Blueprint: `thm:geo-log-sheaves`. -/
@[no_expose] def logSheafMul (p q : ℕ) :
    (logSheaf P p).obj ⊗ (logSheaf P q).obj ⟶ (logSheaf P (p + q)).obj :=
  tensorEquiv P.ambient.obj.left _ _ _ (logMulSheaf P p q)

/-- Logarithmic multiplication is the restriction of the actual wedge product on complement
forms, under the canonical inclusions. -/
theorem logSheafMul_logToOpenSheaf (p q : ℕ) :
    logSheafMul P p q ≫ (logToOpenSheaf P (p + q)).hom =
      ((logToOpenSheaf P p).hom ⊗ₘ (logToOpenSheaf P q).hom) ≫
        Functor.whiskerLeft (TopologicalSpace.Opens.map P.j.hom.left.base).op
          (formsSheafMul k P.compl.obj p q) := by
  rw [logSheafMul, ← tensorEquiv_comp_right, logMulSheaf, CommSq.fac_right,
    tensorEquiv_precomp]
  dsimp only [openFormsSheaf]
  rw [tensorEquiv_openMulSheaf (P := P) p q]
  rfl

/-- The section-level wedge product of logarithmic forms on an ambient open. -/
def logSheafWedge (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    (logSheaf P (p + q)).obj.obj U :=
  (logSheafMul P p q).app U (a ⊗ₜ[k] b)

/-- The section-level logarithmic wedge product is bilinear over the base ring. -/
def logSheafWedgeLinear (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logSheaf P p).obj.obj U →ₗ[k]
      (logSheaf P q).obj.obj U →ₗ[k] (logSheaf P (p + q)).obj.obj U :=
  LinearMap.compr₂ (TensorProduct.mk k _ _) ((logSheafMul P p q).app U).hom

/-- Evaluation of the bilinear product is the original wedge operation. -/
@[simp] theorem logSheafWedgeLinear_apply (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    logSheafWedgeLinear P p q U a b = logSheafWedge P p q U a b := rfl

/-- The logarithmic wedge product vanishes when its left factor is zero. -/
@[simp] theorem logSheafWedge_zero_left (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (b : (logSheaf P q).obj.obj U) : logSheafWedge P p q U 0 b = 0 := by
  exact LinearMap.congr_fun ((logSheafWedgeLinear P p q U).map_zero) b

/-- The logarithmic wedge product vanishes when its right factor is zero. -/
@[simp] theorem logSheafWedge_zero_right (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) : logSheafWedge P p q U a 0 = 0 := by
  exact (logSheafWedgeLinear P p q U a).map_zero

/-- The logarithmic wedge product is additive in its left factor. -/
@[simp] theorem logSheafWedge_add_left (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a a' : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    logSheafWedge P p q U (a + a') b =
      logSheafWedge P p q U a b + logSheafWedge P p q U a' b := by
  exact LinearMap.congr_fun ((logSheafWedgeLinear P p q U).map_add a a') b

/-- The logarithmic wedge product is additive in its right factor. -/
@[simp] theorem logSheafWedge_add_right (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b b' : (logSheaf P q).obj.obj U) :
    logSheafWedge P p q U a (b + b') =
      logSheafWedge P p q U a b + logSheafWedge P p q U a b' := by
  exact (logSheafWedgeLinear P p q U a).map_add b b'

/-- Base scalars can be moved through the left logarithmic wedge factor. -/
@[simp] theorem logSheafWedge_smul_left (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (c : k) (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    logSheafWedge P p q U (c • a) b = c • logSheafWedge P p q U a b := by
  exact LinearMap.congr_fun ((logSheafWedgeLinear P p q U).map_smul c a) b

/-- Base scalars can be moved through the right logarithmic wedge factor. -/
@[simp] theorem logSheafWedge_smul_right (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (c : k) (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    logSheafWedge P p q U a (c • b) = c • logSheafWedge P p q U a b := by
  exact (logSheafWedgeLinear P p q U a).map_smul c b

/-- On sections, logarithmic inclusion takes the product to the ordinary wedge product on the
inverse-image open in the complement. -/
@[simp] theorem logSheafWedge_logToOpenSheaf (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    (logToOpenSheaf P (p + q)).hom.app U (logSheafWedge P p q U a b) =
      formsSheafWedge k P.compl.obj p q (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((logToOpenSheaf P p).hom.app U a) ((logToOpenSheaf P q).hom.app U b) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (logSheafMul_logToOpenSheaf P p q) U)
    (a ⊗ₜ[k] b)

/-- The degree-zero logarithmic unit is the image of the regular unit. -/
def logSheafOneSection (U : P.ambient.obj.left.Opensᵒᵖ) : (logSheaf P 0).obj.obj U :=
  (regularToLogSheaf P 0).hom.app U (formsSheafOneSection k P.ambient.obj U)

/-- The logarithmic unit section commutes with restriction to smaller opens. -/
@[simp] theorem logSheafOneSection_naturality {U V : P.ambient.obj.left.Opensᵒᵖ}
    (i : U ⟶ V) :
    (logSheaf P 0).obj.map i (logSheafOneSection P U) = logSheafOneSection P V := by
  have h := ConcreteCategory.congr_hom ((regularToLogSheaf P 0).hom.naturality i)
    (formsSheafOneSection k P.ambient.obj U)
  simp only [ModuleCat.comp_apply, formsSheafOneSection_naturality] at h
  exact h.symm

/-- On sections, regular inclusion followed by logarithmic inclusion is ordinary pullback. -/
@[simp] theorem regularToLogSheaf_logToOpenSheaf (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    (logToOpenSheaf P n).hom.app U ((regularToLogSheaf P n).hom.app U a) =
      (formsSheafPullback P.j.hom n).hom.app U a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (regularToLogSheaf_comp_logToOpenSheaf P n)) U) a

/-- The logarithmic generator includes as left multiplication by `df/f`, on sections. -/
@[simp] theorem thetaToLogSheaf_logToOpenSheaf (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    (logToOpenSheaf P (n + 1)).hom.app U ((thetaToLogSheaf P n).hom.app U a) =
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback P.j.hom n).hom.app U a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (thetaToLogSheaf_comp_logToOpenSheaf P n)) U) a

/-- On sections, degree casts commute with logarithmic inclusion. -/
@[simp] theorem logSheafCast_logToOpenSheaf {p q : ℕ} (h : p = q)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (logSheaf P p).obj.obj U) :
    (logToOpenSheaf P q).hom.app U ((logSheafCast P h).hom.app U a) =
      (formsSheafCast k P.compl.obj h).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((logToOpenSheaf P p).hom.app U a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (logSheafCast_comp_logToOpenSheaf P h)) U) a

/-- The logarithmic differential is the ordinary differential after inclusion, on sections. -/
@[simp] theorem logSheafD_logToOpenSheaf (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P n).obj.obj U) :
    (logToOpenSheaf P (n + 1)).hom.app U ((logSheafD P n).hom.app U a) =
      (formsSheafD k P.compl.obj n).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        ((logToOpenSheaf P n).hom.app U a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (logSheafD_comp_logToOpenSheaf P n)) U) a

/-- Logarithmic inclusion preserves the unit section. -/
@[simp] theorem logSheafOneSection_logToOpenSheaf (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logToOpenSheaf P 0).hom.app U (logSheafOneSection P U) =
      formsSheafOneSection k P.compl.obj (op (P.j.hom.left ⁻¹ᵁ U.unop)) := by
  rw [logSheafOneSection, regularToLogSheaf_logToOpenSheaf]
  exact formsSheafPullback_one P.j.hom U

/-- The logarithmic wedge product commutes with restriction to smaller ambient opens. -/
theorem logSheafWedge_naturality (p q : ℕ) {U V : P.ambient.obj.left.Opensᵒᵖ} (i : U ⟶ V)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    (logSheaf P (p + q)).obj.map i (logSheafWedge P p q U a b) =
      logSheafWedge P p q V ((logSheaf P p).obj.map i a) ((logSheaf P q).obj.map i b) :=
  (ConcreteCategory.congr_hom ((logSheafMul P p q).naturality i) (a ⊗ₜ[k] b)).symm

/-- Regular inclusion preserves wedge products. -/
theorem logSheafWedge_regular (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj p).obj.obj U)
    (b : (formsSheaf k P.ambient.obj q).obj.obj U) :
    logSheafWedge P p q U ((regularToLogSheaf P p).hom.app U a)
        ((regularToLogSheaf P q).hom.app U b) =
      (regularToLogSheaf P (p + q)).hom.app U (formsSheafWedge k P.ambient.obj p q U a b) := by
  apply logToOpenSheaf_app_injective P (p + q) U
  simp only [logSheafWedge_logToOpenSheaf, regularToLogSheaf_logToOpenSheaf]
  exact (formsSheafPullback_wedge P.j.hom p q U a b).symm

/-- A left logarithmic generator times a regular form is the generator of their regular
wedge product, with the canonical degree cast. -/
theorem logSheafWedge_theta_regular (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj p).obj.obj U)
    (b : (formsSheaf k P.ambient.obj q).obj.obj U) :
    logSheafWedge P (p + 1) q U ((thetaToLogSheaf P p).hom.app U a)
        ((regularToLogSheaf P q).hom.app U b) =
      (logSheafCast P (by omega : p + q + 1 = p + 1 + q)).hom.app U
        ((thetaToLogSheaf P (p + q)).hom.app U (formsSheafWedge k P.ambient.obj p q U a b)) := by
  apply logToOpenSheaf_app_injective P (p + 1 + q) U
  rw [logSheafWedge_logToOpenSheaf, thetaToLogSheaf_logToOpenSheaf,
    regularToLogSheaf_logToOpenSheaf]
  have h := congrArg (tensorEquiv P.ambient.obj.left _ _ _)
    (thetaRegularProduct_inclusion (P := P) p q)
  rw [tensorEquiv_precomp] at h
  dsimp only [openFormsSheaf] at h
  rw [tensorEquiv_openMulSheaf (P := P) (p + 1) q, thetaRegularProduct,
    Category.assoc, tensorEquiv_comp_right, tensorEquiv_formsMulSheaf] at h
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h U) (a ⊗ₜ[k] b)).symm

/-- A regular form of degree `p` moves past the logarithmic generator with sign `(-1)^p`. -/
theorem logSheafWedge_regular_theta (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj p).obj.obj U)
    (b : (formsSheaf k P.ambient.obj q).obj.obj U) :
    logSheafWedge P p (q + 1) U ((regularToLogSheaf P p).hom.app U a)
        ((thetaToLogSheaf P q).hom.app U b) =
      (p : ℤ).negOnePow •
        (logSheafCast P (by omega : p + q + 1 = p + (q + 1))).hom.app U
          ((thetaToLogSheaf P (p + q)).hom.app U
            (formsSheafWedge k P.ambient.obj p q U a b)) := by
  apply logToOpenSheaf_app_injective P (p + (q + 1)) U
  rw [logSheafWedge_logToOpenSheaf, thetaToLogSheaf_logToOpenSheaf,
    regularToLogSheaf_logToOpenSheaf, map_zsmul_unit]
  have h := congrArg (tensorEquiv P.ambient.obj.left _ _ _)
    (regularThetaProduct_inclusion (P := P) p q)
  rw [tensorEquiv_precomp] at h
  dsimp only [openFormsSheaf] at h
  rw [tensorEquiv_openMulSheaf (P := P) p (q + 1), regularThetaProduct,
    Units.smul_def, zsmul_comp, tensorEquiv_zsmul, Category.assoc,
    tensorEquiv_comp_right, tensorEquiv_formsMulSheaf] at h
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h U) (a ⊗ₜ[k] b)).symm

/-- Two logarithmic generators have zero product, over every commutative base ring. -/
@[simp] theorem logSheafWedge_theta_theta (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj p).obj.obj U)
    (b : (formsSheaf k P.ambient.obj q).obj.obj U) :
    logSheafWedge P (p + 1) (q + 1) U ((thetaToLogSheaf P p).hom.app U a)
        ((thetaToLogSheaf P q).hom.app U b) = 0 := by
  apply logToOpenSheaf_app_injective P (p + 1 + (q + 1)) U
  rw [logSheafWedge_logToOpenSheaf, thetaToLogSheaf_logToOpenSheaf,
    thetaToLogSheaf_logToOpenSheaf]
  have h := congrArg (tensorEquiv P.ambient.obj.left _ _ _)
    (thetaThetaProduct_zero (P := P) p q)
  rw [tensorEquiv_precomp, tensorEquiv_zero] at h
  dsimp only [openFormsSheaf] at h
  rw [tensorEquiv_openMulSheaf (P := P) (p + 1) (q + 1)] at h
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h U) (a ⊗ₜ[k] b)).trans
    (map_zero (((logToOpenSheaf P (p + 1 + (q + 1))).hom.app U).hom)).symm

/-- Logarithmic wedge products are associative with the canonical change of degree. -/
theorem logSheafWedge_assoc (p q r : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U)
    (c : (logSheaf P r).obj.obj U) :
    (logSheafCast P (Nat.add_assoc p q r)).hom.app U
        (logSheafWedge P (p + q) r U (logSheafWedge P p q U a b) c) =
      logSheafWedge P p (q + r) U a (logSheafWedge P q r U b c) := by
  apply logToOpenSheaf_app_injective P (p + (q + r)) U
  simp only [logSheafCast_logToOpenSheaf, logSheafWedge_logToOpenSheaf]
  exact formsSheafWedge_assoc k P.compl.obj p q r _ _ _ _

/-- Logarithmic wedge products are graded commutative, with no assumption on `2`. -/
theorem logSheafWedge_comm (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    (logSheafCast P (Nat.add_comm p q)).hom.app U (logSheafWedge P p q U a b) =
      ((p : ℤ) * q).negOnePow • logSheafWedge P q p U b a := by
  apply logToOpenSheaf_app_injective P (q + p) U
  simp only [logSheafCast_logToOpenSheaf, logSheafWedge_logToOpenSheaf, map_zsmul_unit]
  exact formsSheafWedge_comm k P.compl.obj p q _ _ _

/-- The logarithmic differential satisfies the signed Leibniz rule. -/
theorem logSheafWedge_leibniz (p q : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P p).obj.obj U) (b : (logSheaf P q).obj.obj U) :
    (logSheafCast P (by omega : p + q + 1 = p + (q + 1))).hom.app U
        ((logSheafD P (p + q)).hom.app U (logSheafWedge P p q U a b)) =
      (logSheafCast P (by omega : p + 1 + q = p + (q + 1))).hom.app U
          (logSheafWedge P (p + 1) q U ((logSheafD P p).hom.app U a) b) +
        (p : ℤ).negOnePow •
          logSheafWedge P p (q + 1) U a ((logSheafD P q).hom.app U b) := by
  apply logToOpenSheaf_app_injective P (p + (q + 1)) U
  simp only [logSheafCast_logToOpenSheaf, logSheafD_logToOpenSheaf,
    logSheafWedge_logToOpenSheaf, map_add, map_zsmul_unit]
  exact formsSheafWedge_leibniz k P.compl.obj p q _ _ _

/-- The logarithmic unit is a left unit. -/
@[simp] theorem logSheafWedge_one_left (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P n).obj.obj U) :
    (logSheafCast P (Nat.zero_add n)).hom.app U
        (logSheafWedge P 0 n U (logSheafOneSection P U) a) = a := by
  apply logToOpenSheaf_app_injective P n U
  simp only [logSheafCast_logToOpenSheaf, logSheafWedge_logToOpenSheaf,
    logSheafOneSection_logToOpenSheaf]
  exact formsSheafWedge_one_left k P.compl.obj n _ _

/-- The logarithmic unit is a right unit. -/
@[simp] theorem logSheafWedge_one_right (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf P n).obj.obj U) :
    logSheafWedge P n 0 U a (logSheafOneSection P U) = a := by
  apply logToOpenSheaf_app_injective P n U
  have h := logSheafWedge_logToOpenSheaf P n 0 U a (logSheafOneSection P U)
  simp only [Nat.add_zero] at h
  rw [h, logSheafOneSection_logToOpenSheaf]
  exact formsSheafWedge_one_right k P.compl.obj n _ _

/-- The logarithmic unit is closed for the differential. -/
@[simp] theorem logSheafOneSection_d (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logSheafD P 0).hom.app U (logSheafOneSection P U) = 0 := by
  apply logToOpenSheaf_app_injective P 1 U
  rw [logSheafD_logToOpenSheaf, logSheafOneSection_logToOpenSheaf]
  exact (formsSheafOneSection_d k P.compl.obj _).trans (map_zero _).symm

end OrlikSolomon.Geometric.DeRham
