/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Schemes.ModuleGluing
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import OrlikSolomon.DeRham.Log.Basic
public import OrlikSolomon.DeRham.Schemes.Log.Basic
public import OrlikSolomon.DeRham.Schemes.GlobalSections
public import OrlikSolomon.DeRham.Schemes.Forms.Associated
public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Duality
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Associated sheaves of affine logarithmic forms

The associated module sheaf functor takes injective and surjective module maps to
monomorphisms and epimorphisms. Applying this to the algebraic regular-plus-logarithmic
normal form identifies its associated image with the geometric logarithmic sheaf.
This proves the comparison on spectra without asserting that global sections preserve
arbitrary images. Degree zero is treated using surjectivity of regular logarithmic forms.
The image comparison also transports along exact isomorphisms of principal pairs.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
noncomputable section
namespace OrlikSolomon.Geometric.DeRham
open OrlikSolomon.DeRham
variable {k : Type u} [CommRing k] {A : CommRingCat.{u}} [Algebra k A]
/-- The associated module sheaf on an affine spectrum, regarded as a sheaf of base modules. -/
@[implicit_reducible]
def affineAssociatedSheafFunctor : ModuleCat.{u} A ⥤
    TopCat.Sheaf (ModuleCat.{u} k) (Spec A) :=
  tilde.functor A ⋙ modulesSpecToSheaf ⋙
    sheafCompose _ (ModuleCat.restrictScalars (algebraMap k A))

private lemma associatedBase_map_basicOpen_injective {M N : ModuleCat A} (f : M ⟶ N)
    (hf : Function.Injective f) (a : A) :
    Function.Injective (((affineAssociatedSheafFunctor (k := k) (A := A)).map f).hom.app
      (op (PrimeSpectrum.basicOpen a))) :=
  tilde_map_basicOpen_injective f hf a

private lemma associatedBase_map_basicOpen_surjective {M N : ModuleCat A} (f : M ⟶ N)
    (hf : Function.Surjective f) (a : A) :
    Function.Surjective (((affineAssociatedSheafFunctor (k := k) (A := A)).map f).hom.app
      (op (PrimeSpectrum.basicOpen a))) := by
  change Function.Surjective (((modulesSpecToSheaf.map (tilde.map f)).hom.app
    (op (PrimeSpectrum.basicOpen a))).hom)
  rw [tilde_map_basicOpen_eq_localized]
  exact IsLocalizedModule.map_surjective _ _ _ f.hom hf

private lemma associatedBase_map_mono {M N : ModuleCat A} (f : M ⟶ N)
    (hf : Function.Injective f) : Mono ((affineAssociatedSheafFunctor (k := k)).map f) := by
  constructor
  intro K g h e
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro a
  ext x
  apply associatedBase_map_basicOpen_injective f hf a
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun t => t.hom) e) (op (PrimeSpectrum.basicOpen a))) x

private lemma associatedBase_map_epi {M N : ModuleCat A} (f : M ⟶ N)
    (hf : Function.Surjective f) : Epi ((affineAssociatedSheafFunctor (k := k)).map f) := by
  constructor
  intro K g h e
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro a
  ext x
  obtain ⟨x, rfl⟩ := associatedBase_map_basicOpen_surjective (k := k) f hf a x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun t => t.hom) e) (op (PrimeSpectrum.basicOpen a))) x

private instance : (modulesSpecToSheaf (R := A)).Additive where
  map_add := by intros; rfl
private instance : (sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
    (ModuleCat.restrictScalars (algebraMap k A))).Additive where
  map_add := by intros; rfl
private instance associatedBase_additive :
    (affineAssociatedSheafFunctor (k := k) (A := A)).Additive := by
  have : (modulesSpecToSheaf (R := A) ⋙
      sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).Additive := by infer_instance
  unfold affineAssociatedSheafFunctor
  infer_instance

private instance affineAssociatedSectionModule (M : ModuleCat A) (U : (Spec A).Opens) :
    Module A (((affineAssociatedSheafFunctor (k := k)).obj M).obj.obj (op U)) :=
  inferInstanceAs (Module A ((modulesSpecToSheaf.obj (tilde M)).obj.obj (op U)))

/-- The canonical section of an associated sheaf represented by an algebraic module element. -/
def affineAssociatedSection (M : ModuleCat A) (U : (Spec A).Opens) :
    M →+ (((affineAssociatedSheafFunctor (k := k)).obj M).obj.obj (op U)) :=
  (tilde.toOpen M U).hom.toAddMonoidHom

private lemma affineAssociatedSection_res (M : ModuleCat A) {U V : (Spec A).Opens} (i : U ⟶ V)
    (x : M) :
    (((affineAssociatedSheafFunctor (k := k)).obj M).obj.map i.op)
      (affineAssociatedSection M V x) = affineAssociatedSection M U x :=
  ConcreteCategory.congr_hom (tilde.toOpen_res M V U i) x

/-- Associated module maps preserve the canonical algebraic sections. -/
lemma affineAssociatedSection_map {M N : ModuleCat A} (f : M ⟶ N)
    (U : (Spec A).Opens) (x : M) :
    ((affineAssociatedSheafFunctor (k := k)).map f).hom.app (op U)
      (affineAssociatedSection M U x) = affineAssociatedSection N U (f x) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) x

private lemma associatedBase_map_smul {M N : ModuleCat A} (f : M ⟶ N)
    (U : (Spec A).Opens) (a : A)
    (x : ((affineAssociatedSheafFunctor (k := k)).obj M).obj.obj (op U)) :
    ((affineAssociatedSheafFunctor (k := k)).map f).hom.app (op U) (a • x) =
      a • ((affineAssociatedSheafFunctor (k := k)).map f).hom.app (op U) x :=
  ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op U)).hom.map_smul a x

set_option backward.isDefEq.respectTransparency false in
private lemma associatedBase_hom_ext {M N : ModuleCat A}
    (φ ψ : (affineAssociatedSheafFunctor (k := k)).obj M ⟶
      (affineAssociatedSheafFunctor (k := k)).obj N)
    (hφ : ∀ (U : (Spec A).Opens) (a : A)
      (x : ((affineAssociatedSheafFunctor (k := k)).obj M).obj.obj (op U)),
      φ.hom.app (op U) (a • x) = a • φ.hom.app (op U) x)
    (hψ : ∀ (U : (Spec A).Opens) (a : A)
      (x : ((affineAssociatedSheafFunctor (k := k)).obj M).obj.obj (op U)),
      ψ.hom.app (op U) (a • x) = a • ψ.hom.app (op U) x)
    (h : ∀ x : M, φ.hom.app (op ⊤) (affineAssociatedSection M ⊤ x) =
      ψ.hom.app (op ⊤) (affineAssociatedSection M ⊤ x)) : φ = ψ := by
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro a
  let α : ((modulesSpecToSheaf.obj (tilde M)).obj.obj (op (PrimeSpectrum.basicOpen a))) →ₗ[A]
      ((modulesSpecToSheaf.obj (tilde N)).obj.obj (op (PrimeSpectrum.basicOpen a))) :=
    { toFun := φ.hom.app (op (PrimeSpectrum.basicOpen a))
      map_add' := map_add _
      map_smul' := hφ _ }
  let β : ((modulesSpecToSheaf.obj (tilde M)).obj.obj (op (PrimeSpectrum.basicOpen a))) →ₗ[A]
      ((modulesSpecToSheaf.obj (tilde N)).obj.obj (op (PrimeSpectrum.basicOpen a))) :=
    { toFun := ψ.hom.app (op (PrimeSpectrum.basicOpen a))
      map_add' := map_add _
      map_smul' := hψ _ }
  have hab : α = β := by
    apply IsLocalizedModule.linearMap_ext (.powers a)
      (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen a)).hom
    apply LinearMap.ext
    intro x
    have hφres := ConcreteCategory.congr_hom
      (φ.hom.naturality (PrimeSpectrum.basicOpen a).leTop.op)
      (affineAssociatedSection M ⊤ x)
    have hψres := ConcreteCategory.congr_hom
      (ψ.hom.naturality (PrimeSpectrum.basicOpen a).leTop.op)
      (affineAssociatedSection M ⊤ x)
    change φ.hom.app (op (PrimeSpectrum.basicOpen a))
        (affineAssociatedSection M (PrimeSpectrum.basicOpen a) x) =
      ψ.hom.app (op (PrimeSpectrum.basicOpen a))
        (affineAssociatedSection M (PrimeSpectrum.basicOpen a) x)
    simpa only [ConcreteCategory.comp_apply, affineAssociatedSection_res] using
      hφres.trans ((congrArg (((affineAssociatedSheafFunctor (k := k)).obj N).obj.map
        (PrimeSpectrum.basicOpen a).leTop.op) (h x)).trans hψres.symm)
  ext x
  exact LinearMap.congr_fun hab x

open OrlikSolomon.DeRham
attribute [local instance] strongEpi_of_epi

section Algebraic
variable (k) (f : A) (T : Type u) [CommRing T] [Algebra k T]
  [Algebra A T] [IsScalarTower k A T] [IsLocalization.Away f T]

private def thetaToLogPower (n : ℕ) :
    ModuleCat.of A (⋀[A]^n Ω[A⁄k]) ⟶ ModuleCat.of A (logPower k f T (n + 1)) :=
  ModuleCat.ofHom
    { toFun η := ⟨theta k f T * Forms.map (IsScalarTower.toAlgHom k A T) η.val,
        theta_mul_map_mem_logPower k f T η.property⟩
      map_add' x y := Subtype.ext (by simp only [Submodule.coe_add, map_add, mul_add])
      map_smul' a x := Subtype.ext (by
        simp only [SetLike.val_smul, Forms.map_toAlgHom_smul, mul_smul_comm,
          RingHom.id_apply]) }

private def logMkPowerCat (n : ℕ) :
    ModuleCat.of A (⋀[A]^(n + 1) Ω[A⁄k]) ⊞ ModuleCat.of A (⋀[A]^n Ω[A⁄k]) ⟶
      ModuleCat.of A (logPower k f T (n + 1)) :=
  biprod.desc (ModuleCat.ofHom (powerToLog k f T (n + 1))) (thetaToLogPower k f T n)

private lemma logMkPowerCat_surjective (n : ℕ) :
    Function.Surjective (logMkPowerCat k f T n) := by
  rintro ⟨x, hx⟩
  obtain ⟨ω, hω, η, hη, he⟩ := mem_logPower_succ.1 hx
  let l : ModuleCat.of A (⋀[A]^(n + 1) Ω[A⁄k]) ⟶
      ModuleCat.of A (⋀[A]^(n + 1) Ω[A⁄k]) ⊞ ModuleCat.of A (⋀[A]^n Ω[A⁄k]) := biprod.inl
  let r : ModuleCat.of A (⋀[A]^n Ω[A⁄k]) ⟶
      ModuleCat.of A (⋀[A]^(n + 1) Ω[A⁄k]) ⊞ ModuleCat.of A (⋀[A]^n Ω[A⁄k]) := biprod.inr
  refine ⟨l ⟨ω, hω⟩ + r ⟨η, hη⟩, ?_⟩
  rw [map_add]
  have h₁ := ConcreteCategory.congr_hom (biprod.inl_desc
    (ModuleCat.ofHom (powerToLog k f T (n + 1))) (thetaToLogPower k f T n)) ⟨ω, hω⟩
  have h₂ := ConcreteCategory.congr_hom (biprod.inr_desc
    (ModuleCat.ofHom (powerToLog k f T (n + 1))) (thetaToLogPower k f T n)) ⟨η, hη⟩
  change (logMkPowerCat k f T n) (l _) = _ at h₁
  change (logMkPowerCat k f T n) (r _) = _ at h₂
  rw [h₁, h₂]
  exact Subtype.ext he

end Algebraic

section Spectrum
attribute [local instance] strongEpi_of_epi
variable (P : OrlikSolomon.DivisorPair k)
local notation "AP" => (CommRingCat.of P.ambient)
local notation "FA" => (affineAssociatedSheafFunctor (k := k) (A := AP))
local notation "PG" => (Geometric.DivisorPair.spec (SmoothDomain.aff k) P)

private lemma specSectionMap_top_apply (a : P.ambient) :
    specSectionMap (k := k) (A := P.ambient) ⊤ a =
      (Scheme.ΓSpecIso AP).inv a := by
  change (Spec AP).presheaf.map (⊤ : (Spec AP).Opens).leTop.op
    ((Scheme.ΓSpecIso AP).inv a) = _
  rw [show (⊤ : (Spec AP).Opens).leTop.op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

private lemma specSectionMap_j :
    (sectionPullbackTop (PG).j.hom).comp (specSectionMap (k := k) (A := P.ambient) ⊤) =
      (specSectionMap (k := k) (A := P.compl) ⊤).comp (SmoothAlg.algHom P.j) := by
  apply AlgHom.ext
  intro a
  change (PG).j.hom.left.appTop (specSectionMap (k := k) (A := P.ambient) ⊤ a) =
    specSectionMap (k := k) (A := P.compl) ⊤ (P.j a)
  rw [specSectionMap_top_apply P a]
  change (Spec.map (CommRingCat.ofHom (SmoothAlg.algHom P.j).toRingHom)).appTop
    ((Scheme.ΓSpecIso AP).inv a) =
      (Spec (CommRingCat.of P.compl)).presheaf.map
        (⊤ : (Spec (CommRingCat.of P.compl)).Opens).leTop.op
        ((Scheme.ΓSpecIso (CommRingCat.of P.compl)).inv (P.j a))
  rw [show (⊤ : (Spec (CommRingCat.of P.compl)).Opens).leTop.op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (SmoothAlg.algHom P.j).toRingHom)) a).symm

private lemma specSectionMap_compl_top_apply (a : P.compl) :
    specSectionMap (k := k) (A := P.compl) ⊤ a =
      (Scheme.ΓSpecIso (CommRingCat.of P.compl)).inv a := by
  change (Spec (CommRingCat.of P.compl)).presheaf.map
    (⊤ : (Spec (CommRingCat.of P.compl)).Opens).leTop.op
      ((Scheme.ΓSpecIso (CommRingCat.of P.compl)).inv a) = _
  rw [show (⊤ : (Spec (CommRingCat.of P.compl)).Opens).leTop.op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

private lemma specSectionMap_eqnUnit :
    Units.map (specSectionMap (k := k) (A := P.compl) ⊤).toMonoidHom P.eqnUnit =
      (PG).eqnUnit := by
  apply Units.ext
  change specSectionMap (k := k) (A := P.compl) ⊤ (P.eqnUnit : P.compl) =
    ((PG).eqnUnit : Γ((PG).compl.obj.left, ⊤))
  rw [specSectionMap_compl_top_apply]
  exact (Geometric.DivisorPair.coe_spec_eqnUnit (SmoothDomain.aff k) P).symm

private lemma specSectionMap_theta :
    Forms.map (specSectionMap (k := k) (A := P.compl) ⊤)
      (theta k P.eqn P.compl) =
      dlog k (show (sectionAlgebra k (PG).compl.obj ⊤)ˣ from (PG).eqnUnit) := by
  rw [theta_eq_dlog k P.eqn P.compl (show (P.eqnUnit : P.compl) =
      algebraMap P.ambient P.compl P.eqn from rfl),
    Forms.map_dlog]
  exact congrArg (dlog k) (specSectionMap_eqnUnit P)

private def specRegularIso (n : ℕ) :
    (FA).obj (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ≅
      formsSheaf k (PG).ambient.obj n :=
  (specFormsSheafAssociatedBaseIso (k := k) (A := AP) n).symm

private lemma specRegularIso_section (n : ℕ) (U : (Spec AP).Opens)
    (x : ⋀[P.ambient]^n Ω[P.ambient⁄k]) :
    (specRegularIso P n).hom.hom.app (op U)
      (affineAssociatedSection (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) U x) =
        (formsSheafUnit k (PG).ambient.obj n).app (op U)
          (Forms.mapPower (specSectionMap U) n x) :=
  specFormsSheafAssociatedBaseIso_inv_unit n U x

/-- Affine pushforward identifies complement forms with the associated restricted module. -/
@[no_expose] def specOpenFormsAssociatedIso (n : ℕ) :
    (FA).obj (ModuleCat.of AP (⋀[P.compl]^n Ω[P.compl⁄k])) ≅ openFormsSheaf (PG) n :=
  (specFormsSheafPushforwardAssociatedBaseIso (A := AP) (B := CommRingCat.of P.compl)
    (SmoothAlg.algHom P.j) n).symm

/-- The affine complement comparison sends a global algebraic representative to its form section. -/
lemma specOpenFormsAssociatedIso_hom_section (n : ℕ)
    (x : ⋀[P.compl]^n Ω[P.compl⁄k]) :
    (specOpenFormsAssociatedIso P n).hom.hom.app (op ⊤)
      (affineAssociatedSection (k := k) (A := AP)
        (ModuleCat.of AP (⋀[P.compl]^n Ω[P.compl⁄k])) ⊤ x) =
      specFormsSheafPushforwardBaseSection (A := AP) (B := CommRingCat.of P.compl)
        (SmoothAlg.algHom P.j) n ⊤ x :=
  specFormsSheafPushforwardAssociatedBaseIso_inv_top_section
    (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) n x

private local instance specRegularSectionModule (n : ℕ) (U : (Spec AP).Opens) :
    Module P.ambient
      (((FA).obj (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]))).obj.obj (op U)) :=
  affineAssociatedSectionModule (k := k) (A := AP) _ U

private local instance specOpenSectionModule (n : ℕ) (U : (Spec AP).Opens) :
    Module P.ambient
      (((FA).obj (ModuleCat.of AP (⋀[P.compl]^n Ω[P.compl⁄k]))).obj.obj (op U)) :=
  affineAssociatedSectionModule (k := k) (A := AP) _ U

private lemma specAssociated_smul (n : ℕ) (U : (Spec AP).Opens) (a : P.ambient)
    (x : ((FA).obj (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]))).obj.obj (op U)) :
    specFormsAssociatedBaseSMul (k := k) (A := AP) n U
      (specSectionMap (k := k) (A := P.ambient) U a) x = a • x := by
  rfl

private lemma specPushAssociated_smul (n : ℕ) (U : (Spec AP).Opens) (a : P.ambient)
    (x : ((FA).obj (ModuleCat.of AP (⋀[P.compl]^n Ω[P.compl⁄k]))).obj.obj (op U)) :
    specFormsPushforwardAssociatedBaseSMul (k := k) (A := AP) (B := CommRingCat.of P.compl)
      (SmoothAlg.algHom P.j) n U
      (specSectionMap (k := k) (A := P.ambient) U a) x = a • x := by
  rfl

private def specNormalSourceIso (n : ℕ) :
    (FA).obj (ModuleCat.of AP (⋀[P.ambient]^(n + 1) Ω[P.ambient⁄k]) ⊞
      ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ≅
      formsSheaf k (PG).ambient.obj (n + 1) ⊞ formsSheaf k (PG).ambient.obj n := by
  have : (FA).Additive := associatedBase_additive (k := k) (A := AP)
  have : (FA).PreservesZeroMorphisms := inferInstance
  have : PreservesFiniteBiproducts FA := inferInstance
  have : PreservesBiproductsOfShape WalkingPair FA := inferInstance
  have : PreservesBinaryBiproducts FA := preservesBinaryBiproducts_of_preservesBiproducts FA
  exact (FA).mapBiprod _ _ ≪≫
    biprod.mapIso (specRegularIso P (n + 1)) (specRegularIso P n)

private lemma specNormalSourceIso_inl (n : ℕ) :
    (FA).map (biprod.inl : ModuleCat.of AP (⋀[P.ambient]^(n + 1) Ω[P.ambient⁄k]) ⟶
      ModuleCat.of AP (⋀[P.ambient]^(n + 1) Ω[P.ambient⁄k]) ⊞
        ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ≫
      (specNormalSourceIso P n).hom = (specRegularIso P (n + 1)).hom ≫ biprod.inl := by
  have : (FA).Additive := associatedBase_additive (k := k) (A := AP)
  have : (FA).PreservesZeroMorphisms := inferInstance
  apply biprod.hom_ext <;>
    simp only [specNormalSourceIso, Iso.trans_hom, Category.assoc,
      Functor.mapBiprod_hom, biprod.mapIso_hom, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.inl_fst, biprod.inl_snd,
      Category.comp_id, CategoryTheory.Limits.comp_zero]
  all_goals
    simp only [← Category.assoc, ← Functor.map_comp, biprod.inl_fst, biprod.inl_snd,
      CategoryTheory.Functor.map_id, Functor.map_zero,
      Category.id_comp, CategoryTheory.Limits.zero_comp]

private lemma specNormalSourceIso_inr (n : ℕ) :
    (FA).map (biprod.inr : ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]) ⟶
      ModuleCat.of AP (⋀[P.ambient]^(n + 1) Ω[P.ambient⁄k]) ⊞
        ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ≫
      (specNormalSourceIso P n).hom = (specRegularIso P n).hom ≫ biprod.inr := by
  have : (FA).Additive := associatedBase_additive (k := k) (A := AP)
  have : (FA).PreservesZeroMorphisms := inferInstance
  apply biprod.hom_ext <;>
    simp only [specNormalSourceIso, Iso.trans_hom, Category.assoc,
      Functor.mapBiprod_hom, biprod.mapIso_hom, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.inr_fst, biprod.inr_snd, Category.comp_id, CategoryTheory.Limits.comp_zero]
  all_goals
    simp only [← Category.assoc, ← Functor.map_comp,
      biprod.inr_fst, biprod.inr_snd, CategoryTheory.Functor.map_id, Functor.map_zero,
      Category.id_comp, CategoryTheory.Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma specRegular_conjugate_smul (n : ℕ) (U : (Spec AP).Opens) (a : P.ambient)
    (x : ((FA).obj (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]))).obj.obj (op U)) :
    (((specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫
        (specOpenFormsAssociatedIso P n).inv).hom.app (op U)) (a • x) =
      a • (((specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫
        (specOpenFormsAssociatedIso P n).inv).hom.app (op U)) x := by
  let s := (specFormsSheafAssociatedBaseIso (k := k) (A := AP) n).inv.hom.app (op U)
  let p := (formsSheafPullback (PG).j.hom n).hom.app (op U)
  let t := (specFormsSheafPushforwardAssociatedBaseIso
    (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) n).hom.hom.app (op U)
  have hs : s (a • x) = formsSheafSMul k (PG).ambient.obj n U
      (specSectionMap (k := k) (A := P.ambient) U a) (s x) :=
    (congrArg (fun z => s z) (specAssociated_smul P n U a x).symm).trans
      (specFormsSheafAssociatedBaseIso_inv_smul (k := k) (A := AP) n U
        (specSectionMap (k := k) (A := P.ambient) U a) x)
  have hp := formsSheafPullback_smul (PG).j.hom n U
    (specSectionMap (k := k) (A := P.ambient) U a) (s x)
  have ht := specFormsSheafPushforwardAssociatedBaseIso_smul
    (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) n U
    (specSectionMap (k := k) (A := P.ambient) U a) (p (s x))
  exact (congrArg (fun z => t (p z)) hs).trans
    ((congrArg (fun z => t z) hp).trans
      (ht.trans (specPushAssociated_smul P n U a (t (p (s x))))))

private lemma specRegular_pull_section (n : ℕ) (x : ⋀[P.ambient]^n Ω[P.ambient⁄k]) :
    (formsSheafPullback (PG).j.hom n).hom.app (op ⊤)
      ((specRegularIso P n).hom.hom.app (op ⊤)
        (affineAssociatedSection (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ⊤ x)) =
      (formsSheafUnit k (PG).compl.obj n).app (op ⊤)
        (Forms.mapPower (specSectionMap (k := k) (A := P.compl) ⊤) n
          (Forms.mapPower (SmoothAlg.algHom P.j) n x)) := by
  rw [specRegularIso_section]
  rw [formsSheafPullback_unit_apply (PG).j.hom n (op ⊤)
    (Forms.mapPower (specSectionMap (k := k) (A := P.ambient) ⊤) n x)]
  congr 1
  change Forms.mapPower (sectionPullbackTop (PG).j.hom) n
      (Forms.mapPower (specSectionMap (k := k) (A := P.ambient) ⊤) n x) = _
  exact (LinearMap.congr_fun (Forms.mapPower_comp (sectionPullbackTop (PG).j.hom)
    (specSectionMap (k := k) (A := P.ambient) ⊤) n) x).symm.trans
      ((congrArg (fun q => Forms.mapPower q n x) (specSectionMap_j P)).trans
        (LinearMap.congr_fun (Forms.mapPower_comp
          (specSectionMap (k := k) (A := P.compl) ⊤) (SmoothAlg.algHom P.j) n) x))

private lemma specRegular_square (n : ℕ) :
    (specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n =
      (FA).map (ModuleCat.ofHom (powerToLog k P.eqn P.compl n) ≫
        ModuleCat.ofHom (logPowerToPower k P.eqn P.compl n)) ≫
          (specOpenFormsAssociatedIso P n).hom := by
  apply (cancel_mono (specOpenFormsAssociatedIso P n).inv).1
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply associatedBase_hom_ext
  · exact specRegular_conjugate_smul P n
  · exact associatedBase_map_smul _
  · intro x
    change (specOpenFormsAssociatedIso P n).inv.hom.app (op ⊤)
        ((formsSheafPullback (PG).j.hom n).hom.app (op ⊤)
          ((specRegularIso P n).hom.hom.app (op ⊤)
            (affineAssociatedSection (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ⊤ x))) = _
    rw [specRegular_pull_section, affineAssociatedSection_map]
    exact specFormsSheafPushforwardAssociatedBaseIso_top_unit
      (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) n
      (Forms.mapPower (SmoothAlg.algHom P.j) n x)

private lemma specTheta_conjugate_smul (n : ℕ) (U : (Spec AP).Opens) (a : P.ambient)
    (x : ((FA).obj (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]))).obj.obj (op U)) :
    (((specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫
        openThetaWedgeSheaf (PG) n ≫
          (specOpenFormsAssociatedIso P (n + 1)).inv).hom.app (op U)) (a • x) =
      a • (((specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫
        openThetaWedgeSheaf (PG) n ≫
          (specOpenFormsAssociatedIso P (n + 1)).inv).hom.app (op U)) x := by
  let s := (specFormsSheafAssociatedBaseIso (k := k) (A := AP) n).inv.hom.app (op U)
  let p := (formsSheafPullback (PG).j.hom n).hom.app (op U)
  let θ := (thetaWedgeSheaf (PG).compl.obj (PG).eqnUnit n).hom.app (op ((PG).j.hom.left ⁻¹ᵁ U))
  let t := (specFormsSheafPushforwardAssociatedBaseIso
    (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) (n + 1)).hom.hom.app (op U)
  have hs : s (a • x) = formsSheafSMul k (PG).ambient.obj n U
      (specSectionMap (k := k) (A := P.ambient) U a) (s x) :=
    (congrArg (fun z => s z) (specAssociated_smul P n U a x).symm).trans
      (specFormsSheafAssociatedBaseIso_inv_smul (k := k) (A := AP) n U
        (specSectionMap (k := k) (A := P.ambient) U a) x)
  have hp := formsSheafPullback_smul (PG).j.hom n U
    (specSectionMap (k := k) (A := P.ambient) U a) (s x)
  have hθ := thetaWedgeSheaf_smul (PG).compl.obj (PG).eqnUnit n ((PG).j.hom.left ⁻¹ᵁ U)
    (sectionPullback (PG).j.hom U (specSectionMap (k := k) (A := P.ambient) U a)) (p (s x))
  have ht := specFormsSheafPushforwardAssociatedBaseIso_smul
    (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) (n + 1) U
    (specSectionMap (k := k) (A := P.ambient) U a) (θ (p (s x)))
  exact (congrArg (fun z => t (θ (p z))) hs).trans
    ((congrArg (fun z => t (θ z)) hp).trans
      ((congrArg (fun z => t z) hθ).trans
        (ht.trans (specPushAssociated_smul P (n + 1) U a (t (θ (p (s x))))))))

private lemma specTheta_pull_section (n : ℕ) (x : ⋀[P.ambient]^n Ω[P.ambient⁄k]) :
    (openThetaWedgeSheaf (PG) n).hom.app (op ⊤)
      ((formsSheafPullback (PG).j.hom n).hom.app (op ⊤)
        ((specRegularIso P n).hom.hom.app (op ⊤)
          (affineAssociatedSection (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ⊤ x))) =
      (formsSheafUnit k (PG).compl.obj (n + 1)).app (op ⊤)
        (Forms.mapPower (specSectionMap (k := k) (A := P.compl) ⊤) (n + 1)
          (logPowerToPower k P.eqn P.compl (n + 1)
            (thetaToLogPower (A := AP) k P.eqn P.compl n x))) := by
  rw [specRegular_pull_section]
  change (thetaWedgeSheaf (PG).compl.obj (PG).eqnUnit n).hom.app (op ⊤) _ = _
  rw [thetaWedgeSheaf_unit (PG).compl.obj (PG).eqnUnit n (op ⊤)
    (Forms.mapPower (specSectionMap (k := k) (A := P.compl) ⊤) n
      (Forms.mapPower (SmoothAlg.algHom P.j) n x))]
  congr 1
  apply Subtype.ext
  change dlog k (Units.map (sectionRestriction k (PG).compl.obj (𝟙 ⊤)).toMonoidHom (PG).eqnUnit) *
      Forms.map (specSectionMap (k := k) (A := P.compl) ⊤)
        (Forms.map (SmoothAlg.algHom P.j) x.val) =
    Forms.map (specSectionMap (k := k) (A := P.compl) ⊤)
      (theta k P.eqn P.compl * Forms.map (IsScalarTower.toAlgHom k P.ambient P.compl) x.val)
  rw [sectionRestriction_id]
  change dlog k (show (sectionAlgebra k (PG).compl.obj ⊤)ˣ from (PG).eqnUnit) *
      Forms.map (specSectionMap (k := k) (A := P.compl) ⊤)
        (Forms.map (SmoothAlg.algHom P.j) x.val) = _
  rw [map_mul, specSectionMap_theta P]
  rfl

private lemma specTheta_square (n : ℕ) :
    (specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫ openThetaWedgeSheaf (PG) n =
      (FA).map (thetaToLogPower (A := AP) k P.eqn P.compl n ≫
        ModuleCat.ofHom (logPowerToPower k P.eqn P.compl (n + 1))) ≫
          (specOpenFormsAssociatedIso P (n + 1)).hom := by
  apply (cancel_mono (specOpenFormsAssociatedIso P (n + 1)).inv).1
  rw [Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply associatedBase_hom_ext
  · exact specTheta_conjugate_smul P n
  · exact associatedBase_map_smul _
  · intro x
    change (specOpenFormsAssociatedIso P (n + 1)).inv.hom.app (op ⊤)
      ((openThetaWedgeSheaf (PG) n).hom.app (op ⊤)
        ((formsSheafPullback (PG).j.hom n).hom.app (op ⊤)
          ((specRegularIso P n).hom.hom.app (op ⊤)
            (affineAssociatedSection (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k])) ⊤ x)))) = _
    rw [specTheta_pull_section, affineAssociatedSection_map]
    exact specFormsSheafPushforwardAssociatedBaseIso_top_unit
      (A := AP) (B := CommRingCat.of P.compl) (SmoothAlg.algHom P.j) (n + 1)
      (logPowerToPower k P.eqn P.compl (n + 1) (thetaToLogPower (A := AP) k P.eqn P.compl n x))

private lemma specNormal_square (n : ℕ) :
    (specNormalSourceIso P n).hom ≫ logNormalFormSheaf (PG) n =
      (FA).map (logMkPowerCat (A := AP) k P.eqn P.compl n ≫
        ModuleCat.ofHom (logPowerToPower k P.eqn P.compl (n + 1))) ≫
          (specOpenFormsAssociatedIso P (n + 1)).hom := by
  have : (FA).Additive := associatedBase_additive (k := k) (A := AP)
  have : (FA).PreservesZeroMorphisms := inferInstance
  have : PreservesFiniteBiproducts FA := inferInstance
  have : PreservesBiproductsOfShape WalkingPair FA := inferInstance
  have : PreservesBinaryBiproducts FA := preservesBinaryBiproducts_of_preservesBiproducts FA
  apply (cancel_epi ((FA).mapBiprod
    (ModuleCat.of AP (⋀[P.ambient]^(n + 1) Ω[P.ambient⁄k]))
    (ModuleCat.of AP (⋀[P.ambient]^n Ω[P.ambient⁄k]))).inv).1
  apply biprod.hom_ext'
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc]
    rw [specNormalSourceIso_inl, Category.assoc, inl_logNormalFormSheaf,
      specRegular_square P (n + 1), ← Functor.map_comp, logMkPowerCat, biprod.inl_desc_assoc]
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc]
    rw [specNormalSourceIso_inr, Category.assoc, inr_logNormalFormSheaf]
    change (specRegularIso P n).hom ≫ formsSheafPullback (PG).j.hom n ≫
      openThetaWedgeSheaf (PG) n = _
    simp only [← Functor.map_comp, ← Category.assoc, logMkPowerCat, biprod.inr_desc]
    simpa only [Category.assoc] using specTheta_square P n

private def specLogSuccIso (n : ℕ) :
    (FA).obj (ModuleCat.of AP (logPower k P.eqn P.compl (n + 1))) ≅
      logSheaf (PG) (n + 1) := by
  let a := (specNormalSourceIso P n).inv ≫
    (FA).map (logMkPowerCat (A := AP) k P.eqn P.compl n)
  let b := (FA).map (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl (n + 1))) ≫
    (specOpenFormsAssociatedIso P (n + 1)).hom
  have := associatedBase_map_epi (k := k) (A := AP)
    (logMkPowerCat (A := AP) k P.eqn P.compl n)
    (logMkPowerCat_surjective (A := AP) k P.eqn P.compl n)
  have := associatedBase_map_mono (k := k) (A := AP)
    (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl (n + 1)))
    (logPowerToPower_injective k P.eqn P.compl (n + 1))
  have : Epi a := by dsimp only [a]; infer_instance
  have : Mono b := by dsimp only [b]; infer_instance
  have hab : a ≫ b = logNormalFormSheaf (PG) n := by
    dsimp only [a, b]
    rw [Category.assoc, ← Category.assoc ((FA).map _), ← Functor.map_comp,
      ← specNormal_square P n, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafImageIso (PG) n

private lemma specLogSuccIso_hom_comp (n : ℕ) :
    (specLogSuccIso P n).hom ≫ logToOpenSheaf (PG) (n + 1) =
      (FA).map (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl (n + 1))) ≫
        (specOpenFormsAssociatedIso P (n + 1)).hom := by
  dsimp only [specLogSuccIso, Iso.trans_hom]
  rw [Category.assoc, logSheafImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

private def specLogZeroIso :
    (FA).obj (ModuleCat.of AP (logPower k P.eqn P.compl 0)) ≅ logSheaf (PG) 0 := by
  let a := (specRegularIso P 0).inv ≫
    (FA).map (ModuleCat.ofHom (powerToLog k P.eqn P.compl 0))
  let b := (FA).map (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl 0)) ≫
    (specOpenFormsAssociatedIso P 0).hom
  have := associatedBase_map_epi (k := k) (A := AP)
    (ModuleCat.ofHom (powerToLog k P.eqn P.compl 0))
    (powerToLog_zero_surjective k P.eqn P.compl)
  have := associatedBase_map_mono (k := k) (A := AP)
    (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl 0))
    (logPowerToPower_injective k P.eqn P.compl 0)
  have : Epi a := by dsimp only [a]; infer_instance
  have : Mono b := by dsimp only [b]; infer_instance
  have hab : a ≫ b = formsSheafPullback (PG).j.hom 0 := by
    dsimp only [a, b]
    rw [Category.assoc, ← Category.assoc ((FA).map _), ← Functor.map_comp,
      ← specRegular_square P 0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafZeroImageIso (PG)

private lemma specLogZeroIso_hom_comp :
    (specLogZeroIso P).hom ≫ logToOpenSheaf (PG) 0 =
      (FA).map (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl 0)) ≫
        (specOpenFormsAssociatedIso P 0).hom := by
  dsimp only [specLogZeroIso, Iso.trans_hom]
  rw [Category.assoc, logSheafZeroImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

/-- The logarithmic sheaf on a spectrum is the associated sheaf of algebraic logarithmic forms.
The proof uses the exact associated-sheaf construction and the sheaf image. -/
@[no_expose] def specLogSheafAssociatedIso (n : ℕ) :
    (FA).obj (ModuleCat.of AP (logPower k P.eqn P.compl n)) ≅ logSheaf (PG) n :=
  match n with
  | 0 => specLogZeroIso P
  | n + 1 => specLogSuccIso P n

/-- The affine logarithmic comparison preserves inclusion into complement forms. -/
lemma specLogSheafAssociatedIso_hom_comp (n : ℕ) :
    (specLogSheafAssociatedIso P n).hom ≫ logToOpenSheaf (PG) n =
      (FA).map (ModuleCat.ofHom (logPowerToPower k P.eqn P.compl n)) ≫
        (specOpenFormsAssociatedIso P n).hom := by
  cases n with
  | zero => exact specLogZeroIso_hom_comp P
  | succ n => exact specLogSuccIso_hom_comp P n

end Spectrum

private theorem isoOpensMap_isCocontinuous {X Y : TopCat.{u}} (e : X ≅ Y) :
    (TopologicalSpace.Opens.map e.hom).IsCocontinuous
      (_root_.Opens.grothendieckTopology Y) (_root_.Opens.grothendieckTopology X) := by
  let E := TopologicalSpace.Opens.mapMapIso e
  exact (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (coverPreserving_opens_map e.inv)

private theorem isoPushforward_isEquivalence {X Y : TopCat.{u}} (e : X ≅ Y) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.hom).IsEquivalence := by
  let E := TopologicalSpace.Opens.mapMapIso e
  have : E.functor.IsCocontinuous (_root_.Opens.grothendieckTopology Y)
      (_root_.Opens.grothendieckTopology X) := isoOpensMap_isCocontinuous e
  have : E.inverse.IsCocontinuous (_root_.Opens.grothendieckTopology X)
      (_root_.Opens.grothendieckTopology Y) := isoOpensMap_isCocontinuous e.symm
  have : E.functor.IsDenseSubsite (_root_.Opens.grothendieckTopology Y)
      (_root_.Opens.grothendieckTopology X) :=
    E.isDenseSubsite_functor_of_isCocontinuous _ _
  change (E.functor.sheafPushforwardContinuous (ModuleCat.{u} k)
    (_root_.Opens.grothendieckTopology Y) (_root_.Opens.grothendieckTopology X)).IsEquivalence
  infer_instance

variable {D : SmoothDomain k} {P Q : DivisorPair D}
attribute [local instance] strongEpi_of_epi

private def logPairAmbientFunctor (D : SmoothDomain k) :
    DivisorPair D ⥤ Over (Spec (CommRingCat.of k)) where
  obj P := P.ambient.obj
  map F := F.ambient.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem pairPushforward_isEquivalence (e : P ≅ Q) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).IsEquivalence :=
  isoPushforward_isEquivalence
    ((Over.forget _ ⋙ Scheme.forgetToTop).mapIso ((logPairAmbientFunctor D).mapIso e).symm)

private def pairLogSourceIso (e : P ≅ Q) (n : ℕ) :
    formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n ≅
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).obj
        (formsSheaf k Q.ambient.obj (n + 1) ⊞ formsSheaf k Q.ambient.obj n) := by
  have : IsIso e.inv.ambient.hom := (logPairAmbientFunctor D).map_isIso e.inv
  let F := TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base
  have : F.Additive := by dsimp [F]; infer_instance
  have : F.PreservesZeroMorphisms := inferInstance
  have : PreservesFiniteBiproducts F := inferInstance
  have : PreservesBiproductsOfShape WalkingPair F := inferInstance
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  exact biprod.mapIso (asIso (formsSheafPullback e.inv.ambient.hom (n + 1)))
    (asIso (formsSheafPullback e.inv.ambient.hom n)) ≪≫ (F.mapBiprod _ _).symm

private lemma pairLogSourceIso_inl (e : P ≅ Q) (n : ℕ) :
    biprod.inl ≫ (pairLogSourceIso e n).hom = formsSheafPullback e.inv.ambient.hom (n + 1) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map biprod.inl := by
  simp only [pairLogSourceIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
    Functor.mapBiprod_inv, asIso_hom]
  rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]

private lemma pairLogSourceIso_inr (e : P ≅ Q) (n : ℕ) :
    biprod.inr ≫ (pairLogSourceIso e n).hom = formsSheafPullback e.inv.ambient.hom n ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map biprod.inr := by
  simp only [pairLogSourceIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
    Functor.mapBiprod_inv, asIso_hom]
  rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]

private lemma pairLogSourceIso_normal (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    (pairLogSourceIso e n).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map
          (logNormalFormSheaf Q n) =
      logNormalFormSheaf P n ≫ (pairOpenFormsIso e (n + 1)).hom := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, pairLogSourceIso_inl, Category.assoc, ← Functor.map_comp,
      inl_logNormalFormSheaf, pairOpenFormsIso_regular,
      ← Category.assoc, inl_logNormalFormSheaf]
  · rw [← Category.assoc, pairLogSourceIso_inr, Category.assoc, ← Functor.map_comp,
      inr_logNormalFormSheaf, Functor.map_comp, ← Category.assoc,
      pairOpenFormsIso_regular, Category.assoc]
    change formsSheafPullback P.j.hom n ≫
        (pairOpenFormsIso e n).hom ≫
          (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map
            (openThetaWedgeSheaf Q n) = _
    rw [← pairOpenFormsIso_theta e hunit n, ← Category.assoc]
    exact congrArg (fun t => t ≫ (pairOpenFormsIso e (n + 1)).hom)
      (inr_logNormalFormSheaf P n).symm

private def pairLogSuccIso (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).obj
      (logSheaf Q (n + 1)) ≅ logSheaf P (n + 1) := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base
  have : F.IsEquivalence := pairPushforward_isEquivalence e
  let a := (pairLogSourceIso e n).hom ≫ F.map (logMkSheaf Q n)
  let b := F.map (logToOpenSheaf Q (n + 1)) ≫ (pairOpenFormsIso e (n + 1)).inv
  have : Epi a := by dsimp [a]; infer_instance
  have : Mono b := by dsimp [b]; infer_instance
  have hab : a ≫ b = logNormalFormSheaf P n := by
    dsimp [a, b]
    rw [Category.assoc, ← Category.assoc (F.map _), ← Functor.map_comp,
      logMkSheaf_comp_logToOpenSheaf, ← Category.assoc, pairLogSourceIso_normal e hunit,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafImageIso P n

private lemma pairLogSuccIso_hom_comp (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    (pairLogSuccIso e hunit n).hom ≫ logToOpenSheaf P (n + 1) =
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map
        (logToOpenSheaf Q (n + 1)) ≫ (pairOpenFormsIso e (n + 1)).inv := by
  dsimp only [pairLogSuccIso, Iso.trans_hom]
  rw [Category.assoc, logSheafImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

private def pairLogZeroIso (e : P ≅ Q) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).obj
      (logSheaf Q 0) ≅ logSheaf P 0 := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base
  have : F.IsEquivalence := pairPushforward_isEquivalence e
  have : IsIso e.inv.ambient.hom := (logPairAmbientFunctor D).map_isIso e.inv
  let a := formsSheafPullback e.inv.ambient.hom 0 ≫ F.map (regularToLogSheaf Q 0)
  let b := F.map (logToOpenSheaf Q 0) ≫ (pairOpenFormsIso e 0).inv
  have : Epi a := by dsimp [a]; infer_instance
  have : Mono b := by dsimp [b]; infer_instance
  have hab : a ≫ b = formsSheafPullback P.j.hom 0 := by
    dsimp [a, b]
    rw [Category.assoc, ← Category.assoc (F.map _), ← Functor.map_comp,
      regularToLogSheaf_comp_logToOpenSheaf, ← Category.assoc, pairOpenFormsIso_regular,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafZeroImageIso P

private lemma pairLogZeroIso_hom_comp (e : P ≅ Q) :
    (pairLogZeroIso e).hom ≫ logToOpenSheaf P 0 =
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map
        (logToOpenSheaf Q 0) ≫ (pairOpenFormsIso e 0).inv := by
  dsimp only [pairLogZeroIso, Iso.trans_hom]
  rw [Category.assoc, logSheafZeroImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

/-- Transport logarithmic image sheaves along an isomorphism of pairs preserving the
equation unit. -/
@[no_expose] def pairLogSheafIso (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).obj
      (logSheaf Q n) ≅ logSheaf P n :=
  match n with
  | 0 => pairLogZeroIso e
  | n + 1 => pairLogSuccIso e hunit n

/-- Transport of logarithmic sheaves preserves their inclusions in complement forms. -/
lemma pairLogSheafIso_hom_comp (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    (pairLogSheafIso e hunit n).hom ≫ logToOpenSheaf P n =
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) e.inv.ambient.hom.left.base).map
        (logToOpenSheaf Q n) ≫ (pairOpenFormsIso e n).inv := by
  cases n with
  | zero => exact pairLogZeroIso_hom_comp e
  | succ n => exact pairLogSuccIso_hom_comp e hunit n

end OrlikSolomon.Geometric.DeRham
