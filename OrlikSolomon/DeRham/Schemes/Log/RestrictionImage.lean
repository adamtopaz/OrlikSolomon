/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
/-!
# Exact transport of logarithmic image complexes

An additive functor preserving monomorphisms and epimorphisms carries the
regular-plus-logarithmic image to the corresponding image whenever its regular and
complement form comparisons preserve restriction and left logarithmic multiplication.
The construction treats degree zero separately and preserves the inclusion, regular
forms, and differential. In particular, it applies to restriction to open subschemes.
It does not require global sections to preserve images.

Blueprint: the affine-local step of `thm:geo-log-sheaves`.
-/

@[expose] public section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
noncomputable section
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k] {D E : SmoothDomain k}
variable (P : DivisorPair D) (Q : DivisorPair E)
variable (R : TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left ⥤
  TopCat.Sheaf (ModuleCat.{u} k) Q.ambient.obj.left)
variable [R.Additive]
variable (eReg : ∀ n, R.obj (formsSheaf k P.ambient.obj n) ≅ formsSheaf k Q.ambient.obj n)
variable (eOpen : ∀ n, R.obj (openFormsSheaf P n) ≅ openFormsSheaf Q n)
variable (hReg : ∀ n, R.map (formsSheafPullback P.j.hom n) ≫ (eOpen n).hom =
  (eReg n).hom ≫ formsSheafPullback Q.j.hom n)
variable (hTheta : ∀ n, R.map (openThetaWedgeSheaf P n) ≫ (eOpen (n + 1)).hom =
  (eOpen n).hom ≫ openThetaWedgeSheaf Q n)
attribute [local instance] strongEpi_of_epi

/-- The regular-plus-logarithmic generator source is preserved by an additive comparison. -/
def restrictionNormalSourceIso (n : ℕ) :
    R.obj (formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n) ≅
      formsSheaf k Q.ambient.obj (n + 1) ⊞ formsSheaf k Q.ambient.obj n := by
  have : R.PreservesZeroMorphisms := inferInstance
  have : PreservesFiniteBiproducts R := inferInstance
  have : PreservesBiproductsOfShape WalkingPair R := inferInstance
  have : PreservesBinaryBiproducts R := preservesBinaryBiproducts_of_preservesBiproducts R
  exact R.mapBiprod _ _ ≪≫ biprod.mapIso (eReg (n + 1)) (eReg n)

private lemma restrictionNormalSourceIso_inl (n : ℕ) :
    R.map (biprod.inl : formsSheaf k P.ambient.obj (n + 1) ⟶
      formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n) ≫
      (restrictionNormalSourceIso P Q R eReg n).hom = (eReg (n + 1)).hom ≫ biprod.inl := by
  have : R.PreservesZeroMorphisms := inferInstance
  apply biprod.hom_ext <;>
    simp only [restrictionNormalSourceIso, Iso.trans_hom, Category.assoc,
      Functor.mapBiprod_hom, biprod.mapIso_hom, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.inl_fst, biprod.inl_snd,
      Category.comp_id, CategoryTheory.Limits.comp_zero]
  all_goals simp only [← Category.assoc, ← Functor.map_comp, biprod.inl_fst, biprod.inl_snd,
    CategoryTheory.Functor.map_id, Functor.map_zero, Category.id_comp,
      CategoryTheory.Limits.zero_comp]

private lemma restrictionNormalSourceIso_inr (n : ℕ) :
    R.map (biprod.inr : formsSheaf k P.ambient.obj n ⟶
      formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n) ≫
      (restrictionNormalSourceIso P Q R eReg n).hom = (eReg n).hom ≫ biprod.inr := by
  have : R.PreservesZeroMorphisms := inferInstance
  apply biprod.hom_ext <;>
    simp only [restrictionNormalSourceIso, Iso.trans_hom, Category.assoc,
      Functor.mapBiprod_hom, biprod.mapIso_hom, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.inr_fst, biprod.inr_snd,
      Category.comp_id, CategoryTheory.Limits.comp_zero]
  all_goals simp only [← Category.assoc, ← Functor.map_comp, biprod.inr_fst, biprod.inr_snd,
    CategoryTheory.Functor.map_id, Functor.map_zero, Category.id_comp,
      CategoryTheory.Limits.zero_comp]

include hReg hTheta

/-- The normal-form map is preserved when regular restriction and the logarithmic product are. -/
lemma restrictionNormalSourceIso_normal (n : ℕ) :
    (restrictionNormalSourceIso P Q R eReg n).hom ≫ logNormalFormSheaf Q n =
      R.map (logNormalFormSheaf P n) ≫ (eOpen (n + 1)).hom := by
  have : R.PreservesZeroMorphisms := inferInstance
  have : PreservesFiniteBiproducts R := inferInstance
  have : PreservesBiproductsOfShape WalkingPair R := inferInstance
  have : PreservesBinaryBiproducts R := preservesBinaryBiproducts_of_preservesBiproducts R
  apply (cancel_epi (R.mapBiprod (formsSheaf k P.ambient.obj (n + 1))
    (formsSheaf k P.ambient.obj n)).inv).1
  apply biprod.hom_ext'
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc]
    rw [restrictionNormalSourceIso_inl, Category.assoc, inl_logNormalFormSheaf,
      ← hReg, ← Functor.map_comp, inl_logNormalFormSheaf]
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc]
    rw [restrictionNormalSourceIso_inr, Category.assoc, inr_logNormalFormSheaf]
    change (eReg n).hom ≫ formsSheafPullback Q.j.hom n ≫ openThetaWedgeSheaf Q n = _
    rw [← Category.assoc, ← hReg n, Category.assoc, ← hTheta n]
    simp only [← Category.assoc, ← Functor.map_comp, inr_logNormalFormSheaf]
    rfl

variable [R.PreservesMonomorphisms] [R.PreservesEpimorphisms]

private def restrictionLogSuccIso (n : ℕ) : R.obj (logSheaf P (n + 1)) ≅ logSheaf Q (n + 1) := by
  let a := (restrictionNormalSourceIso P Q R eReg n).inv ≫ R.map (logMkSheaf P n)
  let b := R.map (logToOpenSheaf P (n + 1)) ≫ (eOpen (n + 1)).hom
  have : Epi a := by dsimp only [a]; infer_instance
  have : Mono b := by dsimp only [b]; infer_instance
  have hab : a ≫ b = logNormalFormSheaf Q n := by
    dsimp only [a, b]
    rw [Category.assoc, ← Category.assoc (R.map _), ← R.map_comp,
      logMkSheaf_comp_logToOpenSheaf,
      ← restrictionNormalSourceIso_normal P Q R eReg eOpen hReg hTheta,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafImageIso Q n

private lemma restrictionLogSuccIso_hom_comp (n : ℕ) :
    (restrictionLogSuccIso P Q R eReg eOpen hReg hTheta n).hom ≫ logToOpenSheaf Q (n + 1) =
      R.map (logToOpenSheaf P (n + 1)) ≫ (eOpen (n + 1)).hom := by
  dsimp only [restrictionLogSuccIso, Iso.trans_hom]
  rw [Category.assoc, logSheafImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

omit [R.Additive] hTheta in
private def restrictionLogZeroIso : R.obj (logSheaf P 0) ≅ logSheaf Q 0 := by
  let a := (eReg 0).inv ≫ R.map (regularToLogSheaf P 0)
  let b := R.map (logToOpenSheaf P 0) ≫ (eOpen 0).hom
  have : Epi a := by dsimp only [a]; infer_instance
  have : Mono b := by dsimp only [b]; infer_instance
  have hab : a ≫ b = formsSheafPullback Q.j.hom 0 := by
    dsimp only [a, b]
    rw [Category.assoc, ← Category.assoc (R.map _), ← R.map_comp,
      regularToLogSheaf_comp_logToOpenSheaf, hReg, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  exact image.isoStrongEpiMono a b hab ≪≫ logSheafZeroImageIso Q

omit [R.Additive] hTheta in
private lemma restrictionLogZeroIso_hom_comp :
    (restrictionLogZeroIso P Q R eReg eOpen hReg).hom ≫ logToOpenSheaf Q 0 =
      R.map (logToOpenSheaf P 0) ≫ (eOpen 0).hom := by
  dsimp only [restrictionLogZeroIso, Iso.trans_hom]
  rw [Category.assoc, logSheafZeroImageIso_hom_logToOpenSheaf,
    image.isoStrongEpiMono_hom_comp_ι]

/-- An exact additive comparison identifies the logarithmic image sheaves in every degree.
Degree zero uses the image of regular forms and requires no negative-degree convention. -/
@[no_expose] def restrictionLogIso (n : ℕ) : R.obj (logSheaf P n) ≅ logSheaf Q n :=
  match n with
  | 0 => restrictionLogZeroIso P Q R eReg eOpen hReg
  | n + 1 => restrictionLogSuccIso P Q R eReg eOpen hReg hTheta n

/-- Exact transport of logarithmic image sheaves preserves inclusion in complement forms. -/
lemma restrictionLogIso_hom_comp (n : ℕ) :
    (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom ≫ logToOpenSheaf Q n =
      R.map (logToOpenSheaf P n) ≫ (eOpen n).hom := by
  cases n with
  | zero => exact restrictionLogZeroIso_hom_comp P Q R eReg eOpen hReg
  | succ n => exact restrictionLogSuccIso_hom_comp P Q R eReg eOpen hReg hTheta n

/-- Exact transport of logarithmic images preserves regular forms. -/
lemma restrictionLogIso_regular (n : ℕ) :
    R.map (regularToLogSheaf P n) ≫
        (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom =
      (eReg n).hom ≫ regularToLogSheaf Q n := by
  apply (cancel_mono (logToOpenSheaf Q n)).1
  rw [Category.assoc, restrictionLogIso_hom_comp, ← Category.assoc, ← R.map_comp,
    regularToLogSheaf_comp_logToOpenSheaf, hReg,
    Category.assoc, regularToLogSheaf_comp_logToOpenSheaf]

variable (hD : ∀ n, R.map
    ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) P.j.hom.left.base).map
      (formsSheafD k P.compl.obj n)) ≫ (eOpen (n + 1)).hom =
    (eOpen n).hom ≫ (TopCat.Sheaf.pushforward (ModuleCat.{u} k) Q.j.hom.left.base).map
      (formsSheafD k Q.compl.obj n))
include hD

/-- Exact transport of logarithmic images commutes with the differential. -/
lemma restrictionLogIso_d (n : ℕ) :
    (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom ≫ logSheafD Q n =
      R.map (logSheafD P n) ≫
        (restrictionLogIso P Q R eReg eOpen hReg hTheta (n + 1)).hom := by
  apply (cancel_mono (logToOpenSheaf Q (n + 1))).1
  rw [Category.assoc, logSheafD_comp_logToOpenSheaf, ← Category.assoc,
    restrictionLogIso_hom_comp, Category.assoc, ← hD n, ← Category.assoc,
    ← R.map_comp, ← logSheafD_comp_logToOpenSheaf, R.map_comp,
    Category.assoc, ← restrictionLogIso_hom_comp P Q R eReg eOpen hReg hTheta (n + 1),
    ← Category.assoc]

private instance : R.PreservesZeroMorphisms := inferInstance

/-- Exact transport gives an isomorphism of logarithmic complexes. -/
def restrictionLogComplexIso :
    (R.mapHomologicalComplex (.up ℕ)).obj (logComplexNat P) ≅ logComplexNat Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => restrictionLogIso P Q R eReg eOpen hReg hTheta n) (by
      rintro n _ rfl
      change (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom ≫ logSheafD Q n =
        R.map (logSheafD P n) ≫
          (restrictionLogIso P Q R eReg eOpen hReg hTheta (n + 1)).hom
      exact restrictionLogIso_d P Q R eReg eOpen hReg hTheta hD n)

omit [R.PreservesMonomorphisms] [R.PreservesEpimorphisms] hReg hTheta in
/-- Differential-compatible transport of complement forms gives an isomorphism of complexes. -/
def restrictionOpenComplexIso :
    (R.mapHomologicalComplex (.up ℕ)).obj (openFormsComplexNat P) ≅ openFormsComplexNat Q :=
  HomologicalComplex.Hom.isoOfComponents eOpen (by
    rintro n _ rfl
    simp only [openFormsComplexNat, Functor.mapHomologicalComplex_obj_d, formsComplexNat_d]
    exact (hD n).symm)

/-- The logarithmic and complement complex comparisons preserve their inclusion. -/
lemma restrictionLogComplexIso_toOpen :
    (restrictionLogComplexIso P Q R eReg eOpen hReg hTheta hD).hom ≫ logToOpenComplexNat Q =
      (R.mapHomologicalComplex (.up ℕ)).map (logToOpenComplexNat P) ≫
        (restrictionOpenComplexIso P Q R eOpen hD).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom ≫ logToOpenSheaf Q n =
    R.map (logToOpenSheaf P n) ≫ (eOpen n).hom
  exact restrictionLogIso_hom_comp P Q R eReg eOpen hReg hTheta n

/-- The logarithmic complex comparison has the specified degreewise image comparisons. -/
lemma restrictionLogComplexIso_hom_f (n : ℕ) :
    (restrictionLogComplexIso P Q R eReg eOpen hReg hTheta hD).hom.f n =
      (restrictionLogIso P Q R eReg eOpen hReg hTheta n).hom := rfl

omit [R.PreservesMonomorphisms] [R.PreservesEpimorphisms] hReg hTheta in
/-- The complement complex comparison has the specified degreewise form comparisons. -/
lemma restrictionOpenComplexIso_hom_f (n : ℕ) :
    (restrictionOpenComplexIso P Q R eOpen hD).hom.f n = (eOpen n).hom := rfl

end OrlikSolomon.Geometric.DeRham
