/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms.Pullback
public import Mathlib.AlgebraicGeometry.AffineScheme
public import OrlikSolomon.Geometry.Schemes.ModuleGluing
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
/-!
# Affine evaluation of relative forms

The canonical sheafification map for relative forms is an isomorphism on every distinguished
open of an affine spectrum, including the whole spectrum. The construction uses Mathlib's
associated module sheaf and the existing localization theorem for exterior powers of relative
Kähler differentials.

The comparison on distinguished opens is natural under further restriction. Extending this
comparison to the associated sheaf, and then using the universal property of sheafification,
proves that the original sheafification map has the claimed affine values. The final argument
uses the common underlying additive carriers, so no additional scalar structure is chosen.

## Main results

* `specFormsSheafUnit_isIso`: relative forms are unchanged by sheafification on a basic open.
* `specFormsSheafUnit_top_isIso`: the corresponding comparison on the whole spectrum.
* `specFormsSheafAssociatedIso`: identification with Mathlib's associated module sheaf.
* `formsSheafUnit_top_isIso`, `affineFormsComparison`: evaluation on every affine scheme.
* `affineFormsComparison_d`, `affineFormsComparison_wedge`, `affineFormsComparison_pull`:
  compatibility with the differential, multiplication and arbitrary affine scheme maps.

No smoothness, finite-generation, field, nonzero-ring or rational-point assumption is used.

Blueprint: `def:geo-forms-sheaf` and `thm:geo-forms-comparison`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham

-- Fix the canonical scalar structures before specializing Mathlib's spectrum localization
-- instances to the section algebras used by the forms presheaf.
set_option backward.isDefEq.respectTransparency.types false in
@[instance_reducible] private def canonicalSpecAlgebra (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    Algebra R Γ(Spec R, U) := by infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalSpecLocalization (R : CommRingCat.{u}) (r : R) :
    let : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r) := canonicalSpecAlgebra R _
    IsLocalization.Away r Γ(Spec R, PrimeSpectrum.basicOpen r) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalTildeLocalization (R : CommRingCat.{u}) (M : ModuleCat R) (r : R) :
    IsLocalizedModule.Away r (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom := by
  infer_instance

section Spectrum

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
local notation "XS" => (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))

-- The auxiliary A-linear presheaf uses the same carriers and restrictions as relative forms.
-- Its A-action allows comparison with the associated sheaf of the global A-module of forms.
/-- The canonical map from an algebra to functions on an open of its spectrum, over the base. -/
def specSectionMap (U : (Spec (.of A)).Opens) :
    A →ₐ[k] sectionAlgebra k XS U where
  toRingHom := ((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.map U.leTop.op).hom
  commutes' r := by
    change (Spec (.of A)).presheaf.map U.leTop.op
        ((Scheme.ΓSpecIso (.of A)).inv (algebraMap k A r)) =
      (Spec (.of A)).presheaf.map U.leTop.op
        ((Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv r))
    exact congrArg ((Spec (.of A)).presheaf.map U.leTop.op)
      (ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))) r)

set_option backward.isDefEq.respectTransparency.types false in
private local instance specSectionsAlgebra (U : (Spec (.of A)).Opens) :
    Algebra A Γ(Spec (.of A), U) :=
  canonicalSpecAlgebra (CommRingCat.of A) U
private local instance specFormAlgebra (U : (Spec (.of A)).Opens) :
    Algebra A (sectionAlgebra k XS U) :=
  inferInstanceAs (Algebra A Γ(Spec (.of A), U))

private instance specOpenTower (U : (Spec (.of A)).Opens) :
    IsScalarTower k A (sectionAlgebra k XS U) :=
  IsScalarTower.of_algebraMap_eq fun r => ((specSectionMap (k := k) U).commutes r).symm

@[implicit_reducible] private def specPowerModule (n : ℕ) (U : (Spec (.of A)).Opens) :
    ModuleCat A :=
  ModuleCat.of A (⋀[sectionAlgebra k XS U]^n Ω[sectionAlgebra k XS U⁄k])

private def specPowerMap (n : ℕ) (U : (Spec (.of A)).Opens) :
    ModuleCat.of A (⋀[A]^n Ω[A⁄k]) ⟶ specPowerModule (k := k) n U :=
  ModuleCat.ofHom (powerMap (sectionAlgebra k XS U)
    (KaehlerDifferential.map k k A (sectionAlgebra k XS U)) n)

set_option backward.isDefEq.respectTransparency false in
private instance specPowerMap_localized (n : ℕ) (r : A) :
    IsLocalizedModule.Away r (specPowerMap (k := k) n (PrimeSpectrum.basicOpen r)).hom := by
  let : Algebra A Γ(Spec (.of A), PrimeSpectrum.basicOpen r) :=
    canonicalSpecAlgebra (CommRingCat.of A) _
  let : Algebra A (sectionAlgebra k XS (PrimeSpectrum.basicOpen r)) :=
    specFormAlgebra (k := k) (A := A) _
  have : IsLocalization.Away r
      (sectionAlgebra k XS (PrimeSpectrum.basicOpen r)) := by
    change IsLocalization.Away r Γ(Spec (.of A), PrimeSpectrum.basicOpen r)
    exact canonicalSpecLocalization (CommRingCat.of A) r
  have := specOpenTower (k := k) (A := A) (PrimeSpectrum.basicOpen r)
  exact isLocalizedModule_powerMap_kaehlerMap
    (k := k) (T := sectionAlgebra k XS (PrimeSpectrum.basicOpen r))
    (Submonoid.powers r) n

/-- The canonical map to spectrum sections commutes with restriction of opens. -/
theorem specSectionMap_restrict {U V : (Spec (.of A)).Opens} (i : U ⟶ V) :
    (sectionRestriction k XS i).comp (specSectionMap (k := k) V) = specSectionMap U := by
  ext a
  exact (ConcreteCategory.congr_hom ((Spec (.of A)).presheaf.map_comp V.leTop.op i.op)
    ((Scheme.ΓSpecIso (.of A)).inv a)).symm

private theorem specPowerMap_apply (n : ℕ) (U : (Spec (.of A)).Opens) (x : ⋀[A]^n Ω[A⁄k]) :
    specPowerMap (k := k) n U x = Forms.mapPower (specSectionMap U) n x :=
  (Forms.mapPower_toAlgHom (sectionAlgebra k XS U) n x).symm

private def specPowerRestriction (n : ℕ) {U V : (Spec (.of A)).Opens} (i : U ⟶ V) :
    specPowerModule (k := k) n V ⟶ specPowerModule (k := k) n U :=
  ModuleCat.ofHom
    { __ := (Forms.mapPower (sectionRestriction k XS i) n).toAddHom
      map_smul' a x := by
        change Forms.mapPower (sectionRestriction k XS i) n (a • x) =
          a • Forms.mapPower (sectionRestriction k XS i) n x
        calc
          _ = Forms.mapPower (sectionRestriction k XS i) n
              (algebraMap A (sectionAlgebra k XS V) a • x) :=
            congrArg _ (algebraMap_smul (sectionAlgebra k XS V) a x).symm
          _ = sectionRestriction k XS i (algebraMap A (sectionAlgebra k XS V) a) •
              Forms.mapPower (sectionRestriction k XS i) n x := Forms.mapPower_smul _ _ _ _
          _ = algebraMap A (sectionAlgebra k XS U) a •
              Forms.mapPower (sectionRestriction k XS i) n x := by
            exact congrArg (fun t => t • Forms.mapPower (sectionRestriction k XS i) n x)
              (AlgHom.congr_fun (specSectionMap_restrict i) a)
          _ = _ := algebraMap_smul (sectionAlgebra k XS U) a _ }

private def specFormsPresheaf (n : ℕ) : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat A where
  obj U := specPowerModule (k := k) n U.unop
  map i := specPowerRestriction n i.unop
  map_id U := by
    ext x
    change Forms.mapPower (sectionRestriction k XS (𝟙 U.unop)) n x = x
    rw [sectionRestriction_id, Forms.mapPower_id]
    rfl
  map_comp i j := by
    ext x
    change Forms.mapPower (sectionRestriction k XS (j.unop ≫ i.unop)) n x =
      Forms.mapPower (sectionRestriction k XS j.unop) n
        (Forms.mapPower (sectionRestriction k XS i.unop) n x)
    rw [sectionRestriction_comp, Forms.mapPower_comp]
    rfl

private theorem specPowerMap_res (n : ℕ) {U V : (Spec (.of A)).Opens} (i : U ⟶ V) :
    specPowerMap (k := k) n V ≫ specPowerRestriction n i = specPowerMap n U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Forms.mapPower (sectionRestriction k XS i) n (specPowerMap n V x) = specPowerMap n U x
  rw [specPowerMap_apply, specPowerMap_apply, ← LinearMap.comp_apply,
    ← Forms.mapPower_comp, specSectionMap_restrict]

-- Both maps below exhibit a localization of the same exterior power over A.
private def basisFormIso (n : ℕ) (r : A) :
    specPowerModule (k := k) n (PrimeSpectrum.basicOpen r) ≃ₗ[A]
      (modulesSpecToSheaf.obj (tilde (ModuleCat.of (CommRingCat.of A)
        (⋀[A]^n Ω[A⁄k])))).obj.obj (op (PrimeSpectrum.basicOpen r)) := by
  have := canonicalTildeLocalization (CommRingCat.of A)
    (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) r
  exact IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (specPowerMap (k := k) n (PrimeSpectrum.basicOpen r)).hom
    (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
      (PrimeSpectrum.basicOpen r)).hom

@[simp] private theorem basisFormIso_map (n : ℕ) (r : A) (x : ⋀[A]^n Ω[A⁄k]) :
    basisFormIso (k := k) n r (specPowerMap (k := k) n (PrimeSpectrum.basicOpen r) x) =
      tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
        (PrimeSpectrum.basicOpen r) x := by
  have := canonicalTildeLocalization (CommRingCat.of A)
    (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) r
  exact IsLocalizedModule.linearEquiv_apply _ _ _ x

@[implicit_reducible] private def associatedSpecForms (n : ℕ) :
    TopCat.Sheaf (ModuleCat A) (Spec (CommRingCat.of A)) :=
  modulesSpecToSheaf.obj (tilde (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])))

private def basisFormsNat (n : ℕ) :
    (inducedFunctor (fun r : A =>
      (PrimeSpectrum.basicOpen r : (Spec (.of A)).Opens))).op ⋙
        specFormsPresheaf (k := k) (A := A) n ⟶
    (inducedFunctor (fun r : A =>
      (PrimeSpectrum.basicOpen r : (Spec (.of A)).Opens))).op ⋙
        (associatedSpecForms (k := k) (A := A) n).obj where
  app r := (basisFormIso (k := k) (A := A) n r.unop).toModuleIso.hom
  naturality r s i := by
    apply ModuleCat.hom_ext
    apply IsLocalizedModule.ext (Submonoid.powers (M := A) r.unop)
      (specPowerMap (k := k) (A := A) n
        (PrimeSpectrum.basicOpen (R := A) r.unop)).hom
    · rintro ⟨a, ⟨m, rfl⟩⟩
      rw [map_pow]
      let M := tilde (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
      exact (M.isUnit_algebraMap_end_of_le_basicOpen r.unop i.unop.hom.le).pow m
    · apply LinearMap.ext
      intro x
      change basisFormIso (k := k) (A := A) n s.unop
          (specPowerRestriction n i.unop.hom
            (specPowerMap (k := k) (A := A) n (PrimeSpectrum.basicOpen (R := A) r.unop) x)) =
        (associatedSpecForms (k := k) (A := A) n).obj.map i.unop.hom.op
          (basisFormIso (k := k) (A := A) n r.unop
            (specPowerMap (k := k) (A := A) n (PrimeSpectrum.basicOpen (R := A) r.unop) x))
      have hr := ConcreteCategory.congr_hom (specPowerMap_res (k := k) n i.unop.hom) x
      rw [ModuleCat.comp_apply] at hr
      rw [hr, basisFormIso_map, basisFormIso_map]
      exact (ConcreteCategory.congr_hom
        (tilde.toOpen_res (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
          (PrimeSpectrum.basicOpen (R := A) r.unop)
          (PrimeSpectrum.basicOpen (R := A) s.unop) i.unop.hom) x).symm

-- A presheaf morphism that is an isomorphism on a basis induces bijections on morphisms
-- into every sheaf, because both morphism sets are determined by their basis restrictions.
private theorem W_of_isIso_basis {C : Type (u + 1)} [Category.{u} C] {T : TopCat.{u}}
    {ι : Type u} {B : ι → TopologicalSpace.Opens T}
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    {F G : T.Presheaf C} (f : F ⟶ G) (hf : ∀ i, IsIso (f.app (op (B i)))) :
    (_root_.Opens.grothendieckTopology T).W f := by
  intro H hH
  let HS : TopCat.Sheaf C T := ⟨H, hH⟩
  let eF := TopCat.Sheaf.restrictHomEquivHom F HS hB
  let eG := TopCat.Sheaf.restrictHomEquivHom G HS hB
  let fB := Functor.whiskerLeft (inducedFunctor B).op f
  have : IsIso fB := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun i => hf i.unop
  constructor
  · intro a b hab
    apply eG.symm.injective
    apply (cancel_epi fB).mp
    change Functor.whiskerLeft (inducedFunctor B).op (f ≫ a) =
      Functor.whiskerLeft (inducedFunctor B).op (f ≫ b)
    change f ≫ a = f ≫ b at hab
    exact congrArg (Functor.whiskerLeft (inducedFunctor B).op) hab
  · intro a
    refine ⟨eG (inv fB ≫ eF.symm a), ?_⟩
    apply eF.symm.injective
    change fB ≫ eG.symm (eG (inv fB ≫ eF.symm a)) = eF.symm a
    rw [eG.symm_apply_apply, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

-- Explicit basis arguments keep elaboration from reconstructing the spectrum through its
-- category of opens. The extension has the prescribed localization comparison on the basis.
set_option backward.isDefEq.respectTransparency false in
private def specFormsToAssociated (n : ℕ) :
    specFormsPresheaf (k := k) (A := A) n ⟶ (associatedSpecForms (k := k) (A := A) n).obj :=
  @TopCat.Sheaf.restrictHomEquivHom (ModuleCat.{u} A) inferInstance
    (Spec (.of A) : TopCat) A
    (fun r : A => (PrimeSpectrum.basicOpen r : (Spec (.of A)).Opens))
    (specFormsPresheaf (k := k) (A := A) n) (associatedSpecForms (k := k) (A := A) n)
    PrimeSpectrum.isBasis_basic_opens (basisFormsNat (k := k) (A := A) n)

set_option backward.isDefEq.respectTransparency false in
private theorem specFormsToAssociated_app (n : ℕ) (r : A) :
    (specFormsToAssociated (k := k) (A := A) n).app (op (PrimeSpectrum.basicOpen r)) =
      (basisFormIso (k := k) n r).toModuleIso.hom := by
  have h := @TopCat.Sheaf.extend_hom_app (ModuleCat.{u} A) inferInstance
    (Spec (.of A) : TopCat) A
    (fun r : A => (PrimeSpectrum.basicOpen r : (Spec (.of A)).Opens))
    (specFormsPresheaf (k := k) (A := A) n) (associatedSpecForms (k := k) (A := A) n)
    PrimeSpectrum.isBasis_basic_opens (basisFormsNat (k := k) (A := A) n) r
  exact h

-- Forgetting the scalar actions identifies the two presheaves literally. This suffices to
-- prove the original k-linear unit is an isomorphism, since the forgetful functor reflects it.
private def associatedSpecFormsAdd (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat (Spec (.of A)) :=
  (sheafCompose (_root_.Opens.grothendieckTopology (Spec (.of A)))
    (forget₂ (ModuleCat A) AddCommGrpCat)).obj (associatedSpecForms (k := k) (A := A) n)

private def specFormsAddIso (n : ℕ) :
    formsPresheaf k XS n ⋙ forget₂ (ModuleCat k) AddCommGrpCat ≅
      specFormsPresheaf (k := k) (A := A) n ⋙ forget₂ (ModuleCat A) AddCommGrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

private def specFormsToAssociatedAdd (n : ℕ) :
    formsPresheaf k XS n ⋙ forget₂ (ModuleCat k) AddCommGrpCat ⟶
      (associatedSpecFormsAdd (k := k) (A := A) n).obj :=
  (specFormsAddIso (k := k) (A := A) n).hom ≫
    Functor.whiskerRight (specFormsToAssociated (k := k) (A := A) n)
      (forget₂ (ModuleCat A) AddCommGrpCat)

private theorem specFormsToAssociatedAdd_isIso_app (n : ℕ) (r : A) :
    IsIso ((specFormsToAssociatedAdd (k := k) (A := A) n).app
      (op (PrimeSpectrum.basicOpen r))) := by
  change IsIso ((specFormsAddIso (k := k) (A := A) n).hom.app _ ≫
    (forget₂ (ModuleCat A) AddCommGrpCat).map
      ((specFormsToAssociated (k := k) (A := A) n).app _))
  rw [specFormsToAssociated_app]
  have h₁ : IsIso ((specFormsAddIso (k := k) (A := A) n).hom.app
      (op (PrimeSpectrum.basicOpen r))) :=
    Iso.isIso_hom ((specFormsAddIso (k := k) (A := A) n).app _)
  have h₂ : IsIso ((forget₂ (ModuleCat A) AddCommGrpCat).map
      (basisFormIso (k := k) n r).toModuleIso.hom) :=
    Iso.isIso_hom ((forget₂ (ModuleCat A) AddCommGrpCat).mapIso
      (basisFormIso (k := k) n r).toModuleIso)
  exact IsIso.comp_isIso' h₁ h₂

private theorem specFormsToAssociatedAdd_W (n : ℕ) :
    (_root_.Opens.grothendieckTopology (Spec (.of A))).W
      (specFormsToAssociatedAdd (k := k) (A := A) n) := by
  apply W_of_isIso_basis
    (B := fun r : A => (PrimeSpectrum.basicOpen r : (Spec (.of A)).Opens))
    PrimeSpectrum.isBasis_basic_opens
  exact specFormsToAssociatedAdd_isIso_app (k := k) (A := A) n

private def specFormsSheafAdd (n : ℕ) : TopCat.Sheaf AddCommGrpCat (Spec (.of A)) :=
  (sheafCompose (_root_.Opens.grothendieckTopology (Spec (.of A)))
    (forget₂ (ModuleCat k) AddCommGrpCat)).obj (formsSheaf k XS n)

private def specFormsUnitAdd (n : ℕ) :
    formsPresheaf k XS n ⋙ forget₂ (ModuleCat k) AddCommGrpCat ⟶
      (specFormsSheafAdd (k := k) (A := A) n).obj :=
  Functor.whiskerRight (formsSheafUnit k XS n) (forget₂ (ModuleCat k) AddCommGrpCat)

private theorem specFormsUnitAdd_W (n : ℕ) :
    (_root_.Opens.grothendieckTopology (Spec (.of A))).W
      (specFormsUnitAdd (k := k) (A := A) n) := by
  let J := _root_.Opens.grothendieckTopology (Spec (.of A))
  have hinj : Presheaf.IsLocallyInjective J (specFormsUnitAdd (k := k) (A := A) n) :=
    { equalizerSieve_mem := fun a b h =>
        Presheaf.equalizerSieve_mem J (toSheafify J (formsPresheaf k XS n)) a b h }
  have hsurj : Presheaf.IsLocallySurjective J (specFormsUnitAdd (k := k) (A := A) n) :=
    { imageSieve_mem := fun a => Presheaf.imageSieve_mem J (toSheafify J (formsPresheaf k XS n)) a }
  exact (J.W_iff_isLocallyBijective _).2 ⟨hinj, hsurj⟩

-- The additive sheafification unit has the universal property expressed by W. Extend the
-- comparison through it; uniqueness makes the resulting map independent of this choice.
private def specFormsSheafAddMap (n : ℕ) :
    specFormsSheafAdd (k := k) (A := A) n ⟶ associatedSpecFormsAdd (k := k) (A := A) n :=
  ⟨((specFormsUnitAdd_W (k := k) (A := A) n) _
    (associatedSpecFormsAdd (k := k) (A := A) n).property).2
      (specFormsToAssociatedAdd (k := k) (A := A) n) |>.choose⟩

private theorem specFormsUnitAdd_map (n : ℕ) :
    specFormsUnitAdd (k := k) (A := A) n ≫
      (specFormsSheafAddMap (k := k) (A := A) n).hom =
        specFormsToAssociatedAdd (k := k) (A := A) n :=
  (((specFormsUnitAdd_W (k := k) (A := A) n) _
    (associatedSpecFormsAdd (k := k) (A := A) n).property).2
      (specFormsToAssociatedAdd (k := k) (A := A) n)).choose_spec

private theorem specFormsSheafAddMap_isIso (n : ℕ) :
    IsIso (specFormsSheafAddMap (k := k) (A := A) n) := by
  let J := _root_.Opens.grothendieckTopology (Spec (.of A))
  apply (J.W_sheafToPresheaf_map_iff_isIso _).1
  apply J.W.of_precomp (W' := J.W) (specFormsUnitAdd (k := k) (A := A) n)
    (specFormsSheafAddMap (k := k) (A := A) n).hom
  · exact specFormsUnitAdd_W n
  · rw [specFormsUnitAdd_map]
    exact specFormsToAssociatedAdd_W n

/-- Sheafification leaves relative forms unchanged on a distinguished open of an affine spectrum.
Blueprint: `thm:geo-forms-comparison`. -/
theorem specFormsSheafUnit_isIso (n : ℕ) (r : A) :
    IsIso ((formsSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r))) := by
  have := specFormsSheafAddMap_isIso (k := k) (A := A) n
  have : IsIso ((specFormsSheafAddMap (k := k) (A := A) n).hom.app
      (op (PrimeSpectrum.basicOpen r))) := by infer_instance
  have h : IsIso ((specFormsUnitAdd (k := k) (A := A) n).app
      (op (PrimeSpectrum.basicOpen r))) := by
    apply (isIso_comp_right_iff _
      ((specFormsSheafAddMap (k := k) (A := A) n).hom.app _)).1
    change IsIso ((specFormsUnitAdd (k := k) (A := A) n ≫
      (specFormsSheafAddMap (k := k) (A := A) n).hom).app _)
    rw [specFormsUnitAdd_map]
    exact specFormsToAssociatedAdd_isIso_app (k := k) (A := A) n r
  have : IsIso ((forget₂ (ModuleCat k) AddCommGrpCat).map
      ((formsSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r)))) := h
  exact isIso_of_reflects_iso ((formsSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r)))
    (forget₂ (ModuleCat k) AddCommGrpCat)

/-- Sheafification leaves the global relative forms of an affine spectrum unchanged.
Blueprint: `thm:geo-forms-comparison`. -/
theorem specFormsSheafUnit_top_isIso (n : ℕ) :
    IsIso ((formsSheafUnit k XS n).app (op ⊤)) := by
  have h := specFormsSheafUnit_isIso (k := k) (A := A) n (1 : A)
  have he : (PrimeSpectrum.basicOpen (1 : A) : (Spec (.of A)).Opens) = ⊤ :=
    PrimeSpectrum.basicOpen_one
  rw [he] at h
  exact h


/-- Relative form sheaves on a spectrum are the associated sheaves of the old global form modules,
after forgetting scalar actions. This isomorphism uses the existing sheafified carriers.
Blueprint: `def:geo-forms-sheaf`. -/
@[no_expose] def specFormsSheafAssociatedIso (n : ℕ) :
    (sheafCompose (_root_.Opens.grothendieckTopology (Spec (.of A)))
      (forget₂ (ModuleCat k) AddCommGrpCat)).obj (formsSheaf k XS n) ≅
    (sheafCompose (_root_.Opens.grothendieckTopology (Spec (.of A)))
      (forget₂ (ModuleCat A) AddCommGrpCat)).obj
        (modulesSpecToSheaf.obj (tilde (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])))) := by
  let e := @asIso _ _ _ _ (specFormsSheafAddMap (k := k) (A := A) n)
    (specFormsSheafAddMap_isIso (k := k) (A := A) n)
  exact e

/-- On a distinguished open, the associated-sheaf comparison sends algebraic forms to their
usual localization, with no choice of coordinates or representatives. -/
lemma specFormsSheafAssociatedIso_unit (n : ℕ) (r : A) (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsSheafAssociatedIso (k := k) (A := A) n).hom.hom.app
        (op (PrimeSpectrum.basicOpen r))
      ((formsSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r))
        (Forms.mapPower (specSectionMap (k := k) (PrimeSpectrum.basicOpen r)) n x)) =
      tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
        (PrimeSpectrum.basicOpen r) x := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (specFormsUnitAdd_map (k := k) (A := A) n)
      (op (PrimeSpectrum.basicOpen r)))
    (Forms.mapPower (specSectionMap (k := k) (PrimeSpectrum.basicOpen r)) n x)
  refine h.trans ?_
  change (specFormsToAssociated (k := k) (A := A) n).app
      (op (PrimeSpectrum.basicOpen r))
      (Forms.mapPower (specSectionMap (k := k) (PrimeSpectrum.basicOpen r)) n x) = _
  rw [specFormsToAssociated_app]
  exact (congrArg (basisFormIso (k := k) n r)
    (specPowerMap_apply n (PrimeSpectrum.basicOpen r) x).symm).trans (basisFormIso_map n r x)

end Spectrum

variable {k : Type u} [CommRing k]

private def affineOverIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    X ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (sectionAlgebra k X ⊤)))) := by
  refine Over.isoMk X.left.isoSpec ?_
  change X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (sectionAlgebra k X ⊤))) = X.hom
  have h : CommRingCat.ofHom (algebraMap k (sectionAlgebra k X ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop := by
    change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.map (⊤ : X.left.Opens).leTop.op = _
    have hi : (⊤ : X.left.Opens).leTop.op = 𝟙 (op ⊤) := rfl
    rw [hi, X.left.presheaf.map_id, Category.comp_id]
  rw [h, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Sheafification leaves global relative forms unchanged on every affine scheme.
Blueprint: `thm:geo-forms-comparison`. -/
instance formsSheafUnit_top_isIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (n : ℕ) : IsIso ((formsSheafUnit k X n).app (op ⊤)) := by
  have hspec := specFormsSheafUnit_top_isIso (k := k) (A := sectionAlgebra k X ⊤) n
  let Z := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (sectionAlgebra k X ⊤))))
  let e : X ≅ Z := affineOverIso X
  have := formsSheafPullback_isIso e.hom n
  have := formsPresheafPullback_isIso e.hom n
  have : IsIso (formsSheafPullback e.hom n).hom :=
    (sheafToPresheaf (_root_.Opens.grothendieckTopology Z.left) (ModuleCat k)).map_isIso
      (formsSheafPullback e.hom n)
  have : IsIso ((formsSheafUnit k Z n).app (op ⊤)) := hspec
  have hu := NatTrans.congr_app (formsSheafPullback_unit e.hom n) (op ⊤)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  have hcomp : IsIso ((formsPresheafPullback e.hom n).app (op ⊤) ≫
      (formsSheafUnit k X n).app (op (e.hom.left ⁻¹ᵁ ⊤))) := by
    have h : IsIso ((formsSheafUnit k Z n).app (op ⊤) ≫
        (formsSheafPullback e.hom n).hom.app (op ⊤)) := inferInstance
    exact hu ▸ h
  have hx := IsIso.of_isIso_comp_left ((formsPresheafPullback e.hom n).app (op ⊤))
    ((formsSheafUnit k X n).app (op (e.hom.left ⁻¹ᵁ ⊤)))
  change IsIso ((formsSheafUnit k X n).app (op ⊤)) at hx
  exact hx

variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

/-- The canonical degreewise comparison from algebraic forms on global sections to sheaf forms.
It is the original sheafification map, with its inverse supplied by affine evaluation.
Blueprint: `thm:geo-forms-comparison`. -/
def affineFormsComparison (n : ℕ) :
    (⋀[sectionAlgebra k X ⊤]^n Ω[sectionAlgebra k X ⊤⁄k]) ≃ₗ[k]
      (formsSheaf k X n).obj.obj (op ⊤) :=
  (asIso ((formsSheafUnit k X n).app (op ⊤))).toLinearEquiv

/-- The affine comparison acts by the canonical sheafification map. -/
lemma affineFormsComparison_apply (n : ℕ)
    (x : ⋀[sectionAlgebra k X ⊤]^n Ω[sectionAlgebra k X ⊤⁄k]) :
    affineFormsComparison X n x = (formsSheafUnit k X n).app (op ⊤) x := rfl

/-- The affine comparison commutes with the differential. -/
@[simp] lemma affineFormsComparison_d (n : ℕ)
    (x : ⋀[sectionAlgebra k X ⊤]^n Ω[sectionAlgebra k X ⊤⁄k]) :
    (formsSheafD k X n).hom.app (op ⊤) (affineFormsComparison X n x) =
      affineFormsComparison X (n + 1) (powerD k (sectionAlgebra k X ⊤) n x) :=
  formsSheafD_unit k X n (op ⊤) x

/-- The affine comparison preserves exterior products. -/
@[simp] lemma affineFormsComparison_wedge (p q : ℕ)
    (a : ⋀[sectionAlgebra k X ⊤]^p Ω[sectionAlgebra k X ⊤⁄k])
    (b : ⋀[sectionAlgebra k X ⊤]^q Ω[sectionAlgebra k X ⊤⁄k]) :
    formsSheafWedge k X p q (op ⊤) (affineFormsComparison X p a)
      (affineFormsComparison X q b) =
      affineFormsComparison X (p + q) ⟨a.val * b.val, SetLike.mul_mem_graded a.2 b.2⟩ :=
  formsSheafWedge_unit k X p q (op ⊤) a b

/-- The affine comparison preserves the degree-zero unit. -/
@[simp] lemma affineFormsComparison_one :
    affineFormsComparison X 0 ⟨1, SetLike.one_mem_graded _⟩ =
      formsSheafOneSection k X (op ⊤) := by
  change (formsSheafUnit k X 0).app (op ⊤) _ =
    (formsSheafUnit k X 0).app (op ⊤) ((formsPresheafOne k X).app (op ⊤) (1 : k))
  rw [formsPresheafOne_one]

variable {X} {Y : Over (Spec (CommRingCat.of k))}
variable [IsAffine Y.left]

/-- On affine schemes, geometric pullback is the existing algebraic pullback of global forms. -/
lemma affineFormsComparison_pull (g : X ⟶ Y) (n : ℕ)
    (x : ⋀[sectionAlgebra k Y ⊤]^n Ω[sectionAlgebra k Y ⊤⁄k]) :
    (formsSheafPullback g n).hom.app (op ⊤) (affineFormsComparison Y n x) =
      affineFormsComparison X n (Forms.mapPower (sectionPullback g ⊤) n x) :=
  formsSheafPullback_unit_apply g n (op ⊤) x

end OrlikSolomon.Geometric.DeRham
