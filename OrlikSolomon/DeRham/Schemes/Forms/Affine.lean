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
* `formsSheafRestrictionIso`: restriction of forms to an open subscheme.
* `formsSheafUnit_isIso_of_isAffineOpen`, `affineOpenFormsComparison`: evaluation on every affine
  open of an arbitrary scheme.
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

section Restriction

variable (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens)

-- The two section algebras have the same ring carrier. Their displayed base actions agree by
-- functoriality of restriction; the local transparency setting identifies those presentations.
set_option backward.isDefEq.respectTransparency false in
/-- The functions on an open of an open subscheme are the functions on its image in the ambient
scheme, with the same base-ring action. -/
def sectionAlgebraRestrictEquiv (V : U.toScheme.Opens) :
    sectionAlgebra k X (U.ι ''ᵁ V) ≃ₐ[k] sectionAlgebra k (Over.mk (U.ι ≫ X.hom)) V where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.map (U.ι ''ᵁ V).leTop.op) r =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ X.hom).appTop ≫
          U.toScheme.presheaf.map V.leTop.op) r
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.toScheme_presheaf_map]
    congr 2
    simp only [Category.assoc]
    rw [← X.left.presheaf.map_comp]
    rfl

/-- The comparison of section algebras keeps the underlying function. -/
lemma sectionAlgebraRestrictEquiv_apply (V : U.toScheme.Opens)
    (a : sectionAlgebra k X (U.ι ''ᵁ V)) : sectionAlgebraRestrictEquiv X U V a = a := rfl

private def formsPresheafRestrictionIso (n : ℕ) :
    U.ι.opensFunctor.op ⋙ formsPresheaf k X n ≅
      formsPresheaf k (Over.mk (U.ι ≫ X.hom)) n := by
  refine NatIso.ofComponents (fun V ↦ LinearEquiv.toModuleIso
    { __ := Forms.mapPower (sectionAlgebraRestrictEquiv X U V.unop).toAlgHom n
      invFun := Forms.mapPower (sectionAlgebraRestrictEquiv X U V.unop).symm.toAlgHom n
      left_inv a := Subtype.ext
        ((Forms.mapEquiv (sectionAlgebraRestrictEquiv X U V.unop)).left_inv a.val)
      right_inv a := Subtype.ext
        ((Forms.mapEquiv (sectionAlgebraRestrictEquiv X U V.unop)).right_inv a.val) }) ?_
  intro V W i
  apply ModuleCat.hom_ext
  change Forms.mapPower (sectionAlgebraRestrictEquiv X U W.unop).toAlgHom n ∘ₗ
      Forms.mapPower (sectionRestriction k X (U.ι.opensFunctor.map i.unop)) n =
    Forms.mapPower (sectionRestriction k (Over.mk (U.ι ≫ X.hom)) i.unop) n ∘ₗ
      Forms.mapPower (sectionAlgebraRestrictEquiv X U V.unop).toAlgHom n
  rw [← Forms.mapPower_comp, ← Forms.mapPower_comp]
  congr 1

private def formsRestrictedSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat k) U.toScheme :=
  ⟨U.ι.opensFunctor.op ⋙ (formsSheaf k X n).obj,
    TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.ι.isOpenEmbedding (formsSheaf k X n).property⟩

-- Restricting the sheafification unit preserves local bijectivity. The image-open functor is
-- cocontinuous because its right adjoint, inverse image of opens, preserves covers.
private theorem formsRestrictedUnit_W (n : ℕ) :
    (_root_.Opens.grothendieckTopology U.toScheme).W
      (Functor.whiskerLeft U.ι.opensFunctor.op (formsSheafUnit k X n)) := by
  have : U.ι.opensFunctor.IsCocontinuous
      (_root_.Opens.grothendieckTopology U.toScheme) (_root_.Opens.grothendieckTopology X.left) :=
    (U.ι.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map _)
  have : Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X.left)
      (formsSheafUnit k X n) := by
    change Presheaf.IsLocallyInjective _ (toSheafify _ (formsPresheaf k X n))
    infer_instance
  have : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X.left)
      (formsSheafUnit k X n) := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ (formsPresheaf k X n))
    infer_instance
  have := Presheaf.isLocallyInjective_whisker (_root_.Opens.grothendieckTopology U.toScheme)
    (_root_.Opens.grothendieckTopology X.left) U.ι.opensFunctor (formsSheafUnit k X n)
  have := Presheaf.isLocallySurjective_whisker (_root_.Opens.grothendieckTopology U.toScheme)
    (_root_.Opens.grothendieckTopology X.left) U.ι.opensFunctor (formsSheafUnit k X n)
  exact (_root_.Opens.grothendieckTopology U.toScheme).W_of_isLocallyBijective _

private def formsSheafRestrictionMap (n : ℕ) :
    formsRestrictedSheaf X U n ⟶ formsSheaf k (Over.mk (U.ι ≫ X.hom)) n :=
  ⟨((formsRestrictedUnit_W X U n) _ (formsSheaf k (Over.mk (U.ι ≫ X.hom)) n).property).2
    ((formsPresheafRestrictionIso X U n).hom ≫
      formsSheafUnit k (Over.mk (U.ι ≫ X.hom)) n) |>.choose⟩

private theorem formsSheafRestrictionMap_unit (n : ℕ) :
    Functor.whiskerLeft U.ι.opensFunctor.op (formsSheafUnit k X n) ≫
      (formsSheafRestrictionMap X U n).hom =
        (formsPresheafRestrictionIso X U n).hom ≫
          formsSheafUnit k (Over.mk (U.ι ≫ X.hom)) n :=
  (((formsRestrictedUnit_W X U n) _ (formsSheaf k (Over.mk (U.ι ≫ X.hom)) n).property).2
    ((formsPresheafRestrictionIso X U n).hom ≫
      formsSheafUnit k (Over.mk (U.ι ≫ X.hom)) n)).choose_spec

private theorem formsSheafRestrictionMap_isIso (n : ℕ) :
    IsIso (formsSheafRestrictionMap X U n) := by
  let J := _root_.Opens.grothendieckTopology U.toScheme
  apply (J.W_sheafToPresheaf_map_iff_isIso _).1
  apply J.W.of_precomp (W' := J.W)
    (Functor.whiskerLeft U.ι.opensFunctor.op (formsSheafUnit k X n))
    (formsSheafRestrictionMap X U n).hom
  · exact formsRestrictedUnit_W X U n
  · rw [formsSheafRestrictionMap_unit]
    exact J.W.comp_mem _ _ (ObjectProperty.isLocal_of_isIso _ _)
      (J.W_toSheafify (formsPresheaf k (Over.mk (U.ι ≫ X.hom)) n))

/-- Relative forms restricted to an open subscheme are its relative forms. The comparison is
induced by the canonical identifications of regular functions on the corresponding opens.

Blueprint: `def:geo-forms-sheaf`, `thm:geo-forms-comparison`. -/
@[no_expose] def formsSheafRestrictionIso (n : ℕ) :
    (U.sheafRestrict (C := ModuleCat k)).obj (formsSheaf k X n) ≅
      formsSheaf k (Over.mk (U.ι ≫ X.hom)) n :=
  @asIso _ _ _ _ (formsSheafRestrictionMap X U n) (formsSheafRestrictionMap_isIso X U n)

/-- The restriction comparison sends a represented form to the same form on the open subscheme. -/
theorem formsSheafRestrictionIso_unit (n : ℕ) (V : U.toScheme.Opens)
    (a : (formsPresheaf k X n).obj (op (U.ι ''ᵁ V))) :
    (formsSheafRestrictionIso X U n).hom.hom.app (op V)
        ((formsSheafUnit k X n).app (op (U.ι ''ᵁ V)) a) =
      (formsSheafUnit k (Over.mk (U.ι ≫ X.hom)) n).app (op V)
        (Forms.mapPower (sectionAlgebraRestrictEquiv X U V).toAlgHom n a) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (formsSheafRestrictionMap_unit X U n) (op V)) a

/-- Sheafification leaves relative forms unchanged on every affine open of an arbitrary scheme.
There is no affineness or smoothness hypothesis on the ambient scheme.

Blueprint: `def:geo-forms-sheaf`, `thm:geo-forms-comparison`. -/
theorem formsSheafUnit_isIso_of_isAffineOpen (hU : IsAffineOpen U) (n : ℕ) :
    IsIso ((formsSheafUnit k X n).app (op U)) := by
  have : IsAffine (Over.mk (U.ι ≫ X.hom)).left := hU
  have := formsSheafRestrictionMap_isIso X U n
  have : IsIso (formsSheafRestrictionMap X U n).hom :=
    (sheafToPresheaf (_root_.Opens.grothendieckTopology U.toScheme) (ModuleCat k)).map_isIso
      (formsSheafRestrictionMap X U n)
  have hi : IsIso ((formsSheafRestrictionMap X U n).hom.app (op ⊤)) :=
    NatIso.isIso_app_of_isIso (formsSheafRestrictionMap X U n).hom (op ⊤)
  have hcomp : IsIso ((Functor.whiskerLeft U.ι.opensFunctor.op (formsSheafUnit k X n) ≫
      (formsSheafRestrictionMap X U n).hom).app (op ⊤)) := by
    rw [formsSheafRestrictionMap_unit]
    change IsIso ((formsPresheafRestrictionIso X U n).hom.app (op ⊤) ≫
      (formsSheafUnit k (Over.mk (U.ι ≫ X.hom)) n).app (op ⊤))
    infer_instance
  change IsIso ((formsSheafUnit k X n).app (op (U.ι ''ᵁ ⊤)) ≫
    (formsSheafRestrictionMap X U n).hom.app (op ⊤)) at hcomp
  have h := @IsIso.of_isIso_comp_right _ _ _ _ _
    ((formsSheafUnit k X n).app (op (U.ι ''ᵁ ⊤)))
    ((formsSheafRestrictionMap X U n).hom.app (op ⊤)) hi hcomp
  rw [Scheme.Opens.ι_image_top] at h
  exact h

variable (hU : IsAffineOpen U)

/-- The canonical degreewise comparison between algebraic forms on an affine open and sections
of the sheaf of relative forms on that open.

Blueprint: `thm:geo-forms-comparison`. -/
def affineOpenFormsComparison (n : ℕ) :
    (⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) ≃ₗ[k]
      (formsSheaf k X n).obj.obj (op U) := by
  have := formsSheafUnit_isIso_of_isAffineOpen X U hU n
  exact (asIso ((formsSheafUnit k X n).app (op U))).toLinearEquiv

/-- The affine-open comparison is the original sheafification map. -/
lemma affineOpenFormsComparison_apply (n : ℕ)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    affineOpenFormsComparison X U hU n a = (formsSheafUnit k X n).app (op U) a := rfl

/-- The affine-open comparison commutes with the differential. -/
@[simp] lemma affineOpenFormsComparison_d (n : ℕ)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    (formsSheafD k X n).hom.app (op U) (affineOpenFormsComparison X U hU n a) =
      affineOpenFormsComparison X U hU (n + 1) (powerD k (sectionAlgebra k X U) n a) :=
  formsSheafD_unit k X n (op U) a

/-- The affine-open comparison preserves exterior products. -/
@[simp] lemma affineOpenFormsComparison_wedge (p q : ℕ)
    (a : ⋀[sectionAlgebra k X U]^p Ω[sectionAlgebra k X U⁄k])
    (b : ⋀[sectionAlgebra k X U]^q Ω[sectionAlgebra k X U⁄k]) :
    formsSheafWedge k X p q (op U) (affineOpenFormsComparison X U hU p a)
      (affineOpenFormsComparison X U hU q b) =
      affineOpenFormsComparison X U hU (p + q) ⟨a.val * b.val, SetLike.mul_mem_graded a.2 b.2⟩ :=
  formsSheafWedge_unit k X p q (op U) a b

/-- The affine-open comparison preserves the degree-zero unit. -/
@[simp] lemma affineOpenFormsComparison_one :
    affineOpenFormsComparison X U hU 0 ⟨1, SetLike.one_mem_graded _⟩ =
      formsSheafOneSection k X (op U) := by
  change (formsSheafUnit k X 0).app (op U) _ =
    (formsSheafUnit k X 0).app (op U) ((formsPresheafOne k X).app (op U) (1 : k))
  rw [formsPresheafOne_one]

end Restriction

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
      affineFormsComparison X n (Forms.mapPower (sectionPullbackTop g) n x) :=
  formsSheafPullback_unit_apply g n (op ⊤) x

/-- The affine comparison intertwines the typed global pullback maps. -/
@[simp] lemma affineFormsComparison_pullTop {X Y : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [IsAffine Y.left] (g : X ⟶ Y) (n : ℕ)
    (x : ⋀[sectionAlgebra k Y ⊤]^n Ω[sectionAlgebra k Y ⊤⁄k]) :
    formsSheafPullbackTop g n (affineFormsComparison Y n x) =
      affineFormsComparison X n (Forms.mapPower (sectionPullbackTop g) n x) :=
  affineFormsComparison_pull g n x

end OrlikSolomon.Geometric.DeRham
