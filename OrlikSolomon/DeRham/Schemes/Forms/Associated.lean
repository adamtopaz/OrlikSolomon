/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms.Affine

/-!
# Structure-sheaf-linear affine comparison for relative forms

On every affine open, module sheafification identifies algebraic forms with sections over the
actual ring of regular functions. On a spectrum, the canonical tilde-global-sections counit
upgrades this to an isomorphism of structure-sheaf modules with the associated sheaf of the
algebraic form module. Its formulas retain the usual representatives and localization fractions.

## Main definitions and results

* `affineOpenModuleFormsComparison`: evaluation as modules over regular functions.
* `specFormsModuleToOpen`: the canonical map from algebraic forms to module-sheaf sections.
* `specFormsModuleSheaf_isLocalizing`: localization on distinguished opens.
* `specFormsModuleSheafAssociatedIso`: the associated-sheaf comparison as structure-sheaf modules.
* `specFormsModuleSheafAssociatedIso_unit`, `specFormsModuleSheafAssociatedIso_fraction`:
  the comparison on representatives and fractions, typed at the actual additive section carriers.
* `specFormsModuleSheafPushforwardAssociatedIso`: affine pushforward as the associated sheaf of
  the same form module with scalars restricted along the ring map.
* `specFormsSheafAssociatedBaseIso`: the comparison as sheaves of base-ring modules, with
  representative formulas on every open.

The base ring and algebra are arbitrary commutative rings; no smoothness, finite generation,
flatness or nonzero-ring hypothesis is required. There are no geometric-domain imports.

Blueprint: `def:geo-forms-sheaf`, `thm:geo-forms-comparison`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham

section Spectrum

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
local notation "XS" => (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))

-- Canonical section structures agree with the displayed section algebra carriers.
@[instance_reducible] private def canonicalSpecAlgebra (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    Algebra R Γ(Spec R, U) := by infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private local instance specSectionsAlgebra (U : (Spec (.of A)).Opens) :
    Algebra A Γ(Spec (.of A), U) := canonicalSpecAlgebra (CommRingCat.of A) U

private theorem canonicalSpecLocalization (R : CommRingCat.{u}) (r : R) :
    let : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r) := canonicalSpecAlgebra R _
    IsLocalization.Away r Γ(Spec R, PrimeSpectrum.basicOpen r) := by
  infer_instance

private local instance specFormAlgebra (U : (Spec (.of A)).Opens) :
    Algebra A (sectionAlgebra k XS U) :=
  inferInstanceAs (Algebra A Γ(Spec (.of A), U))

private local instance specOpenTower (U : (Spec (.of A)).Opens) :
    IsScalarTower k A (sectionAlgebra k XS U) :=
  IsScalarTower.of_algebraMap_eq fun r => ((specSectionMap (k := k) U).commutes r).symm

-- The spectrum and section-algebra presentations have the same carriers and canonical actions.
-- Limit the extra transparency to declarations that compare these presentations explicitly.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical `A`-linear map from algebraic forms to module-sheaf sections on an open of
`Spec A`. The `A`-action on sections is the one supplied by `modulesSpecToSheaf`. -/
def specFormsModuleToOpen (n : ℕ) (U : (Spec (.of A)).Opens) :
    ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]) ⟶
      (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)).obj.obj (op U) := by
  refine ModuleCat.ofHom (X := ModuleCat.of A (⋀[A]^n Ω[A⁄k]))
    (Y := (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)).obj.obj (op U)) ?_
  exact
    { toFun x := (formsModuleSheafUnit k XS n).app (op U)
        (Forms.mapPower (specSectionMap U) n x)
      map_add' x y := by simp only [map_add]
      map_smul' r x := by
        rw [Forms.mapPower_smul]
        exact ((formsModuleSheafUnit k XS n).app (op U)).hom.map_smul
          (specSectionMap U r) _ }

/-- The canonical map to module-sheaf sections first restricts the algebraic form and then applies
module sheafification. -/
lemma specFormsModuleToOpen_apply (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    specFormsModuleToOpen (k := k) (A := A) n U x =
      (formsModuleSheafUnit k XS n).app (op U)
        (Forms.mapPower (specSectionMap U) n x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map to module-sheaf forms commutes with restriction to smaller opens. -/
lemma specFormsModuleToOpen_res (n : ℕ) {U V : (Spec (.of A)).Opens} (i : U ⟶ V) :
    specFormsModuleToOpen (k := k) (A := A) n V ≫
      (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)).obj.map i.op =
        specFormsModuleToOpen n U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (formsModuleSheaf k XS n).val.map i.op
      ((formsModuleSheafUnit k XS n).app (op V) (Forms.mapPower (specSectionMap V) n x)) = _
  rw [← ModuleCat.comp_apply]
  rw [← (formsModuleSheafUnit k XS n).naturality i.op]
  change (formsModuleSheafUnit k XS n).app (op U)
    (Forms.mapPower (sectionRestriction k XS i) n (Forms.mapPower (specSectionMap V) n x)) = _
  rw [← LinearMap.comp_apply, ← Forms.mapPower_comp, specSectionMap_restrict]
  rfl

/-- The module-valued sheafification map agrees with its base-linear version under the public
comparison of carriers. -/
theorem formsModuleSheafUnit_compare (X : Over (Spec (CommRingCat.of k)))
    (n : ℕ) (U : X.left.Opens)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    (formsModuleSheafBaseIso k X n U).hom ((formsModuleSheafUnit k X n).app (op U) a) =
      (formsSheafUnit k X n).app (op U) a := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (formsModuleSheafUnit_presheaf k X n) (op U)) a
  change (eqToHom (formsModuleSheaf_presheaf k X n)).app (op U)
    ((formsModuleSheafUnit k X n).app (op U) a) = _ at h
  exact (formsModuleSheaf_presheaf_hom_app k X n U _).symm.trans h

/-- Sheafification of relative forms is an isomorphism of modules over the ring of functions on
any affine open. No affineness or smoothness hypothesis is imposed on the ambient scheme.

Blueprint: `thm:geo-forms-comparison`. -/
theorem formsModuleSheafUnit_isIso_of_isAffineOpen (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    IsIso ((formsModuleSheafUnit k X n).app (op U)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  apply Function.Bijective.of_comp_left
    (hf := (ConcreteCategory.bijective_of_isIso (formsModuleSheafBaseIso k X n U).hom).1)
  change Function.Bijective (fun a =>
    (formsModuleSheafBaseIso k X n U).hom ((formsModuleSheafUnit k X n).app (op U) a))
  have he : (fun a => (formsModuleSheafBaseIso k X n U).hom
      ((formsModuleSheafUnit k X n).app (op U) a)) =
        fun a => (formsSheafUnit k X n).app (op U) a :=
    funext (formsModuleSheafUnit_compare X n U)
  rw [he]
  have := formsSheafUnit_isIso_of_isAffineOpen X U hU n
  exact ConcreteCategory.bijective_of_isIso ((formsSheafUnit k X n).app (op U))

/-- Algebraic forms on an affine open are its sections of the structure-sheaf module of forms.
The scalar ring is the actual ring of regular functions on the open.

Blueprint: `thm:geo-forms-comparison`. -/
def affineOpenModuleFormsComparison (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    (⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) ≃ₗ[Γ(X.left, U)]
      Γ(formsModuleSheaf k X n, U) := by
  have := formsModuleSheafUnit_isIso_of_isAffineOpen X U hU n
  exact (asIso ((formsModuleSheafUnit k X n).app (op U))).toLinearEquiv

/-- The structure-sheaf-linear affine-open comparison is the original module sheafification map. -/
lemma affineOpenModuleFormsComparison_apply (X : Over (Spec (CommRingCat.of k)))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    affineOpenModuleFormsComparison X U hU n a =
      (formsModuleSheafUnit k X n).app (op U) a := rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a distinguished open, module-sheaf forms are the localization of algebraic forms.
Blueprint: `thm:geo-forms-comparison`. -/
instance specFormsModuleToOpen_isLocalized (n : ℕ) (r : A) :
    IsLocalizedModule.Away r (specFormsModuleToOpen (k := k) (A := A) n
      (PrimeSpectrum.basicOpen r)).hom := by
  have : IsLocalization.Away r (sectionAlgebra k XS (PrimeSpectrum.basicOpen r)) := by
    change IsLocalization.Away r Γ(Spec (.of A), PrimeSpectrum.basicOpen r)
    exact canonicalSpecLocalization (CommRingCat.of A) r
  let f := powerMap (sectionAlgebra k XS (PrimeSpectrum.basicOpen r))
    (KaehlerDifferential.map k k A (sectionAlgebra k XS (PrimeSpectrum.basicOpen r))) n
  have hf : IsLocalizedModule.Away r f := isLocalizedModule_powerMap_kaehlerMap _ n
  let := ModuleCat.isModule ((modulesSpecToSheaf (R := CommRingCat.of A)).obj
    (formsModuleSheaf k XS n) |>.obj.obj (op (PrimeSpectrum.basicOpen r)))
  let e : (⋀[sectionAlgebra k XS (PrimeSpectrum.basicOpen r)]^n
      Ω[sectionAlgebra k XS (PrimeSpectrum.basicOpen r)⁄k]) →ₗ[A]
      (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)).obj.obj
        (op (PrimeSpectrum.basicOpen r)) :=
    { toFun x := (formsModuleSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r)) x
      map_add' x y := map_add _ _ _
      map_smul' a x :=
        ((formsModuleSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r))).hom.map_smul
        (algebraMap A (sectionAlgebra k XS (PrimeSpectrum.basicOpen r)) a) x }
  have he : Function.Bijective e := by
    have := formsModuleSheafUnit_isIso_of_isAffineOpen XS (PrimeSpectrum.basicOpen r)
      (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of A) r) n
    exact ConcreteCategory.bijective_of_isIso ((formsModuleSheafUnit k XS n).app
      (op (PrimeSpectrum.basicOpen r)))
  have h := IsLocalizedModule.of_linearEquiv (.powers r) f (LinearEquiv.ofBijective e he)
  convert h using 1
  apply LinearMap.ext
  intro x
  change _ = (formsModuleSheafUnit k XS n).app (op (PrimeSpectrum.basicOpen r)) (f x)
  rw [← Forms.mapPower_toAlgHom]
  rfl

private lemma specFormsModuleToOpen_top_bijective (n : ℕ) :
    Function.Bijective (specFormsModuleToOpen (k := k) (A := A) n ⊤) := by
  let e₀ := (specFormsSheafAssociatedIso (k := k) (A := A) n).hom.hom.app (op ⊤)
  let e := fun a : Γ(formsModuleSheaf k XS n, ⊤) =>
    e₀ ((formsModuleSheafBaseIso k XS n ⊤).hom a)
  have he : Function.Injective e := (ConcreteCategory.bijective_of_isIso e₀).1.comp
    (ConcreteCategory.bijective_of_isIso (formsModuleSheafBaseIso k XS n ⊤).hom).1
  have hx (x : ⋀[A]^n Ω[A⁄k]) :
      e (specFormsModuleToOpen (k := k) (A := A) n ⊤ x) =
        tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) ⊤ x := by
    change e₀ ((formsModuleSheafBaseIso k XS n ⊤).hom
      ((formsModuleSheafUnit k XS n).app (op ⊤)
        (Forms.mapPower (specSectionMap ⊤) n x))) = _
    rw [formsModuleSheafUnit_compare XS n ⊤]
    have h := specFormsSheafAssociatedIso_unit (k := k) n (1 : A) x
    rw [PrimeSpectrum.basicOpen_one] at h
    exact h
  apply Function.Bijective.of_comp_left (hf := he)
  change Function.Bijective (fun x => e (specFormsModuleToOpen (k := k) (A := A) n ⊤ x))
  simp only [hx]
  have := tilde.isIso_toOpen_top (M := ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k]))
  exact ConcreteCategory.bijective_of_isIso
    (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) ⊤)

/-- Global algebraic forms identify with global sections of the structure-sheaf module of forms. -/
instance specFormsModuleToOpen_top_isIso (n : ℕ) :
    IsIso (specFormsModuleToOpen (k := k) (A := A) n ⊤) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (specFormsModuleToOpen_top_bijective n)

/-- On `Spec A`, the structure-sheaf module of forms is localizing in the sense of Mathlib's
associated-module sheaf API. -/
theorem specFormsModuleSheaf_isLocalizing (n : ℕ) :
    IsLocalizing (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)) := by
  intro r
  rw [← IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    (specFormsModuleToOpen (k := k) (A := A) n ⊤).hom (specFormsModuleToOpen_top_bijective n),
    ← ModuleCat.hom_comp, specFormsModuleToOpen_res n (PrimeSpectrum.basicOpen r).leTop]
  exact specFormsModuleToOpen_isLocalized n r

/-- The canonical associated-module counit is invertible for relative forms on a spectrum. -/
instance specFormsModuleSheaf_fromTildeΓ_isIso (n : ℕ) :
    IsIso (formsModuleSheaf k XS n).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).2 (specFormsModuleSheaf_isLocalizing n)

set_option backward.isDefEq.respectTransparency false in
/-- Relative forms on a spectrum are the associated sheaf of algebraic forms, as modules over
the structure sheaf. The comparison uses the canonical tilde-global-sections adjunction.

Blueprint: `def:geo-forms-sheaf`, `thm:geo-forms-comparison`. -/
@[no_expose] def specFormsModuleSheafAssociatedIso (n : ℕ) :
    formsModuleSheaf k XS n ≅ tilde (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) := by
  have := specFormsModuleSheaf_fromTildeΓ_isIso (k := k) (A := A) n
  exact ((tilde.functor (CommRingCat.of A)).mapIso (asIso (specFormsModuleToOpen n ⊤)) ≪≫
    asIso (formsModuleSheaf k XS n).fromTildeΓ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse associated-sheaf comparison takes the image of an algebraic form to its
canonical module-sheaf section, on every open. -/
private lemma specFormsModuleSheafAssociatedIso_inv_toOpen_raw (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).inv.app U
      (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U x) =
        specFormsModuleToOpen (k := k) (A := A) n U x := by
  change (modulesSpecToSheaf.map (tilde.map (specFormsModuleToOpen (k := k) (A := A) n ⊤) ≫
    (formsModuleSheaf k XS n).fromTildeΓ)).hom.app (op U)
      (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U x) = _
  rw [← ModuleCat.comp_apply]
  change (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U ≫
    (modulesSpecToSheaf.map
      (tilde.map (specFormsModuleToOpen (k := k) (A := A) n ⊤))).hom.app (op U) ≫
    (modulesSpecToSheaf.map (formsModuleSheaf k XS n).fromTildeΓ).hom.app (op U)) x = _
  rw [tilde.toOpen_map_app_assoc, Scheme.Modules.toOpen_fromTildeΓ_app]
  exact ConcreteCategory.congr_hom (specFormsModuleToOpen_res (k := k) n U.leTop) x

/-- The associated-sheaf comparison takes a canonical module-sheaf section to the corresponding
section of the associated module sheaf, on every open. -/
private lemma specFormsModuleSheafAssociatedIso_toOpen_raw (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).hom.app U
        (specFormsModuleToOpen (k := k) (A := A) n U x) =
      tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U x := by
  let eU := ((Scheme.Modules.toPresheaf _).mapIso
    (specFormsModuleSheafAssociatedIso (k := k) (A := A) n)).app (op U)
  apply (ConcreteCategory.bijective_of_isIso eU.inv).1
  change eU.inv (eU.hom _) = eU.inv _
  exact (eU.hom_inv_id_apply _).trans
    (specFormsModuleSheafAssociatedIso_inv_toOpen_raw n U x).symm

/-- Canonical algebraic forms as sections of the structure-sheaf module, typed at its actual
additive section carrier. This bridge permits further rewriting by ordinary additive rules. -/
def specFormsModuleSection (n : ℕ) (U : (Spec (.of A)).Opens) :
    (⋀[A]^n Ω[A⁄k]) →+ Γ(formsModuleSheaf k XS n, U) :=
  ((formsModuleSheafUnit k XS n).app (op U)).hom.toAddMonoidHom.comp
    (Forms.mapPower (specSectionMap U) n).toAddMonoidHom

/-- The typed module-sheaf section is the canonical map to its base-linear section presentation. -/
lemma specFormsModuleToOpen_eq_section (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    dsimp% specFormsModuleToOpen (k := k) (A := A) n U x = specFormsModuleSection n U x := rfl

/-- The typed module-sheaf section is represented by the restriction of the algebraic form. -/
lemma specFormsModuleSection_apply (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    specFormsModuleSection (k := k) (A := A) n U x =
      (formsModuleSheafUnit k XS n).app (op U)
        (Forms.mapPower (specSectionMap U) n x) := rfl

/-- Canonical algebraic forms as sections of the associated sheaf, typed at its actual additive
section carrier. The construction is Mathlib's `tilde.toOpen` on the same elements. -/
def specFormsAssociatedSection (n : ℕ) (U : (Spec (.of A)).Opens) :
    (⋀[A]^n Ω[A⁄k]) →+ Γ(tilde (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])), U) :=
  (tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U).hom.toAddMonoidHom

/-- The typed section of the associated sheaf is Mathlib's localization map. -/
lemma tilde_toOpen_eq_specFormsAssociatedSection (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    dsimp% tilde.toOpen (ModuleCat.of (CommRingCat.of A) (⋀[A]^n Ω[A⁄k])) U x =
      specFormsAssociatedSection (k := k) n U x := rfl

/-- The inverse associated-sheaf comparison preserves canonical sections on every open. -/
lemma specFormsModuleSheafAssociatedIso_inv_toOpen (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).inv.app U
      (specFormsAssociatedSection (k := k) n U x) =
        specFormsModuleSection (k := k) n U x :=
  specFormsModuleSheafAssociatedIso_inv_toOpen_raw n U x

/-- The associated-sheaf comparison preserves canonical sections on every open. -/
lemma specFormsModuleSheafAssociatedIso_toOpen (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).hom.app U
      (specFormsModuleSection (k := k) n U x) =
        specFormsAssociatedSection (k := k) n U x :=
  specFormsModuleSheafAssociatedIso_toOpen_raw n U x

/-- On every open, the structure-sheaf-linear comparison sends an algebraic representative to
its usual section of the associated module sheaf. -/
lemma specFormsModuleSheafAssociatedIso_unit (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).hom.app U
      ((formsModuleSheafUnit k XS n).app (op U)
        (Forms.mapPower (specSectionMap U) n x)) =
      specFormsAssociatedSection (k := k) n U x :=
  specFormsModuleSheafAssociatedIso_toOpen n U x

/-- The associated-sheaf comparison respects multiplication of represented forms by arbitrary
regular functions. On distinguished opens this includes every localization fraction. -/
lemma specFormsModuleSheafAssociatedIso_smul_toOpen (n : ℕ) (U : (Spec (.of A)).Opens)
    (a : Γ(Spec (.of A), U)) (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsModuleSheafAssociatedIso (k := k) n).hom.app U
      (a • specFormsModuleSection (k := k) n U x) =
        a • specFormsAssociatedSection (k := k) n U x := by
  rw [Scheme.Modules.Hom.app_smul, specFormsModuleSheafAssociatedIso_toOpen]

/-- The comparison sends a represented form divided by an invertible regular function to the
same fraction in the associated module sheaf. This applies on every distinguished open, with any
power of its defining function as denominator. -/
lemma specFormsModuleSheafAssociatedIso_fraction (n : ℕ) (U : (Spec (.of A)).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) (s : Γ(Spec (.of A), U)ˣ) :
    (specFormsModuleSheafAssociatedIso (k := k) n).hom.app U
      ((↑(s⁻¹) : Γ(Spec (.of A), U)) • specFormsModuleSection (k := k) n U x) =
      (↑(s⁻¹) : Γ(Spec (.of A), U)) • specFormsAssociatedSection (k := k) n U x :=
  specFormsModuleSheafAssociatedIso_smul_toOpen n U _ x

omit [Algebra k A] in
/-- Pushing module-sheaf forms forward along a morphism of affine spectra preserves the canonical
associated-module comparison. No flatness or compatibility with the base algebra is required for
this assertion about structure-sheaf modules. -/
theorem specFormsModuleSheafPushforward_fromTildeΓ_isIso {B : Type u} [CommRing B]
    [Algebra k B] (φ : A →+* B) (n : ℕ) :
    IsIso ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).obj
      (formsModuleSheaf k (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap k B)))) n)).fromTildeΓ := by
  have := specFormsModuleSheaf_fromTildeΓ_isIso (k := k) (A := B) n
  exact isIso_fromTildeΓ_pushforward (CommRingCat.ofHom φ) _

omit [Algebra k A] in
set_option backward.isDefEq.respectTransparency false in
private def specFormsModulePushforwardGlobalIso {B : Type u} [CommRing B] [Algebra k B]
    (φ : A →+* B) (n : ℕ) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of (CommRingCat.of B) (⋀[B]^n Ω[B⁄k])) ≅
      (modulesSpecToSheaf.obj
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).obj
          (formsModuleSheaf k (Over.mk
            (Spec.map (CommRingCat.ofHom (algebraMap k B)))) n))).obj.obj (op ⊤) := by
  let e := (pushforwardCompModulesSpecToSheafIso (CommRingCat.ofHom φ)).app
    (formsModuleSheaf k (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))) n)
  let h := ((TopCat.Sheaf.forget _ _) ⋙ (evaluation _ _).obj (op ⊤)).mapIso e
  have := specFormsModuleToOpen_top_isIso (k := k) (A := B) n
  exact (ModuleCat.restrictScalars φ).mapIso
    (asIso (specFormsModuleToOpen (k := k) (A := B) n ⊤)) ≪≫ h.symm

omit [Algebra k A] in
set_option backward.isDefEq.respectTransparency false in
/-- Forms on an affine spectrum, pushed forward along any morphism of spectra, are the associated
sheaf of the algebraic form module with scalars restricted along the ring map. The isomorphism is
induced by the canonical global-section comparison and the tilde-global-sections adjunction.

No flatness, smoothness or finite-generation assumption is required. -/
@[no_expose] def specFormsModuleSheafPushforwardAssociatedIso {B : Type u} [CommRing B]
    [Algebra k B] (φ : A →+* B) (n : ℕ) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).obj
      (formsModuleSheaf k (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))) n) ≅
        tilde ((ModuleCat.restrictScalars φ).obj
          (ModuleCat.of (CommRingCat.of B) (⋀[B]^n Ω[B⁄k]))) := by
  have := specFormsModuleSheafPushforward_fromTildeΓ_isIso (k := k) φ n
  exact ((tilde.functor (CommRingCat.of A)).mapIso
    (specFormsModulePushforwardGlobalIso (k := k) φ n) ≪≫ asIso
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).obj
        (formsModuleSheaf k (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap k B)))) n)).fromTildeΓ).symm

end Spectrum

section Base

variable {k : Type u} [CommRing k] {A : CommRingCat.{u}} [Algebra k A]
local notation "XS" => (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))

/-- The direct base-ring form sheaf agrees with the base restriction of its structure-sheaf
module. The scalar actions agree by functoriality of regular functions over the base. -/
private def specFormsModuleSheafBaseIso (n : ℕ) :
    formsSheaf k XS n ≅
      (sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).obj
          (modulesSpecToSheaf.obj (formsModuleSheaf k XS n)) := by
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso ?_
  refine NatIso.ofComponents (fun U => ?_) ?_
  · let e := formsModuleSheafBaseIso k XS n U.unop
    let N : ModuleCat k := ((sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).obj
          (modulesSpecToSheaf.obj (formsModuleSheaf k XS n))).obj.obj U
    refine LinearEquiv.toModuleIso (m₂ := N.isModule)
      (X₁ := (formsSheaf k XS n).obj.obj U)
      (X₂ := ((sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).obj
          (modulesSpecToSheaf.obj (formsModuleSheaf k XS n))).obj.obj U)
      { toFun := e.inv
        invFun := e.hom
        left_inv := e.inv_hom_id_apply
        right_inv := e.hom_inv_id_apply
        map_add' := map_add _
        map_smul' r a := ?_ }
    change e.inv (r • a) =
      ((Spec A).presheaf.map U.unop.leTop.op
        ((Scheme.ΓSpecIso A).inv (algebraMap k A r))) • e.inv a
    rw [e.inv.hom.map_smul]
    change (show Γ(Spec A, U.unop) from
      algebraMap k (sectionAlgebra k XS U.unop) r) • e.inv a =
      ((Spec A).presheaf.map U.unop.leTop.op ((Scheme.ΓSpecIso A).inv (algebraMap k A r))) • e.inv a
    exact congrArg (fun s : Γ(Spec A, U.unop) => s • e.inv a)
      ((specSectionMap (k := k) U.unop).commutes r).symm
  · intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (formsModuleSheafBaseIso k XS n V.unop).inv
      ((formsSheaf k XS n).obj.map i a) =
      (formsModuleSheaf k XS n).presheaf.map i
        ((formsModuleSheafBaseIso k XS n U.unop).inv a)
    have h := ConcreteCategory.congr_hom
      ((eqToHom (formsModuleSheaf_presheaf k XS n).symm).naturality i) a
    exact (formsModuleSheaf_presheaf_inv_app k XS n V.unop _).symm.trans
      (h.trans (congrArg (fun z => (formsModuleSheaf k XS n).presheaf.map i z)
        (formsModuleSheaf_presheaf_inv_app k XS n U.unop a)))

/-- Relative forms on a spectrum agree, as sheaves of base-ring modules, with the associated
sheaf of algebraic forms with scalars restricted from the algebra to the base.

Blueprint: `def:geo-forms-sheaf`, `thm:geo-forms-comparison`. -/
@[no_expose] def specFormsSheafAssociatedBaseIso (n : ℕ) :
    formsSheaf k XS n ≅
      (sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).obj
          (modulesSpecToSheaf.obj (tilde (ModuleCat.of A (⋀[A]^n Ω[A⁄k])))) :=
  specFormsModuleSheafBaseIso n ≪≫
    (modulesSpecToSheaf ⋙ sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
      (ModuleCat.restrictScalars (algebraMap k A))).mapIso
        (specFormsModuleSheafAssociatedIso (k := k) (A := A) n)

/-- A canonical algebraic form as a section of the base-ring version of its associated sheaf.
The target is the actual base-linear sheaf carrier, for ordinary additive rewriting. -/
def specFormsAssociatedBaseSection (n : ℕ) (U : (Spec A).Opens) :
    (⋀[A]^n Ω[A⁄k]) →+
      ((sheafCompose (_root_.Opens.grothendieckTopology (Spec A))
        (ModuleCat.restrictScalars (algebraMap k A))).obj
          (modulesSpecToSheaf.obj (tilde (ModuleCat.of A (⋀[A]^n Ω[A⁄k]))))).obj.obj (op U) :=
  (tilde.toOpen (ModuleCat.of A (⋀[A]^n Ω[A⁄k])) U).hom.toAddMonoidHom

/-- The base-linear associated-sheaf comparison preserves canonical algebraic representatives
on every open of the spectrum. -/
lemma specFormsSheafAssociatedBaseIso_unit (n : ℕ) (U : (Spec A).Opens) (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsSheafAssociatedBaseIso (k := k) (A := A) n).hom.hom.app (op U)
      ((formsSheafUnit k XS n).app (op U) (Forms.mapPower (specSectionMap U) n x)) =
        specFormsAssociatedBaseSection (k := k) n U x := by
  change (specFormsModuleSheafAssociatedIso (k := k) (A := A) n).hom.app U
    ((formsModuleSheafBaseIso k XS n U).inv
      ((formsSheafUnit k XS n).app (op U) (Forms.mapPower (specSectionMap U) n x))) = _
  let a := Forms.mapPower (specSectionMap U) n x
  let e := formsModuleSheafBaseIso k XS n U
  have he : e.inv ((formsSheafUnit k XS n).app (op U) a) =
      (formsModuleSheafUnit k XS n).app (op U) a :=
    (congrArg (fun z => e.inv z) (formsModuleSheafUnit_compare XS n U a)).symm.trans
      (e.hom_inv_id_apply _)
  exact (congrArg (fun z =>
    (specFormsModuleSheafAssociatedIso (k := k) (A := A) n).hom.app U z) he).trans
      (specFormsModuleSheafAssociatedIso_unit n U x)

/-- The typed base-linear associated section agrees with Mathlib's localization map. -/
lemma tilde_toOpen_eq_specFormsAssociatedBaseSection (n : ℕ) (U : (Spec A).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    dsimp% tilde.toOpen (ModuleCat.of A (⋀[A]^n Ω[A⁄k])) U x =
      specFormsAssociatedBaseSection (k := k) n U x := rfl

/-- The inverse base-linear comparison takes a canonical associated section to its represented
form in the original sheaf. -/
lemma specFormsSheafAssociatedBaseIso_inv_unit (n : ℕ) (U : (Spec A).Opens)
    (x : ⋀[A]^n Ω[A⁄k]) :
    (specFormsSheafAssociatedBaseIso (k := k) (A := A) n).inv.hom.app (op U)
      (specFormsAssociatedBaseSection (k := k) n U x) =
        (formsSheafUnit k XS n).app (op U) (Forms.mapPower (specSectionMap U) n x) := by
  let e := ((sheafToPresheaf _ _).mapIso
    (specFormsSheafAssociatedBaseIso (k := k) (A := A) n)).app (op U)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  exact (e.inv_hom_id_apply _).trans (specFormsSheafAssociatedBaseIso_unit n U x).symm

end Base

end OrlikSolomon.Geometric.DeRham
