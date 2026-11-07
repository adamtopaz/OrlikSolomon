/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Log
public import OrlikSolomon.DeRham.Schemes.Log.AffineImage

/-!
# Affine logarithmic comparison and neighborhoods of principal pairs

For a geometric principal pair `P = (X, Z, U, f)` and an affine open `V` of `X`,
`affineNeighborhoodPair P V` is the pair of actual open restrictions
`(V, i⁻¹ V, j⁻¹ V, f|V)`. Its three objects are smooth and affine. Smoothness of the
closed and open parts follows from their open inclusions into `Z` and `U`, while
affineness follows from the restricted closed immersion and principal-open certificate.
No closure of the original domain under arbitrary open restrictions is assumed.

`affineNeighborhoodAlgebraicPair` applies the existing affine pair duality to obtain
the smooth algebraic pair of section rings. Its closed part is canonically the quotient
by the equation (`affineNeighborhoodQuotientEquiv`), and its open part is an arbitrary
localization away from that equation through the specified pullback map.
The construction works over any commutative base ring, including unit equations and
empty schemes.

`affineLogComparison` identifies algebraic logarithmic forms on the section-ring pair
of an affine geometric pair with its global logarithmic sections. It preserves the
inclusion into complement forms, regular forms, and the differential. The resulting
`affineLogComplexIso` identifies the two logarithmic complexes. The proof uses the
associated-sheaf image comparison in `AffineImage`, followed by affine pair duality.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k] {D : SmoothDomain k}

/-- Restrict a geometric principal pair to an affine open of its ambient scheme, as a pair in
`SmoothDomain.aff k`. Its divisor and complement are the literal inverse-image open schemes;
all smoothness and principal-pair certificates are inherited from the original pair.

Blueprint: the affine-neighborhood construction in `thm:geo-log-sheaves`. -/
@[implicit_reducible]
def affineNeighborhoodPair (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) : DivisorPair (SmoothDomain.aff k) := by
  have : IsAffine V.1.toScheme := V.2
  have hi : IsClosedImmersion (P.i.hom.left ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict P.isClosedImmersion_i V.1
  have hj : IsOpenImmersion (P.j.hom.left ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict P.isOpenImmersion_j V.1
  have hjRange : (P.j.hom.left ∣_ V.1).opensRange =
      V.1.toScheme.basicOpen (V.1.ι.appTop P.eqn) := by
    have h := Scheme.Hom.opensRange_comp_of_isIso
      (isPullback_morphismRestrict P.j.hom.left V.1).isoPullback.hom
      (pullback.fst V.1.ι P.j.hom.left)
    simpa only [IsPullback.isoPullback_hom_fst] using
      h.trans (opensRange_pullback_fst_of_opensRange_eq P.opensRange_j V.1.ι)
  have : IsAffine (P.i.hom.left ⁻¹ᵁ V.1).toScheme :=
    isAffine_of_isAffineHom (P.i.hom.left ∣_ V.1)
  have : IsAffine (P.j.hom.left ⁻¹ᵁ V.1).toScheme :=
    isAffine_of_opensRange_eq hjRange
  exact {
    ambient := ⟨Over.mk (V.1.ι ≫ P.ambient.obj.hom),
      inferInstanceAs (IsAffine V.1.toScheme),
      inferInstanceAs (Smooth (V.1.ι ≫ P.ambient.obj.hom))⟩
    closed := ⟨Over.mk ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom),
      inferInstanceAs (IsAffine (P.i.hom.left ⁻¹ᵁ V.1).toScheme),
      inferInstanceAs (Smooth ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom))⟩
    compl := ⟨Over.mk ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom),
      inferInstanceAs (IsAffine (P.j.hom.left ⁻¹ᵁ V.1).toScheme),
      inferInstanceAs (Smooth ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom))⟩
    i := ObjectProperty.homMk (Over.homMk (P.i.hom.left ∣_ V.1) (by
      dsimp
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))
    j := ObjectProperty.homMk (Over.homMk (P.j.hom.left ∣_ V.1) (by
      dsimp
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))
    eqn := V.1.ι.appTop P.eqn
    isRegularSection_eqn := by
      intro W
      change P.ambient.obj.left.presheaf.map
          (homOfLE (V.1.ι.image_mono (le_top : W ≤ ⊤))).op
        (P.ambient.obj.left.presheaf.map (homOfLE le_top).op P.eqn) ∈
          nonZeroDivisors Γ(P.ambient.obj.left, V.1.ι ''ᵁ W)
      rw [presheaf_map_presheaf_map]
      exact P.isRegularSection_eqn _
    isClosedImmersion_i := hi
    ker_i := by
      change (P.i.hom.left ∣_ V.1).ker = principalIdealSheaf (V.1.ι.appTop P.eqn)
      rw [← (isPullback_morphismRestrict P.i.hom.left V.1).isoPullback_hom_fst,
        Scheme.Hom.ker_comp_of_isIso]
      exact ker_pullback_fst_of_ker_eq P.ker_i V.1.ι
    isOpenImmersion_j := hj
    opensRange_j := hjRange }


/-- The ambient is the affine open scheme with the restricted structure map to the base. -/
lemma affineNeighborhoodPair_ambient_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).ambient.obj = Over.mk (V.1.ι ≫ P.ambient.obj.hom) := rfl

/-- The divisor is the inverse-image open scheme in the original divisor. -/
lemma affineNeighborhoodPair_closed_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).closed.obj =
      Over.mk ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom) := rfl

/-- The complement is the inverse-image open scheme in the original complement. -/
lemma affineNeighborhoodPair_compl_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).compl.obj =
      Over.mk ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom) := rfl

/-- The local equation is the restriction of the global equation. -/
@[simp] lemma affineNeighborhoodPair_eqn (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).eqn = V.1.ι.appTop P.eqn := rfl

/-- The closed map is the restriction of the original closed immersion. -/
@[simp] lemma affineNeighborhoodPair_i_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).i.hom.left = P.i.hom.left ∣_ V.1 := rfl

/-- The open map is the restriction of the original open immersion. -/
@[simp] lemma affineNeighborhoodPair_j_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).j.hom.left = P.j.hom.left ∣_ V.1 := rfl

/-- The open inclusions of the three restricted schemes form a transverse map to the original
pair in its original domain. The equation multiplier is `1`. -/
def affineNeighborhoodInclusion (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    DivisorPair.ofLE (SmoothDomain.aff_le D) (affineNeighborhoodPair P V) ⟶ P where
  ambient := ObjectProperty.homMk (Over.homMk V.1.ι rfl)
  closed := ObjectProperty.homMk (Over.homMk (P.i.hom.left ⁻¹ᵁ V.1).ι rfl)
  compl := ObjectProperty.homMk (Over.homMk (P.j.hom.left ⁻¹ᵁ V.1).ι rfl)
  i_comp := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (morphismRestrict_ι _ _))
  j_comp := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (morphismRestrict_ι _ _))
  associated_eqn := .refl _

/-- The ambient component of the neighborhood inclusion is the open inclusion of `V`. -/
@[simp] lemma affineNeighborhoodInclusion_ambient_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).ambient.hom.left = V.1.ι := rfl

/-- The divisor component of the neighborhood inclusion is its inverse-image open inclusion. -/
@[simp] lemma affineNeighborhoodInclusion_closed_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).closed.hom.left = (P.i.hom.left ⁻¹ᵁ V.1).ι := rfl

/-- The complement component of the neighborhood inclusion is its inverse-image open inclusion. -/
@[simp] lemma affineNeighborhoodInclusion_compl_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).compl.hom.left = (P.j.hom.left ⁻¹ᵁ V.1).ι := rfl

/-- The smooth algebraic principal pair of section rings on an affine neighborhood.
The specified maps are precisely pullback along the restricted immersions, and the
localization certificate applies to the actual section ring of the open complement.

Blueprint: the algebraic local input to `thm:geo-log-sheaves`. -/
@[implicit_reducible]
def affineNeighborhoodAlgebraicPair (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) : OrlikSolomon.DivisorPair k :=
  DivisorPair.globalSections (affineNeighborhoodPair P V)

/-- The algebraic equation is the same restricted regular function. -/
lemma affineNeighborhoodAlgebraicPair_eqn (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodAlgebraicPair P V).eqn = V.1.ι.appTop P.eqn := rfl

/-- The algebraic closed map pulls functions back along the restricted closed immersion. -/
@[simp] lemma affineNeighborhoodAlgebraicPair_i_apply (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    (affineNeighborhoodAlgebraicPair P V).i a = (P.i.hom.left ∣_ V.1).appTop a := rfl

/-- The algebraic open map pulls functions back along the restricted open immersion. -/
@[simp] lemma affineNeighborhoodAlgebraicPair_j_apply (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    (affineNeighborhoodAlgebraicPair P V).j a = (P.j.hom.left ∣_ V.1).appTop a := rfl

/-- The section ring of the restricted divisor is the quotient of the ambient section ring
by the restricted equation, with no nonemptiness or nontriviality hypothesis. -/
def affineNeighborhoodQuotientEquiv (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    let Q := affineNeighborhoodAlgebraicPair P V
    (Q.ambient ⧸ Ideal.span {Q.eqn}) ≃ₐ[k] Q.closed :=
  (Ideal.quotientEquivAlgOfEq k (affineNeighborhoodAlgebraicPair P V).ker_i.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (affineNeighborhoodAlgebraicPair P V).surjective_i)

/-- The quotient comparison sends the class of a function to its pullback to the divisor. -/
@[simp] lemma affineNeighborhoodQuotientEquiv_mk (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    affineNeighborhoodQuotientEquiv P V (Ideal.Quotient.mk _ a) =
      (affineNeighborhoodAlgebraicPair P V).i a := by
  simp only [affineNeighborhoodQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]


open OrlikSolomon.DeRham

variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

/-- The affine counit identifies spectrum functions with their original global sections. -/
private lemma specGlobalSectionsIso_inv_sectionPullbackTop :
    (sectionPullbackTop (specGlobalSectionsIso X).inv).comp
      (specSectionMap (k := k) (A := globalSections X) ⊤) =
        (globalSectionsAlgEquiv X).toAlgHom := by
  ext a
  change X.left.toSpecΓ.appTop
    ((Spec (CommRingCat.of (globalSections X))).presheaf.map (⊤ : (Spec _).Opens).leTop.op
      ((Scheme.ΓSpecIso (CommRingCat.of (globalSections X))).inv a)) = a
  rw [Scheme.toSpecΓ_appTop]
  have h : (⊤ : (Spec (CommRingCat.of (globalSections X))).Opens).leTop.op = 𝟙 _ := rfl
  rw [h, CategoryTheory.Functor.map_id]
  exact (Scheme.ΓSpecIso (CommRingCat.of (globalSections X))).inv_hom_id_apply a

/-- Pullback along the affine counit preserves global algebraic form representatives. -/
private lemma specGlobalSectionsIso_inv_formsSheafPullback_unit (n : ℕ)
    (x : ⋀[globalSections X]^n Ω[globalSections X⁄k]) :
    formsSheafPullbackTop (specGlobalSectionsIso X).inv n
      ((formsSheafUnit k (spec (globalSections X)) n).app (op ⊤)
        (Forms.mapPower (specSectionMap (k := k) (A := globalSections X) ⊤) n x)) =
          globalFormsEquiv X n x := by
  change formsSheafPullbackTop (specGlobalSectionsIso X).inv n
    (affineFormsComparison (spec (globalSections X)) n
      (Forms.mapPower (specSectionMap (k := k) (A := globalSections X) ⊤) n x)) = _
  rw [affineFormsComparison_pullTop, globalFormsEquiv_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← Forms.mapPower_comp,
    specGlobalSectionsIso_inv_sectionPullbackTop]

-- This is the canonical bundled action, recorded locally for the CommRingCat API.
private local instance globalSectionsRingAlgebra :
    Algebra k (CommRingCat.of (globalSections X)) :=
  inferInstanceAs (Algebra k (globalSections X))

variable {A : CommRingCat.{u}} [Algebra k A]
/-- The affine counit preserves the typed global representative of an affine direct image. -/
private lemma specGlobalSectionsIso_inv_formsSheafPullback_section
    (φ : A →ₐ[k] globalSections X) (n : ℕ)
    (x : ⋀[globalSections X]^n Ω[globalSections X⁄k]) :
    dsimp% formsSheafPullbackTop (specGlobalSectionsIso X).inv n
      (specFormsSheafPushforwardBaseSection (B := CommRingCat.of (globalSections X)) φ n ⊤ x) =
        globalFormsEquiv X n x :=
  specGlobalSectionsIso_inv_formsSheafPullback_unit X n x

variable {D : SmoothDomain k}
/-- Inclusion of global logarithmic forms in global forms on the complement. -/
def logToOpenTop (P : DivisorPair D) (n : ℕ) :
    (logSheaf P n).obj.obj (op ⊤) →ₗ[k]
      (formsSheaf k P.compl.obj n).obj.obj (op ⊤) :=
  ((logToOpenSheaf P n).hom.app (op ⊤)).hom

/-- The map from global regular forms to global logarithmic forms. -/
def regularToLogTop (P : DivisorPair D) (n : ℕ) :
    (formsSheaf k P.ambient.obj n).obj.obj (op ⊤) →ₗ[k]
      (logSheaf P n).obj.obj (op ⊤) :=
  ((regularToLogSheaf P n).hom.app (op ⊤)).hom

private lemma logToOpenTop_injective (P : DivisorPair D) (n : ℕ) :
    Function.Injective (logToOpenTop P n) := by
  have : Mono (logToOpenSheaf P n).hom :=
    (sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left)
      (ModuleCat k)).map_mono _
  have : Mono ((logToOpenSheaf P n).hom.app (op ⊤)) :=
    ((evaluation _ _).obj (op ⊤)).map_mono _
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The complex of global sections of the geometric logarithmic sheaf complex. -/
@[implicit_reducible] def globalLogComplexNat (P : DivisorPair D) :
    CochainComplex (ModuleCat k) ℕ :=
  ((sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left) (ModuleCat k) ⋙
    (evaluation _ _).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).obj (logComplexNat P)

/-- The degreewise terms of the global logarithmic complex are the logarithmic sections. -/
@[simp] lemma globalLogComplexNat_X (P : DivisorPair D) (n : ℕ) :
    (globalLogComplexNat P).X n = (logSheaf P n).obj.obj (op ⊤) := rfl

/-- The differential on global logarithmic forms is induced by the sheaf differential. -/
@[simp] lemma globalLogComplexNat_d (P : DivisorPair D) (n : ℕ) :
    (globalLogComplexNat P).d n (n + 1) = (logSheafD P n).hom.app (op ⊤) := rfl

variable (P : DivisorPair (SmoothDomain.aff k))

private lemma counit_eqnUnit :
    Units.map (sectionPullbackTop (Geometric.DivisorPair.counitIso P).inv.compl.hom).toMonoidHom
      P.eqnUnit = (Geometric.DivisorPair.spec (SmoothDomain.aff k) P.globalSections).eqnUnit := by
  apply Units.ext
  change P.compl.obj.left.isoSpec.inv.appTop (P.eqnUnit : Γ(P.compl.obj.left, ⊤)) = _
  rw [Geometric.isoSpec_inv_appTop]
  exact (Geometric.DivisorPair.coe_spec_eqnUnit (SmoothDomain.aff k) P.globalSections).symm

@[implicit_reducible] private def associatedAffineFunctor
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    ModuleCat.{u} (globalSections X) ⥤ TopCat.Sheaf (ModuleCat.{u} k) X.left :=
  affineAssociatedSheafFunctor (A := CommRingCat.of (globalSections X)) ⋙
    TopCat.Sheaf.pushforward (ModuleCat.{u} k) (specGlobalSectionsIso X).hom.left.base

set_option backward.isDefEq.respectTransparency false in
private def associatedAffineGlobalIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (M : ModuleCat.{u} (globalSections X)) [Module k M] [IsScalarTower k (globalSections X) M] :
    ModuleCat.of k M ≅ ((associatedAffineFunctor X).obj M).obj.obj (op ⊤) := by
  let e : ModuleCat.of k M ≅ (ModuleCat.restrictScalars (algebraMap k (globalSections X))).obj M :=
    LinearEquiv.toModuleIso
      (X₁ := ModuleCat.of k M)
      (X₂ := (ModuleCat.restrictScalars (algebraMap k (globalSections X))).obj M)
      { __ := AddEquiv.refl M
        map_smul' r m := (IsScalarTower.algebraMap_smul (globalSections X) r m).symm }
  exact e ≪≫ (ModuleCat.restrictScalars (algebraMap k (globalSections X))).mapIso
    (tilde.isoTop M)

private def affineLogAssociatedIso (n : ℕ) :
    (associatedAffineFunctor P.ambient.obj).obj
      (ModuleCat.of (globalSections P.ambient.obj)
        (logPower k P.globalSections.eqn P.globalSections.compl n)) ≅ logSheaf P n :=
  (TopCat.Sheaf.pushforward (ModuleCat k)
      (specGlobalSectionsIso P.ambient.obj).hom.left.base).mapIso
        (specLogSheafAssociatedIso P.globalSections n) ≪≫
    pairLogSheafIso (Geometric.DivisorPair.counitIso P) (counit_eqnUnit P) n

private instance logPower_scalarTower (n : ℕ) :
    IsScalarTower k (globalSections P.ambient.obj)
      (logPower k P.globalSections.eqn P.globalSections.compl n) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  apply Subtype.ext
  change algebraMap P.globalSections.compl (Forms k P.globalSections.compl)
      (P.globalSections.j (algebraMap k P.globalSections.ambient r)) * x.val =
    algebraMap P.globalSections.compl (Forms k P.globalSections.compl)
      (algebraMap k P.globalSections.compl r) * x.val
  rw [(SmoothAlg.algHom P.globalSections.j).commutes]

/-- Algebraic logarithmic forms on an affine section-ring pair are precisely the global
sections of its geometric logarithmic sheaf. This comparison applies over every commutative
base ring, with no nonemptiness hypothesis. Blueprint: `thm:geo-log-sheaves`. -/
@[no_expose] def affineLogComparison (n : ℕ) :
    logPower k P.globalSections.eqn P.globalSections.compl n ≃ₗ[k]
      (logSheaf P n).obj.obj (op ⊤) :=
  (associatedAffineGlobalIso P.ambient.obj
    (ModuleCat.of (globalSections P.ambient.obj)
      (logPower k P.globalSections.eqn P.globalSections.compl n)) ≪≫
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤)).mapIso
      (affineLogAssociatedIso P n))).toLinearEquiv

private lemma counitOpen_inv_section (n : ℕ)
    (x : ⋀[P.globalSections.compl]^n Ω[P.globalSections.compl⁄k]) :
    (pairOpenFormsIso (Geometric.DivisorPair.counitIso P) n).inv.hom.app (op ⊤)
      (specFormsSheafPushforwardBaseSection (A := CommRingCat.of P.globalSections.ambient)
        (B := CommRingCat.of P.globalSections.compl) (SmoothAlg.algHom P.globalSections.j) n ⊤ x) =
      globalFormsEquiv P.compl.obj n x := by
  let e := ((sheafToPresheaf _ _).mapIso
    (pairOpenFormsIso (Geometric.DivisorPair.counitIso P) n)).app (op ⊤)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change e.hom (e.inv _) = e.hom _
  refine (e.inv_hom_id_apply _).trans (Eq.trans ?_ (pairOpenFormsIso_hom_appTop
    (Geometric.DivisorPair.counitIso P) n (globalFormsEquiv P.compl.obj n x)).symm)
  change _ = formsSheafPullbackTop (specGlobalSectionsIso P.compl.obj).hom n
    (globalFormsEquiv P.compl.obj n x)
  rw [← specGlobalSectionsIso_inv_formsSheafPullback_section P.compl.obj
    (A := CommRingCat.of P.globalSections.ambient) (SmoothAlg.algHom P.globalSections.j) n x,
    ← LinearMap.comp_apply,
    ← formsSheafPullbackTop_comp, Iso.hom_inv_id, formsSheafPullbackTop_id]
  rfl

private lemma associatedAffineGlobalIso_apply (X : Over (Spec (CommRingCat.of k)))
    [IsAffine X.left] (M : ModuleCat.{u} (globalSections X))
    [Module k M] [IsScalarTower k (globalSections X) M] (x : M) :
    (associatedAffineGlobalIso X M).hom x =
      affineAssociatedSection (k := k) (A := CommRingCat.of (globalSections X)) M ⊤ x := rfl

private lemma affineLogAssociatedIso_hom_comp (n : ℕ) :
    (affineLogAssociatedIso P n).hom ≫ logToOpenSheaf P n =
      (TopCat.Sheaf.pushforward (ModuleCat k)
        (specGlobalSectionsIso P.ambient.obj).hom.left.base).map
          ((affineAssociatedSheafFunctor (k := k)
              (A := CommRingCat.of P.globalSections.ambient)).map
            (ModuleCat.ofHom (logPowerToPower k P.globalSections.eqn P.globalSections.compl n)) ≫
          (specOpenFormsAssociatedIso P.globalSections n).hom) ≫
      (pairOpenFormsIso (Geometric.DivisorPair.counitIso P) n).inv := by
  change ((TopCat.Sheaf.pushforward (ModuleCat k)
    (Geometric.DivisorPair.counitIso P).inv.ambient.hom.left.base).map
      (specLogSheafAssociatedIso P.globalSections n).hom ≫
    (pairLogSheafIso (Geometric.DivisorPair.counitIso P) (counit_eqnUnit P) n).hom) ≫
      logToOpenSheaf P n = _
  rw [Category.assoc, pairLogSheafIso_hom_comp, ← Category.assoc, ← Functor.map_comp,
    specLogSheafAssociatedIso_hom_comp]
  rfl

private lemma affineLogComparison_toOpen_raw (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n) :
    (logToOpenSheaf P n).hom.app (op ⊤) (affineLogComparison P n x) =
      globalFormsEquiv P.compl.obj n
        (logPowerToPower k P.globalSections.eqn P.globalSections.compl n x) := by
  let M := ModuleCat.of (globalSections P.ambient.obj)
    (logPower k P.globalSections.eqn P.globalSections.compl n)
  let y := logPowerToPower k P.globalSections.eqn P.globalSections.compl n x
  change (logToOpenSheaf P n).hom.app (op ⊤)
    ((affineLogAssociatedIso P n).hom.hom.app (op ⊤)
      ((associatedAffineGlobalIso P.ambient.obj M).hom x)) = _
  rw [associatedAffineGlobalIso_apply]
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (affineLogAssociatedIso_hom_comp P n)) (op ⊤))
      (affineAssociatedSection (k := k) (A := CommRingCat.of P.globalSections.ambient) M ⊤ x)
  change (logToOpenSheaf P n).hom.app (op ⊤)
      ((affineLogAssociatedIso P n).hom.hom.app (op ⊤)
        (affineAssociatedSection (k := k) (A := CommRingCat.of P.globalSections.ambient) M ⊤ x)) =
    (pairOpenFormsIso (Geometric.DivisorPair.counitIso P) n).inv.hom.app (op ⊤)
      ((specOpenFormsAssociatedIso P.globalSections n).hom.hom.app (op ⊤)
        (((affineAssociatedSheafFunctor (k := k)
          (A := CommRingCat.of P.globalSections.ambient)).map
            (ModuleCat.ofHom
              (logPowerToPower k P.globalSections.eqn P.globalSections.compl n))).hom.app (op ⊤)
          (affineAssociatedSection (k := k)
            (A := CommRingCat.of P.globalSections.ambient) M ⊤ x))) at hh
  refine hh.trans ?_
  rw [affineAssociatedSection_map]
  have hs := specOpenFormsAssociatedIso_hom_section P.globalSections n y
  exact (congrArg (fun z =>
    (pairOpenFormsIso (Geometric.DivisorPair.counitIso P) n).inv.hom.app (op ⊤) z) hs).trans
      (counitOpen_inv_section P n y)

/-- The affine comparison preserves the inclusion into global forms on the complement. -/
lemma affineLogComparison_toOpen (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n) :
    logToOpenTop P n (affineLogComparison P n x) =
      globalFormsEquiv P.compl.obj n
        (logPowerToPower k P.globalSections.eqn P.globalSections.compl n x) :=
  affineLogComparison_toOpen_raw P n x

/-- The affine logarithmic comparison carries regular algebraic forms to regular sheaf forms. -/
lemma affineLogComparison_regular (n : ℕ)
    (x : ⋀[P.globalSections.ambient]^n Ω[P.globalSections.ambient⁄k]) :
    affineLogComparison P n (powerToLog k P.globalSections.eqn P.globalSections.compl n x) =
      regularToLogTop P n (globalFormsEquiv P.ambient.obj n x) := by
  apply logToOpenTop_injective P n
  change (logToOpenSheaf P n).hom.app (op ⊤) _ = _
  rw [affineLogComparison_toOpen_raw, logPowerToPower_powerToLog]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (regularToLogSheaf_comp_logToOpenSheaf P n)) (op ⊤)) (globalFormsEquiv P.ambient.obj n x)
  exact (globalFormsEquiv_pull P.j.hom n x).symm.trans h.symm

/-- The affine logarithmic comparison commutes with the de Rham differential. -/
lemma affineLogComparison_d (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n) :
    (logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x) =
      affineLogComparison P (n + 1)
        (logPowerD k P.globalSections.eqn P.globalSections.compl n x) := by
  apply logToOpenTop_injective P (n + 1)
  have hd := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (logSheafD_comp_logToOpenSheaf P n)) (op ⊤)) (affineLogComparison P n x)
  change (logToOpenSheaf P (n + 1)).hom.app (op ⊤)
      ((logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x)) =
    (formsSheafD k P.compl.obj n).hom.app (op ⊤)
      ((logToOpenSheaf P n).hom.app (op ⊤) (affineLogComparison P n x)) at hd
  change (logToOpenSheaf P (n + 1)).hom.app (op ⊤)
    ((logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x)) =
      (logToOpenSheaf P (n + 1)).hom.app (op ⊤)
        (affineLogComparison P (n + 1)
        (logPowerD k P.globalSections.eqn P.globalSections.compl n x))
  rw [hd, affineLogComparison_toOpen_raw P n x, globalFormsEquiv_d,
    affineLogComparison_toOpen_raw P (n + 1)
      (logPowerD k P.globalSections.eqn P.globalSections.compl n x),
    logPowerToPower_logPowerD]
  rfl

/-- The algebraic and geometric global logarithmic complexes of an affine pair are isomorphic.
Blueprint: `thm:geo-log-sheaves`. -/
def affineLogComplexIso :
    logComplex k P.globalSections.eqn P.globalSections.compl ≅ globalLogComplexNat P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (affineLogComparison P n).toModuleIso) (by
    rintro n _ rfl
    rw [globalLogComplexNat_d, logComplex_d]
    ext x
    change logPower k P.globalSections.eqn P.globalSections.compl n at x
    exact affineLogComparison_d P n x)


/-- The component of the affine logarithmic complex comparison is the degreewise comparison. -/
lemma affineLogComplexIso_hom_f (n : ℕ) :
    (affineLogComplexIso P).hom.f n = (affineLogComparison P n).toModuleIso.hom := rfl

end OrlikSolomon.Geometric.DeRham
