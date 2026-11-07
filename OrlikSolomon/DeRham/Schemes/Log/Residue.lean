/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Affine
public import OrlikSolomon.DeRham.Schemes.Log.Basic
public import OrlikSolomon.DeRham.Log
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Residue and exactness of logarithmic forms on schemes

Regular forms inject into complement forms and hence into the logarithmic image sheaves.
The affine-local argument works over every commutative base ring, with no hypothesis on
characteristic, nontriviality, points, or the ambient domain beyond `SmoothDomain`.

## Main results

* `formsSheafPullback_injective_affineOpen`: injectivity on each affine neighborhood.
* `formsSheafPullback_mono`: the regular-form map to the complement is a monomorphism.
* `regularToLogSheaf_mono`: the left inclusion into logarithmic forms is a monomorphism.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k] {D : SmoothDomain k}

/-- Regular forms of each degree inject into the forms on the principal complement. -/
lemma algebraicRegularForms_injective (Q : OrlikSolomon.DivisorPair k) (n : ℕ) :
    Function.Injective (Forms.mapPower (SmoothAlg.algHom Q.j) n) := by
  intro x y h
  apply Subtype.ext
  exact Q.isSmoothPrincipalPair.map_injective Q.compl
    (congrArg Subtype.val h)

/-- Sections on an open and global sections of its open subscheme have the same base action. -/
def openSectionAlgebraEquiv (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    sectionAlgebra k X U ≃ₐ[k] globalSections (Over.mk (U.ι ≫ X.hom)) :=
  { U.topIso.symm.commRingCatIsoToRingEquiv with
    commutes' r := by
      change U.topIso.inv ((X.left.presheaf.map U.leTop.op)
        (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) =
          (U.ι ≫ X.hom).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)
      rw [Scheme.Hom.comp_appTop]
      have h : X.left.presheaf.map U.leTop.op ≫ U.topIso.inv = U.ι.appTop := by
        change X.left.presheaf.map U.leTop.op ≫
          X.left.presheaf.map (eqToHom U.ι_image_top).op = _
        rw [← Functor.map_comp]
        rfl
      exact ConcreteCategory.congr_hom h _ }

variable {X Y : Over (Spec (CommRingCat.of k))}

-- The restriction appTop presents its codomain using a preimage of the top open.
set_option backward.isDefEq.respectTransparency false in
/-- The section-ring comparison intertwines pullback and the restricted scheme morphism. -/
lemma openSectionAlgebraEquiv_comp (g : X ⟶ Y) (U : Y.left.Opens) :
    (openSectionAlgebraEquiv X (g.left ⁻¹ᵁ U)).toAlgHom.comp (sectionPullback g U) =
      (globalSectionsMap (Over.homMk (g.left ∣_ U) (by
        dsimp
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))).hom.comp
          (openSectionAlgebraEquiv Y U).toAlgHom := by
  have h : U.topIso.inv ≫ (g.left ∣_ U).appTop =
      g.left.app U ≫ (g.left ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    change U.topIso.inv ≫ (g.left.resLE U (g.left ⁻¹ᵁ U) le_rfl).app ⊤ = _
    rw [Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
    congr 1
    simp [Scheme.Hom.appLE]
  ext a
  exact (ConcreteCategory.congr_hom h a).symm

/-- The algebraic pullback of degreewise forms is injective on an affine neighborhood. -/
lemma affineNeighborhoodForms_injective (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Injective (Forms.mapPower (sectionPullback P.j.hom V.1) n) := by
  let Q := affineNeighborhoodAlgebraicPair P V
  let eA := openSectionAlgebraEquiv P.ambient.obj V.1
  let eB := openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1)
  have hj : eB.toAlgHom.comp (sectionPullback P.j.hom V.1) =
      (SmoothAlg.algHom Q.j).comp eA.toAlgHom :=
    openSectionAlgebraEquiv_comp P.j.hom V.1
  intro x y hxy
  have he : Forms.mapPower eA.toAlgHom n x = Forms.mapPower eA.toAlgHom n y := by
    apply algebraicRegularForms_injective Q n
    change (Forms.mapPower (SmoothAlg.algHom Q.j) n ∘ₗ Forms.mapPower eA.toAlgHom n) x =
      (Forms.mapPower (SmoothAlg.algHom Q.j) n ∘ₗ Forms.mapPower eA.toAlgHom n) y
    rw [← Forms.mapPower_comp, ← hj, Forms.mapPower_comp]
    exact congrArg (Forms.mapPower eB.toAlgHom n) hxy
  exact Subtype.ext ((Forms.mapEquiv eA).injective (congrArg Subtype.val he))

/-- Regular sheaf forms inject into complement forms on every affine open of the ambient. -/
lemma formsSheafPullback_injective_affineOpen (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Injective ((formsSheafPullback P.j.hom n).hom.app (op V.1)) := by
  have hV : IsAffineOpen (P.j.hom.left ⁻¹ᵁ V.1) := by
    exact inferInstanceAs (IsAffine (affineNeighborhoodPair P V).compl.obj.left)
  intro x y hxy
  obtain ⟨x, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective x
  obtain ⟨y, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective y
  apply (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).congr_arg
  apply affineNeighborhoodForms_injective P V n
  apply (affineOpenFormsComparison P.compl.obj _ hV n).injective
  change (formsSheafPullback P.j.hom n).hom.app (op V.1)
      ((formsSheafUnit k P.ambient.obj n).app (op V.1) x) =
    (formsSheafPullback P.j.hom n).hom.app (op V.1)
      ((formsSheafUnit k P.ambient.obj n).app (op V.1) y) at hxy
  exact (formsSheafPullback_unit_apply P.j.hom n (op V.1) x).symm.trans
    (hxy.trans (formsSheafPullback_unit_apply P.j.hom n (op V.1) y))

/-- Restricting regular forms to the principal complement is a monomorphism of sheaves. -/
lemma formsSheafPullback_mono (P : DivisorPair D) (n : ℕ) :
    Mono (formsSheafPullback P.j.hom n) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono _).2
  intro x
  apply ConcreteCategory.mono_of_injective
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    P.ambient.obj.left.isBasis_affineOpens
  intro U hU
  exact formsSheafPullback_injective_affineOpen P ⟨U, hU⟩ n

/-- The regular-form inclusion into logarithmic forms is a monomorphism of sheaves. -/
instance regularToLogSheaf_mono (P : DivisorPair D) (n : ℕ) :
    Mono (regularToLogSheaf P n) := by
  have := formsSheafPullback_mono P n
  exact mono_of_mono_fac (regularToLogSheaf_comp_logToOpenSheaf P n)

/-- Pullback of algebraic forms to the smooth divisor is surjective on every affine neighborhood. -/
lemma affineNeighborhoodClosedForms_surjective (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Surjective (Forms.mapPower (sectionPullback P.i.hom V.1) n) := by
  let Q := affineNeighborhoodAlgebraicPair P V
  let eA := openSectionAlgebraEquiv P.ambient.obj V.1
  let eB := openSectionAlgebraEquiv P.closed.obj (P.i.hom.left ⁻¹ᵁ V.1)
  have hi : eB.toAlgHom.comp (sectionPullback P.i.hom V.1) =
      (SmoothAlg.algHom Q.i).comp eA.toAlgHom :=
    openSectionAlgebraEquiv_comp P.i.hom V.1
  intro x
  obtain ⟨z, hz⟩ := Forms.mapPower_surjective Q.surjective_i n
    (Forms.mapPower eB.toAlgHom n x)
  refine ⟨Forms.mapPower eA.symm.toAlgHom n z, ?_⟩
  apply Subtype.ext
  apply (Forms.mapEquiv eB).injective
  change Forms.map eB.toAlgHom
      (Forms.map (sectionPullback P.i.hom V.1)
        (Forms.map eA.symm.toAlgHom z.val)) = Forms.map eB.toAlgHom x.val
  rw [Forms.map_map, hi, ← Forms.map_map]
  rw [show Forms.map eA.toAlgHom (Forms.map eA.symm.toAlgHom z.val) = z.val from
    (Forms.mapEquiv eA).apply_symm_apply z.val]
  exact congrArg Subtype.val hz

/-- Forms on the divisor lift to regular ambient forms on every affine open of the ambient. -/
lemma formsSheafPullback_surjective_affineOpen (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ) :
    Function.Surjective ((formsSheafPullback P.i.hom n).hom.app (op V.1)) := by
  have hV : IsAffineOpen (P.i.hom.left ⁻¹ᵁ V.1) := by
    exact inferInstanceAs (IsAffine (affineNeighborhoodPair P V).closed.obj.left)
  intro x
  obtain ⟨x, rfl⟩ := (affineOpenFormsComparison P.closed.obj _ hV n).surjective x
  obtain ⟨y, hy⟩ := affineNeighborhoodClosedForms_surjective P V n x
  refine ⟨affineOpenFormsComparison P.ambient.obj V.1 V.2 n y, ?_⟩
  exact (formsSheafPullback_unit_apply P.i.hom n (op V.1) y).trans
    (congrArg ((formsSheafUnit k P.closed.obj n).app
      (op (P.i.hom.left ⁻¹ᵁ V.1))) hy)

/-- Restricting forms to the smooth principal divisor is an epimorphism of sheaves.
This is a local assertion, with no global-section exactness claim on a non-affine ambient. -/
lemma formsSheafPullback_epi (P : DivisorPair D) (n : ℕ) :
    Epi (formsSheafPullback P.i.hom n) := by
  constructor
  intro F g h hgh
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _
    (show TopologicalSpace.Opens.IsBasis
        (Set.range (fun V : P.ambient.obj.left.affineOpens => V.1)) by
      simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
        P.ambient.obj.left.isBasis_affineOpens)
  intro U
  ext x
  obtain ⟨y, rfl⟩ := formsSheafPullback_surjective_affineOpen P U n x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) hgh) (op U.1)) y


/-- The section-ring comparison takes a restricted global function to its pullback to the open
subscheme.
-/
lemma openSectionAlgebraEquiv_restrictTop
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) (a : Γ(X.left, ⊤)) :
    openSectionAlgebraEquiv X U (sectionRestriction k X U.leTop a) = U.ι.appTop a := by
  have h : X.left.presheaf.map U.leTop.op ≫ U.topIso.inv = U.ι.appTop := by
    change X.left.presheaf.map U.leTop.op ≫
      X.left.presheaf.map (eqToHom U.ι_image_top).op = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h a

/-- The restricted geometric equation unit is the equation unit of the algebraic affine
neighborhood.
-/
lemma affineNeighborhood_eqnUnit (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    Units.map (openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1)).toMonoidHom
      (Units.map (sectionRestriction k P.compl.obj
        (P.j.hom.left ⁻¹ᵁ V.1).leTop).toMonoidHom
          (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit)) =
      (affineNeighborhoodAlgebraicPair P V).eqnUnit := by
  apply Units.ext
  change openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1)
    (sectionRestriction k P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1).leTop
      (P.eqnUnit : Γ(P.compl.obj.left, ⊤))) = _
  rw [openSectionAlgebraEquiv_restrictTop]
  change (P.j.hom.left ⁻¹ᵁ V.1).ι.appTop (P.eqnUnit : Γ(P.compl.obj.left, ⊤)) =
    (P.j.hom.left ∣_ V.1).appTop (V.1.ι.appTop P.eqn)
  rw [P.coe_eqnUnit]
  have h := congrArg (fun g => g.appTop) (morphismRestrict_ι P.j.hom.left V.1)
  simp only [Scheme.Hom.comp_appTop] at h
  exact (ConcreteCategory.congr_hom h P.eqn).symm

/-- The algebraic normal-form kernel criterion transports through compatible algebra
equivalences.
-/
lemma normalForm_kernel_of_equiv (Q : OrlikSolomon.DivisorPair k)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (j : A →ₐ[k] B) (i : A →ₐ[k] C) (v : Bˣ)
    (eA : A ≃ₐ[k] Q.ambient) (eB : B ≃ₐ[k] Q.compl) (eC : C ≃ₐ[k] Q.closed)
    (hj : eB.toAlgHom.comp j = (SmoothAlg.algHom Q.j).comp eA.toAlgHom)
    (hi : eC.toAlgHom.comp i = (SmoothAlg.algHom Q.i).comp eA.toAlgHom)
    (hu : Units.map eB.toAlgHom.toMonoidHom v = Q.eqnUnit)
    {ω η : Forms k A} (h : Forms.map j ω + dlog k v * Forms.map j η = 0) :
    Forms.map i η = 0 := by
  have hQ : logMk k Q.eqn Q.compl
      (Forms.map eA.toAlgHom ω, Forms.map eA.toAlgHom η) = 0 := by
    apply Subtype.ext
    change Forms.map (SmoothAlg.algHom Q.j) (Forms.map eA.toAlgHom ω) +
      theta k Q.eqn Q.compl * Forms.map (SmoothAlg.algHom Q.j) (Forms.map eA.toAlgHom η) = 0
    change Units.map (eB.toAlgHom : B →* Q.compl) v = Q.eqnUnit at hu
    have hh := congrArg (Forms.map eB.toAlgHom) h
    rw [map_add, map_mul, Forms.map_dlog, map_zero, Forms.map_map, Forms.map_map, hj, hu] at hh
    rw [Q.theta_eq_dlog_eqnUnit, Forms.map_map, Forms.map_map]
    exact hh
  have hz := Q.isSmoothPrincipalPair.map_eq_zero_of_logMk_eq_zero Q.compl hQ
  apply (Forms.mapEquiv eC).injective
  change Forms.map eC.toAlgHom (Forms.map i η) = Forms.map eC.toAlgHom 0
  rw [Forms.map_map, hi, map_zero]
  simpa only [Forms.map_map] using hz

/-- A vanishing normal form on an affine neighborhood has its logarithmic coefficient vanishing
on the divisor.
-/
lemma affineNeighborhood_normalForm_kernel (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens)
    {ω η : Forms k (sectionAlgebra k P.ambient.obj V.1)}
    (h : Forms.map (sectionPullback P.j.hom V.1) ω +
      dlog k (Units.map (sectionRestriction k P.compl.obj
        (P.j.hom.left ⁻¹ᵁ V.1).leTop).toMonoidHom
          (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit)) *
      Forms.map (sectionPullback P.j.hom V.1) η = 0) :
    Forms.map (sectionPullback P.i.hom V.1) η = 0 := by
  exact normalForm_kernel_of_equiv (affineNeighborhoodAlgebraicPair P V)
    (sectionPullback P.j.hom V.1) (sectionPullback P.i.hom V.1) _
    (openSectionAlgebraEquiv P.ambient.obj V.1)
    (openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1))
    (openSectionAlgebraEquiv P.closed.obj (P.i.hom.left ⁻¹ᵁ V.1))
    (openSectionAlgebraEquiv_comp P.j.hom V.1)
    (openSectionAlgebraEquiv_comp P.i.hom V.1)
    (affineNeighborhood_eqnUnit P V) h

/-- Pullback on an individual open, with its target expressed as sections on the actual inverse
image.
-/
def formsSheafPullbackAt {X Y : Over (Spec (CommRingCat.of k))}
    (g : X ⟶ Y) (U : Y.left.Opens) (n : ℕ) :
    (formsSheaf k Y n).obj.obj (op U) →ₗ[k]
      (formsSheaf k X n).obj.obj (op (g.left ⁻¹ᵁ U)) :=
  ((formsSheafPullback g n).hom.app (op U)).hom

/-- Left exterior multiplication by the logarithmic form of a unit, in a fixed degree. -/
def leftDlogPower {A : Type u} [CommRing A] [Algebra k A] (v : Aˣ) (n : ℕ)
    (a : ⋀[A]^n Ω[A⁄k]) : ⋀[A]^(n + 1) Ω[A⁄k] :=
  ⟨dlog k v * a.val, by simpa only [Nat.add_comm 1 n] using
    SetLike.mul_mem_graded (dlog_mem_exteriorPower_one k _) a.property⟩

/-- Affine-open evaluation commutes with pullback whenever the inverse-image open is affine. -/
lemma affineOpenFormsComparison_pull {X Y : Over (Spec (CommRingCat.of k))}
    (g : X ⟶ Y) (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (g.left ⁻¹ᵁ U)) (n : ℕ)
    (a : ⋀[sectionAlgebra k Y U]^n Ω[sectionAlgebra k Y U⁄k]) :
    formsSheafPullbackAt g U n (affineOpenFormsComparison Y U hU n a) =
      affineOpenFormsComparison X _ hV n (Forms.mapPower (sectionPullback g U) n a) :=
  formsSheafPullback_unit_apply g n (op U) a

/-- Affine-open evaluation identifies logarithmic multiplication with left multiplication by the
restricted unit.
-/
lemma thetaWedgeSheaf_affineOpenFormsComparison
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) (hU : IsAffineOpen U)
    (v : (sectionAlgebra k X ⊤)ˣ) (n : ℕ)
    (a : ⋀[sectionAlgebra k X U]^n Ω[sectionAlgebra k X U⁄k]) :
    (thetaWedgeSheaf X v n).hom.app (op U) (affineOpenFormsComparison X U hU n a) =
      affineOpenFormsComparison X U hU (n + 1)
        (leftDlogPower (Units.map (sectionRestriction k X U.leTop).toMonoidHom v) n a) :=
  thetaWedgeSheaf_unit X v n (op U) a

/-- A sheaf normal-form relation on an affine open forces its logarithmic coefficient to vanish
on the divisor.
-/
lemma affineOpen_normalForm_kernel (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ)
    (ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1))
    (η : (formsSheaf k P.ambient.obj n).obj.obj (op V.1))
    (h : formsSheafPullbackAt P.j.hom V.1 (n + 1) ω +
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
        (formsSheafPullbackAt P.j.hom V.1 n η) = 0) :
    formsSheafPullbackAt P.i.hom V.1 n η = 0 := by
  have hJ : IsAffineOpen (P.j.hom.left ⁻¹ᵁ V.1) :=
    inferInstanceAs (IsAffine (affineNeighborhoodPair P V).compl.obj.left)
  have hI : IsAffineOpen (P.i.hom.left ⁻¹ᵁ V.1) :=
    inferInstanceAs (IsAffine (affineNeighborhoodPair P V).closed.obj.left)
  obtain ⟨a, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 (n + 1)).surjective ω
  obtain ⟨b, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective η
  let c := leftDlogPower (Units.map (sectionRestriction k P.compl.obj
    (P.j.hom.left ⁻¹ᵁ V.1).leTop).toMonoidHom
    (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit)) n
    (Forms.mapPower (sectionPullback P.j.hom V.1) n b)
  have h₁ := affineOpenFormsComparison_pull P.j.hom V.1 V.2 hJ (n + 1) a
  have h₂ := affineOpenFormsComparison_pull P.j.hom V.1 V.2 hJ n b
  have ht := thetaWedgeSheaf_affineOpenFormsComparison P.compl.obj
    (P.j.hom.left ⁻¹ᵁ V.1) hJ P.eqnUnit n
    (Forms.mapPower (sectionPullback P.j.hom V.1) n b)
  change (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
    (affineOpenFormsComparison P.compl.obj _ hJ n
      (Forms.mapPower (sectionPullback P.j.hom V.1) n b)) =
        affineOpenFormsComparison P.compl.obj _ hJ (n + 1) c at ht
  have hθ := (congrArg
    ((thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))) h₂).trans ht
  have hzsheaf := (congrArg₂ (· + ·) h₁ hθ).symm.trans h
  have hz : Forms.mapPower (sectionPullback P.j.hom V.1) (n + 1) a + c = 0 :=
    (affineOpenFormsComparison P.compl.obj _ hJ (n + 1)).injective
      (((affineOpenFormsComparison P.compl.obj _ hJ (n + 1)).map_add _ _).trans
        (hzsheaf.trans (affineOpenFormsComparison P.compl.obj _ hJ (n + 1)).map_zero.symm))
  have hb : Forms.mapPower (sectionPullback P.i.hom V.1) n b = 0 :=
    Subtype.ext (affineNeighborhood_normalForm_kernel P V (congrArg Subtype.val hz))
  exact (affineOpenFormsComparison_pull P.i.hom V.1 V.2 hI n b).trans
    ((congrArg (affineOpenFormsComparison P.closed.obj _ hI n) hb).trans
      (affineOpenFormsComparison P.closed.obj _ hI n).map_zero)


/-- The divisor restriction of the logarithmic coefficient annihilates the kernel of the normal-
form epimorphism.
-/
lemma logMkSheaf_kernel_snd_pull (P : DivisorPair D) (n : ℕ) :
    kernel.ι (logMkSheaf P n) ≫ biprod.snd ≫ formsSheafPullback P.i.hom n = 0 := by
  have hzero : kernel.ι (logMkSheaf P n) ≫ logNormalFormSheaf P n = 0 := by
    rw [← logMkSheaf_comp_logToOpenSheaf, ← Category.assoc, kernel.condition, zero_comp]
  have hnormal :
      (kernel.ι (logMkSheaf P n) ≫ biprod.fst) ≫ formsSheafPullback P.j.hom (n + 1) +
        (kernel.ι (logMkSheaf P n) ≫ biprod.snd) ≫ formsSheafPullback P.j.hom n ≫
          (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
            (thetaWedgeSheaf P.compl.obj P.eqnUnit n) = 0 := by
    simpa only [logNormalFormSheaf, biprod.desc_eq, Preadditive.comp_add, Category.assoc]
      using hzero
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (B := fun V : P.ambient.obj.left.affineOpens => V.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      P.ambient.obj.left.isBasis_affineOpens)
  intro V
  ext x
  let ω := ((kernel.ι (logMkSheaf P n) ≫ biprod.fst).hom.app (op V.1)) x
  let η := ((kernel.ι (logMkSheaf P n) ≫ biprod.snd).hom.app (op V.1)) x
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) hnormal) (op V.1)) x
  change formsSheafPullbackAt P.j.hom V.1 (n + 1) ω +
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
      (formsSheafPullbackAt P.j.hom V.1 n η) = 0 at hh
  exact affineOpen_normalForm_kernel P V n ω η hh

section ResidueMap

variable (P : DivisorPair D)

/-- Differentiating a regular-plus-left-theta normal form negates the differential of its
logarithmic coefficient. -/
@[reassoc] theorem logNormalFormSheaf_d (n : ℕ) :
    logNormalFormSheaf P n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
          (formsSheafD k P.compl.obj (n + 1)) =
      biprod.map (formsSheafD k P.ambient.obj (n + 1)) (-(formsSheafD k P.ambient.obj n)) ≫
        logNormalFormSheaf P (n + 1) := by
  apply biprod.hom_ext'
  · simpa only [Category.assoc, inl_logNormalFormSheaf_assoc, biprod.inl_map_assoc,
      inl_logNormalFormSheaf] using formsSheafPullback_d P.j.hom (n + 1)
  · simp only [inr_logNormalFormSheaf_assoc, biprod.inr_map_assoc,
      inr_logNormalFormSheaf, neg_comp]
    rw [← Functor.map_comp, thetaWedgeSheaf_d, Functor.map_neg, Functor.map_comp, comp_neg]
    rw [← Category.assoc, formsSheafPullback_d]
    simp only [Category.assoc]

/-- The local normal-form epimorphism commutes with the signed differential. -/
@[reassoc] theorem logMkSheaf_d (n : ℕ) :
    logMkSheaf P n ≫ logSheafD P (n + 1) =
      biprod.map (formsSheafD k P.ambient.obj (n + 1)) (-(formsSheafD k P.ambient.obj n)) ≫
        logMkSheaf P (n + 1) := by
  apply (cancel_mono (logToOpenSheaf P (n + 1 + 1))).1
  rw [Category.assoc, logSheafD_comp_logToOpenSheaf,
    ← Category.assoc, logMkSheaf_comp_logToOpenSheaf, Category.assoc,
    logMkSheaf_comp_logToOpenSheaf]
  exact logNormalFormSheaf_d P n

/-- Residue of logarithmic sheaf forms in degree `n + 1`: a local normal form
`ω + θ ∧ η` maps to the restriction of `η` to the divisor. The proven kernel criterion makes
this independent of the normal form, and descent along the sheaf epimorphism glues the result.

Blueprint: `thm:geo-log-sheaves`. -/
def logResidueSheaf (n : ℕ) :
    logSheaf P (n + 1) ⟶ closedFormsSheaf P n :=
  Abelian.epiDesc (logMkSheaf P n) (biprod.snd ≫ formsSheafPullback P.i.hom n)
    (logMkSheaf_kernel_snd_pull P n)

/-- The residue on a local normal form is its logarithmic coefficient restricted to the divisor. -/
@[reassoc (attr := simp)] theorem logMkSheaf_residue (n : ℕ) :
    logMkSheaf P n ≫ logResidueSheaf P n = biprod.snd ≫ formsSheafPullback P.i.hom n :=
  Abelian.comp_epiDesc _ _ _

/-- A regular sheaf form has zero residue. -/
@[reassoc (attr := simp)] theorem regularToLogSheaf_residue (n : ℕ) :
    regularToLogSheaf P (n + 1) ≫ logResidueSheaf P n = 0 := by
  rw [← inl_logMkSheaf, Category.assoc, logMkSheaf_residue,
    biprod.inl_snd_assoc, zero_comp]

/-- The sheaf residue map is an epimorphism. This does not assert surjectivity on arbitrary
global sections. -/
instance logResidueSheaf_epi (n : ℕ) :
    Epi (logResidueSheaf P n) := by
  have := formsSheafPullback_epi P n
  have : Epi (logMkSheaf P n ≫ logResidueSheaf P n) := by
    rw [logMkSheaf_residue]
    infer_instance
  exact epi_of_epi (logMkSheaf P n) _

/-- Residue anticommutes with the de Rham differential. This is the chain-map convention
for the divisor shift with differential `-d`.

Blueprint: `thm:geo-log-sheaves`. -/
@[reassoc] theorem logResidueSheaf_d (n : ℕ) :
    logSheafD P (n + 1) ≫ logResidueSheaf P (n + 1) =
      -(logResidueSheaf P n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
          (formsSheafD k P.closed.obj n)) := by
  apply (cancel_epi (logMkSheaf P n)).1
  calc
    _ = biprod.map (formsSheafD k P.ambient.obj (n + 1)) (-(formsSheafD k P.ambient.obj n)) ≫
        biprod.snd ≫ formsSheafPullback P.i.hom (n + 1) := by
      rw [← Category.assoc, logMkSheaf_d, Category.assoc, logMkSheaf_residue]
    _ = -(biprod.snd ≫ formsSheafD k P.ambient.obj n ≫
        formsSheafPullback P.i.hom (n + 1)) := by
      simp only [biprod.map_snd_assoc, comp_neg, neg_comp]
    _ = -(biprod.snd ≫ formsSheafPullback P.i.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
          (formsSheafD k P.closed.obj n)) := by
      rw [formsSheafPullback_d]
    _ = _ := by
      simpa only [comp_neg, Category.assoc] using
        (congrArg (fun f ↦ -(f ≫
          (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
            (formsSheafD k P.closed.obj n))) (logMkSheaf_residue P n)).symm


end ResidueMap

end OrlikSolomon.Geometric.DeRham
