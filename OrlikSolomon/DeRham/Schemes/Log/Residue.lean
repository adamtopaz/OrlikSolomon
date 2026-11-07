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
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Residue and exactness of logarithmic forms on schemes

The local formula `ρ(ω + θ ∧ η) = η|D` descends to the logarithmic image sheaf. It gives a
degreewise short exact sequence of sheaf complexes from regular forms to logarithmic forms
to divisor forms shifted with differential `-d`. All arguments work over every commutative
base ring, without characteristic, nontriviality, points or ambient affineness hypotheses.

## Main results

* `formsSheafPullback_injective_affineOpen`: injectivity on each affine neighborhood.
* `formsSheafPullback_mono`: the regular-form map to the complement is a monomorphism.
* `regularToLogSheaf_mono`: the left inclusion into logarithmic forms is a monomorphism.
* `logResidueSheaf`, `logMkSheaf_residue`: residue and its local normal-form formula.
* `logResidueSheaf_d`: residue anticommutes with the differential.
* `logResidueComplexNat`: the residue map of sheaf complexes to the signed shift.
* `logResidueShortComplexNat_shortExact`: the sheaf residue sequence is short exact.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite AlgebraicGeometry
open scoped ZeroObject
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

/-- Degreewise regularity of a logarithmic term transports through compatible algebra
equivalences.
-/
lemma theta_regular_of_equiv (Q : OrlikSolomon.DivisorPair k)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (j : A →ₐ[k] B) (i : A →ₐ[k] C) (v : Bˣ)
    (eA : A ≃ₐ[k] Q.ambient) (eB : B ≃ₐ[k] Q.compl) (eC : C ≃ₐ[k] Q.closed)
    (hj : eB.toAlgHom.comp j = (SmoothAlg.algHom Q.j).comp eA.toAlgHom)
    (hi : eC.toAlgHom.comp i = (SmoothAlg.algHom Q.i).comp eA.toAlgHom)
    (hu : Units.map eB.toAlgHom.toMonoidHom v = Q.eqnUnit)
    (n : ℕ) (η : ⋀[A]^n Ω[A⁄k]) (h : Forms.map i η.val = 0) :
    ∃ ω : ⋀[A]^(n + 1) Ω[A⁄k], Forms.map j ω.val = dlog k v * Forms.map j η.val := by
  have hQ : Forms.map (SmoothAlg.algHom Q.i) (Forms.map eA.toAlgHom η.val) = 0 := by
    rw [Forms.map_map, ← hi, ← Forms.map_map, h, map_zero]
  have hdeg := (Forms.mapPower eA.toAlgHom n η).property
  obtain ⟨ω, hω, hωeq⟩ := mem_regularPower.1
    ((Q.isSmoothPrincipalPair.theta_mul_map_mem_regularPower_iff Q.compl hdeg).2 hQ)
  let ωA := Forms.mapPower eA.symm.toAlgHom (n + 1) ⟨ω, hω⟩
  refine ⟨ωA, ?_⟩
  apply (Forms.mapEquiv eB).injective
  change Forms.map eB.toAlgHom (Forms.map j ωA.val) =
    Forms.map eB.toAlgHom (dlog k v * Forms.map j η.val)
  rw [Forms.map_map eB.toAlgHom j ωA.val, hj, map_mul, Forms.map_dlog,
    Forms.map_map eB.toAlgHom j η.val, hj,
    ← Forms.map_map (SmoothAlg.algHom Q.j) eA.toAlgHom ωA.val,
    ← Forms.map_map (SmoothAlg.algHom Q.j) eA.toAlgHom η.val]
  have hleft : Forms.map eA.toAlgHom ωA.val = ω :=
    (Forms.mapEquiv eA).apply_symm_apply ω
  change Units.map (eB.toAlgHom : B →* Q.compl) v = Q.eqnUnit at hu
  rw [hleft, hu, ← Q.theta_eq_dlog_eqnUnit]
  exact hωeq

/-- A coefficient vanishing on the divisor has a logarithmic term with an ambient primitive of the
correct degree. -/
lemma affineNeighborhood_theta_regular (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ)
    (η : ⋀[sectionAlgebra k P.ambient.obj V.1]^n Ω[sectionAlgebra k P.ambient.obj V.1⁄k])
    (h : Forms.map (sectionPullback P.i.hom V.1) η.val = 0) :
    ∃ ω : ⋀[sectionAlgebra k P.ambient.obj V.1]^(n + 1)
        Ω[sectionAlgebra k P.ambient.obj V.1⁄k],
      Forms.map (sectionPullback P.j.hom V.1) ω.val =
        dlog k (Units.map (sectionRestriction k P.compl.obj
          (P.j.hom.left ⁻¹ᵁ V.1).leTop).toMonoidHom
            (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit)) *
          Forms.map (sectionPullback P.j.hom V.1) η.val :=
  theta_regular_of_equiv (affineNeighborhoodAlgebraicPair P V)
    (sectionPullback P.j.hom V.1) (sectionPullback P.i.hom V.1) _
    (openSectionAlgebraEquiv P.ambient.obj V.1)
    (openSectionAlgebraEquiv P.compl.obj (P.j.hom.left ⁻¹ᵁ V.1))
    (openSectionAlgebraEquiv P.closed.obj (P.i.hom.left ⁻¹ᵁ V.1))
    (openSectionAlgebraEquiv_comp P.j.hom V.1)
    (openSectionAlgebraEquiv_comp P.i.hom V.1)
    (affineNeighborhood_eqnUnit P V) n η h

/-- On an affine neighborhood, a coefficient restricting to zero on the divisor gives a regular
logarithmic term. -/
lemma affineOpen_theta_regular (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ)
    (η : (formsSheaf k P.ambient.obj n).obj.obj (op V.1))
    (h : formsSheafPullbackAt P.i.hom V.1 n η = 0) :
    ∃ ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1),
      formsSheafPullbackAt P.j.hom V.1 (n + 1) ω =
        (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
          (formsSheafPullbackAt P.j.hom V.1 n η) := by
  have hJ : IsAffineOpen (P.j.hom.left ⁻¹ᵁ V.1) :=
    inferInstanceAs (IsAffine (affineNeighborhoodPair P V).compl.obj.left)
  have hI : IsAffineOpen (P.i.hom.left ⁻¹ᵁ V.1) :=
    inferInstanceAs (IsAffine (affineNeighborhoodPair P V).closed.obj.left)
  obtain ⟨b, rfl⟩ := (affineOpenFormsComparison P.ambient.obj V.1 V.2 n).surjective η
  have hB : Forms.mapPower (sectionPullback P.i.hom V.1) n b = 0 :=
    (affineOpenFormsComparison P.closed.obj _ hI n).injective
      ((affineOpenFormsComparison_pull P.i.hom V.1 V.2 hI n b).symm.trans
        (h.trans (affineOpenFormsComparison P.closed.obj _ hI n).map_zero.symm))
  obtain ⟨a, ha⟩ := affineNeighborhood_theta_regular P V n b (congrArg Subtype.val hB)
  have ha' : Forms.mapPower (sectionPullback P.j.hom V.1) (n + 1) a =
      leftDlogPower (Units.map (sectionRestriction k P.compl.obj
        (P.j.hom.left ⁻¹ᵁ V.1).leTop).toMonoidHom
        (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit)) n
        (Forms.mapPower (sectionPullback P.j.hom V.1) n b) := Subtype.ext ha
  refine ⟨affineOpenFormsComparison P.ambient.obj V.1 V.2 (n + 1) a, ?_⟩
  have hθ := (congrArg
    ((thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1)))
      (affineOpenFormsComparison_pull P.j.hom V.1 V.2 hJ n b)).trans
        (thetaWedgeSheaf_affineOpenFormsComparison P.compl.obj _ hJ P.eqnUnit n
          (Forms.mapPower (sectionPullback P.j.hom V.1) n b))
  exact (affineOpenFormsComparison_pull P.j.hom V.1 V.2 hJ (n + 1) a).trans
    ((congrArg (affineOpenFormsComparison P.compl.obj _ hJ (n + 1)) ha').trans hθ.symm)

/-- A normal form with vanishing divisor coefficient is the pullback of an ambient form of the same
degree. -/
lemma affineOpen_normalForm_regular (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ)
    (ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1))
    (η : (formsSheaf k P.ambient.obj n).obj.obj (op V.1))
    (h : formsSheafPullbackAt P.i.hom V.1 n η = 0) :
    ∃ α : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1),
      formsSheafPullbackAt P.j.hom V.1 (n + 1) α =
        formsSheafPullbackAt P.j.hom V.1 (n + 1) ω +
          (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
            (formsSheafPullbackAt P.j.hom V.1 n η) := by
  obtain ⟨δ, hδ⟩ := affineOpen_theta_regular P V n η h
  exact ⟨ω + δ, ((formsSheafPullbackAt P.j.hom V.1 (n + 1)).map_add ω δ).trans
    (congrArg (formsSheafPullbackAt P.j.hom V.1 (n + 1) ω + ·) hδ)⟩


/-- Every represented logarithmic section with zero residue on an affine neighborhood has a regular
preimage. -/
lemma affineOpen_logMkSheaf_regular (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (n : ℕ)
    (ρ : logSheaf P (n + 1) ⟶ closedFormsSheaf P n)
    (hρ : logMkSheaf P n ≫ ρ = biprod.snd ≫ formsSheafPullback P.i.hom n)
    (t : ((formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n).obj.obj (op V.1)))
    (h : ρ.hom.app (op V.1) ((logMkSheaf P n).hom.app (op V.1) t) = 0) :
    ∃ α : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1),
      (regularToLogSheaf P (n + 1)).hom.app (op V.1) α =
        (logMkSheaf P n).hom.app (op V.1) t := by
  let ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op V.1) :=
    ((biprod.fst : formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n ⟶ _).hom.app
      (op V.1)) t
  let η : (formsSheaf k P.ambient.obj n).obj.obj (op V.1) :=
    ((biprod.snd : formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n ⟶ _).hom.app
      (op V.1)) t
  have hη := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) hρ) (op V.1)) t
  change ρ.hom.app (op V.1) ((logMkSheaf P n).hom.app (op V.1) t) =
    formsSheafPullbackAt P.i.hom V.1 n η at hη
  obtain ⟨α, hα⟩ := affineOpen_normalForm_regular P V n ω η (hη.symm.trans h)
  refine ⟨α, ?_⟩
  have hinj : Function.Injective ((logToOpenSheaf P (n + 1)).hom.app (op V.1)) := by
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    exact (NatTrans.mono_iff_mono_app _).1 inferInstance (op V.1)
  apply hinj
  have hreg := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (regularToLogSheaf_comp_logToOpenSheaf P (n + 1))) (op V.1)) α
  have hnf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (logMkSheaf_comp_logToOpenSheaf P n)) (op V.1)) t
  have hm : logNormalFormSheaf P n =
      biprod.fst ≫ formsSheafPullback P.j.hom (n + 1) +
        biprod.snd ≫ formsSheafPullback P.j.hom n ≫
          (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
            (thetaWedgeSheaf P.compl.obj P.eqnUnit n) :=
    biprod.desc_eq
  have hnormal := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) hm) (op V.1)) t
  change (logNormalFormSheaf P n).hom.app (op V.1) t =
    formsSheafPullbackAt P.j.hom V.1 (n + 1) ω +
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ V.1))
        (formsSheafPullbackAt P.j.hom V.1 n η) at hnormal
  exact hreg.trans (hα.trans (hnormal.symm.trans hnf.symm))


/-- The kernel of residue vanishes in the cokernel of the regular-form inclusion, checked by local
normal forms. -/
lemma kernel_logResidueSheaf_cokernel_regular (P : DivisorPair D) (n : ℕ) :
    kernel.ι (logResidueSheaf P n) ≫ cokernel.π (regularToLogSheaf P (n + 1)) = 0 := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (logMkSheaf P n).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).2 inferInstance
  let N := formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n
  let L := logSheaf P (n + 1)
  let C := closedFormsSheaf P n
  let T := cokernel (regularToLogSheaf P (n + 1))
  let π := cokernel.π (regularToLogSheaf P (n + 1))
  apply ObjectProperty.hom_ext
  ext U s
  let y := (kernel.ι (logResidueSheaf P n)).hom.app U s
  change π.hom.app U y = 0
  apply TopCat.Presheaf.section_ext T U.unop
  intro p hp
  obtain ⟨W, iWU, ⟨t, ht⟩, hpW⟩ := hloc.imageSieve_mem y p hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVW⟩ :=
    P.ambient.obj.left.isBasis_affineOpens.exists_subset_of_mem_open hpW W.2
  let iVW : V ⟶ W := homOfLE hVW
  let iVU : V ⟶ U.unop := iVW ≫ iWU
  let tV := N.obj.map iVW.op t
  have htV : (logMkSheaf P n).hom.app (op V) tV = L.obj.map iVU.op y := by
    calc
      _ = L.obj.map iVW.op ((logMkSheaf P n).hom.app (op W) t) :=
        ConcreteCategory.congr_hom ((logMkSheaf P n).hom.naturality iVW.op) t
      _ = L.obj.map iVW.op (L.obj.map iWU.op y) := congrArg (L.obj.map iVW.op) ht
      _ = _ := by
        rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
        rfl
  have hker := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (kernel.condition (logResidueSheaf P n))) U) s
  change (logResidueSheaf P n).hom.app U y = 0 at hker
  have hr : (logResidueSheaf P n).hom.app (op V)
      ((logMkSheaf P n).hom.app (op V) tV) = 0 := by
    calc
      _ = (logResidueSheaf P n).hom.app (op V) (L.obj.map iVU.op y) :=
        congrArg ((logResidueSheaf P n).hom.app (op V)) htV
      _ = C.obj.map iVU.op ((logResidueSheaf P n).hom.app U y) :=
        ConcreteCategory.congr_hom ((logResidueSheaf P n).hom.naturality iVU.op) y
      _ = 0 := (congrArg (C.obj.map iVU.op) hker).trans (C.obj.map iVU.op).hom.map_zero
  obtain ⟨α, hα⟩ := affineOpen_logMkSheaf_regular P ⟨V, hV⟩ n
    (logResidueSheaf P n) (logMkSheaf_residue P n) tV hr
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (cokernel.condition (regularToLogSheaf P (n + 1)))) (op V)) α
  change π.hom.app (op V) ((regularToLogSheaf P (n + 1)).hom.app (op V) α) = 0 at hf
  have hz : π.hom.app (op V) ((logMkSheaf P n).hom.app (op V) tV) = 0 :=
    (congrArg (π.hom.app (op V)) hα.symm).trans hf
  have hres : T.obj.map iVU.op (π.hom.app U y) = 0 := by
    calc
      _ = π.hom.app (op V) (L.obj.map iVU.op y) :=
        (ConcreteCategory.congr_hom (π.hom.naturality iVU.op) y).symm
      _ = π.hom.app (op V) ((logMkSheaf P n).hom.app (op V) tV) :=
        congrArg (π.hom.app (op V)) htV.symm
      _ = 0 := hz
  exact (TopCat.Presheaf.germ_res_apply T.obj iVU p hpV (π.hom.app U y)).symm.trans
    ((congrArg (TopCat.Presheaf.germ T.obj V p hpV) hres).trans
      ((TopCat.Presheaf.germ T.obj V p hpV).hom.map_zero.trans
        (TopCat.Presheaf.germ T.obj U.unop p hp).hom.map_zero.symm))

/-- The regular inclusion and residue form an exact sequence of sheaves in every positive
logarithmic degree.
Blueprint: `thm:geo-log-sheaves`. -/
lemma logResidueSheaf_exact (P : DivisorPair D) (n : ℕ) :
    (ShortComplex.mk (regularToLogSheaf P (n + 1)) (logResidueSheaf P n)
      (regularToLogSheaf_residue P n)).Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  exact kernel_logResidueSheaf_cokernel_regular P n


section ResidueComplex

variable (P : DivisorPair D)

/-- The differential of a degree-zero logarithmic form has zero residue. -/
@[reassoc (attr := simp)] theorem logSheafD_zero_residue :
    logSheafD P 0 ≫ logResidueSheaf P 0 = 0 := by
  apply (cancel_epi (regularToLogSheaf P 0)).1
  rw [← Category.assoc, regularToLogSheaf_d, Category.assoc,
    regularToLogSheaf_residue, comp_zero, comp_zero]

/-- Residue as a map of sheaf complexes to the divisor complex shifted with differential `-d`.
It is zero in degree zero, and the usual residue in each positive degree.

Blueprint: `thm:geo-log-sheaves`. -/
def logResidueComplexNat : logComplexNat P ⟶ shiftedClosedComplexNat P := by
  refine CochainComplex.ofHom (fun | 0 => 0 | n + 1 => logResidueSheaf P n) ?_
  rintro (_ | n)
  · simp only [zero_comp]
    exact (logSheafD_zero_residue P).symm
  · change logResidueSheaf P n ≫ (shiftedClosedComplexNat P).d (n + 1) (n + 1 + 1) =
      logSheafD P (n + 1) ≫ logResidueSheaf P (n + 1)
    exact (congrArg (fun δ : closedFormsSheaf P n ⟶ closedFormsSheaf P (n + 1) =>
      logResidueSheaf P n ≫ δ) (shiftedClosedComplexNat_d P n)).trans
        ((comp_neg _ _).trans (logResidueSheaf_d P n).symm)

/-- Residue has zero component in degree zero. -/
@[simp] theorem logResidueComplexNat_f_zero : (logResidueComplexNat P).f 0 = 0 := rfl
/-- In positive degrees, complex residue is the sheaf residue. -/
theorem logResidueComplexNat_f_succ (n : ℕ) :
    (logResidueComplexNat P).f (n + 1) = logResidueSheaf P n := rfl

/-- The positive component of complex residue, transported to the named divisor-form target. -/
@[simp] theorem logResidueComplexNat_component_succ (n : ℕ) :
    (logResidueComplexNat P).f (n + 1) ≫
        eqToHom (shiftedClosedComplexNat_X_succ P n) = logResidueSheaf P n := by
  change logResidueSheaf P n ≫ 𝟙 _ = logResidueSheaf P n
  exact Category.comp_id _

/-- Regular forms have zero residue as a map of complexes. -/
@[reassoc (attr := simp)] theorem regularToLogComplexNat_residue :
    regularToLogComplexNat P ≫ logResidueComplexNat P = 0 := by
  apply HomologicalComplex.hom_ext
  rintro (_ | n)
  · change regularToLogSheaf P 0 ≫ 0 = 0
    exact comp_zero
  · exact regularToLogSheaf_residue P n


/-- The logarithmic residue sequence as a short complex of sheaf complexes. The final complex
is the divisor direct image shifted up one degree, with differential `-d`.

Blueprint: `thm:geo-log-sheaves`. -/
def logResidueShortComplexNat :
    ShortComplex (CochainComplex (TopCat.Sheaf (ModuleCat k) P.ambient.obj.left) ℕ) :=
  ShortComplex.mk (regularToLogComplexNat P) (logResidueComplexNat P)
    (regularToLogComplexNat_residue P)

/-- The logarithmic residue sequence is degreewise short exact on every admissible domain.
This is sheaf exactness; it does not pass underived global sections through a short exact sequence
on an arbitrary non-affine scheme.

Blueprint: `thm:geo-log-sheaves`. -/
theorem logResidueShortComplexNat_shortExact : (logResidueShortComplexNat P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  rintro (_ | n)
  · change (ShortComplex.mk (regularToLogSheaf P 0) (0 : logSheaf P 0 ⟶ 0)
      (by simp)).ShortExact
    exact { exact := (ShortComplex.exact_iff_epi _ rfl).2 inferInstance }
  · change (ShortComplex.mk (regularToLogSheaf P (n + 1)) (logResidueSheaf P n)
      (regularToLogSheaf_residue P n)).ShortExact
    exact { exact := logResidueSheaf_exact P n }


end ResidueComplex

end OrlikSolomon.Geometric.DeRham
