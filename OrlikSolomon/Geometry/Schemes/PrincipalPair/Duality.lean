/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Standard

/-!
# Duality between geometric and algebraic pairs

This file proves `thm:geo-pair-duality` of the geometric refactor blueprint: geometric pairs with
affine ambient scheme are anti-equivalent to the algebraic pairs `OrlikSolomon.DivisorPair k`, and
the equivalence preserves the immersions, the equation, its unit on the open part, the standard
pairs and changes of equation.

## Main definitions

* `DivisorPair.spec D P`: `Spec` of an algebraic pair `P`, a geometric pair in any domain `D`. Its
  maps are `Spec` of the maps of `P`, and its equation is the function of `P.eqn`.
* `DivisorPair.specMap D F`: `Spec` of an algebraic morphism `F : P ⟶ Q`, a geometric morphism
  `spec D Q ⟶ spec D P` in the opposite direction.
* `DivisorPair.specFunctor D`: these, as a functor
  `OrlikSolomon.DivisorPair k ⥤ (DivisorPair D)ᵒᵖ`.
  It is the functor through which a geometric theory on `D` is evaluated on algebraic pairs.
* `DivisorPair.globalSections P`: the algebraic pair of global sections of a pair `P` of smooth
  affine schemes, with maps `i^*` and `j^*` and equation `P.eqn`.
* `DivisorPair.globalSectionsMap`, `DivisorPair.globalSectionsFunctor k`: global sections of
  morphisms, as a functor `(DivisorPair (aff k))ᵒᵖ ⥤ OrlikSolomon.DivisorPair k`.
* `Geometric.affinePairEquivalence k`: the equivalence `OrlikSolomon.DivisorPair k ≌
  (DivisorPair (aff k))ᵒᵖ`, whose unit and counit are `η` and `ε` of `smoothAffineEquivalence` on
  each of the three objects of a pair.
* `DivisorPair.specStandardPairIso D A`: `Spec` of the algebraic standard pair of `A` is the
  geometric standard pair of `Spec A`.

## Implementation notes

A geometric pair whose ambient scheme is affine has affine divisor and open part
(`isAffine_closed`, `isAffine_compl`), so it is a pair in the domain `aff k` of smooth affine
schemes (`toAff`, `ofLE_toAff`). The anti-equivalence is stated there.

Inside `namespace OrlikSolomon.Geometric.DivisorPair`, the names `spec`, `specMap`, `specFunctor`,
`globalSections`, `globalSectionsMap` and `globalSectionsFunctor` are the pair-level declarations of
this file; write `Geometric.spec` and so on for the object-level ones of `Geometry/Schemes/Basic`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

namespace DivisorPair

/-! ### Affine pairs -/

section Affine

variable {D : SmoothDomain k} (P : DivisorPair D) [IsAffine P.ambient.obj.left]

/-- A pair with affine ambient scheme has affine divisor: a closed immersion is affine. -/
lemma isAffine_closed : IsAffine P.closed.obj.left := isAffine_of_isAffineHom P.i.hom.left

/-- A pair with affine ambient scheme has affine open part: a basic open of an affine scheme is
affine. -/
lemma isAffine_compl : IsAffine P.compl.obj.left := isAffine_of_opensRange_eq P.opensRange_j

/-- A pair with affine ambient scheme in any domain, as a pair in the domain `aff k` of smooth
affine schemes, with the same schemes, maps and equation (`ofLE_toAff`).

Blueprint: `thm:geo-pair-duality`. -/
@[implicit_reducible]
def toAff : DivisorPair (SmoothDomain.aff k) where
  ambient := ⟨P.ambient.obj, inferInstance, inferInstance⟩
  closed := ⟨P.closed.obj, P.isAffine_closed, inferInstance⟩
  compl := ⟨P.compl.obj, P.isAffine_compl, inferInstance⟩
  i := ObjectProperty.homMk P.i.hom
  j := ObjectProperty.homMk P.j.hom
  eqn := P.eqn
  isRegularSection_eqn := P.isRegularSection_eqn
  isClosedImmersion_i := P.isClosedImmersion_i
  ker_i := P.ker_i
  isOpenImmersion_j := P.isOpenImmersion_j
  opensRange_j := P.opensRange_j

@[simp] lemma toAff_eqn : P.toAff.eqn = P.eqn := rfl

/-- Seen in `D` again, `P.toAff` is `P`. -/
lemma ofLE_toAff : ofLE (SmoothDomain.aff_le D) P.toAff = P := rfl

end Affine

/-! ### `Spec` of an algebraic pair -/

section Spec

variable (D : SmoothDomain k)

/-- `Spec` of an algebraic pair `P`, a geometric pair in any domain `D`: the schemes `Spec` of the
three rings of `P`, the maps `Spec P.i` and `Spec P.j`, and the function of `P.eqn` on
`Spec P.ambient`. Surjectivity with kernel `(f)`, localization away from `f` and the
non-zero-divisor condition become the closed, open and regularity certificates.

Blueprint: `thm:geo-pair-duality`. -/
@[implicit_reducible]
def spec (P : OrlikSolomon.DivisorPair k) : DivisorPair D where
  ambient := D.spec P.ambient
  closed := D.spec P.closed
  compl := D.spec P.compl
  i := (D.specFunctor.map P.i).unop
  j := (D.specFunctor.map P.j).unop
  eqn := (Scheme.ΓSpecIso (.of P.ambient)).inv P.eqn
  isRegularSection_eqn := (isRegularSection_ΓSpecIso_inv_iff _).2 P.eqn_mem_nonZeroDivisors
  isClosedImmersion_i := IsClosedImmersion.spec_of_surjective _ P.surjective_i
  ker_i := ker_specMap_of_ker_eq _ P.ker_i
  isOpenImmersion_j := isOpenImmersion_specMap_of_isLocalization
    (CommRingCat.ofHom P.j.hom.hom.toRingHom) P.eqn P.isLocalization_j
  opensRange_j := opensRange_specMap_of_isLocalization
    (CommRingCat.ofHom P.j.hom.hom.toRingHom) P.eqn P.isLocalization_j

variable (P : OrlikSolomon.DivisorPair k)

lemma spec_ambient : (spec D P).ambient = D.spec P.ambient := rfl
lemma spec_closed : (spec D P).closed = D.spec P.closed := rfl
lemma spec_compl : (spec D P).compl = D.spec P.compl := rfl
@[simp] lemma spec_i : (spec D P).i = (D.specFunctor.map P.i).unop := rfl
@[simp] lemma spec_j : (spec D P).j = (D.specFunctor.map P.j).unop := rfl
@[simp] lemma spec_eqn : (spec D P).eqn = (Scheme.ΓSpecIso (.of P.ambient)).inv P.eqn := rfl

/-- The unit of `spec D P` on its open part is the function of the unit of `P`. -/
lemma coe_spec_eqnUnit :
    ((spec D P).eqnUnit : Γ((spec D P).compl.obj.left, ⊤)) =
      (Scheme.ΓSpecIso (.of P.compl)).inv (P.eqnUnit : P.compl) :=
  specMap_left_appTop_ΓSpecIso_inv P.j.hom P.eqn

/-- `Spec` of a pair in a domain `D` is `Spec` of the pair in the smallest domain `aff k`, seen in
`D`. -/
lemma spec_eq_ofLE : spec D P = ofLE (SmoothDomain.aff_le D) (spec (SmoothDomain.aff k) P) := rfl

variable {D} {P} {Q R : OrlikSolomon.DivisorPair k}

variable (D) in
/-- `Spec` of an algebraic morphism `F : P ⟶ Q` is a geometric morphism `spec D Q ⟶ spec D P`:
arrows reverse. The multiplier is the image of the algebraic one.

Blueprint: `thm:geo-pair-duality`. -/
def specMap (F : P ⟶ Q) : spec D Q ⟶ spec D P where
  ambient := (D.specFunctor.map F.ambient).unop
  closed := (D.specFunctor.map F.closed).unop
  compl := (D.specFunctor.map F.compl).unop
  i_comp := by
    rw [spec_i, spec_i, ← unop_comp, ← unop_comp, ← Functor.map_comp, ← Functor.map_comp,
      F.i_comp]
  j_comp := by
    rw [spec_j, spec_j, ← unop_comp, ← unop_comp, ← Functor.map_comp, ← Functor.map_comp,
      F.j_comp]
  associated_eqn := by
    change Associated ((Geometric.specMap F.ambient.hom).left.appTop
      ((Scheme.ΓSpecIso (.of P.ambient)).inv P.eqn)) ((Scheme.ΓSpecIso (.of Q.ambient)).inv Q.eqn)
    rw [specMap_left_appTop_ΓSpecIso_inv]
    exact F.associated_eqn.map (Scheme.ΓSpecIso (.of Q.ambient)).inv.hom

@[simp] lemma specMap_ambient (F : P ⟶ Q) :
    (specMap D F).ambient = (D.specFunctor.map F.ambient).unop := rfl
@[simp] lemma specMap_closed (F : P ⟶ Q) :
    (specMap D F).closed = (D.specFunctor.map F.closed).unop := rfl
@[simp] lemma specMap_compl (F : P ⟶ Q) :
    (specMap D F).compl = (D.specFunctor.map F.compl).unop := rfl

variable (D) in
/-- `Spec`, as a functor from algebraic pairs to the opposite of geometric pairs in `D`. A geometric
theory on `D` is evaluated on algebraic pairs through it.

Blueprint: `thm:geo-pair-duality`, used for `thm:geo-to-algebraic`. -/
@[simps obj, implicit_reducible]
def specFunctor : OrlikSolomon.DivisorPair k ⥤ (DivisorPair D)ᵒᵖ where
  obj P := op (spec D P)
  map F := (specMap D F).op
  map_id P := Quiver.Hom.unop_inj (hom_ext (by
    change (D.specFunctor.map (𝟙 P.ambient)).unop = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl))
  map_comp F G := Quiver.Hom.unop_inj (hom_ext (by
    change (D.specFunctor.map (F.ambient ≫ G.ambient)).unop =
      (D.specFunctor.map G.ambient).unop ≫ (D.specFunctor.map F.ambient).unop
    rw [CategoryTheory.Functor.map_comp, unop_comp]))

@[simp] lemma specFunctor_map_unop_ambient (F : P ⟶ Q) :
    ((specFunctor D).map F).unop.ambient = (D.specFunctor.map F.ambient).unop := rfl
@[simp] lemma specFunctor_map_unop_closed (F : P ⟶ Q) :
    ((specFunctor D).map F).unop.closed = (D.specFunctor.map F.closed).unop := rfl
@[simp] lemma specFunctor_map_unop_compl (F : P ⟶ Q) :
    ((specFunctor D).map F).unop.compl = (D.specFunctor.map F.compl).unop := rfl

end Spec

/-! ### Global sections of an affine pair -/

section GlobalSections

/-- The algebraic pair of global sections of a pair of smooth affine schemes: the rings
`Γ(X, 𝒪)`, `Γ(D, 𝒪)` and `Γ(U, 𝒪)`, the maps `i^*` and `j^*`, and the equation `P.eqn`. The closed,
open and regularity certificates become surjectivity with kernel `(f)`, localization away from `f`
and the non-zero-divisor condition.

Blueprint: `thm:geo-pair-duality`, used for `thm:geo-from-algebraic`. -/
@[implicit_reducible]
def globalSections (P : DivisorPair (SmoothDomain.aff k)) : OrlikSolomon.DivisorPair k where
  ambient := (affineGlobalSectionsFunctor k).obj (op P.ambient)
  closed := (affineGlobalSectionsFunctor k).obj (op P.closed)
  compl := (affineGlobalSectionsFunctor k).obj (op P.compl)
  i := (affineGlobalSectionsFunctor k).map P.i.op
  j := (affineGlobalSectionsFunctor k).map P.j.op
  eqn := P.eqn
  surjective_i := P.i.hom.left.app_surjective ⊤ (isAffineOpen_top _)
  ker_i := (ker_eq_principalIdealSheaf_iff P.i.hom.left).1 P.ker_i
  isLocalization_j := isLocalization_appTop_of_opensRange_eq (j := P.j.hom.left) P.opensRange_j
  eqn_mem_nonZeroDivisors := (isRegularSection_iff P.eqn).1 P.isRegularSection_eqn

variable (P : DivisorPair (SmoothDomain.aff k))

lemma globalSections_ambient :
    (globalSections P).ambient = (affineGlobalSectionsFunctor k).obj (op P.ambient) := rfl
lemma globalSections_closed :
    (globalSections P).closed = (affineGlobalSectionsFunctor k).obj (op P.closed) := rfl
lemma globalSections_compl :
    (globalSections P).compl = (affineGlobalSectionsFunctor k).obj (op P.compl) := rfl
@[simp] lemma globalSections_i :
    (globalSections P).i = (affineGlobalSectionsFunctor k).map P.i.op := rfl
@[simp] lemma globalSections_j :
    (globalSections P).j = (affineGlobalSectionsFunctor k).map P.j.op := rfl
@[simp] lemma globalSections_eqn : (globalSections P).eqn = P.eqn := rfl

/-- The unit of `globalSections P` on its open part is the unit of `P`. -/
lemma coe_globalSections_eqnUnit :
    ((globalSections P).eqnUnit : (globalSections P).compl) =
      (P.eqnUnit : Γ(P.compl.obj.left, ⊤)) :=
  rfl

/-- Changing the equation of `P` changes the equation of its global sections in the same way. -/
@[simp] lemma globalSections_withEqn_eqn (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) :
    (globalSections (P.withEqn f hf)).eqn = f := rfl

variable {P} {Q R : DivisorPair (SmoothDomain.aff k)}

/-- Global sections of a geometric morphism `g : P ⟶ Q` are an algebraic morphism
`globalSections Q ⟶ globalSections P`: arrows reverse, and the multiplier is the same unit.

Blueprint: `thm:geo-pair-duality`. -/
def globalSectionsMap (g : P ⟶ Q) : globalSections Q ⟶ globalSections P where
  ambient := (affineGlobalSectionsFunctor k).map g.ambient.op
  closed := (affineGlobalSectionsFunctor k).map g.closed.op
  compl := (affineGlobalSectionsFunctor k).map g.compl.op
  i_comp := by
    rw [globalSections_i, globalSections_i, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp, g.i_comp]
  j_comp := by
    rw [globalSections_j, globalSections_j, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp, g.j_comp]
  associated_eqn := g.associated_eqn

@[simp] lemma globalSectionsMap_ambient (g : P ⟶ Q) :
    (globalSectionsMap g).ambient = (affineGlobalSectionsFunctor k).map g.ambient.op := rfl
@[simp] lemma globalSectionsMap_closed (g : P ⟶ Q) :
    (globalSectionsMap g).closed = (affineGlobalSectionsFunctor k).map g.closed.op := rfl
@[simp] lemma globalSectionsMap_compl (g : P ⟶ Q) :
    (globalSectionsMap g).compl = (affineGlobalSectionsFunctor k).map g.compl.op := rfl

variable (k) in
/-- Global sections, as a functor from the opposite of pairs of smooth affine schemes to algebraic
pairs. An algebraic theory is evaluated on geometric affine pairs through it.

Blueprint: `thm:geo-pair-duality`, used for `thm:geo-from-algebraic`. -/
@[simps obj, implicit_reducible]
def globalSectionsFunctor : (DivisorPair (SmoothDomain.aff k))ᵒᵖ ⥤ OrlikSolomon.DivisorPair k where
  obj P := globalSections P.unop
  map g := globalSectionsMap g.unop
  map_id P := OrlikSolomon.DivisorPair.hom_ext (by
    change (affineGlobalSectionsFunctor k).map (𝟙 (op P.unop.ambient)) = 𝟙 _
    exact (affineGlobalSectionsFunctor k).map_id _)
  map_comp f g := OrlikSolomon.DivisorPair.hom_ext (by
    change (affineGlobalSectionsFunctor k).map (f.unop.ambient.op ≫ g.unop.ambient.op) =
      (affineGlobalSectionsFunctor k).map f.unop.ambient.op ≫
        (affineGlobalSectionsFunctor k).map g.unop.ambient.op
    exact (affineGlobalSectionsFunctor k).map_comp _ _)

@[simp] lemma globalSectionsFunctor_map_ambient {P Q : (DivisorPair (SmoothDomain.aff k))ᵒᵖ}
    (g : P ⟶ Q) :
    ((globalSectionsFunctor k).map g).ambient =
      (affineGlobalSectionsFunctor k).map g.unop.ambient.op :=
  rfl

end GlobalSections

/-! ### The unit and counit -/

section UnitCounit

variable (P : OrlikSolomon.DivisorPair k)

/-- The unit `η : P ≅ Γ(Spec P)` of pair duality, `η` of `smoothAffineEquivalence` on each of the
three rings. -/
def unitIso : P ≅ globalSections (spec (SmoothDomain.aff k) P) where
  hom :=
    { ambient := (smoothAffineUnitIso k).hom.app P.ambient
      closed := (smoothAffineUnitIso k).hom.app P.closed
      compl := (smoothAffineUnitIso k).hom.app P.compl
      i_comp := (smoothAffineUnitIso k).hom.naturality P.i
      j_comp := (smoothAffineUnitIso k).hom.naturality P.j
      associated_eqn := .refl _ }
  inv :=
    { ambient := (smoothAffineUnitIso k).inv.app P.ambient
      closed := (smoothAffineUnitIso k).inv.app P.closed
      compl := (smoothAffineUnitIso k).inv.app P.compl
      i_comp := (smoothAffineUnitIso k).inv.naturality P.i
      j_comp := (smoothAffineUnitIso k).inv.naturality P.j
      associated_eqn := by
        change Associated ((Scheme.ΓSpecIso (.of P.ambient)).hom
          ((Scheme.ΓSpecIso (.of P.ambient)).inv P.eqn)) P.eqn
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] }
  hom_inv_id := OrlikSolomon.DivisorPair.hom_ext ((smoothAffineUnitIso k).hom_inv_id_app _)
  inv_hom_id := OrlikSolomon.DivisorPair.hom_ext ((smoothAffineUnitIso k).inv_hom_id_app _)

@[simp] lemma unitIso_hom_ambient :
    (unitIso P).hom.ambient = (smoothAffineUnitIso k).hom.app P.ambient := rfl
@[simp] lemma unitIso_hom_closed :
    (unitIso P).hom.closed = (smoothAffineUnitIso k).hom.app P.closed := rfl
@[simp] lemma unitIso_hom_compl :
    (unitIso P).hom.compl = (smoothAffineUnitIso k).hom.app P.compl := rfl
@[simp] lemma unitIso_inv_ambient :
    (unitIso P).inv.ambient = (smoothAffineUnitIso k).inv.app P.ambient := rfl
@[simp] lemma unitIso_inv_closed :
    (unitIso P).inv.closed = (smoothAffineUnitIso k).inv.app P.closed := rfl
@[simp] lemma unitIso_inv_compl :
    (unitIso P).inv.compl = (smoothAffineUnitIso k).inv.app P.compl := rfl

variable (Q : DivisorPair (SmoothDomain.aff k))

/-- The counit `ε⁻¹ : Q ≅ Spec Γ(Q)` of pair duality, `ε⁻¹` of `smoothAffineEquivalence` on each of
the three schemes. -/
def counitIso : Q ≅ spec (SmoothDomain.aff k) (globalSections Q) :=
  isoMk ((smoothAffineCounitIso k).app (op Q.ambient)).unop
    ((smoothAffineCounitIso k).app (op Q.closed)).unop
    ((smoothAffineCounitIso k).app (op Q.compl)).unop
    (congrArg Quiver.Hom.unop ((smoothAffineCounitIso k).hom.naturality Q.i.op)).symm
    (congrArg Quiver.Hom.unop ((smoothAffineCounitIso k).hom.naturality Q.j.op)).symm (by
      change Associated (Q.ambient.obj.left.isoSpec.hom.appTop
        ((Scheme.ΓSpecIso Γ(Q.ambient.obj.left, ⊤)).inv Q.eqn)) Q.eqn
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply, Iso.inv_hom_id,
        CommRingCat.id_apply])

@[simp] lemma counitIso_hom_ambient :
    (counitIso Q).hom.ambient = ((smoothAffineCounitIso k).hom.app (op Q.ambient)).unop := rfl
@[simp] lemma counitIso_hom_closed :
    (counitIso Q).hom.closed = ((smoothAffineCounitIso k).hom.app (op Q.closed)).unop := rfl
@[simp] lemma counitIso_hom_compl :
    (counitIso Q).hom.compl = ((smoothAffineCounitIso k).hom.app (op Q.compl)).unop := rfl
@[simp] lemma counitIso_inv_ambient :
    (counitIso Q).inv.ambient = ((smoothAffineCounitIso k).inv.app (op Q.ambient)).unop := rfl
@[simp] lemma counitIso_inv_closed :
    (counitIso Q).inv.closed = ((smoothAffineCounitIso k).inv.app (op Q.closed)).unop := rfl
@[simp] lemma counitIso_inv_compl :
    (counitIso Q).inv.compl = ((smoothAffineCounitIso k).inv.app (op Q.compl)).unop := rfl

end UnitCounit

end DivisorPair

/-! ### The anti-equivalence -/

variable (k) in
/-- **Duality for certified pairs.** Geometric pairs of smooth affine schemes are anti-equivalent to
algebraic pairs: `P ↦ Spec P` and `Q ↦ Γ(Q)` are inverse equivalences
`OrlikSolomon.DivisorPair k ≌ (DivisorPair (aff k))ᵒᵖ`, with unit `η` and counit `ε` of
`smoothAffineEquivalence` on each of the three objects of a pair. Arrows reverse, the immersions
and the equation correspond (`spec_i`, `spec_j`, `spec_eqn`, `globalSections_i`,
`globalSections_j`, `globalSections_eqn`), and so do the units on the open parts
(`coe_spec_eqnUnit`, `coe_globalSections_eqnUnit`), the standard pairs (`specStandardPairIso`) and
changes of equation (`globalSections_withEqn_eqn`). A geometric pair whose ambient scheme is affine
is a pair in `aff k` (`toAff`, `ofLE_toAff`).

Blueprint: `thm:geo-pair-duality`. -/
def affinePairEquivalence : OrlikSolomon.DivisorPair k ≌ (DivisorPair (SmoothDomain.aff k))ᵒᵖ where
  functor := DivisorPair.specFunctor (SmoothDomain.aff k)
  inverse := DivisorPair.globalSectionsFunctor k
  unitIso := NatIso.ofComponents DivisorPair.unitIso fun F ↦
    OrlikSolomon.DivisorPair.hom_ext ((smoothAffineUnitIso k).hom.naturality F.ambient)
  counitIso := NatIso.ofComponents (fun Q ↦ (DivisorPair.counitIso Q.unop).op) fun g ↦
    Quiver.Hom.unop_inj (DivisorPair.hom_ext (congrArg Quiver.Hom.unop
      ((smoothAffineCounitIso k).hom.naturality g.unop.ambient.op)))
  functor_unitIso_comp P := Quiver.Hom.unop_inj (DivisorPair.hom_ext (congrArg Quiver.Hom.unop
    ((smoothAffineEquivalence k).functor_unitIso_comp P.ambient)))

@[simp] lemma affinePairEquivalence_functor :
    (affinePairEquivalence k).functor = DivisorPair.specFunctor (SmoothDomain.aff k) := rfl

@[simp] lemma affinePairEquivalence_inverse :
    (affinePairEquivalence k).inverse = DivisorPair.globalSectionsFunctor k := rfl

@[simp] lemma affinePairEquivalence_unitIso_app (P : OrlikSolomon.DivisorPair k) :
    (affinePairEquivalence k).unitIso.app P = DivisorPair.unitIso P := rfl

@[simp] lemma affinePairEquivalence_counitIso_app (Q : (DivisorPair (SmoothDomain.aff k))ᵒᵖ) :
    (affinePairEquivalence k).counitIso.app Q = (DivisorPair.counitIso Q.unop).op := rfl

/-! ### Standard pairs -/

namespace DivisorPair

variable (D : SmoothDomain k) (A : SmoothAlg.{u} k)

/-- `Spec` of the algebraic standard pair `(A[z], A, A[z, z⁻¹], z)` is the geometric standard pair
of `Spec A`, through `Spec A[z] ≅ Spec A ×_S 𝔸¹` and `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, with the
identity on the divisor.

Blueprint: `thm:geo-pair-duality`, `lem:geo-products`. -/
def specStandardPairIso :
    spec D (OrlikSolomon.DivisorPair.standardPair A) ≅ standardPair D (D.spec A) :=
  isoMk (D.specPolynomialIso A) (Iso.refl (D.spec A)) (D.specLaurentIso A)
    (by
      refine (D.specFunctor_map_polynomialLift_zero_comp_specPolynomialIso_hom A).trans ?_
      exact (Category.id_comp _).symm)
    (D.specFunctor_map_polynomialToLaurent_comp_specPolynomialIso_hom A)
    (by
      change Associated ((Geometric.specPolynomialIso A.obj).hom.left.appTop (prodCoord _)) _
      rw [specPolynomialIso_hom_appTop_prodCoord]
      exact .refl _)

@[simp] lemma specStandardPairIso_hom_ambient :
    (specStandardPairIso D A).hom.ambient = (D.specPolynomialIso A).hom := rfl
@[simp] lemma specStandardPairIso_hom_closed :
    (specStandardPairIso D A).hom.closed = 𝟙 (D.spec A) := rfl
@[simp] lemma specStandardPairIso_hom_compl :
    (specStandardPairIso D A).hom.compl = (D.specLaurentIso A).hom := rfl

end DivisorPair

end OrlikSolomon.Geometric
