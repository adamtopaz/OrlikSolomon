/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Axioms

/-!
# Affine transport of ordinary cohomology

`OrdinaryTheory.toAlgebraic` evaluates a geometric theory on spectra. `ofAlgebraic` evaluates an
algebraic theory on affine global sections. Their canonical graded comparisons preserve pullback,
coefficients, Gysin and residue, and obey the affine-duality triangle identities.
Blueprint: `thm:geo-to-algebraic`, `thm:geo-from-algebraic`, `lem:geo-empty`.

## Main definitions

* `OrdinaryTheory.toAlgebraic`, `ofAlgebraic`: the two affine transports, with all 22 fields.
* `OrdinaryTheory.algebraicRoundTripEquiv`, `affineRoundTripEquiv`: canonical comparisons.

## Main results

* The comparisons preserve and reflect grading and commute with pullback, coefficient maps,
  Gysin and residue; their two `triangle` lemmas express the affine-duality triangle identities.
* `OrdinaryTheory.emptySubsingleton`, `gysin_eq_zero_of_isUnit`, `residue_eq_zero_of_isUnit`:
  vanishing forced by exactness, including zero coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

universe u v w z

namespace OrlikSolomon.Geometric
variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}

namespace OrdinaryTheory

variable (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-- Evaluation on spectra constructs all 22 fields of the algebraic theory. Gysin and residue
are the maps of the spectrum pair, with the same degrees and signs.
Blueprint: `thm:geo-to-algebraic`. -/
@[implicit_reducible]
def toAlgebraic : OrlikSolomon.OrdinaryTheory k ℬ where
  bijective_algebraMap_gradeZero := T.bijective_algebraMap_gradeZero
  C := D.specFunctor ⋙ T.C
  algebra A := T.algebra (D.spec A)
  isScalarTower A := T.isScalarTower (D.spec A)
  grading A := T.grading (D.spec A)
  gradedAlgebra A := T.gradedAlgebra (D.spec A)
  algebraMap_mem_grading A := T.algebraMap_mem_grading _
  isHomogeneousOfShift_map f := T.isHomogeneousOfShift_map (D.specFunctor.map f).unop
  isGradedCommutative A := T.isGradedCommutative _
  bijective_algebraMap_point := by
    have h := (T.pullIso D.specPointIso).bijective.comp T.bijective_algebraMap_point
    change Function.Bijective (algebraMap B (T.C.obj (op (D.spec (SmoothAlg.point k)))))
    have he : (T.pullIso D.specPointIso) ∘ algebraMap B (T.C.obj (op D.point)) =
        algebraMap B (T.C.obj (op (D.spec (SmoothAlg.point k)))) :=
      funext (T.pullIso D.specPointIso).commutes
    rw [he] at h
    exact h
  eq_zero_of_mem_grading_point hp x hx := by
    apply (T.pullIso D.specPointIso.symm).injective
    simpa using T.eq_zero_of_mem_grading_point hp (T.pull_mem_grading _ hx)
  bijective_map_polynomialC A := by
    have h : Function.Bijective (fun x ↦ T.pull (D.specPolynomialIso A).hom
        (T.pull (D.prodAffineLineFst (D.spec A)) x)) :=
      (T.pullIso (D.specPolynomialIso A)).bijective.comp
        (T.bijective_pullback_affineLine (D.spec A))
    have he := D.specPolynomialIso_hom_prodAffineLineFst A
    simp only [← pull_comp, he] at h
    exact h
  gysin P := T.gysin (DivisorPair.spec D P)
  residue P := T.residue (DivisorPair.spec D P)
  isHomogeneousOfShift_gysin P := T.isHomogeneousOfShift_gysin (DivisorPair.spec D P)
  isHomogeneousOfShift_residue P := T.isHomogeneousOfShift_residue (DivisorPair.spec D P)
  exact_gysin_map P := T.exact_gysin_map (DivisorPair.spec D P)
  exact_map_residue P := T.exact_map_residue (DivisorPair.spec D P)
  exact_residue_gysin P := T.exact_residue_gysin (DivisorPair.spec D P)
  gysin_map f := T.gysin_map (DivisorPair.specMap D f)
  residue_map f := T.residue_map (DivisorPair.specMap D f)
  residue_mul_map P := T.residue_mul_map (DivisorPair.spec D P)

@[simp] lemma toAlgebraic_map {A A' : SmoothAlg k} (f : A ⟶ A')
    (x : T.toAlgebraic.C.obj A) :
    T.toAlgebraic.C.map f x = T.pull (D.specFunctor.map f).unop x := rfl

@[simp] lemma toAlgebraic_gysin (P : OrlikSolomon.DivisorPair k)
    (x : T.toAlgebraic.C.obj P.closed) :
    T.toAlgebraic.gysin P x = T.gysin (DivisorPair.spec D P) x := rfl

@[simp] lemma toAlgebraic_residue (P : OrlikSolomon.DivisorPair k)
    (x : T.toAlgebraic.C.obj P.compl) :
    T.toAlgebraic.residue P x = T.residue (DivisorPair.spec D P) x := rfl

/-- Spectrum transport preserves the standard residue after the canonical Laurent comparison. -/
lemma toAlgebraic_standardResidue (A : SmoothAlg k)
    (x : T.obj (D.prodGm (D.spec A))) :
    T.toAlgebraic.stdResidue A (T.pull (D.specLaurentIso A).hom x) =
      T.standardResidue (D.spec A) x := by
  have h := T.residue_map (DivisorPair.specStandardPairIso D A).hom x
  change T.toAlgebraic.stdResidue A (T.pull (D.specLaurentIso A).hom x) =
    T.pull (𝟙 (D.spec A)) (T.standardResidue (D.spec A) x) at h
  simpa only [pull_id] using h

/-- Spectrum transport preserves the standard Gysin after the canonical polynomial comparison. -/
lemma toAlgebraic_standardGysin (A : SmoothAlg k) (x : T.obj (D.spec A)) :
    T.toAlgebraic.stdGysin A x =
      T.pull (D.specPolynomialIso A).hom (T.standardGysin (D.spec A) x) := by
  have h := T.gysin_map (DivisorPair.specStandardPairIso D A).hom x
  change T.toAlgebraic.stdGysin A (T.pull (𝟙 (D.spec A)) x) =
    T.pull (D.specPolynomialIso A).hom (T.standardGysin (D.spec A) x) at h
  simpa only [pull_id] using h

end OrdinaryTheory

private def prodAffineLineIso {D : SmoothDomain k} {X Y : D.Obj} (e : X ≅ Y) :
    D.prodAffineLine X ≅ D.prodAffineLine Y where
  hom := D.prodAffineLineMap e.hom
  inv := D.prodAffineLineMap e.inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    change (e.hom.hom ▷ affineLine k) ≫ (e.inv.hom ▷ affineLine k) = 𝟙 _
    rw [← comp_whiskerRight]
    change (e.hom ≫ e.inv).hom ▷ affineLine k = 𝟙 _
    rw [e.hom_inv_id]
    exact id_whiskerRight _ _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    change (e.inv.hom ▷ affineLine k) ≫ (e.hom.hom ▷ affineLine k) = 𝟙 _
    rw [← comp_whiskerRight]
    change (e.inv ≫ e.hom).hom ▷ affineLine k = 𝟙 _
    rw [e.inv_hom_id]
    exact id_whiskerRight _ _

private def affinePolynomialSchemeIso (X : (SmoothDomain.aff k).Obj) :
    (SmoothDomain.aff k).spec
        (SmoothAlg.polynomial ((affineGlobalSectionsFunctor k).obj (op X))) ≅
      (SmoothDomain.aff k).prodAffineLine X :=
  (SmoothDomain.aff k).specPolynomialIso _ ≪≫
    prodAffineLineIso ((smoothAffineCounitIso k).app (op X)).unop.symm

private def affinePointIso : SmoothAlg.point k ≅
    (affineGlobalSectionsFunctor k).obj (op (SmoothDomain.aff k).point) :=
  (smoothAffineUnitIso k).app _ ≪≫
    (affineGlobalSectionsFunctor k).mapIso (SmoothDomain.aff k).specPointIso.symm.op

private def affinePolynomialIso (X : (SmoothDomain.aff k).Obj) :
    SmoothAlg.polynomial ((affineGlobalSectionsFunctor k).obj (op X)) ≅
      (affineGlobalSectionsFunctor k).obj (op ((SmoothDomain.aff k).prodAffineLine X)) :=
  (smoothAffineUnitIso k).app _ ≪≫
    (affineGlobalSectionsFunctor k).mapIso (affinePolynomialSchemeIso X).symm.op

private lemma affinePolynomialIso_constants (X : (SmoothDomain.aff k).Obj) :
    SmoothAlg.polynomialC ((affineGlobalSectionsFunctor k).obj (op X)) ≫
        (affinePolynomialIso X).hom =
      (affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).prodAffineLineFst X).op := by
  let F := (SmoothDomain.aff k).specFunctor
  let G := affineGlobalSectionsFunctor k
  have hc : F.map (SmoothAlg.polynomialC (G.obj (op X))) ≫
        (affinePolynomialSchemeIso X).inv.op =
      (smoothAffineCounitIso k).hom.app (op X) ≫
        ((SmoothDomain.aff k).prodAffineLineFst X).op := by
    apply Quiver.Hom.unop_inj
    change (affinePolynomialSchemeIso X).inv ≫
        (F.map (SmoothAlg.polynomialC (G.obj (op X)))).unop =
      (SmoothDomain.aff k).prodAffineLineFst X ≫
        ((smoothAffineCounitIso k).hom.app (op X)).unop
    rw [← (SmoothDomain.aff k).specPolynomialIso_hom_prodAffineLineFst]
    dsimp only [affinePolynomialSchemeIso, Iso.trans_inv]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    apply ObjectProperty.hom_ext
    exact whiskerRight_fst _ _
  change SmoothAlg.polynomialC (G.obj (op X)) ≫
      ((smoothAffineUnitIso k).hom.app (SmoothAlg.polynomial (G.obj (op X))) ≫
        G.map (affinePolynomialSchemeIso X).inv.op) = _
  have hn := ((smoothAffineUnitIso k).hom.naturality
    (SmoothAlg.polynomialC (G.obj (op X)))).symm
  change (smoothAffineUnitIso k).hom.app (G.obj (op X)) ≫
    G.map (F.map (SmoothAlg.polynomialC (G.obj (op X)))) =
    SmoothAlg.polynomialC (G.obj (op X)) ≫
      (smoothAffineUnitIso k).hom.app (SmoothAlg.polynomial (G.obj (op X))) at hn
  rw [← Category.assoc, ← hn, Category.assoc, ← G.map_comp, hc,
    G.map_comp, ← Category.assoc]
  have ht := (smoothAffineEquivalence k).unit_inverse_comp (op X)
  change (smoothAffineUnitIso k).hom.app (G.obj (op X)) ≫
    G.map ((smoothAffineCounitIso k).hom.app (op X)) = 𝟙 _ at ht
  rw [ht]
  exact Category.id_comp _

namespace OrdinaryTheory

variable (E : OrlikSolomon.OrdinaryTheory.{u, v, w, z} k ℬ)

/-- Evaluation on affine global sections constructs the geometric ordinary theory. Every field
is transported, including both pair naturalities. Blueprint: `thm:geo-from-algebraic`. -/
@[implicit_reducible]
def ofAlgebraic : OrdinaryTheory (SmoothDomain.aff k) ℬ where
  bijective_algebraMap_gradeZero := E.bijective_algebraMap_gradeZero
  C := affineGlobalSectionsFunctor k ⋙ E.C
  algebra X := E.algebra _
  isScalarTower X := E.isScalarTower _
  grading X := E.grading ((affineGlobalSectionsFunctor k).obj (op X))
  gradedAlgebra X := E.gradedAlgebra _
  algebraMap_mem_grading X := E.algebraMap_mem_grading _
  isHomogeneousOfShift_map f := E.isHomogeneousOfShift_map _
  isGradedCommutative X := E.isGradedCommutative _
  bijective_algebraMap_point := by
    have h := (E.C.mapIso affinePointIso).toAlgEquiv.bijective.comp E.bijective_algebraMap_point
    have he : (E.C.mapIso affinePointIso).toAlgEquiv ∘
        algebraMap B (E.C.obj (SmoothAlg.point k)) =
        algebraMap B (E.C.obj ((affineGlobalSectionsFunctor k).obj
          (op (SmoothDomain.aff k).point))) :=
      funext (E.C.mapIso affinePointIso).toAlgEquiv.commutes
    rw [he] at h
    exact h
  eq_zero_of_mem_grading_point hp x hx := by
    apply (E.C.mapIso affinePointIso.symm).toAlgEquiv.injective
    simpa using E.eq_zero_of_mem_grading_point hp
      (E.map_mem_grading affinePointIso.inv hx)
  bijective_pullback_affineLine X := by
    have h := (E.C.mapIso (affinePolynomialIso X)).toAlgEquiv.bijective.comp
      (E.bijective_map_polynomialC _)
    have he := congrArg E.C.map (affinePolynomialIso_constants X)
    rw [Functor.map_comp] at he
    change Function.Bijective (fun x ↦ E.C.map (affinePolynomialIso X).hom
      (E.C.map (SmoothAlg.polynomialC _) x)) at h
    simp only [← AlgCat.comp_apply, he] at h
    exact h
  gysin P := E.gysin (DivisorPair.globalSections P)
  residue P := E.residue (DivisorPair.globalSections P)
  isHomogeneousOfShift_gysin P := E.isHomogeneousOfShift_gysin (DivisorPair.globalSections P)
  isHomogeneousOfShift_residue P := E.isHomogeneousOfShift_residue (DivisorPair.globalSections P)
  exact_gysin_map P := E.exact_gysin_map (DivisorPair.globalSections P)
  exact_map_residue P := E.exact_map_residue (DivisorPair.globalSections P)
  exact_residue_gysin P := E.exact_residue_gysin (DivisorPair.globalSections P)
  gysin_map f := E.gysin_map (DivisorPair.globalSectionsMap f)
  residue_map f := E.residue_map (DivisorPair.globalSectionsMap f)
  residue_mul_map P := E.residue_mul_map (DivisorPair.globalSections P)

@[simp] lemma ofAlgebraic_pull {X Y : (SmoothDomain.aff k).Obj} (f : X ⟶ Y)
    (x : (ofAlgebraic E).obj Y) :
    (ofAlgebraic E).pull f x = E.C.map ((affineGlobalSectionsFunctor k).map f.op) x := rfl

@[simp] lemma ofAlgebraic_gysin (P : DivisorPair (SmoothDomain.aff k))
    (x : (ofAlgebraic E).obj P.closed) :
    (ofAlgebraic E).gysin P x = E.gysin (DivisorPair.globalSections P) x := rfl

@[simp] lemma ofAlgebraic_residue (P : DivisorPair (SmoothDomain.aff k))
    (x : (ofAlgebraic E).obj P.compl) :
    (ofAlgebraic E).residue P x = E.residue (DivisorPair.globalSections P) x := rfl

/-- The algebraic round-trip comparison is cohomology of the unit `A ≅ Γ(Spec A)`.
Blueprint: `thm:geo-from-algebraic`. -/
def algebraicRoundTripEquiv (A : SmoothAlg k) :
    E.C.obj A ≃ₐ[B] (ofAlgebraic E).toAlgebraic.C.obj A :=
  (E.C.mapIso ((smoothAffineUnitIso k).app A)).toAlgEquiv

@[simp] lemma algebraicRoundTripEquiv_apply (A : SmoothAlg k) (x : E.C.obj A) :
    algebraicRoundTripEquiv E A x = E.C.map ((smoothAffineUnitIso k).hom.app A) x := rfl

/-- The algebraic round-trip comparison preserves and reflects each bidegree. -/
lemma algebraicRoundTripEquiv_mem_grading_iff (A : SmoothAlg k) {i : ℤ × ℤ}
    {x : E.C.obj A} :
    algebraicRoundTripEquiv E A x ∈ (ofAlgebraic E).toAlgebraic.grading A i ↔
      x ∈ E.grading A i := by
  constructor
  · intro hx
    have h := E.map_mem_grading ((smoothAffineUnitIso k).inv.app A) hx
    change E.C.map ((smoothAffineUnitIso k).inv.app A)
      (E.C.map ((smoothAffineUnitIso k).hom.app A) x) ∈ E.grading A i at h
    rw [E.map_map, (smoothAffineUnitIso k).hom_inv_id_app, E.C.map_id] at h
    exact h
  · exact E.map_mem_grading ((smoothAffineUnitIso k).hom.app A)

/-- Pullback commutes with the algebraic round-trip comparison. -/
lemma algebraicRoundTripEquiv_map {A A' : SmoothAlg k} (f : A ⟶ A') (x : E.C.obj A) :
    algebraicRoundTripEquiv E A' (E.C.map f x) =
      (ofAlgebraic E).toAlgebraic.C.map f (algebraicRoundTripEquiv E A x) := by
  change E.C.map ((smoothAffineUnitIso k).hom.app A') (E.C.map f x) =
    E.C.map ((affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).specFunctor.map f))
      (E.C.map ((smoothAffineUnitIso k).hom.app A) x)
  have hn := (smoothAffineUnitIso k).hom.naturality f
  change f ≫ (smoothAffineUnitIso k).hom.app A' =
    (smoothAffineUnitIso k).hom.app A ≫
      (affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).specFunctor.map f) at hn
  rw [E.map_map, E.map_map, hn]

/-- Gysin commutes with the algebraic round-trip comparison on certified pairs. -/
lemma algebraicRoundTripEquiv_gysin (P : OrlikSolomon.DivisorPair k) (x : E.C.obj P.closed) :
    algebraicRoundTripEquiv E P.ambient (E.gysin P x) =
      (ofAlgebraic E).toAlgebraic.gysin P (algebraicRoundTripEquiv E P.closed x) :=
  (E.gysin_map (DivisorPair.unitIso P).hom x).symm

/-- Residue commutes with the algebraic round-trip comparison on certified pairs. -/
lemma algebraicRoundTripEquiv_residue (P : OrlikSolomon.DivisorPair k) (x : E.C.obj P.compl) :
    algebraicRoundTripEquiv E P.closed (E.residue P x) =
      (ofAlgebraic E).toAlgebraic.residue P (algebraicRoundTripEquiv E P.compl x) :=
  (E.residue_map (DivisorPair.unitIso P).hom x).symm

/-- The algebraic round-trip comparison fixes coefficients. -/
lemma algebraicRoundTripEquiv_algebraMap (A : SmoothAlg k) (b : B) :
    algebraicRoundTripEquiv E A (algebraMap B (E.C.obj A) b) =
      algebraMap B ((ofAlgebraic E).toAlgebraic.C.obj A) b :=
  (algebraicRoundTripEquiv E A).commutes b

variable (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The canonical affine evaluation isomorphism `Spec Γ(X) ≅ X`, in the original domain. -/
def affineEvaluationIso (X : (SmoothDomain.aff k).Obj) :
    D.spec ((affineGlobalSectionsFunctor k).obj (op X)) ≅
      (ObjectProperty.ιOfLE (SmoothDomain.aff_le D)).obj X :=
  ObjectProperty.isoMk _ (specGlobalSectionsIso X.obj)

/-- The geometric round trip recovers precisely the affine restriction, by pullback along the
canonical evaluation isomorphism. No value on a non-affine scheme is reconstructed.
Blueprint: `thm:geo-from-algebraic`. -/
def affineRoundTripEquiv (X : (SmoothDomain.aff k).Obj) :
    (T.restrict (SmoothDomain.aff_le D)).obj X ≃ₐ[B] (ofAlgebraic T.toAlgebraic).obj X :=
  T.pullIso (affineEvaluationIso X)

@[simp] lemma affineRoundTripEquiv_apply (X : (SmoothDomain.aff k).Obj)
    (x : (T.restrict (SmoothDomain.aff_le D)).obj X) :
    affineRoundTripEquiv T X x = T.pull (affineEvaluationIso X).hom x := rfl

/-- The geometric round-trip comparison preserves and reflects each bidegree. -/
lemma affineRoundTripEquiv_mem_grading_iff (X : (SmoothDomain.aff k).Obj) {i : ℤ × ℤ}
    {x : (T.restrict (SmoothDomain.aff_le D)).obj X} :
    affineRoundTripEquiv T X x ∈ (ofAlgebraic T.toAlgebraic).grading X i ↔
      x ∈ (T.restrict (SmoothDomain.aff_le D)).grading X i :=
  T.pullIso_mem_grading_iff (affineEvaluationIso X)

/-- Pullback commutes with the geometric round-trip comparison. -/
lemma affineRoundTripEquiv_pull {X Y : (SmoothDomain.aff k).Obj} (f : X ⟶ Y)
    (x : (T.restrict (SmoothDomain.aff_le D)).obj Y) :
    affineRoundTripEquiv T X ((T.restrict (SmoothDomain.aff_le D)).pull f x) =
      (ofAlgebraic T.toAlgebraic).pull f (affineRoundTripEquiv T Y x) := by
  change T.pull (affineEvaluationIso X).hom
      (T.pull ((ObjectProperty.ιOfLE (SmoothDomain.aff_le D)).map f) x) =
    T.pull (D.specFunctor.map ((affineGlobalSectionsFunctor k).map f.op)).unop
      (T.pull (affineEvaluationIso Y).hom x)
  rw [← pull_comp, ← pull_comp]
  have he : (affineEvaluationIso (D := D) X).hom ≫
      (ObjectProperty.ιOfLE (SmoothDomain.aff_le D)).map f =
      (D.specFunctor.map ((affineGlobalSectionsFunctor k).map f.op)).unop ≫
        (affineEvaluationIso Y).hom :=
    ObjectProperty.hom_ext _ (specGlobalSectionsIso_naturality f.hom).symm
  exact congrArg (fun g ↦ T.pull g x) he

/-- Gysin commutes with the geometric round-trip comparison on every affine pair. -/
lemma affineRoundTripEquiv_gysin (P : DivisorPair (SmoothDomain.aff k))
    (x : (T.restrict (SmoothDomain.aff_le D)).obj P.closed) :
    affineRoundTripEquiv T P.ambient ((T.restrict (SmoothDomain.aff_le D)).gysin P x) =
      (ofAlgebraic T.toAlgebraic).gysin P (affineRoundTripEquiv T P.closed x) := by
  exact (T.gysin_map ((DivisorPair.functorOfLE (SmoothDomain.aff_le D)).map
    (DivisorPair.counitIso P).inv) x).symm

/-- Residue commutes with the geometric round-trip comparison on every affine pair. -/
lemma affineRoundTripEquiv_residue (P : DivisorPair (SmoothDomain.aff k))
    (x : (T.restrict (SmoothDomain.aff_le D)).obj P.compl) :
    affineRoundTripEquiv T P.closed ((T.restrict (SmoothDomain.aff_le D)).residue P x) =
      (ofAlgebraic T.toAlgebraic).residue P (affineRoundTripEquiv T P.compl x) := by
  exact (T.residue_map ((DivisorPair.functorOfLE (SmoothDomain.aff_le D)).map
    (DivisorPair.counitIso P).inv) x).symm

/-- The geometric round-trip comparison fixes coefficients. -/
lemma affineRoundTripEquiv_algebraMap (X : (SmoothDomain.aff k).Obj) (b : B) :
    affineRoundTripEquiv T X
        (algebraMap B ((T.restrict (SmoothDomain.aff_le D)).obj X) b) =
      algebraMap B ((ofAlgebraic T.toAlgebraic).obj X) b :=
  (affineRoundTripEquiv T X).commutes b

/-- The geometric triangle identity: on a spectrum the two comparison maps are compatible
inverses. This is cohomology of the first affine-duality triangle. -/
lemma affineRoundTripEquiv_triangle (A : SmoothAlg k) (x : T.toAlgebraic.C.obj A) :
    (affineRoundTripEquiv T ((SmoothDomain.aff k).spec A)).symm
        (algebraicRoundTripEquiv T.toAlgebraic A x) = x := by
  apply (affineRoundTripEquiv T ((SmoothDomain.aff k).spec A)).injective
  rw [AlgEquiv.apply_symm_apply]
  change T.pull (D.specFunctor.map ((smoothAffineUnitIso k).hom.app A)).unop x =
    T.pull (affineEvaluationIso ((SmoothDomain.aff k).spec A)).hom x
  have he : (D.specFunctor.map ((smoothAffineUnitIso k).hom.app A)).unop =
      (affineEvaluationIso ((SmoothDomain.aff k).spec A)).hom :=
    ObjectProperty.hom_ext _ (specGlobalSectionsIso_hom_spec A.obj).symm
  exact congrArg (fun g ↦ T.pull g x) he

/-- The algebraic triangle identity: after global sections, the two comparison maps are compatible
inverses. This is cohomology of the second affine-duality triangle. -/
lemma algebraicRoundTripEquiv_triangle (X : (SmoothDomain.aff k).Obj)
    (x : (ofAlgebraic E).obj X) :
    (algebraicRoundTripEquiv E ((affineGlobalSectionsFunctor k).obj (op X))).symm
        (affineRoundTripEquiv (ofAlgebraic E) X x) = x := by
  apply (algebraicRoundTripEquiv E ((affineGlobalSectionsFunctor k).obj (op X))).injective
  rw [AlgEquiv.apply_symm_apply]
  change E.C.map ((affineGlobalSectionsFunctor k).map
      (affineEvaluationIso X).hom.op) x =
    E.C.map ((smoothAffineUnitIso k).hom.app ((affineGlobalSectionsFunctor k).obj (op X))) x
  have he : (affineGlobalSectionsFunctor k).map (affineEvaluationIso X).hom.op =
      (smoothAffineUnitIso k).hom.app ((affineGlobalSectionsFunctor k).obj (op X)) :=
    ObjectProperty.hom_ext _ (globalSectionsMap_specGlobalSectionsIso_hom (X := X.obj))
  rw [he]

/-- Every empty scheme has zero cohomology, as a consequence of localization exactness, without
an empty-object axiom. Blueprint: `lem:geo-empty`. -/
lemma emptySubsingleton (X : D.Obj) [IsEmpty X.obj.left] : Subsingleton (T.obj X) := by
  let A : SmoothAlg k := ⟨globalSections X.obj, inferInstance⟩
  have : Subsingleton A := inferInstanceAs (Subsingleton Γ(X.obj.left, ⊤))
  have : Subsingleton (T.obj (D.spec A)) := T.toAlgebraic.subsingleton_obj_of_subsingleton A
  let e : D.spec A ≅ X := ObjectProperty.isoMk _ (specGlobalSectionsIso X.obj)
  exact (T.pullIso e).injective.subsingleton

/-- A unit equation has zero Gysin, since its closed scheme is empty. -/
lemma gysin_eq_zero_of_isUnit (P : DivisorPair D) (h : IsUnit P.eqn) : T.gysin P = 0 := by
  have := P.isEmpty_closed_of_isUnit h
  have : Subsingleton (T.C.obj (op P.closed)) := T.emptySubsingleton P.closed
  ext x
  rw [Subsingleton.elim x 0, map_zero]
  rfl

/-- A unit equation has zero residue, since its closed scheme is empty. -/
lemma residue_eq_zero_of_isUnit (P : DivisorPair D) (h : IsUnit P.eqn) : T.residue P = 0 := by
  have := P.isEmpty_closed_of_isUnit h
  have : Subsingleton (T.C.obj (op P.closed)) := T.emptySubsingleton P.closed
  exact Subsingleton.elim _ _

end OrdinaryTheory
end OrlikSolomon.Geometric
