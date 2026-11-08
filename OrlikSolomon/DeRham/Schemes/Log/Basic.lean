/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms
public import OrlikSolomon.Geometry.Schemes.PrincipalPair
public import OrlikSolomon.DeRham.Log.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Logarithmic forms on schemes

For a principal smooth divisor pair, the logarithmic sheaves are the images of regular forms
and their products on the left with `θ = df / f` inside the ordinary direct image of forms on
the complement. The differential is base-linear, and the closed shift has differential `-d`.

## Main definitions and results

* `thetaSection`: the global logarithmic form on the complement.
* `thetaWedgeSheaf`: left exterior multiplication by the logarithmic form of a global unit.
* `logComplexNat`, `logSheaf`: logarithmic forms as the image of the normal-form chain map.
* `logMkSheaf`: the epimorphism giving local regular-plus-left-theta normal forms.
* `logSheafImageIso`: comparison with the degreewise categorical image of that formula.
* `regularToLogSheaf`, `logToOpenSheaf`: the canonical regular and open inclusions.
* `shiftedClosedComplexNat`: the explicit divisor shift with differential `-d`.

The constructions use a commutative base ring. No characteristic-zero hypothesis, global
localization assertion for a non-affine scheme, or rational point is needed.

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

attribute [local instance] strongEpi_of_epi

variable {k : Type u} [CommRing k]

section Unit

variable (X : Over (Spec (CommRingCat.of k))) (v : (sectionAlgebra k X ⊤)ˣ)

private def restrictedUnit (U : X.left.Opens) : (sectionAlgebra k X U)ˣ :=
  Units.map ((sectionRestriction k X U.leTop).toMonoidHom) v

private theorem restrictedUnit_naturality {U V : X.left.Opens} (i : U ⟶ V) :
    Units.map (sectionRestriction k X i).toMonoidHom (restrictedUnit X v V) =
      restrictedUnit X v U := by
  apply Units.ext
  change sectionRestriction k X i (sectionRestriction k X V.leTop (v : sectionAlgebra k X ⊤)) =
    sectionRestriction k X U.leTop (v : sectionAlgebra k X ⊤)
  exact (AlgHom.congr_fun (sectionRestriction_comp k X i V.leTop) v).symm

private def thetaWedgePresheaf (n : ℕ) :
    formsPresheaf k X n ⟶ formsPresheaf k X (n + 1) where
  app U := ModuleCat.ofHom
    { toFun a := ⟨dlog k (restrictedUnit X v U.unop) * a.val, by
        simpa only [Nat.add_comm 1 n] using
          SetLike.mul_mem_graded (dlog_mem_exteriorPower_one k _) a.property⟩
      map_add' a b := Subtype.ext (mul_add _ _ _)
      map_smul' r a := Subtype.ext (mul_smul_comm _ _ _) }
  naturality U V i := by
    ext a
    apply Subtype.ext
    symm
    change Forms.map (sectionRestriction k X i.unop)
      (dlog k (restrictedUnit X v U.unop) * a.val) =
        dlog k (restrictedUnit X v V.unop) * Forms.map (sectionRestriction k X i.unop) a.val
    rw [map_mul, Forms.map_dlog]
    congr 2
    exact restrictedUnit_naturality X v i.unop

private theorem thetaWedgePresheaf_d (n : ℕ) :
    thetaWedgePresheaf X v n ≫ formsPresheafD k X (n + 1) =
      -(formsPresheafD k X n ≫ thetaWedgePresheaf X v (n + 1)) := by
  ext U a
  apply Subtype.ext
  exact d_dlog_mul k (restrictedUnit X v U.unop) a.val

/-- Left exterior multiplication by the logarithmic form of a global unit, on sheaves of
relative forms. Its construction uses restrictions of the unit, rather than any assertion
about localization of global sections. -/
@[no_expose] def thetaWedgeSheaf (n : ℕ) : formsSheaf k X n ⟶ formsSheaf k X (n + 1) :=
  (presheafToSheaf (_root_.Opens.grothendieckTopology X.left) (ModuleCat k)).map
    (thetaWedgePresheaf X v n)

/-- Multiplication by a closed logarithmic one-form anticommutes with the differential. -/
theorem thetaWedgeSheaf_d (n : ℕ) :
    thetaWedgeSheaf X v n ≫ formsSheafD k X (n + 1) =
      -(formsSheafD k X n ≫ thetaWedgeSheaf X v (n + 1)) := by
  change (presheafToSheaf _ (ModuleCat k)).map (thetaWedgePresheaf X v n) ≫
    (presheafToSheaf _ (ModuleCat k)).map (formsPresheafD k X (n + 1)) = _
  rw [← Functor.map_comp, thetaWedgePresheaf_d, Functor.map_neg, Functor.map_comp]
  rfl

/-- Multiplication by the logarithmic form acts on algebraic representatives by exterior
multiplication on the left. -/
theorem thetaWedgeSheaf_unit (n : ℕ) (U : X.left.Opensᵒᵖ)
    (a : (formsPresheaf k X n).obj U) :
    (thetaWedgeSheaf X v n).hom.app U ((formsSheafUnit k X n).app U a) =
      (formsSheafUnit k X (n + 1)).app U
        ⟨dlog k (Units.map (sectionRestriction k X U.unop.leTop).toMonoidHom v) * a.val,
          by simpa only [Nat.add_comm 1 n] using
            SetLike.mul_mem_graded (dlog_mem_exteriorPower_one k _) a.property⟩ := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality _ (thetaWedgePresheaf X v n)) U) a |>.symm

/-- Left multiplication by the logarithmic form of a unit is linear over regular functions.
The differential itself remains only base-ring linear. -/
theorem thetaWedgeSheaf_smul (n : ℕ) (U : X.left.Opens) (r : Γ(X.left, U))
    (a : (formsSheaf k X n).obj.obj (op U)) :
    (thetaWedgeSheaf X v n).hom.app (op U) (formsSheafSMul k X n U r a) =
      formsSheafSMul k X (n + 1) U r ((thetaWedgeSheaf X v n).hom.app (op U) a) := by
  have : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X.left)
      (formsSheafUnit k X n) := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ (formsPresheaf k X n))
    infer_instance
  apply (formsSheaf k X (n + 1)).isSeparated _ _
    (Presheaf.imageSieve_mem _ (formsSheafUnit k X n) a)
  rintro V f ⟨b, hb⟩
  have hθ (x : (formsSheaf k X n).obj.obj (op U)) :
      (formsSheaf k X (n + 1)).obj.map f.op ((thetaWedgeSheaf X v n).hom.app (op U) x) =
        (thetaWedgeSheaf X v n).hom.app (op V) ((formsSheaf k X n).obj.map f.op x) :=
    (ConcreteCategory.congr_hom ((thetaWedgeSheaf X v n).hom.naturality f.op) x).symm
  change (formsSheaf k X (n + 1)).obj.map f.op
      ((thetaWedgeSheaf X v n).hom.app (op U) (formsSheafSMul k X n U r a)) =
    (formsSheaf k X (n + 1)).obj.map f.op
      (formsSheafSMul k X (n + 1) U r ((thetaWedgeSheaf X v n).hom.app (op U) a))
  rw [hθ, formsSheafSMul_naturality, formsSheafSMul_naturality, hθ]
  have hb' : (formsSheafUnit k X n).app (op V) b = (formsSheaf k X n).obj.map f.op a := hb
  rw [← hb']
  let c : ⋀[sectionAlgebra k X V]^n Ω[sectionAlgebra k X V⁄k] := b
  let r' : sectionAlgebra k X V := sectionRestriction k X f r
  let t : ⋀[sectionAlgebra k X V]^(n + 1) Ω[sectionAlgebra k X V⁄k] :=
    (thetaWedgePresheaf X v n).app (op V) c
  have ht : (thetaWedgeSheaf X v n).hom.app (op V)
      ((formsSheafUnit k X n).app (op V) c) =
        (formsSheafUnit k X (n + 1)).app (op V) t :=
    thetaWedgeSheaf_unit X v n (op V) c
  have hr : (thetaWedgePresheaf X v n).app (op V) (r' • c) = r' • t :=
    Subtype.ext (mul_smul_comm _ _ _)
  calc
    _ = (thetaWedgeSheaf X v n).hom.app (op V)
        ((formsSheafUnit k X n).app (op V) (r' • c)) :=
      congrArg ((thetaWedgeSheaf X v n).hom.app (op V))
        (formsSheafSMul_unit k X n V r' c)
    _ = (formsSheafUnit k X (n + 1)).app (op V)
        ((thetaWedgePresheaf X v n).app (op V) (r' • c)) :=
      thetaWedgeSheaf_unit X v n (op V) (r' • c)
    _ = (formsSheafUnit k X (n + 1)).app (op V) (r' • t) := congrArg _ hr
    _ = formsSheafSMul k X (n + 1) V r'
        ((formsSheafUnit k X (n + 1)).app (op V) t) :=
      (formsSheafSMul_unit k X (n + 1) V r' t).symm
    _ = _ := congrArg (formsSheafSMul k X (n + 1) V r') ht.symm

end Unit

section UnitPullback

variable {X Y : Over (Spec (CommRingCat.of k))} (g : X ⟶ Y)
  (v : (sectionAlgebra k Y ⊤)ˣ)

private theorem restrictedUnit_pullback (U : Y.left.Opens) :
    Units.map (sectionPullback g U).toMonoidHom (restrictedUnit Y v U) =
      restrictedUnit X (Units.map (sectionPullbackTop g).toMonoidHom v) (g.left ⁻¹ᵁ U) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (g.left.naturality U.leTop.op)
    (v : sectionAlgebra k Y ⊤)

/-- Exterior multiplication by a unit's logarithmic form commutes with arbitrary pullback.
This equality includes open restrictions and affine comparison isomorphisms, and requires no
flatness hypothesis. -/
theorem thetaWedgeSheaf_pullback (n : ℕ) :
    thetaWedgeSheaf Y v n ≫ formsSheafPullback g (n + 1) =
      formsSheafPullback g n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).map
          (thetaWedgeSheaf X (Units.map (sectionPullbackTop g).toMonoidHom v) n) := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (_root_.Opens.grothendieckTopology Y.left) _ _
    ((TopCat.Sheaf.pushforward (ModuleCat k) g.left.base).obj
      (formsSheaf k X (n + 1))).property
  ext U a
  change (formsSheafPullback g (n + 1)).hom.app U
      ((thetaWedgeSheaf Y v n).hom.app U ((formsSheafUnit k Y n).app U a)) =
    (thetaWedgeSheaf X (Units.map (sectionPullbackTop g).toMonoidHom v) n).hom.app
      (op (g.left ⁻¹ᵁ U.unop))
        ((formsSheafPullback g n).hom.app U ((formsSheafUnit k Y n).app U a))
  have hθ (Z : Over (Spec (CommRingCat.of k))) (w : (sectionAlgebra k Z ⊤)ˣ)
      (V : Z.left.Opensᵒᵖ) (z : (formsPresheaf k Z n).obj V) :
      (thetaWedgeSheaf Z w n).hom.app V ((formsSheafUnit k Z n).app V z) =
        (formsSheafUnit k Z (n + 1)).app V ((thetaWedgePresheaf Z w n).app V z) :=
    (ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality _ (thetaWedgePresheaf Z w n)) V) z).symm
  have hu (m : ℕ) (z : (formsPresheaf k Y m).obj U) :
      (formsSheafPullback g m).hom.app U ((formsSheafUnit k Y m).app U z) =
        (formsSheafUnit k X m).app (op (g.left ⁻¹ᵁ U.unop))
          ((formsPresheafPullback g m).app U z) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (formsSheafPullback_unit g m) U) z
  rw [hθ, hu, hu, hθ]
  congr 1
  apply Subtype.ext
  change Forms.map (sectionPullback g U.unop)
    (dlog k (restrictedUnit Y v U.unop) * a.val) =
      dlog k (restrictedUnit X (Units.map (sectionPullbackTop g).toMonoidHom v)
        (g.left ⁻¹ᵁ U.unop)) * Forms.map (sectionPullback g U.unop) a.val
  rw [map_mul, Forms.map_dlog]
  congr 2
  exact restrictedUnit_pullback g v U.unop

end UnitPullback

section Shift

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  (K : CochainComplex C ℕ)

/-- The terms of a nonnegative complex shifted up one degree, with zero in degree zero. -/
def signedShiftedX : ℕ → C
  | 0 => 0
  | n + 1 => K.X n

/-- The signed differential of a nonnegative complex shifted up one degree. -/
def signedShiftedD : (n : ℕ) → signedShiftedX K n ⟶ signedShiftedX K (n + 1)
  | 0 => 0
  | n + 1 => -K.d n (n + 1)

/-- A nonnegative complex shifted up one degree, with differential `-d`. This explicit
nonnegative model is the convention used by the logarithmic residue sequence. -/
def signedShiftedComplexNat : CochainComplex C ℕ :=
  CochainComplex.of (signedShiftedX K) (signedShiftedD K) (by
    rintro (_ | n)
    · exact zero_comp
    · change (-K.d n (n + 1)) ≫ (-K.d (n + 1) (n + 1 + 1)) = 0
      rw [neg_comp, comp_neg, neg_neg, K.d_comp_d])

/-- The differential on the positive degrees of the explicit shift is the negative differential. -/
theorem signedShiftedComplexNat_d (n : ℕ) :
    (signedShiftedComplexNat K).d (n + 1) (n + 1 + 1) = -K.d n (n + 1) :=
  CochainComplex.of_d _ _ _

end Shift

/-- Ordinary direct image of module sheaves is additive. -/
instance sheafPushforward_additive {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).Additive where
  map_add := by intros; rfl

variable {D : SmoothDomain k} (P : Geometric.DivisorPair D)

/-- The global one-form `θ = df / f` on the open complement of a principal smooth divisor pair.

Blueprint: `thm:geo-log-sheaves`. -/
def thetaSection : (formsSheaf k P.compl.obj 1).obj.obj (op ⊤) :=
  (formsSheafUnit k P.compl.obj 1).app (op ⊤)
    ⟨dlog k P.eqnUnit, dlog_mem_exteriorPower_one k _⟩

-- Algebraic exterior-power carriers and presheaf section carriers coincide after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The logarithmic section restricts to the differential of the restricted unit. -/
lemma thetaSection_restrict (U : P.compl.obj.left.Opens) :
    (formsSheaf k P.compl.obj 1).obj.map U.leTop.op (thetaSection P) =
      (formsSheafUnit k P.compl.obj 1).app (op U)
        ⟨dlog k (Units.map (sectionRestriction k P.compl.obj U.leTop).toMonoidHom
          P.eqnUnit), dlog_mem_exteriorPower_one k _⟩ := by
  rw [thetaSection]
  rw [← (formsSheafUnit k P.compl.obj 1).naturality_apply U.leTop.op]
  congr 1
  apply Subtype.ext
  exact Forms.map_dlog _ _

-- The sheafification representative and its exterior degree cast use the same underlying form.
set_option backward.isDefEq.respectTransparency false in
/-- On every complement open, left logarithmic multiplication is the wedge product with
the restriction of the actual global section `thetaSection`. The cast records `1 + n = n + 1`. -/
lemma thetaWedgeSheaf_eq_wedge (n : ℕ) (U : P.compl.obj.left.Opens)
    (a : (formsSheaf k P.compl.obj n).obj.obj (op U)) :
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op U) a =
      (formsSheafCast k P.compl.obj (Nat.add_comm 1 n)).hom.app (op U)
        (formsSheafWedge k P.compl.obj 1 n (op U)
          ((formsSheaf k P.compl.obj 1).obj.map U.leTop.op (thetaSection P)) a) := by
  have : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology P.compl.obj.left)
      (formsSheafUnit k P.compl.obj n) := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ (formsPresheaf k P.compl.obj n))
    infer_instance
  apply (formsSheaf k P.compl.obj (n + 1)).isSeparated _ _
    (Presheaf.imageSieve_mem _ (formsSheafUnit k P.compl.obj n) a)
  rintro V f ⟨b, hb⟩
  rw [← (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.naturality_apply f.op,
    ← (formsSheafCast k P.compl.obj (Nat.add_comm 1 n)).hom.naturality_apply f.op,
    formsSheafWedge_naturality, ← Functor.map_comp_apply, ← hb]
  have hf : U.leTop.op ≫ f.op = V.leTop.op := Subsingleton.elim _ _
  rw [hf, thetaSection_restrict, thetaWedgeSheaf_unit, formsSheafWedge_unit,
    formsSheafCast_unit_apply]
  congr 1
  apply Subtype.ext
  let c : (formsPresheaf k P.compl.obj 1).obj (op V) :=
    ⟨dlog k (Units.map (sectionRestriction k P.compl.obj V.leTop).toMonoidHom
      P.eqnUnit), dlog_mem_exteriorPower_one k _⟩
  change (dlog k (Units.map (sectionRestriction k P.compl.obj V.leTop).toMonoidHom
      P.eqnUnit) * b.val) =
    ((formsPresheafCast k P.compl.obj (Nat.add_comm 1 n)).app (op V)
      ((formsPresheafMul k P.compl.obj 1 n).app (op V) (c ⊗ₜ[k] b)) :
        ⋀[sectionAlgebra k P.compl.obj V]^(n + 1) Ω[sectionAlgebra k P.compl.obj V⁄k]).val
  rw [formsPresheafCast_val, formsPresheafMul_tmul]

/-- On global sections, logarithmic multiplication is wedge with `thetaSection` itself,
without restricting it along the identity of the top open. -/
lemma thetaWedgeSheaf_top_eq_wedge (n : ℕ)
    (a : (formsSheaf k P.compl.obj n).obj.obj (op ⊤)) :
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op ⊤) a =
      (formsSheafCast k P.compl.obj (Nat.add_comm 1 n)).hom.app (op ⊤)
        (formsSheafWedge k P.compl.obj 1 n (op ⊤) (thetaSection P) a) := by
  have h : (formsSheaf k P.compl.obj 1).obj.map
      (⊤ : P.compl.obj.left.Opens).leTop.op (thetaSection P) = thetaSection P := by
    change (formsSheaf k P.compl.obj 1).obj.map (𝟙 (op ⊤)) (thetaSection P) = _
    exact ConcreteCategory.congr_hom ((formsSheaf k P.compl.obj 1).obj.map_id _) _
  exact (thetaWedgeSheaf_eq_wedge P n ⊤ a).trans (congrArg
    (fun b => (formsSheafCast k P.compl.obj (Nat.add_comm 1 n)).hom.app (op ⊤)
      (formsSheafWedge k P.compl.obj 1 n (op ⊤) b a)) h)

/-- The logarithmic one-form on the complement is closed. -/
theorem thetaSection_d :
    (formsSheafD k P.compl.obj 1).hom.app (op ⊤) (thetaSection P) = 0 := by
  let a : (formsPresheaf k P.compl.obj 1).obj (op ⊤) :=
    ⟨dlog k P.eqnUnit, dlog_mem_exteriorPower_one k _⟩
  have ha : (formsPresheafD k P.compl.obj 1).app (op ⊤) a = 0 :=
    Subtype.ext (d_dlog k (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit))
  exact (formsSheafD_unit k P.compl.obj 1 (op ⊤) a).trans (by rw [ha, map_zero])

/-- Relative forms on the complement, regarded as sheaves on the ambient scheme by ordinary
direct image. No derived direct image is asserted here. -/
@[implicit_reducible] def openFormsSheaf (n : ℕ) :
    TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left :=
  (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).obj
    (formsSheaf k P.compl.obj n)

/-- Relative forms on the divisor, regarded as sheaves on the ambient scheme. -/
@[implicit_reducible] def closedFormsSheaf (n : ℕ) :
    TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left :=
  (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).obj
    (formsSheaf k P.closed.obj n)

/-- The ordinary direct image of the de Rham complex on the open complement. -/
@[implicit_reducible] def openFormsComplexNat :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left) ℕ :=
  ((TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).mapHomologicalComplex
    (.up ℕ)).obj (formsComplexNat k P.compl.obj)

/-- The explicit closed shift: zero in degree zero, divisor forms in degree `n + 1`, and
differential `-d`. -/
@[implicit_reducible] def shiftedClosedComplexNat :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left) ℕ :=
  signedShiftedComplexNat
    (((TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).mapHomologicalComplex
      (.up ℕ)).obj (formsComplexNat k P.closed.obj))

/-- Degree zero of the shifted divisor complex is zero. -/
@[simp] theorem shiftedClosedComplexNat_X_zero : (shiftedClosedComplexNat P).X 0 = 0 := rfl

/-- Degree `n + 1` of the shifted divisor complex is the direct image of divisor `n`-forms. -/
@[simp] theorem shiftedClosedComplexNat_X_succ (n : ℕ) :
    (shiftedClosedComplexNat P).X (n + 1) = closedFormsSheaf P n := rfl

/-- The differential on the shifted divisor complex is the negative of its original
differential. -/
theorem shiftedClosedComplexNat_d (n : ℕ) :
    (shiftedClosedComplexNat P).d (n + 1) (n + 1 + 1) =
      -(TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
        (formsSheafD k P.closed.obj n) := by
  exact (signedShiftedComplexNat_d _ n).trans (by
    rw [Functor.mapHomologicalComplex_obj_d, formsComplexNat_d]
    rfl)

private def shiftedAmbientComplexNat :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left) ℕ :=
  signedShiftedComplexNat (formsComplexNat k P.ambient.obj)

private def thetaToOpen (n : ℕ) :
    (shiftedAmbientComplexNat P).X n ⟶ (openFormsComplexNat P).X n :=
  match n with
  | 0 => 0
  | n + 1 => formsSheafPullback P.j.hom n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
        (thetaWedgeSheaf P.compl.obj P.eqnUnit n)

private theorem thetaToOpen_comm (n : ℕ) :
    thetaToOpen P n ≫ (openFormsComplexNat P).d n (n + 1) =
      (shiftedAmbientComplexNat P).d n (n + 1) ≫ thetaToOpen P (n + 1) := by
  cases n with
  | zero =>
    apply (isZero_zero _).eq_of_src
  | succ n =>
    simp only [thetaToOpen, openFormsComplexNat, Functor.mapHomologicalComplex_obj_d,
      formsComplexNat_d, shiftedAmbientComplexNat, signedShiftedComplexNat_d,
      formsComplexNat_X]
    change (formsSheafPullback P.j.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
          (thetaWedgeSheaf P.compl.obj P.eqnUnit n)) ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
          (formsSheafD k P.compl.obj (n + 1)) = _
    rw [Category.assoc, ← Functor.map_comp, thetaWedgeSheaf_d, Functor.map_neg,
      Functor.map_comp, comp_neg, ← Category.assoc, formsSheafPullback_d]
    change -(formsSheafD k P.ambient.obj n ≫ formsSheafPullback P.j.hom (n + 1)) ≫ _ =
      (-formsSheafD k P.ambient.obj n) ≫ (formsSheafPullback P.j.hom (n + 1) ≫ _)
    simp only [neg_comp, Category.assoc]

private def thetaToOpenComplexNat : shiftedAmbientComplexNat P ⟶ openFormsComplexNat P :=
  CochainComplex.ofHom (thetaToOpen P) (thetaToOpen_comm P)

private def logGeneratorComplexNat :
    formsComplexNat k P.ambient.obj ⊞ shiftedAmbientComplexNat P ⟶ openFormsComplexNat P :=
  biprod.desc (formsComplexNatPullback P.j.hom) (thetaToOpenComplexNat P)

/-- The logarithmic complex is the image of regular forms and their left products with `df/f`
inside the ordinary direct-image complex of forms on the complement.

Blueprint: `thm:geo-log-sheaves`. -/
@[no_expose, implicit_reducible] def logComplexNat :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left) ℕ :=
  image (logGeneratorComplexNat P)

/-- The sheaf of logarithmic `n`-forms, with its canonical embedding in forms on the complement.
Its image construction does not assert a global normal form for sections on arbitrary opens.

Blueprint: `thm:geo-log-sheaves`. -/
@[implicit_reducible] def logSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{u} k) P.ambient.obj.left :=
  (logComplexNat P).X n

/-- Inclusion of logarithmic forms in ordinary forms on the complement, as a map of complexes. -/
@[no_expose] def logToOpenComplexNat : logComplexNat P ⟶ openFormsComplexNat P :=
  image.ι (logGeneratorComplexNat P)

/-- The regular-form inclusion into the logarithmic complex. Its injectivity is proved locally
from smoothness of the pair. -/
@[no_expose] def regularToLogComplexNat :
    formsComplexNat k P.ambient.obj ⟶ logComplexNat P :=
  biprod.inl ≫ factorThruImage (logGeneratorComplexNat P)

/-- The degreewise inclusion in forms on the complement. -/
def logToOpenSheaf (n : ℕ) : logSheaf P n ⟶ openFormsSheaf P n :=
  (logToOpenComplexNat P).f n

/-- The degreewise regular inclusion in logarithmic forms. -/
def regularToLogSheaf (n : ℕ) : formsSheaf k P.ambient.obj n ⟶ logSheaf P n :=
  (regularToLogComplexNat P).f n

/-- The logarithmic differential is the restriction of the ordinary de Rham differential. -/
def logSheafD (n : ℕ) : logSheaf P n ⟶ logSheaf P (n + 1) :=
  (logComplexNat P).d n (n + 1)

/-- The logarithmic differential squares to zero. -/
@[reassoc (attr := simp)] theorem logSheafD_comp (n : ℕ) :
    logSheafD P n ≫ logSheafD P (n + 1) = 0 :=
  (logComplexNat P).d_comp_d n (n + 1) (n + 1 + 1)

/-- Regular inclusion commutes with the differential. -/
@[reassoc] theorem regularToLogSheaf_d (n : ℕ) :
    regularToLogSheaf P n ≫ logSheafD P n =
      formsSheafD k P.ambient.obj n ≫ regularToLogSheaf P (n + 1) := by
  simpa only [regularToLogSheaf, logSheafD, formsComplexNat_d, formsComplexNat_X,
    logSheaf] using
    (regularToLogComplexNat P).comm n (n + 1)

/-- The logarithmic differential commutes with inclusion in ordinary forms. -/
@[reassoc] theorem logSheafD_comp_logToOpenSheaf (n : ℕ) :
    logSheafD P n ≫ logToOpenSheaf P (n + 1) =
      logToOpenSheaf P n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
          (formsSheafD k P.compl.obj n) :=
  by
    simpa only [logSheafD, logToOpenSheaf, openFormsComplexNat,
      Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X,
      formsComplexNat_d, formsComplexNat_X, openFormsSheaf, logSheaf] using
      ((logToOpenComplexNat P).comm n (n + 1)).symm

/-- Regular forms followed by logarithmic inclusion are their original pullback to the open. -/
@[reassoc (attr := simp)] theorem regularToLogSheaf_comp_logToOpenSheaf (n : ℕ) :
    regularToLogSheaf P n ≫ logToOpenSheaf P n = formsSheafPullback P.j.hom n := by
  have h : regularToLogComplexNat P ≫ logToOpenComplexNat P =
      formsComplexNatPullback P.j.hom := by
    dsimp only [regularToLogComplexNat, logToOpenComplexNat]
    rw [Category.assoc, image.fac]
    exact biprod.inl_desc _ _
  exact congrArg (fun f ↦ f.f n) h

/-- The logarithmic inclusion is a monomorphism in every degree. -/
instance logToOpenSheaf_mono (n : ℕ) : Mono (logToOpenSheaf P n) := by
  change Mono ((HomologicalComplex.eval _ _ n).map (image.ι (logGeneratorComplexNat P)))
  infer_instance

/-- In degree zero, regular forms cover the logarithmic sheaf: there is no negative-degree
form contributing a logarithmic summand. -/
instance regularToLogSheaf_zero_epi : Epi (regularToLogSheaf P 0) := by
  let K := formsComplexNat k P.ambient.obj
  let L := shiftedAmbientComplexNat P
  have hL : IsZero (L.X 0) := isZero_zero _
  have : IsIso (biprod.inl : K.X 0 ⟶ K.X 0 ⊞ L.X 0) := by
    refine ⟨⟨biprod.fst, biprod.inl_fst, ?_⟩⟩
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp]
    · exact hL.eq_of_tgt _ _
  have : IsIso ((biprod.inl : K ⟶ K ⊞ L).f 0) := by
    rw [← HomologicalComplex.inl_biprodXIso_inv]
    infer_instance
  have : Epi ((factorThruImage (logGeneratorComplexNat P)).f 0) :=
    (HomologicalComplex.eval _ _ 0).map_epi _
  change Epi ((biprod.inl : K ⟶ K ⊞ L).f 0 ≫
    (factorThruImage (logGeneratorComplexNat P)).f 0)
  infer_instance

/-- Degree-zero logarithmic forms are the image of the ordinary regular-form pullback. -/
def logSheafZeroImageIso : image (formsSheafPullback P.j.hom 0) ≅ logSheaf P 0 :=
  (image.isoStrongEpiMono (regularToLogSheaf P 0) (logToOpenSheaf P 0)
    (regularToLogSheaf_comp_logToOpenSheaf P 0)).symm

/-- The degree-zero image comparison preserves the inclusion in complement forms. -/
@[reassoc (attr := simp)] theorem logSheafZeroImageIso_hom_logToOpenSheaf :
    (logSheafZeroImageIso P).hom ≫ logToOpenSheaf P 0 =
      image.ι (formsSheafPullback P.j.hom 0) :=
  image.isoStrongEpiMono_inv_comp_mono (regularToLogSheaf P 0) (logToOpenSheaf P 0)
    (regularToLogSheaf_comp_logToOpenSheaf P 0)

/-- The regular-plus-left-theta map in positive degrees. Its image is precisely the logarithmic
sheaf, whereas sections of that sheaf need only have such normal forms locally. -/
def logNormalFormSheaf (n : ℕ) :
    formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n ⟶
      openFormsSheaf P (n + 1) :=
  biprod.desc (formsSheafPullback P.j.hom (n + 1))
    (formsSheafPullback P.j.hom n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
        (thetaWedgeSheaf P.compl.obj P.eqnUnit n))

/-- A normal form with no logarithmic term is the pullback of its regular part. -/
@[reassoc (attr := simp)] theorem inl_logNormalFormSheaf (n : ℕ) :
    biprod.inl ≫ logNormalFormSheaf P n = formsSheafPullback P.j.hom (n + 1) :=
  biprod.inl_desc _ _

/-- A normal form with no regular part is left multiplication by the logarithmic form. -/
@[reassoc (attr := simp)] theorem inr_logNormalFormSheaf (n : ℕ) :
    biprod.inr ≫ logNormalFormSheaf P n = formsSheafPullback P.j.hom n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
        (thetaWedgeSheaf P.compl.obj P.eqnUnit n) :=
  biprod.inr_desc _ _

/-- The local normal-form map onto logarithmic forms. Epimorphy is a sheaf assertion, rather than
surjectivity on sections of every open. -/
@[no_expose] def logMkSheaf (n : ℕ) :
    formsSheaf k P.ambient.obj (n + 1) ⊞ formsSheaf k P.ambient.obj n ⟶
      logSheaf P (n + 1) :=
  (HomologicalComplex.biprodXIso (formsComplexNat k P.ambient.obj)
      (shiftedAmbientComplexNat P) (n + 1)).inv ≫
    (factorThruImage (logGeneratorComplexNat P)).f (n + 1)

/-- Normal forms cover the logarithmic sheaf locally. -/
instance logMkSheaf_epi (n : ℕ) : Epi (logMkSheaf P n) := by
  change Epi ((HomologicalComplex.biprodXIso _ _ (n + 1)).inv ≫
    (HomologicalComplex.eval _ _ (n + 1)).map (factorThruImage (logGeneratorComplexNat P)))
  apply (epi_comp_iff_of_epi _ _).2
  exact (HomologicalComplex.eval _ _ (n + 1)).map_epi _

/-- Inclusion of a logarithmic normal form is its defining regular-plus-left-theta formula. -/
@[reassoc (attr := simp)] theorem logMkSheaf_comp_logToOpenSheaf (n : ℕ) :
    logMkSheaf P n ≫ logToOpenSheaf P (n + 1) = logNormalFormSheaf P n := by
  change ((HomologicalComplex.biprodXIso _ _ (n + 1)).inv ≫
    (factorThruImage (logGeneratorComplexNat P)).f (n + 1)) ≫
      (image.ι (logGeneratorComplexNat P)).f (n + 1) = _
  rw [Category.assoc, ← HomologicalComplex.comp_f, image.fac]
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv]
    exact (HomologicalComplex.biprod_inl_desc_f (formsComplexNatPullback P.j.hom)
      (thetaToOpenComplexNat P) (n + 1)).trans (biprod.inl_desc _ _).symm
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv]
    exact (HomologicalComplex.biprod_inr_desc_f (formsComplexNatPullback P.j.hom)
      (thetaToOpenComplexNat P) (n + 1)).trans (biprod.inr_desc _ _).symm

/-- The regular part of a normal form is the original regular inclusion. -/
@[reassoc (attr := simp)] theorem inl_logMkSheaf (n : ℕ) :
    biprod.inl ≫ logMkSheaf P n = regularToLogSheaf P (n + 1) := by
  apply (cancel_mono (logToOpenSheaf P (n + 1))).1
  rw [Category.assoc, logMkSheaf_comp_logToOpenSheaf, inl_logNormalFormSheaf,
    regularToLogSheaf_comp_logToOpenSheaf]

/-- The categorical image of the ordinary normal-form map is the logarithmic sheaf. This
comparison is used when exact associated-module functors identify its affine values. -/
def logSheafImageIso (n : ℕ) : image (logNormalFormSheaf P n) ≅ logSheaf P (n + 1) :=
  (image.isoStrongEpiMono (logMkSheaf P n) (logToOpenSheaf P (n + 1))
    (logMkSheaf_comp_logToOpenSheaf P n)).symm

/-- The image comparison preserves the actual embedding into forms on the complement. -/
@[reassoc (attr := simp)] theorem logSheafImageIso_hom_logToOpenSheaf (n : ℕ) :
    (logSheafImageIso P n).hom ≫ logToOpenSheaf P (n + 1) =
      image.ι (logNormalFormSheaf P n) :=
  by
    exact image.isoStrongEpiMono_inv_comp_mono (logMkSheaf P n)
      (logToOpenSheaf P (n + 1)) (logMkSheaf_comp_logToOpenSheaf P n)

section PairTransport

private theorem formsSheafPullback_congr {X Y : Over (Spec (CommRingCat.of k))} (f g : X ⟶ Y)
    (h : f = g) (n : ℕ) :
    formsSheafPullback f n ≫ eqToHom (congrArg
      (fun t : X ⟶ Y => (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
        (formsSheaf k X n)) h) = formsSheafPullback g n := by
  subst g
  simp only [eqToHom_refl, Category.comp_id]

variable {P Q : Geometric.DivisorPair D}
/-- The complement square of a morphism of pairs identifies the two composite direct-image
functors on sheaves of base-linear modules. -/
def pairOpenPushforwardIso (F : P ⟶ Q) :
    TopCat.Sheaf.pushforward (ModuleCat k) F.compl.hom.left.base ⋙
        TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base ≅
      TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base ⋙
        TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base := by
  apply eqToIso
  exact congrArg (TopCat.Sheaf.pushforward (ModuleCat k))
    (congrArg (fun f => f.hom.left.base) F.j_comp).symm

/-- Pullback of complement forms along a transverse map of geometric pairs, as a map on the
ambient schemes. The square of open immersions supplies the target comparison. -/
@[no_expose] def openFormsPullback (F : P ⟶ Q) (n : ℕ) :
    openFormsSheaf Q n ⟶
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).obj (openFormsSheaf P n) :=
  (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
    (formsSheafPullback F.compl.hom n) ≫
      (pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)

/-- Complement-form pullback is ordinary pullback on the complement, transported through the
commutative square of open immersions. -/
lemma openFormsPullback_eq (F : P ⟶ Q) (n : ℕ) :
    openFormsPullback F n =
      (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
        (formsSheafPullback F.compl.hom n) ≫
          (pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n) := by
  rfl

/-- Regular-form pullback commutes with the complement square of a morphism of pairs. -/
@[reassoc] theorem regularPullback_openFormsPullback (F : P ⟶ Q) (n : ℕ) :
    formsSheafPullback Q.j.hom n ≫ openFormsPullback F n =
      formsSheafPullback F.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (formsSheafPullback P.j.hom n) := by
  dsimp only [openFormsPullback]
  rw [← Category.assoc, ← formsSheafPullback_comp]
  have h : F.compl.hom ≫ Q.j.hom = P.j.hom ≫ F.ambient.hom :=
    (congrArg (fun f => f.hom) F.j_comp).symm
  have hc : (pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n) =
      eqToHom (congrArg
        (fun t : P.compl.obj ⟶ Q.ambient.obj =>
          (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
            (formsSheaf k P.compl.obj n)) h) := by
    dsimp only [pairOpenPushforwardIso, eqToIso]
    exact eqToHom_app _ _
  rw [hc]
  exact (formsSheafPullback_congr _ _ h n).trans
    (formsSheafPullback_comp P.j.hom F.ambient.hom n)

private def pairComplOverFunctor (D : SmoothDomain k) :
    Geometric.DivisorPair D ⥤ Over (Spec (CommRingCat.of k)) where
  obj P := P.compl.obj
  map F := F.compl.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Left multiplication by `df/f` on complement forms, as a map on the ambient scheme. -/
def openThetaWedgeSheaf (P : Geometric.DivisorPair D) (n : ℕ) :
    openFormsSheaf P n ⟶ openFormsSheaf P (n + 1) :=
  (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n)

/-- Complement-form pullback commutes with multiplication by the logarithmic form when it
preserves the specified equation unit exactly. -/
@[reassoc] theorem openThetaWedgeSheaf_pullback (F : P ⟶ Q)
    (hunit : Units.map (sectionPullbackTop F.compl.hom).toMonoidHom Q.eqnUnit = P.eqnUnit)
    (n : ℕ) :
    openThetaWedgeSheaf Q n ≫ openFormsPullback F (n + 1) =
      openFormsPullback F n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (openThetaWedgeSheaf P n) := by
  have hθ := thetaWedgeSheaf_pullback F.compl.hom
    (show (sectionAlgebra k Q.compl.obj ⊤)ˣ from Q.eqnUnit) n
  rw [hunit] at hθ
  dsimp only [openThetaWedgeSheaf, openFormsPullback]
  rw [← Category.assoc, ← Functor.map_comp, hθ, Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg
    (fun f ↦ (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
      (formsSheafPullback F.compl.hom n) ≫ f)
    ((pairOpenPushforwardIso F).hom.naturality
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n))

/-- An isomorphism of pairs identifies complement forms on the ambient scheme with the direct
image of the corresponding complement forms. -/
@[no_expose] def pairOpenFormsIso (e : P ≅ Q) (n : ℕ) :
    openFormsSheaf P n ≅
      (TopCat.Sheaf.pushforward (ModuleCat k) e.inv.ambient.hom.left.base).obj
        (openFormsSheaf Q n) := by
  have : IsIso e.inv.compl.hom := (pairComplOverFunctor D).map_isIso e.inv
  have : IsIso (openFormsPullback e.inv n) := by
    dsimp only [openFormsPullback]
    infer_instance
  exact asIso (openFormsPullback e.inv n)

/-- On global sections, transport of complement forms is the usual pullback along the
complement component of the inverse pair isomorphism. -/
lemma pairOpenFormsIso_hom_appTop (e : P ≅ Q) (n : ℕ)
    (x : (formsSheaf k P.compl.obj n).obj.obj (op ⊤)) :
    dsimp% (pairOpenFormsIso e n).hom.hom.app (op ⊤) x =
      formsSheafPullbackTop e.inv.compl.hom n x := by
  change (openFormsPullback e.inv n).hom.app (op ⊤) x = _
  dsimp only [openFormsPullback]
  let E := sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left)
    (ModuleCat.{u} k) ⋙ (evaluation _ _).obj (op ⊤)
  have he : e.inv.compl.hom ≫ P.j.hom = Q.j.hom ≫ e.inv.ambient.hom :=
    (congrArg (fun f => f.hom) e.inv.j_comp).symm
  have hc : (pairOpenPushforwardIso e.inv).hom.app (formsSheaf k Q.compl.obj n) =
      eqToHom (congrArg
        (fun t : Q.compl.obj ⟶ P.ambient.obj =>
          (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
            (formsSheaf k Q.compl.obj n)) he) := by
    dsimp only [pairOpenPushforwardIso, eqToIso]
    exact eqToHom_app _ _
  have h : E.map ((pairOpenPushforwardIso e.inv).hom.app (formsSheaf k Q.compl.obj n)) =
      𝟙 ((formsSheaf k Q.compl.obj n).obj.obj (op ⊤)) := by
    rw [hc]
    exact (eqToHom_map E _).trans (by rfl)
  exact ConcreteCategory.congr_hom h (formsSheafPullbackTop e.inv.compl.hom n x)

/-- The global complement-form map of a pair isomorphism, with the section carriers explicit. -/
def pairOpenFormsPullbackTop (e : P ≅ Q) (n : ℕ) :
    (formsSheaf k P.compl.obj n).obj.obj (op ⊤) →ₗ[k]
      (formsSheaf k Q.compl.obj n).obj.obj (op ⊤) :=
  ((pairOpenFormsIso e n).hom.hom.app (op ⊤)).hom

/-- The typed global complement-form map is ordinary pullback on the complement. -/
lemma pairOpenFormsPullbackTop_eq (e : P ≅ Q) (n : ℕ) :
    pairOpenFormsPullbackTop e n = formsSheafPullbackTop e.inv.compl.hom n := by
  ext x
  exact pairOpenFormsIso_hom_appTop e n x

/-- The complement-forms comparison commutes with regular-form restriction. -/
@[reassoc] theorem pairOpenFormsIso_regular (e : P ≅ Q) (n : ℕ) :
    formsSheafPullback e.inv.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) e.inv.ambient.hom.left.base).map
          (formsSheafPullback Q.j.hom n) =
      formsSheafPullback P.j.hom n ≫ (pairOpenFormsIso e n).hom :=
  (regularPullback_openFormsPullback e.inv n).symm

/-- The complement-forms comparison preserves the left logarithmic product for an exact
equation-unit comparison. -/
@[reassoc] theorem pairOpenFormsIso_theta (e : P ≅ Q)
    (hunit : Units.map (sectionPullbackTop e.inv.compl.hom).toMonoidHom P.eqnUnit = Q.eqnUnit)
    (n : ℕ) :
    openThetaWedgeSheaf P n ≫ (pairOpenFormsIso e (n + 1)).hom =
      (pairOpenFormsIso e n).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) e.inv.ambient.hom.left.base).map
          (openThetaWedgeSheaf Q n) :=
  openThetaWedgeSheaf_pullback e.inv hunit n

end PairTransport

end OrlikSolomon.Geometric.DeRham
