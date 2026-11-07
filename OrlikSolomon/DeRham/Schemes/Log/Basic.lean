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
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Logarithmic forms on schemes

For a principal smooth divisor pair, the logarithmic sheaves are the images of regular forms
and their products on the left with `θ = df / f` inside the ordinary direct image of forms on
the complement. The differential is base-linear, and the closed shift has differential `-d`.

## Main definitions and results

* `thetaSection`: the global logarithmic form on the complement.
* `thetaWedgeSheaf`: left exterior multiplication by the logarithmic form of a global unit.

The constructions use a commutative base ring. No characteristic-zero hypothesis, global
localization assertion for a non-affine scheme, or rational point is needed.

Blueprint: `thm:geo-log-sheaves`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

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

end Unit

variable {D : SmoothDomain k} (P : Geometric.DivisorPair D)

/-- The global one-form `θ = df / f` on the open complement of a principal smooth divisor pair.

Blueprint: `thm:geo-log-sheaves`. -/
def thetaSection : (formsSheaf k P.compl.obj 1).obj.obj (op ⊤) :=
  (formsSheafUnit k P.compl.obj 1).app (op ⊤)
    ⟨dlog k P.eqnUnit, dlog_mem_exteriorPower_one k _⟩

/-- The logarithmic one-form on the complement is closed. -/
theorem thetaSection_d :
    (formsSheafD k P.compl.obj 1).hom.app (op ⊤) (thetaSection P) = 0 := by
  let a : (formsPresheaf k P.compl.obj 1).obj (op ⊤) :=
    ⟨dlog k P.eqnUnit, dlog_mem_exteriorPower_one k _⟩
  have ha : (formsPresheafD k P.compl.obj 1).app (op ⊤) a = 0 :=
    Subtype.ext (d_dlog k (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit))
  exact (formsSheafD_unit k P.compl.obj 1 (op ⊤) a).trans (by rw [ha, map_zero])

end OrlikSolomon.Geometric.DeRham
