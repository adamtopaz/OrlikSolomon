/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Over
public import OrlikSolomon.DeRham.Localization
/-!
# Presheaves of relative differential forms

For a scheme over `Spec k`, functions on each open carry their canonical `k`-algebra structure.
Applying the existing algebraic forms functor in each exterior degree gives a presheaf of
`k`-modules. The algebraic differential is natural under restriction and squares to zero.

## Main definitions and results

* `sectionAlgebraPresheaf`: the presheaf of functions as commutative `k`-algebras.
* `formsPresheaf`: relative forms in a specified nonnegative exterior degree.
* `formsPresheafD` and `formsPresheafD_comp`: the differential and its square-zero identity.

The base ring is arbitrary, and the scheme need not be affine, smooth, separated or nonempty.
The differential is `k`-linear; it is not asserted to be linear over the structure sheaf.

Blueprint: the presheaf construction in `def:geo-forms-sheaf`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace OrlikSolomon.Geometric.DeRham
variable (k : Type u) [CommRing k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Functions on an open, with the scalar structure induced by the map to `Spec k`. -/
def sectionAlgebra (U : X.left.Opens) : CommAlgCat k := by
  letI : Algebra k Γ(X.left, U) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      X.hom.appTop ≫ X.left.presheaf.map U.leTop.op).hom).toAlgebra
  exact CommAlgCat.of k Γ(X.left, U)

/-- Restriction of functions is a homomorphism of `k`-algebras. -/
def sectionRestriction {U V : X.left.Opens} (i : U ⟶ V) :
    sectionAlgebra k X V →ₐ[k] sectionAlgebra k X U where
  toRingHom := (X.left.presheaf.map i.op).hom
  commutes' r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.map V.leTop.op ≫ X.left.presheaf.map i.op) r =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
        X.left.presheaf.map U.leTop.op) r
    rw [← X.left.presheaf.map_comp]
    rfl

@[simp] theorem sectionRestriction_id (U : X.left.Opens) :
    sectionRestriction k X (𝟙 U) = AlgHom.id k (sectionAlgebra k X U) := by
  ext x
  exact ConcreteCategory.congr_hom (X.left.presheaf.map_id (op U)) x

theorem sectionRestriction_comp {U V W : X.left.Opens} (i : U ⟶ V) (j : V ⟶ W) :
    sectionRestriction k X (i ≫ j) =
      (sectionRestriction k X i).comp (sectionRestriction k X j) := by
  ext x
  exact ConcreteCategory.congr_hom (X.left.presheaf.map_comp j.op i.op) x

/-- The structure presheaf, with its canonical base-ring action on every open. -/
def sectionAlgebraPresheaf : X.left.Opensᵒᵖ ⥤ CommAlgCat k where
  obj U := sectionAlgebra k X U.unop
  map {U V} i := ConcreteCategory.ofHom (C := CommAlgCat k)
    (X := sectionAlgebra k X U.unop) (Y := sectionAlgebra k X V.unop)
    (sectionRestriction k X i.unop)
  map_id U := by apply CommAlgCat.hom_ext; exact sectionRestriction_id k X U.unop
  map_comp i j := by
    apply CommAlgCat.hom_ext
    exact sectionRestriction_comp k X j.unop i.unop

open OrlikSolomon.DeRham
open scoped TensorProduct

/-- The presheaf of relative forms in exterior degree `n`. -/
def formsPresheaf (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat k where
  obj U := ModuleCat.of k (⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k])
  map i := ModuleCat.ofHom (Forms.mapPower (sectionRestriction k X i.unop) n)
  map_id U := by
    apply ModuleCat.hom_ext
    change Forms.mapPower (sectionRestriction k X (𝟙 U).unop) n = LinearMap.id
    rw [unop_id, sectionRestriction_id, Forms.mapPower_id]
  map_comp i j := by
    apply ModuleCat.hom_ext
    change Forms.mapPower (sectionRestriction k X (i ≫ j).unop) n =
      Forms.mapPower (sectionRestriction k X j.unop) n ∘ₗ
        Forms.mapPower (sectionRestriction k X i.unop) n
    rw [unop_comp, sectionRestriction_comp, Forms.mapPower_comp]

/-- The algebraic differential, natural under restriction of opens. -/
def formsPresheafD (n : ℕ) : formsPresheaf k X n ⟶ formsPresheaf k X (n + 1) where
  app U := ModuleCat.ofHom (powerD k (sectionAlgebra k X U.unop) n)
  naturality U V i := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => (Forms.mapPower_powerD (sectionRestriction k X i.unop) n x).symm

/-- The presheaf differential squares to zero, including on the empty scheme. -/
theorem formsPresheafD_comp (n : ℕ) : formsPresheafD k X n ≫ formsPresheafD k X (n + 1) = 0 := by
  ext U x
  exact powerD_powerD k n x
end OrlikSolomon.Geometric.DeRham
