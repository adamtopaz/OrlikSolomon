/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
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
* `formsPresheafMul`, `formsPresheafOne`: natural wedge multiplication and its degree-zero unit.
* `formsPresheafZeroIso`: functions are precisely the forms of degree zero.

The base ring is arbitrary, and the scheme need not be affine, smooth, separated or nonempty.
The differential is `k`-linear; it is not asserted to be linear over the structure sheaf.

Blueprint: the presheaf construction in `def:geo-forms-sheaf`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
universe u
namespace OrlikSolomon.Geometric.DeRham
variable (k : Type u) [CommRing k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Functions on an open, with the scalar structure induced by the map to `Spec k`. -/
@[implicit_reducible] def sectionAlgebra (U : X.left.Opens) : CommAlgCat k := by
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

/-- The structure presheaf viewed as modules over the base ring. -/
@[implicit_reducible] def functionsPresheaf : X.left.Opensᵒᵖ ⥤ ModuleCat k where
  obj U := ModuleCat.of k (sectionAlgebra k X U.unop)
  map i := ModuleCat.ofHom (sectionRestriction k X i.unop).toLinearMap
  map_id U := by ext a; exact congrArg (fun f ↦ f a) (sectionRestriction_id k X U.unop)
  map_comp i j := by
    ext a
    exact congrArg (fun f ↦ f a) (sectionRestriction_comp k X j.unop i.unop)

/-- Functions are precisely exterior forms of degree zero. -/
def formsPresheafZero : functionsPresheaf k X ⟶ formsPresheaf k X 0 where
  app U := ModuleCat.ofHom (show sectionAlgebra k X U.unop →ₗ[k]
      ⋀[sectionAlgebra k X U.unop]^0 Ω[sectionAlgebra k X U.unop⁄k] from
    { toFun a := ⟨algebraMap (sectionAlgebra k X U.unop) _ a,
        algebraMap_mem_exteriorPower_zero k a⟩
      map_add' a b := Subtype.ext (map_add _ a b)
      map_smul' r a := Subtype.ext
        ((IsScalarTower.toAlgHom k (sectionAlgebra k X U.unop)
          (Forms k (sectionAlgebra k X U.unop))).toLinearMap.map_smul r a) })
  naturality U V i := by
    ext a
    apply Subtype.ext
    exact (Forms.map_algebraMap (sectionRestriction k X i.unop) a).symm

/-- The degree-zero presheaf of forms is the structure presheaf, with its base-ring action. -/
def formsPresheafZeroIso : functionsPresheaf k X ≅ formsPresheaf k X 0 := by
  refine NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective ((formsPresheafZero k X).app U).hom (by
      constructor
      · intro a b h
        exact (ExteriorAlgebra.algebraMap_leftInverse
          (R := sectionAlgebra k X U.unop) Ω[sectionAlgebra k X U.unop⁄k]).injective
            (congrArg Subtype.val h)
      · intro x
        obtain ⟨a, ha⟩ := (mem_exteriorPower_zero_iff k).1 x.2
        exact ⟨a, Subtype.ext ha⟩))) ?_
  intro U V f
  exact (formsPresheafZero k X).naturality f

@[simp] theorem formsPresheafZeroIso_hom :
    (formsPresheafZeroIso k X).hom = formsPresheafZero k X := rfl

/-- Wedge multiplication, as a natural bilinear map on the presheaves of forms. -/
def formsPresheafMul (p q : ℕ) :
    formsPresheaf k X p ⊗ formsPresheaf k X q ⟶ formsPresheaf k X (p + q) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun (a : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k])
        (b : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k]) ↦
      ⟨(a : Forms k (sectionAlgebra k X U.unop)) * b,
      SetLike.mul_mem_graded a.2 b.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _))
    (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))
  naturality U V i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    apply Subtype.ext
    let a' : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k] := a
    let b' : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k] := b
    exact ((Forms.map (sectionRestriction k X i.unop)).map_mul a'.val b'.val).symm

/-- On elementary tensors the natural product is the existing exterior product. -/
@[simp] theorem formsPresheafMul_tmul (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (a : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k])
    (b : ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k]) :
    (formsPresheafMul k X p q).app U (a ⊗ₜ[k] b) =
      ⟨(a : Forms k (sectionAlgebra k X U.unop)) * b, SetLike.mul_mem_graded a.2 b.2⟩ := rfl

/-- The degree-zero unit of the presheaf exterior algebra. -/
def formsPresheafOne : 𝟙_ (X.left.Opensᵒᵖ ⥤ ModuleCat k) ⟶ formsPresheaf k X 0 where
  app U := ModuleCat.ofHom (show k →ₗ[k]
      ⋀[sectionAlgebra k X U.unop]^0 Ω[sectionAlgebra k X U.unop⁄k] from
    (LinearMap.id : k →ₗ[k] k).smulRight ⟨1, SetLike.one_mem_graded _⟩)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    let c : k := r
    apply Subtype.ext
    change c • (1 : Forms k (sectionAlgebra k X V.unop)) =
      Forms.map (sectionRestriction k X i.unop) (c • 1)
    simp

/-- The presheaf unit sends the scalar one to the exterior unit. -/
@[simp] theorem formsPresheafOne_one (U : X.left.Opensᵒᵖ) :
    (formsPresheafOne k X).app U (1 : k) =
      (⟨1, SetLike.one_mem_graded _⟩ : ⋀[sectionAlgebra k X U.unop]^0
        Ω[sectionAlgebra k X U.unop⁄k]) := by
  change (1 : k) • (⟨1, SetLike.one_mem_graded _⟩ :
    ⋀[sectionAlgebra k X U.unop]^0 Ω[sectionAlgebra k X U.unop⁄k]) = _
  exact one_smul _ _

/-- Change the displayed exterior degree along an equality of indices. -/
def formsPresheafCast {p q : ℕ} (h : p = q) :
    formsPresheaf k X p ⟶ formsPresheaf k X q :=
  eqToHom (congrArg (formsPresheaf k X) h)

/-- Changing the displayed degree does not change the underlying total form. -/
@[simp] theorem formsPresheafCast_val {p q : ℕ} (h : p = q) (U : X.left.Opensᵒᵖ)
    (a : ⋀[sectionAlgebra k X U.unop]^p Ω[sectionAlgebra k X U.unop⁄k]) :
    ((formsPresheafCast k X h).app U a :
      ⋀[sectionAlgebra k X U.unop]^q Ω[sectionAlgebra k X U.unop⁄k]).val = a.val := by
  subst q
  rfl

end OrlikSolomon.Geometric.DeRham
