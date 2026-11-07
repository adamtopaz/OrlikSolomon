/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.AffineDuality

/-!
# Functions and units as maps to the affine line and the multiplicative group

For every scheme `X` over `S = Spec k`, affine or not, global sections of `𝒪_X` are the
`S`-morphisms `X → 𝔸¹_S`, and global units are the `S`-morphisms `X → 𝔾ₘ`. The second statement is
`thm:geo-units` of the geometric refactor blueprint; the first is the map `X → 𝔸¹` attached to a
global function, used in its proof of `thm:geo-log-laws`.

## Main definitions

* `Geometric.affineLineCoord k`: the coordinate `z` on `𝔸¹_S`.
* `Geometric.homAffineLineEquiv X`: `(X ⟶ 𝔸¹_S) ≃ Γ(X, 𝒪_X)`, `f ↦ f^* z`.
* `Geometric.gmCoord k`: the coordinate `z`, a unit on `𝔾ₘ`.
* `Geometric.unitsEquivHomGm X`: `Γ(X, 𝒪_X)ˣ ≃* (X ⟶ 𝔾ₘ)`, `u ↦ û`, an isomorphism of groups for
  the group structure of `X ⟶ 𝔾ₘ` given by the group object `𝔾ₘ`. Its inverse is `f ↦ f^* z`.
* `Geometric.specUnit u`: a unit of a `k`-algebra `A`, as a global unit on `Spec A`.

## Main results

* `unitsEquivHomGm_comp`: naturality, `\widehat{g^* u} = û ∘ g`.
* `lift_unitsEquivHomGm_comp_mul`, `unitsEquivHomGm_comp_inv`, `toUnit_comp_one`: under
  `unitsEquivHomGm`, multiplication, inverse and the unit `1` correspond to the multiplication,
  inverse and identity of the group scheme `𝔾ₘ`.

No affineness, smoothness or rational point of `X` is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
  MonObj GrpObj
open scoped Polynomial LaurentPolynomial MonObj TensorProduct

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### The affine line -/

variable (k) in
/-- The coordinate `z` of `𝔸¹_S = Spec k[z]`, as a global function. -/
def affineLineCoord : Γ((affineLine k).left, ⊤) :=
  (Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X : k[X])

/-- For any `S`-scheme `X`, the `S`-morphisms `X ⟶ 𝔸¹_S` correspond to global functions on `X`,
by pullback of the coordinate. -/
def homAffineLineEquiv (X : Over (Spec (.of k))) : (X ⟶ affineLine k) ≃ Γ(X.left, ⊤) where
  toFun f := f.left.appTop (affineLineCoord k)
  invFun s := (specHomEquiv X (CommAlgCat.of k k[X])).symm
    (ConcreteCategory.ofHom (C := CommAlgCat k) (X := CommAlgCat.of k k[X])
      (Y := globalSections X) (Polynomial.aeval (R := k) (A := globalSections X) s))
  left_inv f := by
    rw [Equiv.symm_apply_eq]
    ext1
    exact Polynomial.algHom_ext ((Polynomial.aeval_X _).trans rfl)
  right_inv s := by
    change specHomEquiv X (CommAlgCat.of k k[X]) ((specHomEquiv X _).symm _)
      (Polynomial.X : k[X]) = s
    rw [Equiv.apply_symm_apply]
    exact Polynomial.aeval_X _

variable {X X' : Over (Spec (.of k))}

@[simp] lemma homAffineLineEquiv_apply (f : X ⟶ affineLine k) :
    homAffineLineEquiv X f = f.left.appTop (affineLineCoord k) := rfl

/-- Naturality of `homAffineLineEquiv`: the map of a pulled-back function is the composite. -/
lemma homAffineLineEquiv_comp (g : X' ⟶ X) (f : X ⟶ affineLine k) :
    homAffineLineEquiv X' (g ≫ f) = g.left.appTop (homAffineLineEquiv X f) := rfl

lemma homAffineLineEquiv_symm_comp (g : X' ⟶ X) (s : Γ(X.left, ⊤)) :
    (homAffineLineEquiv X').symm (g.left.appTop s) = g ≫ (homAffineLineEquiv X).symm s := by
  rw [Equiv.symm_apply_eq, homAffineLineEquiv_comp, Equiv.apply_symm_apply]

/-! ### The multiplicative group -/

variable (k) in
/-- The coordinate `z` of `𝔾ₘ = Spec k[z, z⁻¹]`, as a global unit. -/
def gmCoord : Γ((gm k).left, ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (.of k[T;T⁻¹])).inv.hom.toMonoidHom :
    k[T;T⁻¹] →* Γ((gm k).left, ⊤)) (laurentPolynomialT (R := k))

lemma coe_gmCoord :
    (gmCoord k : Γ((gm k).left, ⊤)) =
      (Scheme.ΓSpecIso (.of k[T;T⁻¹])).inv (LaurentPolynomial.T 1 : k[T;T⁻¹]) := rfl

/-- The `S`-morphisms `X ⟶ 𝔾ₘ` correspond to global units on `X`, by pullback of the coordinate.
This is the inverse of `unitsEquivHomGm`. -/
def homGmEquiv (X : Over (Spec (.of k))) : (X ⟶ gm k) ≃ Γ(X.left, ⊤)ˣ where
  toFun f := Units.map f.left.appTop.hom (gmCoord k)
  invFun u := (specHomEquiv X (CommAlgCat.of k k[T;T⁻¹])).symm
    (ConcreteCategory.ofHom (C := CommAlgCat k) (X := CommAlgCat.of k k[T;T⁻¹])
      (Y := globalSections X)
      (laurentPolynomialLift (k := k) (R := k) (Algebra.ofId k (globalSections X)) u))
  left_inv f := by
    rw [Equiv.symm_apply_eq]
    ext1
    refine laurentPolynomial_algHom_ext (fun a ↦ ?_) ?_
    · rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
    · exact (laurentPolynomialLift_T (k := k) (R := k) (S := globalSections X) _ _).trans rfl
  right_inv u := by
    ext
    change specHomEquiv X (CommAlgCat.of k k[T;T⁻¹]) ((specHomEquiv X _).symm _)
      (LaurentPolynomial.T 1 : k[T;T⁻¹]) = (u : Γ(X.left, ⊤))
    rw [Equiv.apply_symm_apply]
    exact laurentPolynomialLift_T (k := k) (R := k) _ _

@[simp] lemma coe_homGmEquiv_apply (f : X ⟶ gm k) :
    (homGmEquiv X f : Γ(X.left, ⊤)) = f.left.appTop (gmCoord k) := rfl

/-- Naturality of `homGmEquiv`. -/
lemma homGmEquiv_comp (g : X' ⟶ X) (f : X ⟶ gm k) :
    homGmEquiv X' (g ≫ f) = Units.map g.left.appTop.hom (homGmEquiv X f) := rfl

/-- On `Spec (S ⊗[R] T) ≅ Spec S ×_{Spec R} Spec T`, the function `s ⊗ t` is the product of the
pullbacks of `s` and `t` along the two projections. -/
lemma pullbackSpecIso_hom_appTop_tmul {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (s : S) (t : T) :
    (pullbackSpecIso R S T).hom.appTop ((Scheme.ΓSpecIso (.of (S ⊗[R] T))).inv (s ⊗ₜ t)) =
      Scheme.Hom.appTop (pullback.fst _ _) ((Scheme.ΓSpecIso (.of S)).inv s) *
        Scheme.Hom.appTop (pullback.snd _ _) ((Scheme.ΓSpecIso (.of T)).inv t) := by
  have h : s ⊗ₜ[R] t = Algebra.TensorProduct.includeLeftRingHom s *
      (Algebra.TensorProduct.includeRight (R := R) (A := S) t) := by
    simp
  rw [h, map_mul, map_mul, ← pullbackSpecIso_hom_fst, ← pullbackSpecIso_hom_snd,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply]
  congr 2
  · exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := T)))) s
  · exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom)) t

/-- The multiplication of `𝔾ₘ` pulls the coordinate back to the product of the two coordinates,
since the comultiplication of `k[z, z⁻¹]` sends `z` to `z ⊗ z`. -/
lemma mul_appTop_gmCoord :
    μ[gm k].left.appTop (gmCoord k) =
      (fst (gm k) (gm k)).left.appTop (gmCoord k) *
        (snd (gm k) (gm k)).left.appTop (gmCoord k) := by
  have hμ : μ[gm k].left = (pullbackSpecIso k k[T;T⁻¹] k[T;T⁻¹]).hom ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k k[T;T⁻¹]).toRingHom) :=
    mul_spec_asOver_spec_left (R := .of k) (A := .of k[T;T⁻¹])
  rw [hμ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coe_gmCoord,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, CommRingCat.ofHom_apply]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Bialgebra.comulAlgHom_apply,
    LaurentPolynomial.comul_T]
  exact pullbackSpecIso_hom_appTop_tmul _ _

/-- Pullback of the coordinate turns the multiplication of `X ⟶ 𝔾ₘ` into multiplication of
units. -/
lemma homGmEquiv_mul (f g : X ⟶ gm k) : homGmEquiv X (f * g) = homGmEquiv X f * homGmEquiv X g := by
  ext
  rw [Hom.mul_def, coe_homGmEquiv_apply, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, mul_appTop_gmCoord, map_mul, Units.val_mul, coe_homGmEquiv_apply,
    coe_homGmEquiv_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Over.comp_left, ← Over.comp_left,
    lift_fst, lift_snd]

/-- Global units on any `S`-scheme `X` are the `S`-morphisms `X ⟶ 𝔾ₘ`, as groups: `u ↦ û`, where
`û` is the unique `S`-morphism pulling back the coordinate `z` to `u`. The group structure on
`X ⟶ 𝔾ₘ` is that of the group object `𝔾ₘ`.

Blueprint: `thm:geo-units`. -/
def unitsEquivHomGm (X : Over (Spec (.of k))) : Γ(X.left, ⊤)ˣ ≃* (X ⟶ gm k) :=
  MulEquiv.symm
    { homGmEquiv X with
      map_mul' := homGmEquiv_mul }

@[simp] lemma unitsEquivHomGm_symm_apply (f : X ⟶ gm k) :
    (unitsEquivHomGm X).symm f = homGmEquiv X f := rfl

/-- The map `û` pulls back the coordinate of `𝔾ₘ` to `u`. -/
@[simp] lemma unitsEquivHomGm_appTop_gmCoord (u : Γ(X.left, ⊤)ˣ) :
    (unitsEquivHomGm X u).left.appTop (gmCoord k) = u :=
  congrArg Units.val ((homGmEquiv X).apply_symm_apply u)

/-- Two `S`-morphisms to `𝔾ₘ` agree when they pull back the coordinate to the same unit. -/
lemma hom_ext_gm {f g : X ⟶ gm k}
    (h : f.left.appTop (gmCoord k) = g.left.appTop (gmCoord k)) : f = g :=
  (homGmEquiv X).injective (Units.ext h)

/-- Naturality: `\widehat{g^* u} = û ∘ g`.

Blueprint: `thm:geo-units`. -/
lemma unitsEquivHomGm_comp (g : X' ⟶ X) (u : Γ(X.left, ⊤)ˣ) :
    unitsEquivHomGm X' (Units.map g.left.appTop.hom u) = g ≫ unitsEquivHomGm X u := by
  apply hom_ext_gm
  rw [unitsEquivHomGm_appTop_gmCoord, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, unitsEquivHomGm_appTop_gmCoord]
  rfl

/-- The product of units corresponds to the multiplication of `𝔾ₘ`.

Blueprint: `thm:geo-units`. -/
lemma lift_unitsEquivHomGm_comp_mul (u v : Γ(X.left, ⊤)ˣ) :
    lift (unitsEquivHomGm X u) (unitsEquivHomGm X v) ≫ μ[gm k] = unitsEquivHomGm X (u * v) := by
  rw [map_mul, Hom.mul_def]

/-- The inverse of a unit corresponds to the inverse of `𝔾ₘ`.

Blueprint: `thm:geo-units`. -/
lemma unitsEquivHomGm_comp_inv (u : Γ(X.left, ⊤)ˣ) :
    unitsEquivHomGm X u ≫ ι[gm k] = unitsEquivHomGm X u⁻¹ := by
  rw [map_inv, Hom.inv_def]

/-- The unit `1` corresponds to the identity of `𝔾ₘ`.

Blueprint: `thm:geo-units`. -/
lemma toUnit_comp_one : toUnit X ≫ η[gm k] = unitsEquivHomGm X 1 := by
  rw [map_one, Hom.one_def]

/-! ### Units of spectra -/

/-- A unit `u` of a `k`-algebra `A`, as a global unit on `Spec A`. -/
abbrev specUnit {A : CommAlgCat.{u} k} (u : Aˣ) : Γ((spec A).left, ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom : A →* Γ((spec A).left, ⊤)) u

lemma coe_specUnit {A : CommAlgCat.{u} k} (u : Aˣ) :
    (specUnit u : Γ((spec A).left, ⊤)) = (Scheme.ΓSpecIso (.of A)).inv u :=
  rfl

/-- Pulling back a unit along `Spec φ` gives the unit of its image. -/
lemma map_specMap_specUnit {A B : CommAlgCat.{u} k} (φ : A ⟶ B) (u : Aˣ) :
    Units.map (specMap φ).left.appTop.hom (specUnit u) = specUnit (Units.map (φ.hom : A →* B) u) :=
  Units.ext (specMap_left_appTop_ΓSpecIso_inv φ u)

end OrlikSolomon.Geometric
