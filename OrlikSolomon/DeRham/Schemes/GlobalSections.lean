/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Homology.Additive
public import OrlikSolomon.DeRham.Schemes.Forms
public import OrlikSolomon.Geometry.Schemes.Basic

/-!
# Global sections of relative forms

This file connects the sheaves of relative forms of `DeRham/Schemes/Forms` with the bundled global
sections `globalSections X` of the scheme layer. It provides the two pieces on which the de Rham
cohomology of affine schemes and the global logarithmic comparison are built.

* The functions `sectionAlgebra k X ⊤` on the top open, used by the sheaves of forms, and the
  global sections `globalSections X` of the scheme layer have the same carrier `Γ(X, 𝒪_X)`, but
  their structure maps `k → Γ(X, 𝒪_X)` agree only up to `Functor.map_id`.
  `globalSectionsAlgEquiv X` is the identity between them, and it intertwines the two pullbacks of
  global functions by `rfl`.
* `globalFormsComplex k X` is the complex `Γ(X, Ω^•_{X/k})` of global sections of the relative de
  Rham complex of sheaves, for every scheme over `Spec k`.
* For affine `X`, `globalFormsEquiv X n` identifies the forms of degree `n` of the algebra
  `globalSections X` with the global sheaf forms of degree `n`, compatibly with the differential,
  wedge products and pullback, and `complexIsoGlobalFormsComplex X` is the resulting isomorphism of
  complexes with the de Rham complex of `globalSections X`.

The base ring is any commutative ring. Only the comparisons in the last item need affineness.

## Main definitions

* `globalSectionsAlgEquiv X : globalSections X ≃ₐ[k] sectionAlgebra k X ⊤`.
* `globalFormsComplex k X : CochainComplex (ModuleCat k) ℕ`.
* `globalFormsEquiv X n`, `complexIsoGlobalFormsComplex X`, for affine `X`.

## Blueprint

The global sections in `def:geo-dr-cohomology`, from `thm:geo-forms-comparison`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k]

/-! ### The two presentations of global sections -/

section GlobalSections

variable (X : Over (Spec (CommRingCat.of k))) {Y Z : Over (Spec (CommRingCat.of k))}

/-- The identity of `Γ(X, 𝒪_X)`, as an isomorphism of `k`-algebras from the global sections
`globalSections X` of the scheme layer to the functions `sectionAlgebra k X ⊤` on the top open
used by the sheaves of forms. Their structure maps `k → Γ(X, 𝒪_X)` differ by the restriction along
`⊤ ≤ ⊤`, which is the identity only up to `Functor.map_id`, so the two algebras are not the same
term. -/
def globalSectionsAlgEquiv : globalSections X ≃ₐ[k] sectionAlgebra k X ⊤ :=
  { RingEquiv.refl Γ(X.left, ⊤) with
    commutes' := fun c => by
      change X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
        X.left.presheaf.map (⊤ : X.left.Opens).leTop.op
          (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
      have h : (⊤ : X.left.Opens).leTop.op = 𝟙 _ := rfl
      rw [h, CategoryTheory.Functor.map_id]
      rfl }

/-- `globalSectionsAlgEquiv` is the identity on the common carrier `Γ(X, 𝒪_X)`. -/
lemma globalSectionsAlgEquiv_apply (a : globalSections X) :
    (globalSectionsAlgEquiv X a : Γ(X.left, ⊤)) = a :=
  rfl

/-- The inverse of `globalSectionsAlgEquiv` is the identity on the common carrier. -/
lemma globalSectionsAlgEquiv_symm_apply (a : sectionAlgebra k X ⊤) :
    ((globalSectionsAlgEquiv X).symm a : Γ(X.left, ⊤)) = a :=
  rfl

variable {X}

/-- `globalSectionsAlgEquiv` intertwines the two pullbacks of global functions. -/
lemma globalSectionsAlgEquiv_globalSectionsMap (g : X ⟶ Y) (a : globalSections Y) :
    globalSectionsAlgEquiv X (globalSectionsMap g a) =
      sectionPullbackTop g (globalSectionsAlgEquiv Y a) :=
  rfl

/-- `globalSectionsAlgEquiv` intertwines the two pullbacks of global functions, as algebra
maps. -/
lemma globalSectionsAlgEquiv_comp_globalSectionsMap (g : X ⟶ Y) :
    (globalSectionsAlgEquiv X).toAlgHom.comp (globalSectionsMap g).hom =
      (sectionPullbackTop g).comp (globalSectionsAlgEquiv Y).toAlgHom :=
  rfl

/-- The inverse of `globalSectionsAlgEquiv` intertwines the two pullbacks of global functions, as
algebra maps. -/
lemma globalSectionsAlgEquiv_symm_comp_sectionPullbackTop (g : X ⟶ Y) :
    (globalSectionsAlgEquiv X).symm.toAlgHom.comp (sectionPullbackTop g) =
      (globalSectionsMap g).hom.comp (globalSectionsAlgEquiv Y).symm.toAlgHom :=
  rfl

end GlobalSections

/-! ### The complex of global forms -/

section GlobalForms

variable (k) in
/-- The complex `Γ(X, Ω^•_{X/k})` of global sections of the relative de Rham complex of sheaves: the
global sections functor applied to `formsComplexNat k X`. It is a complex of `k`-modules; its
differentials are not linear over `Γ(X, 𝒪_X)`.

Blueprint: `def:geo-dr-cohomology`. -/
def globalFormsComplex (X : Over (Spec (CommRingCat.of k))) : CochainComplex (ModuleCat k) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat k) ⋙
    (evaluation _ _).obj (op ⊤)).mapHomologicalComplex _).obj (formsComplexNat k X)

variable (X : Over (Spec (CommRingCat.of k)))

/-- The term of degree `n` of `Γ(X, Ω^•_{X/k})` is the module of global sheaf forms of degree
`n`. -/
@[simp]
lemma globalFormsComplex_X (n : ℕ) :
    (globalFormsComplex k X).X n = (formsSheaf k X n).obj.obj (op ⊤) :=
  rfl

/-- The differential of `Γ(X, Ω^•_{X/k})` is the sheaf differential on global sections. -/
@[simp]
lemma globalFormsComplex_d (n : ℕ) :
    (globalFormsComplex k X).d n (n + 1) = (formsSheafD k X n).hom.app (op ⊤) := by
  simp [globalFormsComplex]

variable {X}

/-- A cycle of `Γ(X, Ω^•_{X/k})` is a closed global sheaf form. -/
lemma formsSheafD_iCycles (n : ℕ) (z : (globalFormsComplex k X).cycles n) :
    (formsSheafD k X n).hom.app (op ⊤) ((globalFormsComplex k X).iCycles n z) = 0 := by
  have h := (globalFormsComplex k X).iCycles_d n (n + 1)
  rw [globalFormsComplex_d] at h
  exact congr(($h).hom z)

/-- The pullback of a closed global sheaf form is closed, along any morphism over `S`. -/
lemma formsSheafD_pullbackTop_eq_zero {Y : Over (Spec (CommRingCat.of k))} (g : X ⟶ Y)
    {n : ℕ} {ω : (formsSheaf k Y n).obj.obj (op ⊤)}
    (hω : (formsSheafD k Y n).hom.app (op ⊤) ω = 0) :
    (formsSheafD k X n).hom.app (op ⊤) (formsSheafPullbackTop g n ω) = 0 := by
  rw [formsSheafPullbackTop_d, hω, map_zero]

end GlobalForms

/-! ### Affine evaluation of global forms -/

section Affine

variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

/-- **Global forms of an affine scheme.** For affine `X`, the forms of degree `n` of the algebra
`Γ(X, 𝒪_X)` are the global sections of the sheaf `Ω^n_{X/k}`. This is `affineFormsComparison`,
after `globalSectionsAlgEquiv`. It sends a word `a₀ da₁ ∧ ⋯ ∧ daₙ` in global functions to the same
word of global sheaf forms.

Blueprint: `def:geo-dr-cohomology`, from `thm:geo-forms-comparison`. -/
def globalFormsEquiv (n : ℕ) :
    (⋀[globalSections X]^n Ω[globalSections X⁄k]) ≃ₗ[k] (formsSheaf k X n).obj.obj (op ⊤) :=
  ({ Forms.mapPower (globalSectionsAlgEquiv X).toAlgHom n with
      invFun := Forms.mapPower (globalSectionsAlgEquiv X).symm.toAlgHom n
      left_inv := fun a => Subtype.ext ((Forms.mapEquiv (globalSectionsAlgEquiv X)).left_inv a.val)
      right_inv := fun a =>
        Subtype.ext ((Forms.mapEquiv (globalSectionsAlgEquiv X)).right_inv a.val) } :
    (⋀[globalSections X]^n Ω[globalSections X⁄k]) ≃ₗ[k]
      (⋀[sectionAlgebra k X ⊤]^n Ω[sectionAlgebra k X ⊤⁄k])).trans
    (affineFormsComparison X n)

/-- `globalFormsEquiv` is the affine comparison of the forms transported along
`globalSectionsAlgEquiv`. -/
lemma globalFormsEquiv_apply (n : ℕ) (x : ⋀[globalSections X]^n Ω[globalSections X⁄k]) :
    globalFormsEquiv X n x =
      affineFormsComparison X n (Forms.mapPower (globalSectionsAlgEquiv X).toAlgHom n x) :=
  rfl

/-- The inverse of `globalFormsEquiv` on a form of `Γ(X, 𝒪_X)` given by the affine comparison. -/
lemma globalFormsEquiv_symm_affineFormsComparison (n : ℕ)
    (x : ⋀[sectionAlgebra k X ⊤]^n Ω[sectionAlgebra k X ⊤⁄k]) :
    (globalFormsEquiv X n).symm (affineFormsComparison X n x) =
      Forms.mapPower (globalSectionsAlgEquiv X).symm.toAlgHom n x := by
  rw [LinearEquiv.symm_apply_eq, globalFormsEquiv_apply, ← LinearMap.comp_apply,
    ← Forms.mapPower_comp]
  congr 1
  apply Subtype.ext
  change x.val = Forms.map ((globalSectionsAlgEquiv X).toAlgHom.comp
    (globalSectionsAlgEquiv X).symm.toAlgHom) x.val
  rw [show (globalSectionsAlgEquiv X).toAlgHom.comp (globalSectionsAlgEquiv X).symm.toAlgHom =
    AlgHom.id k _ from AlgHom.ext fun _ => rfl, Forms.map_id]
  rfl

/-- `globalFormsEquiv` commutes with the differential. -/
@[simp]
lemma globalFormsEquiv_d (n : ℕ) (x : ⋀[globalSections X]^n Ω[globalSections X⁄k]) :
    (formsSheafD k X n).hom.app (op ⊤) (globalFormsEquiv X n x) =
      globalFormsEquiv X (n + 1) (powerD k (globalSections X) n x) := by
  rw [globalFormsEquiv_apply, globalFormsEquiv_apply, affineFormsComparison_d,
    Forms.mapPower_powerD]

/-- `globalFormsEquiv` carries the exterior product to the wedge product of sheaf forms. -/
@[simp]
lemma globalFormsEquiv_wedge (p q : ℕ) (a : ⋀[globalSections X]^p Ω[globalSections X⁄k])
    (b : ⋀[globalSections X]^q Ω[globalSections X⁄k]) :
    formsSheafWedge k X p q (op ⊤) (globalFormsEquiv X p a) (globalFormsEquiv X q b) =
      globalFormsEquiv X (p + q) ⟨a.val * b.val, SetLike.mul_mem_graded a.2 b.2⟩ := by
  rw [globalFormsEquiv_apply, globalFormsEquiv_apply, affineFormsComparison_wedge,
    globalFormsEquiv_apply]
  congr 1
  exact Subtype.ext (map_mul (Forms.map (globalSectionsAlgEquiv X).toAlgHom) a.val b.val).symm

variable {X} {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left]

/-- `globalFormsEquiv` carries pullback of algebraic forms along `Γ(g)` to pullback of global sheaf
forms along `g`, for every morphism `g` over `S` of affine schemes. -/
@[simp]
lemma globalFormsEquiv_pull (g : X ⟶ Y) (n : ℕ)
    (x : ⋀[globalSections Y]^n Ω[globalSections Y⁄k]) :
    formsSheafPullbackTop g n (globalFormsEquiv Y n x) =
      globalFormsEquiv X n (Forms.mapPower (globalSectionsMap g).hom n x) := by
  rw [globalFormsEquiv_apply, globalFormsEquiv_apply, affineFormsComparison_pullTop]
  congr 1
  apply Subtype.ext
  simp only [Forms.coe_mapPower, Forms.map_map]
  rw [globalSectionsAlgEquiv_comp_globalSectionsMap]

variable (X)

/-- `Γ(X, Ω^•_{X/k})` is the de Rham complex of `Γ(X, 𝒪_X)`, for affine `X`. -/
def complexIsoGlobalFormsComplex : complex k (globalSections X) ≅ globalFormsComplex k X :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (globalFormsEquiv X n).toModuleIso)
    (by
      rintro n _ rfl
      rw [globalFormsComplex_d, OrlikSolomon.DeRham.complex_d]
      ext x
      exact globalFormsEquiv_d X n x)

/-! ### Closed global forms -/

variable {X}

/-- A global sheaf form is closed exactly when the corresponding form of `Γ(X, 𝒪_X)` is. -/
lemma formsSheafD_globalFormsEquiv_eq_zero_iff {n : ℕ}
    {x : ⋀[globalSections X]^n Ω[globalSections X⁄k]} :
    (formsSheafD k X n).hom.app (op ⊤) (globalFormsEquiv X n x) = 0 ↔
      d k (x : Forms k (globalSections X)) = 0 := by
  rw [globalFormsEquiv_d, LinearEquiv.map_eq_zero_iff, ← Subtype.coe_inj, coe_powerD]
  rfl

/-- The algebraic form of a closed global sheaf form is closed. -/
lemma d_globalFormsEquiv_symm_eq_zero {n : ℕ} {ω : (formsSheaf k X n).obj.obj (op ⊤)}
    (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0) :
    d k ((globalFormsEquiv X n).symm ω : Forms k (globalSections X)) = 0 :=
  formsSheafD_globalFormsEquiv_eq_zero_iff.1 (by rwa [LinearEquiv.apply_symm_apply])

/-- The wedge product of closed global sheaf forms is closed. -/
lemma formsSheafD_wedge_eq_zero {p q : ℕ} {a : (formsSheaf k X p).obj.obj (op ⊤)}
    {b : (formsSheaf k X q).obj.obj (op ⊤)} (ha : (formsSheafD k X p).hom.app (op ⊤) a = 0)
    (hb : (formsSheafD k X q).hom.app (op ⊤) b = 0) :
    (formsSheafD k X (p + q)).hom.app (op ⊤) (formsSheafWedge k X p q (op ⊤) a b) = 0 := by
  rw [← (globalFormsEquiv X p).apply_symm_apply a, ← (globalFormsEquiv X q).apply_symm_apply b,
    globalFormsEquiv_wedge, formsSheafD_globalFormsEquiv_eq_zero_iff]
  change d k (_ * _) = 0
  rw [d_mul, d_globalFormsEquiv_symm_eq_zero ha, d_globalFormsEquiv_symm_eq_zero hb, zero_mul,
    mul_zero, add_zero]

end Affine

end OrlikSolomon.Geometric.DeRham
