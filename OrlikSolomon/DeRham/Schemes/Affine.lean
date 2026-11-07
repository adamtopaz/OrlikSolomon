/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Cohomology
public import OrlikSolomon.DeRham.Schemes.GlobalSections

/-!
# De Rham cohomology of affine schemes

For a smooth affine scheme `X` over `S = Spec k`, the de Rham cohomology `H^•_dR(X/k)` is the
existing algebraic de Rham cohomology `OrlikSolomon.DeRham.Cohomology k Γ(X, 𝒪_X)` of its global
sections, as `def:geo-dr-cohomology` prescribes. This file proves that this is the cohomology of
the complex `Γ(X, Ω^•_{X/k})` of global sections of the sheaves of relative forms: in each degree
`n`, the homology of `Γ(X, Ω^•_{X/k})` is the piece `H^n` of the existing cohomology, and the total
algebra is the direct sum of these pieces. Products are induced by the wedge product of sheaf
forms and pullbacks by pullback of sheaf forms.

The comparison is taken degree by degree, from `affineFormsComparison`, before any direct sum is
formed: global sections are never commuted with an infinite direct sum of sheaves. It needs only
that `X` is affine, over any commutative ring `k`. The formula is not used to define de Rham
cohomology of a scheme that is not affine.

## Main definitions

* `globalFormsHomologyIso X n : H^n(Γ(X, Ω^•_{X/k})) ≅ H^n_dR(Γ(X, 𝒪_X)/k)`, for affine `X`.
* `globalClass X n ω hω`: the class of a closed global sheaf form.
* `Cohomology X`: the de Rham cohomology `H^•_dR(X/k)` of `X` in `aff k`, with its degree pieces
  `Cohomology.degree X n` and its pullbacks `Cohomology.pull f`.
* `Cohomology.directSumEquiv X : H^•_dR(X/k) ≃ₗ[k] ⨁ n, H^n(Γ(X, Ω^•_{X/k}))`.

## Main results

* `globalFormsHomologyIso_hom_homologyπ`: the comparison sends the homology class of a global
  cycle to its class.
* `globalClass_wedge`, `globalClass_pull`: the comparison carries the wedge product of sheaf forms
  to the cup product, and pullback of sheaf forms to pullback.
* `globalClass_eq_zero_iff`, `globalClass_surjective`: classes are closed global sheaf forms modulo
  exact ones.

## Blueprint

`def:geo-dr-cohomology`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry DirectSum
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k]

/-! ### The degreewise comparison -/

section Affine

variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

/-- **The degreewise comparison** `H^n(Γ(X, Ω^•_{X/k})) ≅ H^n_dR(Γ(X, 𝒪_X)/k)`, for affine `X`:
the homology in degree `n` of the complex of global sheaf forms is the piece of degree `n` of the
de Rham cohomology of `Γ(X, 𝒪_X)`. It is induced by `globalFormsEquiv`, degree by degree,
followed by `homologyIso`. It sends the homology class of a global cycle to its class, by
`globalFormsHomologyIso_hom_homologyπ`.

Blueprint: `def:geo-dr-cohomology`. -/
def globalFormsHomologyIso (n : ℕ) :
    (globalFormsComplex k X).homology n ≅
      ModuleCat.of k (OrlikSolomon.DeRham.Cohomology.degree k (globalSections X) n) :=
  HomologicalComplex.homologyMapIso (complexIsoGlobalFormsComplex X).symm n ≪≫
    homologyIso k (globalSections X) n

/-! ### Classes of closed global forms -/

variable {X}

variable (X) in
/-- The de Rham class in `H^n_dR(Γ(X, 𝒪_X)/k)` of a closed global sheaf form `ω` of degree `n`, for
affine `X`: the class of the corresponding form of `Γ(X, 𝒪_X)`. Every class of degree `n` is one
(`globalClass_surjective`), exactly the exact forms have class zero (`globalClass_eq_zero_iff`),
and it carries wedge products to products (`globalClass_wedge`) and pullbacks to pullbacks
(`globalClass_pull`).

Blueprint: `def:geo-dr-cohomology`. -/
def globalClass (n : ℕ) (ω : (formsSheaf k X n).obj.obj (op ⊤))
    (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0) :
    OrlikSolomon.DeRham.Cohomology k (globalSections X) :=
  OrlikSolomon.DeRham.Cohomology.mk ((globalFormsEquiv X n).symm ω : Forms k (globalSections X))
    (d_globalFormsEquiv_symm_eq_zero hω)

/-- The class of the global sheaf form of an algebraic form is the class of that form. -/
@[simp]
lemma globalClass_globalFormsEquiv {n : ℕ} (x : ⋀[globalSections X]^n Ω[globalSections X⁄k])
    (h : (formsSheafD k X n).hom.app (op ⊤) (globalFormsEquiv X n x) = 0) :
    globalClass X n (globalFormsEquiv X n x) h =
      OrlikSolomon.DeRham.Cohomology.mk (x : Forms k (globalSections X))
        (formsSheafD_globalFormsEquiv_eq_zero_iff.1 h) :=
  OrlikSolomon.DeRham.Cohomology.mk_congr
    (congrArg Subtype.val ((globalFormsEquiv X n).symm_apply_apply x)) _

/-- The class of a closed global sheaf form of degree `n` has degree `n`. -/
lemma globalClass_mem_degree {n : ℕ} (ω : (formsSheaf k X n).obj.obj (op ⊤))
    (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0) :
    globalClass X n ω hω ∈ OrlikSolomon.DeRham.Cohomology.degree k (globalSections X) n :=
  OrlikSolomon.DeRham.Cohomology.mk_mem_degree ((globalFormsEquiv X n).symm ω).2 _

@[simp]
lemma globalClass_zero {n : ℕ} (h : (formsSheafD k X n).hom.app (op ⊤) 0 = 0) :
    globalClass X n 0 h = 0 := by
  simp only [globalClass, map_zero, Submodule.coe_zero, OrlikSolomon.DeRham.Cohomology.mk_zero]

lemma globalClass_add {n : ℕ} {ω ω' : (formsSheaf k X n).obj.obj (op ⊤)}
    (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0)
    (hω' : (formsSheafD k X n).hom.app (op ⊤) ω' = 0)
    (h : (formsSheafD k X n).hom.app (op ⊤) (ω + ω') = 0) :
    globalClass X n (ω + ω') h = globalClass X n ω hω + globalClass X n ω' hω' := by
  simp only [globalClass, map_add, Submodule.coe_add, OrlikSolomon.DeRham.Cohomology.mk_add]

lemma globalClass_smul {n : ℕ} (c : k) {ω : (formsSheaf k X n).obj.obj (op ⊤)}
    (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0)
    (h : (formsSheafD k X n).hom.app (op ⊤) (c • ω) = 0) :
    globalClass X n (c • ω) h = c • globalClass X n ω hω := by
  simp only [globalClass, map_smul, Submodule.coe_smul_of_tower,
    OrlikSolomon.DeRham.Cohomology.mk_smul]

/-- **Cup product is induced by the wedge product.** The class of the wedge product of two closed
global sheaf forms is the product of their classes.

Blueprint: `def:geo-dr-cohomology`. -/
lemma globalClass_wedge {p q : ℕ} {a : (formsSheaf k X p).obj.obj (op ⊤)}
    {b : (formsSheaf k X q).obj.obj (op ⊤)} (ha : (formsSheafD k X p).hom.app (op ⊤) a = 0)
    (hb : (formsSheafD k X q).hom.app (op ⊤) b = 0) :
    globalClass X (p + q) (formsSheafWedge k X p q (op ⊤) a b) (formsSheafD_wedge_eq_zero ha hb) =
      globalClass X p a ha * globalClass X q b hb := by
  rw [globalClass, globalClass, globalClass, OrlikSolomon.DeRham.Cohomology.mk_mul]
  refine OrlikSolomon.DeRham.Cohomology.mk_congr ?_ _
  conv_lhs => rw [← (globalFormsEquiv X p).apply_symm_apply a,
    ← (globalFormsEquiv X q).apply_symm_apply b, globalFormsEquiv_wedge,
    LinearEquiv.symm_apply_apply]

/-- **Pullback is induced by pullback of sheaf forms.** For a morphism `g : X ⟶ Y` over `S` of
affine schemes, the class of the pullback of a closed global sheaf form is the image of its class
under the map induced by `Γ(g)`.

Blueprint: `def:geo-dr-cohomology`. -/
lemma globalClass_pull {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left] (g : X ⟶ Y)
    {n : ℕ} {ω : (formsSheaf k Y n).obj.obj (op ⊤)}
    (hω : (formsSheafD k Y n).hom.app (op ⊤) ω = 0) :
    globalClass X n (formsSheafPullbackTop g n ω) (formsSheafD_pullbackTop_eq_zero g hω) =
      OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap g).hom (globalClass Y n ω hω) := by
  rw [globalClass, globalClass, OrlikSolomon.DeRham.Cohomology.map_mk]
  refine OrlikSolomon.DeRham.Cohomology.mk_congr ?_ _
  conv_lhs => rw [← (globalFormsEquiv Y n).apply_symm_apply ω, globalFormsEquiv_pull,
    LinearEquiv.symm_apply_apply]
  rfl

/-- **Classes are closed forms modulo exact forms.** A closed global sheaf form of degree `n + 1`
has class zero exactly when it is the differential of a global sheaf form of degree `n`.

Blueprint: `def:geo-dr-cohomology`. -/
lemma globalClass_eq_zero_iff {n : ℕ} {ω : (formsSheaf k X (n + 1)).obj.obj (op ⊤)}
    (hω : (formsSheafD k X (n + 1)).hom.app (op ⊤) ω = 0) :
    globalClass X (n + 1) ω hω = 0 ↔
      ∃ η : (formsSheaf k X n).obj.obj (op ⊤), (formsSheafD k X n).hom.app (op ⊤) η = ω := by
  rw [globalClass, OrlikSolomon.DeRham.Cohomology.mk_eq_zero_iff_of_mem_exteriorPower_succ
    ((globalFormsEquiv X (n + 1)).symm ω).2]
  constructor
  · rintro ⟨y, hy, hyω⟩
    refine ⟨globalFormsEquiv X n ⟨y, hy⟩, ?_⟩
    rw [globalFormsEquiv_d, ← (globalFormsEquiv X (n + 1)).apply_symm_apply ω]
    exact congrArg _ (Subtype.ext hyω)
  · rintro ⟨η, rfl⟩
    refine ⟨((globalFormsEquiv X n).symm η : Forms k (globalSections X)),
      ((globalFormsEquiv X n).symm η).2, ?_⟩
    conv_rhs => rw [← (globalFormsEquiv X n).apply_symm_apply η, globalFormsEquiv_d,
      LinearEquiv.symm_apply_apply]
    rfl

/-- A closed global function has class zero exactly when it is zero. -/
lemma globalClass_eq_zero_iff_of_zero {ω : (formsSheaf k X 0).obj.obj (op ⊤)}
    (hω : (formsSheafD k X 0).hom.app (op ⊤) ω = 0) :
    globalClass X 0 ω hω = 0 ↔ ω = 0 := by
  rw [globalClass, OrlikSolomon.DeRham.Cohomology.mk_eq_zero_iff_of_mem_exteriorPower_zero
    ((globalFormsEquiv X 0).symm ω).2, Submodule.coe_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- Every class of degree `n` is the class of a closed global sheaf form of degree `n`.

Blueprint: `def:geo-dr-cohomology`. -/
lemma globalClass_surjective {n : ℕ} {c : OrlikSolomon.DeRham.Cohomology k (globalSections X)}
    (hc : c ∈ OrlikSolomon.DeRham.Cohomology.degree k (globalSections X) n) :
    ∃ (ω : (formsSheaf k X n).obj.obj (op ⊤)) (hω : (formsSheafD k X n).hom.app (op ⊤) ω = 0),
      globalClass X n ω hω = c := by
  obtain ⟨x, hx, hxn, rfl⟩ := OrlikSolomon.DeRham.Cohomology.mem_degree_iff.1 hc
  exact ⟨globalFormsEquiv X n ⟨x, hxn⟩, formsSheafD_globalFormsEquiv_eq_zero_iff.2 hx,
    globalClass_globalFormsEquiv _ _⟩

/-- The degreewise comparison sends the homology class of a global cycle to the class of that
closed global sheaf form. So it is the identification of the two descriptions of `H^n`, and not
merely some isomorphism.

Blueprint: `def:geo-dr-cohomology`. -/
lemma globalFormsHomologyIso_hom_homologyπ (n : ℕ) (z : (globalFormsComplex k X).cycles n) :
    (((globalFormsHomologyIso X n).hom ((globalFormsComplex k X).homologyπ n z) :
        OrlikSolomon.DeRham.Cohomology.degree k (globalSections X) n) :
      OrlikSolomon.DeRham.Cohomology k (globalSections X)) =
      globalClass X n ((globalFormsComplex k X).iCycles n z) (formsSheafD_iCycles n z) := by
  let φ := (complexIsoGlobalFormsComplex X).inv
  have h₁ : (globalFormsHomologyIso X n).hom ((globalFormsComplex k X).homologyπ n z) =
      (homologyIso k (globalSections X) n).hom
        ((complex k (globalSections X)).homologyπ n (HomologicalComplex.cyclesMap φ n z)) := by
    change (homologyIso k (globalSections X) n).hom
      (HomologicalComplex.homologyMap φ n ((globalFormsComplex k X).homologyπ n z)) = _
    exact congrArg (homologyIso k (globalSections X) n).hom
      congr(($(HomologicalComplex.homologyπ_naturality φ n)).hom z)
  have h₂ : (complex k (globalSections X)).iCycles n (HomologicalComplex.cyclesMap φ n z) =
      (globalFormsEquiv X n).symm ((globalFormsComplex k X).iCycles n z) :=
    congr(($(HomologicalComplex.cyclesMap_i φ n)).hom z)
  rw [h₁, coe_homologyIso_hom_homologyπ]
  exact OrlikSolomon.DeRham.Cohomology.mk_congr (congrArg Subtype.val h₂) _

end Affine

/-! ### De Rham cohomology of smooth affine schemes -/

/-- **De Rham cohomology of a smooth affine scheme.** For `X` in the domain `aff k` of smooth affine
schemes over `S = Spec k`, `H^•_dR(X/k)` is the existing algebraic de Rham cohomology of the
`k`-algebra `Γ(X, 𝒪_X)` of global sections, as the blueprint prescribes. Its specification is the
cohomology of global sheaf forms: `Cohomology.degreeEquiv` identifies its piece of degree `n` with
`H^n(Γ(X, Ω^•_{X/k}))`, `Cohomology.directSumEquiv` identifies it with their direct sum, and
`globalClass_wedge` and `Cohomology.pull_globalClass` say that products and pullbacks are those of
sheaf forms.

It is a reducible abbreviation, so that the whole API of `OrlikSolomon.DeRham.Cohomology` applies.
It is not defined for schemes that are not affine.

Blueprint: `def:geo-dr-cohomology`. -/
abbrev Cohomology (X : (SmoothDomain.aff k).Obj) : Type u :=
  OrlikSolomon.DeRham.Cohomology k (globalSections X.obj)

namespace Cohomology

/-- The piece `H^n_dR(X/k)` of degree `n` of the de Rham cohomology of a smooth affine scheme. It
is `H^n(Γ(X, Ω^•_{X/k}))` by `degreeEquiv`.

Blueprint: `def:geo-dr-cohomology`. -/
abbrev degree (X : (SmoothDomain.aff k).Obj) (n : ℕ) : Submodule k (Cohomology X) :=
  OrlikSolomon.DeRham.Cohomology.degree k (globalSections X.obj) n

/-- **The degreewise specification** `H^n_dR(X/k) ≃ H^n(Γ(X, Ω^•_{X/k}))`, from
`globalFormsHomologyIso`.

Blueprint: `def:geo-dr-cohomology`. -/
def degreeEquiv (X : (SmoothDomain.aff k).Obj) (n : ℕ) :
    (globalFormsComplex k X.obj).homology n ≃ₗ[k] degree X n :=
  (globalFormsHomologyIso X.obj n).toLinearEquiv

/-- The degreewise specification sends the homology class of a global cycle to its class. -/
@[simp]
lemma coe_degreeEquiv_homologyπ (X : (SmoothDomain.aff k).Obj) (n : ℕ)
    (z : (globalFormsComplex k X.obj).cycles n) :
    (degreeEquiv X n ((globalFormsComplex k X.obj).homologyπ n z) : Cohomology X) =
      globalClass X.obj n ((globalFormsComplex k X.obj).iCycles n z) (formsSheafD_iCycles n z) :=
  globalFormsHomologyIso_hom_homologyπ n z

/-- **The total specification** `H^•_dR(X/k) ≃ ⨁_{n ≥ 0} H^n(Γ(X, Ω^•_{X/k}))`: the decomposition of
the total cohomology into its degrees, followed by the degreewise comparison in each degree. The
direct sum is formed after the comparison, so global sections are not commuted with an infinite
direct sum of sheaves.

Blueprint: `def:geo-dr-cohomology`. -/
def directSumEquiv (X : (SmoothDomain.aff k).Obj) :
    Cohomology X ≃ₗ[k] ⨁ n : ℕ, (globalFormsComplex k X.obj).homology n :=
  (decomposeLinearEquiv (degree X)).trans
    (DFinsupp.mapRange.linearEquiv fun n => (degreeEquiv X n).symm)

/-- The component of degree `n` of `directSumEquiv` is the degreewise comparison applied to the
component of degree `n`. -/
@[simp]
lemma directSumEquiv_apply (X : (SmoothDomain.aff k).Obj) (c : Cohomology X) (n : ℕ) :
    directSumEquiv X c n = (degreeEquiv X n).symm (decompose (degree X) c n) :=
  rfl

variable {X Y Z : (SmoothDomain.aff k).Obj}

/-- Pullback `f^* : H^•_dR(Y/k) → H^•_dR(X/k)` along a morphism `f : X ⟶ Y` of smooth affine
schemes over `S`: the map induced by `Γ(f) : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. It is pullback of global
sheaf forms, by `pull_globalClass`.

Blueprint: `def:geo-dr-cohomology`. -/
def pull (f : X ⟶ Y) : Cohomology Y →ₐ[k] Cohomology X :=
  OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap f.hom).hom

lemma pull_apply (f : X ⟶ Y) (c : Cohomology Y) :
    pull f c = OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap f.hom).hom c :=
  rfl

@[simp]
lemma pull_id (c : Cohomology X) : pull (𝟙 X) c = c := by
  rw [pull_apply]
  exact congrArg (fun φ => φ c) OrlikSolomon.DeRham.Cohomology.map_id

lemma pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (c : Cohomology Z) :
    pull (f ≫ g) c = pull f (pull g c) := by
  rw [pull_apply, pull_apply, pull_apply, OrlikSolomon.DeRham.Cohomology.map_map]
  rfl

/-- Pullback preserves degrees. -/
lemma pull_mem_degree (f : X ⟶ Y) {n : ℕ} {c : Cohomology Y} (hc : c ∈ degree Y n) :
    pull f c ∈ degree X n :=
  OrlikSolomon.DeRham.Cohomology.map_mem_degree _ hc

/-- **Pullback is pullback of global sheaf forms.**

Blueprint: `def:geo-dr-cohomology`. -/
lemma pull_globalClass (f : X ⟶ Y) {n : ℕ} {ω : (formsSheaf k Y.obj n).obj.obj (op ⊤)}
    (hω : (formsSheafD k Y.obj n).hom.app (op ⊤) ω = 0) :
    pull f (globalClass Y.obj n ω hω) =
      globalClass X.obj n (formsSheafPullbackTop f.hom n ω)
        (formsSheafD_pullbackTop_eq_zero f.hom hω) :=
  (globalClass_pull f.hom hω).symm

end Cohomology

end OrlikSolomon.Geometric.DeRham
