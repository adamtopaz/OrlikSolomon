/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Units

/-!
# Products with the affine line and the multiplicative group

This file proves `lem:geo-products` of the geometric refactor blueprint: for any `k`-algebra `A`,
smooth or not, `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` and `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, compatibly with
the first projections, the sections `z = 0` and `z = 1`, the open immersion `𝔾ₘ → 𝔸¹`, the
coordinate and naturality in `A`. It also writes the standard pair in geometric form,
`X → X ×_S 𝔸¹ ← X ×_S 𝔾ₘ`, for every `S`-scheme `X`, and specializes everything to smooth algebras
and to domains, in terms of the maps of `SmoothAlg`, for the transport of an algebraic theory.

## Main definitions

* `Geometric.gmToAffineLine k`: the open immersion `𝔾ₘ → 𝔸¹_S`, the map of the function `z`.
* `Geometric.prodCoord X`: the coordinate `z` on `X ×_S 𝔸¹_S`.
* `Geometric.zeroSection X`, `Geometric.oneSection X`: the sections `z = 0` of `X ×_S 𝔸¹ → X` and
  `z = 1` of `X ×_S 𝔾ₘ → X`.
* `Geometric.polynomialAlg A`, `Geometric.laurentAlg A`: the `k`-algebras `A[z]` and `A[z, z⁻¹]` of
  any `A : CommAlgCat k`, with `polynomialAlgC`, `laurentAlgC`, `polynomialAlgToLaurent`,
  `polynomialAlgLift` and `laurentAlgLift`.
* `Geometric.specPolynomialIso A`, `Geometric.specLaurentIso A`: the isomorphisms
  `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` and `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ` of `S`-schemes.
* `SmoothDomain.specPolynomialIso`, `SmoothDomain.specLaurentIso`: the same isomorphisms for a
  smooth algebra, in a domain.

## Main results

* `specPolynomialIso_hom_fst`, `specLaurentIso_hom_fst`: the inclusions of constants are the first
  projections.
* `specMap_polynomialAlgLift_zero_comp_specPolynomialIso_hom`: evaluation at `0` is the zero
  section.
* `specMap_laurentAlgLift_one_comp_specLaurentIso_hom`: evaluation at `1` is the section `z = 1`.
* `specMap_polynomialAlgToLaurent_comp_specPolynomialIso_hom`: `A[z] → A[z, z⁻¹]` is the open
  immersion.
* `specPolynomialIso_hom_appTop_prodCoord`: the coordinate of `X ×_S 𝔸¹` is the variable of `A[z]`.
* `specMap_polynomialAlgMap_comp_specPolynomialIso_hom`,
  `specMap_laurentAlgMap_comp_specLaurentIso_hom`: naturality in `A`.
* The `SmoothDomain.specFunctor_map_..._comp_...` lemmas: the same statements for the maps of
  `SmoothAlg` (`polynomialC`, `polynomialLift`, `laurentSection`, `polynomialToLaurent`), in a
  domain.

So `Spec` of the standard pair `(A[z], A, A[z, z⁻¹], z)` is the geometric standard pair of
`Spec A`. Nothing here needs smoothness, and `A = 0` is allowed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial MonObj

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### The standard pair in geometric form -/

variable (k) in
/-- The open immersion `𝔾ₘ → 𝔸¹_S`: the `S`-morphism of the function `z` on `𝔾ₘ`. -/
def gmToAffineLine : gm k ⟶ affineLine k := (homAffineLineEquiv _).symm (gmCoord k : _)

@[simp] lemma gmToAffineLine_appTop_affineLineCoord :
    (gmToAffineLine k).left.appTop (affineLineCoord k) = gmCoord k :=
  (homAffineLineEquiv _).apply_symm_apply _

section StandardPair

variable (X : Over (Spec (.of k)))

/-- The coordinate `z` on `X ×_S 𝔸¹_S`, the pullback of the coordinate of `𝔸¹_S`. It is the equation
of the zero section, the divisor of the geometric standard pair.

Blueprint: `lem:geo-products`. -/
def prodCoord : Γ((X ⊗ affineLine k).left, ⊤) := homAffineLineEquiv _ (snd X (affineLine k))

/-- The section `z = 0` of the projection `X ×_S 𝔸¹_S → X`, the closed immersion of the geometric
standard pair.

Blueprint: `lem:geo-products`. -/
def zeroSection : X ⟶ X ⊗ affineLine k := lift (𝟙 X) ((homAffineLineEquiv X).symm 0)

/-- The section `z = 1` of the projection `X ×_S 𝔾ₘ → X`.

Blueprint: `lem:geo-products`. -/
def oneSection : X ⟶ X ⊗ gm k := lift (𝟙 X) (unitsEquivHomGm X 1)

@[reassoc (attr := simp)] lemma zeroSection_fst : zeroSection X ≫ fst _ _ = 𝟙 X := lift_fst _ _

@[reassoc (attr := simp)] lemma oneSection_fst : oneSection X ≫ fst _ _ = 𝟙 X := lift_fst _ _

/-- The coordinate vanishes on the zero section. -/
lemma zeroSection_appTop_prodCoord : (zeroSection X).left.appTop (prodCoord X) = 0 := by
  rw [prodCoord, ← homAffineLineEquiv_comp, zeroSection, lift_snd, Equiv.apply_symm_apply]

/-- The open immersion `X ×_S 𝔾ₘ → X ×_S 𝔸¹_S` pulls the coordinate back to the coordinate unit. -/
lemma whiskerLeft_gmToAffineLine_appTop_prodCoord :
    (X ◁ gmToAffineLine k).left.appTop (prodCoord X) =
      (snd X (gm k)).left.appTop (gmCoord k) := by
  rw [prodCoord, ← homAffineLineEquiv_comp, whiskerLeft_snd, homAffineLineEquiv_comp,
    homAffineLineEquiv_apply, gmToAffineLine_appTop_affineLineCoord]

end StandardPair

/-! ### Polynomial and Laurent algebras -/

section Algebras

variable (A : CommAlgCat.{u} k) {B : CommAlgCat.{u} k}

/-- The polynomial algebra `A[z]` of a `k`-algebra `A`, the ring of `Spec A ×_S 𝔸¹_S`. -/
@[implicit_reducible]
def polynomialAlg : CommAlgCat.{u} k := CommAlgCat.of k A[X]

/-- The Laurent polynomial algebra `A[z, z⁻¹]` of a `k`-algebra `A`, the ring of
`Spec A ×_S 𝔾ₘ`. -/
@[implicit_reducible]
def laurentAlg : CommAlgCat.{u} k := CommAlgCat.of k A[T;T⁻¹]

/-- The inclusion of constants `A → A[z]`. -/
def polynomialAlgC : A ⟶ polynomialAlg A :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := A) (Y := polynomialAlg A) Polynomial.CAlgHom

/-- The inclusion of constants `A → A[z, z⁻¹]`. -/
def laurentAlgC : A ⟶ laurentAlg A :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := A) (Y := laurentAlg A)
    (IsScalarTower.toAlgHom k A A[T;T⁻¹])

/-- The inclusion `A[z] → A[z, z⁻¹]`. -/
def polynomialAlgToLaurent : polynomialAlg A ⟶ laurentAlg A :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := polynomialAlg A) (Y := laurentAlg A)
    (Polynomial.toLaurentAlg.restrictScalars k : A[X] →ₐ[k] A[T;T⁻¹])

variable {A}

/-- The universal property of `A[z]`: the map extending `φ` and sending `z` to `b`. -/
def polynomialAlgLift (φ : A ⟶ B) (b : B) : polynomialAlg A ⟶ B :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := polynomialAlg A) (Y := B)
    (Polynomial.eval₂AlgHom φ.hom b fun _ ↦ Commute.all _ _)

/-- The universal property of `A[z, z⁻¹]`: the map extending `φ` and sending `z` to the unit
`u`. -/
def laurentAlgLift (φ : A ⟶ B) (u : Bˣ) : laurentAlg A ⟶ B :=
  ConcreteCategory.ofHom (C := CommAlgCat k) (X := laurentAlg A) (Y := B)
    (laurentPolynomialLift φ.hom u)

@[simp] lemma polynomialAlgLift_C (φ : A ⟶ B) (b : B) (a : A) :
    polynomialAlgLift φ b (polynomialAlgC A a) = φ a :=
  Polynomial.eval₂_C _ _

@[simp] lemma polynomialAlgLift_X (φ : A ⟶ B) (b : B) :
    polynomialAlgLift φ b (Polynomial.X : A[X]) = b :=
  Polynomial.eval₂_X _ _

@[simp] lemma laurentAlgLift_C (φ : A ⟶ B) (u : Bˣ) (a : A) :
    laurentAlgLift φ u (laurentAlgC A a) = φ a :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] lemma laurentAlgLift_T (φ : A ⟶ B) (u : Bˣ) :
    laurentAlgLift φ u (LaurentPolynomial.T 1 : A[T;T⁻¹]) = u :=
  laurentPolynomialLift_T _ _

@[simp] lemma polynomialAlgToLaurent_C (a : A) :
    polynomialAlgToLaurent A (polynomialAlgC A a) = laurentAlgC A a :=
  Polynomial.toLaurent_C a

@[simp] lemma polynomialAlgToLaurent_X :
    polynomialAlgToLaurent A (Polynomial.X : A[X]) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) :=
  Polynomial.toLaurent_X

@[reassoc (attr := simp)]
lemma polynomialAlgC_comp_polynomialAlgLift (φ : A ⟶ B) (b : B) :
    polynomialAlgC A ≫ polynomialAlgLift φ b = φ := by
  ext a
  exact polynomialAlgLift_C φ b a

@[reassoc (attr := simp)]
lemma laurentAlgC_comp_laurentAlgLift (φ : A ⟶ B) (u : Bˣ) :
    laurentAlgC A ≫ laurentAlgLift φ u = φ := by
  ext a
  exact laurentAlgLift_C φ u a

@[reassoc (attr := simp)]
lemma polynomialAlgC_comp_polynomialAlgToLaurent :
    polynomialAlgC A ≫ polynomialAlgToLaurent A = laurentAlgC A := by
  ext a
  exact polynomialAlgToLaurent_C a

/-- `k`-algebra maps out of `A[z]` agree when they agree on constants and on `z`. -/
lemma polynomialAlg_hom_ext {f g : polynomialAlg A ⟶ B}
    (hC : ∀ a, f (polynomialAlgC A a) = g (polynomialAlgC A a))
    (hX : f (Polynomial.X : A[X]) = g (Polynomial.X : A[X])) : f = g := by
  ext1
  exact Polynomial.algHom_ext' (AlgHom.ext hC) hX

/-- `k`-algebra maps out of `A[z, z⁻¹]` agree when they agree on constants and on `z`. -/
lemma laurentAlg_hom_ext {f g : laurentAlg A ⟶ B}
    (hC : ∀ a, f (laurentAlgC A a) = g (laurentAlgC A a))
    (hT : f (LaurentPolynomial.T 1 : A[T;T⁻¹]) = g (LaurentPolynomial.T 1 : A[T;T⁻¹])) :
    f = g := by
  ext1
  exact laurentPolynomial_algHom_ext hC hT

end Algebras

section Spec

/-! ### `Spec A[z]` -/

variable (A : CommAlgCat.{u} k)

/-- The `k`-algebra map `A[z] → Γ(P, 𝒪)` for an `S`-morphism `P → Spec A ×_S 𝔸¹`. -/
def polynomialToGlobalSections {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ affineLine k) :
    polynomialAlg A ⟶ globalSections P :=
  polynomialAlgLift (specHomEquiv P A (g ≫ fst _ _)) (homAffineLineEquiv P (g ≫ snd _ _))

lemma polynomialToGlobalSections_C {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ affineLine k)
    (a : A) :
    polynomialToGlobalSections A g (polynomialAlgC A a) = specHomEquiv P A (g ≫ fst _ _) a :=
  polynomialAlgLift_C _ _ _

lemma polynomialToGlobalSections_X {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ affineLine k) :
    polynomialToGlobalSections A g (Polynomial.X : A[X]) = homAffineLineEquiv P (g ≫ snd _ _) :=
  polynomialAlgLift_X _ _

lemma polynomialToGlobalSections_comp {P Q : Over (Spec (.of k))} (h : Q ⟶ P)
    (g : P ⟶ spec A ⊗ affineLine k) :
    polynomialToGlobalSections A g ≫ globalSectionsMap h =
      polynomialToGlobalSections A (h ≫ g) := by
  apply polynomialAlg_hom_ext
  · intro a
    rw [CategoryTheory.comp_apply, polynomialToGlobalSections_C,
      polynomialToGlobalSections_C, Category.assoc, specHomEquiv_comp]
    rfl
  · rw [CategoryTheory.comp_apply, polynomialToGlobalSections_X,
      polynomialToGlobalSections_X, Category.assoc, homAffineLineEquiv_comp]
    rfl

/-- The variable `z` of `A[z]`, as a global function on `Spec A[z]`. -/
abbrev polynomialVar : Γ((spec (polynomialAlg A)).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (polynomialAlg A))).inv (Polynomial.X : A[X])

/-- The isomorphism `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` of `S`-schemes, for any `k`-algebra `A`. Its
components are `Spec` of the inclusion of constants and the map of the variable `z`.

Blueprint: `lem:geo-products`. -/
def specPolynomialIso : spec (polynomialAlg A) ≅ spec A ⊗ affineLine k where
  hom := lift (specMap (polynomialAlgC A)) ((homAffineLineEquiv _).symm (polynomialVar A))
  inv := (specHomEquiv _ _).symm (polynomialToGlobalSections A (𝟙 _))
  hom_inv_id := by
    apply (specHomEquiv _ (polynomialAlg A)).injective
    rw [specHomEquiv_comp, Equiv.apply_symm_apply, polynomialToGlobalSections_comp,
      Category.comp_id]
    apply polynomialAlg_hom_ext
    · intro a
      rw [polynomialToGlobalSections_C, lift_fst, ← Category.id_comp (specMap _),
        specHomEquiv_comp_specMap]
      rfl
    · rw [polynomialToGlobalSections_X, lift_snd, Equiv.apply_symm_apply]
      rfl
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (specHomEquiv _ A).injective
      rw [Category.assoc, lift_fst, specHomEquiv_comp_specMap, Equiv.apply_symm_apply,
        Category.id_comp]
      ext a
      exact polynomialToGlobalSections_C A (𝟙 _) a
    · apply (homAffineLineEquiv _).injective
      rw [Category.assoc, lift_snd, homAffineLineEquiv_comp, Equiv.apply_symm_apply,
        Category.id_comp]
      change specHomEquiv (spec A ⊗ affineLine k) (polynomialAlg A)
        ((specHomEquiv (spec A ⊗ affineLine k) (polynomialAlg A)).symm
          (polynomialToGlobalSections A (𝟙 _))) (Polynomial.X : A[X]) = _
      rw [Equiv.apply_symm_apply, polynomialToGlobalSections_X, Category.id_comp]

@[reassoc (attr := simp)]
lemma specPolynomialIso_hom_fst :
    (specPolynomialIso A).hom ≫ fst _ _ = specMap (polynomialAlgC A) :=
  lift_fst _ _

lemma specPolynomialIso_hom_snd :
    (specPolynomialIso A).hom ≫ snd _ _ = (homAffineLineEquiv _).symm (polynomialVar A) :=
  lift_snd _ _

/-- The coordinate of `Spec A ×_S 𝔸¹_S` is the variable of `A[z]`. -/
lemma specPolynomialIso_hom_appTop_prodCoord :
    (specPolynomialIso A).hom.left.appTop (prodCoord _) = polynomialVar A := by
  rw [prodCoord, ← homAffineLineEquiv_comp, specPolynomialIso_hom_snd, Equiv.apply_symm_apply]

/-- Evaluation at `z = 0` is the zero section: `Spec` of the closed map of the standard pair of `A`.

Blueprint: `lem:geo-products`. -/
lemma specMap_polynomialAlgLift_zero_comp_specPolynomialIso_hom :
    specMap (polynomialAlgLift (𝟙 A) 0) ≫ (specPolynomialIso A).hom = zeroSection (spec A) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, specPolynomialIso_hom_fst, ← specMap_comp, zeroSection_fst,
      polynomialAlgC_comp_polynomialAlgLift]
    exact specMap_id _
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, homAffineLineEquiv_comp, specPolynomialIso_hom_snd,
      Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv, zeroSection, lift_snd,
      Equiv.apply_symm_apply]
    exact (congrArg _ (polynomialAlgLift_X _ _)).trans (map_zero _)

/-- Naturality of `specPolynomialIso` in `A`. -/
@[reassoc]
lemma specMap_polynomialAlgMap_comp_specPolynomialIso_hom {B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    specMap (polynomialAlgLift (φ ≫ polynomialAlgC B) (Polynomial.X : B[X])) ≫
        (specPolynomialIso A).hom =
      (specPolynomialIso B).hom ≫ (specMap φ ▷ affineLine k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specPolynomialIso_hom_fst, whiskerRight_fst,
      specPolynomialIso_hom_fst_assoc, ← specMap_comp, ← specMap_comp,
      polynomialAlgC_comp_polynomialAlgLift]
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, Category.assoc, whiskerRight_snd, homAffineLineEquiv_comp,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply]
    exact congrArg _ (polynomialAlgLift_X _ _)

/-! ### `Spec A[z, z⁻¹]` -/

/-- The `k`-algebra map `A[z, z⁻¹] → Γ(P, 𝒪)` for an `S`-morphism `P → Spec A ×_S 𝔾ₘ`. -/
def laurentToGlobalSections {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ gm k) :
    laurentAlg A ⟶ globalSections P :=
  laurentAlgLift (specHomEquiv P A (g ≫ fst _ _)) (homGmEquiv P (g ≫ snd _ _))

lemma laurentToGlobalSections_C {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ gm k) (a : A) :
    laurentToGlobalSections A g (laurentAlgC A a) = specHomEquiv P A (g ≫ fst _ _) a :=
  laurentAlgLift_C _ _ _

lemma laurentToGlobalSections_T {P : Over (Spec (.of k))} (g : P ⟶ spec A ⊗ gm k) :
    laurentToGlobalSections A g (LaurentPolynomial.T 1 : A[T;T⁻¹]) =
      (homGmEquiv P (g ≫ snd _ _) : Γ(P.left, ⊤)) :=
  laurentAlgLift_T _ _

lemma laurentToGlobalSections_comp {P Q : Over (Spec (.of k))} (h : Q ⟶ P)
    (g : P ⟶ spec A ⊗ gm k) :
    laurentToGlobalSections A g ≫ globalSectionsMap h = laurentToGlobalSections A (h ≫ g) := by
  apply laurentAlg_hom_ext
  · intro a
    rw [CategoryTheory.comp_apply, laurentToGlobalSections_C, laurentToGlobalSections_C,
      Category.assoc, specHomEquiv_comp]
    rfl
  · rw [CategoryTheory.comp_apply, laurentToGlobalSections_T, laurentToGlobalSections_T,
      Category.assoc, homGmEquiv_comp]
    rfl

/-- The variable `z` of `A[z, z⁻¹]`, as a global unit on `Spec A[z, z⁻¹]`. -/
abbrev laurentVar : Γ((spec (laurentAlg A)).left, ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (.of (laurentAlg A))).inv.hom.toMonoidHom :
    laurentAlg A →* Γ((spec (laurentAlg A)).left, ⊤)) (laurentPolynomialT (R := A))

/-- The isomorphism `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ` of `S`-schemes, for any `k`-algebra `A`. Its
components are `Spec` of the inclusion of constants and the map of the unit `z`.

Blueprint: `lem:geo-products`. -/
def specLaurentIso : spec (laurentAlg A) ≅ spec A ⊗ gm k where
  hom := lift (specMap (laurentAlgC A)) (unitsEquivHomGm _ (laurentVar A))
  inv := (specHomEquiv _ _).symm (laurentToGlobalSections A (𝟙 _))
  hom_inv_id := by
    apply (specHomEquiv _ (laurentAlg A)).injective
    rw [specHomEquiv_comp, Equiv.apply_symm_apply, laurentToGlobalSections_comp,
      Category.comp_id]
    apply laurentAlg_hom_ext
    · intro a
      rw [laurentToGlobalSections_C, lift_fst, ← Category.id_comp (specMap _),
        specHomEquiv_comp_specMap]
      rfl
    · rw [laurentToGlobalSections_T, lift_snd, ← unitsEquivHomGm_symm_apply,
        MulEquiv.symm_apply_apply]
      rfl
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (specHomEquiv _ A).injective
      rw [Category.assoc, lift_fst, specHomEquiv_comp_specMap, Equiv.apply_symm_apply,
        Category.id_comp]
      ext a
      exact laurentToGlobalSections_C A (𝟙 _) a
    · apply hom_ext_gm
      rw [Category.assoc, lift_snd, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        unitsEquivHomGm_appTop_gmCoord, Category.id_comp]
      change specHomEquiv (spec A ⊗ gm k) (laurentAlg A)
        ((specHomEquiv (spec A ⊗ gm k) (laurentAlg A)).symm
          (laurentToGlobalSections A (𝟙 _))) (LaurentPolynomial.T 1 : A[T;T⁻¹]) = _
      rw [Equiv.apply_symm_apply, laurentToGlobalSections_T, Category.id_comp]
      rfl

@[reassoc (attr := simp)]
lemma specLaurentIso_hom_fst : (specLaurentIso A).hom ≫ fst _ _ = specMap (laurentAlgC A) :=
  lift_fst _ _

lemma specLaurentIso_hom_snd :
    (specLaurentIso A).hom ≫ snd _ _ = unitsEquivHomGm _ (laurentVar A) :=
  lift_snd _ _

/-- The coordinate unit of `Spec A ×_S 𝔾ₘ` is the variable of `A[z, z⁻¹]`. -/
lemma specLaurentIso_hom_appTop_snd_gmCoord :
    (specLaurentIso A).hom.left.appTop ((snd (spec A) (gm k)).left.appTop (gmCoord k)) =
      laurentVar A := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, specLaurentIso_hom_snd,
    unitsEquivHomGm_appTop_gmCoord]

/-- Evaluation at `z = 1` is the section `z = 1`.

Blueprint: `lem:geo-products`. -/
lemma specMap_laurentAlgLift_one_comp_specLaurentIso_hom :
    specMap (laurentAlgLift (𝟙 A) 1) ≫ (specLaurentIso A).hom = oneSection (spec A) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, specLaurentIso_hom_fst, ← specMap_comp, oneSection_fst,
      laurentAlgC_comp_laurentAlgLift]
    exact specMap_id _
  · apply hom_ext_gm
    rw [Category.assoc, specLaurentIso_hom_snd, oneSection, lift_snd, Over.comp_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, unitsEquivHomGm_appTop_gmCoord,
      unitsEquivHomGm_appTop_gmCoord, Units.coe_map, Units.val_one]
    change (specMap _).left.appTop ((Scheme.ΓSpecIso _).inv _) = 1
    rw [specMap_left_appTop_ΓSpecIso_inv]
    exact (congrArg _ (laurentAlgLift_T _ _)).trans (map_one _)

/-- The inclusion `A[z] → A[z, z⁻¹]` is the open immersion `Spec A ×_S 𝔾ₘ → Spec A ×_S 𝔸¹`:
`Spec` of the open map of the standard pair of `A`.

Blueprint: `lem:geo-products`. -/
@[reassoc]
lemma specMap_polynomialAlgToLaurent_comp_specPolynomialIso_hom :
    specMap (polynomialAlgToLaurent A) ≫ (specPolynomialIso A).hom =
      (specLaurentIso A).hom ≫ (spec A ◁ gmToAffineLine k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specPolynomialIso_hom_fst, whiskerLeft_fst,
      specLaurentIso_hom_fst, ← specMap_comp, polynomialAlgC_comp_polynomialAlgToLaurent]
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, Category.assoc, whiskerLeft_snd, homAffineLineEquiv_comp,
      specPolynomialIso_hom_snd, Equiv.apply_symm_apply, specMap_left_appTop_ΓSpecIso_inv,
      ← Category.assoc, homAffineLineEquiv_comp, gmToAffineLine, Equiv.apply_symm_apply,
      specLaurentIso_hom_snd, unitsEquivHomGm_appTop_gmCoord]
    exact congrArg _ (polynomialAlgToLaurent_X (A := A))

/-- Naturality of `specLaurentIso` in `A`. -/
@[reassoc]
lemma specMap_laurentAlgMap_comp_specLaurentIso_hom {B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    specMap (laurentAlgLift (φ ≫ laurentAlgC B) (laurentPolynomialT (R := B))) ≫
        (specLaurentIso A).hom =
      (specLaurentIso B).hom ≫ (specMap φ ▷ gm k) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, specLaurentIso_hom_fst, whiskerRight_fst,
      specLaurentIso_hom_fst_assoc, ← specMap_comp, ← specMap_comp,
      laurentAlgC_comp_laurentAlgLift]
  · apply hom_ext_gm
    rw [Category.assoc, Category.assoc, whiskerRight_snd, specLaurentIso_hom_snd,
      specLaurentIso_hom_snd, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      unitsEquivHomGm_appTop_gmCoord, unitsEquivHomGm_appTop_gmCoord]
    change (specMap _).left.appTop ((Scheme.ΓSpecIso _).inv _) = _
    rw [specMap_left_appTop_ΓSpecIso_inv]
    exact congrArg _ (laurentAlgLift_T _ _)

end Spec

/-! ### Smooth algebras and domains -/

namespace SmoothDomain

variable (D : SmoothDomain k)

/-- The section `z = 0` of `X ×_S 𝔸¹_S → X`, in a domain. -/
def zeroSection (X : D.Obj) : X ⟶ D.prodAffineLine X :=
  ObjectProperty.homMk (Geometric.zeroSection X.obj)

/-- The section `z = 1` of `X ×_S 𝔾ₘ → X`, in a domain. -/
def oneSection (X : D.Obj) : X ⟶ D.prodGm X := ObjectProperty.homMk (Geometric.oneSection X.obj)

/-- The open immersion `X ×_S 𝔾ₘ → X ×_S 𝔸¹_S`, in a domain. -/
def prodGmToProdAffineLine (X : D.Obj) : D.prodGm X ⟶ D.prodAffineLine X :=
  ObjectProperty.homMk (X.obj ◁ Geometric.gmToAffineLine k)

/-- The map `X ×_S 𝔸¹_S → Y ×_S 𝔸¹_S` of `f : X ⟶ Y`, in a domain. -/
def prodAffineLineMap {X Y : D.Obj} (f : X ⟶ Y) : D.prodAffineLine X ⟶ D.prodAffineLine Y :=
  ObjectProperty.homMk (f.hom ▷ Geometric.affineLine k)

/-- The map `X ×_S 𝔾ₘ → Y ×_S 𝔾ₘ` of `f : X ⟶ Y`, in a domain. -/
def prodGmMap {X Y : D.Obj} (f : X ⟶ Y) : D.prodGm X ⟶ D.prodGm Y :=
  ObjectProperty.homMk (f.hom ▷ Geometric.gm k)

variable (A : SmoothAlg.{u} k)

/-- `Spec A[z] ≅ Spec A ×_S 𝔸¹_S` for a smooth `k`-algebra `A`, in a domain `D`: the general
`Geometric.specPolynomialIso`, since `SmoothAlg.polynomial A` has underlying algebra `A[z]`.

Blueprint: `lem:geo-products`. -/
def specPolynomialIso : D.spec (SmoothAlg.polynomial A) ≅ D.prodAffineLine (D.spec A) :=
  ObjectProperty.isoMk _ (Geometric.specPolynomialIso A.obj)

/-- `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ` for a smooth `k`-algebra `A`, in a domain `D`.

Blueprint: `lem:geo-products`. -/
def specLaurentIso : D.spec (SmoothAlg.laurent A) ≅ D.prodGm (D.spec A) :=
  ObjectProperty.isoMk _ (Geometric.specLaurentIso A.obj)

@[simp] lemma specPolynomialIso_hom_hom :
    (D.specPolynomialIso A).hom.hom = (Geometric.specPolynomialIso A.obj).hom := rfl

@[simp] lemma specLaurentIso_hom_hom :
    (D.specLaurentIso A).hom.hom = (Geometric.specLaurentIso A.obj).hom := rfl

/-- Under `Spec A[z] ≅ Spec A ×_S 𝔸¹_S`, the projection is `Spec` of the inclusion of constants:
the polynomial axiom of an algebraic theory is the affine-line axiom of a geometric one. -/
@[reassoc (attr := simp)]
lemma specPolynomialIso_hom_prodAffineLineFst :
    (D.specPolynomialIso A).hom ≫ D.prodAffineLineFst (D.spec A) =
      (D.specFunctor.map (SmoothAlg.polynomialC A)).unop :=
  ObjectProperty.hom_ext _ (Geometric.specPolynomialIso_hom_fst A.obj)

/-- Under `Spec A[z, z⁻¹] ≅ Spec A ×_S 𝔾ₘ`, the projection is `Spec` of the inclusion of
constants. -/
@[reassoc (attr := simp)]
lemma specLaurentIso_hom_prodGmFst :
    (D.specLaurentIso A).hom ≫ D.prodGmFst (D.spec A) =
      (D.specFunctor.map (SmoothAlg.laurentC A)).unop :=
  ObjectProperty.hom_ext _ (Geometric.specLaurentIso_hom_fst A.obj)

/-- The closed map `A[z] → A` of the standard pair is the zero section. -/
@[reassoc]
lemma specFunctor_map_polynomialLift_zero_comp_specPolynomialIso_hom :
    (D.specFunctor.map (SmoothAlg.polynomialLift (𝟙 A) 0)).unop ≫ (D.specPolynomialIso A).hom =
      D.zeroSection (D.spec A) :=
  ObjectProperty.hom_ext _ (specMap_polynomialAlgLift_zero_comp_specPolynomialIso_hom A.obj)

/-- Evaluation at `z = 1` is the section `z = 1`. -/
@[reassoc]
lemma specFunctor_map_laurentSection_comp_specLaurentIso_hom :
    (D.specFunctor.map (SmoothAlg.laurentSection A)).unop ≫ (D.specLaurentIso A).hom =
      D.oneSection (D.spec A) :=
  ObjectProperty.hom_ext _ (specMap_laurentAlgLift_one_comp_specLaurentIso_hom A.obj)

/-- The open map `A[z] → A[z, z⁻¹]` of the standard pair is the open immersion. -/
@[reassoc]
lemma specFunctor_map_polynomialToLaurent_comp_specPolynomialIso_hom :
    (D.specFunctor.map (SmoothAlg.polynomialToLaurent A)).unop ≫ (D.specPolynomialIso A).hom =
      (D.specLaurentIso A).hom ≫ D.prodGmToProdAffineLine (D.spec A) :=
  ObjectProperty.hom_ext _ (specMap_polynomialAlgToLaurent_comp_specPolynomialIso_hom A.obj)

/-- Naturality of `specPolynomialIso` in the smooth algebra. -/
@[reassoc]
lemma specFunctor_map_polynomialMap_comp_specPolynomialIso_hom {B : SmoothAlg.{u} k}
    (φ : A ⟶ B) :
    (D.specFunctor.map (SmoothAlg.polynomialLift (φ ≫ SmoothAlg.polynomialC B)
        (SmoothAlg.polynomialX B))).unop ≫ (D.specPolynomialIso A).hom =
      (D.specPolynomialIso B).hom ≫ D.prodAffineLineMap (D.specFunctor.map φ).unop :=
  ObjectProperty.hom_ext _ (specMap_polynomialAlgMap_comp_specPolynomialIso_hom A.obj φ.hom)

/-- Naturality of `specLaurentIso` in the smooth algebra. -/
@[reassoc]
lemma specFunctor_map_laurentMap_comp_specLaurentIso_hom {B : SmoothAlg.{u} k} (φ : A ⟶ B) :
    (D.specFunctor.map (SmoothAlg.laurentLift (φ ≫ SmoothAlg.laurentC B)
        (SmoothAlg.laurentT B))).unop ≫ (D.specLaurentIso A).hom =
      (D.specLaurentIso B).hom ≫ D.prodGmMap (D.specFunctor.map φ).unop :=
  ObjectProperty.hom_ext _ (specMap_laurentAlgMap_comp_specLaurentIso_hom A.obj φ.hom)

end SmoothDomain

end OrlikSolomon.Geometric
