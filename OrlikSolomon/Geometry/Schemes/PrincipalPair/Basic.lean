/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Certificates

/-!
# Geometric divisor pairs

This file defines the principal smooth divisor pairs of the geometric refactor blueprint
(`def:geo-divisor-pair`), their morphisms in the geometric direction (`def:geo-pair-hom`), and
proves their Cartesian characterization (`thm:geo-cartesian`).

## Main definitions

* `Geometric.DivisorPair D`: objects `X`, `D`, `U` of a domain, maps `i : D ⟶ X` and `j : U ⟶ X`,
  and a global function `f` on `X`, with data-free certificates: `f` is regular, `i` is a closed
  immersion with kernel `f 𝒪_X`, and `j` is an open immersion onto `X.basicOpen f`.
* `DivisorPair.Hom`: scheme maps of ambients, divisors and open parts commuting with `i` and `j`,
  such that `g_X^* f_Q` is a unit multiple of `f_P`. The multiplier lives on the source and is not
  part of the data. Pairs and these morphisms form a category.
* `DivisorPair.homOfAmbient`: a map of ambients satisfying the equation condition extends uniquely
  (`DivisorPair.hom_ext`) to a morphism of pairs.
* `DivisorPair.eqnUnit`: the equation as a unit on the open part.
* `DivisorPair.closedLift`, `DivisorPair.complLift`: the universal properties of the divisor and of
  the open part.
* `DivisorPair.isoMk`, `DivisorPair.withEqn`, `DivisorPair.withEqnIso`: isomorphisms of pairs, and
  changing the equation by a unit.
* `DivisorPair.ofLE`, `DivisorPair.functorOfLE`: a pair in a smaller domain is a pair in a larger
  one.

## Main results

* `DivisorPair.associated_iff_ker_pullback_fst`, `DivisorPair.associated_iff_isPullback`: the
  equation condition holds exactly when `D_P` is the scheme-theoretic preimage `X_P ×_{X_Q} D_Q`,
  on every scheme, affine or not (`thm:geo-cartesian`).
* `DivisorPair.Hom.isPullback_closed`, `DivisorPair.Hom.isPullback_compl`: both squares of a
  morphism of pairs are Cartesian.
* `DivisorPair.Hom.isRegularSection_appTop`: the pulled-back equation is regular, so the closed
  square is Tor-independent.
* `DivisorPair.isEmpty_closed_of_isUnit`, `DivisorPair.isIso_j_of_isUnit`: a unit equation cuts out
  the empty divisor, and its open part is the whole ambient scheme.

## Implementation notes

Morphisms of geometric pairs run in the geometric direction, opposite to the algebraic
`OrlikSolomon.DivisorPair.Hom`; `Geometry/Schemes/PrincipalPair/Duality` proves the
anti-equivalence.
Pairs built from named objects, such as `withEqn` and `ofLE`, are `@[implicit_reducible] def`s, and
the equations giving their objects are not `simp` lemmas: see "Schemes, domains and affine duality"
and "Principal pairs" in `docs/ARCHITECTURE.md`.

A unit equation, giving an empty divisor, and an empty ambient scheme are allowed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k] {D : SmoothDomain k}

namespace SmoothDomain

/-- Pullback of global functions along a composite in a domain. -/
lemma appTop_comp_apply {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z.obj.left, ⊤)) :
    (f ≫ g).hom.left.appTop x = f.hom.left.appTop (g.hom.left.appTop x) := by
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

/-- Pullback of global functions along an identity in a domain. -/
lemma appTop_id_apply (X : D.Obj) (x : Γ(X.obj.left, ⊤)) :
    (𝟙 X : X ⟶ X).hom.left.appTop x = x := by
  rw [ObjectProperty.FullSubcategory.id_hom, Over.id_left, Scheme.Hom.id_appTop,
    CommRingCat.id_apply]

end SmoothDomain

/-- A principal smooth divisor pair in a domain `D`: objects `X = ambient`, `D = closed` and
`U = compl` of `D`, maps `i : D ⟶ X` and `j : U ⟶ X`, and a global function `f = eqn` on `X`, such
that

* multiplication by `f` on `𝒪_X` is injective (`IsRegularSection`);
* `i` identifies `D` with the closed subscheme `Z_X(f)`: it is a closed immersion with kernel
  `f 𝒪_X`;
* `j` identifies `U` with the open subscheme `X_f`: it is an open immersion onto `X.basicOpen f`.

The certificates are propositions, so named objects such as actual arrangement complements form a
pair without a literal quotient or restriction. Smoothness of the three schemes is their membership
in `D`. A unit `f` and an empty `X` are allowed.

Blueprint: `def:geo-divisor-pair`. -/
structure DivisorPair (D : SmoothDomain k) where
  /-- The ambient scheme `X`. -/
  ambient : D.Obj
  /-- The divisor `D`. -/
  closed : D.Obj
  /-- The open complement `U`. -/
  compl : D.Obj
  /-- The closed immersion `D → X`. -/
  i : closed ⟶ ambient
  /-- The open immersion `U → X`. -/
  j : compl ⟶ ambient
  /-- The equation of the divisor. -/
  eqn : Γ(ambient.obj.left, ⊤)
  /-- The equation is regular: multiplication by it on `𝒪_X` is injective. -/
  isRegularSection_eqn : IsRegularSection eqn
  /-- The map `i` is a closed immersion. -/
  [isClosedImmersion_i : IsClosedImmersion i.hom.left]
  /-- The kernel of `i` is the ideal sheaf generated by `eqn`, so `D` is the zero scheme of
  `eqn`. -/
  ker_i : i.hom.left.ker = principalIdealSheaf eqn
  /-- The map `j` is an open immersion. -/
  [isOpenImmersion_j : IsOpenImmersion j.hom.left]
  /-- The image of `j` is the basic open of `eqn`, so `U` is the complement of the divisor. -/
  opensRange_j : j.hom.left.opensRange = ambient.obj.left.basicOpen eqn

namespace DivisorPair

attribute [instance] isClosedImmersion_i isOpenImmersion_j

section Basic

variable (P : DivisorPair D) {T : D.Obj}

/-- The equation vanishes on the divisor. -/
@[simp] lemma i_appTop_eqn : P.i.hom.left.appTop P.eqn = 0 :=
  appTop_eq_zero_of_ker_eq P.eqn P.ker_i

/-- The equation is a unit on the open part. -/
lemma isUnit_j_appTop_eqn : IsUnit (P.j.hom.left.appTop P.eqn) :=
  isUnit_appTop_of_opensRange_eq P.eqn P.opensRange_j

/-- The equation of the divisor, as a unit on the open part.

Blueprint: `thm:geo-pair-duality`. -/
def eqnUnit : Γ(P.compl.obj.left, ⊤)ˣ := P.isUnit_j_appTop_eqn.unit

@[simp] lemma coe_eqnUnit : (P.eqnUnit : Γ(P.compl.obj.left, ⊤)) = P.j.hom.left.appTop P.eqn :=
  rfl

instance : Mono P.i :=
  ⟨fun _ _ e ↦ ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((cancel_mono P.i.hom.left).1 (congrArg (fun φ ↦ φ.hom.left) e)))⟩

instance : Mono P.j :=
  ⟨fun _ _ e ↦ ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((cancel_mono P.j.hom.left).1 (congrArg (fun φ ↦ φ.hom.left) e)))⟩

/-- A pair with a unit equation has empty divisor. -/
lemma isEmpty_closed_of_isUnit (h : IsUnit P.eqn) : IsEmpty P.closed.obj.left := by
  rw [← Scheme.Hom.ker_eq_top_iff_isEmpty P.i.hom.left, P.ker_i,
    principalIdealSheaf_eq_top_of_isUnit _ h]

/-- A pair with a unit equation has `j` an isomorphism onto the ambient scheme. -/
lemma isIso_j_of_isUnit (h : IsUnit P.eqn) : IsIso P.j.hom.left :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [P.opensRange_j, Scheme.basicOpen_of_isUnit _ h])

variable {P}

/-- A map pulling the equation back to zero has kernel containing that of `i`. -/
lemma ker_i_le_ker {g : T ⟶ P.ambient} (hg : g.hom.left.appTop P.eqn = 0) :
    P.i.hom.left.ker ≤ g.hom.left.ker := by
  rw [P.ker_i]
  exact principalIdealSheaf_le_ker hg

/-- A map pulling the equation back to a unit lands in the image of `j`. -/
lemma range_subset_range_j {g : T ⟶ P.ambient} (hg : IsUnit (g.hom.left.appTop P.eqn)) :
    Set.range g.hom.left ⊆ Set.range P.j.hom.left :=
  (range_subset_range_iff_of_opensRange_eq P.opensRange_j _).2 hg

variable (P) in
/-- The universal property of the divisor: a map pulling the equation back to zero factors through
`i`, uniquely since `i` is a monomorphism. -/
def closedLift (g : T ⟶ P.ambient) (hg : g.hom.left.appTop P.eqn = 0) : T ⟶ P.closed :=
  ObjectProperty.homMk <| Over.homMk (IsClosedImmersion.lift _ _ (ker_i_le_ker hg)) <| by
    rw [← Over.w P.i.hom, IsClosedImmersion.lift_fac_assoc, Over.w g.hom]

@[reassoc (attr := simp)]
lemma closedLift_i (g : T ⟶ P.ambient) (hg : g.hom.left.appTop P.eqn = 0) :
    P.closedLift g hg ≫ P.i = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _))

variable (P) in
/-- The universal property of the open part: a map pulling the equation back to a unit factors
through `j`, uniquely since `j` is a monomorphism. -/
def complLift (g : T ⟶ P.ambient) (hg : IsUnit (g.hom.left.appTop P.eqn)) : T ⟶ P.compl :=
  ObjectProperty.homMk <| Over.homMk (IsOpenImmersion.lift _ _ (range_subset_range_j hg)) <| by
    rw [← Over.w P.j.hom, IsOpenImmersion.lift_fac_assoc, Over.w g.hom]

@[reassoc (attr := simp)]
lemma complLift_j (g : T ⟶ P.ambient) (hg : IsUnit (g.hom.left.appTop P.eqn)) :
    P.complLift g hg ≫ P.j = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _))

end Basic

/-! ### Morphisms in the geometric direction -/

/-- A morphism `g : P ⟶ Q` of divisor pairs: scheme maps `g_X : X_P ⟶ X_Q`, `g_D : D_P ⟶ D_Q` and
`g_U : U_P ⟶ U_Q` with `g_X ∘ i_P = i_Q ∘ g_D` and `g_X ∘ j_P = j_Q ∘ g_U`, such that `g_X^* f_Q` is
a unit multiple of `f_P` (`exists_unit_mul`). The multiplier is a unit on the source `X_P`, which is
the target of the ring map, and only its existence is required.

These morphisms run in the geometric direction, opposite to the algebraic
`OrlikSolomon.DivisorPair.Hom`. By `thm:geo-cartesian` the equation condition says that `D_P` is the
scheme-theoretic preimage of `D_Q`, and it asks for no flatness of `g_X`. The maps `g_D` and `g_U`
are determined by `g_X` (`hom_ext`, `homOfAmbient`).

Blueprint: `def:geo-pair-hom`. -/
@[ext]
structure Hom (P Q : DivisorPair D) where
  /-- The map of ambient schemes. -/
  ambient : P.ambient ⟶ Q.ambient
  /-- The map of divisors. -/
  closed : P.closed ⟶ Q.closed
  /-- The map of open parts. -/
  compl : P.compl ⟶ Q.compl
  /-- The maps of divisors and of ambient schemes commute with `i`. -/
  i_comp : P.i ≫ ambient = closed ≫ Q.i
  /-- The maps of open parts and of ambient schemes commute with `j`. -/
  j_comp : P.j ≫ ambient = compl ≫ Q.j
  /-- The ambient map pulls `Q.eqn` back to a unit multiple of `P.eqn`. This excludes `z ↦ x²`,
  which commutes with `i` and `j` but pulls back the reduced point to the doubled point. -/
  associated_eqn : Associated (ambient.hom.left.appTop Q.eqn) P.eqn

attribute [reassoc] Hom.i_comp Hom.j_comp

/-- Divisor pairs in `D` and their morphisms form a category, with identities and composition
those of schemes. -/
instance : Category (DivisorPair D) where
  Hom := Hom
  id P :=
    { ambient := 𝟙 _
      closed := 𝟙 _
      compl := 𝟙 _
      i_comp := by simp
      j_comp := by simp
      associated_eqn := by rw [SmoothDomain.appTop_id_apply] }
  comp {P Q R} f g :=
    { ambient := f.ambient ≫ g.ambient
      closed := f.closed ≫ g.closed
      compl := f.compl ≫ g.compl
      i_comp := by rw [f.i_comp_assoc, g.i_comp, Category.assoc]
      j_comp := by rw [f.j_comp_assoc, g.j_comp, Category.assoc]
      associated_eqn := by
        rw [SmoothDomain.appTop_comp_apply]
        exact (g.associated_eqn.map f.ambient.hom.left.appTop.hom).trans f.associated_eqn }

variable {P Q R : DivisorPair D}

@[simp] lemma id_ambient : (𝟙 P : P ⟶ P).ambient = 𝟙 P.ambient := rfl
@[simp] lemma id_closed : (𝟙 P : P ⟶ P).closed = 𝟙 P.closed := rfl
@[simp] lemma id_compl : (𝟙 P : P ⟶ P).compl = 𝟙 P.compl := rfl

@[simp] lemma comp_ambient (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).ambient = f.ambient ≫ g.ambient := rfl
@[simp] lemma comp_closed (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).closed = f.closed ≫ g.closed := rfl
@[simp] lemma comp_compl (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).compl = f.compl ≫ g.compl := rfl

/-- A morphism of pairs is determined by its ambient map, because `i` and `j` are monomorphisms. -/
@[ext] lemma hom_ext {f g : P ⟶ Q} (h : f.ambient = g.ambient) : f = g := by
  refine Hom.ext h ?_ ?_
  · rw [← cancel_mono Q.i, ← f.i_comp, ← g.i_comp, h]
  · rw [← cancel_mono Q.j, ← f.j_comp, ← g.j_comp, h]

/-- The equation condition in the form of the blueprint: `g_X^* f_Q = u f_P` for a unit `u` on the
source `X_P`. Modulo the ideals of the divisors, `u` is the conormal map, which is therefore an
isomorphism of line bundles.

Blueprint: `def:geo-pair-hom`, `thm:geo-cartesian`. -/
lemma Hom.exists_unit_mul (g : P ⟶ Q) :
    ∃ u : Γ(P.ambient.obj.left, ⊤)ˣ, g.ambient.hom.left.appTop Q.eqn = u * P.eqn := by
  obtain ⟨u, hu⟩ := g.associated_eqn.symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- A map of ambients satisfying the equation condition restricts to zero on the divisor. -/
lemma closedLift_aux (g : P.ambient ⟶ Q.ambient)
    (hg : Associated (g.hom.left.appTop Q.eqn) P.eqn) :
    (P.i ≫ g).hom.left.appTop Q.eqn = 0 := by
  rw [SmoothDomain.appTop_comp_apply, ← zero_dvd_iff, ← P.i_appTop_eqn]
  exact map_dvd P.i.hom.left.appTop.hom hg.symm.dvd

/-- A map of ambients satisfying the equation condition restricts to a unit on the open part. -/
lemma complLift_aux (g : P.ambient ⟶ Q.ambient)
    (hg : Associated (g.hom.left.appTop Q.eqn) P.eqn) :
    IsUnit ((P.j ≫ g).hom.left.appTop Q.eqn) := by
  rw [SmoothDomain.appTop_comp_apply]
  exact (hg.map P.j.hom.left.appTop.hom).isUnit_iff.2 P.isUnit_j_appTop_eqn

/-- A map of ambient schemes pulling `Q.eqn` back to a unit multiple of `P.eqn` extends to a
morphism of pairs, uniquely by `hom_ext`. The maps of divisors and of open parts come from the
universal properties of the zero scheme and of the basic open.

Blueprint: `def:geo-pair-hom`. -/
def homOfAmbient (g : P.ambient ⟶ Q.ambient)
    (hg : Associated (g.hom.left.appTop Q.eqn) P.eqn) : P ⟶ Q where
  ambient := g
  closed := Q.closedLift (P.i ≫ g) (closedLift_aux g hg)
  compl := Q.complLift (P.j ≫ g) (complLift_aux g hg)
  i_comp := (Q.closedLift_i _ _).symm
  j_comp := (Q.complLift_j _ _).symm
  associated_eqn := hg

@[simp] lemma homOfAmbient_ambient (g : P.ambient ⟶ Q.ambient)
    (hg : Associated (g.hom.left.appTop Q.eqn) P.eqn) : (homOfAmbient g hg).ambient = g := rfl

/-- Every morphism of pairs is `homOfAmbient` of its ambient map. -/
lemma eq_homOfAmbient (g : P ⟶ Q) : g = homOfAmbient g.ambient g.associated_eqn := hom_ext rfl

/-! ### Isomorphisms and changes of equation -/

/-- An isomorphism of pairs from isomorphisms of the three schemes compatible with `i`, `j` and
the equations. -/
def isoMk (eX : P.ambient ≅ Q.ambient) (eD : P.closed ≅ Q.closed) (eU : P.compl ≅ Q.compl)
    (hi : P.i ≫ eX.hom = eD.hom ≫ Q.i) (hj : P.j ≫ eX.hom = eU.hom ≫ Q.j)
    (he : Associated (eX.hom.hom.left.appTop Q.eqn) P.eqn) : P ≅ Q where
  hom :=
    { ambient := eX.hom
      closed := eD.hom
      compl := eU.hom
      i_comp := hi
      j_comp := hj
      associated_eqn := he }
  inv :=
    { ambient := eX.inv
      closed := eD.inv
      compl := eU.inv
      i_comp := by rw [Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
      j_comp := by rw [Iso.comp_inv_eq, Category.assoc, hj, Iso.inv_hom_id_assoc]
      associated_eqn := by
        have h1 : eX.inv.hom.left.appTop (eX.hom.hom.left.appTop Q.eqn) = Q.eqn := by
          rw [← SmoothDomain.appTop_comp_apply, Iso.inv_hom_id, SmoothDomain.appTop_id_apply]
        have h := he.map eX.inv.hom.left.appTop.hom
        change Associated (eX.inv.hom.left.appTop (eX.hom.hom.left.appTop Q.eqn))
          (eX.inv.hom.left.appTop P.eqn) at h
        rw [h1] at h
        exact h.symm }
  hom_inv_id := hom_ext eX.hom_inv_id
  inv_hom_id := hom_ext eX.inv_hom_id

section IsoMk

variable (eX : P.ambient ≅ Q.ambient) (eD : P.closed ≅ Q.closed) (eU : P.compl ≅ Q.compl)
    (hi : P.i ≫ eX.hom = eD.hom ≫ Q.i) (hj : P.j ≫ eX.hom = eU.hom ≫ Q.j)
    (he : Associated (eX.hom.hom.left.appTop Q.eqn) P.eqn)

@[simp] lemma isoMk_hom_ambient : (isoMk eX eD eU hi hj he).hom.ambient = eX.hom := rfl
@[simp] lemma isoMk_hom_closed : (isoMk eX eD eU hi hj he).hom.closed = eD.hom := rfl
@[simp] lemma isoMk_hom_compl : (isoMk eX eD eU hi hj he).hom.compl = eU.hom := rfl
@[simp] lemma isoMk_inv_ambient : (isoMk eX eD eU hi hj he).inv.ambient = eX.inv := rfl
@[simp] lemma isoMk_inv_closed : (isoMk eX eD eU hi hj he).inv.closed = eD.inv := rfl
@[simp] lemma isoMk_inv_compl : (isoMk eX eD eU hi hj he).inv.compl = eU.inv := rfl

end IsoMk

variable (P) in
/-- The pair `P` with its equation replaced by a unit multiple `f` of `P.eqn`. The certificates are
unchanged: unit multiples generate the same ideal sheaf and have the same basic open. -/
@[implicit_reducible]
def withEqn (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) : DivisorPair D where
  ambient := P.ambient
  closed := P.closed
  compl := P.compl
  i := P.i
  j := P.j
  eqn := f
  isRegularSection_eqn := P.isRegularSection_eqn.of_associated hf
  ker_i := P.ker_i.trans (principalIdealSheaf_eq_of_associated hf).symm
  opensRange_j := P.opensRange_j.trans (basicOpen_eq_of_associated hf).symm

section WithEqn

variable (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn)

lemma withEqn_ambient : (P.withEqn f hf).ambient = P.ambient := rfl
lemma withEqn_closed : (P.withEqn f hf).closed = P.closed := rfl
lemma withEqn_compl : (P.withEqn f hf).compl = P.compl := rfl
@[simp] lemma withEqn_i : (P.withEqn f hf).i = P.i := rfl
@[simp] lemma withEqn_j : (P.withEqn f hf).j = P.j := rfl
@[simp] lemma withEqn_eqn : (P.withEqn f hf).eqn = f := rfl

variable (P) in
/-- Changing the equation by a unit gives an isomorphic pair, by the identity maps. This is the
change of equation of `thm:geo-pair-duality`; cohomological maps of a pair are therefore
independent of the chosen equation.

Blueprint: `thm:geo-pair-duality`. -/
def withEqnIso : P.withEqn f hf ≅ P :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by rw [Iso.refl_hom, SmoothDomain.appTop_id_apply]; exact hf.symm)

@[simp] lemma withEqnIso_hom_ambient : (P.withEqnIso f hf).hom.ambient = 𝟙 P.ambient := rfl
@[simp] lemma withEqnIso_hom_closed : (P.withEqnIso f hf).hom.closed = 𝟙 P.closed := rfl
@[simp] lemma withEqnIso_hom_compl : (P.withEqnIso f hf).hom.compl = 𝟙 P.compl := rfl
@[simp] lemma withEqnIso_inv_ambient : (P.withEqnIso f hf).inv.ambient = 𝟙 P.ambient := rfl
@[simp] lemma withEqnIso_inv_closed : (P.withEqnIso f hf).inv.closed = 𝟙 P.closed := rfl
@[simp] lemma withEqnIso_inv_compl : (P.withEqnIso f hf).inv.compl = 𝟙 P.compl := rfl

end WithEqn

/-! ### Change of domain -/

section OfLE

variable {D₁ D₂ : SmoothDomain k} (h : D₁ ≤ D₂)

/-- A pair in a domain `D₁` is a pair in any larger domain `D₂`, with the same schemes, maps and
equation. -/
@[implicit_reducible]
def ofLE (P : DivisorPair D₁) : DivisorPair D₂ where
  ambient := (ObjectProperty.ιOfLE h).obj P.ambient
  closed := (ObjectProperty.ιOfLE h).obj P.closed
  compl := (ObjectProperty.ιOfLE h).obj P.compl
  i := (ObjectProperty.ιOfLE h).map P.i
  j := (ObjectProperty.ιOfLE h).map P.j
  eqn := P.eqn
  isRegularSection_eqn := P.isRegularSection_eqn
  isClosedImmersion_i := P.isClosedImmersion_i
  ker_i := P.ker_i
  isOpenImmersion_j := P.isOpenImmersion_j
  opensRange_j := P.opensRange_j

variable (P : DivisorPair D₁)

lemma ofLE_ambient : (ofLE h P).ambient = (ObjectProperty.ιOfLE h).obj P.ambient := rfl
lemma ofLE_closed : (ofLE h P).closed = (ObjectProperty.ιOfLE h).obj P.closed := rfl
lemma ofLE_compl : (ofLE h P).compl = (ObjectProperty.ιOfLE h).obj P.compl := rfl
@[simp] lemma ofLE_i : (ofLE h P).i = (ObjectProperty.ιOfLE h).map P.i := rfl
@[simp] lemma ofLE_j : (ofLE h P).j = (ObjectProperty.ιOfLE h).map P.j := rfl
@[simp] lemma ofLE_eqn : (ofLE h P).eqn = P.eqn := rfl

/-- Pairs and their morphisms in `D₁` are pairs and morphisms in a larger domain `D₂`. -/
@[simps obj]
def functorOfLE : DivisorPair D₁ ⥤ DivisorPair D₂ where
  obj := ofLE h
  map g :=
    { ambient := (ObjectProperty.ιOfLE h).map g.ambient
      closed := (ObjectProperty.ιOfLE h).map g.closed
      compl := (ObjectProperty.ιOfLE h).map g.compl
      i_comp := by rw [ofLE_i, ofLE_i, ← Functor.map_comp, g.i_comp, Functor.map_comp]
      j_comp := by rw [ofLE_j, ofLE_j, ← Functor.map_comp, g.j_comp, Functor.map_comp]
      associated_eqn := g.associated_eqn }

@[simp] lemma functorOfLE_map_ambient {P Q : DivisorPair D₁} (g : P ⟶ Q) :
    ((functorOfLE h).map g).ambient = (ObjectProperty.ιOfLE h).map g.ambient := rfl

end OfLE

/-! ### The Cartesian characterization -/

section Cartesian

variable (g : P.ambient ⟶ Q.ambient)

/-- The scheme-theoretic preimage `X_P ×_{X_Q} D_Q` of the divisor of `Q` is the zero scheme of
`g^* f_Q`. -/
lemma ker_pullback_fst_i :
    (pullback.fst g.hom.left Q.i.hom.left).ker = principalIdealSheaf (g.hom.left.appTop Q.eqn) :=
  ker_pullback_fst_of_ker_eq Q.ker_i _

/-- **Cartesian characterization.** For pairs `P` and `Q` and a map `g : X_P ⟶ X_Q`, the pulled-back
equation `g^* f_Q` is a unit multiple of `f_P` exactly when `D_P` and `X_P ×_{X_Q} D_Q` are the same
closed subscheme of `X_P`, that is, when their ideal sheaves agree. This holds on every `X_P`,
affine or not: local ratios glue to a global unit by regularity of `f_P`. Equality of the
underlying closed sets would not suffice.

Blueprint: `thm:geo-cartesian`. -/
theorem associated_iff_ker_pullback_fst :
    Associated (g.hom.left.appTop Q.eqn) P.eqn ↔
      (pullback.fst g.hom.left Q.i.hom.left).ker = P.i.hom.left.ker := by
  rw [ker_pullback_fst_i, P.ker_i, associated_iff_principalIdealSheaf_eq P.isRegularSection_eqn]

/-- **Cartesian characterization**, as a pullback square: `g^* f_Q` is a unit multiple of `f_P`
exactly when `D_P ≅ X_P ×_{X_Q} D_Q` over `X_P`.

Blueprint: `thm:geo-cartesian`. -/
theorem associated_iff_isPullback :
    Associated (g.hom.left.appTop Q.eqn) P.eqn ↔
      ∃ gD : P.closed.obj.left ⟶ Q.closed.obj.left,
        IsPullback P.i.hom.left gD g.hom.left Q.i.hom.left := by
  rw [associated_iff_ker_pullback_fst]
  constructor
  · intro h
    let e := IsClosedImmersion.lift (pullback.fst g.hom.left Q.i.hom.left) P.i.hom.left h.le
    have : IsIso e := IsClosedImmersion.isIso_lift _ _ h
    have he : e ≫ pullback.fst _ _ = P.i.hom.left := IsClosedImmersion.lift_fac _ _ _
    refine ⟨e ≫ pullback.snd _ _, IsPullback.of_iso_pullback ⟨?_⟩ (asIso e) he rfl⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he]
  · rintro ⟨gD, hgD⟩
    rw [← hgD.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- The closed square of a morphism of pairs is Cartesian: `D_P = X_P ×_{X_Q} D_Q`.

Blueprint: `thm:geo-cartesian`. -/
theorem Hom.isPullback_closed (g : P ⟶ Q) :
    IsPullback P.i.hom.left g.closed.hom.left g.ambient.hom.left Q.i.hom.left := by
  obtain ⟨gD, hgD⟩ := (associated_iff_isPullback g.ambient).1 g.associated_eqn
  have : gD = g.closed.hom.left := by
    rw [← cancel_mono Q.i.hom.left, ← hgD.w, ← Over.comp_left, ← Over.comp_left,
      ← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      g.i_comp]
  exact this ▸ hgD

/-- The open square of a morphism of pairs is Cartesian: `U_P = X_P ×_{X_Q} U_Q`.

Blueprint: `thm:geo-cartesian`. -/
theorem Hom.isPullback_compl (g : P ⟶ Q) :
    IsPullback P.j.hom.left g.compl.hom.left g.ambient.hom.left Q.j.hom.left := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · rw [← Over.comp_left, ← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom,
      ← ObjectProperty.FullSubcategory.comp_hom, g.j_comp]
  · rw [Q.opensRange_j, Scheme.preimage_basicOpen_top, P.opensRange_j]
    exact basicOpen_eq_of_associated g.associated_eqn

/-- The pullback of the equation along a morphism of pairs is regular. So the resolution
`0 → 𝒪 → 𝒪 → 𝒪_{D_Q} → 0` given by `f_Q` stays exact after pullback to `X_P`, which is the
Tor-independence of the closed square, with no flatness of `g_X`.

Blueprint: `thm:geo-cartesian`. -/
theorem Hom.isRegularSection_appTop (g : P ⟶ Q) :
    IsRegularSection (g.ambient.hom.left.appTop Q.eqn) :=
  P.isRegularSection_eqn.of_associated g.associated_eqn

end Cartesian

end DivisorPair

end OrlikSolomon.Geometric
