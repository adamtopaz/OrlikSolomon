/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Smooth algebras and divisor pairs

This file sets up the concrete geometry on which cohomology is evaluated. It realizes the
blueprint's `def:geometry-interface` as refined in `docs/ARCHITECTURE.md`, and discharges the part
of `lem:geometry-adapter` concerning the standard pair, its products, the maps `x` and `xy`, and
the section `x = 1`.

Everything here is on the algebra side: a smooth affine scheme `X` is represented by its coordinate
ring, so a morphism `X → Y` is a morphism `O(Y) ⟶ O(X)` in `SmoothAlg k`. Cohomology will be a
**covariant** functor on `SmoothAlg k`, and "pullback along `X → Y`" is the image of the algebra
map. No hypothesis on `k` beyond being a commutative ring is needed.

## Main definitions

* `OrlikSolomon.SmoothAlg k`: the category of smooth commutative `k`-algebras, as a full
  subcategory of `CommAlgCat k`.
* `SmoothAlg.point k`, `SmoothAlg.polynomial A`, `SmoothAlg.laurent A`, `SmoothAlg.gm k`: the
  coordinate rings `k`, `A[t]`, `A[t;t⁻¹]` and `k[t;t⁻¹]` of the point, of `X × 𝔸¹`, of `X × 𝔾ₘ`
  and of `𝔾ₘ`, with universal properties `polynomialLift`, `laurentLift` and `gmHom`.
* `SmoothAlg.zero k`: the zero ring, the coordinate ring of the empty scheme.
* `SmoothAlg.gmHom u`: the map `k[t;t⁻¹] ⟶ A` attached to a unit `u` of `A`, which replaces a
  regular map `X → 𝔾ₘ`.
* `SmoothAlg.constUnit`: a unit of `k`, as a unit of a smooth algebra.
* `SmoothAlg.isoOfAlgEquiv`: an isomorphism of `SmoothAlg k` from a `k`-algebra isomorphism.
* `OrlikSolomon.DivisorPair k`: certified smooth-divisor pairs `(X, D, U)`, with `D` cut out by a
  non-zero-divisor.
* `DivisorPair.Hom`: transverse morphisms, which make `DivisorPair k` a category.
* `DivisorPair.standardPair A`: the pair `(A[t], A, A[t;t⁻¹], t)`.
* `DivisorPair.standardLift`, `DivisorPair.standardMap`, `DivisorPair.fromStandard`: the
  transverse morphisms out of a standard pair.
* `DivisorPair.emptyDivisor A D`: the pair `(A, D, A, 1)` for a zero ring `D`, whose divisor is
  empty.

## Main results

* `smooth_polynomial`, `smooth_laurentPolynomial`: `A[t]` and `A[t;t⁻¹]` are smooth over `k` when
  `A` is.
* `DivisorPair.hom_ext`, `DivisorPair.homOfAmbient`: a transverse morphism is the same thing as a
  map of ambient algebras carrying `eqn` to a unit multiple of `eqn`.

## How the logarithm lemmas use this file

With `A` a smooth algebra and `P₀ = standardPair (point k)`, write `z` for the coordinate of `P₀`
and `x` for the coordinate of `standardPair A`.

* `lem:gm` uses `P₀` itself, together with `polynomialC_comp_i` and `polynomialC_comp_j`.
* `lem:log-mul` takes `y` to be a unit of `A`. The blueprint's universal case is `A = gm k` with
  `y = laurentT (point k)`. The maps `z ↦ x` and `z ↦ yx` are `standardMap (fromPoint A) 1` and
  `standardMap (fromPoint A) y`. By `standardMap_fromPoint_compl` their open parts are
  `gmHom (mapUnits (laurentC A) u * laurentT A)` for `u = 1` and `u = y`, and by
  `standardMap_closed` their closed parts are `fromPoint A`. The section `x = 1` is
  `laurentSection A`. The final pullback along `x ↦ g`, for a unit `g` of `A`, is
  `laurentLift (𝟙 A) g : laurent A ⟶ A`.
* `lem:gm-product` uses `standardMap (fromPoint A) 1` for general `A`, together with `laurentC A`
  for the projection and `laurentSection A` for the section.
* `lem:log-residue` uses `fromStandard P : P₀ ⟶ P`, the morphism `z ↦ P.eqn`.

## Implementation notes

`point`, `polynomial` and `laurent` are `def`s, not `abbrev`s, and new objects built with
`SmoothAlg.of` should be too. `simp` indexes the source and target of a coerced morphism. A
reducible object unfolds to a constructor application, whose projections stay stuck when a lemma is
added to the simp set but reduce when a goal is matched, so a lemma about such a coercion silently
never fires. Use `polynomialC`, `polynomialX`, `laurentC` and `laurentT` rather than Mathlib's `C`,
`X` and `T`; the lemmas `polynomialC_apply`, `polynomialX_eq`, `laurentC_apply` and `coe_laurentT`
are the bridge to them.

`standardPair` is a `def` too, and so should any pair be that lemmas will mention, such as the
deletion pair. With `abbrev standardPair` this file still builds, but a `simp` lemma about the
residue of a standard pair silently never fires. The price is that `(standardPair A).closed` is only
defeq to `A`, and not at reducible transparency, and likewise for `.ambient` and `.compl`. So for a
class `x` on `laurent A`, the term `T.residue (standardPair A) x` of `Cohomology/Axioms` is not
type-correct at the transparency `rw` and `simp` use:

* `rw` fails under it, even with `map_sub`, though `rw` with a lemma about that exact term works;
* plain `simp` applies `standardPair_compl` and `standardPair_closed` inside the types of the
  coercions, after which neither a lemma about that term nor `add_zero` on a sum containing it
  fires, though `simp only` with them does.

Do not reach for `change` at each step. Use wrappers typed by the literal objects, as
`T.stdResidue A` and `T.stdGysin A` are in `Cohomology/Axioms`, and state lemmas about those. The
same cause explains why `simp only [standardPair_eqnUnit]` applied to its own statement stops at a
goal with identical sides, of different types at reducible transparency; `rw` and `exact` close it.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Polynomial LaurentPolynomial

universe u

namespace OrlikSolomon

section Smoothness

variable (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]

/-- The scalar tower `k → R[X] → R[T;T⁻¹]`, which Mathlib does not yet provide. -/
instance isScalarTower_polynomial_laurentPolynomial : IsScalarTower k R[X] R[T;T⁻¹] :=
  .of_algebraMap_eq fun r ↦ by
    simp [LaurentPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]

/-- If `R` is smooth over `k`, then so is `R[X]`. -/
instance smooth_polynomial [Algebra.Smooth k R] : Algebra.Smooth k R[X] :=
  have : Algebra.Smooth R R[X] := {}
  .comp k R R[X]

/-- If `R` is smooth over `k`, then so is `R[T;T⁻¹]`, a localization of `R[X]` away from `X`. -/
instance smooth_laurentPolynomial [Algebra.Smooth k R] : Algebra.Smooth k R[T;T⁻¹] :=
  have : Algebra.Smooth R[X] R[T;T⁻¹] := .of_isLocalization_Away Polynomial.X
  .comp k R[X] R[T;T⁻¹]

/-- The zero ring is smooth over any ring: it is the localization away from `0`. -/
instance smooth_punit : Algebra.Smooth k PUnit :=
  have : IsLocalization.Away (0 : k) PUnit :=
    .mk _ (isUnit_of_subsingleton _) (fun _ ↦ ⟨0, 0, Subsingleton.elim _ _⟩)
      fun _ _ _ ↦ ⟨1, by simp⟩
  .of_isLocalization_Away (0 : k)

variable {R} in
/-- The variable `T`, as a unit of the Laurent polynomial ring. -/
def laurentPolynomialT : R[T;T⁻¹]ˣ := unitOfInvertible (LaurentPolynomial.T 1)

variable {k R} in
/-- The `k`-algebra map `R[T;T⁻¹] → S` extending `φ : R → S` and sending `T` to the unit `u`. -/
def laurentPolynomialLift {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (u : Sˣ) :
    R[T;T⁻¹] →ₐ[k] S where
  __ := LaurentPolynomial.eval₂ (φ : R →+* S) u
  commutes' r := by simp [LaurentPolynomial.algebraMap_apply]

variable {k R} in
@[simp]
lemma laurentPolynomialLift_C {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (u : Sˣ)
    (a : R) : laurentPolynomialLift φ u (LaurentPolynomial.C a) = φ a :=
  LaurentPolynomial.eval₂_C _ _ _

variable {k R} in
@[simp]
lemma laurentPolynomialLift_T {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (u : Sˣ) :
    laurentPolynomialLift φ u (LaurentPolynomial.T 1) = u :=
  (LaurentPolynomial.eval₂_T _ _ _).trans (by simp)

variable {k R} in
/-- `k`-algebra maps out of `R[T;T⁻¹]` agree if they agree on constants and on `T`. -/
lemma laurentPolynomial_algHom_ext {S : Type*} [CommRing S] [Algebra k S]
    {f g : R[T;T⁻¹] →ₐ[k] S} (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  refine AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : R[X])) ?_
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simpa [LaurentPolynomial.algebraMap_apply, Polynomial.toLaurent_C] using hC a
  · simpa [LaurentPolynomial.algebraMap_apply, Polynomial.toLaurent_X] using hT

/-- Transports `IsLocalization.Away f S` from a given algebra structure to the one defined by a
ring map `g` that equals its structure map. This is the form in which `DivisorPair.isLocalization_j`
is stated, and it is how to supply that field from an existing `IsLocalization` instance. -/
lemma isLocalizationAway_toAlgebra {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {f : R}
    [IsLocalization.Away f S] {g : R →+* S} (hg : g = algebraMap R S) :
    letI := g.toAlgebra
    IsLocalization.Away f S := by
  subst hg
  rwa [toAlgebra_algebraMap]

end Smoothness

variable (k : Type u) [CommRing k]

/-- The category of smooth commutative `k`-algebras, a full subcategory of `CommAlgCat k`. It is
`Spec`-dual to smooth affine `k`-schemes, so all maps here run in the direction of algebras.

Objects live in `Type u`, the universe of `k`. This loses nothing: a smooth algebra is finitely
presented, so it is isomorphic to a quotient of `k[x₁, …, xₙ]`, which lives in `Type u`.

Blueprint: `def:geometry-interface`. -/
abbrev SmoothAlg : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : CommAlgCat.{u} k ↦ Algebra.Smooth k A

namespace SmoothAlg

instance : CoeSort (SmoothAlg k) (Type u) := ⟨fun A ↦ A.obj⟩

variable {k}

instance (A : SmoothAlg k) : Algebra.Smooth k A := A.property

variable (k) in
/-- Bundles a smooth `k`-algebra as an object of `SmoothAlg k`. See the implementation notes in the
module docstring: an object that lemmas will mention should be a `def` built from this. -/
abbrev of (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R] : SmoothAlg k :=
  ⟨CommAlgCat.of k R, ‹_›⟩

/-- Regards a `k`-algebra map between smooth algebras as a morphism of `SmoothAlg k`. -/
abbrev ofHom {A B : SmoothAlg k} (f : A →ₐ[k] B) : A ⟶ B := ConcreteCategory.ofHom f

variable {A B C : SmoothAlg k}

/-- The `k`-algebra map underlying a morphism of `SmoothAlg k`. -/
abbrev algHom (f : A ⟶ B) : A →ₐ[k] B := ConcreteCategory.hom f

@[ext high] lemma hom_ext {f g : A ⟶ B} (h : ∀ x : A, f x = g x) : f = g :=
  ConcreteCategory.hom_ext f g h

/-- A morphism whose target is a localization of its source, in the sense of the algebra structure
that the morphism defines, is an epimorphism. -/
lemma epi_of_isLocalization (f : A ⟶ B) (M : Submonoid A)
    (hf : letI := (algHom f).toRingHom.toAlgebra; IsLocalization M B) : Epi f := by
  let := (algHom f).toRingHom.toAlgebra
  refine ⟨fun g h e ↦ ConcreteCategory.ext ?_⟩
  refine AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext M <| RingHom.ext fun x ↦ ?_
  exact ConcreteCategory.congr_hom e x

/-- A morphism acts on units. Units of `A` are the regular maps to `𝔾ₘ`, so this is composition
with the morphism of schemes; see `gmHom_comp`. -/
def mapUnits (f : A ⟶ B) : Aˣ →* Bˣ := Units.map (algHom f : A →* B)

@[simp] lemma coe_mapUnits (f : A ⟶ B) (u : Aˣ) : (mapUnits f u : B) = f u := rfl

@[simp] lemma mapUnits_id (u : Aˣ) : mapUnits (𝟙 A) u = u := by
  ext; simp

@[simp] lemma mapUnits_comp (f : A ⟶ B) (g : B ⟶ C) (u : Aˣ) :
    mapUnits (f ≫ g) u = mapUnits g (mapUnits f u) := by
  ext; simp

/-- A `k`-algebra isomorphism between smooth algebras, as an isomorphism of `SmoothAlg k`. -/
def isoOfAlgEquiv (e : A ≃ₐ[k] B) : A ≅ B where
  hom := ofHom (e : A →ₐ[k] B)
  inv := ofHom (e.symm : B →ₐ[k] A)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x

/-! ### The point -/

variable (k) in
/-- The coordinate ring `k` of the point. Its cohomology is the coefficient algebra. -/
def point : SmoothAlg k := of k k

variable (A) in
/-- The structure map `k → A`, which is the pullback along the map from `Spec A` to the point. -/
def fromPoint : point k ⟶ A := ofHom (Algebra.ofId k A)

@[simp] lemma fromPoint_apply (c : k) : fromPoint A c = algebraMap k A c := rfl

/-- There is exactly one map from `point k`: it is initial in `SmoothAlg k`. -/
instance : Unique (point k ⟶ A) where
  default := fromPoint A
  uniq f := by
    ext c
    exact (algHom f).commutes c

@[simp] lemma fromPoint_comp (f : A ⟶ B) : fromPoint A ≫ f = fromPoint B :=
  Subsingleton.elim _ _

variable (A) in
/-- A unit of `k`, as a unit of a smooth algebra. It is the pullback of a unit of the point along
`fromPoint A`, by `constUnit_eq_mapUnits`. -/
def constUnit : kˣ →* Aˣ := Units.map (algebraMap k A : k →* A)

@[simp] lemma coe_constUnit (c : kˣ) : (constUnit A c : A) = algebraMap k A c := rfl

lemma constUnit_eq_mapUnits (c : kˣ) : constUnit A c = mapUnits (fromPoint A) (c : (point k)ˣ) :=
  rfl

@[simp] lemma mapUnits_constUnit (f : A ⟶ B) (c : kˣ) :
    mapUnits f (constUnit A c) = constUnit B c := by
  ext
  exact (algHom f).commutes _

/-! ### The zero ring -/

variable (k) in
/-- The zero ring, which is the coordinate ring of the empty scheme. -/
def zero : SmoothAlg k := of k PUnit

instance : Subsingleton (zero k) := inferInstanceAs (Subsingleton PUnit)

/-- There is exactly one map to a zero ring: it is terminal in `SmoothAlg k`. -/
instance [Subsingleton B] : Unique (A ⟶ B) where
  default := ofHom default
  uniq _ := by
    ext
    exact Subsingleton.elim _ _

/-! ### Polynomial algebras -/

/-- The polynomial algebra `A[t]`, the coordinate ring of `X × 𝔸¹` when `A` is that of `X`. -/
def polynomial (A : SmoothAlg k) : SmoothAlg k := of k A[X]

variable (A) in
/-- The inclusion `A → A[t]` of constants, which is the pullback along the projection
`X × 𝔸¹ → X`. -/
def polynomialC : A ⟶ polynomial A := ofHom Polynomial.CAlgHom

variable (A) in
/-- The coordinate `t` of `A[t]`. -/
def polynomialX : polynomial A := (Polynomial.X : A[X])

lemma polynomialC_apply (a : A) : polynomialC A a = (Polynomial.C a : A[X]) := rfl

variable (A) in
lemma polynomialX_eq : polynomialX A = (Polynomial.X : A[X]) := rfl

/-- The universal property of `A[t]`: the map extending `φ : A ⟶ B` and sending `t` to `b`. -/
def polynomialLift (φ : A ⟶ B) (b : B) : polynomial A ⟶ B :=
  ofHom (Polynomial.eval₂AlgHom (algHom φ) b fun _ ↦ Commute.all _ _)

lemma polynomialLift_apply (φ : A ⟶ B) (b : B) (p : A[X]) :
    polynomialLift φ b p = p.eval₂ (algHom φ : A →+* B) b := rfl

@[simp] lemma polynomialLift_polynomialC (φ : A ⟶ B) (b : B) (a : A) :
    polynomialLift φ b (polynomialC A a) = φ a :=
  Polynomial.eval₂_C _ _

@[simp] lemma polynomialLift_polynomialX (φ : A ⟶ B) (b : B) :
    polynomialLift φ b (polynomialX A) = b :=
  Polynomial.eval₂_X _ _

@[reassoc (attr := simp)]
lemma polynomialC_comp_polynomialLift (φ : A ⟶ B) (b : B) :
    polynomialC A ≫ polynomialLift φ b = φ := by
  ext a
  simp

/-- Maps out of `A[t]` agree if they agree on constants and on `t`. -/
lemma polynomial_hom_ext {f g : polynomial A ⟶ B}
    (hC : polynomialC A ≫ f = polynomialC A ≫ g)
    (hX : f (polynomialX A) = g (polynomialX A)) : f = g := by
  apply ConcreteCategory.ext
  apply Polynomial.algHom_ext'
  · exact congr(ConcreteCategory.hom $hC)
  · exact hX

lemma polynomialLift_comp (φ : A ⟶ B) (b : B) (f : B ⟶ C) :
    polynomialLift φ b ≫ f = polynomialLift (φ ≫ f) (f b) := by
  apply polynomial_hom_ext <;> simp

/-! ### Laurent polynomial algebras -/

/-- The Laurent polynomial algebra `A[t;t⁻¹]`, the coordinate ring of `X × 𝔾ₘ` when `A` is that of
`X`. -/
def laurent (A : SmoothAlg k) : SmoothAlg k := of k A[T;T⁻¹]

variable (A) in
/-- The inclusion `A → A[t;t⁻¹]` of constants, which is the pullback along the projection
`X × 𝔾ₘ → X`. -/
def laurentC : A ⟶ laurent A := ofHom (IsScalarTower.toAlgHom k A A[T;T⁻¹])

variable (A) in
/-- The inclusion `A[t] → A[t;t⁻¹]`, which is the pullback along the open immersion
`X × 𝔾ₘ → X × 𝔸¹`. -/
def polynomialToLaurent : polynomial A ⟶ laurent A :=
  ofHom (Polynomial.toLaurentAlg.restrictScalars k : A[X] →ₐ[k] A[T;T⁻¹])

variable (A) in
/-- The coordinate `t`, as a unit of `A[t;t⁻¹]`. -/
def laurentT : (laurent A)ˣ := laurentPolynomialT (R := A)

/-- The universal property of `A[t;t⁻¹]`: the map extending `φ : A ⟶ B` and sending `t` to the unit
`u`. -/
def laurentLift (φ : A ⟶ B) (u : Bˣ) : laurent A ⟶ B :=
  ofHom (laurentPolynomialLift (algHom φ) u)

lemma laurentC_apply (a : A) : laurentC A a = (LaurentPolynomial.C a : A[T;T⁻¹]) := rfl

variable (A) in
lemma coe_laurentT : (laurentT A : laurent A) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) := rfl

variable (A) in
@[simp] lemma polynomialToLaurent_polynomialC (a : A) :
    polynomialToLaurent A (polynomialC A a) = laurentC A a := by
  change Polynomial.toLaurent (Polynomial.C a) = LaurentPolynomial.C a
  exact Polynomial.toLaurent_C a

variable (A) in
@[simp] lemma polynomialToLaurent_polynomialX :
    polynomialToLaurent A (polynomialX A) = (laurentT A : laurent A) := by
  change Polynomial.toLaurent Polynomial.X = LaurentPolynomial.T 1
  exact Polynomial.toLaurent_X

variable (A) in
@[reassoc (attr := simp)]
lemma polynomialC_comp_polynomialToLaurent :
    polynomialC A ≫ polynomialToLaurent A = laurentC A := by
  ext a
  simp

@[simp] lemma laurentLift_laurentC (φ : A ⟶ B) (u : Bˣ) (a : A) :
    laurentLift φ u (laurentC A a) = φ a :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] lemma laurentLift_laurentT (φ : A ⟶ B) (u : Bˣ) :
    laurentLift φ u (laurentT A : laurent A) = u :=
  (LaurentPolynomial.eval₂_T _ _ _).trans (by simp)

@[simp] lemma mapUnits_laurentLift_laurentT (φ : A ⟶ B) (u : Bˣ) :
    mapUnits (laurentLift φ u) (laurentT A) = u := by
  ext; simp

@[simp] lemma mapUnits_laurentLift_mapUnits_laurentC (φ : A ⟶ B) (u : Bˣ) (v : Aˣ) :
    mapUnits (laurentLift φ u) (mapUnits (laurentC A) v) = mapUnits φ v := by
  ext; simp

@[reassoc (attr := simp)]
lemma laurentC_comp_laurentLift (φ : A ⟶ B) (u : Bˣ) :
    laurentC A ≫ laurentLift φ u = φ := by
  ext a
  simp

@[reassoc (attr := simp)]
lemma polynomialToLaurent_comp_laurentLift (φ : A ⟶ B) (u : Bˣ) :
    polynomialToLaurent A ≫ laurentLift φ u = polynomialLift φ u := by
  apply polynomial_hom_ext <;> simp

variable (A) in
instance : Epi (polynomialToLaurent A) :=
  epi_of_isLocalization _ (Submonoid.powers (polynomialX A))
    (isLocalizationAway_toAlgebra (S := A[T;T⁻¹]) (f := (Polynomial.X : A[X])) rfl)

/-- Maps out of `A[t;t⁻¹]` agree if they agree on constants and on `t`. -/
lemma laurent_hom_ext {f g : laurent A ⟶ B}
    (hC : laurentC A ≫ f = laurentC A ≫ g)
    (hT : f (laurentT A : laurent A) = g (laurentT A : laurent A)) : f = g := by
  rw [← cancel_epi (polynomialToLaurent A)]
  apply polynomial_hom_ext
  · simpa using hC
  · simpa using hT

lemma laurentLift_comp (φ : A ⟶ B) (u : Bˣ) (f : B ⟶ C) :
    laurentLift φ u ≫ f = laurentLift (φ ≫ f) (mapUnits f u) := by
  apply laurent_hom_ext <;> simp

variable (A) in
/-- The evaluation `A[t;t⁻¹] → A` at `t = 1`, which is the pullback along the section `t = 1` of
`X × 𝔾ₘ → X`. -/
def laurentSection : laurent A ⟶ A := laurentLift (𝟙 A) 1

variable (A) in
@[reassoc (attr := simp)]
lemma laurentC_comp_laurentSection : laurentC A ≫ laurentSection A = 𝟙 A :=
  laurentC_comp_laurentLift _ _

variable (A) in
@[reassoc (attr := simp)]
lemma polynomialToLaurent_comp_laurentSection :
    polynomialToLaurent A ≫ laurentSection A = polynomialLift (𝟙 A) 1 :=
  polynomialToLaurent_comp_laurentLift _ _

variable (A) in
@[simp] lemma mapUnits_laurentSection_laurentT : mapUnits (laurentSection A) (laurentT A) = 1 :=
  mapUnits_laurentLift_laurentT _ _

@[simp] lemma mapUnits_laurentSection_mapUnits_laurentC (v : Aˣ) :
    mapUnits (laurentSection A) (mapUnits (laurentC A) v) = v := by
  simp [laurentSection]

/-! ### The multiplicative group -/

variable (k) in
/-- The coordinate ring `k[t;t⁻¹]` of `𝔾ₘ`. -/
abbrev gm : SmoothAlg k := laurent (point k)

/-- The map `k[t;t⁻¹] ⟶ A` sending `t` to the unit `u`. Units of `A` are the regular maps from
`Spec A` to `𝔾ₘ`, and this is the corresponding map of coordinate rings. It is the map along which
the logarithmic class of `u` is pulled back. -/
def gmHom (u : Aˣ) : gm k ⟶ A := laurentLift (fromPoint A) u

@[simp] lemma gmHom_laurentT (u : Aˣ) : gmHom u (laurentT (point k) : gm k) = u :=
  laurentLift_laurentT _ _

@[simp] lemma mapUnits_gmHom_laurentT (u : Aˣ) : mapUnits (gmHom u) (laurentT (point k)) = u :=
  mapUnits_laurentLift_laurentT _ _

@[simp, reassoc]
lemma laurentC_comp_gmHom (u : Aˣ) : laurentC (point k) ≫ gmHom u = fromPoint A :=
  laurentC_comp_laurentLift _ _

/-- Maps out of `k[t;t⁻¹]` agree if they agree on `t`, so they correspond to units. -/
lemma gm_hom_ext {f g : gm k ⟶ A}
    (h : f (laurentT (point k) : gm k) = g (laurentT (point k) : gm k)) : f = g :=
  laurent_hom_ext (Subsingleton.elim _ _) h

@[simp, reassoc]
lemma gmHom_comp (u : Aˣ) (f : A ⟶ B) : gmHom u ≫ f = gmHom (mapUnits f u) := by
  apply gm_hom_ext
  simp

/-- The coordinate of `𝔾ₘ` corresponds to the identity map. -/
@[simp] lemma gmHom_laurentT_eq_id : gmHom (laurentT (point k)) = 𝟙 (gm k) := by
  apply gm_hom_ext
  simp

end SmoothAlg

/-- A certified smooth-divisor pair: a smooth affine `X` with coordinate ring `ambient`, a principal
divisor `D` with coordinate ring `closed` cut out by `eqn`, and its complement `U` with coordinate
ring `compl`.

The conditions certify `closed` as `ambient ⧸ (eqn)` and `compl` as `ambient[1/eqn]` without
requiring them to be those rings literally, which lets a pair of arrangement complements form a pair
directly, with no transport.

**The non-zero-divisor condition is essential.** If `eqn = 0` were allowed on a nonzero ambient
ring, the open part would be empty and exactness would force a bijective Gysin map of shift `(2, 1)`
on that ring. For the ambient ring `k` this contradicts the dimension axiom of a **nonzero** theory.
It does not contradict the zero theory, and `0` is a non-zero-divisor of the zero ring, which stays
allowed. Units are allowed too, as in `emptyDivisor`. No stronger condition is needed: see
`docs/ARCHITECTURE.md`.

Blueprint: `def:geometry-interface`. -/
structure DivisorPair where
  /-- The coordinate ring of the ambient space `X`. -/
  ambient : SmoothAlg k
  /-- The coordinate ring of the divisor `D`. -/
  closed : SmoothAlg k
  /-- The coordinate ring of the open complement `U`. -/
  compl : SmoothAlg k
  /-- The pullback along the closed immersion `D → X`. -/
  i : ambient ⟶ closed
  /-- The pullback along the open immersion `U → X`. -/
  j : ambient ⟶ compl
  /-- The equation of the divisor. -/
  eqn : ambient
  /-- The map `i` is surjective, so `closed` is a quotient of `ambient` and `D` is a closed
  subscheme of `X`. -/
  surjective_i : Function.Surjective i
  /-- The kernel of `i` is generated by `eqn`. With `surjective_i`, this identifies `closed` with
  `ambient ⧸ (eqn)`, so `D` is exactly the zero locus of `eqn`. -/
  ker_i : RingHom.ker (SmoothAlg.algHom i) = Ideal.span {eqn}
  /-- The map `j` exhibits `compl` as the localization `ambient[1/eqn]`, for the algebra structure
  that `j` itself defines. So `U` is exactly the complement of `D` in `X`. -/
  isLocalization_j :
    letI := (SmoothAlg.algHom j).toRingHom.toAlgebra
    IsLocalization.Away eqn compl
  /-- The equation is a non-zero-divisor of `ambient`, so `D` is an effective Cartier divisor and
  contains no component of `X`. Units are allowed, which gives an empty `D`. -/
  eqn_mem_nonZeroDivisors : eqn ∈ nonZeroDivisors ambient

namespace DivisorPair

open SmoothAlg

variable {k}

section Basic

variable (P : DivisorPair k) {B : SmoothAlg k}

/-- The open part is an algebra over the ambient ring through `j`. -/
instance : Algebra P.ambient P.compl := (algHom P.j).toRingHom.toAlgebra

@[simp] lemma algebraMap_compl_apply (x : P.ambient) :
    algebraMap P.ambient P.compl x = P.j x := rfl

instance : IsLocalization.Away P.eqn P.compl := P.isLocalization_j

instance : IsScalarTower k P.ambient P.compl :=
  .of_algebraMap_eq fun r ↦ ((algHom P.j).commutes r).symm

/-- An element restricts to zero on the divisor exactly when `eqn` divides it. -/
lemma i_eq_zero_iff {x : P.ambient} : P.i x = 0 ↔ P.eqn ∣ x := by
  rw [← RingHom.mem_ker, P.ker_i, Ideal.mem_span_singleton]

@[simp] lemma i_eqn : P.i P.eqn = 0 := P.i_eq_zero_iff.2 dvd_rfl

lemma isUnit_j_eqn : IsUnit (P.j P.eqn) :=
  IsLocalization.Away.algebraMap_isUnit (S := P.compl) P.eqn

/-- The equation of the divisor, as a unit on the open part. Its logarithmic class is the class
whose residue is `1` (`lem:log-residue`). -/
def eqnUnit : P.complˣ := P.isUnit_j_eqn.unit

@[simp] lemma coe_eqnUnit : (P.eqnUnit : P.compl) = P.j P.eqn := rfl

instance : Epi P.i := by
  refine ⟨fun f g h ↦ ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := P.surjective_i x
  exact ConcreteCategory.congr_hom h y

instance : Epi P.j := epi_of_isLocalization _ (Submonoid.powers P.eqn) P.isLocalization_j

/-- The kernel condition needed to descend a map killing `eqn` along `i`. -/
lemma ker_i_le_ker (f : P.ambient ⟶ B) (hf : f P.eqn = 0) :
    RingHom.ker (algHom P.i).toRingHom ≤ RingHom.ker (algHom f).toRingHom := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := P.i_eq_zero_iff.1 hx
  change f (P.eqn * y) = 0
  simp [hf]

/-- The universal property of the divisor: a map killing `eqn` factors through `i`. -/
def closedLift (f : P.ambient ⟶ B) (hf : f P.eqn = 0) : P.closed ⟶ B :=
  ofHom <| AlgHom.liftOfSurjective (algHom P.i) P.surjective_i (algHom f) (P.ker_i_le_ker f hf)

@[simp] lemma closedLift_i (f : P.ambient ⟶ B) (hf : f P.eqn = 0) (x : P.ambient) :
    P.closedLift f hf (P.i x) = f x :=
  AlgHom.liftOfSurjective_apply (algHom P.i) P.surjective_i (algHom f) (P.ker_i_le_ker f hf) x

@[reassoc (attr := simp)]
lemma i_comp_closedLift (f : P.ambient ⟶ B) (hf : f P.eqn = 0) :
    P.i ≫ P.closedLift f hf = f := by
  ext x
  simp

/-- The universal property of the open part: a map inverting `eqn` factors through `j`. -/
def complLift (f : P.ambient ⟶ B) (hf : IsUnit (f P.eqn)) : P.compl ⟶ B :=
  ofHom (IsLocalization.Away.liftAlgHom (S := P.compl) (f := algHom f) P.eqn hf)

@[simp] lemma complLift_j (f : P.ambient ⟶ B) (hf : IsUnit (f P.eqn)) (x : P.ambient) :
    P.complLift f hf (P.j x) = f x :=
  IsLocalization.Away.lift_eq (S := P.compl) (g := (algHom f : P.ambient →+* B)) P.eqn hf x

@[reassoc (attr := simp)]
lemma j_comp_complLift (f : P.ambient ⟶ B) (hf : IsUnit (f P.eqn)) :
    P.j ≫ P.complLift f hf = f := by
  ext x
  simp

end Basic

/-! ### Transverse morphisms -/

/-- A transverse morphism `P ⟶ Q` of divisor pairs: maps of the three algebras commuting with `i`
and `j`, such that the ambient map sends `P.eqn` to a **unit multiple** of `Q.eqn`. Geometrically
it is a map `X_Q → X_P` under which the divisor `D_P` pulls back to exactly `D_Q`.

The unit is what makes `lem:log-mul` work: there `z ↦ xy` pulls back the divisor `z = 0` to the
divisor `x = 0`, with `y` a unit.

Blueprint: `def:geometry-interface`. -/
@[ext]
structure Hom (P Q : DivisorPair k) where
  /-- The map of ambient algebras. -/
  ambient : P.ambient ⟶ Q.ambient
  /-- The map of divisors. -/
  closed : P.closed ⟶ Q.closed
  /-- The map of open parts. -/
  compl : P.compl ⟶ Q.compl
  /-- The maps of ambient algebras and of divisors commute with `i`: the map `X_Q → X_P` restricts
  to the given map `D_Q → D_P`. -/
  i_comp : P.i ≫ closed = ambient ≫ Q.i
  /-- The maps of ambient algebras and of open parts commute with `j`: the map `X_Q → X_P` restricts
  to the given map `U_Q → U_P`. -/
  j_comp : P.j ≫ compl = ambient ≫ Q.j
  /-- Transversality: the ambient map sends `P.eqn` to a multiple of `Q.eqn` by a unit of
  `Q.ambient`, so `D_P` pulls back to exactly `D_Q`. This excludes `z ↦ x²`, which also commutes
  with `i` and `j` but multiplies the residue by two. -/
  associated_eqn : Associated (ambient P.eqn) Q.eqn

attribute [reassoc] Hom.i_comp Hom.j_comp

/-- Divisor pairs and transverse morphisms form a category, with composition componentwise. -/
instance : Category (DivisorPair k) where
  Hom := Hom
  id P :=
    { ambient := 𝟙 _
      closed := 𝟙 _
      compl := 𝟙 _
      i_comp := by simp
      j_comp := by simp
      associated_eqn := by simp }
  comp {P Q R} f g :=
    { ambient := f.ambient ≫ g.ambient
      closed := f.closed ≫ g.closed
      compl := f.compl ≫ g.compl
      i_comp := by rw [f.i_comp_assoc, g.i_comp, Category.assoc]
      j_comp := by rw [f.j_comp_assoc, g.j_comp, Category.assoc]
      associated_eqn := by
        simpa using (f.associated_eqn.map (algHom g.ambient)).trans g.associated_eqn }

variable {P Q R : DivisorPair k}

@[simp] lemma id_ambient : (𝟙 P : P ⟶ P).ambient = 𝟙 P.ambient := rfl
@[simp] lemma id_closed : (𝟙 P : P ⟶ P).closed = 𝟙 P.closed := rfl
@[simp] lemma id_compl : (𝟙 P : P ⟶ P).compl = 𝟙 P.compl := rfl

@[simp] lemma comp_ambient (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).ambient = f.ambient ≫ g.ambient := rfl
@[simp] lemma comp_closed (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).closed = f.closed ≫ g.closed := rfl
@[simp] lemma comp_compl (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).compl = f.compl ≫ g.compl := rfl

/-- A transverse morphism is determined by its ambient map, because `i` and `j` are epimorphisms. -/
@[ext] lemma hom_ext {f g : P ⟶ Q} (h : f.ambient = g.ambient) : f = g := by
  refine Hom.ext h ?_ ?_
  · rw [← cancel_epi P.i, f.i_comp, g.i_comp, h]
  · rw [← cancel_epi P.j, f.j_comp, g.j_comp, h]

/-- A map of ambient algebras carrying `P.eqn` to a unit multiple of `Q.eqn` extends to a transverse
morphism, uniquely by `hom_ext`. -/
def homOfAmbient (f : P.ambient ⟶ Q.ambient) (hf : Associated (f P.eqn) Q.eqn) : P ⟶ Q where
  ambient := f
  closed := P.closedLift (f ≫ Q.i) <| by
    simpa using Q.i_eq_zero_iff.2 hf.dvd'
  compl := P.complLift (f ≫ Q.j) <| by
    simpa using isUnit_of_dvd_unit (map_dvd (algHom Q.j) hf.dvd) Q.isUnit_j_eqn
  i_comp := by simp
  j_comp := by simp
  associated_eqn := hf

@[simp] lemma homOfAmbient_ambient (f : P.ambient ⟶ Q.ambient)
    (hf : Associated (f P.eqn) Q.eqn) : (homOfAmbient f hf).ambient = f := rfl

/-! ### The empty divisor -/

/-- The pair `(A, D, A, 1)` for a zero ring `D`, which is the empty divisor of `X`, cut out by the
equation `1`. Its open map is an isomorphism, so its exact sequence shows that the cohomology of `D`
vanishes, with no separate axiom for the empty object: see
`OrdinaryTheory.subsingleton_obj_of_subsingleton`.

Blueprint: item C2 of `def:cohomology`. -/
def emptyDivisor (A D : SmoothAlg k) [Subsingleton D] : DivisorPair k where
  ambient := A
  closed := D
  compl := A
  i := default
  j := 𝟙 A
  eqn := 1
  surjective_i _ := ⟨0, Subsingleton.elim _ _⟩
  ker_i := by
    rw [Ideal.span_singleton_one, eq_top_iff]
    exact fun _ _ ↦ Subsingleton.elim _ _
  isLocalization_j := IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  eqn_mem_nonZeroDivisors := one_mem _

section EmptyDivisor

variable (A D : SmoothAlg k) [Subsingleton D]

@[simp] lemma emptyDivisor_ambient : (emptyDivisor A D).ambient = A := rfl
@[simp] lemma emptyDivisor_closed : (emptyDivisor A D).closed = D := rfl
@[simp] lemma emptyDivisor_compl : (emptyDivisor A D).compl = A := rfl
@[simp] lemma emptyDivisor_j : (emptyDivisor A D).j = 𝟙 A := rfl
@[simp] lemma emptyDivisor_eqn : (emptyDivisor A D).eqn = 1 := rfl

end EmptyDivisor

/-! ### The standard pairs -/

variable {A B : SmoothAlg k}

variable (A) in
/-- The pair `(A[t], A, A[t;t⁻¹], t)`, that is `X × 0 ⊂ X × 𝔸¹` with complement `X × 𝔾ₘ`. For
`A = k` it is the standard pair `(𝔸¹, 0, 𝔾ₘ)`, and for `A = k[y;y⁻¹]` it is the pair in
`lem:log-mul`.

Blueprint: `def:geometry-interface`, `lem:geometry-adapter`. -/
def standardPair : DivisorPair k where
  ambient := polynomial A
  closed := A
  compl := laurent A
  i := polynomialLift (𝟙 A) 0
  j := polynomialToLaurent A
  eqn := polynomialX A
  surjective_i x := ⟨polynomialC A x, by simp⟩
  ker_i := by
    refine Eq.trans ?_ (Polynomial.ker_constantCoeff (R := A))
    ext (p : A[X])
    have h : polynomialLift (𝟙 A) 0 p = p.coeff 0 := Polynomial.eval₂_at_zero _
    exact Eq.congr_left h
  isLocalization_j := isLocalizationAway_toAlgebra (S := A[T;T⁻¹]) (f := (Polynomial.X : A[X])) rfl
  eqn_mem_nonZeroDivisors := Polynomial.X_mem_nonZeroDivisors

variable (A)

@[simp] lemma standardPair_ambient : (standardPair A).ambient = polynomial A := rfl
@[simp] lemma standardPair_closed : (standardPair A).closed = A := rfl
@[simp] lemma standardPair_compl : (standardPair A).compl = laurent A := rfl
@[simp] lemma standardPair_i : (standardPair A).i = polynomialLift (𝟙 A) 0 := rfl
@[simp] lemma standardPair_j : (standardPair A).j = polynomialToLaurent A := rfl
@[simp] lemma standardPair_eqn : (standardPair A).eqn = polynomialX A := rfl

@[simp] lemma standardPair_eqnUnit : (standardPair A).eqnUnit = laurentT A :=
  Units.ext (polynomialToLaurent_polynomialX A)

/-- Constants restrict identically to the divisor `X × 0`. This is not a `simp` lemma, because
`simp` already proves it by rewriting `(standardPair A).i` with `standardPair_i`. -/
@[reassoc]
lemma polynomialC_comp_i : polynomialC A ≫ (standardPair A).i = 𝟙 A :=
  polynomialC_comp_polynomialLift _ _

/-- Constants on `X × 𝔸¹` restrict to constants on `X × 𝔾ₘ`. This is not a `simp` lemma, because
`simp` already proves it by rewriting `(standardPair A).j` with `standardPair_j`. -/
@[reassoc]
lemma polynomialC_comp_j : polynomialC A ≫ (standardPair A).j = laurentC A :=
  polynomialC_comp_polynomialToLaurent A

variable {A}

/-- The transverse morphism from `standardPair A` to any pair `P` with `φ : A ⟶ P.ambient` on
constants and `t ↦ u * P.eqn` for a unit `u` of `P.ambient`. -/
def standardLift (φ : A ⟶ P.ambient) (u : P.ambientˣ) : standardPair A ⟶ P where
  ambient := polynomialLift φ (u * P.eqn)
  closed := φ ≫ P.i
  compl := laurentLift (φ ≫ P.j) (mapUnits P.j u * P.eqnUnit)
  i_comp := by
    apply polynomial_hom_ext <;> simp
  j_comp := by
    apply polynomial_hom_ext <;> simp
  associated_eqn := by
    change Associated (polynomialLift φ (u * P.eqn) (polynomialX A)) P.eqn
    rw [polynomialLift_polynomialX]
    exact associated_unit_mul_left _ _ u.isUnit

@[simp] lemma standardLift_ambient (φ : A ⟶ P.ambient) (u : P.ambientˣ) :
    (standardLift φ u).ambient = polynomialLift φ (u * P.eqn) := rfl

@[simp] lemma standardLift_closed (φ : A ⟶ P.ambient) (u : P.ambientˣ) :
    (standardLift φ u).closed = φ ≫ P.i := rfl

@[simp] lemma standardLift_compl (φ : A ⟶ P.ambient) (u : P.ambientˣ) :
    (standardLift φ u).compl = laurentLift (φ ≫ P.j) (mapUnits P.j u * P.eqnUnit) := rfl

/-- The transverse morphism `standardPair A ⟶ standardPair B` given by `φ : A ⟶ B` on constants and
by `t ↦ u * t` for a unit `u` of `B`.

For `lem:log-mul`, with `y` a unit of `A`, the maps `z ↦ x` and `z ↦ yx` out of the standard pair
of the point are `standardMap (fromPoint A) 1` and `standardMap (fromPoint A) y`. -/
def standardMap (φ : A ⟶ B) (u : Bˣ) : standardPair A ⟶ standardPair B where
  ambient := polynomialLift (φ ≫ polynomialC B) (polynomialC B u * polynomialX B)
  closed := φ
  compl := laurentLift (φ ≫ laurentC B) (mapUnits (laurentC B) u * laurentT B)
  i_comp := by
    change polynomialLift (𝟙 A) 0 ≫ φ =
      polynomialLift (φ ≫ polynomialC B) (polynomialC B u * polynomialX B) ≫
        polynomialLift (𝟙 B) 0
    apply polynomial_hom_ext <;> simp
  j_comp := by
    change polynomialToLaurent A ≫
        laurentLift (φ ≫ laurentC B) (mapUnits (laurentC B) u * laurentT B) =
      polynomialLift (φ ≫ polynomialC B) (polynomialC B u * polynomialX B) ≫
        polynomialToLaurent B
    apply polynomial_hom_ext <;> simp
  associated_eqn := by
    change Associated (polynomialLift (φ ≫ polynomialC B) (polynomialC B u * polynomialX B)
      (polynomialX A)) (polynomialX B)
    rw [polynomialLift_polynomialX]
    exact associated_unit_mul_left _ _ (u.isUnit.map (algHom (polynomialC B)))

@[simp] lemma standardMap_ambient (φ : A ⟶ B) (u : Bˣ) :
    (standardMap φ u).ambient =
      polynomialLift (φ ≫ polynomialC B) (polynomialC B u * polynomialX B) := rfl

@[simp] lemma standardMap_closed (φ : A ⟶ B) (u : Bˣ) : (standardMap φ u).closed = φ := rfl

@[simp] lemma standardMap_compl (φ : A ⟶ B) (u : Bˣ) :
    (standardMap φ u).compl =
      laurentLift (φ ≫ laurentC B) (mapUnits (laurentC B) u * laurentT B) := rfl

/-- On open parts, `z ↦ u * x` from the standard pair of the point is the map attached to the unit
`u * x`. -/
lemma standardMap_fromPoint_compl (u : Bˣ) :
    (standardMap (fromPoint B) u).compl = gmHom (mapUnits (laurentC B) u * laurentT B) := by
  simp [gmHom]

/-- The transverse morphism `z ↦ P.eqn` from the standard pair of the point to `P`. On open parts it
is the map attached to the unit `P.eqnUnit` (`fromStandard_compl`), which is how `lem:log-residue`
computes the residue of the logarithm of an equation. -/
def fromStandard (P : DivisorPair k) : standardPair (point k) ⟶ P :=
  standardLift (fromPoint P.ambient) 1

variable (P) in
@[simp] lemma fromStandard_closed : (fromStandard P).closed = fromPoint P.closed := by
  simp [fromStandard]

variable (P) in
@[simp] lemma fromStandard_compl : (fromStandard P).compl = gmHom P.eqnUnit := by
  simp [fromStandard, gmHom]

end DivisorPair

end OrlikSolomon
