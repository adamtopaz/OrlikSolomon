/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import OrlikSolomon.Cohomology.Axioms
public import OrlikSolomon.Cohomology.BridgeData.Category
public import OrlikSolomon.Grading.DirectSum

/-!
# Degreewise cohomology with products and coefficients

`DegreewiseTheory` records cohomology groups indexed by cohomological degree and twist, their
products and pullbacks, and their homogeneous coefficient maps. All maps in the input are
degreewise. This is the product and functoriality part of the input to `lem:standard-bridge`;
localization with supports and oriented purity are supplied separately.

## Hand check of the input against a real theory

This is a mathematical check, not a Lean instance. For a field with a chosen embedding into
`ℂ`, take `B = R[t,t⁻¹]`, `ℬ w = R t^w`, and `H^{p,w}(A) = H^p((Spec A)(ℂ); R) t^w`, for any
commutative ring `R`. This verifies the fields as follows:

* `H`, `addCommGroup`, `module`, `gRing` and `gAlgebra` are ordinary cohomology groups and cup
  products. The formal symbol `t` is central, and `graded_comm` uses only cohomological degree.
* `coeff`, `coeff_one` and `coeff_mul` are pullback of constant classes times `t^w`.
  `bijective_algebraMap_gradeZero` is the identification `R = R t⁰`.
* `map`, `map_id`, `map_comp`, `map_one`, `map_mul` and `map_coeff` are the usual functorial
  pullbacks and their compatibility with products and constant classes.
* `bijective_coeff_point` and `eq_zero_point` are the cohomology of a point.
  `bijective_map_polynomialC` is homotopy invariance for the contractible factor `ℂ`.

This model uses the specified Laurent coefficient algebra; it does not interpret an arbitrary
weight-graded `B` as singular cohomology. It is checked by hand, not in Lean: no singular or étale
instance is constructed. The values of `OrdinaryTheory` constructed in Lean are the zero theories in
`Examples/Sanity` and `Examples/Bridge`, and the de Rham instance of `DeRham/Instance`, which is
built directly rather than through this bridge.

For geometric étale cohomology the analogous input uses `H^p(X_{k^sep}; ℤ_ℓ(w))`, with `ℓ`
invertible in the base field and a separably closed geometric point. Arithmetic cohomology of
`Spec k` generally has higher Galois cohomology and fails the point axiom. A Lean instance would
also have to supply coherent twists and the strict indexed products required by `GRing`;
these are implementation obligations, not additional fields or a formal model supplied here.

The external direct sums carry the ring structure supplied by Mathlib's `DirectSum.GRing`.
The coefficient maps extend to a central algebra map from `B`, and degreewise pullbacks extend
to a functor to `AlgCat B`. No exactness assertion is part of this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg

universe u v w z

namespace OrlikSolomon

/-- Cohomology given by degreewise groups, products, twists and pullbacks, with the point and
affine-line axioms. The coefficient maps are `ℬ w → H^{0,w}(A)`. The indexed product is Mathlib's
`DirectSum.GRing`, and is required to supercommute only in cohomological degree.

Localization with supports and oriented purity are not fields here: they form the separate
input `SupportsAndPurity`. Blueprint: the input to `lem:standard-bridge`. -/
structure DegreewiseTheory (k : Type u) [CommRing k] {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B] (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] where
  /-- The group `H^{p,w}(A)`. -/
  H (A : SmoothAlg k) : ℤ × ℤ → Type z
  /-- Cohomology groups are additive abelian groups. -/
  [addCommGroup : ∀ A i, AddCommGroup (H A i)]
  /-- Each cohomology group is an `R`-module. -/
  [module : ∀ A i, Module R (H A i)]
  /-- The cup products, with their associative unital graded ring laws. -/
  [gRing : ∀ A, GRing (H A)]
  /-- Cup products are compatible with the `R`-module structures. -/
  [gAlgebra : ∀ A, GAlgebra R (H A)]
  /-- The structural coefficient map in each weight. -/
  coeff (A : SmoothAlg k) (w : ℤ) : ℬ w →ₗ[R] H A (0, w)
  /-- The coefficient maps preserve the unit. -/
  coeff_one (A : SmoothAlg k) :
    coeff A 0 (GradedMonoid.GOne.one (A := fun w ↦ ℬ w)) = GradedMonoid.GOne.one
  /-- The coefficient maps preserve products. -/
  coeff_mul (A : SmoothAlg k) {w v : ℤ} (b : ℬ w) (c : ℬ v) :
    coeff A (w + v) (GradedMonoid.GMul.mul (A := fun w ↦ ℬ w) b c) =
      GradedMonoid.GMul.mul (coeff A w b) (coeff A v c)
  /-- The structural map identifies `R` with `ℬ 0`. -/
  bijective_algebraMap_gradeZero : Function.Bijective (algebraMap R (ℬ 0))
  /-- Cup products supercommute; a sigma equality records the change from `i+j` to `j+i`. -/
  graded_comm (A : SmoothAlg k) {i j : ℤ × ℤ} (x : H A i) (y : H A j) :
    GradedMonoid.mk (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.mk (j + i) ((i.1 * j.1).negOnePow • GradedMonoid.GMul.mul y x)
  /-- Pullback in each bidegree, in the direction of the coordinate-ring map. -/
  map {A D : SmoothAlg k} (f : A ⟶ D) (i : ℤ × ℤ) : H A i →ₗ[R] H D i
  /-- Pullback along an identity is the identity. -/
  map_id (A : SmoothAlg k) (i : ℤ × ℤ) (x : H A i) : map (𝟙 A) i x = x
  /-- Pullback respects composition. -/
  map_comp {A D E : SmoothAlg k} (f : A ⟶ D) (g : D ⟶ E) (i : ℤ × ℤ) (x : H A i) :
    map (f ≫ g) i x = map g i (map f i x)
  /-- Pullback preserves the unit. -/
  map_one {A D : SmoothAlg k} (f : A ⟶ D) :
    map f 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one
  /-- Pullback preserves cup products. -/
  map_mul {A D : SmoothAlg k} (f : A ⟶ D) {i j : ℤ × ℤ} (x : H A i) (y : H A j) :
    map f (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (map f i x) (map f j y)
  /-- Pullback preserves homogeneous coefficients. -/
  map_coeff {A D : SmoothAlg k} (f : A ⟶ D) (w : ℤ) (b : ℬ w) :
    map f (0, w) (coeff A w b) = coeff D w b
  /-- At the point, the coefficient map is bijective in every weight. -/
  bijective_coeff_point (w : ℤ) : Function.Bijective (coeff (point k) w)
  /-- The point has no cohomology in nonzero cohomological degrees. -/
  eq_zero_point {p w : ℤ} (hp : p ≠ 0) (x : H (point k) (p, w)) : x = 0
  /-- Affine-line invariance in every bidegree. -/
  bijective_map_polynomialC (A : SmoothAlg k) (i : ℤ × ℤ) :
    Function.Bijective (map (polynomialC A) i)

namespace DegreewiseTheory

attribute [instance] addCommGroup module gRing gAlgebra

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (D : DegreewiseTheory.{u, v, w, z} k ℬ)

/-- The category-independent degreewise data underlying the algebraic bridge. -/
@[implicit_reducible]
def toCore :
    CategoricalDegreewiseTheory (SmoothAlg k) (point k) polynomial polynomialC ℬ where
  H := D.H
  addCommGroup := D.addCommGroup
  module := D.module
  gRing := D.gRing
  gAlgebra := D.gAlgebra
  coeff := D.coeff
  coeff_one := D.coeff_one
  coeff_mul := D.coeff_mul
  bijective_algebraMap_gradeZero := D.bijective_algebraMap_gradeZero
  graded_comm := D.graded_comm
  map := D.map
  map_id := D.map_id
  map_comp := D.map_comp
  map_one := D.map_one
  map_mul := D.map_mul
  map_coeff := D.map_coeff
  bijective_coeff_point := D.bijective_coeff_point
  eq_zero_point := D.eq_zero_point
  bijective_map_line := D.bijective_map_polynomialC

/-- Total cohomology, as the external direct sum over cohomological degree and twist. -/
abbrev Total (A : SmoothAlg k) := ⨁ i, D.H A i

/-- The inclusion of a degreewise group in total cohomology. -/
abbrev incl (A : SmoothAlg k) (i : ℤ × ℤ) : D.H A i →ₗ[R] D.Total A :=
  DirectSum.lof R _ (D.H A) i

/-- Multiplication of classes from two degreewise summands is their indexed cup product. -/
@[simp]
lemma incl_mul_incl (A : SmoothAlg k) {i j : ℤ × ℤ} (x : D.H A i) (y : D.H A j) :
    D.incl A i x * D.incl A j y =
      D.incl A (i + j) (GradedMonoid.GMul.mul x y) :=
  D.toCore.incl_mul_incl A x y

/-- The homogeneous coefficient maps, extended to the direct sum of the weights of `B`. -/
def coeffSum (A : SmoothAlg k) : (⨁ w, ℬ w) →ₐ[R] D.Total A :=
  D.toCore.coeffSum A

/-- The coefficient algebra map `B → C(A)`, assembled from the homogeneous coefficient maps. -/
def coeffMap (A : SmoothAlg k) : B →ₐ[R] D.Total A :=
  D.toCore.coeffMap A

@[simp]
lemma coeffMap_coe (A : SmoothAlg k) {w : ℤ} (b : ℬ w) :
    D.coeffMap A (b : B) = D.incl A (0, w) (D.coeff A w b) :=
  D.toCore.coeffMap_coe A b

/-- Homogeneous classes supercommute in total cohomology. -/
lemma incl_mul_comm (A : SmoothAlg k) {i j : ℤ × ℤ} (x : D.H A i) (y : D.H A j) :
    D.incl A i x * D.incl A j y = (i.1 * j.1).negOnePow •
      (D.incl A j y * D.incl A i x) :=
  D.toCore.incl_mul_comm A x y

/-- Coefficients are central, since their cohomological degree is zero. -/
lemma coeffMap_commutes (A : SmoothAlg k) (b : B) (x : D.Total A) :
    D.coeffMap A b * x = x * D.coeffMap A b :=
  D.toCore.coeffMap_commutes A b x

/-- The central `B`-algebra structure on total cohomology. -/
instance algebra (A : SmoothAlg k) : Algebra B (D.Total A) :=
  D.toCore.algebra A

instance isScalarTower (A : SmoothAlg k) : IsScalarTower R B (D.Total A) :=
  D.toCore.isScalarTower A

@[simp]
lemma algebraMap_coe (A : SmoothAlg k) {w : ℤ} (b : ℬ w) :
    algebraMap B (D.Total A) (b : B) = D.incl A (0, w) (D.coeff A w b) :=
  D.toCore.algebraMap_coe A b

/-- Pullback on total cohomology as an `R`-algebra map, obtained by summing degreewise pullback. -/
def mapTotalR {A E : SmoothAlg k} (f : A ⟶ E) : D.Total A →ₐ[R] D.Total E :=
  D.toCore.mapTotalR f

@[simp]
lemma mapTotalR_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) (x : D.H A i) :
    D.mapTotalR f (D.incl A i x) = D.incl E i (D.map f i x) :=
  D.toCore.mapTotalR_incl f i x

/-- Pulling back a summand and then taking its component gives the original degreewise map. -/
lemma component_mapTotalR_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) :
    (DirectSum.component R _ (D.H E) i).comp
        ((D.mapTotalR f).toLinearMap.comp (D.incl A i)) = D.map f i :=
  D.toCore.component_mapTotalR_incl f i

/-- Total pullback preserves the full coefficient ring. -/
lemma mapTotalR_coeffMap {A E : SmoothAlg k} (f : A ⟶ E) (b : B) :
    D.mapTotalR f (D.coeffMap A b) = D.coeffMap E b :=
  D.toCore.mapTotalR_coeffMap f b

/-- Pullback on total cohomology as a `B`-algebra map. -/
def mapTotal {A E : SmoothAlg k} (f : A ⟶ E) : D.Total A →ₐ[B] D.Total E :=
  D.toCore.mapTotal f

@[simp]
lemma mapTotal_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) (x : D.H A i) :
    D.mapTotal f (D.incl A i x) = D.incl E i (D.map f i x) :=
  D.toCore.mapTotal_incl f i x

/-- The additive map underlying total pullback is the componentwise direct-sum map. -/
lemma mapTotal_eq_lmap {A E : SmoothAlg k} (f : A ⟶ E) :
    (D.mapTotal f : D.Total A → D.Total E) = DirectSum.lmap (D.map f) :=
  D.toCore.mapTotal_eq_lmap f

/-- The internal bigrading on total cohomology, given by the original summands. -/
def grading (A : SmoothAlg k) : ℤ × ℤ → Submodule R (D.Total A) :=
  D.toCore.grading A

instance gradedAlgebra (A : SmoothAlg k) : GradedAlgebra (D.grading A) :=
  D.toCore.gradedAlgebra A

/-- Homogeneous coefficient classes land in cohomological degree zero. -/
lemma algebraMap_mem_grading (A : SmoothAlg k) {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (D.Total A) b ∈ D.grading A (0, w) :=
  D.toCore.algebraMap_mem_grading A hb

/-- The `R`-algebra pullback preserves bidegrees with the original direct-sum scalar structure.
This form can be used to take components when `R` and `B` coincide. -/
lemma isHomogeneousOfShift_mapTotalR {A E : SmoothAlg k} (f : A ⟶ E) :
    IsHomogeneousOfShift (D.grading A) (D.grading E) 0 (D.mapTotalR f) :=
  D.toCore.isHomogeneousOfShift_mapTotalR f

/-- Total pullbacks preserve bidegrees. -/
lemma isHomogeneousOfShift_mapTotal {A E : SmoothAlg k} (f : A ⟶ E) :
    IsHomogeneousOfShift (D.grading A) (D.grading E) 0 (D.mapTotal f) :=
  D.toCore.isHomogeneousOfShift_mapTotal f

/-- The total ring is graded commutative in cohomological degree. -/
lemma isGradedCommutative (A : SmoothAlg k) : IsGradedCommutative (D.grading A) Prod.fst :=
  D.toCore.isGradedCommutative A

/-- Taking a weight component commutes with the coefficient map to the point. -/
lemma component_coeffMap_point (b : B) (w : ℤ) :
    DirectSum.component R _ (D.H (point k)) (0, w) (D.coeffMap (point k) b) =
      D.coeff (point k) w (DirectSum.decompose ℬ b w) :=
  D.toCore.component_coeffMap_point b w

/-- The total coefficient map to the point is bijective, from the degreewise dimension axiom. -/
lemma bijective_coeffMap_point : Function.Bijective (D.coeffMap (point k)) :=
  D.toCore.bijective_coeffMap_point

/-- The total cohomology of the point vanishes in nonzero cohomological degrees. -/
lemma eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : D.Total (point k)}
    (hx : x ∈ D.grading (point k) (p, w)) : x = 0 :=
  D.toCore.eq_zero_of_mem_grading_point hp hx

/-- Degreewise affine-line invariance gives bijectivity on total cohomology. -/
lemma bijective_mapTotal_polynomialC (A : SmoothAlg k) :
    Function.Bijective (D.mapTotal (polynomialC A)) :=
  D.toCore.bijective_mapTotal_line A

/-- The total cohomology functor, constructed from degreewise groups and pullbacks. -/
@[implicit_reducible]
def functor : SmoothAlg k ⥤ AlgCat.{z} B :=
  D.toCore.functor

end DegreewiseTheory

end OrlikSolomon
