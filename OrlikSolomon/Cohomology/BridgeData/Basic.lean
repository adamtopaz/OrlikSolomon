/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import OrlikSolomon.Cohomology.Axioms
public import OrlikSolomon.Grading.DirectSum

/-!
# Degreewise cohomology with products and coefficients

`DegreewiseTheory` records cohomology groups indexed by cohomological degree and twist, their
products and pullbacks, and their homogeneous coefficient maps. All maps in the input are
degreewise. This is the product and functoriality part of the input to `lem:standard-bridge`;
localization with supports and oriented purity are supplied separately.

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
  DirectSum.of_mul_of x y

/-- The homogeneous coefficient maps, extended to the direct sum of the weights of `B`. -/
def coeffSum (A : SmoothAlg k) : (⨁ w, ℬ w) →ₐ[R] D.Total A :=
  DirectSum.toAlgebra R _ (fun w ↦ (D.incl A (0, w)).comp (D.coeff A w))
    (by
      change D.incl A 0
        (D.coeff A 0 (GradedMonoid.GOne.one (A := fun w ↦ ℬ w))) = 1
      rw [D.coeff_one]
      rfl)
    (fun {w v} b c ↦ by
      simp only [LinearMap.comp_apply, D.coeff_mul, DirectSum.lof_eq_of,
        DirectSum.of_mul_of]
      rfl)

/-- The coefficient algebra map `B → C(A)`, assembled from the homogeneous coefficient maps. -/
def coeffMap (A : SmoothAlg k) : B →ₐ[R] D.Total A :=
  (D.coeffSum A).comp (DirectSum.decomposeAlgEquiv ℬ).toAlgHom

@[simp]
lemma coeffMap_coe (A : SmoothAlg k) {w : ℤ} (b : ℬ w) :
    D.coeffMap A (b : B) = D.incl A (0, w) (D.coeff A w b) := by
  change D.coeffSum A (DirectSum.decompose ℬ (b : B)) = _
  rw [DirectSum.decompose_coe]
  change DirectSum.toModule R ℤ (D.Total A)
      (fun w ↦ (D.incl A (0, w)).comp (D.coeff A w))
      (DirectSum.lof R _ (fun w ↦ ℬ w) w b) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- Homogeneous classes supercommute in total cohomology. -/
lemma incl_mul_comm (A : SmoothAlg k) {i j : ℤ × ℤ} (x : D.H A i) (y : D.H A j) :
    D.incl A i x * D.incl A j y = (i.1 * j.1).negOnePow •
      (D.incl A j y * D.incl A i x) := by
  simp only [incl, DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rw [DirectSum.of_eq_of_gradedMonoid_eq (D.graded_comm A x y), map_zsmul_unit]

/-- Coefficients are central, since their cohomological degree is zero. -/
lemma coeffMap_commutes (A : SmoothAlg k) (b : B) (x : D.Total A) :
    D.coeffMap A b * x = x * D.coeffMap A b := by
  induction b using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous w b =>
    rw [D.coeffMap_coe]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simpa only [incl, DirectSum.lof_eq_of, Int.zero_mul,
        Int.negOnePow_zero, one_smul] using D.incl_mul_comm A (D.coeff A w b) x
    | add x y hx hy => simp [mul_add, add_mul, hx, hy]
  | add b c hb hc => simp [mul_add, add_mul, hb, hc]

/-- The central `B`-algebra structure on total cohomology. -/
instance algebra (A : SmoothAlg k) : Algebra B (D.Total A) :=
  (D.coeffMap A).toRingHom.toAlgebra' (D.coeffMap_commutes A)

instance isScalarTower (A : SmoothAlg k) : IsScalarTower R B (D.Total A) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ (D.coeffMap A).commutes r |>.symm

@[simp]
lemma algebraMap_coe (A : SmoothAlg k) {w : ℤ} (b : ℬ w) :
    algebraMap B (D.Total A) (b : B) = D.incl A (0, w) (D.coeff A w b) :=
  D.coeffMap_coe A b

/-- Pullback on total cohomology as an `R`-algebra map, obtained by summing degreewise pullback. -/
def mapTotalR {A E : SmoothAlg k} (f : A ⟶ E) : D.Total A →ₐ[R] D.Total E :=
  DirectSum.toAlgebra R _ (fun i ↦ (D.incl E i).comp (D.map f i))
    (by
      change D.incl E 0 (D.map f 0 GradedMonoid.GOne.one) = 1
      rw [D.map_one]
      rfl)
    (fun {i j} x y ↦ by
      simp only [LinearMap.comp_apply, D.map_mul, DirectSum.lof_eq_of,
        DirectSum.of_mul_of])

@[simp]
lemma mapTotalR_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) (x : D.H A i) :
    D.mapTotalR f (D.incl A i x) = D.incl E i (D.map f i x) := by
  change DirectSum.toModule R (ℤ × ℤ) (D.Total E)
      (fun j ↦ (D.incl E j).comp (D.map f j)) (D.incl A i x) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- Total pullback preserves the full coefficient ring. -/
lemma mapTotalR_coeffMap {A E : SmoothAlg k} (f : A ⟶ E) (b : B) :
    D.mapTotalR f (D.coeffMap A b) = D.coeffMap E b := by
  induction b using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp
  | homogeneous b => simp only [D.coeffMap_coe, D.mapTotalR_incl, D.map_coeff]
  | add b c hb hc => simp [hb, hc]

/-- Pullback on total cohomology as a `B`-algebra map. -/
def mapTotal {A E : SmoothAlg k} (f : A ⟶ E) : D.Total A →ₐ[B] D.Total E :=
  { (D.mapTotalR f).toRingHom with commutes' := D.mapTotalR_coeffMap f }

@[simp]
lemma mapTotal_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) (x : D.H A i) :
    D.mapTotal f (D.incl A i x) = D.incl E i (D.map f i x) :=
  D.mapTotalR_incl f i x

/-- The additive map underlying total pullback is the componentwise direct-sum map. -/
lemma mapTotal_eq_lmap {A E : SmoothAlg k} (f : A ⟶ E) :
    (D.mapTotal f : D.Total A → D.Total E) = DirectSum.lmap (D.map f) := by
  funext x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i x => exact (D.mapTotal_incl f i x).trans (DirectSum.lmap_lof _ _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The internal bigrading on total cohomology, given by the original summands. -/
def grading (A : SmoothAlg k) : ℤ × ℤ → Submodule R (D.Total A) :=
  directSumGrading (R := R) (D.H A)

instance gradedAlgebra (A : SmoothAlg k) : GradedAlgebra (D.grading A) :=
  directSumGradedAlgebra (D.H A)

/-- Homogeneous coefficient classes land in cohomological degree zero. -/
lemma algebraMap_mem_grading (A : SmoothAlg k) {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (D.Total A) b ∈ D.grading A (0, w) := by
  rw [D.algebraMap_coe A ⟨b, hb⟩]
  exact lof_mem_directSumGrading (D.H A) _ _

/-- Total pullbacks preserve bidegrees. -/
lemma isHomogeneousOfShift_mapTotal {A E : SmoothAlg k} (f : A ⟶ E) :
    IsHomogeneousOfShift (D.grading A) (D.grading E) 0 (D.mapTotal f) := by
  rintro i _ ⟨x, rfl⟩
  rw [D.mapTotal_incl, add_zero]
  exact lof_mem_directSumGrading (D.H E) _ _

/-- The total ring is graded commutative in cohomological degree. -/
lemma isGradedCommutative (A : SmoothAlg k) : IsGradedCommutative (D.grading A) Prod.fst := by
  rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  exact D.incl_mul_comm A x y

/-- Taking a weight component commutes with the coefficient map to the point. -/
lemma component_coeffMap_point (b : B) (w : ℤ) :
    DirectSum.component R _ (D.H (point k)) (0, w) (D.coeffMap (point k) b) =
      D.coeff (point k) w (DirectSum.decompose ℬ b w) := by
  induction b using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous v b =>
    obtain rfl | hv := eq_or_ne v w
    · rw [D.coeffMap_coe, DirectSum.component.lof_self, DirectSum.decompose_coe,
        DirectSum.of_eq_same]
    · rw [D.coeffMap_coe, DirectSum.component.of]
      split_ifs with h
      · exact (hv (congrArg Prod.snd h)).elim
      · have hz : DirectSum.decompose ℬ (b : B) w = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne ℬ b.2 hv)
        rw [hz, map_zero]
  | add b c hb hc => simp [hb, hc]

/-- The total coefficient map to the point is bijective, from the degreewise dimension axiom. -/
lemma bijective_coeffMap_point : Function.Bijective (D.coeffMap (point k)) := by
  constructor
  · intro b c h
    apply (DirectSum.decompose ℬ).injective
    apply DFinsupp.ext
    intro w
    apply (D.bijective_coeff_point w).1
    rw [← D.component_coeffMap_point, ← D.component_coeffMap_point, h]
  · intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of i x =>
      rcases i with ⟨p, w⟩
      by_cases hp : p = 0
      · subst p
        obtain ⟨b, rfl⟩ := (D.bijective_coeff_point w).2 x
        exact ⟨b, D.coeffMap_coe (point k) b⟩
      · exact ⟨0, by rw [D.eq_zero_point hp x, map_zero, map_zero]⟩
    | add x y hx hy =>
      obtain ⟨b, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨b + c, map_add _ _ _⟩

/-- The total cohomology of the point vanishes in nonzero cohomological degrees. -/
lemma eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : D.Total (point k)}
    (hx : x ∈ D.grading (point k) (p, w)) : x = 0 := by
  obtain ⟨x, rfl⟩ := hx
  rw [D.eq_zero_point hp x, map_zero]

/-- Degreewise affine-line invariance gives bijectivity on total cohomology. -/
lemma bijective_mapTotal_polynomialC (A : SmoothAlg k) :
    Function.Bijective (D.mapTotal (polynomialC A)) := by
  rw [D.mapTotal_eq_lmap]
  exact ⟨(DirectSum.lmap_injective _).2 fun i ↦ (D.bijective_map_polynomialC A i).1,
    (DirectSum.lmap_surjective _).2 fun i ↦ (D.bijective_map_polynomialC A i).2⟩

/-- The total cohomology functor, constructed from degreewise groups and pullbacks. -/
def functor : SmoothAlg k ⥤ AlgCat.{z} B where
  obj A := AlgCat.of B (D.Total A)
  map f := AlgCat.ofHom (D.mapTotal f)
  map_id A := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact map_zero _
    | of i x =>
      change D.mapTotal (𝟙 A) (D.incl A i x) = D.incl A i x
      rw [D.mapTotal_incl, D.map_id]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp f g := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of i x =>
      change D.mapTotal (f ≫ g) (D.incl _ i x) =
        D.mapTotal g (D.mapTotal f (D.incl _ i x))
      rw [D.mapTotal_incl, D.mapTotal_incl, D.mapTotal_incl, D.map_comp]
    | add x y hx hy => simp only [map_add, hx, hy]

end DegreewiseTheory

end OrlikSolomon
