/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import OrlikSolomon.Geometry.SmoothAlg
public import OrlikSolomon.Grading.Basic

/-!
# The ordinary cohomology theory

This file defines the structure `OrlikSolomon.OrdinaryTheory`, the input of the whole project: the
main theorems are stated for any term of this type. Blueprint: `def:cohomology`, items C1–C5.

The structure holds the blueprint's axioms and nothing else. It has **no field** asserting a
logarithmic class, logarithmic generation, arrangement vanishing, surjectivity of residues,
vanishing of Gysin maps, a short exact deletion sequence, freeness, or the structure theorem. Those
are outputs of the proof.

## Main definitions

* `OrlikSolomon.OrdinaryTheory k ℬ`: an ordinary cohomology theory on `SmoothAlg k`, with
  coefficients in the `R`-algebra `B` with weight grading `ℬ`.
* `OrdinaryTheory.stdResidue`, `OrdinaryTheory.stdGysin`: the residue and Gysin maps of the standard
  pair `(A[t], A, A[t;t⁻¹], t)`, typed by `laurent A`, `A` and `polynomial A`.
* `OrdinaryTheory.gradeZeroEquiv`, `OrdinaryTheory.pointEquiv`, `OrdinaryTheory.polynomialEquiv`:
  the identifications `R ≃ ℬ 0`, `B ≃ C(k)` and `C(A) ≃ C(A[t])`.

## Main results

* `OrdinaryTheory.algebraMap_mem_grading_point_iff`,
  `OrdinaryTheory.exists_algebraMap_eq_of_mem_grading_point`: the map `B → C(k)` carries `ℬ w` onto
  degree `(0, w)`.
* `OrdinaryTheory.subsingleton_obj_of_subsingleton`: the zero ring has zero cohomology. This is the
  blueprint's "empty object" clause of C2, derived from the pair `DivisorPair.emptyDivisor`.
* `OrdinaryTheory.gysin_eq_zero_of_surjective_residue`,
  `OrdinaryTheory.injective_map_j_of_gysin_eq_zero`: the steps of `lem:ses` that follow from
  exactness alone.
* `OrdinaryTheory.exists_mem_grading_gysin_eq`, `OrdinaryTheory.exists_mem_grading_map_j_eq`,
  `OrdinaryTheory.exists_mem_grading_residue_eq`: homogeneous preimages in the exact sequence.

## Working with standard pairs

Write `T.stdResidue A` and `T.stdGysin A`, never `T.residue (standardPair A)`. The object
`(standardPair A).closed` is `A` only at default transparency, so `rw` and `simp` cannot work under
`T.residue (standardPair A)`; see the implementation notes in `Geometry/SmoothAlg`. Every field that
is used at a standard pair has a typed form here, stated with `polynomialToLaurent A`,
`polynomialLift (𝟙 A) 0` and so on, and `simp` and `rw` work on it as usual. A new family of pairs
that lemmas will mention, such as the deletion pair, should get wrappers of the same kind.

Pullbacks are written `T.C.map f`, coerced to a function, and `(T.C.map f).hom` is the underlying
algebra map. The `simp` normal form of a composite is the nested `T.C.map g (T.C.map f x)`, because
`Functor.map_comp` is a `simp` lemma, so `T.map_map` is for `rw` and is not a `simp` lemma.

## How the fields are used

The class `τ` of `lem:gm` is not a field: it is constructed from the fields below.

| Field | First use |
| --- | --- |
| `bijective_algebraMap_gradeZero` | the diagonal in `cor:ordinary` |
| `algebra`, `isScalarTower` | `R`-submodule pieces, `R`-linear components as in `lem:extraction` |
| `grading`, `gradedAlgebra` | the bidegrees of `τ` and of the logarithms |
| `algebraMap_mem_grading` | the shifted summand in `lem:gm`, empty arrangements in `thm:affine` |
| `isHomogeneousOfShift_map` | `[f] ∈ C(X)_{1,1}` in `def:log`, the affine line and the point |
| `isGradedCommutative` | exterior relations of the logarithms in `def:realization` |
| `bijective_algebraMap_point` | `lem:gm` |
| `eq_zero_of_mem_grading_point` | `lem:gm`, `[c] = 0` in `lem:log-basic` |
| `bijective_map_polynomialC` | `lem:gm`, `lem:log-mul`, `lem:gm-product`, the empty arrangement |
| `isHomogeneousOfShift_gysin` | Gysin vanishing in `lem:gm` |
| `isHomogeneousOfShift_residue` | extracting `τ` in `lem:gm`, the bound in `thm:generation` |
| `exact_gysin_map` | `lem:gm`, `lem:ses` |
| `exact_map_residue` | `lem:gm`, `lem:log-mul`, `lem:gm-product`, `lem:ses` |
| `exact_residue_gysin` | `lem:gm`, `lem:ses` |
| `residue_map` | `lem:log-mul`, `lem:log-residue` |
| `residue_mul_map` | `lem:log-residue`, `lem:gm-product`, `lem:comparison-residue` |
| `gysin_map` | no step of the blueprint's proof: C5 asks for the whole sequence to commute |

`lem:standard-bridge` would build a term of this type by taking `C(A) = ⨁ H^{p,w}(A)`, with
`grading` the images of the summands. The direct sum has its own `R`-algebra structure, which is why
`algebra` is a field, tied to `B` by `isScalarTower`, rather than a structure defined through `B`.

## Implementation notes

`algebra`, `isScalarTower` and `gradedAlgebra` are instances, so `T.C.obj A` is an `R`-algebra with
`R`-submodules `T.grading A i`. In the degenerate case `R = B` the two `B`-algebra structures on
`T.C.obj A` agree by `isScalarTower`, but not definitionally.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg OrlikSolomon.DivisorPair

universe u v w z

namespace OrlikSolomon

/-- An *ordinary cohomology theory* on smooth `k`-algebras, with coefficients in the commutative
`R`-algebra `B` with weight grading `ℬ`. It assigns to a smooth affine `X = Spec A` its total
cohomology `C(X) = ⨁_{(p, w)} H^{p, w}(X)`, a possibly noncommutative `B`-algebra bigraded by
`R`-submodules, where `p` is the cohomological degree and `w` the weight. Blueprint:
`def:cohomology`.

Cohomology is **covariant** on `SmoothAlg k`, whose morphisms run in the direction of algebras: a
map `O(Y) ⟶ O(X)` induces the pullback `C(Y) → C(X)` along `X → Y`.

**Check against singular cohomology, by hand.** Every field was checked by hand against complex
singular cohomology, and the comments on the fields record the outcome. This is a mathematical
argument, not a formal one: no such instance exists in Lean. The only theory constructed here is the
zero theory in `Examples/Sanity`, which tests the zero-ring edge case and not the substantive
axioms. So the nonvacuity of the main theorem for nonzero coefficients rests on this check.

The model is as follows, for `k = ℂ` or a chosen embedding `k → ℂ`, and any commutative ring `R`.
Put `B = R[t, t⁻¹]` with `ℬ w = R t^w`, and `H^{p, w}(X) = H^p(X(ℂ); R) t^w`, so that
`C(X) = H^*(X(ℂ); R)[t, t⁻¹]` with `t` central of degree `(0, 1)`. The Gysin map is the topological
one times `t`, and the residue is the topological one times `t⁻¹`, which gives exactly the shifts
`(2, 1)` and `(-1, -1)`. This is a consistency interpretation, not a claim that every field `k` has
a Betti realization. The topological inputs are the long exact sequence of `(X(ℂ), U(ℂ))` and the
Thom isomorphism `H^{p - 2}(D(ℂ)) ≃ H^p(X(ℂ), U(ℂ))` of the complex normal line of `D`.

The boundary projection formula is stated only for `α` of degree `(1, 1)`, as the blueprint allows:
a weaker hypothesis gives a stronger theorem. There is no axiom for the empty object, since
`OrdinaryTheory.subsingleton_obj_of_subsingleton` derives it. -/
structure OrdinaryTheory (k : Type u) [CommRing k] {R : Type v} [CommRing R] {B : Type w}
    [CommRing B] [Algebra R B] (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] where
  /-- C1: the structure map identifies `R` with the weight-zero part `ℬ 0` of `B`.
  In the model, `R → R t⁰` is the identity. -/
  bijective_algebraMap_gradeZero : Function.Bijective (algebraMap R (ℬ 0))
  /-- C1, C2: the total cohomology, as a functor to `B`-algebras. Its values need not be
  commutative, and its morphisms are unital `B`-algebra maps. Mathlib's `Algebra` makes the
  `B`-action central, as C1 asks.
  In the model, `f ↦ f^*` on `H^*(X(ℂ); R)[t, t⁻¹]`, extended `t`-linearly. Cup products of odd
  classes do not commute, so this cannot be `CommAlgCat B`. -/
  C : SmoothAlg k ⥤ AlgCat.{z} B
  /-- C1: each `C(X)` is an `R`-algebra.
  In the model, this is the `R`-algebra structure of `H^*(X(ℂ); R)[t, t⁻¹]`. -/
  [algebra : ∀ A : SmoothAlg k, Algebra R (C.obj A)]
  /-- C1: the `R`-algebra structure of `C(X)` is the one induced from `B`.
  In the model, `r x = (r t⁰) x`. -/
  [isScalarTower : ∀ A : SmoothAlg k, IsScalarTower R B (C.obj A)]
  /-- C1: the piece `H^{p, w}(X)` of `C(X)`, as an `R`-submodule. It is not a `B`-submodule, since
  multiplying by `ℬ v` changes the weight.
  In the model, `H^p(X(ℂ); R) t^w`. -/
  grading (A : SmoothAlg k) : ℤ × ℤ → Submodule R (C.obj A)
  /-- C1: `C(X)` is the internal direct sum of its pieces, compatibly with products.
  In the model, the cup product is additive in `p` and `t^w t^v = t^(w + v)`. -/
  [gradedAlgebra : ∀ A : SmoothAlg k, GradedAlgebra (grading A)]
  /-- C1: the map `B → C(X)` sends `ℬ w` into degree `(0, w)`.
  In the model, `r t^w ↦ r 1 t^w`, with `1 ∈ H⁰(X(ℂ); R)`. -/
  algebraMap_mem_grading (A : SmoothAlg k) {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (C.obj A) b ∈ grading A (0, w)
  /-- C2: pullbacks preserve bidegrees.
  In the model, `f^*` preserves `p` and is `t`-linear. -/
  isHomogeneousOfShift_map {A D : SmoothAlg k} (f : A ⟶ D) :
    IsHomogeneousOfShift (grading A) (grading D) 0 (C.map f)
  /-- C2: homogeneous classes supercommute, with a sign depending only on cohomological degree. It
  does not follow that an odd class squares to zero, and nothing here assumes this.
  In the model, this is graded commutativity of the cup product, with `t` central. -/
  isGradedCommutative (A : SmoothAlg k) : IsGradedCommutative (grading A) Prod.fst
  /-- C3: the point is identified with `B`, through the structure map.
  In the model, `H^*(pt; R) = R`, so `C(pt) = R[t, t⁻¹] = B`. -/
  bijective_algebraMap_point : Function.Bijective (algebraMap B (C.obj (point k)))
  /-- C3: the cohomology of the point is concentrated in cohomological degree zero.
  In the model, `H^p(pt; R) = 0` for `p ≠ 0`. -/
  eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : C.obj (point k)}
    (hx : x ∈ grading (point k) (p, w)) : x = 0
  /-- C3: pullback along `X × 𝔸¹ → X` is bijective, for every smooth `X`.
  In the model, `X(ℂ) × ℂ → X(ℂ)` is a homotopy equivalence. -/
  bijective_map_polynomialC (A : SmoothAlg k) : Function.Bijective (C.map (polynomialC A))
  /-- C4: the Gysin map `C(D) → C(X)` of a divisor pair.
  In the model, the topological Gysin map `H^{p - 2}(D(ℂ)) → H^p(X(ℂ))`, namely the Thom
  isomorphism followed by `H^p(X(ℂ), U(ℂ)) → H^p(X(ℂ))`, times `t`. -/
  gysin (P : DivisorPair k) : C.obj P.closed →ₗ[B] C.obj P.ambient
  /-- C4: the residue map `C(U) → C(D)` of a divisor pair.
  In the model, the topological residue `H^p(U(ℂ)) → H^{p - 1}(D(ℂ))`, namely the connecting map
  of `(X(ℂ), U(ℂ))` followed by the inverse Thom isomorphism, times `t⁻¹`. -/
  residue (P : DivisorPair k) : C.obj P.compl →ₗ[B] C.obj P.closed
  /-- C4: the Gysin map has shift `(2, 1)`.
  In the model, the Thom class has degree `2`, and the factor `t` adds `1` to the weight. -/
  isHomogeneousOfShift_gysin (P : DivisorPair k) :
    IsHomogeneousOfShift (grading P.closed) (grading P.ambient) (2, 1) (gysin P)
  /-- C4: the residue map has shift `(-1, -1)`.
  In the model, the connecting map adds `1` to `p`, the Thom isomorphism subtracts `2`, and the
  factor `t⁻¹` subtracts `1` from the weight. -/
  isHomogeneousOfShift_residue (P : DivisorPair k) :
    IsHomogeneousOfShift (grading P.compl) (grading P.closed) (-1, -1) (residue P)
  /-- C4: `im g = ker j^*`.
  In the model, exactness of `H^p(X(ℂ), U(ℂ)) → H^p(X(ℂ)) → H^p(U(ℂ))`, summed over `(p, w)`. -/
  exact_gysin_map (P : DivisorPair k) : Function.Exact (gysin P) (C.map P.j)
  /-- C4: `im j^* = ker r`.
  In the model, exactness of `H^p(X(ℂ)) → H^p(U(ℂ)) → H^{p + 1}(X(ℂ), U(ℂ))`, summed over
  `(p, w)`. -/
  exact_map_residue (P : DivisorPair k) : Function.Exact (C.map P.j) (residue P)
  /-- C4: `im r = ker g`. Together with the two previous fields this encodes a long exact sequence,
  **not** a short exact one.
  In the model, exactness of `H^p(U(ℂ)) → H^{p + 1}(X(ℂ), U(ℂ)) → H^{p + 1}(X(ℂ))`, summed over
  `(p, w)`. -/
  exact_residue_gysin (P : DivisorPair k) : Function.Exact (residue P) (gysin P)
  /-- C5: the Gysin map commutes with transverse pullback.
  In the model, the Thom class of `D_P` pulls back to that of `D_Q`, because a transverse morphism
  induces a `ℂ`-linear isomorphism of normal lines. The induced square for `j` commutes by
  functoriality and `DivisorPair.Hom.j_comp`. -/
  gysin_map {P Q : DivisorPair k} (f : P ⟶ Q) (x : C.obj P.closed) :
    gysin Q (C.map f.closed x) = C.map f.ambient (gysin P x)
  /-- C5: the residue map commutes with transverse pullback.
  In the model, naturality of the connecting map of a pair, and of the Thom class as in `gysin_map`.
  The orientation of the normal line is preserved because morphisms are `k`-algebra maps and the
  multiplier in `DivisorPair.Hom.associated_eqn` is a unit: `z ↦ x²` is excluded, and it would
  multiply by two on `H¹(ℂ^*)`. -/
  residue_map {P Q : DivisorPair k} (f : P ⟶ Q) (x : C.obj P.compl) :
    residue Q (C.map f.compl x) = C.map f.closed (residue P x)
  /-- C5: the boundary projection formula, with the degree-one factor first, for `α` of degree
  `(1, 1)` and an arbitrary `β` on the ambient space.
  In the model, the formula holds for every `α`: `δ(α ∪ j^*β) = δ(α) ∪ β` for the connecting map
  `δ`, with no sign because `α` comes first, and the Thom class has even degree. -/
  residue_mul_map (P : DivisorPair k) {α : C.obj P.compl} (hα : α ∈ grading P.compl (1, 1))
    (β : C.obj P.ambient) :
    residue P (α * C.map P.j β) = residue P α * C.map P.i β

namespace OrdinaryTheory

attribute [instance] algebra isScalarTower gradedAlgebra

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {A D E : SmoothAlg k}

/-! ### Coefficients -/

section Coefficients

/-- The identification of `R` with the weight-zero part of `B`. Blueprint: item C1 of
`def:cohomology`. -/
def gradeZeroEquiv : R ≃ₐ[R] ℬ 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (ℬ 0)) T.bijective_algebraMap_gradeZero

@[simp] lemma coe_gradeZeroEquiv_apply (r : R) :
    (T.gradeZeroEquiv r : B) = algebraMap R B r := rfl

include T in
lemma injective_algebraMap : Function.Injective (algebraMap R B) := fun _ _ h ↦
  T.bijective_algebraMap_gradeZero.1 (Subtype.ext h)

include T in
/-- An element of weight zero comes from `R`. -/
lemma exists_algebraMap_eq_of_mem_zero {b : B} (hb : b ∈ ℬ 0) : ∃ r, algebraMap R B r = b :=
  let ⟨r, hr⟩ := T.bijective_algebraMap_gradeZero.2 ⟨b, hb⟩
  ⟨r, congrArg Subtype.val hr⟩

end Coefficients

/-! ### The bigrading -/

section Grading

lemma one_mem_grading (A : SmoothAlg k) : (1 : T.C.obj A) ∈ T.grading A (0, 0) :=
  SetLike.one_mem_graded (T.grading A)

lemma mul_mem_grading {p w q v : ℤ} {x y : T.C.obj A} (hx : x ∈ T.grading A (p, w))
    (hy : y ∈ T.grading A (q, v)) : x * y ∈ T.grading A (p + q, w + v) :=
  SetLike.mul_mem_graded hx hy

/-- Multiplying by a coefficient of weight `v` adds `v` to the weight. -/
lemma smul_mem_grading {p w v : ℤ} {b : B} {x : T.C.obj A} (hb : b ∈ ℬ v)
    (hx : x ∈ T.grading A (p, w)) : b • x ∈ T.grading A (p, w + v) := by
  rw [Algebra.smul_def, add_comm w v, ← zero_add p]
  exact T.mul_mem_grading (T.algebraMap_mem_grading A hb) hx

/-- Supercommutativity of homogeneous classes, at literal bidegrees. Blueprint: item C2 of
`def:cohomology`. -/
lemma mul_comm_of_mem_grading {p w q v : ℤ} {x y : T.C.obj A} (hx : x ∈ T.grading A (p, w))
    (hy : y ∈ T.grading A (q, v)) : x * y = (p * q).negOnePow • (y * x) :=
  T.isGradedCommutative A hx hy

/-- Classes of odd cohomological degree anticommute. -/
lemma mul_eq_neg_of_odd {p w q v : ℤ} {x y : T.C.obj A} (hp : Odd p) (hq : Odd q)
    (hx : x ∈ T.grading A (p, w)) (hy : y ∈ T.grading A (q, v)) : x * y = -(y * x) :=
  (T.isGradedCommutative A).mul_eq_neg_of_odd hp hq hx hy

/-- Components of a coefficient: the map `B → C(X)` commutes with taking homogeneous components. -/
lemma coe_decompose_algebraMap (A : SmoothAlg k) (b : B) (w : ℤ) :
    (decompose (T.grading A) (algebraMap B (T.C.obj A) b) (0, w) : T.C.obj A) =
      algebraMap B (T.C.obj A) (decompose ℬ b w) := by
  induction b using Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous v m =>
    obtain rfl | hv := eq_or_ne v w
    · rw [decompose_of_mem_same _ (T.algebraMap_mem_grading A m.2), decompose_coe, of_eq_same]
    · rw [decompose_of_mem_ne _ (T.algebraMap_mem_grading A m.2) (by simpa using hv),
        decompose_of_mem_ne ℬ m.2 hv, map_zero]
  | add x y hx hy => simp [hx, hy, Submodule.coe_add]

end Grading

/-! ### Pullbacks -/

section Pullback

/-- Pullbacks preserve bidegrees. Blueprint: item C2 of `def:cohomology`. -/
lemma map_mem_grading (f : A ⟶ D) {i : ℤ × ℤ} {x : T.C.obj A} (hx : x ∈ T.grading A i) :
    T.C.map f x ∈ T.grading D i :=
  isHomogeneousOfShift_zero_iff.1 (T.isHomogeneousOfShift_map f) hx

/-- A composite of pullbacks. This is for `rw`: it is the reverse of what `simp` does. -/
lemma map_map (f : A ⟶ D) (g : D ⟶ E) (x : T.C.obj A) :
    T.C.map g (T.C.map f x) = T.C.map (f ≫ g) x := by
  simp

@[simp] lemma map_algebraMap (f : A ⟶ D) (b : B) :
    T.C.map f (algebraMap B (T.C.obj A) b) = algebraMap B (T.C.obj D) b :=
  (T.C.map f).hom.commutes b

/-- Pullback along a map with a retraction is injective. This gives injectivity of the pullback to
`X × 𝔾ₘ`, by the section `t = 1`. -/
lemma injective_map_of_comp_eq_id {f : A ⟶ D} {g : D ⟶ A} (h : f ≫ g = 𝟙 A) :
    Function.Injective (T.C.map f) :=
  Function.LeftInverse.injective (g := T.C.map g) fun x ↦ by
    rw [map_map, h]
    simp

end Pullback

/-! ### The point -/

section Point

/-- The identification of the cohomology of the point with `B`. Blueprint: item C3 of
`def:cohomology`. -/
def pointEquiv : B ≃ₐ[B] T.C.obj (point k) :=
  AlgEquiv.ofBijective (Algebra.ofId B _) T.bijective_algebraMap_point

@[simp] lemma pointEquiv_apply (b : B) :
    T.pointEquiv b = algebraMap B (T.C.obj (point k)) b := rfl

/-- The map `B → C(k)` reflects weights. -/
lemma algebraMap_mem_grading_point_iff {w : ℤ} {b : B} :
    algebraMap B (T.C.obj (point k)) b ∈ T.grading (point k) (0, w) ↔ b ∈ ℬ w := by
  refine ⟨fun h ↦ ?_, T.algebraMap_mem_grading _⟩
  have hb := T.coe_decompose_algebraMap (point k) b w
  rw [decompose_of_mem_same _ h] at hb
  rw [T.bijective_algebraMap_point.1 hb]
  exact (decompose ℬ b w).2

/-- The map `B → C(k)` carries `ℬ w` onto degree `(0, w)`. Blueprint: item C3 of
`def:cohomology`. -/
lemma exists_algebraMap_eq_of_mem_grading_point {w : ℤ} {x : T.C.obj (point k)}
    (hx : x ∈ T.grading (point k) (0, w)) : ∃ b ∈ ℬ w, algebraMap B _ b = x := by
  obtain ⟨b, rfl⟩ := T.bijective_algebraMap_point.2 x
  exact ⟨b, T.algebraMap_mem_grading_point_iff.1 hx, rfl⟩

end Point

/-! ### The affine line -/

section AffineLine

/-- Affine-line invariance as an algebra equivalence. It preserves bidegrees by
`isHomogeneousOfShift_map`. Blueprint: item C3 of `def:cohomology`. -/
def polynomialEquiv (A : SmoothAlg k) : T.C.obj A ≃ₐ[B] T.C.obj (polynomial A) :=
  AlgEquiv.ofBijective (T.C.map (polynomialC A)).hom (T.bijective_map_polynomialC A)

@[simp] lemma polynomialEquiv_apply (x : T.C.obj A) :
    T.polynomialEquiv A x = T.C.map (polynomialC A) x := rfl

/-- A homogeneous class on `X × 𝔸¹` is the pullback of a homogeneous class of the same degree. -/
lemma exists_mem_grading_map_polynomialC_eq {i : ℤ × ℤ} {x : T.C.obj (polynomial A)}
    (hx : x ∈ T.grading (polynomial A) i) :
    ∃ y ∈ T.grading A i, T.C.map (polynomialC A) y = x :=
  (T.isHomogeneousOfShift_map (polynomialC A)).exists_mem_preimage_of_surjective
    (T.bijective_map_polynomialC A).2 (add_zero i) hx

@[simp] lemma map_polynomialLift_map_polynomialC (φ : A ⟶ D) (b : D) (x : T.C.obj A) :
    T.C.map (polynomialLift φ b) (T.C.map (polynomialC A) x) = T.C.map φ x := by
  rw [map_map, polynomialC_comp_polynomialLift]

@[simp] lemma map_polynomialToLaurent_map_polynomialC (x : T.C.obj A) :
    T.C.map (polynomialToLaurent A) (T.C.map (polynomialC A) x) = T.C.map (laurentC A) x := by
  rw [map_map, polynomialC_comp_polynomialToLaurent]

@[simp] lemma map_laurentLift_map_laurentC (φ : A ⟶ D) (u : Dˣ) (x : T.C.obj A) :
    T.C.map (laurentLift φ u) (T.C.map (laurentC A) x) = T.C.map φ x := by
  rw [map_map, laurentC_comp_laurentLift]

@[simp] lemma map_laurentSection_map_laurentC (x : T.C.obj A) :
    T.C.map (laurentSection A) (T.C.map (laurentC A) x) = x := by
  simp [laurentSection]

/-- Restriction to the section `t = b` of `X × 𝔸¹` is bijective, being a one-sided inverse of the
bijective pullback along the projection. -/
lemma bijective_map_polynomialLift_id (A : SmoothAlg k) (b : A) :
    Function.Bijective (T.C.map (polynomialLift (𝟙 A) b)) := by
  refine ⟨fun x y h ↦ ?_, fun x ↦ ⟨T.C.map (polynomialC A) x, by simp⟩⟩
  obtain ⟨x, rfl⟩ := (T.bijective_map_polynomialC A).2 x
  obtain ⟨y, rfl⟩ := (T.bijective_map_polynomialC A).2 y
  simp only [map_polynomialLift_map_polynomialC] at h
  simpa using congrArg _ h

/-- Pullback to `X × 𝔾ₘ` is injective, by the section `t = 1`. -/
lemma injective_map_laurentC (A : SmoothAlg k) : Function.Injective (T.C.map (laurentC A)) :=
  T.injective_map_of_comp_eq_id (laurentC_comp_laurentSection A)

end AffineLine

/-! ### Divisor pairs -/

section Divisor

variable (P : DivisorPair k)

@[simp] lemma map_j_gysin (x : T.C.obj P.closed) : T.C.map P.j (T.gysin P x) = 0 :=
  (T.exact_gysin_map P).apply_apply_eq_zero x

@[simp] lemma residue_map_j (x : T.C.obj P.ambient) : T.residue P (T.C.map P.j x) = 0 :=
  (T.exact_map_residue P).apply_apply_eq_zero x

@[simp] lemma gysin_residue (x : T.C.obj P.compl) : T.gysin P (T.residue P x) = 0 :=
  (T.exact_residue_gysin P).apply_apply_eq_zero x

/-- Coefficients have zero residue. -/
@[simp] lemma residue_algebraMap (b : B) : T.residue P (algebraMap B (T.C.obj P.compl) b) = 0 := by
  rw [← T.map_algebraMap P.j b, residue_map_j]

@[simp] lemma residue_one : T.residue P 1 = 0 := by
  simpa using T.residue_algebraMap P 1

/-- Homogeneous extraction at `im g = ker j^*`, by `lem:extraction`. -/
lemma exists_mem_grading_gysin_eq {i j : ℤ × ℤ} (hij : i + (2, 1) = j) {x : T.C.obj P.ambient}
    (hx : x ∈ T.grading P.ambient j) (h : T.C.map P.j x = 0) :
    ∃ y ∈ T.grading P.closed i, T.gysin P y = x :=
  (T.isHomogeneousOfShift_gysin P).exists_mem_preimage_of_exact (T.exact_gysin_map P) hij hx h

/-- Homogeneous extraction at `im j^* = ker r`, by `lem:extraction`. -/
lemma exists_mem_grading_map_j_eq {i : ℤ × ℤ} {x : T.C.obj P.compl}
    (hx : x ∈ T.grading P.compl i) (h : T.residue P x = 0) :
    ∃ y ∈ T.grading P.ambient i, T.C.map P.j y = x :=
  (T.isHomogeneousOfShift_map P.j).exists_mem_preimage_of_exact (T.exact_map_residue P)
    (add_zero i) hx h

/-- Homogeneous extraction at `im r = ker g`, by `lem:extraction`. -/
lemma exists_mem_grading_residue_eq {i j : ℤ × ℤ} (hij : i + (-1, -1) = j) {x : T.C.obj P.closed}
    (hx : x ∈ T.grading P.closed j) (h : T.gysin P x = 0) :
    ∃ y ∈ T.grading P.compl i, T.residue P y = x :=
  (T.isHomogeneousOfShift_residue P).exists_mem_preimage_of_exact (T.exact_residue_gysin P) hij hx h

/-- A surjective residue forces the Gysin map to vanish. This and
`injective_map_j_of_gysin_eq_zero` are the steps of `lem:ses` that follow from exactness alone. -/
lemma gysin_eq_zero_of_surjective_residue (h : Function.Surjective (T.residue P)) :
    T.gysin P = 0 :=
  LinearMap.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := h x
    simp

/-- If the Gysin map vanishes, the open pullback is injective. -/
lemma injective_map_j_of_gysin_eq_zero (h : T.gysin P = 0) :
    Function.Injective (T.C.map P.j) := by
  refine (injective_iff_map_eq_zero (T.C.map P.j).hom).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (T.exact_gysin_map P x).1 hx
  simp [h]

/-- If the open pullback of a pair is bijective, then the divisor has zero cohomology. The Gysin map
is both zero and injective. -/
lemma subsingleton_closed_of_bijective (hj : Function.Bijective (T.C.map P.j)) :
    Subsingleton (T.C.obj P.closed) := by
  have hr (x : T.C.obj P.compl) : T.residue P x = 0 := (T.exact_map_residue P x).2 (hj.2 x)
  have hg (x : T.C.obj P.closed) : T.gysin P x = 0 :=
    hj.1 (by simp)
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (T.exact_residue_gysin P x).1 (hg x)
  exact hr y

/-- The cohomology of a zero ring is zero, so the empty scheme has zero cohomology. This is the
last clause of C2 in `def:cohomology`, and it needs no axiom: the empty divisor of the point has
bijective open pullback. -/
lemma subsingleton_obj_of_subsingleton (A : SmoothAlg k) [Subsingleton A] :
    Subsingleton (T.C.obj A) :=
  T.subsingleton_closed_of_bijective (emptyDivisor (point k) A) <| by
    change Function.Bijective (T.C.map (𝟙 (point k)))
    simpa using Function.bijective_id

variable {P} {Q : DivisorPair k}

/-- The square of `j` for a transverse morphism commutes, by functoriality. With `gysin_map` and
`residue_map`, this is the commutativity of the whole sequence asked for by item C5 of
`def:cohomology`. -/
lemma map_compl_map_j (f : P ⟶ Q) (x : T.C.obj P.ambient) :
    T.C.map f.compl (T.C.map P.j x) = T.C.map Q.j (T.C.map f.ambient x) := by
  rw [map_map, map_map, f.j_comp]

/-- The square of `i` for a transverse morphism commutes, by functoriality. -/
lemma map_closed_map_i (f : P ⟶ Q) (x : T.C.obj P.ambient) :
    T.C.map f.closed (T.C.map P.i x) = T.C.map Q.i (T.C.map f.ambient x) := by
  rw [map_map, map_map, f.i_comp]

end Divisor

/-! ### Standard pairs

These are the fields of the structure at `standardPair A`, typed by `polynomial A`, `A` and
`laurent A`, and by the maps `polynomialLift (𝟙 A) 0` and `polynomialToLaurent A`. See "Working with
standard pairs" in the module docstring. -/

section Standard

/-- The residue `C(X × 𝔾ₘ) → C(X)` of the standard pair of `X`, typed so that `rw` and `simp` work.
Use this rather than `T.residue (standardPair A)`. -/
def stdResidue (A : SmoothAlg k) : T.C.obj (laurent A) →ₗ[B] T.C.obj A :=
  T.residue (standardPair A)

/-- The Gysin map `C(X) → C(X × 𝔸¹)` of the standard pair of `X`, typed so that `rw` and `simp`
work. Use this rather than `T.gysin (standardPair A)`. -/
def stdGysin (A : SmoothAlg k) : T.C.obj A →ₗ[B] T.C.obj (polynomial A) :=
  T.gysin (standardPair A)

/-- The wrapper is the residue of the standard pair, by definition. To specialize a result about a
general pair `P`, use it with `exact`, since `rw` cannot see through the types. -/
lemma residue_standardPair : T.residue (standardPair A) = T.stdResidue A := rfl

/-- The wrapper is the Gysin map of the standard pair, by definition. -/
lemma gysin_standardPair : T.gysin (standardPair A) = T.stdGysin A := rfl

lemma isHomogeneousOfShift_stdResidue (A : SmoothAlg k) :
    IsHomogeneousOfShift (T.grading (laurent A)) (T.grading A) (-1, -1) (T.stdResidue A) :=
  T.isHomogeneousOfShift_residue (standardPair A)

lemma isHomogeneousOfShift_stdGysin (A : SmoothAlg k) :
    IsHomogeneousOfShift (T.grading A) (T.grading (polynomial A)) (2, 1) (T.stdGysin A) :=
  T.isHomogeneousOfShift_gysin (standardPair A)

lemma exact_stdGysin_map (A : SmoothAlg k) :
    Function.Exact (T.stdGysin A) (T.C.map (polynomialToLaurent A)) :=
  T.exact_gysin_map (standardPair A)

lemma exact_map_stdResidue (A : SmoothAlg k) :
    Function.Exact (T.C.map (polynomialToLaurent A)) (T.stdResidue A) :=
  T.exact_map_residue (standardPair A)

lemma exact_stdResidue_stdGysin (A : SmoothAlg k) :
    Function.Exact (T.stdResidue A) (T.stdGysin A) :=
  T.exact_residue_gysin (standardPair A)

/-- Classes pulled back from `X × 𝔸¹` have zero residue. -/
@[simp] lemma stdResidue_map_polynomialToLaurent (x : T.C.obj (polynomial A)) :
    T.stdResidue A (T.C.map (polynomialToLaurent A) x) = 0 :=
  (T.exact_map_stdResidue A).apply_apply_eq_zero x

/-- Classes pulled back from `X` have zero residue. -/
@[simp] lemma stdResidue_map_laurentC (x : T.C.obj A) :
    T.stdResidue A (T.C.map (laurentC A) x) = 0 := by
  rw [← T.map_polynomialToLaurent_map_polynomialC, stdResidue_map_polynomialToLaurent]

/-- Coefficients have zero residue. -/
@[simp] lemma stdResidue_algebraMap (b : B) :
    T.stdResidue A (algebraMap B (T.C.obj (laurent A)) b) = 0 :=
  T.residue_algebraMap (standardPair A) b

@[simp] lemma stdResidue_one : T.stdResidue A 1 = 0 :=
  T.residue_one (standardPair A)

/-- Homogeneous extraction at `im j^* = ker r`, for the standard pair. -/
lemma exists_mem_grading_map_polynomialToLaurent_eq {i : ℤ × ℤ} {x : T.C.obj (laurent A)}
    (hx : x ∈ T.grading (laurent A) i) (h : T.stdResidue A x = 0) :
    ∃ y ∈ T.grading (polynomial A) i, T.C.map (polynomialToLaurent A) y = x :=
  T.exists_mem_grading_map_j_eq (standardPair A) hx h

/-- Homogeneous extraction at `im r = ker g`, for the standard pair. -/
lemma exists_mem_grading_stdResidue_eq {i j : ℤ × ℤ} (hij : i + (-1, -1) = j) {x : T.C.obj A}
    (hx : x ∈ T.grading A j) (h : T.stdGysin A x = 0) :
    ∃ y ∈ T.grading (laurent A) i, T.stdResidue A y = x :=
  T.exists_mem_grading_residue_eq (standardPair A) hij hx h

/-- The boundary projection formula of the standard pair. Blueprint: item C5 of `def:cohomology`. -/
lemma stdResidue_mul_map {α : T.C.obj (laurent A)} (hα : α ∈ T.grading (laurent A) (1, 1))
    (β : T.C.obj (polynomial A)) :
    T.stdResidue A (α * T.C.map (polynomialToLaurent A) β) =
      T.stdResidue A α * T.C.map (polynomialLift (𝟙 A) 0) β :=
  T.residue_mul_map (standardPair A) hα β

/-- The boundary projection formula for a class pulled back from `X`. -/
lemma stdResidue_mul_map_laurentC {α : T.C.obj (laurent A)}
    (hα : α ∈ T.grading (laurent A) (1, 1)) (β : T.C.obj A) :
    T.stdResidue A (α * T.C.map (laurentC A) β) = T.stdResidue A α * β := by
  have h := T.stdResidue_mul_map hα (T.C.map (polynomialC A) β)
  simpa using h

/-- Residue naturality along the transverse morphism `standardMap φ u`, which is `φ` on constants
and `t ↦ u * t`. -/
lemma stdResidue_map_laurentLift (φ : A ⟶ D) (u : Dˣ) (x : T.C.obj (laurent A)) :
    T.stdResidue D
        (T.C.map (laurentLift (φ ≫ laurentC D) (mapUnits (laurentC D) u * laurentT D)) x) =
      T.C.map φ (T.stdResidue A x) :=
  T.residue_map (standardMap φ u) x

/-- Gysin naturality along the transverse morphism `standardMap φ u`. -/
lemma stdGysin_map (φ : A ⟶ D) (u : Dˣ) (x : T.C.obj A) :
    T.stdGysin D (T.C.map φ x) =
      T.C.map (polynomialLift (φ ≫ polynomialC D) (polynomialC D u * polynomialX D))
        (T.stdGysin A x) :=
  T.gysin_map (standardMap φ u) x

/-- Residue naturality along `z ↦ u * t`, from the standard pair of the point to the standard pair
of `X`. This is what gives both logarithmic classes in `lem:log-mul` residue `1`. -/
lemma stdResidue_map_gmHom (u : Dˣ) (x : T.C.obj (gm k)) :
    T.stdResidue D (T.C.map (gmHom (mapUnits (laurentC D) u * laurentT D)) x) =
      T.C.map (fromPoint D) (T.stdResidue (point k) x) := by
  have h := T.stdResidue_map_laurentLift (fromPoint D) u x
  rwa [← standardMap_compl, standardMap_fromPoint_compl] at h

/-- Residue naturality along `z ↦ t`, from the standard pair of the point to the standard pair of
`X`. -/
lemma stdResidue_map_gmHom_laurentT (x : T.C.obj (gm k)) :
    T.stdResidue D (T.C.map (gmHom (laurentT D)) x) =
      T.C.map (fromPoint D) (T.stdResidue (point k) x) := by
  simpa using T.stdResidue_map_gmHom (1 : Dˣ) x

/-- Residue naturality along the transverse morphism `standardLift φ u` to any pair `P`, which is
`φ` on constants and `t ↦ u * P.eqn`. -/
lemma residue_map_laurentLift {P : DivisorPair k} (φ : A ⟶ P.ambient) (u : P.ambientˣ)
    (x : T.C.obj (laurent A)) :
    T.residue P (T.C.map (laurentLift (φ ≫ P.j) (mapUnits P.j u * P.eqnUnit)) x) =
      T.C.map (φ ≫ P.i) (T.stdResidue A x) :=
  T.residue_map (standardLift φ u) x

/-- Gysin naturality along the transverse morphism `standardLift φ u` to any pair `P`. -/
lemma gysin_map_standardLift {P : DivisorPair k} (φ : A ⟶ P.ambient) (u : P.ambientˣ)
    (x : T.C.obj A) :
    T.gysin P (T.C.map (φ ≫ P.i) x) =
      T.C.map (polynomialLift φ (u * P.eqn)) (T.stdGysin A x) :=
  T.gysin_map (standardLift φ u) x

/-- Residue naturality along `z ↦ P.eqn`, from the standard pair of the point to any pair `P`. This
is the first half of `lem:log-residue`. -/
lemma residue_map_gmHom_eqnUnit (P : DivisorPair k) (x : T.C.obj (gm k)) :
    T.residue P (T.C.map (gmHom P.eqnUnit) x) =
      T.C.map (fromPoint P.closed) (T.stdResidue (point k) x) := by
  have h := T.residue_map (fromStandard P) x
  rwa [fromStandard_compl, fromStandard_closed] at h

end Standard

end OrdinaryTheory

end OrlikSolomon
