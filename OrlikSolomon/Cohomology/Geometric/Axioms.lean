/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Axioms
public import OrlikSolomon.Geometry.Schemes.PrincipalPair

/-!
# Ordinary cohomology on smooth schemes

`Geometric.OrdinaryTheory` has exactly the 22 fields of the algebraic ordinary theory, with
contravariant pullback on an admissible domain of actual schemes. The grading uses `R`-submodules
and commutativity is signed by cohomological degree. No arrangement conclusion or empty-object
condition is an assumption. Blueprint: `def:geo-theory`, `lem:geo-restriction`, `lem:geo-empty`.

The public `obj`, `pull`, and `OverR` wrappers keep variance and scalar structures explicit.

## Main definitions

* `OrdinaryTheory.obj`, `pull`: total cohomology and contravariant pullback.
* `OrdinaryTheory.mapOverR`, `gysinOverR`, `residueOverR`: maps for the specified scalar structure.
* `OrdinaryTheory.standardResidue`, `standardGysin`: maps typed by the chosen product schemes.
* `OrdinaryTheory.restrict`: restriction of all fields along a domain inclusion.

## Main results

* `OrdinaryTheory.pullIso_mem_grading_iff`: an isomorphism preserves and reflects the grading.
* `OrdinaryTheory.subsingleton_closed_of_bijective`: exactness forces vanishing when open pullback
  is bijective. `Transport` derives empty-scheme vanishing from the algebraic empty-divisor
  consequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w z

namespace OrlikSolomon.Geometric

/-- An ordinary cohomology theory on an admissible domain of smooth schemes over `Spec k`.
Its fields are precisely C1–C5, with pullback in the geometric direction. In particular it has no
empty-scheme or arrangement-theoretic axiom. Blueprint: `def:geo-theory`. -/
structure OrdinaryTheory {k : Type u} [CommRing k] (D : SmoothDomain k)
    {R : Type v} [CommRing R] {B : Type w}
    [CommRing B] [Algebra R B] (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] where
  /-- C1: the structure map identifies `R` with the weight-zero part `ℬ 0` of `B`. -/
  bijective_algebraMap_gradeZero : Function.Bijective (algebraMap R (ℬ 0))
  /-- C1, C2: the total cohomology, as a functor to `B`-algebras. Its values need not be
  commutative, and its morphisms are unital `B`-algebra maps. Mathlib's `Algebra` makes the
  `B`-action central, as C1 asks. -/
  C : D.Objᵒᵖ ⥤ AlgCat.{z} B
  /-- C1: each `C(X)` is an `R`-algebra. -/
  [algebra : ∀ A : D.Obj, Algebra R (C.obj (op A))]
  /-- C1: the `R`-algebra structure of `C(X)` is the one induced from `B`. -/
  [isScalarTower : ∀ A : D.Obj, IsScalarTower R B (C.obj (op A))]
  /-- C1: the piece `H^{p, w}(X)` of `C(X)`, as an `R`-submodule. It is not a `B`-submodule, since
  multiplying by `ℬ v` changes the weight. -/
  grading (A : D.Obj) : ℤ × ℤ → Submodule R (C.obj (op A))
  /-- C1: `C(X)` is the internal direct sum of its pieces, compatibly with products. -/
  [gradedAlgebra : ∀ A : D.Obj, GradedAlgebra (grading A)]
  /-- C1: the map `B → C(X)` sends `ℬ w` into degree `(0, w)`. -/
  algebraMap_mem_grading (A : D.Obj) {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (C.obj (op A)) b ∈ grading A (0, w)
  /-- C2: pullbacks preserve bidegrees. -/
  isHomogeneousOfShift_map {X Y : D.Obj} (f : X ⟶ Y) :
    IsHomogeneousOfShift (grading Y) (grading X) 0 (C.map f.op)
  /-- C2: homogeneous classes supercommute, with a sign depending only on cohomological degree. It
  does not follow that an odd class squares to zero, and nothing here assumes this. -/
  isGradedCommutative (A : D.Obj) : IsGradedCommutative (grading A) Prod.fst
  /-- C3: the point is identified with `B`, through the structure map. -/
  bijective_algebraMap_point : Function.Bijective (algebraMap B (C.obj (op D.point)))
  /-- C3: the cohomology of the point is concentrated in cohomological degree zero. -/
  eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : C.obj (op D.point)}
    (hx : x ∈ grading D.point (p, w)) : x = 0
  /-- C3: pullback along `X × 𝔸¹ → X` is bijective, for every smooth `X`. -/
  bijective_pullback_affineLine (X : D.Obj) :
    Function.Bijective (C.map (D.prodAffineLineFst X).op)
  /-- C4: the Gysin map `C(D) → C(X)` of a divisor pair. -/
  gysin (P : DivisorPair D) : C.obj (op P.closed) →ₗ[B] C.obj (op P.ambient)
  /-- C4: the residue map `C(U) → C(D)` of a divisor pair. -/
  residue (P : DivisorPair D) : C.obj (op P.compl) →ₗ[B] C.obj (op P.closed)
  /-- C4: the Gysin map has shift `(2, 1)`. -/
  isHomogeneousOfShift_gysin (P : DivisorPair D) :
    IsHomogeneousOfShift (grading P.closed) (grading P.ambient) (2, 1) (gysin P)
  /-- C4: the residue map has shift `(-1, -1)`. -/
  isHomogeneousOfShift_residue (P : DivisorPair D) :
    IsHomogeneousOfShift (grading P.compl) (grading P.closed) (-1, -1) (residue P)
  /-- C4: `im g = ker j^*`. -/
  exact_gysin_map (P : DivisorPair D) : Function.Exact (gysin P) (C.map P.j.op)
  /-- C4: `im j^* = ker r`. -/
  exact_map_residue (P : DivisorPair D) : Function.Exact (C.map P.j.op) (residue P)
  /-- C4: `im r = ker g`. Together with the two previous fields this encodes a long exact sequence,
  **not** a short exact one. -/
  exact_residue_gysin (P : DivisorPair D) : Function.Exact (residue P) (gysin P)
  /-- C5: the Gysin map commutes with transverse pullback. -/
  gysin_map {P Q : DivisorPair D} (f : P ⟶ Q) (x : C.obj (op Q.closed)) :
    gysin P (C.map f.closed.op x) = C.map f.ambient.op (gysin Q x)
  /-- C5: the residue map commutes with transverse pullback. -/
  residue_map {P Q : DivisorPair D} (f : P ⟶ Q) (x : C.obj (op Q.compl)) :
    residue P (C.map f.compl.op x) = C.map f.closed.op (residue Q x)
  /-- C5: the boundary projection formula, with the degree-one factor first, for `α` of degree
  `(1, 1)` and an arbitrary `β` on the ambient space. -/
  residue_mul_map (P : DivisorPair D) {α : C.obj (op P.compl)} (hα : α ∈ grading P.compl (1, 1))
    (β : C.obj (op P.ambient)) :
    residue P (α * C.map P.j.op β) = residue P α * C.map P.i.op β

namespace OrdinaryTheory

attribute [instance] algebra isScalarTower gradedAlgebra

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The total cohomology algebra of a scheme. This reducible accessor lets the functor fields
and the pullback API use the same ring operations. -/
abbrev obj (X : D.Obj) : AlgCat.{z} B := T.C.obj (op X)

instance objAlgebra (X : D.Obj) : Algebra R (T.obj X) := T.algebra X

instance objIsScalarTower (X : D.Obj) : IsScalarTower R B (T.obj X) := T.isScalarTower X

/-- Contravariant pullback along a scheme morphism. -/
def pull {X Y : D.Obj} (f : X ⟶ Y) : T.obj Y →ₐ[B] T.obj X := (T.C.map f.op).hom

@[simp] lemma map_apply {X Y : D.Obj} (f : X ⟶ Y) (x : T.obj Y) :
    T.C.map f.op x = T.pull f x := rfl

@[simp] lemma pull_id (X : D.Obj) (x : T.obj X) : T.pull (𝟙 X) x = x := by
  change (T.C.map (𝟙 (op X))).hom x = x
  rw [T.C.map_id]
  rfl

@[simp] lemma pull_comp {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (x : T.obj Z) :
    T.pull (f ≫ g) x = T.pull f (T.pull g x) := by simp [pull]

/-- Pullbacks preserve each homogeneous piece. -/
lemma pull_mem_grading {X Y : D.Obj} (f : X ⟶ Y) {i : ℤ × ℤ} {x : T.obj Y}
    (hx : x ∈ T.grading Y i) : T.pull f x ∈ T.grading X i :=
  isHomogeneousOfShift_zero_iff.1 (T.isHomogeneousOfShift_map f) hx

/-- Pullback by an isomorphism, with its inverse supplied by inverse pullback. -/
def pullIso {X Y : D.Obj} (e : X ≅ Y) : T.obj Y ≃ₐ[B] T.obj X where
  __ := T.pull e.hom
  invFun := T.pull e.inv
  left_inv x := by
    change T.pull e.inv (T.pull e.hom x) = x
    rw [← pull_comp]; simp
  right_inv x := by
    change T.pull e.hom (T.pull e.inv x) = x
    rw [← pull_comp]; simp

@[simp] lemma pullIso_apply {X Y : D.Obj} (e : X ≅ Y) (x : T.obj Y) :
    T.pullIso e x = T.pull e.hom x := rfl

@[simp] lemma pullIso_symm_apply {X Y : D.Obj} (e : X ≅ Y) (x : T.obj X) :
    (T.pullIso e).symm x = T.pull e.inv x := rfl

/-- Homotopy invariance in the public pullback notation. -/
lemma bijective_pull_prodAffineLineFst (X : D.Obj) :
    Function.Bijective (T.pull (D.prodAffineLineFst X)) :=
  T.bijective_pullback_affineLine X

/-- The Gysin image is the kernel of open pullback. -/
lemma exact_gysin_pull (P : DivisorPair D) :
    Function.Exact (T.gysin P) (T.pull P.j) := T.exact_gysin_map P

/-- The image of open pullback is the kernel of residue. -/
lemma exact_pull_residue (P : DivisorPair D) :
    Function.Exact (T.pull P.j) (T.residue P) := T.exact_map_residue P

/-- Gysin commutes with transverse pullback, in the public pullback notation. -/
lemma gysin_pull {P Q : DivisorPair D} (f : P ⟶ Q) (x : T.obj Q.closed) :
    T.gysin P (T.pull f.closed x) = T.pull f.ambient (T.gysin Q x) :=
  T.gysin_map f x

/-- Residue commutes with transverse pullback, in the public pullback notation. -/
lemma residue_pull {P Q : DivisorPair D} (f : P ⟶ Q) (x : T.obj Q.compl) :
    T.residue P (T.pull f.compl x) = T.pull f.closed (T.residue Q x) :=
  T.residue_map f x

/-- The boundary projection formula with the degree-one factor first. -/
lemma residue_mul_pull (P : DivisorPair D) {α : T.obj P.compl}
    (hα : α ∈ T.grading P.compl (1, 1)) (β : T.obj P.ambient) :
    T.residue P (α * T.pull P.j β) = T.residue P α * T.pull P.i β :=
  T.residue_mul_map P hα β

/-- Pullback by an isomorphism preserves and reflects the grading. -/
lemma pullIso_mem_grading_iff {X Y : D.Obj} (e : X ≅ Y) {i : ℤ × ℤ} {x : T.obj Y} :
    T.pullIso e x ∈ T.grading X i ↔ x ∈ T.grading Y i := by
  constructor
  · intro hx
    simpa [pullIso, ← pull_comp] using T.pull_mem_grading e.inv hx
  · exact T.pull_mem_grading e.hom

/-- Pullback as an `R`-linear map for the specified scalar structure, including when `R = B`. -/
def mapOverR {X Y : D.Obj} (f : X ⟶ Y) : T.obj Y →ₗ[R] T.obj X :=
  (T.pull f).toLinearMap.restrictScalars R

/-- Gysin as an `R`-linear map for the specified scalar structure. -/
def gysinOverR (P : DivisorPair D) : T.obj P.closed →ₗ[R] T.obj P.ambient :=
  (T.gysin P).restrictScalars R

/-- Residue as an `R`-linear map for the specified scalar structure. -/
def residueOverR (P : DivisorPair D) : T.obj P.compl →ₗ[R] T.obj P.closed :=
  (T.residue P).restrictScalars R

@[simp] lemma mapOverR_apply {X Y : D.Obj} (f : X ⟶ Y) (x : T.obj Y) :
    T.mapOverR f x = T.pull f x := rfl

@[simp] lemma gysinOverR_apply (P : DivisorPair D) (x : T.obj P.closed) :
    T.gysinOverR P x = T.gysin P x := rfl

@[simp] lemma residueOverR_apply (P : DivisorPair D) (x : T.obj P.compl) :
    T.residueOverR P x = T.residue P x := rfl

lemma isHomogeneousOfShift_mapOverR {X Y : D.Obj} (f : X ⟶ Y) :
    IsHomogeneousOfShift (T.grading Y) (T.grading X) 0 (T.mapOverR f) :=
  T.isHomogeneousOfShift_map f

lemma isHomogeneousOfShift_gysinOverR (P : DivisorPair D) :
    IsHomogeneousOfShift (T.grading P.closed) (T.grading P.ambient) (2, 1) (T.gysinOverR P) :=
  T.isHomogeneousOfShift_gysin P

lemma isHomogeneousOfShift_residueOverR (P : DivisorPair D) :
    IsHomogeneousOfShift (T.grading P.compl) (T.grading P.closed) (-1, -1) (T.residueOverR P) :=
  T.isHomogeneousOfShift_residue P

/-- The standard residue, typed by the chosen product with `𝔾ₘ`. -/
def standardResidue (X : D.Obj) : T.obj (D.prodGm X) →ₗ[B] T.obj X :=
  T.residue (DivisorPair.standardPair D X)

/-- The standard Gysin map, typed by the chosen product with `𝔸¹`. -/
def standardGysin (X : D.Obj) : T.obj X →ₗ[B] T.obj (D.prodAffineLine X) :=
  T.gysin (DivisorPair.standardPair D X)

lemma residue_standardPair (X : D.Obj) :
    T.residue (DivisorPair.standardPair D X) = T.standardResidue X := rfl

lemma gysin_standardPair (X : D.Obj) :
    T.gysin (DivisorPair.standardPair D X) = T.standardGysin X := rfl

lemma standardResidue_apply (X : D.Obj) (x : T.obj (D.prodGm X)) :
    T.standardResidue X x = T.residue (DivisorPair.standardPair D X) x := rfl

lemma standardGysin_apply (X : D.Obj) (x : T.obj X) :
    T.standardGysin X x = T.gysin (DivisorPair.standardPair D X) x := rfl

lemma isHomogeneousOfShift_standardResidue (X : D.Obj) :
    IsHomogeneousOfShift (T.grading (D.prodGm X)) (T.grading X) (-1, -1)
      (T.standardResidue X) :=
  T.isHomogeneousOfShift_residue (DivisorPair.standardPair D X)

lemma isHomogeneousOfShift_standardGysin (X : D.Obj) :
    IsHomogeneousOfShift (T.grading X) (T.grading (D.prodAffineLine X)) (2, 1)
      (T.standardGysin X) :=
  T.isHomogeneousOfShift_gysin (DivisorPair.standardPair D X)

lemma exact_standardGysin_pull (X : D.Obj) :
    Function.Exact (T.standardGysin X) (T.pull (D.prodGmToProdAffineLine X)) :=
  T.exact_gysin_pull (DivisorPair.standardPair D X)

lemma exact_pull_standardResidue (X : D.Obj) :
    Function.Exact (T.pull (D.prodGmToProdAffineLine X)) (T.standardResidue X) :=
  T.exact_pull_residue (DivisorPair.standardPair D X)

lemma exact_standardResidue_standardGysin (X : D.Obj) :
    Function.Exact (T.standardResidue X) (T.standardGysin X) :=
  T.exact_residue_gysin (DivisorPair.standardPair D X)

/-- The right projection formula of the standard pair, with the logarithmic factor first. -/
lemma standardResidue_mul_pull (X : D.Obj) {α : T.obj (D.prodGm X)}
    (hα : α ∈ T.grading (D.prodGm X) (1, 1)) (β : T.obj (D.prodAffineLine X)) :
    T.standardResidue X (α * T.pull (D.prodGmToProdAffineLine X) β) =
      T.standardResidue X α * T.pull (D.zeroSection X) β :=
  T.residue_mul_pull (DivisorPair.standardPair D X) hα β

/-- Exactness forces a divisor to have zero cohomology whenever open pullback is bijective. -/
lemma subsingleton_closed_of_bijective (P : DivisorPair D)
    (hj : Function.Bijective (T.pull P.j)) : Subsingleton (T.obj P.closed) := by
  have hr (x : T.obj P.compl) : T.residue P x = 0 := (T.exact_pull_residue P x).2 (hj.2 x)
  have hg (x : T.obj P.closed) : T.gysin P x = 0 :=
    hj.1 (by simpa only [map_zero] using (T.exact_gysin_pull P).apply_apply_eq_zero x)
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (T.exact_residue_gysin P x).1 (hg x)
  exact hr y

/-- Restriction of all 22 fields along an inclusion of admissible full domains.
The point and products are the same underlying schemes, so the canonical comparison maps are
identities. Blueprint: `lem:geo-restriction`. -/
@[implicit_reducible]
def restrict {D₁ : SmoothDomain k} (h : D₁ ≤ D) : OrdinaryTheory D₁ ℬ where
  bijective_algebraMap_gradeZero := T.bijective_algebraMap_gradeZero
  C := (ObjectProperty.ιOfLE h).op ⋙ T.C
  algebra X := T.algebra ((ObjectProperty.ιOfLE h).obj X)
  isScalarTower X := T.isScalarTower ((ObjectProperty.ιOfLE h).obj X)
  grading X := T.grading ((ObjectProperty.ιOfLE h).obj X)
  gradedAlgebra X := T.gradedAlgebra ((ObjectProperty.ιOfLE h).obj X)
  algebraMap_mem_grading X := T.algebraMap_mem_grading ((ObjectProperty.ιOfLE h).obj X)
  isHomogeneousOfShift_map f := T.isHomogeneousOfShift_map ((ObjectProperty.ιOfLE h).map f)
  isGradedCommutative X := T.isGradedCommutative ((ObjectProperty.ιOfLE h).obj X)
  bijective_algebraMap_point := T.bijective_algebraMap_point
  eq_zero_of_mem_grading_point := T.eq_zero_of_mem_grading_point
  bijective_pullback_affineLine X :=
    T.bijective_pullback_affineLine ((ObjectProperty.ιOfLE h).obj X)
  gysin P := T.gysin (DivisorPair.ofLE h P)
  residue P := T.residue (DivisorPair.ofLE h P)
  isHomogeneousOfShift_gysin P := T.isHomogeneousOfShift_gysin (DivisorPair.ofLE h P)
  isHomogeneousOfShift_residue P := T.isHomogeneousOfShift_residue (DivisorPair.ofLE h P)
  exact_gysin_map P := T.exact_gysin_map (DivisorPair.ofLE h P)
  exact_map_residue P := T.exact_map_residue (DivisorPair.ofLE h P)
  exact_residue_gysin P := T.exact_residue_gysin (DivisorPair.ofLE h P)
  gysin_map f := T.gysin_map ((DivisorPair.functorOfLE h).map f)
  residue_map f := T.residue_map ((DivisorPair.functorOfLE h).map f)
  residue_mul_map P := T.residue_mul_map (DivisorPair.ofLE h P)

@[simp] lemma restrict_grading {D₁ : SmoothDomain k} (h : D₁ ≤ D) (X : D₁.Obj)
    (i : ℤ × ℤ) :
    (T.restrict h).grading X i = T.grading ((ObjectProperty.ιOfLE h).obj X) i := rfl

@[simp] lemma restrict_pull {D₁ : SmoothDomain k} (h : D₁ ≤ D) {X Y : D₁.Obj}
    (f : X ⟶ Y) (x : (T.restrict h).obj Y) :
    (T.restrict h).pull f x = T.pull ((ObjectProperty.ιOfLE h).map f) x := rfl

@[simp] lemma restrict_gysin {D₁ : SmoothDomain k} (h : D₁ ≤ D) (P : DivisorPair D₁)
    (x : (T.restrict h).obj P.closed) :
    (T.restrict h).gysin P x = T.gysin (DivisorPair.ofLE h P) x := rfl

@[simp] lemma restrict_residue {D₁ : SmoothDomain k} (h : D₁ ≤ D) (P : DivisorPair D₁)
    (x : (T.restrict h).obj P.compl) :
    (T.restrict h).residue P x = T.residue (DivisorPair.ofLE h P) x := rfl

end OrdinaryTheory
end OrlikSolomon.Geometric
