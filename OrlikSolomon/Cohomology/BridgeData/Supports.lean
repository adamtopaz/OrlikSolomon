/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.BridgeData.Basic
public import OrlikSolomon.Cohomology.BridgeData.CategorySupports

/-!
# Localization with supports and oriented divisor purity

`SupportsAndPurity` is the standard degreewise input for the localization part of
`lem:standard-bridge`. It includes groups with supports, support-forgetting maps, the connecting
maps of localization, and oriented purity equivalences. Its exactness fields concern the
degreewise sequence with supports; neither total exactness nor Gysin or residue maps are input.

## Hand check of supports, purity and signs

Continue the Betti interpretation recorded in `BridgeData/Basic`, with `B = R[t,t⁻¹]` and
`H^{p,w}(X) = H^p(X(ℂ); R) t^w`. This is a hand check of every input field, not a formal
construction of singular cohomology in Lean:

* `support`, `addCommGroup` and `module` are relative cohomology `H^p(X(ℂ), U(ℂ); R) t^w`.
  `forget` is the relative-to-absolute map, and `boundary` is the connecting homomorphism,
  raising cohomological degree by one and preserving `w`.
* `purity` is the Thom isomorphism for the complex normal line, multiplied by `t`. Its shift
  is `(2,1)`. The three `exact_*` fields are consecutive positions of the localization long
  exact sequence, with no injectivity or surjectivity assertion at its ends.
* `supportMap` is pullback of pairs. `forget_natural` and `boundary_natural` are naturality of
  relative cohomology. `purity_natural` is naturality of the oriented Thom class under the
  certified transverse maps: the induced normal-line map is complex linear and invertible.
* `supportMul` is the relative cup product with an ambient class on the right. `forget_mul`
  expresses its compatibility with forgetting supports. `purity_mul` has no sign because
  the Thom class has even cohomological degree two.
* `boundary_mul` has no sign with the ambient factor on the right: if `b` is its closed
  cochain representative, the cochain formula is `d(ã ∪ b) = dã ∪ b`.

The Thom isomorphism and these products hold for any commutative `R`, including characteristic
two and the zero ring. A geometric étale interpretation instead uses oriented divisor purity
with the same twist shift, with `ℓ` invertible and the geometric point convention described in
`BridgeData/Basic`. Passing finite-coefficient localization to an integral `ℓ`-adic theory and
implementing coherent twist products remain obligations of such a model. No singular or étale
model is constructed here, and no such passage is an assumption of this bridge theorem.

Mixed products of a supported class and an ambient class encode the usual boundary projection
formula and the compatibility of oriented purity with products. These give coefficient linearity
of the Gysin and residue maps constructed from the data.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg

universe u v w z t

namespace OrlikSolomon

/-- The covariant diagram of certified algebraic divisor pairs. -/
def algebraicPairDiagram {k : Type u} [CommRing k] :
    CovariantPairDiagram (SmoothAlg k) (DivisorPair k) where
  ambient := { obj := DivisorPair.ambient, map f := f.ambient }
  closed := { obj := DivisorPair.closed, map f := f.closed }
  compl := { obj := DivisorPair.compl, map f := f.compl }
  i := { app := DivisorPair.i, naturality _ _ f := f.i_comp.symm }
  j := { app := DivisorPair.j, naturality _ _ f := f.j_comp.symm }

/-- Degreewise localization with supports and oriented purity for all the certified divisor pairs.
The supported group is `H_D^{p,w}(X)`, the connecting map raises `p` by one, and purity raises the
bidegree by `(2,1)`. Products and their compatibilities use sigma equalities whenever the written
degrees differ by associativity or commutativity. Blueprint: `lem:standard-bridge`.

The projection identities are supplied for arbitrary homogeneous factors. This is the standard
full homogeneous projection formula allowed by the blueprint. Only the specialization with the
first factor in degree `(1,1)` is retained in `OrdinaryTheory`. -/
structure SupportsAndPurity {k : Type u} [CommRing k] {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (D : DegreewiseTheory.{u, v, w, z} k ℬ) where
  /-- Cohomology of the ambient object with supports in its divisor. -/
  support (P : DivisorPair k) : ℤ × ℤ → Type t
  /-- Supported cohomology groups are additive abelian groups. -/
  [addCommGroup : ∀ P i, AddCommGroup (support P i)]
  /-- Supported cohomology groups are `R`-modules. -/
  [module : ∀ P i, Module R (support P i)]
  /-- The support-forgetting map `H_D^{p,w}(X) → H^{p,w}(X)`. -/
  forget (P : DivisorPair k) (i : ℤ × ℤ) : support P i →ₗ[R] D.H P.ambient i
  /-- The connecting homomorphism `H^{p,w}(U) → H_D^{p+1,w}(X)`. -/
  boundary (P : DivisorPair k) (i : ℤ × ℤ) :
    D.H P.compl i →ₗ[R] support P (i + (1, 0))
  /-- Oriented divisor purity `H^{p,w}(D) ≃ H_D^{p+2,w+1}(X)`. -/
  purity (P : DivisorPair k) (i : ℤ × ℤ) :
    D.H P.closed i ≃ₗ[R] support P (i + (2, 1))
  /-- Exactness at ambient cohomology in the localization sequence with supports. -/
  exact_forget_map (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (forget P i) (D.map P.j i)
  /-- Exactness at open cohomology in the localization sequence with supports. -/
  exact_map_boundary (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (D.map P.j i) (boundary P i)
  /-- Exactness at supported cohomology in the localization sequence. -/
  exact_boundary_forget (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (boundary P i) (forget P (i + (1, 0)))
  /-- Transverse pullback in supported cohomology. -/
  supportMap {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) :
    support P i →ₗ[R] support Q i
  /-- Support-forgetting commutes with transverse pullback. -/
  forget_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : support P i) :
    forget Q i (supportMap f i x) = D.map f.ambient i (forget P i x)
  /-- The localization connecting homomorphism commutes with transverse pullback. -/
  boundary_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : D.H P.compl i) :
    boundary Q i (D.map f.compl i x) = supportMap f (i + (1, 0)) (boundary P i x)
  /-- Oriented purity commutes with transverse pullback. -/
  purity_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : D.H P.closed i) :
    purity Q i (D.map f.closed i x) = supportMap f (i + (2, 1)) (purity P i x)
  /-- The mixed cup product of a supported class with an ambient class. -/
  supportMul (P : DivisorPair k) (i j : ℤ × ℤ) :
    support P i →ₗ[R] D.H P.ambient j →ₗ[R] support P (i + j)
  /-- Forgetting supports preserves mixed products. -/
  forget_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : support P i) (y : D.H P.ambient j) :
    forget P (i + j) (supportMul P i j x y) = GradedMonoid.GMul.mul (forget P i x) y
  /-- Oriented purity respects products with classes from the ambient object. -/
  purity_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : D.H P.closed i) (y : D.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (2, 1))
        (purity P (i + j) (GradedMonoid.GMul.mul x (D.map P.i j y))) =
      GradedMonoid.mk ((i + (2, 1)) + j) (supportMul P (i + (2, 1)) j (purity P i x) y)
  /-- The boundary projection formula, with the open class first and no sign. -/
  boundary_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : D.H P.compl i) (y : D.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (1, 0))
        (boundary P (i + j) (GradedMonoid.GMul.mul x (D.map P.j j y))) =
      GradedMonoid.mk ((i + (1, 0)) + j)
        (supportMul P (i + (1, 0)) j (boundary P i x) y)

namespace SupportsAndPurity

attribute [instance] addCommGroup module

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {D : DegreewiseTheory.{u, v, w, z} k ℬ} (S : SupportsAndPurity.{u, v, w, z, t} D)

/-- The category-independent supports and purity underlying the algebraic bridge. -/
def toCore :
    CategoricalSupportsAndPurity D.toCore algebraicPairDiagram where
  support := S.support
  addCommGroup := S.addCommGroup
  module := S.module
  forget := S.forget
  boundary := S.boundary
  purity := S.purity
  exact_forget_map := S.exact_forget_map
  exact_map_boundary := S.exact_map_boundary
  exact_boundary_forget := S.exact_boundary_forget
  supportMap := S.supportMap
  forget_natural := S.forget_natural
  boundary_natural := S.boundary_natural
  purity_natural := S.purity_natural
  supportMul := S.supportMul
  forget_mul := S.forget_mul
  purity_mul := S.purity_mul
  boundary_mul := S.boundary_mul

/-- Total cohomology with supports, summed over cohomological degree and twist. -/
abbrev Total (P : DivisorPair k) := ⨁ i, S.support P i

/-- The inclusion of one supported cohomology group in its total direct sum. -/
abbrev incl (P : DivisorPair k) (i : ℤ × ℤ) : S.support P i →ₗ[R] S.Total P :=
  DirectSum.lof R _ (S.support P) i

/-- Support-forgetting on the external direct sums. -/
def forgetTotal (P : DivisorPair k) : S.Total P →ₗ[R] D.Total P.ambient :=
  S.toCore.forgetTotal P

@[simp]
lemma forgetTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : S.support P i) :
    S.forgetTotal P (S.incl P i x) = D.incl P.ambient i (S.forget P i x) :=
  S.toCore.forgetTotal_incl P i x

/-- Transverse pullback on total cohomology with supports. -/
def supportMapTotal {P Q : DivisorPair k} (f : P ⟶ Q) : S.Total P →ₗ[R] S.Total Q :=
  S.toCore.supportMapTotal f

@[simp]
lemma supportMapTotal_incl {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ)
    (x : S.support P i) :
    S.supportMapTotal f (S.incl P i x) = S.incl Q i (S.supportMap f i x) :=
  S.toCore.supportMapTotal_incl f i x

/-- Mixed cup product on total supported and ambient cohomology. -/
def supportMulTotal (P : DivisorPair k) :
    S.Total P →ₗ[R] D.Total P.ambient →ₗ[R] S.Total P :=
  DirectSum.toModule R _ _ fun i ↦
    (DirectSum.toModule R _ _ fun j ↦
      ((S.supportMul P i j).compr₂ (S.incl P (i + j))).flip).flip

@[simp]
lemma supportMulTotal_incl (P : DivisorPair k) {i j : ℤ × ℤ}
    (x : S.support P i) (y : D.H P.ambient j) :
    S.supportMulTotal P (S.incl P i x) (D.incl P.ambient j y) =
      S.incl P (i + j) (S.supportMul P i j x y) :=
  S.toCore.supportMulTotal_incl P x y

/-- The support-forgetting projection formula holds on total cohomology by bilinearity. -/
lemma forgetTotal_mul (P : DivisorPair k) (x : S.Total P) (y : D.Total P.ambient) :
    S.forgetTotal P (S.supportMulTotal P x y) = S.forgetTotal P x * y :=
  S.toCore.forgetTotal_mul P x y

/-- Support-forgetting commutes with total transverse pullback. -/
lemma forgetTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : S.Total P) :
    S.forgetTotal Q (S.supportMapTotal f x) = D.mapTotal f.ambient (S.forgetTotal P x) :=
  S.toCore.forgetTotal_natural f x

/-- The localization connecting homomorphism on total cohomology, of shift `(1,0)`. -/
def boundaryTotal (P : DivisorPair k) : D.Total P.compl →ₗ[R] S.Total P :=
  S.toCore.boundaryTotal P

@[simp]
lemma boundaryTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.compl i) :
    S.boundaryTotal P (D.incl P.compl i x) =
      S.incl P (i + (1, 0)) (S.boundary P i x) :=
  S.toCore.boundaryTotal_incl P i x

/-- The boundary map commutes with transverse pullback on total cohomology. -/
lemma boundaryTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.compl) :
    S.boundaryTotal Q (D.mapTotal f.compl x) =
      S.supportMapTotal f (S.boundaryTotal P x) :=
  S.toCore.boundaryTotal_natural f x

/-- The boundary projection formula on the direct sums, obtained by summing homogeneous formulas. -/
lemma boundaryTotal_mul (P : DivisorPair k) (x : D.Total P.compl) (y : D.Total P.ambient) :
    S.boundaryTotal P (x * D.mapTotal P.j y) =
      S.supportMulTotal P (S.boundaryTotal P x) y :=
  S.toCore.boundaryTotal_mul P x y

/-- Support-forgetting preserves bidegrees. -/
lemma isHomogeneousOfShift_forgetTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (directSumGrading (R := R) (S.support P)) (D.grading P.ambient) 0
      (S.forgetTotal P) :=
  S.toCore.isHomogeneousOfShift_forgetTotal P

/-- The connecting homomorphism raises cohomological degree by one and preserves the twist. -/
lemma isHomogeneousOfShift_boundaryTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.compl) (directSumGrading (R := R) (S.support P)) (1, 0)
      (S.boundaryTotal P) :=
  S.toCore.isHomogeneousOfShift_boundaryTotal P

/-- Exactness at total ambient cohomology, derived from degreewise localization with supports. -/
lemma exact_forgetTotal_map (P : DivisorPair k) :
    Function.Exact (S.forgetTotal P) (D.mapTotal P.j) :=
  S.toCore.exact_forgetTotal_map P

/-- Exactness at total open cohomology, derived from localization in each degree. -/
lemma exact_map_boundaryTotal (P : DivisorPair k) :
    Function.Exact (D.mapTotal P.j) (S.boundaryTotal P) :=
  S.toCore.exact_map_boundaryTotal P

/-- Exactness at total supported cohomology, derived from the degreewise localization sequence. -/
lemma exact_boundaryTotal_forgetTotal (P : DivisorPair k) :
    Function.Exact (S.boundaryTotal P) (S.forgetTotal P) :=
  S.toCore.exact_boundaryTotal_forgetTotal P

/-- Oriented purity on the total direct sums. It is a reindexed sum of the degreewise purity
equivalences, rather than an additional assumption. -/
def purityTotal (P : DivisorPair k) : D.Total P.closed ≃ₗ[R] S.Total P :=
  S.toCore.purityTotal P

@[simp]
lemma purityTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.closed i) :
    S.purityTotal P (D.incl P.closed i x) =
      S.incl P (i + (2, 1)) (S.purity P i x) :=
  S.toCore.purityTotal_incl P i x

/-- Oriented purity on total cohomology has bidegree `(2,1)`. -/
lemma isHomogeneousOfShift_purityTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.closed) (directSumGrading (R := R) (S.support P)) (2, 1)
      (S.purityTotal P) :=
  S.toCore.isHomogeneousOfShift_purityTotal P

/-- Oriented purity commutes with transverse pullback on total cohomology. -/
lemma purityTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.closed) :
    S.purityTotal Q (D.mapTotal f.closed x) = S.supportMapTotal f (S.purityTotal P x) :=
  S.toCore.purityTotal_natural f x

/-- Purity respects the product with an ambient class, on total cohomology. -/
lemma purityTotal_mul (P : DivisorPair k) (x : D.Total P.closed) (y : D.Total P.ambient) :
    S.purityTotal P (x * D.mapTotal P.i y) =
      S.supportMulTotal P (S.purityTotal P x) y :=
  S.toCore.purityTotal_mul P x y

/-- The Gysin map, constructed as oriented purity followed by forgetting supports. -/
def gysinR (P : DivisorPair k) : D.Total P.closed →ₗ[R] D.Total P.ambient :=
  (S.forgetTotal P).comp (S.purityTotal P).toLinearMap

/-- The residue map, constructed as the localization boundary followed by inverse purity. -/
def residueR (P : DivisorPair k) : D.Total P.compl →ₗ[R] D.Total P.closed :=
  (S.purityTotal P).symm.toLinearMap.comp (S.boundaryTotal P)

/-- The Gysin map has bidegree `(2,1)`. -/
lemma isHomogeneousOfShift_gysinR (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.closed) (D.grading P.ambient) (2, 1) (S.gysinR P) :=
  S.toCore.isHomogeneousOfShift_gysinR P

/-- The residue map has bidegree `(-1,-1)`. -/
lemma isHomogeneousOfShift_residueR (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.compl) (D.grading P.closed) (-1, -1) (S.residueR P) :=
  S.toCore.isHomogeneousOfShift_residueR P

/-- The Gysin projection formula follows from the product identities for purity and supports. -/
lemma gysinR_mul_map (P : DivisorPair k) (x : D.Total P.closed) (y : D.Total P.ambient) :
    S.gysinR P (x * D.mapTotal P.i y) = S.gysinR P x * y :=
  S.toCore.gysinR_mul_map P x y

/-- The residue projection formula follows from the boundary formula and oriented purity. -/
lemma residueR_mul_map (P : DivisorPair k) (x : D.Total P.compl) (y : D.Total P.ambient) :
    S.residueR P (x * D.mapTotal P.j y) = S.residueR P x * D.mapTotal P.i y :=
  S.toCore.residueR_mul_map P x y

/-- Gysin naturality follows from the support-forgetting and purity squares. -/
lemma gysinR_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.closed) :
    S.gysinR Q (D.mapTotal f.closed x) = D.mapTotal f.ambient (S.gysinR P x) :=
  S.toCore.gysinR_natural f x

/-- Residue naturality follows from the localization boundary and purity squares. -/
lemma residueR_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.compl) :
    S.residueR Q (D.mapTotal f.compl x) = D.mapTotal f.closed (S.residueR P x) :=
  S.toCore.residueR_natural f x

/-- Exactness at ambient cohomology after using purity to replace support groups. -/
lemma exact_gysinR_map (P : DivisorPair k) :
    Function.Exact (S.gysinR P) (D.mapTotal P.j) :=
  S.toCore.exact_gysinR_map P

/-- Exactness at open cohomology after using inverse purity in the residue map. -/
lemma exact_map_residueR (P : DivisorPair k) :
    Function.Exact (D.mapTotal P.j) (S.residueR P) :=
  S.toCore.exact_map_residueR P

/-- Exactness at divisor cohomology after identifying it with shifted supported cohomology. -/
lemma exact_residueR_gysinR (P : DivisorPair k) :
    Function.Exact (S.residueR P) (S.gysinR P) :=
  S.toCore.exact_residueR_gysinR P

/-- The Gysin map is linear over the whole coefficient ring, including nonzero weights. This
follows from the homogeneous mixed-product identities, not from an extra linearity assumption. -/
lemma gysinR_smul (P : DivisorPair k) (b : B) (x : D.Total P.closed) :
    S.gysinR P (b • x) = b • S.gysinR P x :=
  S.toCore.gysinR_smul P b x

/-- The residue map is linear over the whole coefficient ring, by the boundary and purity
projection formulas. -/
lemma residueR_smul (P : DivisorPair k) (b : B) (x : D.Total P.compl) :
    S.residueR P (b • x) = b • S.residueR P x :=
  S.toCore.residueR_smul P b x

/-- The Gysin map, bundled as a `B`-linear map. -/
def gysin (P : DivisorPair k) : D.Total P.closed →ₗ[B] D.Total P.ambient:=
  S.toCore.gysin P

/-- The residue map, bundled as a `B`-linear map. -/
def residue (P : DivisorPair k) : D.Total P.compl →ₗ[B] D.Total P.closed:=
  S.toCore.residue P


-- Retain the equations exported by the original implementation, even though the proof wrappers
-- no longer cause the equation compiler to generate them as a side effect of simplification.
attribute [backward_defeq] supportMulTotal.eq_1 gysinR.eq_1 residueR.eq_1

end SupportsAndPurity

end OrlikSolomon
