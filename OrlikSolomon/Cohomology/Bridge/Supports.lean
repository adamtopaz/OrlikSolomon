/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Bridge.Basic

/-!
# Localization with supports and oriented divisor purity

`SupportsAndPurity` is the standard degreewise input for the localization part of
`lem:standard-bridge`. It includes groups with supports, support-forgetting maps, the connecting
maps of localization, and oriented purity equivalences. Its exactness fields concern the
degreewise sequence with supports; neither total exactness nor Gysin or residue maps are input.

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

/-- Total cohomology with supports, summed over cohomological degree and twist. -/
abbrev Total (P : DivisorPair k) := ⨁ i, S.support P i

/-- The inclusion of one supported cohomology group in its total direct sum. -/
abbrev incl (P : DivisorPair k) (i : ℤ × ℤ) : S.support P i →ₗ[R] S.Total P :=
  DirectSum.lof R _ (S.support P) i

/-- Support-forgetting on the external direct sums. -/
def forgetTotal (P : DivisorPair k) : S.Total P →ₗ[R] D.Total P.ambient :=
  DirectSum.lmap (S.forget P)

@[simp]
lemma forgetTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : S.support P i) :
    S.forgetTotal P (S.incl P i x) = D.incl P.ambient i (S.forget P i x) :=
  DirectSum.lmap_lof _ _ _

/-- Transverse pullback on total cohomology with supports. -/
def supportMapTotal {P Q : DivisorPair k} (f : P ⟶ Q) : S.Total P →ₗ[R] S.Total Q :=
  DirectSum.lmap (S.supportMap f)

@[simp]
lemma supportMapTotal_incl {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ)
    (x : S.support P i) :
    S.supportMapTotal f (S.incl P i x) = S.incl Q i (S.supportMap f i x) :=
  DirectSum.lmap_lof _ _ _

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
      S.incl P (i + j) (S.supportMul P i j x y) := by
  simp only [supportMulTotal, incl, DegreewiseTheory.incl, DirectSum.toModule_lof,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

/-- The support-forgetting projection formula holds on total cohomology by bilinearity. -/
lemma forgetTotal_mul (P : DivisorPair k) (x : S.Total P) (y : D.Total P.ambient) :
    S.forgetTotal P (S.supportMulTotal P x y) = S.forgetTotal P x * y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      change S.forgetTotal P (S.supportMulTotal P (S.incl P i x) (D.incl P.ambient j y)) =
        S.forgetTotal P (S.incl P i x) * D.incl P.ambient j y
      rw [S.supportMulTotal_incl, S.forgetTotal_incl, S.forgetTotal_incl, S.forget_mul]
      exact (DirectSum.of_mul_of _ _).symm
    | add y z hy hz => simp [hy, hz, mul_add]
  | add x y hx hy => simp [hx, hy, add_mul]

/-- Support-forgetting commutes with total transverse pullback. -/
lemma forgetTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : S.Total P) :
    S.forgetTotal Q (S.supportMapTotal f x) = D.mapTotal f.ambient (S.forgetTotal P x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change S.forgetTotal Q (S.supportMapTotal f (S.incl P i x)) =
      D.mapTotal f.ambient (S.forgetTotal P (S.incl P i x))
    rw [S.supportMapTotal_incl, S.forgetTotal_incl, S.forgetTotal_incl,
      D.mapTotal_incl, S.forget_natural]
  | add x y hx hy => simp [hx, hy]

end SupportsAndPurity

end OrlikSolomon
