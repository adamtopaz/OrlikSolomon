/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Bridge
public import OrlikSolomon.Examples.Sanity

/-!
# Zero inputs for the standard localization bridge

The zero coefficient ring gives degreewise cohomology and supported cohomology consisting of
zero groups. These inputs check that the standard bridge permits the zero coefficient ring,
all integer degrees and weights, and every certified divisor pair. They are consistency checks
of the interface rather than checks of the substantive cohomology axioms.

The same-ring component tests first construct the component maps with separate abstract rings
`R` and `B`, then specialize to `R = B = PUnit`. This fixes the recorded scalar structures
before identifying the rings, as required for explicit `OverR` component consumers.

The last section checks, for abstract inputs, that plain `simp` closes the component formulas
of pullback and Gysin, for both the algebraic and the geometric bridge. Each formula equates
elements of the carrier of the constructed theory, while its right side is an element of the
direct sum; `simp` can close such a goal only because the constructions are
`@[implicit_reducible]` (issue #132).

Blueprint: `lem:standard-bridge`, `thm:geo-bridge` and the zero-coefficient-ring regression.
-/

@[expose] public section

noncomputable section

universe u v w z t

namespace OrlikSolomon.Sanity

/-- Zero degreewise cohomology, with zero coefficients, on every smooth algebra. -/
def zeroDegreewiseTheory (k : Type u) [CommRing k] :
    DegreewiseTheory.{u, v, w, z} k zeroWeight.{v, w} where
  H _ _ := PUnit.{z + 1}
  coeff _ _ := 0
  coeff_one _ := Subsingleton.elim _ _
  coeff_mul _ _ _ _ _ := Subsingleton.elim _ _
  bijective_algebraMap_gradeZero :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  graded_comm _ _ _ _ _ := Sigma.ext (add_comm _ _) (heq_of_eq (Subsingleton.elim _ _))
  map _ _ := 0
  map_id _ _ _ := Subsingleton.elim _ _
  map_comp _ _ _ _ := Subsingleton.elim _ _
  map_one _ := Subsingleton.elim _ _
  map_mul _ _ _ _ _ := Subsingleton.elim _ _
  map_coeff _ _ _ := Subsingleton.elim _ _
  bijective_coeff_point _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  eq_zero_point _ _ := Subsingleton.elim _ _
  bijective_map_polynomialC _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

instance {k : Type u} [CommRing k] (A : SmoothAlg k) (i : ℤ × ℤ) :
    Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} k).H A i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- Zero supported cohomology, with its localization sequence and oriented purity. Every map
has its prescribed source and target degree, including negative cohomological degrees. -/
def zeroSupportsAndPurity (k : Type u) [CommRing k] :
    SupportsAndPurity.{u, v, w, z, t} (zeroDegreewiseTheory.{u, v, w, z} k) where
  support _ _ := PUnit.{t + 1}
  forget _ _ := 0
  boundary _ _ := 0
  purity _ _ :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _
      map_add' _ _ := Subsingleton.elim _ _
      map_smul' _ _ := Subsingleton.elim _ _ }
  exact_forget_map _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_map_boundary _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_boundary_forget _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  supportMap _ _ := 0
  forget_natural _ _ _ := Subsingleton.elim _ _
  boundary_natural _ _ _ := Subsingleton.elim _ _
  purity_natural _ _ _ := Subsingleton.elim _ _
  supportMul _ _ _ := 0
  forget_mul _ _ _ _ _ := Subsingleton.elim _ _
  purity_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))
  boundary_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))

instance {k : Type u} [CommRing k] (P : DivisorPair k) (i : ℤ × ℤ) :
    Subsingleton ((zeroSupportsAndPurity.{u, v, w, z, t} k).support P i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The ordinary theory produced by the standard bridge from the zero degreewise inputs.
Blueprint: `lem:standard-bridge`. -/
def zeroBridgeTheory (k : Type u) [CommRing k] :
    OrdinaryTheory.{u, v, w, z} k zeroWeight.{v, w} :=
  ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} k)
    (zeroSupportsAndPurity.{u, v, w, z, t} k)

/-- Summing the zero degreewise inputs gives zero total cohomology on every object. -/
instance {k : Type u} [CommRing k] (A : SmoothAlg k) :
    Subsingleton ((zeroBridgeTheory.{u, v, w, z, t} k).C.obj A) :=
  inferInstanceAs (Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} k).Total A))

/-- The Gysin map obtained from zero supported cohomology is zero on every divisor pair. -/
theorem zeroBridgeTheory_gysin (k : Type u) [CommRing k] (P : DivisorPair k) :
    (zeroBridgeTheory.{u, v, w, z, t} k).gysin P = 0 :=
  LinearMap.ext fun _ ↦ Subsingleton.elim _ _

/-- The residue obtained from zero supported cohomology is zero on every divisor pair. -/
theorem zeroBridgeTheory_residue (k : Type u) [CommRing k] (P : DivisorPair k) :
    (zeroBridgeTheory.{u, v, w, z, t} k).residue P = 0 :=
  LinearMap.ext fun _ ↦ Subsingleton.elim _ _

section FrozenComponents

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]

private def gysinComponent (T : OrdinaryTheory.{u, v, w, z} k ℬ)
    (P : DivisorPair k) (i : ℤ × ℤ) :
    T.grading P.closed i →ₗ[R] T.grading P.ambient (i + (2, 1)) :=
  (T.isHomogeneousOfShift_gysinOverR P).component rfl

private def residueComponent (T : OrdinaryTheory.{u, v, w, z} k ℬ)
    (P : DivisorPair k) (i : ℤ × ℤ) :
    T.grading P.compl i →ₗ[R] T.grading P.closed (i + (-1, -1)) :=
  (T.isHomogeneousOfShift_residueOverR P).component rfl

private def pullbackComponent (D : DegreewiseTheory.{u, v, w, z} k ℬ)
    {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ) :
    D.grading A i →ₗ[R] D.grading E i :=
  (D.isHomogeneousOfShift_mapTotalR f).component (add_zero i)

end FrozenComponents

/-- The concrete zero bridge specializes actual component maps constructed before identifying
its coefficient rings. -/
private theorem sameRingPinned (k : Type u) [CommRing k] (P : DivisorPair k) (i : ℤ × ℤ) :
    let T := zeroBridgeTheory.{u, v, v, v, v} k
    ∀ (x : T.grading P.closed i) (y : T.grading P.compl i),
      (gysinComponent T P i x : T.C.obj P.ambient) = T.gysin P x ∧
        (residueComponent T P i y : T.C.obj P.closed) = T.residue P y := by
  intro T x y
  exact ⟨rfl, rfl⟩

/-- The concrete zero degreewise theory specializes the actual R-linear component construction. -/
private theorem sameRingPullback (k : Type u) [CommRing k] {A E : SmoothAlg k}
    (f : A ⟶ E) (i : ℤ × ℤ) :
    let D := zeroDegreewiseTheory.{u, v, v, v} k
    ∀ x : D.grading A i,
      (pullbackComponent D f i x : D.Total E) = D.mapTotalR f x := by
  intro D x
  rfl

/-! ### `simp` on the component formulas

Without `@[implicit_reducible]` on the bridge constructions, `simp` rewrote each left side below
and then left a goal whose two sides were identical: the carrier of the constructed theory was
not the direct sum at implicit transparency, so `eq_self` did not apply. -/

section SimpNormalForm

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]

section Algebraic

variable (D : DegreewiseTheory.{u, v, w, z} k ℬ) (S : SupportsAndPurity.{u, v, w, z, t} D)

example {A A' : SmoothAlg k} (f : A ⟶ A') (i : ℤ × ℤ) (x : D.H A i) :
    (ofSupportsAndPurity D S).C.map f (D.incl A i x) = D.incl A' i (D.map f i x) := by
  simp only [ofSupportsAndPurity_map_incl]

example {A A' : SmoothAlg k} (f : A ⟶ A') (i : ℤ × ℤ) (x : D.H A i) :
    (ofSupportsAndPurity D S).C.map f (D.incl A i x) = D.incl A' i (D.map f i x) := by
  simp

example (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.closed i) :
    (ofSupportsAndPurity D S).gysin P (D.incl P.closed i x) =
      D.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) := by
  simp only [ofSupportsAndPurity_gysin_incl]

example (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.closed i) :
    (ofSupportsAndPurity D S).gysin P (D.incl P.closed i x) =
      D.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) := by
  simp

/- `map_add` applies to sums of summands. -/
example {A A' : SmoothAlg k} (f : A ⟶ A') (i j : ℤ × ℤ) (x : D.H A i) (y : D.H A j) :
    (ofSupportsAndPurity D S).C.map f (D.incl A i x + D.incl A j y) =
      D.incl A' i (D.map f i x) + D.incl A' j (D.map f j y) := by
  simp

/- Gysin after pullback. -/
example {P Q : DivisorPair k} (g : P ⟶ Q) (i : ℤ × ℤ) (x : D.H P.closed i) :
    (ofSupportsAndPurity D S).gysin Q
        ((ofSupportsAndPurity D S).C.map g.closed (D.incl P.closed i x)) =
      D.incl Q.ambient (i + (2, 1))
        (S.forget Q (i + (2, 1)) (S.purity Q i (D.map g.closed i x))) := by
  simp

end Algebraic

section Geometric

variable {D : Geometric.SmoothDomain k} (E : Geometric.DegreewiseTheory.{u, v, w, z} D ℬ)
  (S : Geometric.SupportsAndPurity.{u, v, w, z, t} E)

example {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) (x : E.H Y i) :
    (Geometric.ofSupportsAndPurity E S).pull f (E.incl Y i x) = E.incl X i (E.pull f i x) := by
  simp only [Geometric.ofSupportsAndPurity_pull_incl]

example {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) (x : E.H Y i) :
    (Geometric.ofSupportsAndPurity E S).pull f (E.incl Y i x) = E.incl X i (E.pull f i x) := by
  simp

example (P : Geometric.DivisorPair D) (i : ℤ × ℤ) (x : E.H P.closed i) :
    (Geometric.ofSupportsAndPurity E S).gysin P (E.incl P.closed i x) =
      E.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) := by
  simp only [Geometric.ofSupportsAndPurity_gysin_incl]

example (P : Geometric.DivisorPair D) (i : ℤ × ℤ) (x : E.H P.closed i) :
    (Geometric.ofSupportsAndPurity E S).gysin P (E.incl P.closed i x) =
      E.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) := by
  simp

/- `map_add` applies to sums of summands. -/
example {X Y : D.Obj} (f : X ⟶ Y) (i j : ℤ × ℤ) (x : E.H Y i) (y : E.H Y j) :
    (Geometric.ofSupportsAndPurity E S).pull f (E.incl Y i x + E.incl Y j y) =
      E.incl X i (E.pull f i x) + E.incl X j (E.pull f j y) := by
  simp

/- Gysin after pullback, which is contravariant. -/
example {P Q : Geometric.DivisorPair D} (g : P ⟶ Q) (i : ℤ × ℤ) (x : E.H Q.closed i) :
    (Geometric.ofSupportsAndPurity E S).gysin P
        ((Geometric.ofSupportsAndPurity E S).pull g.closed (E.incl Q.closed i x)) =
      E.incl P.ambient (i + (2, 1))
        (S.forget P (i + (2, 1)) (S.purity P i (E.pull g.closed i x))) := by
  simp

end Geometric

end SimpNormalForm

end OrlikSolomon.Sanity
