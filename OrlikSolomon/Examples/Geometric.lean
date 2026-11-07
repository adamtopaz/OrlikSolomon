/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Bridge
public import OrlikSolomon.Examples.Bridge

/-!
# Regressions for geometric cohomology

These consumers check that the public geometric cohomology notation works with ordinary ring
rewriting. In particular, a normalized residue and the projection formula give restriction to the
divisor using either `rw` or `simp`, and products involving Gysin and residue values use the same
ring operations as `OrdinaryTheory.obj`.

The remaining examples check the pullback notation and the algebraic standard-residue
simplification after transport. They apply to every admissible domain and geometric ordinary
theory, without nonzero-coefficient assumptions.

A zero-coefficient supports-and-purity model also exercises the geometric bridge and its
component maps. This checks that the degreewise inputs can be instantiated without strengthening
the coefficient hypotheses.

Blueprint: acceptance consumers for `def:geo-theory`, `thm:geo-to-algebraic` and `thm:geo-bridge`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v w z t

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The normalized residue projection formula supports subsequent ring rewrites. -/
example (P : DivisorPair D) {α : T.obj P.compl}
    (hα : α ∈ T.grading P.compl (1, 1)) (h1 : T.residue P α = 1)
    (β : T.obj P.ambient) : T.residue P (α * T.pull P.j β) = T.pull P.i β := by
  rw [T.residue_mul_pull P hα β, h1, one_mul]

/-- The normalized residue projection formula also simplifies with ordinary ring lemmas. -/
example (P : DivisorPair D) {α : T.obj P.compl}
    (hα : α ∈ T.grading P.compl (1, 1)) (h1 : T.residue P α = 1)
    (β : T.obj P.ambient) : T.residue P (α * T.pull P.j β) = T.pull P.i β := by
  simp [T.residue_mul_pull P hα β, h1]

/-- Gysin values and classes in the public ambient algebra use the same multiplication. -/
example (P : DivisorPair D) (x : T.obj P.closed) (y : T.obj P.ambient) :
    T.gysin P x * (1 * y) = T.gysin P x * y := by
  rw [one_mul]

/-- Residue values and restricted classes use the same multiplication on the divisor. -/
example (P : DivisorPair D) (α : T.obj P.compl) (β : T.obj P.ambient) :
    (T.residue P α : T.obj P.closed) * (1 * T.pull P.i β) =
      T.residue P α * T.pull P.i β := by
  rw [one_mul]

/-- Functor evaluation simplifies to the public pullback notation. -/
example {X Y : D.Obj} (f : X ⟶ Y) (x : T.obj Y) : T.C.map f.op x = T.pull f x := by
  simp

/-- Affine transport preserves the algebraic standard-residue simplification. -/
example (A : SmoothAlg k) (x : T.toAlgebraic.C.obj (SmoothAlg.polynomial A)) :
    T.toAlgebraic.stdResidue A
      (T.toAlgebraic.C.map (SmoothAlg.polynomialToLaurent A) x) = 0 := by
  simp

/-! ### A zero-coefficient supports-and-purity model -/

open OrlikSolomon.Sanity
/-- A geometric degreewise input with zero coefficients and zero groups in every degree. -/
def zeroDegreewiseTheory {k : Type u} [CommRing k] (D : SmoothDomain k) :
    DegreewiseTheory.{u, v, w, z} D zeroWeight.{v, w} where
  H _ _ := PUnit.{z + 1}
  coeff _ _ := 0
  coeff_one _ := Subsingleton.elim _ _
  coeff_mul _ _ _ _ _ := Subsingleton.elim _ _
  bijective_algebraMap_gradeZero :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  graded_comm _ _ _ _ _ := Sigma.ext (add_comm _ _) (heq_of_eq (Subsingleton.elim _ _))
  pull _ _ := 0
  pull_id _ _ _ := Subsingleton.elim _ _
  pull_comp _ _ _ _ := Subsingleton.elim _ _
  pull_one _ := Subsingleton.elim _ _
  pull_mul _ _ _ _ _ := Subsingleton.elim _ _
  pull_coeff _ _ _ := Subsingleton.elim _ _
  bijective_coeff_point _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  eq_zero_point _ _ := Subsingleton.elim _ _
  bijective_pullback_affineLine _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

instance {k : Type u} [CommRing k] (D : SmoothDomain k) (X : D.Obj) (i : ℤ × ℤ) :
    Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} D).H X i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- Zero supported cohomology, with localization and oriented purity on every geometric pair. -/
def zeroSupportsAndPurity {k : Type u} [CommRing k] (D : SmoothDomain k) :
    SupportsAndPurity.{u, v, w, z, t} (zeroDegreewiseTheory.{u, v, w, z} D) where
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
  exact_forget_pull _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_pull_boundary _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_boundary_forget _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  supportPull _ _ := 0
  forget_natural _ _ _ := Subsingleton.elim _ _
  boundary_natural _ _ _ := Subsingleton.elim _ _
  purity_natural _ _ _ := Subsingleton.elim _ _
  supportMul _ _ _ := 0
  forget_mul _ _ _ _ _ := Subsingleton.elim _ _
  purity_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))
  boundary_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))

private def frozenPullComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) :
    T.grading Y i →ₗ[R] T.grading X i :=
  (T.isHomogeneousOfShift_mapOverR f).component (add_zero i)

private def frozenGysinComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) (P : DivisorPair D) (i : ℤ × ℤ) :
    T.grading P.closed i →ₗ[R] T.grading P.ambient (i + (2, 1)) :=
  (T.isHomogeneousOfShift_gysinOverR P).component rfl

private def frozenResidueComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) (P : DivisorPair D) (i : ℤ × ℤ) :
    T.grading P.compl i →ₗ[R] T.grading P.closed (i + (-1, -1)) :=
  (T.isHomogeneousOfShift_residueOverR P).component rfl

/-- The bridge preserves the component maps of a realizable zero-coefficient input. -/
example {k : Type u} [CommRing k] (D : SmoothDomain k) {X Y : D.Obj} (f : X ⟶ Y)
    (P : DivisorPair D) (i : ℤ × ℤ) :
    let T := ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, v, v} D)
      (zeroSupportsAndPurity.{u, v, v, v, v} D)
    (∀ x : T.grading Y i, (frozenPullComponent T f i x : T.obj X) = T.pull f x) ∧
    (∀ x : T.grading P.closed i,
      (frozenGysinComponent T P i x : T.obj P.ambient) = T.gysin P x) ∧
    (∀ x : T.grading P.compl i,
      (frozenResidueComponent T P i x : T.obj P.closed) = T.residue P x) := by
  intro T
  exact ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

end OrlikSolomon.Geometric.Examples
