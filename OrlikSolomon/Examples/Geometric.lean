/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Transport

/-!
# Regressions for geometric cohomology

These consumers check that the public geometric cohomology notation works with ordinary ring
rewriting. In particular, a normalized residue and the projection formula give restriction to the
divisor using either `rw` or `simp`, and products involving Gysin and residue values use the same
ring operations as `OrdinaryTheory.obj`.

The remaining examples check the pullback notation and the algebraic standard-residue
simplification after transport. They apply to every admissible domain and geometric ordinary
theory, without nonzero-coefficient assumptions.

Blueprint: acceptance consumers for `def:geo-theory` and `thm:geo-to-algebraic`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

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

end OrlikSolomon.Geometric.Examples
