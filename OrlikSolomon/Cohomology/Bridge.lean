/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.BridgeData.Supports

/-!
# From standard degreewise localization to the ordinary theory

`ofSupportsAndPurity` constructs `OrdinaryTheory` from degreewise cohomology with products,
twists, localization with supports, and oriented divisor purity. Blueprint: `lem:standard-bridge`.

The groups in `DegreewiseTheory` are summed over **all** bidegrees. Support-forgetting and the
connecting map are summed componentwise, and purity is summed with the reindexing `(p,w) ↦
(p+2,w+1)`. Gysin is purity followed by forgetting supports, and residue is the connecting map
followed by inverse purity. Finite support and degreewise exactness prove total exactness; none
of the three total exactness statements is an input. The degreewise mixed-product identities
also prove linearity over the whole coefficient ring `B`.

This is a bridge for someone supplying a standard cohomology theory. It does not construct
singular, de Rham, or étale cohomology in Lean, and does not claim that such a theory exists
over an arbitrary base ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg

universe u v w z t

namespace OrlikSolomon

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]

/-- A standard degreewise theory with products, localization with supports, oriented divisor
purity, transverse naturality and the boundary projection formula gives an ordinary theory.
The total cohomology is the direct sum over all cohomological degrees and twists, and the
three total exactness statements are proved from the degreewise localization sequence.
Blueprint: `lem:standard-bridge`. -/
def ofSupportsAndPurity (D : DegreewiseTheory.{u, v, w, z} k ℬ)
    (S : SupportsAndPurity.{u, v, w, z, t} D) : OrdinaryTheory.{u, v, w, z} k ℬ where
  bijective_algebraMap_gradeZero := D.bijective_algebraMap_gradeZero
  C := D.functor
  algebra A := inferInstanceAs (Algebra R (D.Total A))
  isScalarTower A := D.isScalarTower A
  grading := D.grading
  gradedAlgebra A := D.gradedAlgebra A
  algebraMap_mem_grading := D.algebraMap_mem_grading
  isHomogeneousOfShift_map := D.isHomogeneousOfShift_mapTotal
  isGradedCommutative := D.isGradedCommutative
  bijective_algebraMap_point := D.bijective_coeffMap_point
  eq_zero_of_mem_grading_point := D.eq_zero_of_mem_grading_point
  bijective_map_polynomialC := D.bijective_mapTotal_polynomialC
  gysin := S.gysin
  residue := S.residue
  isHomogeneousOfShift_gysin := S.isHomogeneousOfShift_gysinR
  isHomogeneousOfShift_residue := S.isHomogeneousOfShift_residueR
  exact_gysin_map := S.exact_gysinR_map
  exact_map_residue := S.exact_map_residueR
  exact_residue_gysin := S.exact_residueR_gysinR
  gysin_map := S.gysinR_natural
  residue_map := S.residueR_natural
  residue_mul_map P α _ β := S.residueR_mul_map P α β

variable (D : DegreewiseTheory.{u, v, w, z} k ℬ) (S : SupportsAndPurity.{u, v, w, z, t} D)

/-- Pullback in the constructed theory restricts to the given degreewise pullback. -/
@[simp]
lemma ofSupportsAndPurity_map_incl {A E : SmoothAlg k} (f : A ⟶ E) (i : ℤ × ℤ)
    (x : D.H A i) :
    (ofSupportsAndPurity D S).C.map f (D.incl A i x) = D.incl E i (D.map f i x) :=
  D.mapTotal_incl f i x

/-- Gysin in the constructed theory is oriented purity followed by support-forgetting. -/
lemma ofSupportsAndPurity_gysin_apply (P : DivisorPair k) (x : D.Total P.closed) :
    (ofSupportsAndPurity D S).gysin P x = S.forgetTotal P (S.purityTotal P x) := rfl

/-- Residue in the constructed theory is the connecting homomorphism followed by inverse purity. -/
lemma ofSupportsAndPurity_residue_apply (P : DivisorPair k) (x : D.Total P.compl) :
    (ofSupportsAndPurity D S).residue P x = (S.purityTotal P).symm (S.boundaryTotal P x) := rfl

end OrlikSolomon
