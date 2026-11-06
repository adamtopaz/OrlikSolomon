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

/-- On one summand, the constructed Gysin map is the given degreewise purity followed by the
given support-forgetting map. -/
@[simp]
lemma ofSupportsAndPurity_gysin_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.closed i) :
    (ofSupportsAndPurity D S).gysin P (D.incl P.closed i x) =
      D.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) := by
  rw [ofSupportsAndPurity_gysin_apply, S.purityTotal_incl, S.forgetTotal_incl]

/-- Residue in the constructed theory is the connecting homomorphism followed by inverse purity. -/
lemma ofSupportsAndPurity_residue_apply (P : DivisorPair k) (x : D.Total P.compl) :
    (ofSupportsAndPurity D S).residue P x = (S.purityTotal P).symm (S.boundaryTotal P x) := rfl

/-- Applying purity to the constructed residue gives the original localization boundary. -/
@[simp]
lemma ofSupportsAndPurity_purity_residue (P : DivisorPair k) (x : D.Total P.compl) :
    S.purityTotal P ((ofSupportsAndPurity D S).residue P x) = S.boundaryTotal P x :=
  (S.purityTotal P).apply_symm_apply _

/-- The degreewise Gysin map on the original groups, obtained by projecting the constructed
total map from degree `i` to degree `j`. The localization sequence uses `i + (2,1) = j`. -/
def gysinDegreewiseOfSupportsAndPurity (P : DivisorPair k) (i j : ℤ × ℤ) :
    D.H P.closed i →ₗ[R] D.H P.ambient j :=
  (DirectSum.component R _ (D.H P.ambient) j).comp
    ((S.gysinR P).comp (D.incl P.closed i))

/-- The degreewise residue on the original groups, obtained by projecting the constructed
total map from degree `i` to degree `j`. The localization sequence uses `i + (-1,-1) = j`. -/
def residueDegreewiseOfSupportsAndPurity (P : DivisorPair k) (i j : ℤ × ℤ) :
    D.H P.compl i →ₗ[R] D.H P.closed j :=
  (DirectSum.component R _ (D.H P.closed) j).comp
    ((S.residueR P).comp (D.incl P.compl i))

/-- The degreewise Gysin map is exactly the constructed map on a homogeneous summand. -/
lemma gysinDegreewiseOfSupportsAndPurity_incl (P : DivisorPair k) {i j : ℤ × ℤ}
    (hij : i + (2, 1) = j) (x : D.H P.closed i) :
    (ofSupportsAndPurity D S).gysin P (D.incl P.closed i x) =
      D.incl P.ambient j (gysinDegreewiseOfSupportsAndPurity D S P i j x) := by
  change S.gysinR P (D.incl P.closed i x) =
    D.incl P.ambient j (DirectSum.component R _ (D.H P.ambient) j
      (S.gysinR P (D.incl P.closed i x)))
  exact (lof_component_of_mem_directSumGrading _ _ _
    ((S.isHomogeneousOfShift_gysinR P).map_mem hij (lof_mem_directSumGrading _ _ _))).symm

/-- The degreewise residue is exactly the constructed map on a homogeneous summand. -/
lemma residueDegreewiseOfSupportsAndPurity_incl (P : DivisorPair k) {i j : ℤ × ℤ}
    (hij : i + (-1, -1) = j) (x : D.H P.compl i) :
    (ofSupportsAndPurity D S).residue P (D.incl P.compl i x) =
      D.incl P.closed j (residueDegreewiseOfSupportsAndPurity D S P i j x) := by
  change S.residueR P (D.incl P.compl i x) =
    D.incl P.closed j (DirectSum.component R _ (D.H P.closed) j
      (S.residueR P (D.incl P.compl i x)))
  exact (lof_component_of_mem_directSumGrading _ _ _
    ((S.isHomogeneousOfShift_residueR P).map_mem hij (lof_mem_directSumGrading _ _ _))).symm

/-- The constructed degreewise localization sequence is exact at ambient cohomology:
`H^{p-2,w-1}(D) → H^{p,w}(X) → H^{p,w}(U)`. Blueprint: `lem:standard-bridge`. -/
theorem ofSupportsAndPurity_exact_gysin_map (P : DivisorPair k) {i j : ℤ × ℤ}
    (hij : i + (2, 1) = j) :
    Function.Exact (gysinDegreewiseOfSupportsAndPurity D S P i j) (D.map P.j j) := by
  have h := exact_directSum_components (D.H P.closed) (D.H P.ambient) (D.H P.compl)
    (S.gysinR P) (D.mapTotalR P.j).toLinearMap
    (S.isHomogeneousOfShift_gysinR P) (D.isHomogeneousOfShift_mapTotalR P.j)
    (S.exact_gysinR_map P) hij (add_zero j)
  simpa only [gysinDegreewiseOfSupportsAndPurity, D.component_mapTotalR_incl] using h

/-- The constructed degreewise localization sequence is exact at open cohomology:
`H^{p,w}(X) → H^{p,w}(U) → H^{p-1,w-1}(D)`. Blueprint: `lem:standard-bridge`. -/
theorem ofSupportsAndPurity_exact_map_residue (P : DivisorPair k) {i j : ℤ × ℤ}
    (hij : i + (-1, -1) = j) :
    Function.Exact (D.map P.j i) (residueDegreewiseOfSupportsAndPurity D S P i j) := by
  have h := exact_directSum_components (D.H P.ambient) (D.H P.compl) (D.H P.closed)
    (D.mapTotalR P.j).toLinearMap (S.residueR P)
    (D.isHomogeneousOfShift_mapTotalR P.j) (S.isHomogeneousOfShift_residueR P)
    (S.exact_map_residueR P) (add_zero i) hij
  simpa only [residueDegreewiseOfSupportsAndPurity, D.component_mapTotalR_incl] using h

/-- The constructed degreewise localization sequence is exact at divisor cohomology:
`H^{p,w}(U) → H^{p-1,w-1}(D) → H^{p+1,w}(X)`. Blueprint: `lem:standard-bridge`. -/
theorem ofSupportsAndPurity_exact_residue_gysin (P : DivisorPair k) {i j l : ℤ × ℤ}
    (hij : i + (-1, -1) = j) (hjl : j + (2, 1) = l) :
    Function.Exact (residueDegreewiseOfSupportsAndPurity D S P i j)
      (gysinDegreewiseOfSupportsAndPurity D S P j l) :=
  exact_directSum_components (D.H P.compl) (D.H P.closed) (D.H P.ambient)
    (S.residueR P) (S.gysinR P)
    (S.isHomogeneousOfShift_residueR P) (S.isHomogeneousOfShift_gysinR P)
    (S.exact_residueR_gysinR P) hij hjl

end OrlikSolomon
