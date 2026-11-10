/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.DegreeOne
public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Maps
public import OrlikSolomon.HyperplaneGT.Diagram.Basic.MarkingMaps
public import OrlikSolomon.Presentation.Geometric.Ordinary

/-!
# Canonical logarithmic coordinates on actual degree-one cohomology

The canonical generator coordinates of A01 followed by the existing geometric structure
theorem identify each finite free hyperplane module with actual `H^{1,1}`. The common target
has the ordered logarithmic basis `[t]`, `[t-1]`. Both actual inclusion and tagged marking
pullbacks agree with their combinatorial linear maps.

All results concern a supplied full geometric ordinary theory. They construct no new
cohomology instance, and hold also for zero coefficients and in characteristic two.

Blueprint: the degree-one comparison in A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u v r b h

open CategoryTheory AlgebraicGeometry Module

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Arrangement OSAlgebra

variable {k : Type u} [Field k] {R : Type r} [CommRing R]
  {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Actual cohomology of bidegree `(1,1)` on the open complement. -/
def degreeOne (A : Arrangement k V) : Submodule R (T.obj (D.complement A)) :=
  T.grading (D.complement A) (1, 1)

/-- Actual cohomology of bidegree `(2,2)` on the open complement. -/
def degreeTwo (A : Arrangement k V) : Submodule R (T.obj (D.complement A)) :=
  T.grading (D.complement A) (2, 2)

/-- Canonical hyperplane-generator coordinates in the actual degree-one cohomology.
The coefficient ring may be zero.

Blueprint: A04 (`thm:a04`). -/
def degreeOneEquiv (A : Arrangement k V) : (A →₀ R) ≃ₗ[R] degreeOne T A :=
  (osDegreeOneEquiv R A).trans (T.degreeEquiv A 1)

/-- The degree-one comparison is the existing realization of the canonical OS coordinates.
-/
@[simp]
theorem coe_degreeOneEquiv (A : Arrangement k V) (x : A →₀ R) :
    (degreeOneEquiv T A x : T.obj (D.complement A)) =
      T.realizationOverR A (osDegreeOneEquiv R A x) := rfl

/-- A standard basis vector maps to its geometric logarithmic generator, independently of
the equation chosen for the hyperplane. -/
theorem degreeOneEquiv_single_of_isEquation (A : Arrangement k V) (H : A)
    {f : V →ᵃ[k] k} (hf : IsEquation f H) (c : R) :
    (degreeOneEquiv T A (Finsupp.single H c) : T.obj (D.complement A)) =
      c • T.logClass (Geometric.complementUnit A f (hf.covers H.property)) := by
  rw [coe_degreeOneEquiv, osDegreeOneEquiv_single]
  simp only [Submodule.coe_smul, map_smul,
    T.realizationOverR_generator_of_isEquation H hf]

/-- The canonical logarithmic basis is indexed by the actual hyperplane labels. -/
def degreeOneBasis (A : Arrangement k V) : Basis A R (degreeOne T A) :=
  (Finsupp.basisSingleOne (R := R) (ι := A)).map (degreeOneEquiv T A)

/-- Basis coordinates are exactly the inverse canonical generator comparison. -/
@[simp]
theorem degreeOneBasis_repr (A : Arrangement k V) (x : degreeOne T A) :
    (degreeOneBasis T A).repr x = (degreeOneEquiv T A).symm x := rfl

/-- The existing realization over `R` commutes with actual complement inclusions. -/
theorem realizationOverR_map {A A' : Arrangement k V} (hA : A ≤ A')
    (x : OSAlgebra R A) :
    T.realizationOverR A' (OSAlgebra.map R hA x) =
      T.pull (D.complementInclusion hA) (T.realizationOverR A x) := by
  rw [T.realizationOverR_apply, T.realizationOverR_apply,
    ← OSAlgebra.map_coefficientMap, T.affineEquiv_map]

/-- Canonical degree-one coordinates identify actual inclusion pullback with extension by
zero on the arrangement labels. -/
theorem degreeOneEquiv_inclusion {A A' : Arrangement k V} (hA : A ≤ A') :
    (componentPull T (D.complementInclusion hA) 1).comp
        (degreeOneEquiv T A).toLinearMap =
      (degreeOneEquiv T A').toLinearMap.comp
        (Finsupp.lmapDomain R R (Arrangement.inclusion hA)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change T.pull _ (T.realizationOverR A (osDegreeOneEquiv R A x)) =
    T.realizationOverR A' (osDegreeOneEquiv R A'
      (Finsupp.lmapDomain R R (Arrangement.inclusion hA) x))
  rw [osDegreeOneEquiv_naturality]
  exact (realizationOverR_map T hA _).symm

/-- Ordered coordinates at the single actual common target. -/
def targetDegreeOneEquiv :
    (Fin 2 →₀ R) ≃ₗ[R] degreeOne T (twoPunctureArrangement k) :=
  (markingTargetDegreeOneEquiv (k := k) R).trans
    (T.degreeEquiv (twoPunctureArrangement k) 1)

/-- The ordered logarithmic basis at the one common two-puncture target. -/
def targetDegreeOneBasis : Basis (Fin 2) R (degreeOne T (twoPunctureArrangement k)) :=
  (Finsupp.basisSingleOne (R := R) (ι := Fin 2)).map (targetDegreeOneEquiv T)

/-- Ordered target basis coordinates are the inverse target comparison. -/
@[simp]
theorem targetDegreeOneBasis_repr (x : degreeOne T (twoPunctureArrangement k)) :
    (targetDegreeOneBasis T).repr x = (targetDegreeOneEquiv T).symm x := rfl

/-- The ordered target basis consists of the actual geometric classes `[t]`, `[t-1]`. -/
@[simp]
theorem coe_targetDegreeOneEquiv_single (a : Fin 2) (c : R) :
    (targetDegreeOneEquiv T (Finsupp.single a c) :
      T.obj (D.complement (twoPunctureArrangement k))) =
      c • T.logClass (schemeMarkingTargetUnit D a) := by
  change T.realizationOverR (twoPunctureArrangement k)
    (markingTargetDegreeOneEquiv (k := k) R (Finsupp.single a c)) = _
  rw [markingTargetDegreeOneEquiv_single, map_smul]
  congr 1
  have hm : zeroLocus (AffineMap.id k k - AffineMap.const k k (a.val : k)) ∈
      twoPunctureArrangement k := by
    rw [← twoPunctureLabel_val k a]
    exact (twoPunctureLabel k a).property
  have hf : IsEquation (AffineMap.id k k - AffineMap.const k k (a.val : k))
      (twoPunctureLabelEquiv k a) := by
    simpa only [twoPunctureLabelEquiv_apply, twoPunctureLabel_val] using
      isEquation_of_zeroLocus_mem hm
  exact T.realizationOverR_generator_of_isEquation _ hf

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k] {S : Set k₀} {n : ℕ}

/-- Each available marking label is sent to the logarithm of its actual level equation. -/
theorem degreeOneEquiv_fiberLabel (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) (a : Fin 2) (c : R) :
    (degreeOneEquiv T A (Finsupp.single (w.fiberLabel hw a) c) :
      T.obj (D.complement A)) =
      c • T.logClass (Geometric.complementUnit A
        (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
        (hw.covers_fiber a)) := by
  have hm := (w.fiberLabel hw a).property
  rw [w.fiberLabel_val, w.fiber_val] at hm
  have hf : IsEquation
      (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
      (w.fiberLabel hw a) := by
    simpa only [w.fiberLabel_val, w.fiber_val] using isEquation_of_zeroLocus_mem hm
  exact degreeOneEquiv_single_of_isEquation T A _ hf c

/-- The canonical basis comparison intertwines the actual tagged scheme pullback and the
ordered combinatorial marking map, with the same target for every tag and stage. -/
theorem degreeOneEquiv_marking (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (componentPull T (w.schemeMap D hw) 1).comp (targetDegreeOneEquiv T).toLinearMap =
      (degreeOneEquiv T A).toLinearMap.comp (w.basisMap R hw) := by
  apply Finsupp.lhom_ext
  intro a c
  apply Subtype.ext
  change T.pull (w.schemeMap D hw)
      (targetDegreeOneEquiv T (Finsupp.single a c) :
        T.obj (D.complement (twoPunctureArrangement k))) =
    (degreeOneEquiv T A (w.basisMap R hw (Finsupp.single a c)) :
      T.obj (D.complement A))
  rw [coe_targetDegreeOneEquiv_single T a c, w.basisMap_single R hw a c,
    degreeOneEquiv_fiberLabel T w hw a c]
  change ((T.pull (w.schemeMap D hw)).restrictScalars R)
      (c • T.logClass (schemeMarkingTargetUnit D a)) = _
  rw [map_smul]
  congr 1
  exact w.pull_logClass_targetUnit T hw a

end OrlikSolomon.HyperplaneGT.Cohomology
