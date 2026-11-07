/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import OrlikSolomon.Cohomology.Deletion
public import OrlikSolomon.Geometry.Projective
public import OrlikSolomon.Geometry.RelationTargets

/-!
# Regression examples

This file collects consistency checks of the definitions against the blueprint's regression list.
At present it covers the structure `OrdinaryTheory` of `def:cohomology`, in particular the
blueprint's "zero coefficient ring" case and the case `R = B`, the logarithmic classes with
coefficients in `ℤ/2`, the example of two points of `𝔸¹` over `F₂` and its projective analogue, and
the first induction with zero coefficients and in dimension zero. The other arrangement examples of
that list will be added here as the modules they test appear. The example of one projective
hyperplane is `SmoothAlg.projectiveComplementIsoAffineSpace`.

## Main definitions

* `OrlikSolomon.Sanity.zeroTheory k`: the zero theory, with zero coefficients, over any `k`.
* `OrlikSolomon.Sanity.laurentWeight R`: the coefficient grading `ℬ w = R t^w` of `R[t, t⁻¹]`,
  used by the comparison with singular cohomology in the docstring of `OrdinaryTheory`.
* `OrlikSolomon.Sanity.twoPoints`: the two rational points of `𝔸¹` over `F₂`. Their complement has
  no `F₂`-points (`isEmpty_algHom_twoPoints`), and its ring is nonzero
  (`nontrivial_complementRing_twoPoints`). It still has the first target of `lem:small-targets`
  (`nonempty_relationTarget_twoPoints`).
* `OrlikSolomon.Sanity.twoPointsPair`: the deletion pair of one of them. Here `H` is a point, the
  restriction is empty (`restriction_twoPoints_eq_empty`), the open part has no `F₂`-points, and the
  other point restricts to the constant `1` (`mapUnits_complementRestriction_twoPoints`).
* `OrlikSolomon.Sanity.threePoints`: the three rational points of `P¹` over `F₂`. Their complement
  has no `F₂`-points (`isEmpty_algHom_threePoints`), and its ring is nonzero
  (`nontrivial_complementRing_threePoints`).

## Main results

* `OrlikSolomon.Sanity.exists_logMonomialBasis_zeroTheory_twoPoints`: the first induction with zero
  coefficients on a complement with no rational points. The recursive basis has two words of length
  one, although over the zero ring every family is a basis.

## What these checks show, and what they do not

`zeroTheory` shows that the fields of `OrdinaryTheory` can be satisfied at all, and it tests the
zero-ring edge case. It says nothing about the substantive axioms, because every field holds in it
trivially. Those axioms are checked in Lean by the de Rham instance `DeRham.ordinaryTheory k` of
`DeRham/Instance`, for a field `k` of characteristic zero, whose coefficients and point are nonzero.
The comparison with complex singular cohomology, recorded in the docstring of `OrdinaryTheory`, is
by hand and is not formalized.

The zero theory must have zero coefficients: a theory with `B = 0` has `R = 0`, since `R` is
identified with the weight-zero part of `B` (`subsingleton_coefficients_of_subsingleton`). A theory
over the zero ring has `B = 0` (`subsingleton_of_subsingleton_base`).

The equation `0` on the ambient ring `k` would give a bijective map of shift `(2, 1)` on `C(k)`,
which forces `B = 0` (`subsingleton_of_bijective_shift`). So it contradicts the dimension axiom only
for a nonzero theory, and `C(k) ≠ 0` for such a theory (`nontrivial_obj_point`). `DivisorPair` rules
out that equation on any nonzero ring (Mathlib's `zero_notMem_nonZeroDivisors`), and it keeps it on
the zero ring (`zero_mem_nonZeroDivisors_zero`).
-/

@[expose] public section

noncomputable section

open CategoryTheory OrlikSolomon.SmoothAlg
open scoped LaurentPolynomial

universe u v w z

namespace OrlikSolomon

namespace Sanity

/-! ### The zero theory -/

/-- The weight grading of the zero coefficient ring: every piece is the whole ring. -/
def zeroWeight : ℤ → Submodule PUnit.{v + 1} PUnit.{w + 1} := fun _ ↦ ⊤

instance : GradedAlgebra zeroWeight.{v, w} where
  one_mem := Submodule.mem_top
  mul_mem _ _ _ _ _ _ := Submodule.mem_top
  decompose' _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := DFinsupp.ext fun _ ↦ Subsingleton.elim _ _

/-- The functor sending every smooth algebra to the zero ring. -/
def zeroFunctor (k : Type u) [CommRing k] : SmoothAlg k ⥤ AlgCat.{z} PUnit.{w + 1} where
  obj _ := AlgCat.of _ PUnit.{z + 1}
  map _ := 𝟙 _

instance {k : Type u} [CommRing k] (A : SmoothAlg k) :
    Subsingleton ((zeroFunctor.{u, w, z} k).obj A) :=
  inferInstanceAs (Subsingleton PUnit)

instance {k : Type u} [CommRing k] (A : SmoothAlg k) :
    Algebra PUnit.{v + 1} ((zeroFunctor.{u, w, z} k).obj A) :=
  PUnit.algebra

/-- The zero theory: `C(X) = 0` for every `X`, with zero coefficients. It is a consistency check of
`OrdinaryTheory` and tests its zero-ring edge cases. It does not test the substantive axioms: see
the module docstring. -/
def zeroTheory (k : Type u) [CommRing k] : OrdinaryTheory.{u, v, w, z} k zeroWeight.{v, w} where
  bijective_algebraMap_gradeZero :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  C := zeroFunctor k
  algebra _ := inferInstance
  isScalarTower _ := ⟨fun _ _ _ ↦ Subsingleton.elim _ _⟩
  grading _ _ := ⊤
  gradedAlgebra _ :=
    { one_mem := Submodule.mem_top
      mul_mem _ _ _ _ _ _ := Submodule.mem_top
      decompose' _ := 0
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := DFinsupp.ext fun _ ↦ Subsingleton.elim _ _ }
  algebraMap_mem_grading _ _ _ _ := Submodule.mem_top
  isHomogeneousOfShift_map _ _ _ _ := Submodule.mem_top
  isGradedCommutative _ _ _ _ _ _ _ := Subsingleton.elim _ _
  bijective_algebraMap_point :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  eq_zero_of_mem_grading_point _ _ _ := Subsingleton.elim _ _
  bijective_map_polynomialC _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  gysin _ := 0
  residue _ := 0
  isHomogeneousOfShift_gysin _ _ _ _ := Submodule.mem_top
  isHomogeneousOfShift_residue _ _ _ _ := Submodule.mem_top
  exact_gysin_map _ _ := ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_map_residue _ _ := ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_residue_gysin _ _ := ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  gysin_map _ _ := Subsingleton.elim _ _
  residue_map _ _ := Subsingleton.elim _ _
  residue_mul_map _ _ _ _ := Subsingleton.elim _ _

/-! ### What the coefficient axioms force -/

section Coefficients

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)

include T

/-- Zero coefficients in `B` force zero coefficients in `R`, since `R` is identified with the
weight-zero part of `B`. So the zero theory needs `R = 0`. -/
theorem subsingleton_coefficients_of_subsingleton [Subsingleton B] : Subsingleton R :=
  T.injective_algebraMap.subsingleton

/-- A theory over the zero ring has zero coefficients: the point is then the empty scheme. -/
theorem subsingleton_of_subsingleton_base [Subsingleton k] : Subsingleton B :=
  have : Subsingleton (point k) := inferInstanceAs (Subsingleton k)
  have := T.subsingleton_obj_of_subsingleton (point k)
  T.bijective_algebraMap_point.1.subsingleton

/-- Nonzero coefficients give a nonzero point, unlike the zero theory. -/
theorem nontrivial_obj_point [Nontrivial B] : Nontrivial (T.C.obj (point k)) :=
  T.bijective_algebraMap_point.1.nontrivial

/-- A bijective map of shift `(2, 1)` on the cohomology of the point forces zero coefficients: it
vanishes, because the point is concentrated in cohomological degree zero. This is what the equation
`0` on the ambient ring `k` would produce, if it were allowed. So it would contradict the dimension
axiom of a nonzero theory, but not the zero theory. -/
theorem subsingleton_of_bijective_shift {g : T.C.obj (point k) →ₗ[B] T.C.obj (point k)}
    (hg : IsHomogeneousOfShift (T.grading (point k)) (T.grading (point k)) (2, 1) g)
    (hb : Function.Bijective g) : Subsingleton B := by
  have h (x : T.C.obj (point k)) : g x = 0 := by
    refine hg.map_eq_zero_of_forall (fun ⟨p, w⟩ ↦ ?_) x
    by_cases hp : p = 0
    · refine Or.inr fun y hy ↦ T.eq_zero_of_mem_grading_point (p := p + 2) (w := w + 1) ?_ hy
      simp [hp]
    · exact Or.inl fun y hy ↦ T.eq_zero_of_mem_grading_point hp hy
  have : Subsingleton (T.C.obj (point k)) :=
    subsingleton_of_forall_eq 0 fun x ↦ hb.1 (by rw [h, map_zero])
  exact T.bijective_algebraMap_point.1.subsingleton

end Coefficients

/-! ### Divisor pairs: what `eqn` may be -/

section Pairs

/-- The equation `0` is ruled out on any nonzero ambient ring, such as `k` for `k ≠ 0`. -/
example {A : Type*} [CommRing A] [Nontrivial A] : (0 : A) ∉ nonZeroDivisors A :=
  zero_notMem_nonZeroDivisors

/-- The equation `0` stays allowed on the zero ring, and no stronger condition is needed. -/
theorem zero_mem_nonZeroDivisors_zero (k : Type u) [CommRing k] :
    (0 : zero k) ∈ nonZeroDivisors (zero k) :=
  Subsingleton.elim (1 : zero k) 0 ▸ one_mem _

/-- The pair `(A, 1)` is a divisor pair, for any smooth `A`, and it proves that the zero ring has
zero cohomology: there is no axiom for the empty object. -/
example {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
    [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
    (A : SmoothAlg k) : Subsingleton (T.C.obj (zero k)) :=
  T.subsingleton_closed_of_bijective (DivisorPair.emptyDivisor A (zero k)) <| by
    change Function.Bijective (T.C.map (𝟙 A))
    simpa using Function.bijective_id

end Pairs

/-! ### The coefficients of singular cohomology

The comparison in the docstring of `OrdinaryTheory` takes `B = R[t, t⁻¹]` with `ℬ w = R t^w`. The
coefficient axiom C1 can at least be checked formally for it, and this is the only part of that
comparison that is formal. -/

section Laurent

variable (R : Type v) [CommRing R]

/-- The weight grading `ℬ w = R t^w` of `R[t, t⁻¹]`. -/
abbrev laurentWeight : ℤ → Submodule R R[T;T⁻¹] := AddMonoidAlgebra.grade R

/-- The structure map identifies `R` with the weight-zero part of `R[t, t⁻¹]`, for any `R`,
including the zero ring. This is the field `bijective_algebraMap_gradeZero` for the model. -/
theorem bijective_algebraMap_laurentWeight :
    Function.Bijective (algebraMap R (laurentWeight R 0)) := by
  constructor
  · intro r s h
    have h' : LaurentPolynomial.C r = LaurentPolynomial.C s := congrArg Subtype.val h
    simpa using congr($(h').coeff 0)
  · rintro ⟨x, hx⟩
    have hx' : x ∈ LinearMap.range (AddMonoidAlgebra.lsingle (R := R) (S := R) (0 : ℤ)) :=
      AddMonoidAlgebra.grade_eq_lsingle_range (R := R) (0 : ℤ) ▸ hx
    obtain ⟨r, rfl⟩ := hx'
    exact ⟨r, Subtype.ext rfl⟩

end Laurent

/-! ### Coefficients with `R = B`

At `R = B`, a term that mixes a `B`-linear map with the grading pieces fails with an instance
mismatch: see the implementation notes in `Cohomology/Axioms`. Components must be available all the
same, through the wrappers that are defined with `R` and `B` separate. -/

section SameRing

variable {k : Type u} [CommRing k] {B : Type w} [CommRing B] {ℬ : ℤ → Submodule B B}
  [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, w, w, z} k ℬ) {A D : SmoothAlg k}

example (f : A ⟶ D) (i : ℤ × ℤ) : T.grading A i →ₗ[B] T.grading D i :=
  (T.isHomogeneousOfShift_mapOverR f).component (add_zero i)

example (P : DivisorPair k) {i j : ℤ × ℤ} (h : i + (2, 1) = j) :
    T.grading P.closed i →ₗ[B] T.grading P.ambient j :=
  (T.isHomogeneousOfShift_gysinOverR P).component h

example (P : DivisorPair k) {i j : ℤ × ℤ} (h : i + (-1, -1) = j) :
    T.grading P.compl i →ₗ[B] T.grading P.closed j :=
  (T.isHomogeneousOfShift_residueOverR P).component h

/-- The component of the wrapper is the Gysin map itself, on underlying elements. -/
example (P : DivisorPair k) {i j : ℤ × ℤ} (h : i + (2, 1) = j) (x : T.grading P.closed i) :
    ((T.isHomogeneousOfShift_gysinOverR P).component h x : T.C.obj P.ambient) = T.gysin P x := by
  simp

/-- Total exactness gives exactness of components at `R = B`, as in `lem:extraction`. -/
example (P : DivisorPair k) {i j l : ℤ × ℤ} (hij : i + (2, 1) = j) (hjl : j + 0 = l) :
    Function.Exact ((T.isHomogeneousOfShift_gysinOverR P).component hij)
      ((T.isHomogeneousOfShift_mapOverR P.j).component hjl) :=
  ((T.isHomogeneousOfShift_gysinOverR P).exact_iff_forall_component
    (T.isHomogeneousOfShift_mapOverR P.j)).1 (T.exact_gysin_map P) hij hjl

end SameRing

/-! ### Logarithmic classes with coefficients in `ℤ/2`

Blueprint regression list: the square of a generator is zero with coefficients in `ℤ/2`. The
statements have no hypothesis on `2`, and these instances record that they apply where `2τ² = 0`
would say nothing. -/

section ZModTwo

variable {k : Type u} [CommRing k] {B : Type w} [CommRing B] [Algebra (ZMod 2) B]
  {ℬ : ℤ → Submodule (ZMod 2) B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, 0, w, z} k ℬ)
  {A : SmoothAlg k}

example : T.tau * T.tau = 0 := T.tau_mul_tau

example (u : Aˣ) : T.logClass u * T.logClass u = 0 := T.logClass_mul_self u

end ZModTwo

/-! ### Two points of the line over the field with two elements

The blueprint's regression example of a complement with no `k`-points whose coordinate ring is
nonzero. This is why `O(U_𝒜)` is a localization, and never a subset of `V`. -/

section TwoPoints

open Arrangement CoordinateRing

open scoped Classical in
/-- The two rational points of the affine line over the field with two elements. -/
def twoPoints : Arrangement (ZMod 2) (ZMod 2) :=
  ofFinset {zeroLocus (AffineMap.id _ _), zeroLocus (AffineMap.id _ _ - AffineMap.const _ _ 1)}

theorem zeroLocus_id_mem_twoPoints :
    zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) ∈ twoPoints := by
  refine mem_ofFinset.2 ⟨by simp, isHyperplane_zeroLocus_iff.2 ?_⟩
  simpa using fun h ↦ one_ne_zero (LinearMap.congr_fun h (1 : ZMod 2))

theorem zeroLocus_id_sub_one_mem_twoPoints :
    zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) ∈ twoPoints := by
  refine mem_ofFinset.2 ⟨by simp, isHyperplane_zeroLocus_iff.2 ?_⟩
  simpa using fun h ↦ one_ne_zero (LinearMap.congr_fun h (1 : ZMod 2))

/-- Every `F₂`-point of the line lies on one of the two hyperplanes. -/
theorem exists_mem_twoPoints (v : ZMod 2) : ∃ H ∈ twoPoints, v ∈ H := by
  obtain rfl | rfl : v = 0 ∨ v = 1 := by revert v; decide
  · exact ⟨_, zeroLocus_id_mem_twoPoints, by simp⟩
  · exact ⟨_, zeroLocus_id_sub_one_mem_twoPoints, by simp⟩

/-- The complement of the two points of the line over `F₂` has no `F₂`-points, even as a scheme: its
coordinate ring has no `F₂`-algebra map to `F₂`. -/
theorem isEmpty_algHom_twoPoints : IsEmpty (twoPoints.ComplementRing →ₐ[ZMod 2] ZMod 2) := by
  refine ⟨fun φ ↦ ?_⟩
  have h₀ := (ComplementRing.isUnit_coord (𝒜 := twoPoints)
    (.of_mem zeroLocus_id_mem_twoPoints)).map φ
  have h₁ := (ComplementRing.isUnit_coord (𝒜 := twoPoints)
    (.of_mem zeroLocus_id_sub_one_mem_twoPoints)).map φ
  rw [map_sub, map_sub, map_sub, coord_const] at h₁
  set a := φ (algebraMap _ _ (coord (AffineMap.id (ZMod 2) (ZMod 2))))
  have h1 : φ (algebraMap _ _ (algebraMap (ZMod 2) (CoordinateRing (ZMod 2) (ZMod 2)) 1)) = 1 := by
    simp
  rw [h1] at h₁
  obtain h | h := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  · simp [h] at h₀
  · simp [h] at h₁

/-- The coordinate ring of the complement of the two points of the line over `F₂` is nonzero, even
though the complement has no `F₂`-points, see `isEmpty_algHom_twoPoints`.

Blueprint: the regression list, "the two rational points in `𝔸¹` over `F₂`". -/
theorem nontrivial_complementRing_twoPoints : Nontrivial twoPoints.ComplementRing :=
  inferInstance

/-- The two points have empty intersection, so their equations factor through the first target of
`lem:small-targets`, although the source has no `F₂`-points, see `isEmpty_algHom_twoPoints`. This is
the geometry behind the relation `e₁ e₂ = 0`.

Blueprint: the regression list, "the two rational points in `𝔸¹` over `F₂`". -/
theorem nonempty_relationTarget_twoPoints :
    Nonempty (RelationTarget twoPoints
      ([⟨_, zeroLocus_id_mem_twoPoints⟩, ⟨_, zeroLocus_id_sub_one_mem_twoPoints⟩].map
        (SmoothAlg.equationUnit twoPoints))) := by
  refine ⟨RelationTarget.ofInterEqBot _ ?_⟩
  ext x
  refine iff_of_false (fun hx ↦ ?_) (AffineSubspace.notMem_bot _ _ _)
  obtain ⟨rfl, h⟩ : x = 0 ∧ x - 1 = 0 := by simpa [AffineSubspace.mem_inf_iff] using hx
  simp at h

/-! The deletion pair of the origin, in dimension one, over a finite field, with an open part that
has no rational points. -/

/-- The identity is an equation of the origin of the line. -/
theorem isEquation_id_twoPoints :
    IsEquation (AffineMap.id (ZMod 2) (ZMod 2)) (zeroLocus (AffineMap.id _ _)) :=
  isEquation_of_zeroLocus_mem zeroLocus_id_mem_twoPoints

/-- The deletion pair `(O(𝔸¹ ∖ {1}), O(pt), O(𝔸¹ ∖ {0, 1}), x)` over `F₂`. The open part is the
complement in `isEmpty_algHom_twoPoints`, which has no `F₂`-points. -/
def twoPointsPair : DivisorPair (ZMod 2) :=
  DivisorPair.deletionPair twoPoints zeroLocus_id_mem_twoPoints isEquation_id_twoPoints

/-- The open part of `twoPointsPair` is the complement of the two points. -/
example : twoPointsPair.compl = complement twoPoints := rfl

instance : Subsingleton (zeroLocus (AffineMap.id (ZMod 2) (ZMod 2))).direction := by
  rw [isEquation_id_twoPoints.direction_eq]
  simpa using inferInstanceAs (Subsingleton (⊥ : Submodule (ZMod 2) (ZMod 2)))

/-- The origin of the line is a point, with direction zero, so the restriction to it is empty and
the divisor of `twoPointsPair` is the ring of the empty arrangement on the zero vector space. -/
theorem restriction_twoPoints_eq_empty :
    twoPoints.restriction (zeroLocus (AffineMap.id (ZMod 2) (ZMod 2))) = ∅ :=
  eq_empty_of_subsingleton _

theorem zeroLocus_id_sub_one_mem_deletion :
    zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) ∈
      twoPoints.deletion (zeroLocus (AffineMap.id _ _)) := by
  refine mem_deletion.2 ⟨fun h ↦ ?_, zeroLocus_id_sub_one_mem_twoPoints⟩
  have h0 : (0 : ZMod 2) ∈ zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) := by simp
  rw [← h] at h0
  simp at h0

theorem inf_zeroLocus_id_twoPoints :
    zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) ⊓
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) = ⊥ := by
  by_contra h
  obtain ⟨x, hx⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 h
  obtain ⟨h₀, h₁⟩ := (AffineSubspace.mem_inf_iff _ _ _).1 hx
  simp only [mem_zeroLocus, AffineMap.id_apply] at h₀
  simp [mem_zeroLocus, h₀] at h₁

/-- The other point does not meet the origin, so its equation `x - 1` restricts to a nonzero
constant, and over `F₂` the only one is `1`. -/
theorem mapUnits_complementRestriction_twoPoints :
    mapUnits (complementRestriction twoPoints isEquation_id_twoPoints.isHyperplane)
      (complementUnit (twoPoints.deletion (zeroLocus (AffineMap.id (ZMod 2) (ZMod 2))))
        (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1)
        (.of_mem zeroLocus_id_sub_one_mem_deletion)) = 1 := by
  obtain ⟨c, hc⟩ := exists_mapUnits_complementRestriction_eq_constUnit
    isEquation_id_twoPoints.isHyperplane zeroLocus_id_sub_one_mem_deletion
    (isEquation_of_zeroLocus_mem zeroLocus_id_sub_one_mem_twoPoints) inf_zeroLocus_id_twoPoints
  obtain rfl : c = 1 := Units.ext ((by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) c c.ne_zero)
  simpa using hc

/-- The two points have `b₁ = 2`, and this is what `thm:cohom-basis` counts. -/
theorem bettiNumber_one_twoPoints : twoPoints.bettiNumber 1 = 2 := by
  classical
  have hne : zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) ≠
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) := fun h ↦
    (mem_deletion.1 zeroLocus_id_sub_one_mem_deletion).1 h.symm
  have h𝒜 : twoPoints.hyperplanes = {zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)),
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1)} := by
    ext K
    simp only [mem_hyperplanes, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hK ↦ ?_, ?_⟩
    · simpa using (mem_ofFinset.1 hK).1
    · rintro (rfl | rfl)
      exacts [zeroLocus_id_mem_twoPoints, zeroLocus_id_sub_one_mem_twoPoints]
  simp [bettiNumber, poincarePolynomial_pair_disjoint twoPoints hne h𝒜 inf_zeroLocus_id_twoPoints,
    Polynomial.coeff_one]

/-- The first induction with zero coefficients, on a complement with no rational points. Over the
zero ring every family is a basis, and yet the recursive basis of the two points has exactly two
words of length one, so the count of `exists_logMonomialBasis` does not come from a rank. -/
theorem exists_logMonomialBasis_zeroTheory_twoPoints :
    ∃ b : (zeroTheory.{0, v, w, z} (ZMod 2)).LogMonomialBasis twoPoints, b.wordCount 1 = 2 :=
  let ⟨b, hb⟩ := (zeroTheory.{0, v, w, z} (ZMod 2)).exists_logMonomialBasis twoPoints
  ⟨b, (hb 1).trans bettiNumber_one_twoPoints⟩

/-- The bound above the dimension holds on a complement with no rational points. -/
example {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{0, v, w, z} (ZMod 2) ℬ) {w' : ℤ}
    {x : T.C.obj (complement twoPoints)} (hx : x ∈ T.grading (complement twoPoints) (2, w')) :
    x = 0 :=
  T.eq_zero_of_mem_grading_of_finrank_lt twoPoints (by simp) hx

/-- In dimension zero, there are no hyperplanes, and the bound says that all classes are in degree
zero. -/
example {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
    (𝒜 : Arrangement k PUnit.{u + 1}) {p w' : ℤ} (hp : p ≠ 0)
    {x : T.C.obj (complement 𝒜)} (hx : x ∈ T.grading (complement 𝒜) (p, w')) : x = 0 := by
  obtain hp | hp := hp.lt_or_gt
  · exact T.eq_zero_of_mem_grading_of_neg 𝒜 hp hx
  · exact T.eq_zero_of_mem_grading_of_finrank_lt 𝒜
      (by simpa [Module.finrank_zero_of_subsingleton] using hp) hx

end TwoPoints

section ThreePoints

open ProjectiveArrangement ProjectiveArrangement.ComplementRing

/-- The linear form `x` on `F₂²`. -/
def formX : Module.Dual (ZMod 2) (Fin 2 → ZMod 2) := LinearMap.proj 0

/-- The linear form `y` on `F₂²`. -/
def formY : Module.Dual (ZMod 2) (Fin 2 → ZMod 2) := LinearMap.proj 1

theorem formX_ne_zero : formX ≠ 0 := fun h ↦
  one_ne_zero (α := ZMod 2) (by simpa [formX] using LinearMap.congr_fun h ![1, 0])

theorem formY_ne_zero : formY ≠ 0 := fun h ↦
  one_ne_zero (α := ZMod 2) (by simpa [formY] using LinearMap.congr_fun h ![0, 1])

theorem formX_add_formY_ne_zero : formX + formY ≠ 0 := fun h ↦
  one_ne_zero (α := ZMod 2) (by simpa [formX, formY] using LinearMap.congr_fun h ![1, 0])

open scoped Classical in
/-- The three rational points of the projective line over the field with two elements: the zeros of
`x`, of `y` and of `x + y`. -/
def threePoints : ProjectiveArrangement (ZMod 2) (Fin 2 → ZMod 2) :=
  ofForms {formX, formY, formX + formY} <| by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨formX_ne_zero, formY_ne_zero, formX_add_formY_ne_zero⟩

/-- The complement of the three points of the projective line over `F₂` has no `F₂`-points, even as
a scheme: its coordinate ring has no `F₂`-algebra map to `F₂`. Both `x / y` and
`(x + y) / y = x / y + 1` are units, and no element of `F₂` has that property. -/
theorem isEmpty_algHom_threePoints : IsEmpty (threePoints.ComplementRing →ₐ[ZMod 2] ZMod 2) := by
  classical
  refine ⟨fun φ ↦ ?_⟩
  have hx : LinearMap.ker formX ∈ threePoints := ker_mem_ofForms (by simp)
  have hy : LinearMap.ker formY ∈ threePoints := ker_mem_ofForms (by simp)
  have hxy : LinearMap.ker (formX + formY) ∈ threePoints := ker_mem_ofForms (by simp)
  have h₀ := (ratioUnit hx hy).isUnit.map φ
  have h₁ := (ratioUnit hxy hy).isUnit.map φ
  rw [coe_ratioUnit] at h₀ h₁
  rw [ratio_add, ratio_self, map_add, map_one] at h₁
  obtain h | h := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (φ (ratio formX hy))
  · simp [h] at h₀
  · rw [h, show (1 + 1 : ZMod 2) = 0 by decide] at h₁
    simp at h₁

/-- The coordinate ring of the complement of the three points of the projective line over `F₂` is
nonzero, even though the complement has no `F₂`-points, see `isEmpty_algHom_threePoints`. So it does
not matter that no hyperplane at infinity can be chosen to make the complement have a point.

Blueprint: the regression list, the projective form of "the two rational points in `𝔸¹` over `F₂`".
-/
theorem nontrivial_complementRing_threePoints : Nontrivial threePoints.ComplementRing :=
  inferInstance

end ThreePoints

end Sanity

end OrlikSolomon
