/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Data.ZMod.Defs
public import OrlikSolomon.Cohomology.Logarithms

/-!
# Regression examples

This file collects consistency checks of the definitions against the blueprint's regression list.
At present it covers the structure `OrdinaryTheory` of `def:cohomology`, in particular the
blueprint's "zero coefficient ring" case and the case `R = B`, and the logarithmic classes with
coefficients in `ℤ/2`. The arrangement examples of that list will be added here as the modules they
test appear.

## Main definitions

* `OrlikSolomon.Sanity.zeroTheory k`: the zero theory, with zero coefficients, over any `k`.
* `OrlikSolomon.Sanity.laurentWeight R`: the coefficient grading `ℬ w = R t^w` of `R[t, t⁻¹]`,
  used by the comparison with singular cohomology in the docstring of `OrdinaryTheory`.

## What these checks show, and what they do not

`zeroTheory` shows that the fields of `OrdinaryTheory` can be satisfied at all, and it tests the
zero-ring edge case. It says nothing about the substantive axioms, because every field holds in it
trivially. The check of those axioms is the comparison with complex singular cohomology by hand,
recorded in the docstring of `OrdinaryTheory`, which is not formalized.

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

end Sanity

end OrlikSolomon
