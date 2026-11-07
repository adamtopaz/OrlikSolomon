/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Axioms
public import OrlikSolomon.DeRham.Instance.Twisted

/-!
# The Laurent-twisted functor, and the first fields of the de Rham instance

This file packages `TwistedCohomology k A` of `DeRham/Instance/Twisted` as a functor
`SmoothAlg k ⥤ AlgCat k[T;T⁻¹]`, and it proves every field of `OrdinaryTheory` that precedes the
Gysin and residue maps, for `R = k`, `B = k[T;T⁻¹]` and `ℬ = laurentGrading k`.

## Main definitions

* `OrlikSolomon.DeRham.twistedCohomologyFunctor k`: the field `C`.

## Main results

The fields of `OrdinaryTheory`, in order:

| Field | Here |
| --- | --- |
| `bijective_algebraMap_gradeZero` | `bijective_algebraMap_laurentGrading_zero` |
| `C` | `twistedCohomologyFunctor` |
| `algebra` | `instAlgebraObjTwistedCohomologyFunctor` |
| `isScalarTower` | `instIsScalarTowerObjTwistedCohomologyFunctor` |
| `grading` | `TwistedCohomology.grading` |
| `gradedAlgebra` | `TwistedCohomology.gradedAlgebraGrading` |
| `algebraMap_mem_grading` | `TwistedCohomology.algebraMap_mem_grading` |
| `isHomogeneousOfShift_map` | `isHomogeneousOfShift_twistedCohomologyFunctor_map` |
| `isGradedCommutative` | `TwistedCohomology.isGradedCommutative_grading` |
| `bijective_algebraMap_point` | `bijective_algebraMap_twistedCohomologyFunctor_point` |
| `eq_zero_of_mem_grading_point` | `TwistedCohomology.eq_zero_of_mem_grading_point` |
| `bijective_map_polynomialC` | `bijective_twistedCohomologyFunctor_map_polynomialC` |

`Examples/DeRhamInstance` fills the structure with these, taking the remaining fields as arguments,
which checks that each of them has the exact shape of its field. That is a test of shape: the
remaining fields are not hypotheses of anything here.

The coefficient ring and the point are nonzero: `nontrivial_coefficients`, and the instance on
`(twistedCohomologyFunctor k).obj (point k)`.

## How the instance computes

The object `(twistedCohomologyFunctor k).obj A` is `TwistedCohomology k A` at default transparency.
It is not at the transparency that `rw` and `simp` use, because the functor is a `def`, as objects
and pairs are: see the implementation notes in `Geometry/SmoothAlg`. An instance found through the
object, such as its multiplication, is the instance of the tensor product only at default
transparency too. In particular `simp` leaves a goal `x = y` unsolved, with identical sides, when
they are typed differently.

So state and prove computations on `TwistedCohomology k A`, where `simp` works, and pass between the
two once, with `exact` or `change`. The lemmas `twistedCohomologyFunctor_map_apply` and
`twistedCohomologyFunctor_map_tmul` are `rfl`. `Examples/DeRhamInstance` shows this on a value of
the structure: reading a homogeneous class as `T w ⊗ₜ c`, and assembling
`OS_k(𝒜) ≃ₐ[k] H^•_dR(U_𝒜)` from `OrdinaryTheory.diagonalEquiv` and
`TwistedCohomology.diagonalEquiv`.

## Blueprint

`def:dr-twisted-functor`, `lem:dr-ordinary-basic`, and the nonvanishing in `thm:dr-instance`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial (T)
open OrlikSolomon.SmoothAlg

universe u

namespace OrlikSolomon.DeRham

variable (k : Type u) [CommRing k]

/-- **The Laurent-twisted functor**, the field `C` of the de Rham instance. It sends a smooth
algebra `A` to `C(A) = k[T;T⁻¹] ⊗[k] H^•_dR(A/k)`, and a map `φ` to `H(φ) ⊗ 1`. The
`k[T;T⁻¹]`-algebra structure uses the coefficient factor.

Blueprint: `def:dr-twisted-functor`. -/
def twistedCohomologyFunctor : SmoothAlg k ⥤ AlgCat.{u} k[T;T⁻¹] where
  obj A := AlgCat.of k[T;T⁻¹] (TwistedCohomology k A)
  map f := AlgCat.ofHom (TwistedCohomology.map (algHom f))
  map_id A := by
    apply AlgCat.hom_ext
    exact TwistedCohomology.map_id
  map_comp f g := by
    apply AlgCat.hom_ext
    exact TwistedCohomology.map_comp (algHom g) (algHom f)

/-- The `k`-algebra structure of `C(A)`, which is the restriction of its `k[T;T⁻¹]`-algebra
structure. It is the field `algebra` of the de Rham instance.

Blueprint: `def:dr-twisted-functor`. -/
instance instAlgebraObjTwistedCohomologyFunctor (A : SmoothAlg k) :
    Algebra k ((twistedCohomologyFunctor k).obj A) :=
  inferInstanceAs (Algebra k (TwistedCohomology k A))

/-- The `k`-action on `C(A)` is the restriction of the `k[T;T⁻¹]`-action, the field `isScalarTower`
of the de Rham instance.

Blueprint: `def:dr-twisted-functor`. -/
instance instIsScalarTowerObjTwistedCohomologyFunctor (A : SmoothAlg k) :
    IsScalarTower k k[T;T⁻¹] ((twistedCohomologyFunctor k).obj A) :=
  inferInstanceAs (IsScalarTower k k[T;T⁻¹] (TwistedCohomology k A))

variable {k} {A D : SmoothAlg k}

/-- The object of a smooth algebra is its twisted cohomology. This is not a `simp` lemma: see the
module docstring. -/
theorem twistedCohomologyFunctor_obj (A : SmoothAlg k) :
    (twistedCohomologyFunctor k).obj A = AlgCat.of k[T;T⁻¹] (TwistedCohomology k A) :=
  rfl

/-- The algebra map underlying the image of a morphism. -/
theorem twistedCohomologyFunctor_map_hom (f : A ⟶ D) :
    ((twistedCohomologyFunctor k).map f).hom = TwistedCohomology.map (algHom f) :=
  rfl

/-- The image of a morphism, on an element. -/
theorem twistedCohomologyFunctor_map_apply (f : A ⟶ D) (x : TwistedCohomology k A) :
    (twistedCohomologyFunctor k).map f x = TwistedCohomology.map (algHom f) x :=
  rfl

/-- The image of a morphism is `H(φ) ⊗ 1`. This is not a `simp` lemma: see the module docstring.

Blueprint: `def:dr-twisted-functor`. -/
theorem twistedCohomologyFunctor_map_tmul (f : A ⟶ D) (b : k[T;T⁻¹]) (c : Cohomology k A) :
    (twistedCohomologyFunctor k).map f (b ⊗ₜ[k] c : TwistedCohomology k A) =
      (b ⊗ₜ[k] Cohomology.map (algHom f) c : TwistedCohomology k D) :=
  rfl

/-! ### The fields -/

/-- Pullbacks preserve bidegrees.

Blueprint: `lem:dr-ordinary-basic`, for the field `isHomogeneousOfShift_map`. -/
theorem isHomogeneousOfShift_twistedCohomologyFunctor_map (f : A ⟶ D) :
    IsHomogeneousOfShift (TwistedCohomology.grading k A) (TwistedCohomology.grading k D) 0
      ((twistedCohomologyFunctor k).map f) :=
  TwistedCohomology.isHomogeneousOfShift_map (algHom f)

variable (k) in
/-- The point is identified with the coefficient ring, through the structure map.

Blueprint: `lem:dr-ordinary-basic`, for the field `bijective_algebraMap_point`. -/
theorem bijective_algebraMap_twistedCohomologyFunctor_point :
    Function.Bijective (algebraMap k[T;T⁻¹] ((twistedCohomologyFunctor k).obj (point k))) :=
  TwistedCohomology.bijective_algebraMap_point k

/-- Pullback along `X × 𝔸¹ → X` is bijective, for every smooth `X`. This is where the field and
characteristic hypotheses supply the rational scalars used in the homotopy of `thm:dr-homotopy`.

Blueprint: `lem:dr-ordinary-basic`, for the field `bijective_map_polynomialC`. -/
theorem bijective_twistedCohomologyFunctor_map_polynomialC {k : Type u} [Field k] [CharZero k]
    (A : SmoothAlg k) :
    Function.Bijective ((twistedCohomologyFunctor k).map (polynomialC A)) :=
  TwistedCohomology.bijective_map_C k A fun n ↦
    isUnit_iff_ne_zero.2 (Nat.cast_add_one_ne_zero n)

/-! ### Non-vacuity -/

variable (k) in
/-- The coefficient ring of the de Rham instance is nonzero: evaluation at `T = 1` maps it to `k`.

Blueprint: `thm:dr-instance`. -/
theorem nontrivial_coefficients [Nontrivial k] : Nontrivial k[T;T⁻¹] :=
  (laurentEvalOne k).toRingHom.domain_nontrivial

/-- The cohomology of the point is nonzero, so the de Rham instance is not a zero theory. Nothing
says that `C(A)` is nonzero for every `A`: it is zero for the zero algebra.

Blueprint: `thm:dr-instance`. -/
instance nontrivialObjPoint [Nontrivial k] :
    Nontrivial ((twistedCohomologyFunctor k).obj (point k)) :=
  inferInstanceAs (Nontrivial (TwistedCohomology k k))

end OrlikSolomon.DeRham
