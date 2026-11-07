/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Instance.Basic
public import OrlikSolomon.DeRham.Instance.Maps

/-!
# The de Rham instance of the axioms

For a field `k` of characteristic zero, this file constructs `OrlikSolomon.DeRham.ordinaryTheory k`,
a value of `OrdinaryTheory k (laurentGrading k)`, with `R = k` and `B = k[T;T⁻¹]`. Its cohomology is
`C(A) = k[T;T⁻¹] ⊗[k] H^•_dR(A/k)`, with `H^p_dR(A/k) T^w` in bidegree `(p, w)`. Its Gysin map and
residue are those of `DeRham/Maps` multiplied by `T` and by `T⁻¹`. Every field is proved, and none
is weakened. The coefficient ring and the cohomology of the point are nonzero, so this is not a zero
theory.

## Main definitions

* `OrlikSolomon.DeRham.ordinaryTheory k`: the de Rham instance.
* `OrlikSolomon.DeRham.twistedClass w c`: the class `c T^w` of `(ordinaryTheory k).C.obj A`, for a
  de Rham class `c`.

## Main results

* `OrlikSolomon.DeRham.nontrivial_coefficients` and the instance
  `OrlikSolomon.DeRham.nontrivialOrdinaryTheoryObjPoint`: nonvanishing.
* `OrlikSolomon.DeRham.mem_grading_ordinaryTheory_iff`: a class of bidegree `(p, w)` is
  `twistedClass w c` for some `c ∈ H^p`, and `twistedClass_inj` says that `c` is unique.
* `OrlikSolomon.DeRham.map_twistedClass`, `twistedClass_mul_twistedClass`,
  `gysin_twistedClass`, `residue_twistedClass`, `stdResidue_twistedClass`, `evalOne_twistedClass`:
  the structure, computed on `twistedClass w c`.

## Where each field comes from

| Fields | Here |
| --- | --- |
| up to `bijective_map_polynomialC` | `DeRham/Instance/Basic` |
| `gysin`, `residue` | `TwistedCohomology.gysin`, `TwistedCohomology.residue` |
| the shifts, exactness, naturality, the projection formula | `DeRham/Instance/Maps` |

The hypotheses that `DeRham/Maps` needs are supplied by a divisor pair: `P.isSmoothPrincipalPair`,
with `P.compl` as the localization, and `F.isPairHom` for a morphism `F` of divisor pairs. The
hypothesis that positive integers are units is `isUnit_natCast_add_one`, and it is the only place
where the field and the characteristic are used.

## Computing in the instance

`ordinaryTheory` is a `def`, so that the generic lemmas about a value `T` of `OrdinaryTheory`, which
mention `T.C`, fire on it under `simp`. With an `abbrev`, `simp` would unfold `T.C` and they would
not. The price is that `(ordinaryTheory k).C.obj A` is `TwistedCohomology k A` only at default
transparency, so that `rw` and `simp` do not see the tensor product in it.

So compute with `twistedClass w c`, which is typed in `(ordinaryTheory k).C.obj A`: the lemmas
below say what the structure does to it, and `simp` uses them with no change of type. It is
`T w ⊗ₜ c` by `rfl` (`twistedClass_apply`), and the fields are those of `DeRham/Instance/Maps` by
`rfl` (`ordinaryTheory_gysin` and the lemmas after it), for statements that are easier to prove on
`TwistedCohomology k A`; cross between the two once, with `exact` or `change`.

## Blueprint

`def:dr-twisted-maps`, `thm:dr-ordinary-localization` (with `DeRham/Instance/Maps`), and
`thm:dr-instance`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial (T)
open OrlikSolomon.SmoothAlg OrlikSolomon.DivisorPair

universe u

namespace OrlikSolomon.DeRham

variable (k : Type u) [Field k] [CharZero k]

/-- In a field of characteristic zero, every positive integer is a unit. This is the hypothesis of
the homotopy of `thm:dr-homotopy` and of the comparison of `thm:dr-comparison`, on which the residue
depends. -/
theorem isUnit_natCast_add_one (n : ℕ) : IsUnit (n + 1 : k) :=
  isUnit_iff_ne_zero.2 (Nat.cast_add_one_ne_zero n)

/-- **The de Rham instance of the axioms.** For a field `k` of characteristic zero, algebraic de
Rham cohomology with Laurent coefficients is an ordinary cohomology theory, with `R = k`,
`B = k[T;T⁻¹]` and `ℬ w = k T^w`:

* `C(A) = k[T;T⁻¹] ⊗[k] H^•_dR(A/k)`, with `H^p_dR(A/k) T^w` in bidegree `(p, w)`, and pullbacks
  `1 ⊗ H(φ)`;
* the Gysin map is `T^w y ↦ T^(w+1) G(y)` and the residue is `T^w x ↦ T^(w-1) r(x)`, for the Gysin
  map `G` and the residue `r` of the smooth divisor of a divisor pair.

Every field holds for every smooth algebra and every divisor pair, with no hypothesis about
arrangements, connectedness, nonemptiness, or flatness of morphisms. The coefficient ring and the
cohomology of the point are nonzero: `nontrivial_coefficients` and
`nontrivialOrdinaryTheoryObjPoint`.

This is a `def` rather than an `abbrev`, so that the generic lemmas about `T.C` fire on it: see the
module docstring.

Blueprint: `thm:dr-instance`. -/
def ordinaryTheory : OrdinaryTheory.{u, u, u, u} k (laurentGrading k) where
  bijective_algebraMap_gradeZero := bijective_algebraMap_laurentGrading_zero k
  C := twistedCohomologyFunctor k
  grading A := TwistedCohomology.grading k A
  gradedAlgebra A := TwistedCohomology.gradedAlgebraGrading k A
  algebraMap_mem_grading _ _ _ hb := TwistedCohomology.algebraMap_mem_grading hb
  isHomogeneousOfShift_map := isHomogeneousOfShift_twistedCohomologyFunctor_map
  isGradedCommutative A := TwistedCohomology.isGradedCommutative_grading k A
  bijective_algebraMap_point := bijective_algebraMap_twistedCohomologyFunctor_point k
  eq_zero_of_mem_grading_point hp _ hx := TwistedCohomology.eq_zero_of_mem_grading_point hp hx
  bijective_map_polynomialC := bijective_twistedCohomologyFunctor_map_polynomialC
  gysin P := TwistedCohomology.gysin P.compl P.isSmoothPrincipalPair
  residue P := TwistedCohomology.residue P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair
  isHomogeneousOfShift_gysin P :=
    TwistedCohomology.isHomogeneousOfShift_gysin P.compl P.isSmoothPrincipalPair
  isHomogeneousOfShift_residue P :=
    TwistedCohomology.isHomogeneousOfShift_residue P.compl _ P.isSmoothPrincipalPair
  exact_gysin_map P :=
    TwistedCohomology.exact_gysin_map P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair
  exact_map_residue P := TwistedCohomology.exact_map_residue P.compl _ P.isSmoothPrincipalPair
  exact_residue_gysin P := TwistedCohomology.exact_residue_gysin P.compl _ P.isSmoothPrincipalPair
  gysin_map F x := TwistedCohomology.gysin_map F.isPairHom _ _ x
  residue_map F x := TwistedCohomology.residue_map _ F.isPairHom _ _ x
  residue_mul_map P _ _ β := TwistedCohomology.residue_mul_map _ P.isSmoothPrincipalPair _ β

/-- The cohomology of the point in the de Rham instance is nonzero, so the instance is not a zero
theory. With `nontrivial_coefficients`, this is the nonvanishing in `thm:dr-instance`. Nothing says
that `C(A)` is nonzero for every `A`: it is zero for the zero algebra.

Blueprint: `thm:dr-instance`. -/
instance nontrivialOrdinaryTheoryObjPoint : Nontrivial ((ordinaryTheory k).C.obj (point k)) :=
  nontrivialObjPoint

variable {k}

/-! ### The fields, by definition -/

section Fields

/-- The functor of the instance. Not a `simp` lemma: see the module docstring. -/
theorem ordinaryTheory_C : (ordinaryTheory k).C = twistedCohomologyFunctor k :=
  rfl

/-- The bigrading of the instance is `TwistedCohomology.grading`, with `H^p T^w` in bidegree
`(p, w)`. -/
theorem ordinaryTheory_grading (A : SmoothAlg k) :
    (ordinaryTheory k).grading A = TwistedCohomology.grading k A :=
  rfl

/-- The Gysin map of the instance at a divisor pair is the twisted Gysin map at its open part. -/
theorem ordinaryTheory_gysin (P : DivisorPair k) :
    (ordinaryTheory k).gysin P = TwistedCohomology.gysin P.compl P.isSmoothPrincipalPair :=
  rfl

/-- The residue of the instance at a divisor pair is the twisted residue at its open part. -/
theorem ordinaryTheory_residue (P : DivisorPair k) :
    (ordinaryTheory k).residue P =
      TwistedCohomology.residue P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair :=
  rfl

/-- The pullbacks of the instance are `1 ⊗ H(φ)`. -/
theorem ordinaryTheory_map_apply {A D : SmoothAlg k} (f : A ⟶ D) (x : TwistedCohomology k A) :
    (ordinaryTheory k).C.map f x = TwistedCohomology.map (algHom f) x :=
  rfl

end Fields

/-! ### Computing with `twistedClass` -/

section TwistedClass

variable {A D : SmoothAlg k}

/-- The class `c T^w` of `C(A) = k[T;T⁻¹] ⊗[k] H^•_dR(A/k)` in the de Rham instance, for a de Rham
class `c`. A class of bidegree `(p, w)` is `twistedClass w c` for a unique `c ∈ H^p`, by
`mem_grading_ordinaryTheory_iff` and `twistedClass_inj`. It is `T w ⊗ₜ c`, by `twistedClass_apply`,
and it is typed in `(ordinaryTheory k).C.obj A`, so that `simp` computes the structure on it. -/
def twistedClass (w : ℤ) : Cohomology k A →ₗ[k] (ordinaryTheory k).C.obj A :=
  TensorProduct.mk k k[T;T⁻¹] (Cohomology k A) (T w)

/-- The class `c T^w` is `T w ⊗ₜ c`. Not a `simp` lemma, since its two sides have different types:
see the module docstring. -/
theorem twistedClass_apply (w : ℤ) (c : Cohomology k A) :
    twistedClass w c = (T w ⊗ₜ[k] c : TwistedCohomology k A) :=
  rfl

/-- **A class of bidegree `(p, w)` is `c T^w`**, with `c ∈ H^p`. -/
theorem mem_grading_ordinaryTheory_iff {p w : ℤ} {x : (ordinaryTheory k).C.obj A} :
    x ∈ (ordinaryTheory k).grading A (p, w) ↔
      ∃ c ∈ Cohomology.grading k A p, twistedClass w c = x :=
  TwistedCohomology.mem_grading_iff

@[simp]
theorem twistedClass_mem_grading_iff {p w : ℤ} {c : Cohomology k A} :
    twistedClass w c ∈ (ordinaryTheory k).grading A (p, w) ↔ c ∈ Cohomology.grading k A p :=
  TwistedCohomology.T_tmul_mem_grading_iff

theorem twistedClass_mem_grading {p : ℤ} (w : ℤ) {c : Cohomology k A}
    (hc : c ∈ Cohomology.grading k A p) : twistedClass w c ∈ (ordinaryTheory k).grading A (p, w) :=
  twistedClass_mem_grading_iff.2 hc

/-- In a natural degree, `c T^w` has bidegree `(n, w)` exactly when `c ∈ H^n`. -/
theorem twistedClass_mem_grading_natCast_iff {n : ℕ} {w : ℤ} {c : Cohomology k A} :
    twistedClass w c ∈ (ordinaryTheory k).grading A ((n : ℤ), w) ↔ c ∈ Cohomology.degree k A n :=
  TwistedCohomology.T_tmul_mem_grading_natCast_iff

@[simp]
theorem twistedClass_inj {w : ℤ} {c c' : Cohomology k A} :
    twistedClass w c = twistedClass w c' ↔ c = c' :=
  TwistedCohomology.T_tmul_inj

@[simp]
theorem twistedClass_eq_zero {w : ℤ} {c : Cohomology k A} : twistedClass w c = 0 ↔ c = 0 :=
  TwistedCohomology.T_tmul_eq_zero

/-- Removing the power of `T` from `c T^w` gives `c`. -/
@[simp]
theorem evalOne_twistedClass (w : ℤ) (c : Cohomology k A) :
    TwistedCohomology.evalOne k A (twistedClass w c) = c :=
  TwistedCohomology.evalOne_T_tmul w c

/-- Pullbacks act on the de Rham class. -/
@[simp]
theorem map_twistedClass (f : A ⟶ D) (w : ℤ) (c : Cohomology k A) :
    (ordinaryTheory k).C.map f (twistedClass w c) = twistedClass w (Cohomology.map (algHom f) c) :=
  rfl

/-- Weights add and de Rham classes multiply. -/
@[simp]
theorem twistedClass_mul_twistedClass (w v : ℤ) (c c' : Cohomology k A) :
    twistedClass w c * twistedClass v c' = twistedClass (w + v) (c * c') :=
  TwistedCohomology.T_tmul_mul_T_tmul w v c c'

/-- The unit is `1 T^0`. -/
@[simp]
theorem twistedClass_zero_one : twistedClass 0 (1 : Cohomology k A) = 1 := by
  rw [twistedClass_apply, LaurentPolynomial.T_zero]
  rfl

/-- The image of `T^w` under `B → C(A)` is `1 T^w`. -/
theorem algebraMap_T (w : ℤ) :
    algebraMap k[T;T⁻¹] ((ordinaryTheory k).C.obj A) (T w) = twistedClass w 1 :=
  rfl

/-- The coefficient `T^v` adds `v` to the weight. -/
@[simp]
theorem T_smul_twistedClass (v w : ℤ) (c : Cohomology k A) :
    (T v : k[T;T⁻¹]) • twistedClass w c = twistedClass (v + w) c :=
  TwistedCohomology.T_smul_T_tmul v w c

/-- **The Gysin map of the instance**: `g(c T^w) = G(c) T^(w+1)`.

Blueprint: `def:dr-twisted-maps`. -/
@[simp]
theorem gysin_twistedClass (P : DivisorPair k) (w : ℤ) (c : Cohomology k P.closed) :
    (ordinaryTheory k).gysin P (twistedClass w c) =
      twistedClass (w + 1) (DeRham.gysin P.compl P.isSmoothPrincipalPair c) :=
  TwistedCohomology.gysin_T_tmul _ w c

/-- **The residue of the instance**: `R(c T^w) = r(c) T^(w-1)`.

Blueprint: `def:dr-twisted-maps`. -/
@[simp]
theorem residue_twistedClass (P : DivisorPair k) (w : ℤ) (c : Cohomology k P.compl) :
    (ordinaryTheory k).residue P (twistedClass w c) =
      twistedClass (w - 1)
        (DeRham.residue P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair c) :=
  TwistedCohomology.residue_T_tmul _ _ w c

/-- The residue of the standard pair of `A`, typed by `laurent A` as `OrdinaryTheory.stdResidue`
is. -/
@[simp]
theorem stdResidue_twistedClass (A : SmoothAlg k) (w : ℤ) (c : Cohomology k (laurent A)) :
    (ordinaryTheory k).stdResidue A (twistedClass w c) =
      twistedClass (w - 1) (DeRham.residue (standardPair A).compl (isUnit_natCast_add_one k)
        (standardPair A).isSmoothPrincipalPair c) :=
  residue_twistedClass (standardPair A) w c

/-- The Gysin map of the standard pair of `A`, typed by `polynomial A` as `OrdinaryTheory.stdGysin`
is. -/
@[simp]
theorem stdGysin_twistedClass (A : SmoothAlg k) (w : ℤ) (c : Cohomology k A) :
    (ordinaryTheory k).stdGysin A (twistedClass w c) =
      (twistedClass (w + 1)
        (DeRham.gysin (standardPair A).compl (standardPair A).isSmoothPrincipalPair c) :
          (ordinaryTheory k).C.obj (polynomial A)) :=
  gysin_twistedClass (standardPair A) w c

end TwistedClass

end OrlikSolomon.DeRham
