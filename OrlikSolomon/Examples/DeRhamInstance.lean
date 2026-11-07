/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.Cohomology.Logarithms
public import OrlikSolomon.DeRham.Instance.Basic
public import OrlikSolomon.Examples.DeRhamCohomology
public import OrlikSolomon.Presentation.Ordinary

/-!
# Regressions for the first fields of the de Rham instance

The first part tests the shape of `lem:dr-ordinary-basic`. `RemainingFields k` collects the fields
of `OrdinaryTheory` from `gysin` on, stated exactly as in the structure, and
`RemainingFields.theory` fills the whole structure with them and with the fields of
`DeRham/Instance/Basic`. So each of those has the exact shape of its field. This is a test: nothing
in the library takes `RemainingFields` as a hypothesis, and `DeRham/Instance` will fill these fields
itself.

The second part is what the corollaries of the instance need, on a value of the structure. It reads
a homogeneous class as `T w ⊗ₜ c`, the classes `logClass` among them. It shows that there is no
competing `k`-algebra structure, in the forms that fail at `R = B`. It builds the equivalence of
`OS_k(𝒜)` with de Rham cohomology that `cor:dr-affine` asserts, with its value on generators.

The third part is edge cases: the sign is by cohomological degree and not by weight, negative
degrees and the zero algebra vanish, the point is nonzero, and affine-line invariance fails in
characteristic two, so that its hypothesis is needed.

Blueprint: `def:dr-twisted-functor`, `lem:dr-ordinary-basic`.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open scoped TensorProduct LaurentPolynomial
open OrlikSolomon.SmoothAlg OrlikSolomon.DeRham

universe u v

namespace OrlikSolomon.DeRham.Examples

section Shape

/-- The fields of `OrdinaryTheory` that `DeRham/Instance/Basic` does not fill, stated as in the
structure, for the functor of the de Rham instance. This is only a test of shape. -/
structure RemainingFields (k : Type u) [Field k] [CharZero k] where
  /-- The field `gysin`. -/
  gysin (P : DivisorPair k) :
    (twistedCohomologyFunctor k).obj P.closed →ₗ[k[T;T⁻¹]]
      (twistedCohomologyFunctor k).obj P.ambient
  /-- The field `residue`. -/
  residue (P : DivisorPair k) :
    (twistedCohomologyFunctor k).obj P.compl →ₗ[k[T;T⁻¹]]
      (twistedCohomologyFunctor k).obj P.closed
  isHomogeneousOfShift_gysin (P : DivisorPair k) :
    IsHomogeneousOfShift (TwistedCohomology.grading k P.closed)
      (TwistedCohomology.grading k P.ambient) (2, 1) (gysin P)
  isHomogeneousOfShift_residue (P : DivisorPair k) :
    IsHomogeneousOfShift (TwistedCohomology.grading k P.compl)
      (TwistedCohomology.grading k P.closed) (-1, -1) (residue P)
  exact_gysin_map (P : DivisorPair k) :
    Function.Exact (gysin P) ((twistedCohomologyFunctor k).map P.j)
  exact_map_residue (P : DivisorPair k) :
    Function.Exact ((twistedCohomologyFunctor k).map P.j) (residue P)
  exact_residue_gysin (P : DivisorPair k) : Function.Exact (residue P) (gysin P)
  gysin_map {P Q : DivisorPair k} (f : P ⟶ Q) (x : (twistedCohomologyFunctor k).obj P.closed) :
    gysin Q ((twistedCohomologyFunctor k).map f.closed x) =
      (twistedCohomologyFunctor k).map f.ambient (gysin P x)
  residue_map {P Q : DivisorPair k} (f : P ⟶ Q) (x : (twistedCohomologyFunctor k).obj P.compl) :
    residue Q ((twistedCohomologyFunctor k).map f.compl x) =
      (twistedCohomologyFunctor k).map f.closed (residue P x)
  residue_mul_map (P : DivisorPair k) {α : (twistedCohomologyFunctor k).obj P.compl}
    (hα : α ∈ TwistedCohomology.grading k P.compl (1, 1))
    (β : (twistedCohomologyFunctor k).obj P.ambient) :
    residue P (α * (twistedCohomologyFunctor k).map P.j β) =
      residue P α * (twistedCohomologyFunctor k).map P.i β

variable {k : Type u} [Field k] [CharZero k]

/-- The structure `OrdinaryTheory`, with every field of `lem:dr-ordinary-basic` filled by
`DeRham/Instance/Basic`. The fields `algebra` and `isScalarTower` are found by instance search. -/
def RemainingFields.theory (S : RemainingFields k) : OrdinaryTheory k (laurentGrading k) where
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
  gysin := S.gysin
  residue := S.residue
  isHomogeneousOfShift_gysin := S.isHomogeneousOfShift_gysin
  isHomogeneousOfShift_residue := S.isHomogeneousOfShift_residue
  exact_gysin_map := S.exact_gysin_map
  exact_map_residue := S.exact_map_residue
  exact_residue_gysin := S.exact_residue_gysin
  gysin_map := S.gysin_map
  residue_map := S.residue_map
  residue_mul_map := S.residue_mul_map

end Shape

/-! ### What the corollaries need -/

section Consumers

variable {k : Type u} [Field k] [CharZero k] (S : RemainingFields k) {A D : SmoothAlg k}

/-- The generic lemmas about a theory apply to this one under `simp`, because a value of the
structure is a `def`: with an `abbrev`, `simp` unfolds `T.C` and they do not fire. -/
example (P : DivisorPair k) (x : S.theory.C.obj P.ambient) :
    S.theory.residue P (S.theory.C.map P.j x) = 0 := by
  simp

example (u : Aˣ) : S.theory.logClass u * S.theory.logClass u = 0 := by
  simp

/-- Pullbacks of the theory act on the right factor, by `rfl`. -/
example (f : A ⟶ D) (w : ℤ) (c : Cohomology k A) :
    S.theory.C.map f (LaurentPolynomial.T w ⊗ₜ[k] c : TwistedCohomology k A) =
      (LaurentPolynomial.T w ⊗ₜ[k] Cohomology.map (algHom f) c : TwistedCohomology k D) :=
  rfl

/-- The product of the theory is that of the tensor product. -/
example (w v : ℤ) (c c' : Cohomology k A) :
    (LaurentPolynomial.T w ⊗ₜ[k] c : S.theory.C.obj A) * (LaurentPolynomial.T v ⊗ₜ[k] c') =
      (LaurentPolynomial.T (w + v) ⊗ₜ[k] (c * c') : TwistedCohomology k A) :=
  TwistedCohomology.T_tmul_mul_T_tmul w v c c'

/-- A homogeneous class of the theory is `T w ⊗ₜ c`. -/
example {p w : ℤ} {x : S.theory.C.obj A} (hx : x ∈ S.theory.grading A (p, w)) :
    ∃ c ∈ Cohomology.grading k A p, (LaurentPolynomial.T w ⊗ₜ[k] c : TwistedCohomology k A) = x :=
  TwistedCohomology.mem_grading_iff.1 hx

/-- The logarithmic class of a unit has the form that `lem:dr-tau` makes precise. -/
theorem exists_logClass_eq (u : Aˣ) :
    ∃ c ∈ Cohomology.degree k A 1, (LaurentPolynomial.T 1 ⊗ₜ[k] c : TwistedCohomology k A) =
      S.theory.logClass u := by
  have h := TwistedCohomology.mem_grading_iff.1 (S.theory.logClass_mem_grading u)
  obtain ⟨c, hc, hcu⟩ := h
  exact ⟨c, (Cohomology.grading_natCast (k := k) (A := A) 1) ▸ hc, hcu⟩

/-- Removing the power of `T` from a logarithmic class gives a class of degree one. -/
example (u : Aˣ) :
    TwistedCohomology.evalOne k A (S.theory.logClass u) ∈ Cohomology.grading k A 1 :=
  TwistedCohomology.evalOne_mem_of_mem_grading (S.theory.logClass_mem_grading u)

/-- The piece `H^{q, q}` of the theory is `H^q`, with the power of `T` removed. -/
example (A : SmoothAlg k) (q : ℕ) :
    Cohomology.degree k A q ≃ₗ[k] S.theory.grading A ((q : ℤ), (q : ℤ)) :=
  TwistedCohomology.degreeEquiv k A q q

/-- The `k`-algebra structure of the theory is the restriction of the one on the tensor product. -/
example (A : SmoothAlg k) :
    S.theory.algebra A = (inferInstance : Algebra k (TwistedCohomology k A)) :=
  rfl

/-- Homogeneous components are those of `TwistedCohomology.grading`. -/
example (A : SmoothAlg k) (i : ℤ × ℤ) (x : S.theory.C.obj A) :
    ((decompose (S.theory.grading A) x i : S.theory.grading A i) : S.theory.C.obj A) =
      (decompose (TwistedCohomology.grading k A) (x : TwistedCohomology k A) i :
        TwistedCohomology k A) :=
  rfl

/-- The form of an `R`-linear component that fails with an instance mismatch at `R = B`, as
`Cohomology/Axioms` explains. Here `R = k` and `B = k[T;T⁻¹]`, and there is no second `k`-algebra
structure. -/
example (P : DivisorPair k) {i j : ℤ × ℤ} (h : i + (2, 1) = j) :
    S.theory.grading P.closed i →ₗ[k] S.theory.grading P.ambient j :=
  (S.theory.isHomogeneousOfShift_gysin P).component h

/-- So does a `B`-linear map with its scalars restricted to `R`. -/
example (P : DivisorPair k) : S.theory.C.obj P.closed →ₗ[k] S.theory.C.obj P.ambient :=
  (S.theory.gysin P).restrictScalars k

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V)

/-- The shape of `cor:dr-affine`: the diagonal of the structure theorem, followed by the removal of
the powers of `T`. -/
def osCohomologyEquiv : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology k (complement 𝒜) :=
  (S.theory.diagonalEquiv 𝒜).trans (TwistedCohomology.diagonalEquiv k (complement 𝒜)).symm

/-- The equivalence is the realization map, with the powers of `T` removed. -/
theorem osCohomologyEquiv_apply (x : OSAlgebra k 𝒜) :
    osCohomologyEquiv S 𝒜 x = TwistedCohomology.evalOne k _ (S.theory.realizationOverR 𝒜 x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <|
    congrArg (TwistedCohomology.evalOne k _) (S.theory.coeAlgHom_diagonalEquiv x)

/-- On a generator, the equivalence is the logarithm of an equation, with the power of `T` removed.
By `lem:dr-tau`, this is the class `[df_H / f_H]`. -/
theorem osCohomologyEquiv_generator (H : 𝒜) :
    osCohomologyEquiv S 𝒜 (OSAlgebra.generator k 𝒜 H) =
      TwistedCohomology.evalOne k _ (S.theory.logClass (equationUnit 𝒜 H)) := by
  rw [osCohomologyEquiv_apply, OrdinaryTheory.realizationOverR_generator]

end Consumers

/-! ### Edge cases -/

section EdgeCases

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

/-- The sign is by cohomological degree: classes of bidegrees `(2, 1)` and `(1, 1)` commute,
although both weights are odd. -/
example {x y : TwistedCohomology k A} (hx : x ∈ TwistedCohomology.grading k A (2, 1))
    (hy : y ∈ TwistedCohomology.grading k A (1, 1)) : x * y = y * x := by
  simpa [Int.negOnePow_even 2 even_two] using
    TwistedCohomology.isGradedCommutative_grading k A hx hy

/-- Classes of odd cohomological degree anticommute, although both weights are even. There is no
hypothesis on `2`. -/
example {x y : TwistedCohomology k A} (hx : x ∈ TwistedCohomology.grading k A (1, 0))
    (hy : y ∈ TwistedCohomology.grading k A (1, 2)) : x * y = -(y * x) :=
  (TwistedCohomology.isGradedCommutative_grading k A).mul_eq_neg_of_odd (by simp) (by simp) hx hy

/-- Negative cohomological degrees vanish, in every weight. -/
example (w : ℤ) : TwistedCohomology.grading k A (-1, w) = ⊥ :=
  TwistedCohomology.grading_of_neg (by simp) w

/-- `C(k)` is nonzero for any nonzero ring `k`, including `ℤ` and `ZMod 2`. -/
example [Nontrivial k] : Nontrivial ((twistedCohomologyFunctor k).obj (point k)) :=
  inferInstance

/-- `C(A)` is zero for the zero algebra: `thm:dr-instance` does not claim that it is always nonzero.
-/
example : Subsingleton ((twistedCohomologyFunctor k).obj (zero k)) :=
  inferInstanceAs (Subsingleton (TwistedCohomology k (zero k)))

/-- The map `C(A) → C(A[X])` is not surjective over `ZMod 2`, so `bijective_map_C` needs its
hypothesis and the instance is correctly restricted to characteristic zero. -/
theorem not_surjective_twisted_map_C_of_charTwo :
    ¬ Function.Surjective (TwistedCohomology.map
      (Polynomial.CAlgHom : ZMod 2 →ₐ[ZMod 2] Polynomial (ZMod 2))) := fun h ↦
  not_surjective_map_C_of_charTwo fun c ↦ by
    obtain ⟨x, hx⟩ := h ((1 : (ZMod 2)[T;T⁻¹]) ⊗ₜ[ZMod 2] c)
    exact ⟨TwistedCohomology.evalOne _ _ x, by
      rw [← TwistedCohomology.evalOne_map, hx, TwistedCohomology.evalOne_one_tmul]⟩

end EdgeCases

end OrlikSolomon.DeRham.Examples
