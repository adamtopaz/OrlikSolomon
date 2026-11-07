/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.Cohomology.Logarithms
public import OrlikSolomon.DeRham.Instance
public import OrlikSolomon.Examples.DeRhamCohomology
public import OrlikSolomon.Examples.DeRhamMaps
public import OrlikSolomon.Presentation.Ordinary

/-!
# Regressions for the de Rham instance

The first part checks the instance itself, `OrlikSolomon.DeRham.ordinaryTheory k` of
`thm:dr-instance`: it is not a zero theory, since its point, its residue and its class `τ` are
nonzero, and it exists over `ℚ`.

The second part checks the inputs and computations used by `DeRham/Corollaries`, on the instance
itself. Generic lemmas about a value of `OrdinaryTheory` fire on it under `simp`. A homogeneous
class is `twistedClass w c`, the classes `logClass` among them, and the structure computes on it.
The forms that fail at `R = B` have no competing `k`-algebra structure here. It builds the
equivalence of `OS_k(𝒜)` with de Rham cohomology that `cor:dr-affine` asserts, with its value on
generators.

The third part is edge cases of `TwistedCohomology`: the sign is by cohomological degree and not by
weight, negative degrees and the zero algebra vanish, the point is nonzero when `k` is nonzero, and
affine-line invariance fails in characteristic two, so that the instance needs its hypothesis.

Blueprint: `def:dr-twisted-functor`, `lem:dr-ordinary-basic`, `def:dr-twisted-maps`,
`thm:dr-ordinary-localization`, `thm:dr-instance`.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open scoped TensorProduct LaurentPolynomial
open OrlikSolomon.SmoothAlg OrlikSolomon.DeRham

universe u v

namespace OrlikSolomon.DeRham.Examples

/-! ### The instance -/

section Instance

variable {k : Type u} [Field k] [CharZero k]

/-- The de Rham instance over `ℚ`. -/
example : OrdinaryTheory ℚ (laurentGrading ℚ) :=
  ordinaryTheory ℚ

/-- The coefficient ring is nonzero. -/
example : Nontrivial k[T;T⁻¹] :=
  nontrivial_coefficients k

/-- The cohomology of the point is nonzero. -/
example : (1 : (ordinaryTheory k).C.obj (point k)) ≠ 0 :=
  one_ne_zero

/-- The residue field of the instance is not zero: the class `[θ] T`, which is `[df / f] T` for the
equation `f` of a divisor pair, has residue one, with no sign.

Blueprint: `def:dr-twisted-maps`, with `lem:dr-exactness`. -/
theorem residue_twistedClass_theta (P : DivisorPair k) :
    (ordinaryTheory k).residue P
        (twistedClass 1 (Cohomology.mk (theta k P.eqn P.compl) (d_theta k P.eqn P.compl))) =
      1 := by
  rw [residue_twistedClass, residue_mk_theta_localization, sub_self, twistedClass_zero_one]

/-- The class `τ` of `lem:gm` is nonzero in the instance, because its residue is one in a nonzero
ring. So the theorems about arrangements say something about this instance. -/
theorem tau_ne_zero : (ordinaryTheory k).tau ≠ 0 := fun h ↦ by
  have h₁ := (ordinaryTheory k).stdResidue_tau
  rw [h, map_zero] at h₁
  exact zero_ne_one h₁

/-- The fields of the instance are those of `DeRham/Instance/Maps`, at the localization `P.compl`
of a divisor pair. -/
example (P : DivisorPair k) :
    Function.Exact ((ordinaryTheory k).residue P) ((ordinaryTheory k).gysin P) :=
  TwistedCohomology.exact_residue_gysin P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair

end Instance

/-! ### What the corollaries need -/

section Consumers

variable {k : Type u} [Field k] [CharZero k] {A D : SmoothAlg k}

/-- The generic lemmas about a theory apply to this one under `simp`, because the instance is a
`def`: with an `abbrev`, `simp` unfolds `T.C` and they do not fire. -/
example (P : DivisorPair k) (x : (ordinaryTheory k).C.obj P.ambient) :
    (ordinaryTheory k).residue P ((ordinaryTheory k).C.map P.j x) = 0 := by
  simp

example (u : Aˣ) : (ordinaryTheory k).logClass u * (ordinaryTheory k).logClass u = 0 := by
  simp

example (P : DivisorPair k) :
    (ordinaryTheory k).residue P ((ordinaryTheory k).logClass P.eqnUnit) = 1 := by
  simp

/-- Pullbacks of the theory act on the right factor, by `rfl`. -/
example (f : A ⟶ D) (w : ℤ) (c : Cohomology k A) :
    (ordinaryTheory k).C.map f (LaurentPolynomial.T w ⊗ₜ[k] c : TwistedCohomology k A) =
      (LaurentPolynomial.T w ⊗ₜ[k] Cohomology.map (algHom f) c : TwistedCohomology k D) :=
  rfl

/-- The product of the theory is that of the tensor product. -/
example (w v : ℤ) (c c' : Cohomology k A) :
    (LaurentPolynomial.T w ⊗ₜ[k] c : (ordinaryTheory k).C.obj A) *
        (LaurentPolynomial.T v ⊗ₜ[k] c') =
      (LaurentPolynomial.T (w + v) ⊗ₜ[k] (c * c') : TwistedCohomology k A) :=
  TwistedCohomology.T_tmul_mul_T_tmul w v c c'

/-- `simp` computes the structure on `twistedClass`, with no change of type. -/
example (f : A ⟶ D) (w v : ℤ) (c c' : Cohomology k A) :
    (ordinaryTheory k).C.map f (twistedClass w c * twistedClass v c') =
      twistedClass (w + v) (Cohomology.map (algHom f) (c * c')) := by
  simp

/-- The projection formula of the instance, for a class `c T` of bidegree `(1, 1)`, computed by
`simp` on `twistedClass`. -/
example (P : DivisorPair k) {c : Cohomology k P.compl} (hc : c ∈ Cohomology.grading k P.compl 1)
    (b : Cohomology k P.ambient) :
    (ordinaryTheory k).residue P
        (twistedClass 1 c * (ordinaryTheory k).C.map P.j (twistedClass 0 b)) =
      twistedClass 0
        (DeRham.residue P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair c *
          Cohomology.map (algHom P.i) b) := by
  rw [(ordinaryTheory k).residue_mul_map P (twistedClass_mem_grading 1 hc)]
  simp

/-- A homogeneous class of the theory is `twistedClass w c`. -/
example {p w : ℤ} {x : (ordinaryTheory k).C.obj A} (hx : x ∈ (ordinaryTheory k).grading A (p, w)) :
    ∃ c ∈ Cohomology.grading k A p, twistedClass w c = x :=
  mem_grading_ordinaryTheory_iff.1 hx

/-- A logarithmic class in the instance has bidegree `(1, 1)`, so it is `c T` for a class `c` of
degree one. `ordinaryTheory_logClass` identifies `c` with the de Rham logarithmic class. -/
theorem exists_logClass_eq (u : Aˣ) :
    ∃ c ∈ Cohomology.degree k A 1, twistedClass 1 c = (ordinaryTheory k).logClass u := by
  obtain ⟨c, hc, hcu⟩ :=
    mem_grading_ordinaryTheory_iff.1 ((ordinaryTheory k).logClass_mem_grading u)
  exact ⟨c, (Cohomology.grading_natCast (k := k) (A := A) 1) ▸ hc, hcu⟩

/-- Removing the power of `T` from a logarithmic class gives a class of degree one. -/
example (u : Aˣ) :
    TwistedCohomology.evalOne k A ((ordinaryTheory k).logClass u) ∈ Cohomology.grading k A 1 :=
  TwistedCohomology.evalOne_mem_of_mem_grading ((ordinaryTheory k).logClass_mem_grading u)

/-- The piece `H^{q, q}` of the theory is `H^q`, with the power of `T` removed. -/
example (A : SmoothAlg k) (q : ℕ) :
    Cohomology.degree k A q ≃ₗ[k] (ordinaryTheory k).grading A ((q : ℤ), (q : ℤ)) :=
  TwistedCohomology.degreeEquiv k A q q

/-- The `k`-algebra structure of the theory is the restriction of the one on the tensor product. -/
example (A : SmoothAlg k) :
    (ordinaryTheory k).algebra A = (inferInstance : Algebra k (TwistedCohomology k A)) :=
  rfl

/-- Homogeneous components are those of `TwistedCohomology.grading`. -/
example (A : SmoothAlg k) (i : ℤ × ℤ) (x : (ordinaryTheory k).C.obj A) :
    ((decompose ((ordinaryTheory k).grading A) x i : (ordinaryTheory k).grading A i) :
        (ordinaryTheory k).C.obj A) =
      (decompose (TwistedCohomology.grading k A) (x : TwistedCohomology k A) i :
        TwistedCohomology k A) :=
  rfl

/-- The form of an `R`-linear component that fails with an instance mismatch at `R = B`, as
`Cohomology/Axioms` explains. Here `R = k` and `B = k[T;T⁻¹]`, and there is no second `k`-algebra
structure. -/
example (P : DivisorPair k) {i j : ℤ × ℤ} (h : i + (2, 1) = j) :
    (ordinaryTheory k).grading P.closed i →ₗ[k] (ordinaryTheory k).grading P.ambient j :=
  ((ordinaryTheory k).isHomogeneousOfShift_gysin P).component h

/-- So does a `B`-linear map with its scalars restricted to `R`. -/
example (P : DivisorPair k) :
    (ordinaryTheory k).C.obj P.closed →ₗ[k] (ordinaryTheory k).C.obj P.ambient :=
  ((ordinaryTheory k).gysin P).restrictScalars k

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V)

/-- The shape of `cor:dr-affine`: the diagonal of the structure theorem for the instance, followed
by removal of the powers of `T`. -/
def osCohomologyEquiv : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology k (complement 𝒜) :=
  ((ordinaryTheory k).diagonalEquiv 𝒜).trans
    (TwistedCohomology.diagonalEquiv k (complement 𝒜)).symm

/-- The equivalence is the realization map, with the powers of `T` removed. -/
theorem osCohomologyEquiv_apply (x : OSAlgebra k 𝒜) :
    osCohomologyEquiv 𝒜 x =
      TwistedCohomology.evalOne k _ ((ordinaryTheory k).realizationOverR 𝒜 x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <|
    congrArg (TwistedCohomology.evalOne k _) ((ordinaryTheory k).coeAlgHom_diagonalEquiv x)

/-- On a generator, the equivalence is the logarithm of an equation, with the power of `T` removed.
`ordinaryTheory_logClass` identifies this value with the class `[df_H / f_H]`. -/
theorem osCohomologyEquiv_generator (H : 𝒜) :
    osCohomologyEquiv 𝒜 (OSAlgebra.generator k 𝒜 H) =
      TwistedCohomology.evalOne k _ ((ordinaryTheory k).logClass (equationUnit 𝒜 H)) := by
  rw [osCohomologyEquiv_apply, OrdinaryTheory.realizationOverR_generator]

/-- On a generator, the equivalence is the de Rham class `c` with `logClass (f_H) = c T`. -/
example (H : 𝒜) {c : Cohomology k (complement 𝒜)}
    (hc : twistedClass 1 c = (ordinaryTheory k).logClass (equationUnit 𝒜 H)) :
    osCohomologyEquiv 𝒜 (OSAlgebra.generator k 𝒜 H) = c := by
  rw [osCohomologyEquiv_generator, ← hc, evalOne_twistedClass]

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
