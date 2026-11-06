/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.SmoothPair
public import Mathlib.RingTheory.Smooth.Pi
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Algebra.Polynomial.Div

/-!
# Smooth principal pairs with disconnected or zero algebras

For `A = k × k[X]` and `f = (1,X)`, the divisor is smooth and the conormal sequence
splits, but no derivation takes `f` to one in `A`. The global normal derivation theorem
still applies: the required normalization is only modulo `f`.
Unit equations and the actual zero algebra also satisfy the theorem.

Blueprint: `lem:dr-conormal`, `lem:dr-normal-derivation`, `prop:dr-product-example`,
`prop:dr-unit-example` and the one-form part of `prop:dr-zero-example`.
-/

@[expose] public section

noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

namespace OrlikSolomon.Sanity

section Disconnected
variable (k : Type*) [CommRing k]

/-- An equation whose divisor is supported on the polynomial component of `k × k[X]`. -/
def productPolynomialEquation : k × k[X] := (1, X)

private abbrev components : Bool → Type _ := fun b => cond b k k[X]
private instance (b : Bool) : CommRing (components k b) := by
  cases b
  · exact inferInstanceAs (CommRing k[X])
  · exact inferInstanceAs (CommRing k)
private instance (b : Bool) : Algebra k (components k b) := by
  cases b
  · exact inferInstanceAs (Algebra k k[X])
  · exact inferInstanceAs (Algebra k k)
private instance (b : Bool) : Algebra.FormallySmooth k (components k b) := by
  cases b
  · exact inferInstanceAs (Algebra.FormallySmooth k k[X])
  · exact inferInstanceAs (Algebra.FormallySmooth k k)

private def productEquiv : (∀ b, components k b) ≃ₐ[k] k × k[X] where
  toFun x := (x true, x false)
  invFun x b := by
    cases b
    · exact x.2
    · exact x.1
  left_inv x := by funext b; cases b <;> rfl
  right_inv x := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The disconnected ambient algebra is formally smooth. -/
instance productPolynomial_formallySmooth : Algebra.FormallySmooth k (k × k[X]) :=
  Algebra.FormallySmooth.of_equiv (productEquiv k)

/-- The equation `(1,X)` is regular despite the disconnected ambient algebra. -/
theorem productPolynomialEquation_regular :
    productPolynomialEquation k ∈ nonZeroDivisors (k × k[X]) := by
  rw [mem_nonZeroDivisors_iff]
  suffices h : ∀ x : k × k[X], productPolynomialEquation k * x = 0 → x = 0 by
    exact ⟨h, fun x hx ↦ h x (by simpa only [mul_comm] using hx)⟩
  intro x h
  apply Prod.ext
  · simpa [productPolynomialEquation] using congrArg Prod.fst h
  · have hx : X * x.2 = (0 : k[X]) := by
      simpa [productPolynomialEquation] using congrArg Prod.snd h
    exact (mem_nonZeroDivisors_iff.mp (Polynomial.X_mem_nonZeroDivisors (R := k))).1 _ hx

private def quotientMap : k × k[X] →ₐ[k] k :=
  (Polynomial.aeval (0 : k)).comp (AlgHom.snd k k k[X])

private theorem quotientMap_surjective : Function.Surjective (quotientMap k) := by
  intro r
  exact ⟨(0, C r), by simp [quotientMap]⟩

private theorem quotientMap_ker :
    RingHom.ker (quotientMap k).toRingHom = Ideal.span {productPolynomialEquation k} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hx' : x.2.coeff 0 = 0 := by
      change Polynomial.eval 0 x.2 = 0 at hx
      rwa [← Polynomial.coeff_zero_eq_eval_zero] at hx
    obtain ⟨p, hp⟩ := Polynomial.X_dvd_iff.2 hx'
    exact ⟨(x.1, p), by ext <;> simp [productPolynomialEquation, hp]⟩
  · rintro ⟨a, rfl⟩
    simp [quotientMap, productPolynomialEquation]

/-- The divisor of `(1,X)` is the point `Spec k`. -/
@[no_expose] def productPolynomialQuotientEquiv :
    ((k × k[X]) ⧸ Ideal.span {productPolynomialEquation k}) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (quotientMap_ker k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := quotientMap k) (quotientMap_surjective k))

/-- The divisor quotient of the disconnected pair is formally smooth. -/
instance productPolynomialQuotient_formallySmooth :
    Algebra.FormallySmooth k ((k × k[X]) ⧸ Ideal.span {productPolynomialEquation k}) :=
  Algebra.FormallySmooth.of_equiv (productPolynomialQuotientEquiv k).symm

/-- The explicit normal derivation is zero on `k` and the polynomial derivative on `k[X]`. -/
def productPolynomialNormal : Derivation k (k × k[X]) (k × k[X]) where
  toLinearMap := (0 : (k × k[X]) →ₗ[k] k).prod
    (Polynomial.derivative.comp (LinearMap.snd k k k[X]))
  map_one_eq_zero' := by ext <;> simp
  leibniz' a b := by
    ext
    · simp
    · simp [Polynomial.derivative_mul, mul_comm, add_comm]

/-- The explicit derivation is normal modulo `(1,X)`, with correction term `(-1,0)`. -/
theorem productPolynomialNormal_equation :
    productPolynomialNormal k (productPolynomialEquation k) =
      1 + productPolynomialEquation k * (-1, 0) := by
  ext <;> simp [productPolynomialNormal, productPolynomialEquation]

/-- The conormal functional really takes `df mod f` to one on this disconnected pair. -/
theorem productPolynomial_conormalFunctional_df :
    DeRham.conormalFunctional (k := k) _ (productPolynomialEquation_regular k)
      (1 ⊗ₜ D k (k × k[X]) (productPolynomialEquation k)) = 1 :=
  DeRham.conormalFunctional_df (k := k) _ _

/-- The conormal splitting takes `df mod f` to the first basis vector. -/
theorem productPolynomial_splitConormalSequence_df :
    DeRham.splitConormalSequence (k := k) _ (productPolynomialEquation_regular k)
      (1 ⊗ₜ D k (k × k[X]) (productPolynomialEquation k)) = (1, 0) := by
  simp [DeRham.splitConormalSequence_apply, mapBaseChange_tmul, map_D]

/-- The general normal-derivation theorem applies to the actual disconnected pair. -/
theorem productPolynomial_exists_normalDerivation_modulo :
    ∃ (v : Derivation k (k × k[X]) (k × k[X])) (h : k × k[X]),
      v (productPolynomialEquation k) = 1 + productPolynomialEquation k * h :=
  DeRham.exists_normalDerivation_modulo (k := k) _ (productPolynomialEquation_regular k)

/-- No derivation can take `(1,X)` to one on both components of the ambient algebra. -/
theorem productPolynomial_no_global_normal [Nontrivial k] (v : Derivation k (k × k[X]) (k × k[X])) :
    v (productPolynomialEquation k) ≠ 1 := by
  have he : (v ((1 : k), (0 : k[X]))).1 = 0 := by
    have h := congrArg Prod.fst (v.leibniz ((1 : k), (0 : k[X])) (1, 0))
    simp only [Prod.mk_mul_mk, mul_one, mul_zero, Prod.fst_add, Prod.fst_mul,
      smul_eq_mul, one_mul] at h
    exact add_left_cancel (show (v (1, 0)).1 + (v (1, 0)).1 = (v (1, 0)).1 + 0 by
      simpa only [add_zero] using h.symm)
  have hzero : (v (productPolynomialEquation k)).1 = 0 := by
    have h := congrArg Prod.fst (v.leibniz ((1 : k), (0 : k[X])) (productPolynomialEquation k))
    simpa [productPolynomialEquation, he] using h.symm
  intro h
  exact zero_ne_one (by simpa only [hzero, Prod.fst_one] using congrArg Prod.fst h)

end Disconnected

section UnitsAndZero
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A unit equation admits the zero derivation, with correction term minus its inverse. -/
theorem zeroDerivation_unit_normal (u : Aˣ) :
    (0 : Derivation k A A) u = 1 + (u : A) * (-(↑u⁻¹ : A)) := by simp

/-- The quotient by a unit equation is the zero algebra. -/
theorem unit_quotient_subsingleton (u : Aˣ) : Subsingleton (A ⧸ Ideal.span {(u : A)}) := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
  infer_instance

/-- The general normal-derivation theorem accepts unit equations, whose divisor is empty. -/
theorem unit_exists_normalDerivation_modulo [Algebra.FormallySmooth k A] (u : Aˣ) :
    ∃ (v : Derivation k A A) (h : A), v u = 1 + (u : A) * h := by
  let := unit_quotient_subsingleton u
  exact DeRham.exists_normalDerivation_modulo (k := k) (u : A) u.isUnit.mem_nonZeroDivisors

/-- The zero algebra is formally smooth over every commutative base ring. -/
theorem zero_formallySmooth : Algebra.FormallySmooth k PUnit := inferInstance

/-- The zero algebra is finitely presented over every commutative base ring. -/
theorem zero_finitePresentation : Algebra.FinitePresentation k PUnit := inferInstance

/-- The actual zero algebra also satisfies the normal-derivation conclusion for its equation. -/
theorem zero_exists_normalDerivation_modulo :
    ∃ (v : Derivation k PUnit PUnit) (h : PUnit), v 0 = 1 + (0 : PUnit) * h :=
  DeRham.exists_normalDerivation_modulo (k := k) (0 : PUnit)
    ⟨fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

end UnitsAndZero

end OrlikSolomon.Sanity
