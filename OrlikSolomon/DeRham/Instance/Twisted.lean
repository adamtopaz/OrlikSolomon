/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Homotopy
public import OrlikSolomon.Grading.Diagonal
public import OrlikSolomon.Grading.Laurent
public import OrlikSolomon.Grading.TensorProduct

/-!
# De Rham cohomology with Laurent coefficients

For a commutative algebra `A` over a commutative ring `k`, with no smoothness hypothesis, this file
studies the algebra `C(A) = k[T;T⁻¹] ⊗[k] H^•_dR(A/k)` of the de Rham instance, with the piece
`C(A)_{p, w} = T^w H^p_dR(A/k)` of bidegree `(p, w)`. This is the blueprint's
`H^•_dR(A/k) ⊗_k k[t, t⁻¹]`, with the factors exchanged: Mathlib's `k[T;T⁻¹]`-algebra structure on a
tensor product is on the left factor.

Everything here is about the algebra `TwistedCohomology k A` and does not mention `SmoothAlg k`.
`DeRham/Instance/Basic` packages it as a functor on smooth algebras.

## Main definitions

* `OrlikSolomon.DeRham.TwistedCohomology k A`: the algebra `C(A)`.
* `TwistedCohomology.grading k A (p, w)`: the piece `T^w H^p`, with its `GradedAlgebra` instance.
* `TwistedCohomology.map φ`: the map `H(φ) ⊗ 1`, linear over `k[T;T⁻¹]`.
* `TwistedCohomology.evalOne k A`: the `k`-algebra map `C(A) → H^•` that forgets the powers of `T`.
* `TwistedCohomology.gradingEquiv k A p w`, `TwistedCohomology.degreeEquiv k A n w`: the
  identification of `H^p` with the piece `T^w H^p`, for `p : ℤ` and for `p = n : ℕ`.
* `TwistedCohomology.diagonal k A`: the `k`-algebra map `H^• → C(A)` that sends `x ∈ H^q` to
  `T^q x`.
* `TwistedCohomology.diagonalEquiv k A`: the equivalence of `H^•` with `⨁ q : ℕ, C(A)_{q, q}`.

## Main results

* `TwistedCohomology.mem_grading_iff`: `C(A)_{p, w}` consists of the `T w ⊗ₜ c` with `c ∈ H^p`.
* `TwistedCohomology.T_tmul_inj`: multiplication by `T^w` is injective.
* `TwistedCohomology.isGradedCommutative_grading`: graded commutativity with a sign depending only
  on the cohomological degree `p`, and not on the weight.
* `TwistedCohomology.isHomogeneousOfShift_map`, `TwistedCohomology.algebraMap_mem_grading`.
* `TwistedCohomology.bijective_algebraMap_point`, `TwistedCohomology.eq_zero_of_mem_grading_point`:
  the point.
* `TwistedCohomology.bijective_map_C`: invariance under `A → A[X]`, when positive integers are
  units in `k`.
* `TwistedCohomology.bijOn_diagonal`: `diagonal` restricts to a bijection from `H^q` to
  `C(A)_{q, q}`.

## Normal form

A homogeneous element of bidegree `(p, w)` is `T w ⊗ₜ[k] c`, for a unique `c` in `H^p`, namely
`evalOne k A x`. This is the form in which to compute: `T_tmul_mul_T_tmul` and `T_smul_T_tmul`
multiply such elements, `map_tmul` moves pullbacks to the right factor, and `evalOne_T_tmul` strips
the power of `T`. `induction_on` reduces any statement that is additive in `x` to this form.

## Blueprint

`def:dr-twisted-functor`, and the fields of `lem:dr-ordinary-basic` before they are stated on smooth
algebras. `lem:dr-tau` and `cor:dr-affine` remove the powers of `T` from the diagonal with
`diagonalEquiv` and `evalOne`.
-/

@[expose] public section

noncomputable section

open DirectSum
open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial (T)

universe u v v' v''

namespace OrlikSolomon.DeRham

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {A' : Type v'} [CommRing A'] [Algebra k A'] {A'' : Type v''} [CommRing A''] [Algebra k A'']

/-- The total de Rham cohomology with coefficients in the Laurent polynomials, `C(A)` in the
blueprint. It is a `k[T;T⁻¹]`-algebra through the left factor, as the blueprint asks, and its
`k`-algebra structure is the restriction of that. It is only graded commutative.

Blueprint: `def:dr-twisted-functor`. -/
abbrev TwistedCohomology : Type (max u v) :=
  k[T;T⁻¹] ⊗[k] Cohomology k A

namespace TwistedCohomology

/-! ### The bigrading -/

/-- The piece `C(A)_{p, w} = T^w H^p` of bidegree `(p, w)`, with the cohomological degree `p` first.
It is zero for `p < 0`, by `grading_of_neg`. It is the product of the weight grading of `k[T;T⁻¹]`
and the cohomological grading, with the indices exchanged: `grading_apply` and `mem_grading_iff`
describe it.

Blueprint: `def:dr-twisted-functor`. -/
def grading : ℤ × ℤ → Submodule k (TwistedCohomology k A) :=
  coarsenGrading (tensorProductGrading (laurentGrading k) (Cohomology.grading k A))
    (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom

/-- `C(A)` is the internal direct sum of its pieces, compatibly with products: both degrees add,
and the unit has degree `(0, 0)`.

Blueprint: `def:dr-twisted-functor`. -/
instance gradedAlgebraGrading : GradedAlgebra (grading k A) :=
  inferInstanceAs (GradedAlgebra (coarsenGrading
    (tensorProductGrading (laurentGrading k) (Cohomology.grading k A))
    (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom))

variable {k A}

/-- The piece of bidegree `(p, w)` is the piece `(w, p)` of the product grading. -/
theorem grading_apply (p w : ℤ) :
    grading k A (p, w) =
      tensorProductGrading (laurentGrading k) (Cohomology.grading k A) (w, p) :=
  coarsenGrading_apply (tensorProductGrading (laurentGrading k) (Cohomology.grading k A))
    (f := (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom)
    (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).injective (w, p)

/-- A coefficient of weight `w` times a class of degree `p` has bidegree `(p, w)`. -/
theorem tmul_mem_grading {p w : ℤ} {b : k[T;T⁻¹]} {c : Cohomology k A}
    (hb : b ∈ laurentGrading k w) (hc : c ∈ Cohomology.grading k A p) :
    b ⊗ₜ[k] c ∈ grading k A (p, w) := by
  rw [grading_apply]
  exact tmul_mem_tensorProductGrading _ _ hb hc

/-- The unit times a class of degree `p` has bidegree `(p, 0)`. -/
theorem one_tmul_mem_grading {p : ℤ} {c : Cohomology k A} (hc : c ∈ Cohomology.grading k A p) :
    (1 : k[T;T⁻¹]) ⊗ₜ[k] c ∈ grading k A (p, 0) :=
  tmul_mem_grading (LaurentPolynomial.T_zero (R := k) ▸ T_mem_laurentGrading 0) hc

/-! ### Forgetting the weight -/

variable (k A) in
/-- The `k`-algebra map `C(A) → H^•` that sends `T` to `1`. It sends `T w ⊗ₜ c` to `c`, by
`evalOne_T_tmul`, so it forgets the weight, and it is injective on each piece of the bigrading. It
is how the blueprint's `x t^q ↦ x` is written, in `cor:dr-affine`. -/
def evalOne : TwistedCohomology k A →ₐ[k] Cohomology k A :=
  Algebra.TensorProduct.lift ((Algebra.ofId k (Cohomology k A)).comp (laurentEvalOne k))
    (AlgHom.id k (Cohomology k A)) (by
      intro b c
      exact Algebra.commute_algebraMap_left (R := k) (laurentEvalOne k b) c)

@[simp]
theorem evalOne_tmul (b : k[T;T⁻¹]) (c : Cohomology k A) :
    evalOne k A (b ⊗ₜ[k] c) = laurentEvalOne k b • c := by
  rw [evalOne, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
    Algebra.ofId_apply, Algebra.smul_def]

theorem evalOne_T_tmul (w : ℤ) (c : Cohomology k A) : evalOne k A (T w ⊗ₜ[k] c) = c := by
  rw [evalOne_tmul, laurentEvalOne_T, one_smul]

/-- The map `C(A) → H^•` splits the inclusion `c ↦ 1 ⊗ₜ c` of the right factor. -/
theorem evalOne_one_tmul (c : Cohomology k A) : evalOne k A ((1 : k[T;T⁻¹]) ⊗ₜ[k] c) = c := by
  rw [evalOne_tmul, map_one, one_smul]

/-- Multiplication by `T^w` is injective. -/
theorem T_tmul_injective (w : ℤ) :
    Function.Injective fun c : Cohomology k A ↦ (T w ⊗ₜ[k] c : TwistedCohomology k A) :=
  Function.LeftInverse.injective (g := evalOne k A) (evalOne_T_tmul w)

@[simp]
theorem T_tmul_inj {w : ℤ} {c c' : Cohomology k A} :
    (T w ⊗ₜ[k] c : TwistedCohomology k A) = T w ⊗ₜ[k] c' ↔ c = c' :=
  (T_tmul_injective w).eq_iff

@[simp]
theorem T_tmul_eq_zero {w : ℤ} {c : Cohomology k A} :
    (T w ⊗ₜ[k] c : TwistedCohomology k A) = 0 ↔ c = 0 := by
  rw [← TensorProduct.tmul_zero (R := k) (Cohomology k A) (T w : k[T;T⁻¹]), T_tmul_inj]

/-- The class `c` of a homogeneous element `T w ⊗ₜ c` is the value of `evalOne`. -/
theorem T_tmul_evalOne_of_mem_grading {p w : ℤ} {x : TwistedCohomology k A}
    (hx : x ∈ grading k A (p, w)) : T w ⊗ₜ[k] evalOne k A x = x := by
  rw [grading_apply, tensorProductGrading_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, hb, c, -, rfl⟩ := h
    rw [evalOne_tmul, ← TensorProduct.smul_tmul, eq_laurentEvalOne_smul_T_of_mem hb]
  | zero => simp
  | add _ _ _ _ hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | smul r _ _ hx => rw [map_smul, TensorProduct.tmul_smul, hx]

/-- The map `C(A) → H^•` sends the piece of bidegree `(p, w)` to `H^p`. -/
theorem evalOne_mem_of_mem_grading {p w : ℤ} {x : TwistedCohomology k A}
    (hx : x ∈ grading k A (p, w)) : evalOne k A x ∈ Cohomology.grading k A p := by
  rw [grading_apply, tensorProductGrading_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, -, c, hc, rfl⟩ := h
    rw [evalOne_tmul]
    exact Submodule.smul_mem _ _ hc
  | zero => simp
  | add _ _ _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r _ _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- **The piece of bidegree `(p, w)` is `T^w H^p`**, with no sum and no span. This is the main
description of the grading.

Blueprint: `def:dr-twisted-functor`. -/
theorem mem_grading_iff {p w : ℤ} {x : TwistedCohomology k A} :
    x ∈ grading k A (p, w) ↔ ∃ c ∈ Cohomology.grading k A p, T w ⊗ₜ[k] c = x := by
  refine ⟨fun hx ↦ ⟨_, evalOne_mem_of_mem_grading hx, T_tmul_evalOne_of_mem_grading hx⟩, ?_⟩
  rintro ⟨c, hc, rfl⟩
  exact tmul_mem_grading (T_mem_laurentGrading w) hc

theorem T_tmul_mem_grading {p w : ℤ} {c : Cohomology k A} (hc : c ∈ Cohomology.grading k A p) :
    T w ⊗ₜ[k] c ∈ grading k A (p, w) :=
  mem_grading_iff.2 ⟨c, hc, rfl⟩

/-- The class `T^w c` has bidegree `(p, w)` exactly when `c` has degree `p`. -/
@[simp]
theorem T_tmul_mem_grading_iff {p w : ℤ} {c : Cohomology k A} :
    T w ⊗ₜ[k] c ∈ grading k A (p, w) ↔ c ∈ Cohomology.grading k A p :=
  ⟨fun h ↦ evalOne_T_tmul w c ▸ evalOne_mem_of_mem_grading h, T_tmul_mem_grading⟩

/-- In a natural cohomological degree, the class `T^w c` has bidegree `(n, w)` exactly when `c` is
in `H^n`. -/
theorem T_tmul_mem_grading_natCast_iff {n : ℕ} {w : ℤ} {c : Cohomology k A} :
    T w ⊗ₜ[k] c ∈ grading k A ((n : ℤ), w) ↔ c ∈ Cohomology.degree k A n := by
  rw [T_tmul_mem_grading_iff, Cohomology.grading_natCast]

/-- The grading is zero in negative cohomological degrees, in every weight. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) (w : ℤ) : grading k A (p, w) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 hx
  rw [Cohomology.eq_zero_of_mem_grading_of_neg hp hc, TensorProduct.tmul_zero]

variable (k A) in
/-- The identification of `H^p` with the piece `C(A)_{p, w} = T^w H^p`, which strips the power of
`T`. Its inverse is `evalOne`, by `coe_gradingEquiv_symm_apply`. -/
def gradingEquiv (p w : ℤ) : Cohomology.grading k A p ≃ₗ[k] grading k A (p, w) where
  toFun c := ⟨T w ⊗ₜ[k] (c : Cohomology k A), T_tmul_mem_grading c.2⟩
  map_add' _ _ := Subtype.ext <| TensorProduct.tmul_add _ _ _
  map_smul' r _ := Subtype.ext <| TensorProduct.tmul_smul r _ _
  invFun x := ⟨evalOne k A x, evalOne_mem_of_mem_grading x.2⟩
  left_inv c := Subtype.ext <| evalOne_T_tmul w (c : Cohomology k A)
  right_inv x := Subtype.ext <| T_tmul_evalOne_of_mem_grading x.2

@[simp]
theorem coe_gradingEquiv_apply (p w : ℤ) (c : Cohomology.grading k A p) :
    (gradingEquiv k A p w c : TwistedCohomology k A) = T w ⊗ₜ[k] (c : Cohomology k A) :=
  rfl

@[simp]
theorem coe_gradingEquiv_symm_apply (p w : ℤ) (x : grading k A (p, w)) :
    ((gradingEquiv k A p w).symm x : Cohomology k A) = evalOne k A x :=
  rfl

variable (k A) in
/-- The identification of `H^n` with the piece `C(A)_{n, w} = T^w H^n`, in a natural degree. At
`w = n` this is the diagonal piece of `cor:dr-affine`: the piece `C(A)_{q, q}` is `H^q`, by
stripping `T^q`. Its inverse is `evalOne`.

Blueprint: `cor:dr-affine`, the diagonal. -/
def degreeEquiv (n : ℕ) (w : ℤ) : Cohomology.degree k A n ≃ₗ[k] grading k A ((n : ℤ), w) :=
  LinearEquiv.ofEq _ _ (Cohomology.grading_natCast n).symm ≪≫ₗ gradingEquiv k A n w

@[simp]
theorem coe_degreeEquiv_apply (n : ℕ) (w : ℤ) (c : Cohomology.degree k A n) :
    (degreeEquiv k A n w c : TwistedCohomology k A) = T w ⊗ₜ[k] (c : Cohomology k A) :=
  rfl

@[simp]
theorem coe_degreeEquiv_symm_apply (n : ℕ) (w : ℤ) (x : grading k A ((n : ℤ), w)) :
    ((degreeEquiv k A n w).symm x : Cohomology k A) = evalOne k A x :=
  rfl

/-! ### Computing in the normal form -/

/-- Induction over elements of `C(A)`: every element is a sum of `T w ⊗ₜ c`.

Blueprint: `def:dr-twisted-functor`, where the Laurent monomials form a `k`-basis of `B`. -/
@[elab_as_elim]
theorem induction_on {motive : TwistedCohomology k A → Prop}
    (T_tmul : ∀ (w : ℤ) (c : Cohomology k A), motive (T w ⊗ₜ[k] c))
    (add : ∀ x y, motive x → motive y → motive (x + y)) (x : TwistedCohomology k A) : motive x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact add x y hx hy
  | tmul b c =>
    induction b using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa only [TensorProduct.add_tmul] using add _ _ hp hq
    | C_mul_T n a =>
      have h : (LaurentPolynomial.C a * T n : k[T;T⁻¹]) = a • T n := by
        rw [LaurentPolynomial.smul_eq_C_mul]
      rw [h, TensorProduct.smul_tmul]
      exact T_tmul n _

/-- The action of a coefficient, on the left factor. -/
theorem smul_tmul (b b' : k[T;T⁻¹]) (c : Cohomology k A) :
    b • (b' ⊗ₜ[k] c : TwistedCohomology k A) = (b * b') ⊗ₜ[k] c := by
  rw [TensorProduct.smul_tmul', smul_eq_mul]

/-- Powers of `T` multiply by adding exponents. -/
theorem T_smul_T_tmul (w v : ℤ) (c : Cohomology k A) :
    (T w : k[T;T⁻¹]) • (T v ⊗ₜ[k] c : TwistedCohomology k A) = T (w + v) ⊗ₜ[k] c := by
  rw [smul_tmul, LaurentPolynomial.T_add]

/-- Homogeneous elements multiply by adding weights and multiplying classes. This is not a `simp`
lemma, since `simp` applies `Algebra.TensorProduct.tmul_mul_tmul` to its left side. -/
theorem T_tmul_mul_T_tmul (w v : ℤ) (c c' : Cohomology k A) :
    (T w ⊗ₜ[k] c : TwistedCohomology k A) * T v ⊗ₜ[k] c' = T (w + v) ⊗ₜ[k] (c * c') := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, LaurentPolynomial.T_add]

/-- The structure map of the `k[T;T⁻¹]`-algebra `C(A)`. -/
theorem algebraMap_apply (b : k[T;T⁻¹]) :
    algebraMap k[T;T⁻¹] (TwistedCohomology k A) b = b ⊗ₜ[k] 1 :=
  rfl

/-- `B → C(A)` sends the piece `k T^w` into bidegree `(0, w)`.

Blueprint: `lem:dr-ordinary-basic`, for the field `algebraMap_mem_grading`. -/
theorem algebraMap_mem_grading {w : ℤ} {b : k[T;T⁻¹]} (hb : b ∈ laurentGrading k w) :
    algebraMap k[T;T⁻¹] (TwistedCohomology k A) b ∈ grading k A (0, w) :=
  tmul_mem_grading hb (SetLike.GradedOne.one_mem (A := Cohomology.grading k A))

/-! ### Graded commutativity -/

variable (k A) in
/-- `C(A)` is graded commutative, with the sign `(-1)^(pq)` of the cohomological degrees `p`, `q`.
The sign does not see the weights, since `T` is central. Nothing is assumed about `2`.

Blueprint: `lem:dr-ordinary-basic`, for the field `isGradedCommutative`. -/
theorem isGradedCommutative_grading : IsGradedCommutative (grading k A) Prod.fst := by
  rintro ⟨p, w⟩ ⟨q, v⟩ x y hx hy
  obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 hx
  obtain ⟨c', hc', rfl⟩ := mem_grading_iff.1 hy
  have h : c * c' = (p * q).negOnePow • (c' * c) :=
    Cohomology.isGradedCommutative_grading k A hc hc'
  rw [T_tmul_mul_T_tmul, T_tmul_mul_T_tmul, add_comm w v, h]
  obtain hu | hu := Int.units_eq_one_or ((p * q).negOnePow) <;>
    simp [hu, TensorProduct.tmul_neg]

/-! ### Functoriality -/

/-- The map `H(φ) ⊗ 1` on `C(A)`, linear over `k[T;T⁻¹]`, which is what the blueprint's `C(φ)` is.

Blueprint: `def:dr-twisted-functor`. -/
def map (φ : A →ₐ[k] A') : TwistedCohomology k A →ₐ[k[T;T⁻¹]] TwistedCohomology k A' :=
  Algebra.TensorProduct.map (AlgHom.id k[T;T⁻¹] k[T;T⁻¹]) (Cohomology.map φ)

@[simp]
theorem map_tmul (φ : A →ₐ[k] A') (b : k[T;T⁻¹]) (c : Cohomology k A) :
    map φ (b ⊗ₜ[k] c) = b ⊗ₜ[k] Cohomology.map φ c :=
  rfl

@[simp]
theorem map_id : map (AlgHom.id k A) = AlgHom.id k[T;T⁻¹] (TwistedCohomology k A) := by
  rw [map, Cohomology.map_id]
  exact Algebra.TensorProduct.map_id

theorem map_comp (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  rw [map, Cohomology.map_comp]
  exact Algebra.TensorProduct.map_id_comp _ _

@[simp]
theorem map_map (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') (x : TwistedCohomology k A) :
    map ψ (map φ x) = map (ψ.comp φ) x := by
  rw [map_comp, AlgHom.comp_apply]

/-- The map on `C(A)` commutes with forgetting the weight. -/
@[simp]
theorem evalOne_map (φ : A →ₐ[k] A') (x : TwistedCohomology k A) :
    evalOne k A' (map φ x) = Cohomology.map φ (evalOne k A x) := by
  induction x using induction_on with
  | T_tmul w c => rw [map_tmul, evalOne_T_tmul, evalOne_T_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Pullbacks preserve bidegrees.

Blueprint: `lem:dr-ordinary-basic`, for the field `isHomogeneousOfShift_map`. -/
theorem isHomogeneousOfShift_map (φ : A →ₐ[k] A') :
    IsHomogeneousOfShift (grading k A) (grading k A') 0 (map φ) := by
  refine isHomogeneousOfShift_zero_iff.2 ?_
  rintro ⟨p, w⟩ x hx
  obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 hx
  rw [map_tmul]
  have h := Cohomology.isHomogeneousOfShift_map φ hc
  rw [add_zero] at h
  exact T_tmul_mem_grading h

/-- A map that is bijective on `H^•` is bijective on `C(A)`, by tensoring its inverse with
`k[T;T⁻¹]`. -/
theorem bijective_map {φ : A →ₐ[k] A'} (h : Function.Bijective (Cohomology.map φ)) :
    Function.Bijective (map φ) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : k[T;T⁻¹] ≃ₐ[k[T;T⁻¹]] k[T;T⁻¹])
    (AlgEquiv.ofBijective (Cohomology.map φ) h)).bijective

variable (k A) in
/-- `C(A) → C(A[X])` is bijective, if positive integers are units in `k`. Its inverse is the map of
evaluation at zero, by the integration homotopy of `thm:dr-homotopy`.

Blueprint: `lem:dr-ordinary-basic`, for the field `bijective_map_polynomialC`. -/
theorem bijective_map_C (h : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    Function.Bijective (map (Polynomial.CAlgHom (R := k) (A := A))) :=
  bijective_map (bijective_cohomologyMap_C k A h)

/-! ### The point -/

variable (k) in
/-- The structure map `B → C(k)` is bijective: `H^*(k/k) = k`, tensored with `B`.

Blueprint: `lem:dr-ordinary-basic`, for the field `bijective_algebraMap_point`. -/
theorem bijective_algebraMap_point :
    Function.Bijective (algebraMap k[T;T⁻¹] (TwistedCohomology k k)) := by
  let e : k[T;T⁻¹] ≃ₐ[k[T;T⁻¹]] TwistedCohomology k k :=
    (Algebra.TensorProduct.rid k k[T;T⁻¹] k[T;T⁻¹]).symm.trans
      (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective (Algebra.ofId k _)
        (Cohomology.bijective_algebraMap_point k)))
  convert e.bijective using 1
  exact funext fun b ↦ (e.commutes b).symm

/-- The point has nothing in a nonzero cohomological degree, in any weight.

Blueprint: `lem:dr-ordinary-basic`, for the field `eq_zero_of_mem_grading_point`. -/
theorem eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : TwistedCohomology k k}
    (hx : x ∈ grading k k (p, w)) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 hx
  rw [Cohomology.eq_zero_of_mem_grading_point hp hc, TensorProduct.tmul_zero]

/-! ### Nonvanishing -/

/-- `C(A)` is nonzero for a nonzero algebra `A`. This includes the point over a nonzero ring. -/
instance [Nontrivial A] : Nontrivial (TwistedCohomology k A) :=
  (evalOne k A).toRingHom.domain_nontrivial

/-- `C(A)` is zero for the zero algebra. -/
instance [Subsingleton A] : Subsingleton (TwistedCohomology k A) :=
  ⟨fun x y ↦ by
    have h : ∀ x : TwistedCohomology k A, x = 0 := fun x ↦ by
      induction x using induction_on with
      | T_tmul w c => rw [Subsingleton.elim c 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h x, h y]⟩

/-! ### The diagonal -/

variable (k A) in
/-- The `k`-algebra map `⨁ q : ℕ, H^q → C(A)`, which sends `x ∈ H^q` to `T^q x`. Use `diagonal`. -/
def diagonalAux : (⨁ n : ℕ, Cohomology.degree k A n) →ₐ[k] TwistedCohomology k A :=
  DirectSum.toAlgebra k (fun n : ℕ ↦ Cohomology.degree k A n)
    (fun n ↦ (TensorProduct.mk k k[T;T⁻¹] (Cohomology k A) (T (n : ℤ))) ∘ₗ
      (Cohomology.degree k A n).subtype)
    (by
      change T ((0 : ℕ) : ℤ) ⊗ₜ[k] (1 : Cohomology k A) = 1
      rw [Nat.cast_zero, LaurentPolynomial.T_zero]
      rfl)
    (fun {i j} c c' ↦ by
      change T ((i + j : ℕ) : ℤ) ⊗ₜ[k] ((c : Cohomology k A) * (c' : Cohomology k A)) =
        T (i : ℤ) ⊗ₜ[k] (c : Cohomology k A) * T (j : ℤ) ⊗ₜ[k] (c' : Cohomology k A)
      rw [T_tmul_mul_T_tmul, Nat.cast_add])

variable (k A) in
/-- The `k`-algebra map `H^• → C(A)` that sends a class `x` of degree `q` to `T^q x`, by
`diagonal_of_mem_degree`. In `cor:dr-affine`, this is the blueprint's inverse of `x t^q ↦ x`, and it
is multiplicative because multiplication adds degrees. It is not linear over `k[T;T⁻¹]`, which does
not act on `H^•`. -/
def diagonal : Cohomology k A →ₐ[k] TwistedCohomology k A :=
  (diagonalAux k A).comp (decomposeAlgEquiv (Cohomology.degree k A)).toAlgHom

/-- On a class of degree `q`, the map `H^• → C(A)` is multiplication by `T^q`. -/
theorem diagonal_of_mem_degree {q : ℕ} {c : Cohomology k A} (hc : c ∈ Cohomology.degree k A q) :
    diagonal k A c = T (q : ℤ) ⊗ₜ[k] c := by
  change diagonalAux k A (decompose (Cohomology.degree k A) c) = _
  rw [decompose_of_mem _ hc]
  exact DirectSum.toAddMonoid_of (β := fun n : ℕ ↦ Cohomology.degree k A n) (fun n ↦
    ((TensorProduct.mk k k[T;T⁻¹] (Cohomology k A) (T (n : ℤ))) ∘ₗ
      (Cohomology.degree k A n).subtype).toAddMonoidHom) q ⟨c, hc⟩

@[simp]
theorem evalOne_diagonal (c : Cohomology k A) : evalOne k A (diagonal k A c) = c := by
  induction c using Cohomology.induction_degree with
  | mk n x hxn hx => rw [diagonal_of_mem_degree (Cohomology.mk_mem_degree hxn hx), evalOne_T_tmul]
  | add c c' hc hc' => simp only [map_add, hc, hc']

/-- The map `H^• → C(A)` is natural. -/
@[simp]
theorem map_diagonal (φ : A →ₐ[k] A') (c : Cohomology k A) :
    map φ (diagonal k A c) = diagonal k A' (Cohomology.map φ c) := by
  induction c using Cohomology.induction_degree with
  | mk n x hxn hx =>
    have h := Cohomology.mk_mem_degree hxn hx
    rw [diagonal_of_mem_degree h, map_tmul, diagonal_of_mem_degree (Cohomology.map_mem_degree φ h)]
  | add c c' hc hc' => simp only [map_add, hc, hc']

/-- The map `H^• → C(A)` restricts to a bijection from `H^q` to `C(A)_{q, q}`.

Blueprint: `cor:dr-affine`, the diagonal. -/
theorem bijOn_diagonal (q : ℕ) :
    Set.BijOn (diagonal k A) (Cohomology.degree k A q) (grading k A ((q : ℤ), (q : ℤ))) := by
  refine ⟨fun c hc ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · rw [SetLike.mem_coe] at hc ⊢
    rw [diagonal_of_mem_degree hc, T_tmul_mem_grading_natCast_iff]
    exact hc
  · exact (Function.LeftInverse.injective (g := evalOne k A) evalOne_diagonal).injOn
  · obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 (SetLike.mem_coe.1 hx)
    rw [Cohomology.grading_natCast] at hc
    exact ⟨c, hc, diagonal_of_mem_degree hc⟩

variable (k A) in
/-- **The diagonal of `C(A)` is `H^•`**: the `k`-algebra equivalence of total cohomology with
`⨁ q : ℕ, C(A)_{q, q}`, in which the powers of `T` are removed. Its target is the target of
`OrdinaryTheory.diagonalEquiv` and of `OrdinaryTheory.projectiveDiagonalEquiv`, so composing
with its inverse states those for de Rham cohomology.

Blueprint: `cor:dr-affine`, the diagonal. -/
def diagonalEquiv :
    Cohomology k A ≃ₐ[k] ⨁ q : ℕ, diagonalGrading (grading k A) q :=
  diagonalAlgEquiv (Cohomology.degree k A) bijOn_diagonal

/-- The image in `C(A)` of the equivalence is `diagonal`. -/
@[simp]
theorem coeAlgHom_diagonalEquiv (c : Cohomology k A) :
    coeAlgHom (diagonalGrading (grading k A)) (diagonalEquiv k A c) = diagonal k A c :=
  coeAlgHom_diagonalAlgEquiv _ _ c

/-- The inverse of the equivalence forgets the weights: it is `evalOne` of the image in `C(A)`. -/
theorem diagonalEquiv_symm_apply (x : ⨁ q : ℕ, diagonalGrading (grading k A) q) :
    (diagonalEquiv k A).symm x =
      evalOne k A (coeAlgHom (diagonalGrading (grading k A)) x) := by
  obtain ⟨c, rfl⟩ := (diagonalEquiv k A).surjective x
  rw [AlgEquiv.symm_apply_apply, coeAlgHom_diagonalEquiv, evalOne_diagonal]

/-- On a class of degree `q`, the equivalence is the inclusion of `T^q c`. -/
theorem diagonalEquiv_of_mem_degree {q : ℕ} {c : Cohomology k A}
    (hc : c ∈ Cohomology.degree k A q) :
    diagonalEquiv k A c =
      of (fun q ↦ diagonalGrading (grading k A) q) q ⟨T (q : ℤ) ⊗ₜ[k] c,
        mem_diagonalGrading.2 (T_tmul_mem_grading_natCast_iff.2 hc)⟩ :=
  (diagonalAlgEquiv_of_mem _ _ hc).trans <| congrArg (of _ q) <|
    Subtype.ext (diagonal_of_mem_degree hc)

end TwistedCohomology

end OrlikSolomon.DeRham
