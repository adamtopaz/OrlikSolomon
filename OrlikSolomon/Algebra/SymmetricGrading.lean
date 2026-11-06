/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The grading of a symmetric algebra

This file grades the symmetric algebra `Sym(M)` of a module by degree, with no choice of basis: the
piece of degree `n` is the `n`-th power of the image of `M`. Mathlib grades the tensor algebra and
the exterior algebra in this way, but not yet the symmetric algebra.

## Main definitions

* `OrlikSolomon.symmetricGrading R M`: the grading, with its instance of `GradedAlgebra`.

## Main results

* `OrlikSolomon.map_equivMvPolynomial_symmetricGrading`: in any basis of `M`, this is the grading of
  the polynomial ring by total degree.
* `OrlikSolomon.apply_eq_pow_mul_of_mem_symmetricGrading`: two algebra maps out of `Sym(M)` that are
  proportional on `M` by a factor `u` differ by `u ^ n` on elements of degree `n`. This is what it
  means for an element to be a homogeneous function of degree `n`, and no rational points are
  involved.

## Blueprint

The blueprint does not name this grading. It is what `def:projective` needs in order to say what the
ring of a projective complement is, and what relates that ring to Mathlib's `Proj`.
-/

@[expose] public section

noncomputable section

open Module
open scoped DirectSum

namespace OrlikSolomon

section Grading

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

/-- The grading of the symmetric algebra `Sym(M)` by degree: the piece of degree `n` is the `n`-th
power of the image of `M`, that is, the span of the products of `n` elements of `M`. In a basis of
`M` this is the grading of the polynomial ring by total degree, by
`map_equivMvPolynomial_symmetricGrading`. -/
def symmetricGrading (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

instance : SetLike.GradedMonoid (symmetricGrading R M) :=
  Submodule.nat_power_gradedMonoid _

variable {R M}

theorem ι_mem_symmetricGrading (m : M) :
    SymmetricAlgebra.ι R M m ∈ symmetricGrading R M 1 := by
  rw [symmetricGrading, pow_one]
  exact LinearMap.mem_range_self _ m

theorem algebraMap_mem_symmetricGrading (r : R) :
    algebraMap R (SymmetricAlgebra R M) r ∈ symmetricGrading R M 0 := by
  rw [symmetricGrading, pow_zero]
  exact Submodule.algebraMap_mem r

variable (R M) in
/-- The map from `M` to the graded structure, an auxiliary construction which defines the
decomposition. -/
def symmetricGradingι : M →ₗ[R] ⨁ i, symmetricGrading R M i :=
  DirectSum.lof R ℕ (fun i ↦ symmetricGrading R M i) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ ι_mem_symmetricGrading

instance : GradedAlgebra (symmetricGrading R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (symmetricGradingι R M))
    (SymmetricAlgebra.algHom_ext <| LinearMap.ext fun m ↦ by
      simp [symmetricGradingι, DirectSum.lof_eq_of, DirectSum.coeAlgHom_of])
    fun i x ↦ by
      obtain ⟨x, hx⟩ := x
      dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r =>
        rw [AlgHom.commutes, DirectSum.algebraMap_apply]
        rfl
      | add x y i hx hy ihx ihy =>
        rw [map_add, ihx, ihy, ← map_add]
        rfl
      | mem_mul m hm i x hx ih =>
        obtain ⟨_, rfl⟩ := hm
        rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, symmetricGradingι, LinearMap.comp_apply,
          DirectSum.lof_eq_of, DirectSum.of_mul_of]
        exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- If two algebra maps out of `Sym(M)` satisfy `φ m = u * ψ m` on `M`, then `φ a = u ^ n * ψ a` for
`a` of degree `n`.

This expresses that `a` is a homogeneous function of degree `n`, without evaluating at points.
Taking `ψ` to be the map `ξ ↦ ξ / u` and `φ` the inclusion, it says that dehomogenizing `a` divides
it by `u ^ n`. -/
theorem apply_eq_pow_mul_of_mem_symmetricGrading {φ ψ : SymmetricAlgebra R M →ₐ[R] B} {u : B}
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) = u * ψ (SymmetricAlgebra.ι R M m)) {n : ℕ}
    {a : SymmetricAlgebra R M} (ha : a ∈ symmetricGrading R M n) : φ a = u ^ n * ψ a := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => simp [ihx, ihy, mul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, map_mul, ih, h, pow_succ]
    ring

/-- In any basis of `M`, the degree grading of `Sym(M)` is the grading of the polynomial ring by
total degree. So it does not depend on a basis, and in a basis it is the usual one. -/
theorem map_equivMvPolynomial_symmetricGrading {κ : Type*} (b : Basis κ R M) (n : ℕ) :
    (symmetricGrading R M n).map
        (SymmetricAlgebra.equivMvPolynomial b : _ →ₐ[R] MvPolynomial κ R).toLinearMap =
      MvPolynomial.homogeneousSubmodule κ R n := by
  rw [symmetricGrading, ← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, LinearMap.range_eq_map, ← b.span_eq,
    Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr! 3
  ext i
  simp

end Grading

end OrlikSolomon
