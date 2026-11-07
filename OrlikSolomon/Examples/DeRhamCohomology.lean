/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.DeRham.Cohomology

/-!
# Regressions for de Rham cohomology

These check what is easy to get wrong about the cohomology algebra of `DeRham/Cohomology`, for the
edge cases that `AGENTS.md` requires.

## Main results

* `OrlikSolomon.DeRham.Examples.not_exists_d_eq_X_smul_diff_X`: a function times an exact form need
  not be exact, or even closed. This is why the quotient is taken in the closed forms, as the
  blueprint's `def:dr-cohomology` warns.
* `OrlikSolomon.DeRham.Examples.not_surjective_map_C_of_charTwo`: over `ZMod 2` the map to the
  cohomology of a polynomial ring is not surjective, because `X²` is a nonconstant closed function.
  So the construction is correct in characteristic two, and homotopy invariance really needs its
  hypothesis. This is part of `prop:dr-characteristic-p`.
* The examples at the end of the file: the point over `ℤ` and `ZMod 2`, the zero algebra, negative
  degrees and anticommutation in odd degree, with no hypothesis on `2`.
-/

@[expose] public section

noncomputable section

open OrlikSolomon.DeRham.Cohomology
open scoped Polynomial

namespace OrlikSolomon.DeRham.Examples

variable {k : Type*} [CommRing k]

/-- The exact forms are not an ideal of all forms, for any nonzero `k`: `dX_j` is exact, while
`X_i dX_j` has differential `dX_i ∧ dX_j`, which is nonzero. -/
theorem not_exists_d_eq_X_smul_diff_X [Nontrivial k] {I : Type*} {i j : I} (hij : i ≠ j) :
    ¬ ∃ y : Forms k (MvPolynomial I k),
      d k y =
        (MvPolynomial.X i : MvPolynomial I k) • diff k (MvPolynomial.X j : MvPolynomial I k) := by
  classical
  rintro ⟨y, hy⟩
  have h₀ : diff k (MvPolynomial.X i : MvPolynomial I k) * diff k (MvPolynomial.X j) = 0 := by
    rw [← d_smul_diff, ← hy, d_d]
  -- Contract with the coordinate of `dX_i`, which leaves `dX_j`.
  let ℓ := (KaehlerDifferential.mvPolynomialBasis k I).coord i
  have hi : ℓ (KaehlerDifferential.D k _ (MvPolynomial.X i)) = 1 := by
    rw [← KaehlerDifferential.mvPolynomialBasis_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same]
  have hj : ℓ (KaehlerDifferential.D k _ (MvPolynomial.X j)) = 0 := by
    rw [← KaehlerDifferential.mvPolynomialBasis_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_eq_of_ne hij]
  have h := exteriorContraction_ι_mul_add ℓ (KaehlerDifferential.D k _ (MvPolynomial.X i))
    (diff k (MvPolynomial.X j : MvPolynomial I k))
  rw [ι_D, h₀, map_zero, zero_add, exteriorContraction_diff, hj, map_zero, mul_zero, hi,
    one_smul] at h
  exact diff_X_ne_zero k j h.symm

/-- Over `ZMod 2`, the function `X²` is closed. -/
theorem d_algebraMap_X_sq :
    d (ZMod 2) (algebraMap (ZMod 2)[X] (Forms (ZMod 2) (ZMod 2)[X]) (Polynomial.X ^ 2)) = 0 := by
  rw [d_algebraMap, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2]
  have h : ((2 : ℕ) : ZMod 2) = 0 := rfl
  rw [h, zero_smul]

/-- Over `ZMod 2`, the map from the cohomology of the point to the cohomology of the affine line is
not surjective: the class of `X²` has a nonconstant value in degree zero. So the affine-line axiom
fails here, and `thm:dr-homotopy` needs its hypothesis on `k`. The construction of cohomology itself
has no such hypothesis.

Blueprint: part of `prop:dr-characteristic-p`. -/
theorem not_surjective_map_C_of_charTwo :
    ¬ Function.Surjective
      (map (Polynomial.CAlgHom : ZMod 2 →ₐ[ZMod 2] (ZMod 2)[X])) := by
  intro h
  obtain ⟨c, hc⟩ := h (mk _ d_algebraMap_X_sq)
  have h₁ := congrArg (toDegreeZero (ZMod 2) (ZMod 2)[X]) hc
  rw [toDegreeZero_map, toDegreeZero_mk_algebraMap] at h₁
  have h₂ := congrArg Polynomial.natDegree h₁
  simp only [Polynomial.CAlgHom_apply, Polynomial.natDegree_C, Polynomial.natDegree_X_pow] at h₂
  exact absurd h₂ (by norm_num)

/-! ### Edge cases -/

/-- The point fact holds over `ℤ`, where `2` is not invertible. -/
example : Function.Bijective (algebraMap ℤ (Cohomology ℤ ℤ)) :=
  bijective_algebraMap_point ℤ

/-- The point fact holds in characteristic two. -/
example : Function.Bijective (algebraMap (ZMod 2) (Cohomology (ZMod 2) (ZMod 2))) :=
  bijective_algebraMap_point (ZMod 2)

/-- Cohomology of the zero algebra is zero, including for a zero ring of coefficients. -/
example {A : Type*} [CommRing A] [Algebra k A] [Subsingleton A] : Subsingleton (Cohomology k A) :=
  inferInstance

/-- Cohomology of a nonzero algebra is nonzero. -/
example {A : Type*} [CommRing A] [Algebra k A] [Nontrivial A] : Nontrivial (Cohomology k A) :=
  inferInstance

/-- Negative degrees are zero. -/
example {A : Type*} [CommRing A] [Algebra k A] : grading k A (-1) = ⊥ :=
  grading_of_neg (by norm_num)

/-- Classes of odd degree anticommute, with no hypothesis on `2`. -/
example {A : Type*} [CommRing A] [Algebra k A] {c c' : Cohomology k A} (hc : c ∈ degree k A 1)
    (hc' : c' ∈ degree k A 1) : c * c' = -(c' * c) :=
  (isGradedCommutative_degree k A).mul_eq_neg_of_odd (by simp) (by simp) hc hc'

end OrlikSolomon.DeRham.Examples
