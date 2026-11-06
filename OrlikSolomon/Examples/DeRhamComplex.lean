/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.DeRham.Complex

/-!
# Regressions for the de Rham differential

These check what is easy to get wrong about the differential of `DeRham/Complex`, for the edge cases
that `AGENTS.md` requires.

## Main results

* `OrlikSolomon.DeRham.Examples.d_not_linear`: `d` is not linear over the algebra. This is the
  blueprint's warning about an `A`-linear lift.
* `OrlikSolomon.DeRham.Examples.d_X_sq_of_charTwo`: in characteristic two, `X²` is a nonconstant
  closed function, and `d² = 0` needs no division by two.
* `OrlikSolomon.DeRham.Examples.d_eq_zero_of_subsingleton`: over the zero algebra `d` is zero. There
  is no nontriviality hypothesis anywhere in `DeRham/Complex`.
* `OrlikSolomon.DeRham.Examples.d_algebraMap_base`: elements of `k` are closed.
-/

@[expose] public section

namespace OrlikSolomon.DeRham.Examples

open MvPolynomial (X)

variable {k : Type*} [CommRing k]

/-- The differential is not linear over the algebra, for any nonzero `k`: `X` times `d 1` is zero,
and `d (X • 1)` is `dX`, which is nonzero. -/
theorem d_not_linear [Nontrivial k] {I : Type*} (i : I) :
    d k ((X i : MvPolynomial I k) • (1 : Forms k (MvPolynomial I k))) ≠
      (X i : MvPolynomial I k) • d k (1 : Forms k (MvPolynomial I k)) := by
  rw [d_smul_one, d_one, smul_zero]
  exact diff_X_ne_zero k i

/-- In characteristic two, `d (X²) = 2 X dX = 0`, although `X²` is not a constant. -/
theorem d_X_sq_of_charTwo {I : Type*} (i : I) :
    diff (ZMod 2) ((X i : MvPolynomial I (ZMod 2)) ^ 2) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2]
  have h : ((2 : ℕ) : ZMod 2) = 0 := rfl
  rw [h, zero_smul]

/-- `d² = 0` over `ZMod 2`, where `d` is still not zero. -/
example {I : Type*} (x : Forms (ZMod 2) (MvPolynomial I (ZMod 2))) :
    d (ZMod 2) (d (ZMod 2) x) = 0 :=
  d_d _ x

/-- Over the zero algebra the differential is zero, since all forms are zero. -/
theorem d_eq_zero_of_subsingleton {A : Type*} [CommRing A] [Algebra k A] [Subsingleton A] :
    d k = (0 : Forms k A →ₗ[k] Forms k A) :=
  Subsingleton.elim _ _

/-- Elements of `k` are closed. -/
theorem d_algebraMap_base {A : Type*} [CommRing A] [Algebra k A] (c : k) :
    d k (algebraMap k (Forms k A) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply k A (Forms k A), d_algebraMap, Derivation.map_algebraMap]

end OrlikSolomon.DeRham.Examples
