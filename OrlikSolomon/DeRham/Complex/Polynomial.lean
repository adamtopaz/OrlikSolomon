/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import OrlikSolomon.DeRham.Complex.Differential

/-!
# The de Rham differential of a polynomial ring

For `P = k[X_i | i ∈ I]`, with `I` possibly infinite and `k` any commutative ring, this file proves
the explicit formula of `lem:dr-polynomial-dga` for the differential `d` of
`DeRham/Complex/Differential`:

`d (p dX_{i₁} ∧ ⋯ ∧ dX_{iₙ}) = ∑_j ∂_j p dX_j ∧ dX_{i₁} ∧ ⋯ ∧ dX_{iₙ}`.

The sum has finite support, and the formula determines `d`. Nothing here is special to
characteristic zero. The differential is that of a general algebra, since it is not built from this
case, so `d² = 0` and the signed Leibniz rule are `d_d` and `d_mul_of_mem_exteriorPower`, and that
`d` has degree one is `d_mem_exteriorPower`.

## Main results

Blueprint `lem:dr-polynomial-dga`:

* Freeness of `Ω^1_P` on the `dX_i` is Mathlib's `KaehlerDifferential.mvPolynomialBasis`.
* `OrlikSolomon.DeRham.diff_eq_sum_pderiv`: `dp = ∑_j ∂_j p dX_j`.
* `OrlikSolomon.DeRham.d_smul_word_X` and `OrlikSolomon.DeRham.d_smul_word_X_eq_finsum`: the
  formula.
* `OrlikSolomon.DeRham.finite_support_pderiv_smul`: the sum has finite support.
* `OrlikSolomon.DeRham.Forms.induction_X` and `OrlikSolomon.DeRham.eq_d_of_smul_word_X`: polynomial
  words span, and the formula determines `d`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι)
open KaehlerDifferential (D)
open MvPolynomial (X pderiv)

variable (k : Type*) [CommRing k] {I : Type*}

/-- The differential of a polynomial: `dp = ∑_j ∂_j p dX_j`. The sum runs over the variables of `p`,
since `∂_j p` vanishes for every other `j`.

Blueprint: `lem:dr-polynomial-dga`. -/
theorem diff_eq_sum_pderiv (p : MvPolynomial I k) :
    diff k p = ∑ j ∈ p.vars, pderiv j p • diff k (X j : MvPolynomial I k) := by
  classical
  have hb := (KaehlerDifferential.mvPolynomialBasis k I).linearCombination_repr (D k _ p)
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := p.vars)] at hb
  · simp only [KaehlerDifferential.mvPolynomialBasis_repr_apply,
      KaehlerDifferential.mvPolynomialBasis_apply] at hb
    rw [diff_apply, ← hb, map_sum]
    simp
  · intro j hj
    rw [Finsupp.mem_support_iff, KaehlerDifferential.mvPolynomialBasis_repr_apply] at hj
    by_contra hnot
    exact hj (MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot)
  · simp

/-- The differential of a variable is nonzero when `k` is nontrivial, since these differentials form
a basis. In particular `d` is nonzero, and it is not linear over the polynomial ring. -/
theorem diff_X_ne_zero [Nontrivial k] (i : I) : diff k (X i : MvPolynomial I k) ≠ 0 := fun h => by
  have hi := (KaehlerDifferential.mvPolynomialBasis k I).ne_zero i
  rw [KaehlerDifferential.mvPolynomialBasis_apply] at hi
  exact hi (ExteriorAlgebra.ι_inj _ _ _ |>.1 (h.trans (map_zero _).symm))

/-- The formula for the differential on polynomial words.

Blueprint: `lem:dr-polynomial-dga`. -/
theorem d_smul_word_X (p : MvPolynomial I k) (l : List I) :
    d k (p • word (fun i => diff k (X i : MvPolynomial I k)) l) =
      ∑ j ∈ p.vars, pderiv j p • (diff k (X j : MvPolynomial I k) *
        word (fun i => diff k (X i : MvPolynomial I k)) l) := by
  rw [← word_map, d_smul_word, diff_eq_sum_pderiv, Finset.sum_mul]
  simp only [smul_mul_assoc]

/-- The sum in the formula for the differential has finite support, even when `I` is infinite.

Blueprint: `lem:dr-polynomial-dga`. -/
theorem finite_support_pderiv_smul (p : MvPolynomial I k) (x : Forms k (MvPolynomial I k)) :
    (Function.support fun j : I =>
      pderiv j p • (diff k (X j : MvPolynomial I k) * x)).Finite := by
  refine p.vars.finite_toSet.subset fun j hj => ?_
  by_contra hnot
  exact hj (by simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars (mt Finset.mem_coe.2 hnot)])

/-- The formula for the differential on polynomial words, summing over all of `I`.

Blueprint: `lem:dr-polynomial-dga`. -/
theorem d_smul_word_X_eq_finsum (p : MvPolynomial I k) (l : List I) :
    d k (p • word (fun i => diff k (X i : MvPolynomial I k)) l) =
      ∑ᶠ j, pderiv j p • (diff k (X j : MvPolynomial I k) *
        word (fun i => diff k (X i : MvPolynomial I k)) l) := by
  rw [d_smul_word_X, finsum_eq_sum_of_support_subset]
  intro j hj
  by_contra hnot
  exact hj (by simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars (mt Finset.mem_coe.2 hnot)])

/-- The differentials of the variables span `Ω[k[X]⁄k]`, by Mathlib's basis. -/
private theorem span_range_D_X :
    Submodule.span (MvPolynomial I k)
      (Set.range fun i : I => D k (MvPolynomial I k) (X i)) = ⊤ := by
  have h := (KaehlerDifferential.mvPolynomialBasis k I).span_eq
  rwa [show ⇑(KaehlerDifferential.mvPolynomialBasis k I) =
    fun i : I => D k (MvPolynomial I k) (X i) from
      funext (KaehlerDifferential.mvPolynomialBasis_apply k I)] at h

namespace Forms

variable {k}

/-- Induction over the forms on a polynomial ring: it suffices to treat the polynomial words
`p dX_{i₁} ∧ ⋯ ∧ dX_{iₙ}` and sums.

Blueprint: `lem:dr-polynomial-dga`. -/
@[elab_as_elim]
theorem induction_X {p : Forms k (MvPolynomial I k) → Prop}
    (word : ∀ (q : MvPolynomial I k) (l : List I),
      p (q • word (fun i => diff k (X i : MvPolynomial I k)) l))
    (add : ∀ x y, p x → p y → p (x + y))
    (x : Forms k (MvPolynomial I k)) : p x := by
  refine DirectSum.Decomposition.inductionOn
    (fun n : ℕ => ⋀[MvPolynomial I k]^n Ω[MvPolynomial I k⁄k]) ?_ ?_ add x
  · simpa using word 0 []
  · rintro n ⟨y, hy⟩
    induction hy using exteriorPower_induction_of_span (span_range_D_X k) with
    | word q l _ _ => exact word q l
    | zero => simpa using word 0 []
    | add y _ z _ hy hz => exact add y z hy hz

end Forms

/-- The formula on polynomial words determines the differential among additive operators.

Blueprint: `lem:dr-polynomial-dga`. -/
theorem eq_d_of_smul_word_X (f : Forms k (MvPolynomial I k) →+ Forms k (MvPolynomial I k))
    (hf : ∀ (p : MvPolynomial I k) (l : List I),
      f (p • word (fun i => diff k (X i : MvPolynomial I k)) l) =
        ∑ j ∈ p.vars, pderiv j p • (diff k (X j : MvPolynomial I k) *
          word (fun i => diff k (X i : MvPolynomial I k)) l))
    (x : Forms k (MvPolynomial I k)) : f x = d k x := by
  induction x using Forms.induction_X with
  | word p l => rw [hf, d_smul_word_X]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end OrlikSolomon.DeRham
