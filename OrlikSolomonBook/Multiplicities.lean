/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "Combinatorial multiplicities" =>
%%%
tag := "multiplicities"
file := "multiplicities"
htmlSplit := .never
%%%

The recursive basis of {bp "thm:cohom-basis"}[] can be counted, and the count depends only on which intersections are nonempty and on their dimensions.
So how many copies of each coefficient group occur in each cohomology group is a combinatorial invariant of the arrangement.

# The polynomials

The polynomials are defined by sums over subsets of the arrangement, not over its intersection poset, and this makes the deletion–restriction recursion direct.
The second formula is a genuine polynomial, which avoids the formal negative exponents of the usual expression $`(-t)^n\chi_{\mathcal{A}}(-t^{-1})`.

:::node "def:polynomials" (decl := OrlikSolomon.Arrangement.characteristicPolynomial) (decl := OrlikSolomon.Arrangement.poincarePolynomial) (decl := OrlikSolomon.Arrangement.characteristicPolynomial_eq_sum) (decl := OrlikSolomon.Arrangement.poincarePolynomial_eq_sum) (decl := OrlikSolomon.Arrangement.bettiNumber) (decl := OrlikSolomon.Arrangement.natCast_bettiNumber)
Over $`\mathbb{Z}`, define
$$`\chi_{\mathcal{A}}(T)=\sum_{\substack{S\subseteq\mathcal{A}\\\bigcap S\ne\varnothing}}(-1)^{|S|}T^{\dim\bigcap S},`
$$`P_{\mathcal{A}}(t)=\sum_{\substack{S\subseteq\mathcal{A}\\\bigcap S\ne\varnothing}}(-1)^{|S|+\operatorname{codim}\bigcap S}t^{\operatorname{codim}\bigcap S},`
and let $`b_q(\mathcal{A})` be the coefficient of $`t^q` in $`P_{\mathcal{A}}`.
The natural Betti numbers are defined only after nonnegativity is proved, and casting them to integers recovers these coefficients.
:::

# Deletion and restriction

To compare the sums for $`\mathcal{A}` and for its deletion and restriction, separate the subsets that contain $`H`.
An old hyperplane with empty trace on $`H` makes the intersection empty, so it contributes nothing.
The other subsets are grouped by the set of distinct traces that they produce.
Several old hyperplanes can have the same trace, and for a fiber of $`m>0` equal traces
$$`\sum_{\varnothing\ne S\subseteq\{1,\ldots,m\}}(-1)^{|S|}=-1,`
so each fiber behaves like a single hyperplane of the restriction.
Multiplying over fibers gives the coefficient for each subset of the restriction.
Codimension in the original space is one more than codimension in $`H`, which gives the factor of $`t` in the recursion for $`P`.

:::node "lem:polynomial-recursion" (decl := OrlikSolomon.Arrangement.characteristicPolynomial_empty) (decl := OrlikSolomon.Arrangement.poincarePolynomial_empty) (decl := OrlikSolomon.Arrangement.characteristicPolynomial_deletion_restriction) (decl := OrlikSolomon.Arrangement.poincarePolynomial_deletion_restriction) (decl := OrlikSolomon.Arrangement.poincarePolynomial_coeff_nonneg)
For the empty arrangement, $`\chi=T^n` and $`P=1`.
In general $`\chi_{\mathcal{A}}=\chi_{\mathcal{A}'}-\chi_{\mathcal{A}''}` and $`P_{\mathcal{A}}=P_{\mathcal{A}'}+tP_{\mathcal{A}''}`, so all coefficients of $`P_{\mathcal{A}}` are nonnegative.
:::

# Counting the basis

The recursive basis has two disjoint parts: old words, which keep their length, and lifted restricted words, which gain one.
So the number of words of length $`q` satisfies the same recursion and the same initial condition as $`b_q`, and the two agree.

Since $`H^{p,w}(U_{\mathcal{A}})\simeq\operatorname{OS}_R^p(\mathcal{A})\otimes_R B_{w-p}`, it follows that this group is a direct sum of $`b_p(\mathcal{A})` copies of $`B_{w-p}`.
This isomorphism depends on the basis and is not canonical, whereas {bp "cor:ordinary"}[the Orlik–Solomon presentation] is.

Over the zero ring, these statements do not determine $`b_q`.
Every group vanishes there, every family of words of admissible length is a basis, and so neither the module statements nor the existence of a basis with this word count pins the number down.
For the two points of the line over $`\mathbb{F}_2` with zero coefficients, {name OrlikSolomon.DegenerateExamples.different_basis_sizes_zeroTheory_twoPoints}`different_basis_sizes_zeroTheory_twoPoints` shows that one group has bases with zero and with two vectors.
There $`b_q` is simply the coefficient of the polynomial, and its link to words is the recursive construction in the proof: {name OrlikSolomon.OrdinaryTheory.LogMonomialBasis.empty}`LogMonomialBasis.empty`, {name OrlikSolomon.OrdinaryTheory.LogMonomialBasis.ofDeletion}`ofDeletion` and their word-count lemmas.

As for the values, two disjoint hyperplanes, such as two parallel lines or two points of a line, give $`1+2t` by {name OrlikSolomon.Arrangement.poincarePolynomial_pair_disjoint}`poincarePolynomial_pair_disjoint`.
Three concurrent lines in the plane give $`1+3t+2t^2`, and three lines in general position give $`1+3t+3t^2`.
Here are the statements of the last two, for any three hyperplanes with these incidences.

```lean -show
open OrlikSolomon
open scoped Classical
universe u
variable {k : Type u} [Field k]
  {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {𝒜 : Arrangement k V}
  {H K L : AffineSubspace k V}
```

```lean
example (h𝒜 : 𝒜.hyperplanes = {H, K, L})
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L)
    (htrace : H ⊓ K = H ⊓ L) (hbot : H ⊓ K ≠ ⊥) :
    𝒜.poincarePolynomial =
      1 + 3 * Polynomial.X + 2 * Polynomial.X ^ 2 :=
  Examples.poincarePolynomial_three_same_trace
    𝒜 h𝒜 hHK hHL hKL htrace hbot

example (h𝒜 : 𝒜.hyperplanes = {H, K, L})
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L)
    (h₁ : H ⊓ K ≠ ⊥) (h₂ : H ⊓ L ≠ ⊥) (h₃ : K ⊓ L ≠ ⊥)
    (htriple : H ⊓ (K ⊓ L) = ⊥) :
    𝒜.poincarePolynomial =
      1 + 3 * Polynomial.X + 3 * Polynomial.X ^ 2 :=
  Examples.poincarePolynomial_three_nonconcurrent
    𝒜 h𝒜 hHK hHL hKL h₁ h₂ h₃ htriple
```

The first of these exercises the duplicate traces in the restriction, which must be counted once.
In the second, the triple intersection is empty, so there is no boundary relation in degree two for that triple, and only $`e_1e_2e_3=0` in degree three.
The coordinate hyperplanes in dimension $`n` give $`(1+t)^n`, by {name OrlikSolomon.Examples.poincarePolynomial_coordinate_fin}`poincarePolynomial_coordinate_fin`.

:::node "thm:betti" (decl := OrlikSolomon.OrdinaryTheory.exists_logMonomialBasis) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.wordCount) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.gradingEquiv) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.diagonalBasis) (decl := OrlikSolomon.OrdinaryTheory.nonempty_grading_linearEquiv_bettiNumber) (decl := OrlikSolomon.OrdinaryTheory.nonempty_basis_grading_bettiNumber) (decl := OrlikSolomon.OrdinaryTheory.nonempty_basis_degree_bettiNumber)
The recursive basis has exactly $`b_q(\mathcal{A})` words of length $`q`.
Thus each $`H^{p,w}(U_{\mathcal{A}})` is a direct sum of $`b_p(\mathcal{A})` copies of $`B_{w-p}`, and the ordinary diagonal has an $`R`-basis of that cardinality.
:::

# The Möbius function

The usual form of these numbers, in terms of the Möbius function of the intersection poset, is a useful final combinatorial statement and is not used anywhere in the proof of the ring equivalence.
Group the alternating subset sum by its nonempty intersection $`X`, and call the resulting integer coefficient $`a_X`.
For each proper flat $`X`, summing these coefficients over flats containing $`X` is the alternating sum over subsets of the hyperplanes containing $`X`.
That set of hyperplanes is nonempty, so the sum is zero; for the ambient flat the sum is one.
These are exactly the defining equations of the Möbius function on the poset ordered by reverse inclusion, whose least element is the ambient space.
Mathlib's Möbius inversion identifies $`a_X=\mu(V,X)`, and weighting by dimension or codimension gives the two formulas.

:::node "lem:mobius" (decl := OrlikSolomon.Arrangement.IntersectionPoset) (decl := OrlikSolomon.Arrangement.mem_intersectionFlats) (decl := OrlikSolomon.Arrangement.IntersectionPoset.le_iff) (decl := OrlikSolomon.Arrangement.IntersectionPoset.carrier_bot) (decl := OrlikSolomon.Arrangement.IntersectionPoset.mobius) (decl := OrlikSolomon.Arrangement.sum_Iic_intersectionCoefficient) (decl := OrlikSolomon.Arrangement.intersectionCoefficient_eq_mobius) (decl := OrlikSolomon.Arrangement.characteristicPolynomial_eq_sum_mobius) (decl := OrlikSolomon.Arrangement.poincarePolynomial_coeff_eq_sum_mobius) (decl := OrlikSolomon.Arrangement.natCast_bettiNumber_eq_sum_mobius)
For the poset of nonempty intersections, ordered by reverse inclusion,
$$`\chi_{\mathcal{A}}(T)=\sum_X\mu(V,X)T^{\dim X},\qquad b_q=(-1)^q\sum_{\operatorname{codim}X=q}\mu(V,X).`
:::

# Projective arrangements

A nonempty projective arrangement has Betti numbers too, defined as those of any of its decones, and the polynomial of its cone is $`1+t` times their polynomial.
What they say about cohomology uses the projective complement, so they are treated in the next chapter, at {bp "cor:projective-betti"}[].
