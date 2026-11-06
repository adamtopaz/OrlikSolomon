/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Combinatorial multiplicities" =>
%%%
tag := "multiplicities"
file := "multiplicities"
%%%

The recursive basis of {bp "thm:cohom-basis"}[] can be counted, and the count depends only on which intersections are nonempty and on their dimensions.
The polynomials are defined by sums over subsets of the arrangement rather than over the intersection poset, and this makes the deletion–restriction recursion direct.
For example, three concurrent lines in the plane give $`P(t)=1+3t+2t^2`, three lines in general position give $`1+3t+3t^2`, and two parallel lines give $`1+2t`.

The isomorphisms that a choice of basis produces are not canonical, while the Orlik–Solomon presentation map is.

:::node "def:polynomials" (decl := OrlikSolomon.Arrangement.characteristicPolynomial) (decl := OrlikSolomon.Arrangement.poincarePolynomial) (decl := OrlikSolomon.Arrangement.characteristicPolynomial_eq_sum) (decl := OrlikSolomon.Arrangement.poincarePolynomial_eq_sum) (decl := OrlikSolomon.Arrangement.bettiNumber) (decl := OrlikSolomon.Arrangement.natCast_bettiNumber)
Over $`\mathbb{Z}`, define
$$`\chi_{\mathcal{A}}(T)=\sum_{\substack{S\subseteq\mathcal{A}\\\bigcap S\ne\varnothing}}(-1)^{|S|}T^{\dim\bigcap S},\qquad P_{\mathcal{A}}(t)=\sum_{\substack{S\subseteq\mathcal{A}\\\bigcap S\ne\varnothing}}(-1)^{|S|+\operatorname{codim}\bigcap S}t^{\operatorname{codim}\bigcap S},`
and let $`b_q(\mathcal{A})` be the coefficient of $`t^q` in $`P_{\mathcal{A}}`.
The natural Betti numbers are defined only after nonnegativity is proved; casting them to integers recovers these coefficients.
:::

:::node "lem:polynomial-recursion" (decl := OrlikSolomon.Arrangement.characteristicPolynomial_empty) (decl := OrlikSolomon.Arrangement.poincarePolynomial_empty) (decl := OrlikSolomon.Arrangement.characteristicPolynomial_deletion_restriction) (decl := OrlikSolomon.Arrangement.poincarePolynomial_deletion_restriction) (decl := OrlikSolomon.Arrangement.poincarePolynomial_coeff_nonneg)
For the empty arrangement, $`\chi=T^n` and $`P=1`.
In general $`\chi_{\mathcal{A}}=\chi_{\mathcal{A}'}-\chi_{\mathcal{A}''}` and $`P_{\mathcal{A}}=P_{\mathcal{A}'}+tP_{\mathcal{A}''}`, so all coefficients of $`P_{\mathcal{A}}` are nonnegative.
:::

:::node "thm:betti" (decl := OrlikSolomon.OrdinaryTheory.exists_logMonomialBasis) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.wordCount) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.gradingEquiv) (decl := OrlikSolomon.OrdinaryTheory.LogMonomialBasis.diagonalBasis) (decl := OrlikSolomon.OrdinaryTheory.nonempty_grading_linearEquiv_bettiNumber) (decl := OrlikSolomon.OrdinaryTheory.nonempty_basis_grading_bettiNumber) (decl := OrlikSolomon.OrdinaryTheory.nonempty_basis_degree_bettiNumber)
The recursive basis has exactly $`b_q(\mathcal{A})` words of length $`q`.
Thus each $`H^{p,w}(U_{\mathcal{A}})` is a direct sum of $`b_p(\mathcal{A})` copies of $`B_{w-p}`, and the ordinary diagonal has an $`R`-basis of that cardinality.
:::

:::node "lem:mobius"
For the poset of nonempty intersections, ordered by reverse inclusion,
$$`\chi_{\mathcal{A}}(T)=\sum_X\mu(V,X)T^{\dim X},\qquad b_q=(-1)^q\sum_{\operatorname{codim}X=q}\mu(V,X).`
This final combinatorial form is not used in the proof of the ring equivalence.
:::
