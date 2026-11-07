/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "How the proof is organized" =>
%%%
tag := "organization"
file := "organization"
htmlSplit := .never
%%%

The proof consists of two separate inductions on the number of hyperplanes, with a construction between them.
This chapter gives the plan, explains why the two inductions cannot be merged, and follows one small example through every step.

# Deletion and restriction

Both inductions use the same device.
Pick a hyperplane $`H\in\mathcal{A}`, and let $`\mathcal{A}'=\mathcal{A}\setminus\{H\}` be the _deletion_.
Let the _restriction_ $`\mathcal{A}''` be the arrangement in $`H` of the nonempty intersections $`H\cap K` for $`K\in\mathcal{A}'`, with duplicates removed.
The equation $`f_H` cuts a smooth divisor $`U_{\mathcal{A}''}` out of $`U_{\mathcal{A}'}`, with open complement $`U_{\mathcal{A}}`, so the axioms give a long exact sequence relating the three.

Both smaller arrangements have fewer hyperplanes, but the restriction lives in a smaller ambient space.
So every inductive statement must quantify over all ambient spaces at once.
With the ambient space fixed, the statement would not supply its own induction hypothesis.

# The route through the book

:::table +header
*
 * Chapter
 * Input
 * Output
*
 * {ref "algebra"}[Reusable algebra]
 * nothing about arrangements or cohomology
 * gradings by submodules, exterior words with signs, and a quotient with both an algebra and a linear universal property
*
 * {ref "geometry"}[Geometry]
 * linear algebra and localization
 * arrangements, complements as coordinate rings, deletion, restriction and divisor pairs
*
 * {ref "axioms"}[The axioms]
 * nothing: this is the hypothesis
 * the structure of a cohomology theory, and a bridge from degreewise data
*
 * {ref "logarithms"}[Logarithmic classes]
 * the axioms and the pair $`(\mathbb{A}^1,0,\mathbb{G}_m)`
 * the class $`\tau` on $`\mathbb{G}_m`, and $`f\mapsto[f]=f^*\tau` with the identities of a logarithm
*
 * {ref "first-induction"}[First induction]
 * logarithmic classes and deletion pairs
 * generation by logarithmic monomials, vanishing outside $`0\le p\le n`, short exact deletion sequences, and a monomial basis
*
 * {ref "presentation"}[Realization]
 * the first induction, for all arrangements
 * the relations hold in cohomology, which gives a surjective map $`\Phi_{\mathcal{A}}`
*
 * {ref "second-induction"}[Second induction]
 * $`\Phi` and the short exact sequences
 * $`\Phi_{\mathcal{A}}` is injective, which is the main theorem
*
 * {ref "multiplicities"}[Multiplicities]
 * the recursive basis
 * the multiplicities in all the groups, by a deletion–restriction recursion
*
 * {ref "projective"}[Projective complements]
 * the affine theorem, applied to the central cone
 * the projective theorem, with a map defined using no hyperplane at infinity
*
 * {ref "de-rham"}[A de Rham instance]
 * the structure of the axioms, and the affine and projective theorems
 * a nonzero value of the structure, and the forms of those theorems for algebraic de Rham cohomology, with no hypothetical cohomology theory
*
 * {ref "geometric"}[Arrangements on schemes], in progress, with foundations, affine and projective complements as open subschemes, geometric axioms, affine transports, logarithmic classes and sheaves of forms with affine evaluation formalized
 * the affine and projective theorems, the de Rham instance, and Mathlib's schemes
 * the same theorems for cohomology theories on smooth schemes, with complements as open subschemes, and the de Rham instance on smooth affine schemes
:::

The axioms do not mention logarithmic classes, so the first step has to construct them.
The first induction then proves everything that can be said about cohomology alone: it does not mention the Orlik–Solomon algebra, and the library's module for it does not import the presentation.
That makes it the first real audit of the axioms.
Its short exact sequences are where the vanishing of the Gysin map is proved, rather than assumed.

# Why two inductions and not one

The relations of the Orlik–Solomon algebra hold in cohomology because each of them is pulled back from a low-dimensional auxiliary arrangement, where it holds because its degree exceeds the dimension.
These auxiliary arrangements are not smaller than $`\mathcal{A}` in any sense that an induction on $`|\mathcal{A}|` can use: they are built from the coordinate hyperplanes of an affine space containing the image of $`U_{\mathcal{A}}`, and they can have as many hyperplanes as $`\mathcal{A}`.
For the two points of the affine line, in the example below, the auxiliary arrangement is two points of a line again.
So the dimension bound must already be known for all arrangements when the relations are checked.

If the two inductions were merged into one, then the proof of the relations for $`\mathcal{A}` would appeal to a bound on an arrangement that the induction hypothesis does not cover.
Separating them removes the problem.
The first induction finishes for every arrangement, and only then is $`\Phi_{\mathcal{A}}` constructed.
The second induction then has $`\Phi` available for every arrangement, and proves its injectivity by comparing with the short exact sequences that the first induction has already produced.

The subtle point in the second induction is that this comparison takes place in a quotient of modules, not of rings.
{ref "second-induction"}[That chapter] explains why.

# One example, all the way through

Take the two points $`0` and $`1` of the affine line, so that $`U_{\mathcal{A}}` has coordinate ring $`k[x,1/x(x-1)]`.
Over $`k=\mathbb{F}_2` this scheme has no $`k`-points at all, and nothing below notices.

Delete $`H=\{0\}`.
Then $`\mathcal{A}'=\{\{1\}\}`, and $`H\cap\{1\}` is empty, so the restriction $`\mathcal{A}''` is the empty arrangement on the point $`H`.

The class $`\tau` lives on $`\mathbb{G}_m`, and translating by one gives $`C(U_{\mathcal{A}'})=B\oplus B[x-1]`.
On the point, $`C(U_{\mathcal{A}''})=B`.
The residue sends $`[x]` to $`1`, and $`[x]\,j^*\beta` to $`i^*\beta`.
So the residue is surjective, the Gysin map vanishes, and
$$`0\to C(U_{\mathcal{A}'})\to C(U_{\mathcal{A}})\to B\to0`
is short exact, which gives the $`B`-basis $`1,\ [x-1],\ [x]` of $`C(U_{\mathcal{A}})`.
The old equation $`x-1` restricts to the constant $`-1` on $`H`, and $`[-1]=0`, which is consistent with the restriction having no hyperplanes.

The relation is the empty-intersection relation $`e_0e_1=0`.
It holds because $`(x,x-1)` maps $`U_{\mathcal{A}}` to $`W\cap\mathbb{G}_m^2`, where $`W` is a line in $`\mathbb{A}^2` that misses the origin.
On this target the two coordinate classes are defined, and their product has degree two in dimension one, so it vanishes.
Over a nonzero coefficient ring the boundary relation $`e_1-e_0=0` does not hold, and it must not: the two classes are distinct members of a basis.
This is why the boundary relations are imposed only for nonempty intersections.

In the algebra, write $`A` and $`A'` for the Orlik–Solomon algebras of $`\mathcal{A}` and $`\mathcal{A}'`.
The module $`A/\operatorname{im}(A'\to A)` is generated by the class of $`e_0`, since $`e_0e_1=0` and $`e_0^2=0`.
The map $`s` of the second induction sends $`1\in\operatorname{OS}_B(\mathcal{A}'')=B` to that class.
Its composite with the residue is the identity of $`B`, and the comparison shows that $`\Phi_{\mathcal{A}}` is injective.
The Poincaré polynomial is $`1+2t`, and the monomial basis has one word of length zero and two of length one.

The library tests this example.
The complement over $`\mathbb{F}_2` has no points by {name OrlikSolomon.Sanity.isEmpty_algHom_twoPoints}`isEmpty_algHom_twoPoints`, and its ring is nonzero by {name OrlikSolomon.Sanity.nontrivial_complementRing_twoPoints}`nontrivial_complementRing_twoPoints`.
The relation is {name OrlikSolomon.RealizationExamples.logClass_mul_logClass_twoPoints}`logClass_mul_logClass_twoPoints`, and the group $`H^{1,1}` is free of rank two over $`\mathbb{F}_2` by {name OrlikSolomon.OrdinaryExamples.nonempty_basis_grading_twoPoints}`nonempty_basis_grading_twoPoints`.
The nonvanishing of $`e_1-e_0` over every nonzero coefficient ring is {name OrlikSolomon.PresentationExamples.twoPoints_difference}`twoPoints_difference`, and the polynomial is {name OrlikSolomon.Examples.poincarePolynomial_twoPoints}`poincarePolynomial_twoPoints`.
This is one of the blueprint's nine regression examples, and [the regression index](https://github.com/adamtopaz/OrlikSolomon/blob/main/docs/REGRESSIONS.md) lists the declarations that check each of them.
