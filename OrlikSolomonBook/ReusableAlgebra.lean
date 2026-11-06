/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "Reusable algebra" =>
%%%
tag := "algebra"
file := "algebra"
htmlSplit := .never
%%%

These results mention neither arrangements nor cohomology.
They are collected first because three features of the proof place unusual demands on them.
The rings involved are graded commutative but not commutative, so ordinary commutative algebra does not apply.
The number $`2` is never assumed to be invertible, since the theorem must hold with coefficients in $`\mathbb{Z}/2`.
And the second induction has to map out of an Orlik–Solomon algebra _linearly_, into a module that is not a ring.

# Gradings by submodules

The total cohomology $`C(X)` is a $`B`-algebra, but its pieces $`H^{p,w}(X)` are not $`B`-submodules, because multiplying by an element of $`B_v` adds $`v` to the weight.
They are $`R`-submodules, where $`R=B_0`.
So the maps in the proof are $`B`-linear, while the gradings they respect are by $`R`-submodules, and "homogeneous of shift $`a`" has to make sense for maps that are linear over a larger ring than the pieces.
The formalization makes it a property of a plain function, with no linearity in the definition.

The direct sums here have finite support.
A product over all degrees would be a different object, and the exactness arguments below use finite support: an element of $`C(X)` has finitely many homogeneous components, and each can be treated separately.

Homogeneous extraction is how the proof moves between total statements and individual groups.
If a homogeneous element has a preimage under a homogeneous map, then projecting the preimage to the right degree gives a homogeneous preimage, because a shift is a translation of $`\mathbb{Z}^2` and so exactly one component can contribute.
So exactness of total maps is the same as exactness in each shifted component.
This is what lets the axioms be stated for total cohomology, as three exactness conditions, while the first induction argues degree by degree when it needs to.

:::node "def:grading" (decl := GradedAlgebra) (decl := OrlikSolomon.IsHomogeneousOfShift)
An internal bigrading of an $`R`-algebra $`T` is a family of $`R`-submodules $`T_{p,w}`, for $`(p,w)\in\mathbb{Z}^2`, whose direct sum is $`T` through the inclusions, with $`1\in T_{0,0}` and $`T_{p,w}T_{q,v}\subseteq T_{p+q,w+v}`.
A homogeneous map of shift $`(a,b)` sends $`T_{p,w}` into $`T'_{p+a,w+b}`.

The formalization adds no new class for this: a bigrading is Mathlib's {name GradedAlgebra}`GradedAlgebra` with degrees in $`\mathbb{Z}^2`, so its statement is for a general index type.
:::

:::node "lem:extraction" (decl := OrlikSolomon.IsHomogeneousOfShift.exists_mem_preimage) (decl := OrlikSolomon.IsHomogeneousOfShift.ofBijective_symm) (decl := OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_mem) (decl := OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_component)
A homogeneous element in the range of a homogeneous map has a homogeneous preimage of the corresponding degree, a bijective homogeneous map has a homogeneous inverse, and exactness of composable homogeneous maps can be tested in each shifted component.
:::

# Signs, with nothing divided by two

Graded commutativity says that $`xy=(-1)^{pq}yx` for homogeneous $`x` and $`y` of cohomological degrees $`p` and $`q`.
The sign depends only on the cohomological degrees, not on the weights.
Since $`p` and $`q` are integers, possibly negative, the sign is a function on $`\mathbb{Z}` and not a power of $`-1` with an arbitrary exponent.

Over $`\mathbb{Z}/2` this condition says only that $`xy=yx`, and it says nothing about $`x^2`.
Over $`\mathbb{Z}` it gives $`2x^2=0` for $`x` of odd degree, which does not give $`x^2=0` if there is $`2`-torsion.
So that an odd class squares to zero does not follow from graded commutativity, and the proof can never use it as if it did.
Wherever a square vanishes, there is a separate reason.
For the class $`\tau` of the multiplicative group, {bp "lem:gm"}[the reason] is that $`C(\mathbb{G}_m)` has nothing in cohomological degree two.

This is why a family that should generate an exterior algebra has to satisfy two separate conditions, that $`x_i^2=0` for all $`i` and that $`x_ix_j+x_jx_i=0` for $`i\ne j`.
The universal property of the exterior algebra asks for more than this: _every_ vector, not only a basis vector, must map to an element of square zero.
Expanding the square of a combination gives
$$`\Bigl(\sum_i c_ix_i\Bigr)^2=\sum_i c_i^2x_i^2+\sum_{i<j}c_ic_j(x_ix_j+x_jx_i)=0.`
The diagonal terms vanish, the off-diagonal pairs cancel, and at no point has anything been divided by two.

:::node "lem:exterior-words" (decl := OrlikSolomon.span_range_word) (decl := OrlikSolomon.IsExteriorFamily.word_eq_zero_of_not_nodup) (decl := OrlikSolomon.IsExteriorFamily.word_perm) (decl := OrlikSolomon.IsExteriorFamily.word_mul_word_comm) (decl := OrlikSolomon.IsExteriorFamily.linearCombination_mul_self) (decl := OrlikSolomon.exteriorLift) (decl := OrlikSolomon.exteriorAlgHom_ext)
Ordered words in the generators span the exterior algebra over $`B` on a finite set.
A repeated letter gives zero, a permutation of a word multiplies it by the sign of the permutation, and any two words supercommute according to their lengths.
Square-zero, pairwise anticommuting elements of a $`B`-algebra extend uniquely to a map out of the exterior algebra.
:::

# Two universal properties of one quotient

The Orlik–Solomon algebra is a quotient of a noncommutative ring by a two-sided ideal.
The usual universal property is that algebra maps out of the quotient correspond to algebra maps that kill the relators.
That is enough to construct the realization map $`\Phi_{\mathcal{A}}`, but the deletion argument also needs to map out of the quotient _linearly_, into a module that is not a ring.

A linear map does not respect products, so killing the relators is not enough for it to descend.
It has to kill the whole relation submodule $`J(\mathcal{R})`, the span of all products $`arb`, and it suffices to check this for every $`a` and $`b` and every relator $`r`.
So the relation quotient is set up so that its underlying module is literally the module quotient by that span, and both universal properties are available for one object.
{ref "second-induction"}[The second induction] is the reason for this.
{bp "def:lift-map"}[The linear map it needs] kills the relators only after all their left and right contexts are expanded.

If the relators are homogeneous, then the quotient inherits the grading: every homogeneous component of $`arb` is a sum of contexts of homogeneous relators, so it lies in $`J(\mathcal{R})` too.
The same quotient also carries both a $`B`-algebra structure and a grading by $`R`-submodules, which is the situation of the first section of this chapter.

:::node "def:twosided" (decl := OrlikSolomon.relationSubmodule) (decl := OrlikSolomon.RelationQuotient) (decl := OrlikSolomon.RelationQuotient.quotientLinearEquiv)
For a possibly noncommutative $`B`-algebra $`T` and a set $`\mathcal{R}\subseteq T`, let $`J(\mathcal{R})` be the $`B`-span of all products $`arb` with $`a,b\in T` and $`r\in\mathcal{R}`.
The relation quotient is $`T/J(\mathcal{R})`, a ring and $`B`-algebra whose underlying module is the quotient by that submodule.
:::

:::node "lem:quotient-api" (decl := OrlikSolomon.mul_mem_relationSubmodule_left) (decl := OrlikSolomon.mul_mem_relationSubmodule_right) (decl := OrlikSolomon.relationSubmodule_le_iff) (decl := OrlikSolomon.RelationQuotient.liftAlgHomEquiv) (decl := OrlikSolomon.RelationQuotient.liftLinearEquiv) (decl := OrlikSolomon.RelationQuotient.gradedAlgebra)
The submodule $`J(\mathcal{R})` is stable under multiplication on both sides.
Algebra maps out of the quotient correspond to algebra maps killing every relator, while linear maps out of it correspond to linear maps killing every $`arb`.
Homogeneous relators induce a grading on the quotient.
:::
