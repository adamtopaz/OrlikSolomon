/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Reusable algebra" =>
%%%
tag := "algebra"
file := "algebra"
%%%

These results mention neither arrangements nor cohomology.
They are collected first because three features of the proof place unusual demands on them.

The rings involved are graded commutative but not commutative, so ordinary commutative algebra does not apply.
The sign in graded commutativity depends only on the cohomological degree, and $`2` is never assumed to be invertible, since the theorem must hold with coefficients in $`\mathbb{Z}/2`.
Finally, the second induction needs to map out of an Orlik–Solomon algebra _linearly_, into a module that is not a ring, so a quotient with only an algebra universal property would not be enough.

:::node "def:grading" (decl := GradedAlgebra) (decl := OrlikSolomon.IsHomogeneousOfShift)
An internal bigrading of an $`R`-algebra $`T` is a family of $`R`-submodules $`T_{p,w}`, for $`(p,w)\in\mathbb{Z}^2`, whose direct sum is $`T` through the inclusions, with $`1\in T_{0,0}` and $`T_{p,w}T_{q,v}\subseteq T_{p+q,w+v}`.
The pieces are $`R`-submodules and not $`B`-submodules, because multiplying by $`B_v` changes the weight.
A homogeneous map of shift $`(a,b)` sends $`T_{p,w}` into $`T'_{p+a,w+b}`.
The formalization adds no new class for this: a bigrading is Mathlib's `GradedAlgebra` with degrees in $`\mathbb{Z}^2`, so the first statement below is for a general index type.
:::

:::node "lem:extraction" (decl := OrlikSolomon.IsHomogeneousOfShift.exists_mem_preimage) (decl := OrlikSolomon.IsHomogeneousOfShift.ofBijective_symm) (decl := OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_mem) (decl := OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_component)
A homogeneous element in the range of a homogeneous map has a homogeneous preimage of the corresponding degree, a bijective homogeneous map has a homogeneous inverse, and exactness of composable homogeneous maps can be tested in each shifted component.
This is what lets the proof move between total cohomology and the individual groups $`H^{p,w}`.
:::

:::node "def:twosided" (decl := OrlikSolomon.relationSubmodule) (decl := OrlikSolomon.RelationQuotient) (decl := OrlikSolomon.RelationQuotient.quotientLinearEquiv)
For a possibly noncommutative $`B`-algebra $`T` and a set $`\mathcal{R}\subseteq T`, let $`J(\mathcal{R})` be the $`B`-span of all products $`arb` with $`a,b\in T` and $`r\in\mathcal{R}`.
The relation quotient is $`T/J(\mathcal{R})`, a ring and $`B`-algebra whose underlying module is the quotient by that submodule.
:::

:::node "lem:quotient-api" (decl := OrlikSolomon.mul_mem_relationSubmodule_left) (decl := OrlikSolomon.mul_mem_relationSubmodule_right) (decl := OrlikSolomon.relationSubmodule_le_iff) (decl := OrlikSolomon.RelationQuotient.liftAlgHomEquiv) (decl := OrlikSolomon.RelationQuotient.liftLinearEquiv) (decl := OrlikSolomon.RelationQuotient.gradedAlgebra)
Algebra maps out of the quotient correspond to algebra maps killing every relator, while linear maps out of it correspond to linear maps killing every $`arb`.
Homogeneous relators induce a grading on the quotient.
The second universal property is the one that a standard algebra quotient does not provide, and it is the one the deletion argument uses.
:::

:::node "lem:exterior-words" (decl := OrlikSolomon.span_range_word) (decl := OrlikSolomon.IsExteriorFamily.word_eq_zero_of_not_nodup) (decl := OrlikSolomon.IsExteriorFamily.word_perm) (decl := OrlikSolomon.IsExteriorFamily.word_mul_word_comm) (decl := OrlikSolomon.IsExteriorFamily.linearCombination_mul_self) (decl := OrlikSolomon.exteriorLift) (decl := OrlikSolomon.exteriorAlgHom_ext)
Ordered words in the generators span the exterior algebra over $`B` on a finite set.
A repeated letter gives zero, a permutation of a word multiplies it by the sign of the permutation, and any two words supercommute according to their lengths.
Square-zero, pairwise anticommuting elements of a $`B`-algebra extend uniquely to a map out of the exterior algebra.
The last statement holds without any assumption on $`2`, because expanding the square of a sum makes the diagonal terms vanish and the off-diagonal pairs cancel.
:::
