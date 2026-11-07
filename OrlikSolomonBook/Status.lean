/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Status of the formalization" =>
%%%
tag := "status"
file := "status"
%%%

These tables are generated when the book is built, from the same boxes that appear in the chapters, and they list every node of the three blueprints.
Each is counted separately: the main theorem does not depend on the de Rham instance, neither of them depends on the planned geometric refactor, and in each case the dependence runs the other way.
A node is listed as formalized only if its box names Lean declarations.
For each of those, the build checks only that it exists, and that it depends on no `sorry` and on no axiom other than `propext`, `Classical.choice` and `Quot.sound`.
That the declarations cover the node's statement, and that the prose around them is accurate, are checked by human or agent review, not by the build.
So a row marked formalized records a reviewed judgement that rests on checked declarations, not a machine-checked claim about the node's wording.

Formalized does not mean unconditional.
Every result of the first blueprint that mentions cohomology is proved for an arbitrary value of the structure {ref "axioms"}[of the axioms].
The de Rham instance is one nonzero value, for fields of characteristic zero, and no value has been constructed in Lean for singular or $`\ell`-adic cohomology.
Instantiated at the de Rham instance, the affine and projective theorems become the unconditional statements {bp "cor:dr-affine"}[] and {bp "cor:dr-projective"}[] about algebraic de Rham cohomology over such fields.

Of the third blueprint, the geometric refactor, twenty-five nodes are formalized and two partly formalized: affine duality, principal divisor pairs, affine and projective complements as open subschemes, geometric cohomology, both affine transports, the logarithmic classes with the product with $`\mathbb{G}_m`, and the affine and projective structure theorems on actual arrangement opens, with the transport rule partly formalized. The de Rham realization through sheaf forms remains planned; {ref "geometric"}[its chapter] presents the remaining work.

{statusOverview}
