/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
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

These tables are generated when the book is built, from the same boxes that appear in the chapters, and they list every labeled statement of the four blueprints.
Each blueprint is counted separately.
The main theorem does not depend on the de Rham instance, neither of them depends on the geometric refactor, and the new reconstruction application builds on these results.
A node is listed as formalized only if its box names Lean declarations.
For each of those, the build checks only that it exists, and that it depends on no `sorry` and on no axiom other than `propext`, `Classical.choice` and `Quot.sound`.
That the declarations cover the node's statement, and that the prose around them is accurate, are checked by human or agent review, not by the build.
So a row marked formalized records a reviewed judgement that rests on checked declarations, not a machine-checked claim about the node's wording.

Formalized does not mean unconditional.
Every result of the first blueprint that mentions cohomology is proved for an arbitrary value of the structure {ref "axioms"}[of the axioms].
The de Rham instance is one nonzero value, for fields of characteristic zero, and no value has been constructed in Lean for singular or $`\ell`-adic cohomology.
Instantiated at the de Rham instance, the affine and projective theorems become the unconditional statements {bp "cor:dr-affine"}[] and {bp "cor:dr-projective"}[] about algebraic de Rham cohomology over such fields.

Of the third blueprint, the geometric refactor, forty nodes are formalized and two partly formalized: affine duality, principal divisor pairs, affine and projective complements as open subschemes, geometric cohomology, both affine transports, the supports-and-purity bridge, logarithmic classes with the product with $`\mathbb{G}_m`, sheaves of relative forms with affine evaluation, the affine and projective structure theorems on actual arrangement opens, and de Rham cohomology of smooth affine schemes with the de Rham instance on them and its unconditional corollaries for the actual open subschemes, together with the six worked geometric regressions.
The sheaf logarithmic residue sequence and its local quasi-isomorphism are proved separately; their affine comparison identifies the instance's residue and Gysin maps on global sheaf representatives.
The Cartesian node retains its Tor-sheaf and conormal statements, and the statement-by-statement transport rule remains partly formalized. {ref "geometric"}[Its chapter] gives the proved statements and the remaining clauses.

The fourth blueprint, cohomological hyperplane reconstruction, is in progress.
Its 38 named groups contain 41 separately labeled statements: U01, U04 and L02 each contain a definition and a lemma, which have separate boxes and statuses.
Fifteen statements are formalized.
G01–G03 give coordinate geometry, A01 gives the degree-one generator basis and algebra generation, A02 gives the full degree-two exterior-quotient kernel, U03 gives full-dual coordinates and the contragredient action, U04 defines the determinant and explicit-relation centralizer, and U05 proves the local-ring primitive-coordinate criterion.
A02 identifies that kernel with the span of parallel-pair and guarded dependent-triple wedges, including zero coefficients and characteristic two.
A03 defines the marked quadratic and full graded automorphism groups and their faithful degree-one restriction, with one common target.
G04–G06 construct the coefficient action, finite Galois orbits over algebraic extensions and cofinal stable arrangements with actual common-target marking maps.
C01–C03 give projective span preservation, separate affine coordinate bijections, and, in dimension at least two, the unique field automorphism from the prescribed fixed frame, over an arbitrary field.
One statement is partly formalized: U04's generic centralizer and coordinate calculations are proved, while its geometric relation generators and diagram specialization remain pending.
The other twenty-five statements are planned; the reconstruction theorem is not yet formalized.
{ref "hyperplane-gt"}[Its chapter] explains the proposed theorem, its hypotheses and the limits of the planned applications.

{statusOverview}
