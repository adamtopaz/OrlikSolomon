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

These tables are generated when the book is built, from the same boxes that appear in the chapters, and they list every labeled statement of the five blueprints.
Each blueprint is counted separately.
The main theorem does not depend on the de Rham instance, neither of them depends on the geometric refactor, and the algebraic and topological reconstruction layers build on these results.
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

The fourth blueprint formalizes cohomological hyperplane reconstruction.
Its 38 named groups contain 41 separately labeled statements: U01, U04 and L02 each contain a definition and a lemma, which have separate boxes and statuses.
All forty-one statements are formalized.
G01–G03 give coordinate geometry, A01 gives the degree-one generator basis and algebra generation, A02 gives the full degree-two exterior-quotient kernel, U03 gives full-dual coordinates and the contragredient action, U04 gives the determinant and universal centralizer with its configuration equations and paired diagram invariance, and U05 proves the local-ring primitive-coordinate criterion.
A02 identifies that kernel with the span of parallel-pair and guarded dependent-triple wedges, including zero coefficients and characteristic two.
A03 defines the marked quadratic and full graded automorphism groups and their faithful degree-one restriction, with one common target.
A04 identifies them with the actual degree-one/cup-kernel and full diagonal-cohomology diagrams for a supplied full geometric ordinary theory, preserving all actual arrows, scalar families and faithful degree-one restriction.
The characteristic-two and point-free-target consumers are likewise conditional on such a theory; they construct no new nonzero mod-2 realization.
G04–G06 construct the coefficient action, finite Galois orbits over algebraic extensions and cofinal stable arrangements with actual common-target marking maps.
C01–C03 give projective span preservation, separate affine coordinate bijections, and, in dimension at least two, the unique field automorphism from the prescribed fixed frame, over an arbitrary field.
U01–U02 give the literal universal free module, its finite-stage universal property and quadratic relation witnesses, and the induced diagram action preserving the common target component.
S02 constructs the direct Galois action on the full graded diagram from every defining OS relation, with identity on the one common target.
L01–L03 give the surjective trace map with exact kernel, the explicit decomposition product and all four annihilator identities, the unit-delta centralizer, and surjective restriction from a graph to the actual vertical module with inertia kernel.
L04 transfers graph coefficients over every commutative coefficient ring by cancelling only a specified unit.
L05 detects a unique unit-supported graph functional from the four stated conditions over a nonzero local ring in dimension at least two; its centralizer is the actual decomposition submodule.
P01–P02 recognize every coordinate-supported span intrinsically, derive its diagram invariance from the actual marking squares, and make restriction to its full dual equivariant.
I01–I04 recover the unique inertia permutation, preserve the actual trace kernels and affine/projective incidence, and fix each marked zero/one fiber and the full projective frame, with the explicit local/nonzero, dimension and zero-marking hypotheses.
C04 extracts the Galois homomorphism after descent from the generating marking constants; S01 gives its unique common primal scalar kernel on every stage and the common target.
S03 gives the canonical multiplicative equivalence between coefficient units times base-field automorphisms and the actual quadratic diagram, with both explicit inverse equations and the original common target.
S04 upgrades the same degree-one restriction to a multiplicative equivalence with the full graded group, acts by the scalar degree powers, and identifies both actual scalar quotients with the Galois group using explicit sections and inverse laws.
S05 proves the same quadratic and full graded classifications and both scalar quotients over arbitrary integral domains, with actual coefficient descent and agreement with the local constructions.
E01 transports both coefficient cases and scalar quotients to actual cohomology diagrams, with the logarithmic, whole-degree and common-target formulas.
E02 proves literal cofinal restriction is invertible after classification and gives the unique generator-preserving comparison between two eligible realizations, including all actual arrow, degree and cup-kernel squares.
E03 gives unconditional reconstruction for the actual ordinary de Rham diagram in characteristic zero, including both inverse laws, the k-linear covariant dlog formula, all ordinary degrees and one actual common target. Its comparisons untwist only the diagonal E^(q,q); no semilinear geometric pullback is asserted.
Final regression consumers pin binary and nilpotent local coefficients, actual common targets and both scalar quotients. A full disconnected-coefficient counterexample proves that the coefficient hypotheses cannot be replaced by an arbitrary commutative ring.
{ref "hyperplane-gt"}[Its chapter] explains the proved conditional reconstruction, the unconditional de Rham application and their precise hypotheses.

The fifth blueprint, topological hyperplane reconstruction (M9), has seventeen separately labelled statements T01–T17: thirteen formalized, zero partly formalized and four planned.
It proposes direct finite-stage topologies and upgrades of the existing reconstruction maps, scalar quotients, cofinal and realization comparisons, and the ordinary de Rham specialization.
Coefficient units are discrete; the Krull topology replaces pointwise convergence under the stated fixing condition, in particular for algebraic field extensions.
The pure, actual supplied-theory and constructed characteristic-zero ordinary diagram topologies, component continuity, group and separation properties, and complete-stage-and-target neighborhood bases are proved in every dimension.
Both pure groups are closed in their original ambient products for every commutative coefficient ring, and finite coefficients make both compact, without classification or algebraicity.

T05 proves the arrangement-free pointwise topological group and separation properties, exact normalized affine coefficient tests and the finite hyperplane/stage-kernel comparisons for $`n\geq1`.
T06 proves the exact Krull comparison criterion, its algebraic wrapper, actual normalized coefficient-field fixer equality and chosen-stage containment in every finite intermediate-field fixer for $`n\geq1`.
T04 proves the existing degree-one restriction is a topological embedding for arbitrary coefficients and dimensions, with continuous inverse whenever the map is bijective.
T07 makes the pointwise group compact under finite scalar orbits; supplied stable systems in positive dimension and algebraicity imply those orbits separately, with no normality or separability requirement.
T08 gives the actual rational-function system over every prime field, with finite nontrivial Galois group, indiscrete Krull and discrete pointwise/stage topologies, and proves noncontinuity of the actual M8 direct action and classification over binary coefficients.
T09 proves both continuity directions for the exact local/domain quadratic classifiers, with pointwise convergence or, under the fixing condition or algebraicity, Krull.
T10 proves both exact local/domain graded restriction homeomorphisms with no field-extension hypothesis and both full product classifiers for pointwise convergence, with explicit-condition and algebraic Krull wrappers.
T12 proves literal cofinal restriction is a topological embedding for arbitrary coefficients and dimensions, and upgrades all four existing local/domain quadratic/graded cofinal equivalences and their actual scalar quotients. It retains the single common target, has no algebraicity or union-closure hypothesis, and compares unrelated supplied families through the union of their selected families.
T14 proves the exact actual-to-presentation adapters and both scalar quotient homeomorphisms.
T11 proves the exact local/domain scalar quotient homeomorphisms, closedness and profiniteness, without algebraicity or finiteness of coefficient units for the pointwise result.
The exact old ordinary twists and their literal scalar quotient twists are homeomorphisms. New algebraic ordinary scalar and cofinal wrappers retain the old marking and dimension hypotheses. Final ordinary reconstruction, quotient-to-Galois and cofinal topological upgrades stay planned under T17; the four earlier blueprint counts are unchanged.
{ref "topological-reconstruction"}[Its chapter] records the topology, hypothesis and realization boundaries.

{statusOverview}
