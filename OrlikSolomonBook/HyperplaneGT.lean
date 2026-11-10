/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "Cohomological hyperplane reconstruction" =>
%%%
tag := "hyperplane-gt"
file := "hyperplane-gt"
htmlSplit := .never
%%%

*The coordinate and Galois geometry, low-degree algebra, marked diagrams and direct Galois action, universal module and diagram action, pure coordinate reconstruction, full-dual coordinates, universal centralizers, trace modules, local detection, intrinsic coordinate spans, the recovered incidence permutation and its fixed frame are formalized; the reconstruction theorem is planned.*
This chapter follows the project's [fourth blueprint](https://github.com/adamtopaz/OrlikSolomon/blob/main/blueprint/cohomological_hyperplane_gt_blueprint.tex), for milestone M8.
The blueprint has 38 named groups, G01–E03, containing 41 separately labeled statements.
U01, U04 and L02 each contain a definition and a lemma; each statement has its own box and status below.
Thirty-two boxes are formalized and nine remain planned.
G01–G03 identify hyperplanes with coefficient points and prove the incidence and coordinate graph formulas over every field, including characteristic two and dimension zero.
G04–G06 construct the coefficient Galois action, finite stable enlargements over algebraic extensions, and cofinal systems with actual marking arrows to a single common target.
A01 gives the canonical generator basis in degree one, its inclusion naturality and generation of the whole OS algebra, over every commutative coefficient ring.
A02 identifies the full degree-two kernel of the actual exterior quotient with the parallel-pair and guarded dependent-triple relation span, including zero coefficients and characteristic two.
A03 defines the marked quadratic and full graded automorphism groups, with one common target and faithful degree-one restriction, over arbitrary commutative coefficient rings.
S02 gives the direct Galois action on the full graded diagram, preserving every defining relation and acting identically on its one common target.
U01–U02 construct the universal free module, its explicit quadratic relation span and common finite-stage witnesses, and the induced diagram action retaining the common target component.
C01–C03 recover a unique field automorphism from an arbitrary projective collineation fixing the prescribed frame, over any field and in dimension at least two.
U03 and U05 give the full algebraic dual, its inverse-precomposition action and the local-ring primitive-coordinate criterion for arbitrary index types.
U04 gives the determinant and centralizer, their exact equations on all parallel pairs and guarded dependent triples, and paired invariance under the actual diagram action.
L01–L03 give the surjective trace map and its full kernel, inertia and decomposition with all four annihilator identities, and restriction from a graph to the actual vertical free span.
L04 transfers graph coefficients over any commutative ring by cancelling a specified unit; L05 detects the unique unit-supported graph functional over a nonzero local ring in dimension at least two.
P01–P02 recognize every supported coordinate span using commuting functionals, derive its diagram invariance from the marking squares, and give the actual equivariant restriction to its full dual.
I01–I04 recover the unique hyperplane permutation, transport actual incidence and projective lines, and fix every marked fiber and the full projective frame, over nonzero local coefficients with dimension at least two and zero among the marking constants.
The existing structure theorems and de Rham instance are inputs to the proposed application, rather than proofs of its new reconstruction statements.

# The proposed theorem and its inputs

Let $`k_0` be a perfect field, let $`k` be an algebraic closure of $`k_0`, and assume $`n\ge2`.
Choose $`S\subseteq k_0` containing zero and generating $`k_0` over its prime field.
The diagram consists of complements of a cofinal system of finite Galois-stable hyperplane arrangements in $`\mathbb A_k^n`, their inclusions, and marked maps to one common object $`T=\mathbb A_k^1\setminus\{0,1\}`.
The markings are the functions $`x_i-s` and $`x_i-x_j`, whenever their zero and one fibers have both been removed.

For a nonzero commutative local coefficient ring $`R`, or an integral domain $`R`, the proposed group equivalences are
$$`R^\times\times(k\simeq_{k_0}k)\simeq\operatorname{Aut}_2\simeq\operatorname{Aut}_{\mathrm{gr}},\qquad (u,\sigma)e_H=u e_{\sigma H}.`
Here $`\operatorname{Aut}_2` consists of natural degree-one linear equivalences preserving the full kernel of the exterior product into degree two.
The graded group consists of natural graded unital $`R`-algebra equivalences of the diagonal $`\bigoplus_{q\ge0}E^{q,q}`.
The scalar $`u` acts in degree $`q` by $`u^q`, and the proposed quotient by the central scalar subgroup is $`k\simeq_{k_0}k`.
These are abstract group equivalences; the blueprint supplies no topology on the groups.

The proof is first planned for an explicit Orlik–Solomon diagram, with no cohomology theory as an input.
The existing geometric structure theorem then identifies the diagram of a supplied {name OrlikSolomon.Geometric.OrdinaryTheory}`Geometric.OrdinaryTheory` with that explicit diagram.
Its hypotheses remain exactly C1–C5: products and grading, functorial pullbacks, the point and affine-line axioms, localization with residue and Gysin, and pair naturality with the right projection formula.
No field may assume reconstruction, the Orlik–Solomon theorem, logarithmic generation or an action of field automorphisms on a theory.

The final de Rham application is planned to use the already constructed characteristic-zero instance.
Singular and geometric étale cohomology remain conditional applications until their own C1–C5 data are constructed in Lean.

# Coordinates and finite stable systems

## G01: coefficient points

:::node "lem:g01" (decl := OrlikSolomon.HyperplaneGT.coefficientPointEquiv) (decl := OrlikSolomon.HyperplaneGT.coefficientForm_apply) (decl := OrlikSolomon.HyperplaneGT.zeroLocus_coefficientForm_eq_iff) (decl := OrlikSolomon.HyperplaneGT.coefficientPoint_eq_mk) (decl := OrlikSolomon.HyperplaneGT.hyperplaneOfCoefficientPoint_mk) (decl := OrlikSolomon.HyperplaneGT.coefficientForm_linear_ne_zero_iff)
An affine hyperplane in $`k^n` has an equation $`a_0+\sum_i a_i x_i=0` with nonzero normal part, unique up to nonzero scalar.
Its coefficient point identifies the set of hyperplanes with $`\mathbb P^n(k)\setminus\{[1:0:\cdots:0]\}`.
The equivalence includes equation independence and formulas for its inverse.
:::

## G02: parallel pairs and dependent triples

:::node "lem:g02" (decl := OrlikSolomon.HyperplaneGT.Parallel) (decl := OrlikSolomon.HyperplaneGT.DependentTriple) (decl := OrlikSolomon.HyperplaneGT.parallel_iff_normal_proportional) (decl := OrlikSolomon.HyperplaneGT.normals_linearIndependent_of_not_parallel) (decl := OrlikSolomon.HyperplaneGT.codim_inf_eq_two_of_not_parallel) (decl := OrlikSolomon.HyperplaneGT.dependentTriple_iff_equations_dependent) (decl := OrlikSolomon.HyperplaneGT.dependentTriple_iff_coefficientPoints_collinear) (decl := OrlikSolomon.HyperplaneGT.dependentTriple_iff_trace_eq)
Distinct hyperplanes with proportional normals are disjoint; otherwise they meet in codimension two.
For three distinct hyperplanes that are not parallel in pairs, codimension-two intersection, dependence of affine equations and collinearity of coefficient points are equivalent.
Equal nonempty traces on one hyperplane give the same dependent-triple condition.
An empty-intersection triple is excluded from this definition of dependence.
:::

## G03: vertical hyperplanes and graphs

:::node "lem:g03" (decl := OrlikSolomon.HyperplaneGT.isVertical_iff_of_isEquation) (decl := OrlikSolomon.HyperplaneGT.existsUnique_graph_of_omits_coordinate) (decl := OrlikSolomon.HyperplaneGT.graphProjectionEquiv) (decl := OrlikSolomon.HyperplaneGT.parallel_graphHyperplane_of_sub_eq_const) (decl := OrlikSolomon.HyperplaneGT.map_graphSubspace_inf) (decl := OrlikSolomon.HyperplaneGT.graphSubspace_inf_ne_bot_of_sub_linear_ne_zero)
Verticality over a coordinate subset means that all normal coefficients outside that subset vanish, independently of the chosen equation.
When precisely one coordinate is omitted, every nonvertical hyperplane has a unique graph equation, and projection identifies the graph with the remaining affine space.
Differences of graph functions determine parallelism and the projected common trace.
:::

## G04: the coefficient action

:::node "lem:g04" (decl := OrlikSolomon.HyperplaneGT.galoisAction) (decl := OrlikSolomon.HyperplaneGT.fieldAffineSubspace_iInf) (decl := OrlikSolomon.HyperplaneGT.fieldAffineSubspace_eq_bot_iff) (decl := OrlikSolomon.HyperplaneGT.codim_fieldAffineSubspace) (decl := OrlikSolomon.HyperplaneGT.isEquation_fieldAffineForm) (decl := OrlikSolomon.HyperplaneGT.coefficientPoint_galois_smul) (decl := OrlikSolomon.HyperplaneGT.parallel_galois_smul_iff) (decl := OrlikSolomon.HyperplaneGT.dependentTriple_galois_smul_iff) (decl := OrlikSolomon.HyperplaneGT.isVertical_galois_smul_iff)
Applying a $`k_0`-automorphism of $`k` to equation coefficients defines an action on hyperplanes.
It preserves empty intersections and their codimensions, parallel pairs, dependent triples and coordinate verticality, and agrees with the action on coefficient points.
This is constructed from equations; a natural action on a supplied cohomology theory is not an input.
:::

## G05: finite orbits

:::node "lem:g05" (decl := OrlikSolomon.HyperplaneGT.finite_orbit) (decl := OrlikSolomon.HyperplaneGT.stableClosure) (decl := OrlikSolomon.HyperplaneGT.subset_galoisClosure) (decl := OrlikSolomon.HyperplaneGT.isGaloisStable_stableClosure) (decl := OrlikSolomon.HyperplaneGT.fullCofinalSystem) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.exists_ge_finset)
Algebraicity of $`k/k_0` makes each hyperplane orbit finite: the coefficients of any one fixed equation have only finitely many simultaneous conjugates, bounded by finite minimal-polynomial root sets.
Every finite set therefore has a finite stable enlargement, and finite stable arrangements form a cofinal directed system.
This step itself does not use perfectness.
:::

## G06: the finite index system and markings

:::node "def:g06" (decl := OrlikSolomon.HyperplaneGT.CofinalSystem) (decl := OrlikSolomon.HyperplaneGT.Marking) (decl := OrlikSolomon.HyperplaneGT.Marking.function) (decl := OrlikSolomon.HyperplaneGT.Marking.fiber) (decl := OrlikSolomon.HyperplaneGT.Marking.parallel_zero_one) (decl := OrlikSolomon.HyperplaneGT.Marking.galois_smul_fiber) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.exists_ge_markings) (decl := OrlikSolomon.HyperplaneGT.markingTarget) (decl := OrlikSolomon.HyperplaneGT.Marking.algebraicMap) (decl := OrlikSolomon.HyperplaneGT.Marking.algebraicMap_comp_inclusion)
A cofinal system consists of finite stable arrangements such that every finite set of hyperplanes lies in some member; its morphisms are inclusions.
The tagged markings $`x_i-s` and $`x_i-x_j` have distinct zero and one fibers, both fixed by the Galois group.
When both fibers belong to a stage, their function defines an actual localized coordinate-algebra pullback from the single two-puncture target $`T`, sending $`t` and $`t-1` to the corresponding marking units.
The inclusion/marking square holds as an equation of actual morphisms.
The scheme-open and cohomology comparisons are separate parts of A04.
Cofinality supplies common upper stages; a chosen subsystem need not be closed under unions.
:::

# Finite degree-one and degree-two diagrams

## A01: the canonical degree-one basis

:::node "lem:a01" (decl := OrlikSolomon.HyperplaneGT.osDegreeOneEquiv) (decl := OrlikSolomon.HyperplaneGT.coe_osDegreeOneEquiv_apply) (decl := OrlikSolomon.HyperplaneGT.osDegreeOneEquiv_naturality) (decl := OrlikSolomon.HyperplaneGT.osDegreeOneBasis) (decl := OrlikSolomon.HyperplaneGT.osDegreeOneEquiv_symm_generator) (decl := OrlikSolomon.HyperplaneGT.exists_os_word_sum) (decl := OrlikSolomon.HyperplaneGT.adjoin_range_osGenerator)
For every finite arrangement $`A` over a field and every commutative coefficient ring $`R`, the generator map $`R^{(A)}\to\operatorname{OS}_R^1(A)` is a linear equivalence natural under inclusions.
The whole algebra is generated by these degree-one elements and scalars.
The statement includes zero coefficients and does not require a dimension over $`R`.
:::

## A02: the full quadratic kernel

:::node "thm:a02" (decl := OrlikSolomon.HyperplaneGT.osExteriorSquareMap) (decl := OrlikSolomon.HyperplaneGT.quadraticRelationSpan) (decl := OrlikSolomon.HyperplaneGT.quadraticKernel_eq_span) (decl := OrlikSolomon.HyperplaneGT.coe_osExteriorDifferencePair) (decl := OrlikSolomon.HyperplaneGT.osExteriorSquareMap_naturality)
Under A01, the kernel of $`\bigwedge_R^2R^{(A)}\to\operatorname{OS}_R^2(A)` is spanned by $`e_H\wedge e_K` for parallel pairs and $`(e_H-e_L)\wedge(e_K-e_L)` for dependent triples.
The proof extracts the degree-two part of the actual relation quotient; higher homogeneous relators contribute zero in that degree.
The quotient is surjective onto degree two and natural under inclusions, over every commutative coefficient ring and in every ambient dimension.
This does not assert that all higher Orlik–Solomon relations are generated by quadratic ones.
:::

## A03: the explicit finite diagram

:::node "def:a03" (decl := OrlikSolomon.HyperplaneGT.Marking.basisMap) (decl := OrlikSolomon.HyperplaneGT.Marking.basisMap_quadraticRelationSpan) (decl := OrlikSolomon.HyperplaneGT.Marking.osMap) (decl := OrlikSolomon.HyperplaneGT.markingTarget_exteriorSquareMap_eq_zero) (decl := OrlikSolomon.HyperplaneGT.quadraticDiagramAutSubgroup) (decl := OrlikSolomon.HyperplaneGT.gradedDiagramAutSubgroup) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.toQuadratic) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.toQuadratic_injective)
At a finite stage set $`M_A=R^{(A)}` and let $`Q_A` be A02's explicit relation span.
At the common target set $`M_T=R^{\{0,1\}}` and $`Q_T=\bigwedge^2M_T`.
Inclusions preserve labels, and marking pullback sends the ordered target basis to its zero and one fiber labels.
A diagram automorphism is a compatible family of linear equivalences preserving each full relation submodule by equality, so that inverses also preserve it.
The full graded group uses the existing OS algebras and every homogeneous degree, with actual presentation marking maps from the same two-puncture target.
Its restriction to the quadratic group is faithful by generation in degree one; no extension or classification theorem is asserted here.
:::

## A04: comparison with a supplied theory

:::node "thm:a04"
For a supplied C1–C5 theory, its degree-one modules and full cup kernels form a diagram isomorphic to A03, sending $`e_H` to $`[f_H]` and the target basis to $`[t]`, $`[t-1]`.
The canonical diagonal algebra equivalences are also natural for every inclusion and marking, giving an isomorphism of the full graded diagrams.
Marking naturality is proved on generators using logarithmic pullback, rather than assumed for extra diagram arrows.
:::

# The universal module and its algebraic dual

## U01: finite support and the relation span

:::node "def:u01" (decl := OrlikSolomon.HyperplaneGT.finiteStageMap) (decl := OrlikSolomon.HyperplaneGT.range_finiteStageMap) (decl := OrlikSolomon.HyperplaneGT.universalQuadraticRelationSpan)
Let $`M=R^{(\mathcal H)}` be the free module on all hyperplanes, with basis $`e_H`.
Each finite-stage module embeds by extension by zero, with image exactly the vectors supported on that stage.
Define $`Q\subseteq\bigwedge^2M` to be the span of all parallel-pair and dependent-triple relators.
:::

:::node "lem:u01" (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.exists_stage_vectors) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.finiteStageMap_eq_iff) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.universalLift) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.universalLift_unique) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.mem_universalQuadraticRelationSpan_iff) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.exists_stage_relations) (decl := OrlikSolomon.HyperplaneGT.map_quadraticRelationSpan_finiteStageMap_le)
The finite-stage embeddings exhibit $`M` as the direct limit of the degree-one diagram.
Every finite sum of generators of $`Q` comes from some $`Q_A`, and every image of $`Q_A` lies in $`Q`.
This uses finite support and common upper stages, without an injectivity claim about degree-two cohomology maps.
:::

## U02: the induced universal equivalence

:::node "lem:u02" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.universalEquiv) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_universalQuadraticRelationSpan) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_range_finiteStageMap) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.universalEquiv_marking) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.universalAction) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.ext_of_universalEquiv)
A quadratic-diagram automorphism induces an equivalence of $`M` preserving $`Q` and every finite-stage submodule, with the common marked source still equivariant.
This construction is a group homomorphism, and its universal map together with the component at $`T` determines the original family.
The universal automorphisms retain these stage and marking conditions.
:::

## U03: product coordinates on the dual

:::node "lem:u03" (decl := OrlikSolomon.HyperplaneGT.dualCoordinates) (decl := OrlikSolomon.HyperplaneGT.dualCoordinates_symm_apply) (decl := OrlikSolomon.HyperplaneGT.dualCoordinates_ext) (decl := OrlikSolomon.HyperplaneGT.finsupp_eq_of_dual_eval_eq) (decl := OrlikSolomon.HyperplaneGT.dualAction) (decl := OrlikSolomon.HyperplaneGT.dualAction_apply_apply)
The algebraic dual $`P=\operatorname{Hom}_R(M,R)` is the full product $`\prod_H R`, by evaluation on basis vectors; its inverse evaluates a finite supported sum.
Evaluation separates vectors and functionals.
The left dual action is contragredient, $`g\lambda=\lambda\circ g^{-1}`, and satisfies $`(g\lambda)(gm)=\lambda(m)`.
No topology or double-dual equivalence is used.
:::

## U04: commuting functionals

:::node "def:u04" (decl := OrlikSolomon.HyperplaneGT.dualDeterminant) (decl := OrlikSolomon.HyperplaneGT.dualDeterminant_ιMulti_apply) (decl := OrlikSolomon.HyperplaneGT.Commutes) (decl := OrlikSolomon.HyperplaneGT.centralizer)
For $`\lambda,\mu\in P`, the determinant $`d_{\lambda,\mu}(a,b)=\lambda(a)\mu(b)-\lambda(b)\mu(a)` is alternating and descends to $`\bigwedge^2M`.
Define $`\lambda\sim\mu` when this exterior map annihilates $`Q`, and let $`C(\lambda)` be the set of such $`\mu`.
:::

:::node "lem:u04" (decl := OrlikSolomon.HyperplaneGT.centralizer) (decl := OrlikSolomon.HyperplaneGT.commutes_universalQuadraticRelationSpan_iff) (decl := OrlikSolomon.HyperplaneGT.mem_centralizer_universalQuadraticRelationSpan_iff) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.dualAction) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.commutes_dualAction_iff) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_centralizer_dualAction)
The centralizer $`C(\lambda)` is a submodule.
Commuting is equivalent to the determinant equations on every parallel pair and every dependent triple, and is preserved in both directions by the paired universal and dual actions.
The relation submodule is the literal universal quadratic span from U01, and the action is the induced diagram action from U02 composed with U03's inverse precomposition.
The paired dual equivalence carries the entire centralizer onto the transformed centralizer.
Alternation follows by subtracting equal terms, including in characteristic two.
:::

## U05: primitive functionals over a local ring

:::node "lem:u05" (decl := OrlikSolomon.HyperplaneGT.Primitive) (decl := OrlikSolomon.HyperplaneGT.primitive_iff_unit_coordinate) (decl := OrlikSolomon.HyperplaneGT.primitive_comp_linearEquiv_iff) (decl := OrlikSolomon.HyperplaneGT.primitive_dualAction_iff)
Over a nonzero local ring, a functional $`M\to R` is surjective exactly when some basis coordinate is a unit.
Surjectivity is invariant under precomposition by a linear equivalence.
Primitive means surjectivity, rather than a residue-field test on the infinite product.
:::

# Traces, centralizers and local detection

## L01: the trace map and its kernel

:::node "lem:l01" (decl := OrlikSolomon.HyperplaneGT.traceLabel_eq_none_iff) (decl := OrlikSolomon.HyperplaneGT.traceLabel_eq_some_iff) (decl := OrlikSolomon.HyperplaneGT.traceLabel_surjective) (decl := OrlikSolomon.HyperplaneGT.traceMap) (decl := OrlikSolomon.HyperplaneGT.traceMap_surjective) (decl := OrlikSolomon.HyperplaneGT.traceKernel_eq_span)
For a fixed hyperplane $`H`, let $`U_H` consist of vectors whose coefficient at $`H` vanishes.
The trace map sends $`e_K` to zero for a parallel hyperplane and to the basis vector of $`H\cap K` otherwise.
It is onto the free module on hyperplanes of $`H`, and its kernel $`U_H^1` is spanned by empty-trace labels and differences of labels with the same nonempty trace.
The latter are precisely the dependent-triple differences from G02.
:::

## L02: inertia and decomposition

:::node "def:l02" (decl := OrlikSolomon.HyperplaneGT.inertia) (decl := OrlikSolomon.HyperplaneGT.decomposition)
Define $`I_H=R\delta_H`.
Let $`D_H` consist of functions zero on hyperplanes parallel to $`H` and constant on each nonempty trace fiber; the value at $`H` is unrestricted.
:::

:::node "lem:l02" (decl := OrlikSolomon.HyperplaneGT.traceDomain_dualAnnihilator) (decl := OrlikSolomon.HyperplaneGT.traceKernel_dualAnnihilator) (decl := OrlikSolomon.HyperplaneGT.inertia_dualCoannihilator) (decl := OrlikSolomon.HyperplaneGT.decomposition_dualCoannihilator) (decl := OrlikSolomon.HyperplaneGT.decompositionEquiv) (decl := OrlikSolomon.HyperplaneGT.ker_decompositionTrace) (decl := OrlikSolomon.HyperplaneGT.centralizer_unit_smul_delta)
Under evaluation, $`I_H=\operatorname{Ann}(U_H)` and $`D_H=\operatorname{Ann}(U_H^1)`, with reverse annihilators $`U_H` and $`U_H^1` respectively.
There is an explicit equivalence $`D_H\simeq R\times R^{\mathcal H(H)}`, whose second projection has kernel $`I_H`.
For every unit $`u`, one has $`C(u\delta_H)=D_H`.
These identities are proved directly from trace coordinates.
The trace-coordinate factor is a full function space, and the identities hold over arbitrary commutative coefficient rings, including the zero ring.
:::

## L03: projection from a graph

:::node "lem:l03" (decl := OrlikSolomon.HyperplaneGT.verticalTraceEquiv) (decl := OrlikSolomon.HyperplaneGT.verticalRestriction) (decl := OrlikSolomon.HyperplaneGT.map_decomposition_verticalRestriction) (decl := OrlikSolomon.HyperplaneGT.ker_verticalRestriction_inf_decomposition) (decl := OrlikSolomon.HyperplaneGT.verticalRestriction_delta)
Let $`z` omit one coordinate, and restrict dual functions to the hyperplanes vertical over $`z` by $`p_z:P\to P_z`.
For a graph $`H` over $`z`, the restriction $`D_H\to P_z` is onto with kernel $`I_H`, and $`p_z(\delta_H)=0`.
The graph identifies each hyperplane of its base with exactly one vertical trace.
:::

## L04: the local transfer calculation

:::node "lem:l04" (decl := OrlikSolomon.eq_of_unit_transfer) (decl := OrlikSolomon.HyperplaneGT.exists_vertical_transfer_pair) (decl := OrlikSolomon.HyperplaneGT.centralizerVerticalRestriction) (decl := OrlikSolomon.HyperplaneGT.local_transfer)
Suppose $`p_z\lambda=0`, the map $`C(\lambda)\to P_z` is onto, and $`\lambda_{H_0}` is a unit for a graph $`H_0`.
Then a graph distinct and parallel to $`H_0` has the same value under $`\lambda` as any graph distinct from and meeting $`H_0`.
The calculation derives two distinct actual vertical trace labels and cancels only the specified unit coordinate.
The coefficient ring may be zero and need not be local or a domain; the projection target is the full dual of the actual supported vertical module.
:::

## L05: detecting one supported coordinate

:::node "thm:l05" (decl := OrlikSolomon.HyperplaneGT.local_detection_iff) (decl := OrlikSolomon.HyperplaneGT.existsUnique_unit_delta_of_local_detection) (decl := OrlikSolomon.HyperplaneGT.unit_smul_lapply_eq_iff)
For $`n\ge2` and nonzero local $`R`, a functional is $`u\delta_H` for a unit $`u` and a graph $`H` exactly when it is primitive, vanishes under $`p_z`, vanishes at some graph coordinate, and has surjective centralizer projection to $`P_z`.
The graph and unit are unique, and its centralizer is $`D_H`.
No stronger quotient-isomorphism hypothesis is added.
Primitivity is literal surjectivity of the functional, and the centralizer uses the actual universal quadratic relation span.
The dimension bound is necessary: over geometric $`\mathbb{F}_3` in dimension one and coefficient $`\mathbb{F}_2`, a sum of two distinct point deltas satisfies all four conditions but has two nonzero support coordinates.
:::

# Recognizing the coordinate spans

## P01: intrinsic recognition

:::node "lem:p01" (decl := OrlikSolomon.HyperplaneGT.coordinatePlane) (decl := OrlikSolomon.HyperplaneGT.verticalRestriction_surjective) (decl := OrlikSolomon.HyperplaneGT.ker_verticalRestriction) (decl := OrlikSolomon.HyperplaneGT.exists_coordinateSpan_detector) (decl := OrlikSolomon.HyperplaneGT.coordinateSpan_recognition)
Let $`M_z` be the span of hyperplanes using only coordinates in $`z`, and let $`L_w=Re_{w=0}+Re_{w=1}` for $`w\notin z`.
A vector $`a` lies in $`M_{z\cup\{w\}}` exactly when $`d_{\lambda,\mu}(a\wedge b)=0` for every $`b\in L_w` and every commuting pair in $`\operatorname{Ann}(M_z)`.
This recovers coordinate spans from the given relation and marking data, over any commutative coefficient ring, including the zero ring.
Restriction to every supported coordinate span is surjective, with its actual evaluation annihilator as kernel.
:::

## P02: invariance and the dual quotient

:::node "prop:p02" (decl := OrlikSolomon.HyperplaneGT.Marking.plane) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_markingPlane) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_verticalModule) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_verticalAnnihilator) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.verticalAction) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.verticalDualAction) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.verticalRestriction_dualAction)
Assume that the marking constants contain zero. Every diagram automorphism preserves $`M_z` for every coordinate subset $`z`.
Its dual therefore induces an equivalence on $`P_z` making restriction $`p_z` equivariant.
The proof uses P01 and the actual common-target marking squares. Restricting the universal equivalence to the invariant supported module gives the induced inverse-precomposition action on its full dual and the restriction square.
This agrees with the explicit surjective-restriction quotient construction and uses no exactness assertion about arbitrary dualization.
:::

# Hyperplane permutation and incidence

Throughout I01–I04, the coefficient ring is nonzero and local, the dimension is at least two, and the marking constants contain zero.
A supplied cofinal system is sufficient; these steps impose no perfectness, algebraicity or generation condition on the field extension or the marking set.

## I01: the recovered permutation

:::node "prop:i01" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplanePerm) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplaneUnit) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.dualAction_delta) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.universalEquiv_single) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_inertia) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_decomposition) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_generatorLine) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplaneAction) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplanePerm_unique)
Over a nonzero local coefficient ring, each diagram automorphism has a unique hyperplane permutation $`\pi_g` satisfying $`gI_H=I_{\pi_gH}`, $`gD_H=D_{\pi_gH}` and $`g(Re_H)=Re_{\pi_gH}`.
These permutations respect composition.
The dual action sends each coordinate delta to a unit multiple at the recovered label; the primal generator uses the same label and the inverse unit.
The convention for the dual action is U03's contragredient convention.
:::

## I02: incidence is preserved

:::node "lem:i02" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_traceDomain) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.map_traceKernel) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.parallel_hyperplanePerm_iff) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.dependentTriple_hyperplanePerm_iff) (decl := OrlikSolomon.HyperplaneGT.unit_smul_single_sub_mem_traceKernel_iff)
The permutation preserves parallel pairs and dependent triples in both directions.
The proof transports the actual trace domains and kernels by evaluation coannihilator identities.
A single basis vector detects an empty trace, and a unit-weighted difference with a retained trace detects precisely the guarded dependent triple and equality of the two units.
Nonzero coefficients are required to distinguish trace labels.
:::

## I03: the projective collineation

:::node "lem:i03" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectivePerm) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectivePerm_constantPoint) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectivePerm_coefficientPoint) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.preservesProjectiveLines_projectivePerm) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectiveAction)
Use G01 to view $`\pi_g` as a permutation of coefficient points away from $`o=[1:0:\cdots:0]`, and extend it by fixing $`o`.
The extension and its inverse map every projective line onto a projective line.
Parallel pencils account for lines through $`o`; dependent triples account for the other lines.
:::

## I04: individual marked labels are fixed

:::node "lem:i04" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplanePerm_marking_zero) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.hyperplanePerm_marking_one) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectivePerm_basisPoint) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.projectivePerm_differencePoint) (decl := OrlikSolomon.HyperplaneGT.dependentTriple_marking_coordinate_zero) (decl := OrlikSolomon.HyperplaneGT.not_dependentTriple_marking_coordinate_one)
Each marked zero and one hyperplane is individually fixed.
The single common target component forces the same two-label permutation for every marking, and the dependent triple $`x_i=0`, $`x_j=0`, $`x_i-x_j=0` rules out simultaneous exchange.
This is a combinatorial distinction of labels and remains valid in characteristic two.
:::

# A coordinate proof of field reconstruction

These three geometric steps, C01–C03, concern an arbitrary line-preserving projective bijection over a field.
They are independent of the coefficient ring, cohomology and the construction of the permutation in I01.

## C01: finite projective spans

:::node "lem:c01" (decl := OrlikSolomon.HyperplaneGT.collineation_preserves_span)
A projective bijection preserving lines in both directions preserves the projective span of every finite set.
The Lean theorem preserves arbitrary projective spans by the existing span-induction principle, without assuming a fundamental theorem of projective geometry.
:::

## C02: separate coordinate functions

:::node "lem:c02" (decl := OrlikSolomon.HyperplaneGT.collineation_coordinate_functions) (decl := OrlikSolomon.HyperplaneGT.affineChartPoint_collineationChartMap)
If the bijection fixes the coordinate points $`[e_0]` and $`[e_i]`, it preserves the chart $`a_0=1` and acts there by separate bijections $`f_i:k\to k` with $`f_i(0)=0`.
Preservation of the coordinate directions makes each output coordinate depend only on its corresponding input coordinate.
:::

## C03: the unique field automorphism

:::node "thm:c03" (decl := OrlikSolomon.HyperplaneGT.coordinateFieldEquiv) (decl := OrlikSolomon.HyperplaneGT.coordinateFieldEquiv_affineChartPoint) (decl := OrlikSolomon.HyperplaneGT.coordinateFieldEquiv_mk) (decl := OrlikSolomon.HyperplaneGT.existsUnique_coordinateFieldEquiv)
For $`n\ge2`, additionally fixing $`[e_i-e_0]` and $`[e_i-e_j]` forces a unique field automorphism $`\sigma` with $`F([a])=[\sigma(a)]` coordinatewise.
The coordinate argument proves additivity, multiplicativity and bijectivity, then treats points at infinity.
The points $`[e_i-e_0]` are separate extra markings: on the affine chart they fix minus one on each axis.
Sum lines are described using an affine point and their fixed direction point at infinity, which stay distinct even when the coordinate sum is zero; the zero values of the coordinate bijections are handled explicitly.
:::

## C04: the Galois homomorphism

:::node "prop:c04"
The reconstructed field automorphism fixes each $`s\in S` by the fixed marked coefficient points, and therefore fixes $`k_0`.
Uniqueness and composition give a group homomorphism $`\eta:\operatorname{Aut}_2\to(k\simeq_{k_0}k)` inducing the recovered hyperplane permutation.
:::

# The scalar kernel and the full graded algebra

## S01: the scalar kernel

:::node "lem:s01"
If $`\eta(g)=1`, a unique unit $`u\in R^\times` acts as $`g` on every degree-one object, including $`T`.
Trace differences equate the multipliers in a dependent triple; a transverse hyperplane equates those of a parallel pair.
The dimension hypothesis supplies that transverse direction.
:::

## S02: the explicit Galois action

:::node "lem:s02" (decl := OrlikSolomon.HyperplaneGT.isFamily_galoisLabelEquiv) (decl := OrlikSolomon.HyperplaneGT.galoisOSAlgebraEquiv) (decl := OrlikSolomon.HyperplaneGT.map_degree_galoisOSAlgebraEquiv) (decl := OrlikSolomon.HyperplaneGT.galoisGradedAut) (decl := OrlikSolomon.HyperplaneGT.galoisGradedAut_targetEquiv) (decl := OrlikSolomon.HyperplaneGT.galoisOSAlgebraEquiv_osMap) (decl := OrlikSolomon.HyperplaneGT.galoisGradedAction)
For each $`\sigma\in(k\simeq_{k_0}k)`, the formula $`e_H\mapsto e_{\sigma H}` defines a natural graded $`R`-algebra automorphism of the full diagram, acting identically on $`T`.
These maps form an action and preserve every Orlik–Solomon relator, including higher ones.
The construction uses the presentation and does not depend on local detection or on a semilinear pullback supplied by a theory.
:::

## S03: local coefficient classification

:::node "thm:s03"
For a nonzero commutative local ring, the formula $`(u,\sigma)\mapsto uP_\sigma` gives a group equivalence $`R^\times\times(k\simeq_{k_0}k)\simeq\operatorname{Aut}_2`.
The scalar embedding is an injective central group homomorphism, and the classification includes an inverse and the group laws.
:::

## S04: extension and the scalar quotient

:::node "thm:s04"
Restriction to degree one gives a group equivalence $`\operatorname{Aut}_{\mathrm{gr}}\simeq\operatorname{Aut}_2`.
After S03, the classified automorphism extends by multiplying words of length $`q` by $`u^q` and applying $`P_\sigma`.
The quotient of either group by its central scalar subgroup is canonically $`k\simeq_{k_0}k`.
This extension follows from classification, rather than an assertion that the algebra is quadratic.
:::

## S05: integral domain coefficients

:::node "thm:s05"
The classification, graded extension and scalar quotient also hold over any integral domain $`R`.
The planned proof extends the finite matrices and explicit relation spans to its fraction field, applies the local result there, and descends a unit and all matrix entries using injectivity.
It assumes no localization theorem for the kernels of a new cohomology theory.
:::

# Transport and the planned de Rham application

## E01: reconstruction for the supplied theory

:::node "thm:e01"
Under the stated geometric, marking and coefficient hypotheses, the marked diagonal diagram of an existing geometric ordinary theory has the proposed quadratic and graded automorphism group equivalences.
They send $`[H]` to $`u[\sigma H]` and act by $`u` on degree one of $`T`.
Conjugating by A04 transports the classification; the theory is a supplied C1–C5 value, not a new structure with a reconstruction field.
:::

## E02: cofinal and realization independence

:::node "cor:e02"
Restriction to any cofinal subsystem induces an isomorphism of either automorphism group, by its classified generator formulas.
Two eligible realizations with the same coefficient ring have canonically isomorphic marked diagonal diagrams, by their canonical comparisons with the Orlik–Solomon diagram.
The blueprint does not assume that arbitrary diagram automorphisms extend from a cofinal subsystem before reconstruction is proved.
:::

## E03: algebraic de Rham reconstruction

:::node "cor:e03"
In characteristic zero, the existing de Rham instance is planned to give the unconditional equivalences $`\operatorname{Aut}_{\mathrm{gr}}\simeq\operatorname{Aut}_2\simeq k^\times\times(k\simeq_{k_0}k)` for the ordinary de Rham diagram.
The generator formula is $`[df_H/f_H]\mapsto u[df_{\sigma H}/f_{\sigma H}]`.
The constructed action is $`k`-linear; ordinary transport of differential forms by $`\sigma` is semilinear on coefficients and must be distinguished from it.
:::

# Regressions, limits and completion

The blueprint requires characteristic-two and nilpotent local coefficients, including $`\mathbb F_2[\epsilon]/(\epsilon^2)`, as tests of unit cancellation and alternation without division by two.
The reconstruction theorem requires $`n\ge2`, while the low-degree algebra remains valid in dimensions zero and one and for the empty arrangement.
Zero coefficients remain permitted for the preceding algebraic constructions and the existing structure theorem; they are excluded from the new reconstruction theorem.

The coefficient hypothesis cannot be replaced by arbitrary commutative rings.
For a product $`F\times F` and two distinct Galois automorphisms, the two coefficient factors can carry different permutations, which cannot arise from one common scalar and one common field automorphism.
The proof must also preserve the existing coverage of scheme complements without rational points.

Further checks concern finite-stage compatibility without union closure, the single common marked target, recovery of coordinate spans without adding projection arrows, the full algebraic dual without a reflexivity shortcut, and extension to the graded algebra only after classification.
These are requirements of the planned proof, rather than additional assumptions on the theorem.

Completion requires proved public declarations for every statement, generator and marking formulas, the inverse and group laws of the equivalences, the existing repository checks and independent coverage review, and the application to the constructed de Rham instance.
Until then, the boxes above record the scope of work and claim no formalized reconstruction result.
