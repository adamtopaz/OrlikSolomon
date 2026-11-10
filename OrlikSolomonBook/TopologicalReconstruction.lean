/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Topological hyperplane reconstruction" =>
%%%
tag := "topological-reconstruction"
file := "topological-reconstruction"
htmlSplit := .never
%%%

*Five statements are formalized, two are partly formalized and ten remain planned.*
The pure quadratic and graded component topologies, their topological-group and separation properties, and their complete-stage-and-target neighborhood bases are proved.
The pure groups are closed in their original ambient products, and finite coefficients make both compact.
T04 proves the existing degree-one restriction is a topological embedding, with continuous inverse whenever the map is bijective.
The actual-theory and ordinary de Rham clauses of T01–T02 remain planned.
T05 proves the pointwise Galois topology and its exact finite-equation, geometric-fiber and selected-stage kernel descriptions.
T06 proves the exact comparison with Mathlib's existing Krull topology, normalized coefficient-field fixers and finite-intermediate-field containment by selected-stage kernels.
T08 constructs the actual rational-function counterexample and proves noncontinuity of the M8 direct Galois action and classification for Mathlib's Krull topology.
This chapter follows the [fifth blueprint](https://github.com/adamtopaz/OrlikSolomon/blob/main/blueprint/topological_reconstruction_blueprint.tex), for milestone M9, tracked by [#204](https://github.com/adamtopaz/OrlikSolomon/issues/204).
Its seventeen named nodes T01–T17 each have one labelled statement and one separate box below.
The four earlier blueprints retain their separate counts.
The existing {ref "hyperplane-gt"}[M8 reconstruction equivalences] are algebraic inputs, and their reconstruction homeomorphisms remain planned.

# The intended topology and hypotheses

Let $`k_0\to k` be an algebra map of fields and let $`G=(k\simeq_{k_0}k)`.
A supplied cofinal system consists of finite $`G`-stable arrangements covering every finite set of hyperplanes.
Its selected stages need not be closed under unions.
The proposed diagram topology is induced from the product of discrete groups of complete stage automorphisms, including the single original common-target component.
It concerns neighborhoods or nets, with no countability assumption.
The coefficient units $`R^\times` are discrete, independently of any topology on $`R`; this makes no adic-coefficient claim.

The classification hypotheses are exactly those of M8: $`n\geq2`, zero among the marking constants $`S\subset k_0`, $`\operatorname{Subfield.closure}(S)=k_0`, and either a nonzero local coefficient ring or an integral domain.
The basic topologies, adapters and literal restriction maps have the broader hypotheses specified in their boxes.
Pointwise convergence on $`G` means the topology induced by evaluation into a product of discrete copies of $`k`.
It must be distinguished from Mathlib's existing Krull topology.
The exact comparison condition is that, for every $`a\in k`, some finite-dimensional intermediate field $`E/k_0` has $`\operatorname{Fix}(E)\subset\operatorname{Fix}(\{a\})`.
Algebraicity of $`k/k_0` suffices for this condition; normality, separability, perfectness and algebraic closure are not required.
A supplied cofinal system alone does not imply it.

# Diagram topology

## T01: finite-stage convergence

:::node "def:t01" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.familyTopology) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.stageTopology) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.continuous_stageTopology_iff) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.familyTopology) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.stageTopology) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.continuous_stageTopology_iff) (remaining := "The actual supplied-theory component topologies and adapters (#218), and the direct ordinary de Rham component topologies (#221), remain planned.")
Give the existing quadratic and full graded diagram groups their subspace topologies in products of discrete stage-automorphism groups and the discrete common-target group.
Define the actual supplied-theory and ordinary de Rham topologies directly from their own components as well.
Use deliberate named or scoped instances without changing carriers, group laws or structure fields, and without installing a global discrete topology on all linear or algebra equivalences.
:::

## T02: groups and neighborhood bases

:::node "lem:t02" (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.diagramIsTopologicalGroup) (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.gradedIsTopologicalGroup) (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.diagramT2Space) (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.gradedT2Space) (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.diagramTotallySeparatedSpace) (decl := OrlikSolomon.HyperplaneGT.FiniteStageTopology.gradedTotallySeparatedSpace) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.nhds_one_stageBasis) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.nhds_one_stageBasis) (remaining := "The corresponding group, separation and stage-and-target neighborhood basis results for actual supplied-theory diagrams (#218) and ordinary de Rham diagrams (#221) remain planned.")
The intended topologies make all these groups Hausdorff and totally separated topological groups.
At the identity, agreement with the identity on one selected stage and on the common target gives a neighborhood basis.
Cofinal enlargement controls finitely many stage conditions; union closure and classification are not assumed.
:::

## T03: closedness and finite coefficients

:::node "prop:t03" (decl := OrlikSolomon.HyperplaneGT.DiagramAut.isClosed_subgroup) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.isClosed_subgroup) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.isClosedEmbedding_subtype) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.isClosedEmbedding_subtype) (decl := OrlikSolomon.HyperplaneGT.osGradedAutSubgroup_degreeOne_injective) (decl := OrlikSolomon.HyperplaneGT.finite_osGradedAutSubgroup) (decl := OrlikSolomon.HyperplaneGT.DiagramAut.compactSpace) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.compactSpace)
The pure quadratic and graded diagram groups are closed subgroups of their ambient products for every commutative coefficient ring.
For finite coefficients they are compact and therefore profinite, without classification or algebraicity.
The graded argument uses generation to make each degree-preserving factor finite; it does not claim that every unrestricted algebra-automorphism group is finite.
:::

## T04: degree-one restriction

:::node "lem:t04" (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.stageEquiv_eq_iff_toQuadratic) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.targetEquiv_eq_iff_toQuadratic) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.preimage_stageKernel) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.stageTopology_eq_induced_toQuadratic) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.isEmbedding_toQuadratic) (decl := OrlikSolomon.HyperplaneGT.GradedDiagramAut.continuous_inverse_toQuadratic)
The existing graded-to-quadratic restriction homomorphism is a topological embedding over arbitrary commutative coefficients and in every dimension.
Whenever its existing algebraic map is bijective, the inverse is continuous.
This statement does not assert that every quadratic automorphism extends before classification.
:::

# Pointwise and Krull topology

## T05: finite equations and coordinate fibers

:::node "lem:t05" (decl := OrlikSolomon.HyperplaneGT.galoisPointwiseTopology) (decl := OrlikSolomon.HyperplaneGT.galoisPointwise_nhds_one_basis) (decl := OrlikSolomon.HyperplaneGT.galoisPointwise_isTopologicalGroup) (decl := OrlikSolomon.HyperplaneGT.galoisPointwise_t2Space) (decl := OrlikSolomon.HyperplaneGT.galoisPointwise_totallySeparatedSpace) (decl := OrlikSolomon.HyperplaneGT.hyperplaneStabilizer_eq_fixingCoefficients) (decl := OrlikSolomon.HyperplaneGT.normalizedAffineCoefficients_smul) (decl := OrlikSolomon.HyperplaneGT.coordinateFiber_inj) (decl := OrlikSolomon.HyperplaneGT.galois_smul_coordinateFiber) (decl := OrlikSolomon.HyperplaneGT.galoisPointwise_nhds_one_hyperplaneBasis) (decl := OrlikSolomon.HyperplaneGT.galoisStagePermutation) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.mem_galoisStageKernel_iff) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.galoisPointwise_nhds_one_stageKernelBasis) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.galoisStagePermutationTopology_eq_pointwise)
Pointwise convergence makes $`G` a Hausdorff totally separated topological group.
Fixing a hyperplane is equivalent to fixing its finite set of normalized equation coefficients.
For $`n\geq1`, the coordinate fibers $`x_0=a` identify the pointwise topology with the topology generated by finite hyperplane stabilizers, or by stage permutation kernels of the supplied system.
The values $`a` range over the entire geometric field; the finite coefficient test includes the affine constant.
The basis and selected-stage topology comparison use only cofinality, with no algebraicity or union-closure assumption.
The arrangement-free pointwise group and separation results have no dimension hypothesis.
A deliberate scope selects this named topology while preserving Mathlib's global Krull topology and every pre-existing field topology.
:::

## T06: the exact Krull comparison

:::node "thm:t06" (decl := OrlikSolomon.HyperplaneGT.KrullFixingCondition) (decl := OrlikSolomon.HyperplaneGT.exists_finset_fixingIntermediateField) (decl := OrlikSolomon.HyperplaneGT.galoisPointwiseTopology_le_krull) (decl := OrlikSolomon.HyperplaneGT.krull_eq_pointwise_iff) (decl := OrlikSolomon.HyperplaneGT.krull_eq_pointwise_of_isAlgebraic) (decl := OrlikSolomon.HyperplaneGT.hyperplaneCoefficientField) (decl := OrlikSolomon.HyperplaneGT.fixingHyperplanes_eq_coefficientField) (decl := OrlikSolomon.HyperplaneGT.finiteDimensional_hyperplaneCoefficientField) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.exists_stageKernel_le_fixingSubgroup) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.galoisStagePermutationTopology_eq_krull) (decl := OrlikSolomon.HyperplaneGT.CofinalSystem.galoisStagePermutationTopology_eq_krull_of_isAlgebraic)
For an arbitrary field extension, Mathlib's Krull topology equals the pointwise topology exactly under the finite-intermediate-field fixing condition stated above.
Algebraicity suffices; it is not claimed to be necessary.
Under algebraicity, the field generated by the normalized coefficients of finitely many hyperplanes is finite dimensional and has the same fixing subgroup.
The fixing-subgroup equality itself holds without algebraicity; only finite dimensionality of the coefficient field uses that hypothesis.
For $`n\geq1`, cofinal coordinate fibers place a stage stabilizer inside the fixing subgroup of any finite intermediate field.
That containment needs neither the comparison condition nor algebraicity, and does not assert that the chosen stage has coefficient field equal to the prescribed intermediate field.
Under the exact condition, the selected-stage permutation topology equals the existing Krull topology.
All comparisons use explicit named topology values; importing the optional facade changes no inferred topology.
:::

## T07: compactness from finite orbits

:::node "prop:t07"
If every element of $`k` has finite $`G`-orbit, the pointwise group is profinite.
A supplied cofinal system with $`n\geq1` implies this orbit condition, and algebraicity also implies it directly.
Finite orbits alone are not substituted for the Krull comparison condition.
:::

## T08: the rational-function counterexample

:::node "prop:t08" (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.intermediateField_eq_bot_of_finiteDimensional) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.finite_algEquiv) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.translation_one_ne_one) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.krullTopology_eq_top) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.finiteStableCofinalSystem) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.pointwiseTopology_eq_bot) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.stagePermutationTopology_eq_bot) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.zero_generates_primeField) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.finite_binary_diagramAut) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.nontrivial_binary_diagramAut) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.binary_diagramTopology_eq_bot) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.not_KrullFixingCondition) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.not_continuous_galoisQuadraticAction) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.not_continuous_quadraticAutEquiv) (decl := OrlikSolomon.HyperplaneGT.RatFuncExamples.not_isHomeomorph_quadraticAutEquiv)
For $`\mathbb F_p(t)/\mathbb F_p` with $`p` prime and $`n=2`, construct an actual cofinal system of finite stable arrangements.
Its field-automorphism group is finite and nontrivial, its Krull topology is indiscrete, and its pointwise and stage-permutation topologies are discrete.
With coefficient ring $`\mathbb F_2` and $`S=\{0\}`, the M8 classification hypotheses hold, but that classification is not a homeomorphism for the Krull topology.
The actual binary quadratic diagram is nontrivial, finite and discrete in its original stage-and-common-target topology.
Both the actual direct Galois action and the forward M8 classifier are noncontinuous when the source uses Mathlib's literal Krull topology; the classifier uses the product with discrete coefficient units.
The base prime $`p` is independent of the binary coefficient prime.
The finite stable system is built by actual finite Galois saturation, without an algebraicity assumption or the algebraic full-system wrapper.
For every constant field, the Krull topology is indiscrete and the pointwise topology is discrete; only finite constants are required for the supplied system, whose stage topology comparison explicitly retains $`n\geq1`.
No topology instance is replaced and no cohomology theory is asserted to exist.
:::

# Topological classification

## T09: quadratic reconstruction

:::node "thm:t09"
Under the classification hypotheses, upgrade each existing local-ring or integral-domain quadratic equivalence to a topological group isomorphism from discrete coefficient units times the pointwise group.
Under the exact Krull comparison condition, in particular under algebraicity, use Mathlib's Krull topology instead.
Both directions must be continuous, and the underlying multiplicative equivalence must be the existing M8 map.
:::

## T10: graded reconstruction

:::node "cor:t10"
Under the classification hypotheses, the existing graded restriction equivalence becomes a topological group isomorphism without an algebraicity hypothesis.
The full graded classification has the same discrete-unit and pointwise product topology, with the Krull version under the comparison condition or algebraicity.
The existing degree-power scalar action and common-target formulas remain unchanged.
:::

## T11: scalar quotients

:::node "thm:t11"
Equip both groups modulo their actual scalar ranges with the quotient-group topology.
Under the classification hypotheses, the existing local/domain quotient equivalences become topological group isomorphisms with the pointwise group, and with the Krull group under the comparison condition.
The scalar ranges are closed and the quotients are Hausdorff and profinite.
No equality between a scalar range and the entire center is asserted.
:::

## T12: cofinal restriction

:::node "thm:t12"
Literal stage restriction to a supplied cofinal subsystem is continuous over every commutative coefficient ring and retains the same target.
Under the classification hypotheses, each existing local/domain quadratic/graded restriction equivalence and its induced scalar-quotient equivalence becomes a topological group isomorphism.
No algebraicity or union closure is required, and bijectivity comes from M8 rather than from cofinality alone.
:::

## T13: separation and compactness

:::node "cor:t13"
Under the classification hypotheses, both diagram groups are locally compact, Hausdorff and totally separated.
They are compact, equivalently profinite, exactly when the discrete coefficient-unit group is finite; this includes integral coefficients $`\mathbb Z` as well as finite coefficients.
Their scalar quotients are always profinite in the pointwise topology, including when the Krull comparison condition fails.
:::

# Actual cohomology and de Rham

## T14: the canonical adapters

:::node "thm:t14"
For any supplied eligible C1–C5 ordinary theory over arbitrary commutative coefficients, the existing actual-to-presentation quadratic and graded comparisons become topological group isomorphisms.
They include the actual common targets and induce homeomorphisms on the scalar quotients with their quotient topologies.
No classification, dimension bound, algebraicity or new continuity axiom on the theory is required.
:::

## T15: reconstruction for a supplied theory

:::node "thm:t15"
Under the respective local/domain classification hypotheses and algebraicity, upgrade the existing actual quadratic and graded reconstruction and scalar-quotient equivalences to the Krull versions.
The exact comparison condition may replace algebraicity.
The actual degree-one and cofinal restriction equivalences already become topological group isomorphisms without algebraicity.
All existing classification, marking, scalar and restriction squares are retained.
:::

## T16: realization independence

:::node "thm:t16"
The existing quadratic, graded and scalar-quotient comparisons between two supplied eligible realizations with the same coefficient ring and geometric data become topological group isomorphisms without classification or algebraicity.
Retain the independently sized weight algebras, gradings, cohomology universes and admissible domains allowed by M8, and the single common target.
Under classification the comparisons preserve the unit/Galois parameters and commute with the upgraded cofinal maps, with no assumed theory morphism or cohomology base-change theorem.
:::

## T17: ordinary de Rham reconstruction

:::node "cor:t17"
In characteristic zero, under the marking and dimension hypotheses and algebraicity, upgrade the existing actual ordinary de Rham quadratic/graded reconstruction and scalar quotients to the Krull topological group isomorphisms.
The degree-one restriction equivalence needs no algebraicity; cofinal restriction and the canonical full-system specializations have the corresponding upgrades.
These specialize the already constructed theory rather than asking for a supplied realization.
For a supplied system, the exact comparison condition may replace algebraicity in the Krull assertions.
The action remains coefficient-linear on covariant logarithmic labels, with the original degree-power scalars; it is not semilinear transport of differential forms.
With discrete coefficient units, the full de Rham groups are locally compact and noncompact, while their scalar quotients are profinite under the stated hypotheses.
:::

# Completion and limits

A box becomes formalized only when proved public declarations cover its whole statement.
Coverage of some clauses is marked partly formalized with the remaining clauses listed.
Pointwise reconstruction alone does not complete a Krull wrapper, and continuity of a bijection alone does not complete inverse continuity.
Completion requires the direct component topologies and neighborhood bases, the actual quotient topologies, exact agreement with the underlying M8 maps, all cofinal and realization squares, and the ordinary de Rham specialization.
The required regressions retain characteristic two, nilpotent and integral coefficients, finite and infinite Galois groups, the rational-function counterexample, non-union-closed cofinal systems, zero coefficients, dimension zero and point-free complements wherever the hypotheses allow them.
The supplied-theory examples remain conditional on those theories; the constructed characteristic-zero de Rham realization is separate.
