/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "The geometry of arrangements" =>
%%%
tag := "geometry"
file := "geometry"
htmlSplit := .never
%%%

This chapter sets up the objects on which cohomology is evaluated.
Everything in it is linear algebra and localization, and none of it mentions cohomology.

# Complements cannot be sets of points

It is tempting to define the complement of an arrangement as a subset of the $`k`-points of $`V`, and that would be wrong.
Over the field with two elements, removing the two rational points of $`\mathbb{A}^1` leaves a set with no $`k`-points at all.
Yet the complement is a nonzero scheme: its coordinate ring is the nonzero localization $`\mathbb{F}_2[x,1/x(x+1)]`, and the theorem says that its cohomology has a basis of three elements over $`B`.
Cohomology of the empty set would be zero.

So the complement must be the geometric object, given in coordinates by
$$`\operatorname{Spec}k[x_1,\ldots,x_n,1/P],\qquad P=\prod_{H\in\mathcal{A}}f_H.`
A $`k`-point of this scheme is a $`k`-algebra map from its ring to $`k`, and the library proves that the example has none, while its ring is nonzero.

```lean -show
open OrlikSolomon
```

```lean
example :
    IsEmpty
      (Sanity.twoPoints.ComplementRing →ₐ[ZMod 2] ZMod 2) :=
  Sanity.isEmpty_algHom_twoPoints

example : Nontrivial Sanity.twoPoints.ComplementRing :=
  Sanity.nontrivial_complementRing_twoPoints
```

Sets of $`k`-points are the right language only for the linear incidence data of the hyperplanes themselves, and that is how they are used.
A hyperplane is an affine subspace of $`V`, which is a set of $`k`-points.
This loses nothing, because whether a system of affine equations over $`k` has a solution, and the dimension of its solution set, are questions of linear algebra over $`k`.
A complement of hyperplanes is not such a set.

Every map between complements in the proof is therefore a map of coordinate rings.
So the arguments remain valid when a complement has no $`k`-points, and they never have to treat that case separately.

# Smooth algebras instead of an abstract interface

The blueprint allows a separate interface that lists the required objects and diagrams, to be implemented later by localizations of polynomial rings.
The formalization takes the economical route that the blueprint also names: everything is stated directly on one concrete category, {name OrlikSolomon.SmoothAlg}`SmoothAlg` `k`, the smooth commutative $`k`-algebras, which is dual to smooth affine $`k`-schemes.
The purpose is that the public theorem be about actual arrangements, with no leftover geometric hypothesis.
The two blueprint nodes about the interface, {bp "def:geometry-interface"}[] and {bp "lem:geometry-adapter"}[], are therefore discharged by construction, and their boxes name the declarations that do so.

Two conventions follow from this choice.
Morphisms of {name OrlikSolomon.SmoothAlg}`SmoothAlg` `k` run in the direction of algebras, so cohomology is a _covariant_ functor on it, and "pullback along $`X\to Y`" is the image of the algebra map $`\mathcal{O}(Y)\to\mathcal{O}(X)`.
And an invertible regular function on $`\operatorname{Spec}A` is simply a unit of $`A`, which is the same thing as a regular map to $`\mathbb{G}_m`.

The category is not chosen for generality: it needs regular maps that are not affine-linear, because {bp "lem:small-targets"}[the normalized maps] $`f_i/f_1` of the realization step are fractions.
A category of affine-linear maps would not be enough.
Full scheme theory, on the other hand, is not needed for the proof.
Restating the theorems for open subschemes and for cohomology theories on schemes, without changing this proof, is planned in {ref "geometric"}[the chapter on schemes]; its foundations, affine duality and its compatibilities, divisor pairs, affine and projective complements as open subschemes, geometric cohomology axioms, both affine transports, logarithmic classes, and sheaves of forms with affine evaluation are formalized, with the remaining parts indicated in their boxes.

# Coordinate rings

The coordinate ring of $`V` is the symmetric algebra of its dual, so no basis is chosen.
The coordinate ring of $`U_{\mathcal{A}}` is the localization of it that inverts all equations of all hyperplanes, so its definition involves no choice of equations either.
For any choice of one equation for each hyperplane, with product $`P`, it is also the localization at the single element $`P`, which is the display above: this is {name OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway}`isLocalizationAway`.

# Hyperplanes and equations

:::node "def:arrangement" (decl := OrlikSolomon.IsHyperplane) (decl := OrlikSolomon.Arrangement) (decl := OrlikSolomon.IsEquation)
An affine hyperplane in a finite-dimensional $`k`-vector space $`V` is a nonempty proper affine subspace of codimension one, and an arrangement is a finite set of these.
An equation for $`H` is an affine map $`f_H:V\to k` with nonzero linear part and zero locus $`H`.
:::

Two equations of one hyperplane differ by a unit of $`k`, and this is why the map $`\Phi_{\mathcal{A}}` will not depend on the equations: logarithmic classes of constants vanish.

:::node "lem:equations" (decl := OrlikSolomon.IsHyperplane.exists_isEquation) (decl := OrlikSolomon.IsEquation.existsUnique_smul) (decl := OrlikSolomon.direction_iInf_of_isEquation) (decl := OrlikSolomon.codim_iInf_of_isEquation)
Every hyperplane has an equation, and two equations for the same hyperplane differ by a unique element of $`k^\times`.
A nonempty intersection of hyperplanes has a $`k`-point and is an affine space whose direction is the intersection of the kernels of the linear parts, and its codimension is the rank of the system of equations.

In the formalization an intersection is an infimum of affine subspaces, which are sets of $`k`-points, so an intersection is an affine space by construction, and being nonempty is the same as having a $`k`-point.
:::

# Deletion and restriction

The restriction is an arrangement in $`H`, which is an affine space and not a vector space.
The formalization places it on the direction vector space of $`H`, identified with $`H` by a base point chosen once and hidden inside {name OrlikSolomon.chart}`chart`.
Since nothing says which point it is, results are stated through the intersection $`H\cap K`, whose value does not depend on it.
The induction statements quantify over all finite-dimensional spaces, so the change of ambient space causes no difficulty.

:::node "def:deletion" (decl := OrlikSolomon.Arrangement.deletion) (decl := OrlikSolomon.Arrangement.restriction) (decl := OrlikSolomon.Arrangement.mem_restriction) (decl := OrlikSolomon.Arrangement.mem_restriction_iff_map_chart) (decl := OrlikSolomon.chart)
For $`H\in\mathcal{A}`, the deletion is $`\mathcal{A}'=\mathcal{A}\setminus\{H\}`, and the restriction $`\mathcal{A}''` is the finite set of nonempty intersections $`H\cap K` for $`K\in\mathcal{A}'`, with duplicates removed, regarded as an arrangement in $`H`.
:::

The next box records what the inductions use about this construction.
Its key content is what happens to an old equation on $`H`.
If its hyperplane misses $`H`, then it restricts to a nonzero constant, and otherwise to a nonzero multiple of an equation of its trace.
So two old hyperplanes with the same trace have the same restricted unit up to a constant, and their logarithmic classes restrict to the same class.
That fact is the geometric core of why duplicates in the restriction cause no trouble.

:::node "lem:restriction-geometry" (decl := OrlikSolomon.IsHyperplane.isHyperplaneIn_inf) (decl := OrlikSolomon.Arrangement.isHyperplaneIn_map_chart) (decl := OrlikSolomon.IsHyperplane.finrank_direction_add_one) (decl := OrlikSolomon.Arrangement.card_restriction_le) (decl := OrlikSolomon.Arrangement.card_restriction_lt) (decl := OrlikSolomon.IsEquation.comp_chart_eq_const_or_smul) (decl := OrlikSolomon.Arrangement.exists_representative) (decl := OrlikSolomon.DivisorPair.deletionPair) (decl := OrlikSolomon.IsEquation.ker_pull_chart) (decl := OrlikSolomon.IsEquation.quotientEquiv) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalization_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.surjective_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.ker_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.quotientEquiv) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway_inclusion) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit_mul) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit_mul_of_inf_eq) (decl := OrlikSolomon.DivisorPair.deletionPair_eqnUnit) (decl := OrlikSolomon.DivisorPair.fromStandard_deletionPair_compl) (decl := OrlikSolomon.DivisorPair.deletionPairHom)
Each retained intersection is a hyperplane in $`H`, so the restriction has ambient dimension $`n-1`, and it has at most $`|\mathcal{A}'|<|\mathcal{A}|` hyperplanes.
The restriction of an old equation is either a nonzero constant or a nonzero multiple of an equation for its retained hyperplane, and every retained hyperplane has an old representative.
The function $`f_H` cuts the smooth divisor $`D=H\cap U_{\mathcal{A}'}\simeq U_{\mathcal{A}''}` out of $`X=U_{\mathcal{A}'}`, with open complement $`U_{\mathcal{A}}`, transversely pulled back from $`\{0\}\subset\mathbb{A}^1`.

In the formalization the deletion pair is one certified divisor pair, for any equation of $`H`, in which the restriction map and the inclusion do not depend on the equation.
The transverse pullback is {name OrlikSolomon.DivisorPair.fromStandard}`fromStandard`, which exists for every pair, and {name OrlikSolomon.DivisorPair.deletionPairHom}`deletionPairHom` compares the pairs of two equations.
These statements hold over any field, including when a complement has no rational points, and when $`H` is a point.
:::

# Divisor pairs

The localization axiom is stated for a _certified divisor pair_: three smooth algebras $`\mathcal{O}(X)`, $`\mathcal{O}(D)` and $`\mathcal{O}(U)`, maps $`i` and $`j` out of $`\mathcal{O}(X)`, and an element $`f` of $`\mathcal{O}(X)`, such that $`i` is surjective with kernel $`(f)`, $`j` exhibits $`\mathcal{O}(U)` as the localization at $`f`, and $`f` is a non-zero-divisor.
The maps are certified rather than the rings being literally $`\mathcal{O}(X)/(f)` and $`\mathcal{O}(X)[1/f]`.
This lets the rings of $`U_{\mathcal{A}'}`, $`U_{\mathcal{A}''}` and $`U_{\mathcal{A}}` form a pair directly, with no transport along isomorphisms.

The non-zero-divisor condition is essential.
If $`f=0` were allowed on a nonzero ring, then the open part would be empty, and exactness would force a bijective Gysin map of shift $`(2,1)` on the cohomology of the divisor.
For the ring $`k` this contradicts the dimension axiom of any nonzero theory, so the axioms would have no nonzero model.
No stronger condition is needed.
Units are allowed, which gives an empty divisor, and this is how the axioms force the zero ring to have zero cohomology without a separate axiom for the empty scheme.

A _transverse morphism_ of pairs $`P\to Q` is a triple of maps commuting with $`i` and $`j`, such that the ambient map sends the equation of $`P` to a unit multiple of the equation of $`Q`.
The unit matters in both directions.
It has to be allowed, because the proof that $`[fg]=[f]+[g]` compares the maps $`x` and $`xy` on $`\mathbb{A}^1\times\mathbb{G}_m`, and $`xy` is a unit multiple of $`x`.
And the condition cannot be weakened to ask only that the zero loci agree, because $`z\mapsto x^2` also commutes with $`i` and $`j`, but it multiplies a residue by two.

Only two families of pairs are needed.
The _standard pair_ $`(A[t],A,A[t,t^{-1}],t)`, for a smooth algebra $`A`, serves as $`(\mathbb{A}^1,0,\mathbb{G}_m)` when $`A=k`, and also for products with $`\mathbb{G}_m`.
The _deletion pair_ $`(\mathcal{O}(U_{\mathcal{A}'}),\mathcal{O}(U_{\mathcal{A}''}),\mathcal{O}(U_{\mathcal{A}}),f_H)` is the other.

:::node "def:geometry-interface" (decl := OrlikSolomon.SmoothAlg) (decl := OrlikSolomon.SmoothAlg.point) (decl := OrlikSolomon.SmoothAlg.affineSpace) (decl := OrlikSolomon.SmoothAlg.polynomial) (decl := OrlikSolomon.SmoothAlg.laurent) (decl := OrlikSolomon.SmoothAlg.gm) (decl := OrlikSolomon.SmoothAlg.complement) (decl := OrlikSolomon.SmoothAlg.gmHom) (decl := OrlikSolomon.SmoothAlg.complementUnit) (decl := OrlikSolomon.SmoothAlg.complementUnit_smul) (decl := OrlikSolomon.DivisorPair) (decl := OrlikSolomon.DivisorPair.Hom) (decl := OrlikSolomon.DivisorPair.deletionPair) (decl := OrlikSolomon.toAffineImage) (decl := OrlikSolomon.toNormalizedSlice) (decl := OrlikSolomon.SmoothAlg.projectiveComplement) (decl := OrlikSolomon.SmoothAlg.projectiveRatioUnit) (decl := OrlikSolomon.SmoothAlg.coneIso) (decl := OrlikSolomon.SmoothAlg.deconeIso)
The geometry needed by the proof consists of a category of smooth affine objects, including a point, affine spaces, $`\mathbb{G}_m`, products with $`\mathbb{A}^1` and $`\mathbb{G}_m`, and arrangement complements, together with regular maps attached to invertible functions, and certified smooth-divisor pairs with transverse base-change squares.
This is a list of geometric constructions and identities, and it contains no cohomological conclusion.

There is no structure of this name in the formalization: the box names the concrete objects that play these roles.
:::

:::node "lem:geometry-adapter" (decl := OrlikSolomon.DivisorPair.standardPair) (decl := OrlikSolomon.DivisorPair.standardMap) (decl := OrlikSolomon.SmoothAlg.laurentSection) (decl := OrlikSolomon.Arrangement.ComplementRing) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway) (decl := OrlikSolomon.SmoothAlg.complementLift) (decl := OrlikSolomon.SmoothAlg.complementMap) (decl := OrlikSolomon.SmoothAlg.complementMap_comp) (decl := OrlikSolomon.SmoothAlg.complementMap_id) (decl := OrlikSolomon.SmoothAlg.complementIso) (decl := OrlikSolomon.DivisorPair.deletionPair) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalization_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.restriction_eq_map) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway_inclusion) (decl := OrlikSolomon.toAffineImage) (decl := OrlikSolomon.toNormalizedSlice) (decl := OrlikSolomon.SmoothAlg.coneIso) (decl := OrlikSolomon.SmoothAlg.deconeIso)
Localizations of polynomial algebras realize all of this.
The obligations are the standard pair $`(\mathbb{A}^1,0,\mathbb{G}_m)` and its products, the deletion pairs, the maps $`x` and $`xy` on $`\mathbb{A}^1\times\mathbb{G}_m` with the section $`x=1`, maps to affine images and normalized slices, affine coordinate changes, and the cone and decone isomorphism.

The declarations cover the standard pair and its products, the maps $`x` and $`xy`, which are {name OrlikSolomon.DivisorPair.standardMap}`standardMap` at the units $`1` and $`y`, and the section.
They also cover the complements themselves, displayed as the localization $`k[x_1,\ldots,x_n,1/P]`, with their universal property, and the affine coordinate changes, which are {name OrlikSolomon.SmoothAlg.complementMap}`complementMap` at an affine automorphism and its inverse, packaged as {name OrlikSolomon.SmoothAlg.complementIso}`complementIso`.
They cover the deletion pairs, whose three rings are complements, with the compatibility of quotient and localization: the ring of the restriction is a localization of the coordinate ring of $`H`, and restriction of functions on complements is the localization of restriction of functions on $`V`.
The maps to affine images and normalized slices are {name OrlikSolomon.toAffineImage}`toAffineImage` and {name OrlikSolomon.toNormalizedSlice}`toNormalizedSlice`, the second of which is given by fractions with invertible denominator.
The cone and decone isomorphisms are {name OrlikSolomon.SmoothAlg.coneIso}`coneIso` and {name OrlikSolomon.SmoothAlg.deconeIso}`deconeIso`.
:::
