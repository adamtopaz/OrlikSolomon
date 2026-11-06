/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "The geometry of arrangements" =>
%%%
tag := "geometry"
file := "geometry"
%%%

*Complements cannot be sets of points.*
It is tempting to define the complement of an arrangement as a subset of the $`k`-points of $`V`, and that would be wrong.
Over the field with two elements, removing the two rational points of $`\mathbb{A}^1` leaves a set with no $`k`-points at all, yet the complement is a nonzero scheme: its coordinate ring is the nonzero localization $`\mathbb{F}_2[x,1/x(x+1)]`, and the theorem says that its cohomology has a basis of three elements over $`B`.
So the complement must be the geometric object, given in coordinates by
$$`\operatorname{Spec}k[x_1,\ldots,x_n,1/P],\qquad P=\prod_{H\in\mathcal{A}}f_H.`
Sets of $`k`-points are the right language only for the linear incidence data of the hyperplanes themselves, and that is how they are used.

*Concrete rather than abstract.*
The blueprint allows a separate interface that lists the required objects and diagrams, to be implemented later by localizations of polynomial rings.
This project is designed around the economical route that the blueprint also names: everything is to be stated directly on the category of smooth commutative $`k`-algebras, which is dual to smooth affine $`k`-schemes.
The purpose is that the public theorem be about actual arrangements, with no leftover geometric hypothesis.
The two blueprint nodes about the interface, {bp "def:geometry-interface"}[] and {bp "lem:geometry-adapter"}[], are therefore to be discharged by construction, and their boxes name what exists so far and say what is still missing.

:::node "def:arrangement" (decl := OrlikSolomon.IsHyperplane) (decl := OrlikSolomon.Arrangement) (decl := OrlikSolomon.IsEquation)
An affine hyperplane in a finite-dimensional $`k`-vector space $`V` is a nonempty proper affine subspace of codimension one, and an arrangement is a finite set of these.
An equation for $`H` is an affine map $`f_H:V\to k` with nonzero linear part and zero locus $`H`.
:::

:::node "lem:equations" (decl := OrlikSolomon.IsHyperplane.exists_isEquation) (decl := OrlikSolomon.IsEquation.existsUnique_smul) (decl := OrlikSolomon.direction_iInf_of_isEquation) (decl := OrlikSolomon.codim_iInf_of_isEquation)
Every hyperplane has an equation, and two equations for the same hyperplane differ by a unique element of $`k^\times`.
A nonempty intersection of hyperplanes has a $`k`-point and is an affine space whose direction is the intersection of the kernels of the linear parts, and its codimension is the rank of the system of equations.
These are statements of linear algebra over $`k`, not about rational points of arbitrary varieties.
In the formalization an intersection is an infimum of affine subspaces, which are sets of $`k`-points, so an intersection is an affine space by construction, and being nonempty is the same as having a $`k`-point.
:::

:::node "def:deletion" (decl := OrlikSolomon.Arrangement.deletion) (decl := OrlikSolomon.Arrangement.restriction) (decl := OrlikSolomon.Arrangement.mem_restriction) (decl := OrlikSolomon.Arrangement.mem_restriction_iff_map_chart) (decl := OrlikSolomon.chart)
For $`H\in\mathcal{A}`, the deletion is $`\mathcal{A}'=\mathcal{A}\setminus\{H\}`, and the restriction $`\mathcal{A}''` is the finite set of nonempty intersections $`H\cap K` for $`K\in\mathcal{A}'`, with duplicates removed, regarded as an arrangement in $`H`.
:::

:::node "lem:restriction-geometry" (decl := OrlikSolomon.IsHyperplane.isHyperplaneIn_inf) (decl := OrlikSolomon.Arrangement.isHyperplaneIn_map_chart) (decl := OrlikSolomon.IsHyperplane.finrank_direction_add_one) (decl := OrlikSolomon.Arrangement.card_restriction_le) (decl := OrlikSolomon.Arrangement.card_restriction_lt) (decl := OrlikSolomon.IsEquation.comp_chart_eq_const_or_smul) (decl := OrlikSolomon.Arrangement.exists_representative) (decl := OrlikSolomon.DivisorPair.deletionPair) (decl := OrlikSolomon.IsEquation.ker_pull_chart) (decl := OrlikSolomon.IsEquation.quotientEquiv) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalization_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.surjective_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.ker_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.quotientEquiv) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway_inclusion) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit_mul) (decl := OrlikSolomon.SmoothAlg.exists_mapUnits_complementRestriction_eq_constUnit_mul_of_inf_eq) (decl := OrlikSolomon.DivisorPair.deletionPair_eqnUnit) (decl := OrlikSolomon.DivisorPair.fromStandard_deletionPair_compl) (decl := OrlikSolomon.DivisorPair.deletionPairHom)
Each retained intersection is a hyperplane in $`H`, so the restriction has ambient dimension $`n-1`, and it has at most $`|\mathcal{A}'|<|\mathcal{A}|` hyperplanes.
The restriction of an old equation is either a nonzero constant or a nonzero multiple of an equation for its retained hyperplane, and every retained hyperplane has an old representative.
The function $`f_H` cuts the smooth divisor $`D=H\cap U_{\mathcal{A}'}\simeq U_{\mathcal{A}''}` out of $`X=U_{\mathcal{A}'}`, with open complement $`U_{\mathcal{A}}`, transversely pulled back from $`\{0\}\subset\mathbb{A}^1`.
In the formalization the deletion pair is one certified divisor pair, for any equation of $`H`, in which the restriction map and the inclusion do not depend on the equation.
The transverse pullback is `DivisorPair.fromStandard`, which exists for every pair, and `deletionPairHom` compares the pairs of two equations.
The unit of an old equation restricts to a nonzero constant if its hyperplane misses $`H`, and otherwise to a nonzero constant times the unit of any equation of the retained hyperplane, so two old hyperplanes with the same trace have the same restricted unit up to a constant.
These statements hold over any field, including when a complement has no rational points, and when $`H` is a point.
:::

:::node "def:geometry-interface" (decl := OrlikSolomon.SmoothAlg) (decl := OrlikSolomon.SmoothAlg.point) (decl := OrlikSolomon.SmoothAlg.affineSpace) (decl := OrlikSolomon.SmoothAlg.polynomial) (decl := OrlikSolomon.SmoothAlg.laurent) (decl := OrlikSolomon.SmoothAlg.gm) (decl := OrlikSolomon.SmoothAlg.complement) (decl := OrlikSolomon.SmoothAlg.gmHom) (decl := OrlikSolomon.SmoothAlg.complementUnit) (decl := OrlikSolomon.SmoothAlg.complementUnit_smul) (decl := OrlikSolomon.DivisorPair) (decl := OrlikSolomon.DivisorPair.Hom) (decl := OrlikSolomon.DivisorPair.deletionPair) (remaining := "the two small targets (issue 15), and the cone and decone (issue 19)")
The geometry needed by the proof consists of a category of smooth affine objects, including a point, affine spaces, $`\mathbb{G}_m`, products with $`\mathbb{A}^1` and $`\mathbb{G}_m`, and arrangement complements, together with regular maps attached to invertible functions, and certified smooth-divisor pairs with transverse base-change squares.
This is a list of geometric constructions and identities, and it contains no cohomological conclusion.
:::

:::node "lem:geometry-adapter" (decl := OrlikSolomon.DivisorPair.standardPair) (decl := OrlikSolomon.DivisorPair.standardMap) (decl := OrlikSolomon.SmoothAlg.laurentSection) (decl := OrlikSolomon.Arrangement.ComplementRing) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway) (decl := OrlikSolomon.SmoothAlg.complementLift) (decl := OrlikSolomon.SmoothAlg.complementMap) (decl := OrlikSolomon.SmoothAlg.complementMap_comp) (decl := OrlikSolomon.SmoothAlg.complementMap_id) (decl := OrlikSolomon.DivisorPair.deletionPair) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalization_restriction) (decl := OrlikSolomon.Arrangement.ComplementRing.restriction_eq_map) (decl := OrlikSolomon.Arrangement.ComplementRing.isLocalizationAway_inclusion) (decl := OrlikSolomon.SmoothAlg.coneIso) (decl := OrlikSolomon.SmoothAlg.deconeIso) (remaining := "maps to affine images and normalized slices (issue 15)")
Localizations of polynomial algebras realize all of this.
The obligations are the standard pair $`(\mathbb{A}^1,0,\mathbb{G}_m)` and its products, the deletion pairs, the maps $`x` and $`xy` on $`\mathbb{A}^1\times\mathbb{G}_m` with the section $`x=1`, maps to affine images and normalized slices, affine coordinate changes, and the cone and decone isomorphism.
The declarations below cover the standard pair and its products, the maps $`x` and $`xy`, which are `standardMap` at the units $`1` and $`y`, and the section.
They also cover the complements themselves, which are displayed as the localization $`k[x_1,\ldots,x_n,1/P]`, with their universal property, and the affine coordinate changes, which are `complementMap` at an affine automorphism and its inverse.
They cover the deletion pairs, whose three rings are complements, with the compatibility of quotient and localization: the ring of the restriction is a localization of the coordinate ring of $`H`, and restriction of functions on complements is the localization of restriction of functions on $`V`.
The cone and decone isomorphisms are `coneIso` and `deconeIso`.
:::
