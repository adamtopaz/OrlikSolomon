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
The two blueprint nodes about the interface, {bp "def:geometry-interface"}[] and {bp "lem:geometry-adapter"}[], are therefore to be discharged by construction, and the declarations that do so will be named in their boxes.

:::node "def:arrangement"
An affine hyperplane in a finite-dimensional $`k`-vector space $`V` is a nonempty proper affine subspace of codimension one, and an arrangement is a finite set of these.
An equation for $`H` is an affine map $`f_H:V\to k` with nonzero linear part and zero locus $`H`.
:::

:::node "lem:equations"
Every hyperplane has an equation, and two equations for the same hyperplane differ by a unique element of $`k^\times`.
A nonempty intersection of hyperplanes has a $`k`-point and is an affine space whose direction is the intersection of the kernels of the linear parts, and its codimension is the rank of the system of equations.
These are statements of linear algebra over $`k`, not about rational points of arbitrary varieties.
:::

:::node "def:deletion"
For $`H\in\mathcal{A}`, the deletion is $`\mathcal{A}'=\mathcal{A}\setminus\{H\}`, and the restriction $`\mathcal{A}''` is the finite set of nonempty intersections $`H\cap K` for $`K\in\mathcal{A}'`, with duplicates removed, regarded as an arrangement in $`H`.
:::

:::node "lem:restriction-geometry"
Each retained intersection is a hyperplane in $`H`, so the restriction has ambient dimension $`n-1`, and it has at most $`|\mathcal{A}'|<|\mathcal{A}|` hyperplanes.
The restriction of an old equation is either a nonzero constant or a nonzero multiple of an equation for its retained hyperplane, and every retained hyperplane has an old representative.
The function $`f_H` cuts the smooth divisor $`D=H\cap U_{\mathcal{A}'}\simeq U_{\mathcal{A}''}` out of $`X=U_{\mathcal{A}'}`, with open complement $`U_{\mathcal{A}}`, transversely pulled back from $`\{0\}\subset\mathbb{A}^1`.
:::

:::node "def:geometry-interface"
The geometry needed by the proof consists of a category of smooth affine objects, including a point, affine spaces, $`\mathbb{G}_m`, products with $`\mathbb{A}^1` and $`\mathbb{G}_m`, and arrangement complements, together with regular maps attached to invertible functions, and certified smooth-divisor pairs with transverse base-change squares.
This is a list of geometric constructions and identities, and it contains no cohomological conclusion.
:::

:::node "lem:geometry-adapter"
Localizations of polynomial algebras realize all of this.
The obligations are the standard pair $`(\mathbb{A}^1,0,\mathbb{G}_m)` and its products, the deletion pairs, the maps $`x` and $`xy` on $`\mathbb{A}^1\times\mathbb{G}_m` with the section $`x=1`, maps to affine images and normalized slices, affine coordinate changes, and the cone and decone isomorphism.
:::
