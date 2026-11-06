/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Generalized cohomology (deferred)" =>
%%%
tag := "generalized"
file := "generalized"
%%%

Nothing in this chapter is formalized, and nothing in it is being worked on.
The blueprint also describes a separate theorem, the _stable extension_, for theories that fail the point dimension axiom or lack an orientation, such as motivic or Milnor–Witt theories.
It is outside the current scope of this project, and it is included here so that the book accounts for every node of the blueprint.

The result is additive rather than multiplicative.
In a stable setting, the motive of the complement splits as a finite sum of diagonal spheres, because the middle map of each deletion triangle vanishes for connectivity reasons.
This computes generalized cohomology groups, but it does not give a ring presentation, and it does not say that a splitting preserves diagonals or products.
For those theories, constant unit classes and quadratic information can change the ring relations, so the exterior presentation is not imposed on them.
The ordinary main theorem of this book does not apply to them either, because its hypothesis includes the dimension axiom.

:::node "def:stable-realization" +deferred
An additive triangulated category with finite biproducts and coherent invertible bigraded shifts, together with an object $`M(\mathcal{A})` for each arrangement, such that $`M(\varnothing)` is the unit for affine spaces, deletion gives distinguished triangles, and the connectivity consequence $`\operatorname{Hom}(S^{i,i},S^{j+2,j+1})=0` holds for $`i,j\ge0`.
:::

:::node "lem:split-triangle" +deferred
A distinguished triangle whose middle map is zero yields a noncanonical isomorphism $`X\simeq Y\oplus Z[-1]`.
:::

:::node "thm:stable-splitting" +deferred
Every stable arrangement realization has a noncanonical isomorphism
$$`M(\mathcal{A})\simeq\bigoplus_{q=0}^n(S^{q,q})^{\oplus b_q(\mathcal{A})}.`
:::

:::node "cor:generalized" +deferred
For an object $`E`, a choice of splitting gives
$$`\operatorname{Hom}(M(\mathcal{A}),\Sigma^{a,b}E)\simeq\bigoplus_{q=0}^n\operatorname{Hom}(\mathbf{1},\Sigma^{a-q,b-q}E)^{\oplus b_q(\mathcal{A})},`
natural in $`E`.
:::

:::node "def:universal-coefficients" +deferred
With a symmetric monoidal structure, compatible sphere shifts and a counital cocommutative diagonal on each $`M(\mathcal{A})`, the diagonal cohomotopy rings $`D(k)` and $`D(\mathcal{A})` and a canonical evaluation map $`\Theta_E:C_E(k)\otimes_{D(k)}D(\mathcal{A})\to C_E(\mathcal{A})` are defined for every commutative ring object $`E`, with the graded symmetry induced by the sphere twists.
:::

:::node "thm:universal-basechange" +deferred
For every arrangement and every commutative ring object $`E`, the map $`\Theta_E` is a canonical isomorphism of bigraded algebras with the indicated symmetry.
:::
