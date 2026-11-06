/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "The first induction: generation and the dimension bound" =>
%%%
tag := "first-induction"
file := "first-induction"
%%%

This induction concerns cohomology alone, and the Orlik–Solomon algebra plays no part in it.
Say that $`\mathcal{A}` is _generated_ if $`C(U_{\mathcal{A}})` is spanned over $`B` by finite products of the classes $`[f_H]`, and _bounded_ if its homogeneous pieces vanish outside $`0\le p\le\dim V`.
The induction is on $`|\mathcal{A}|`, over all ambient spaces.

The key observation is why the deletion sequence becomes short exact.
Nothing about the normal bundle is needed.
If the restriction is generated, then every class on the divisor is a combination of restricted logarithmic monomials, and these lift to $`U_{\mathcal{A}'}`, so restriction to the divisor is surjective.
Multiplying a lift by $`[f_H]` then produces a preimage under the residue.
So the residue is surjective, hence the Gysin map vanishes, hence the open pullback is injective.
This is the point at which the vanishing of the Gysin map is proved.

:::node "lem:restriction-surj"
If the restriction $`\mathcal{A}''` is generated, then the restriction map $`i^*:C(U_{\mathcal{A}'})\to C(U_{\mathcal{A}''})` is surjective.
:::

:::node "lem:ses"
If the restriction $`\mathcal{A}''` is generated, then the residue is surjective, the Gysin map is zero, and
$$`0\to C(U_{\mathcal{A}'})\xrightarrow{\ j^*\ }C(U_{\mathcal{A}})\xrightarrow{\ r\ }C(U_{\mathcal{A}''})\to0`
is an exact sequence of $`B`-modules, with $`r` of shift $`(-1,-1)`.
:::

:::node "thm:generation"
Every arrangement is generated and bounded, so the short exact sequence above holds for every deletion.
:::

:::node "lem:basis-ses" (decl := OrlikSolomon.basisOfShortExact) (decl := OrlikSolomon.coe_basisOfShortExact)
In a short exact sequence of modules, a basis of the left term together with lifts of a basis of the right term form a basis of the middle term.
:::

:::node "thm:cohom-basis"
For every arrangement, $`C(U_{\mathcal{A}})` has a finite $`B`-basis of products of logarithmic classes along words in the hyperplanes, with each basis vector of bidegree $`(q,q)` for a word of length $`q\le n`.
The explicit basis is the useful output.
A numerical rank would not be well defined in general, since the theorem also covers the zero coefficient ring.
:::
