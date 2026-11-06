/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "Logarithmic classes" =>
%%%
tag := "logarithms"
file := "logarithms"
%%%

Logarithmic classes are not part of the axioms.
They are constructed from the cohomology of $`\mathbb{G}_m`, which in turn comes from the single divisor pair $`(\mathbb{A}^1,0,\mathbb{G}_m)`: the source and target of its Gysin map are concentrated in cohomological degree zero, and the map has shift $`(2,1)`, so it vanishes for degree reasons and the residue is surjective.

Two proofs here avoid tempting shortcuts.
The relation $`\tau^2=0` comes from the fact that $`C(\mathbb{G}_m)` has nothing in cohomological degree two, and not from $`2\tau^2=0`, which would say nothing in characteristic two.
And additivity $`[fg]=[f]+[g]` does not use a Künneth theorem: it compares the maps $`x` and $`xy` from $`\mathbb{A}^1\times\mathbb{G}_m` to $`\mathbb{A}^1`, which have the same residue along $`x=0`, and it identifies their difference by restricting to $`x=1`.

:::node "lem:gm"
There is a unique $`\tau` in $`C(\mathbb{G}_m)` of bidegree $`(1,1)` with residue $`1` at the origin.
The map $`(a,b)\mapsto a+\tau b` is a $`B`-linear equivalence from $`B\oplus B` to $`C(\mathbb{G}_m)`, with the second summand shifted by $`(1,1)`, and in particular $`\tau^2=0`.
:::

:::node "def:log"
For an invertible regular function $`f` on $`X`, viewed as a map to $`\mathbb{G}_m`, set $`[f]=f^*\tau`, a class of bidegree $`(1,1)` in $`C(X)`.
:::

:::node "lem:log-basic"
Logarithmic classes commute with pullback, $`[c]=0` for $`c\in k^\times`, and $`[f]^2=0`.
:::

:::node "lem:log-mul"
For invertible regular functions $`f` and $`g` and $`c\in k^\times`, we have $`[fg]=[f]+[g]`, $`[f/g]=[f]-[g]` and $`[cf]=[f]`.
:::

:::node "lem:log-residue"
In a deletion pair, the residue of $`[f_H]` is $`1`, and $`r([f_H]\,j^*\beta)=i^*\beta` for every $`\beta` in $`C(U_{\mathcal{A}'})`.
The class $`[f_H]` must stay on the left, because moving it introduces a sign.
:::
