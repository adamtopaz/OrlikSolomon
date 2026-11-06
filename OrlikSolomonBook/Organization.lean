/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "How the proof is organized" =>
%%%
tag := "organization"
file := "organization"
%%%

The proof consists of two separate inductions on the number of hyperplanes, with a construction between them.

Both inductions use deletion and restriction.
Pick a hyperplane $`H\in\mathcal{A}`, and let $`\mathcal{A}'=\mathcal{A}\setminus\{H\}` be the deletion and $`\mathcal{A}''` be the restriction, the arrangement in $`H` of the nonempty intersections $`H\cap K` for $`K\in\mathcal{A}'`, with duplicates removed.
The equation $`f_H` cuts a smooth divisor $`U_{\mathcal{A}''}` out of $`U_{\mathcal{A}'}`, with open complement $`U_{\mathcal{A}}`, so the axioms give a long exact sequence relating the three.
Both smaller arrangements have fewer hyperplanes, but the restriction lives in a smaller ambient space.
So every inductive statement must quantify over all ambient spaces at once: with the ambient space fixed, it would not supply its own induction hypothesis.

*From the axioms to logarithms.*
The axioms do not mention logarithmic classes.
{ref "logarithms"}[The first step] constructs a canonical class $`\tau` on $`\mathbb{G}_m` from the divisor pair $`(\mathbb{A}^1,0,\mathbb{G}_m)` and the dimension axiom, and proves that $`f\mapsto[f]=f^*\tau` behaves like a logarithm.

*The first induction.*
{ref "first-induction"}[This induction] proves three things about cohomology alone, without mentioning the Orlik–Solomon algebra: logarithmic classes generate $`C(U_{\mathcal{A}})` over $`B`, the cohomology vanishes outside degrees $`0\le p\le n`, and the deletion sequence is short exact.
That short exactness is where the vanishing of the Gysin map is proved rather than assumed.

*The realization map.*
{ref "presentation"}[The construction in the middle] shows that the classes $`[f_H]` satisfy the Orlik–Solomon relations, which gives the map $`\Phi_{\mathcal{A}}`.
Each relation is pulled back from a low-dimensional auxiliary arrangement, where it holds because the degree exceeds the dimension.
These auxiliary arrangements have nothing to do with the cardinality of $`\mathcal{A}`, which is why the dimension bound must be finished for all arrangements first, and why the two inductions cannot be merged into one.
Generation already shows that $`\Phi_{\mathcal{A}}` is surjective.

*The second induction.*
{ref "second-induction"}[This induction] proves that the relations are complete, meaning that $`\Phi_{\mathcal{A}}` is injective.
It compares the Orlik–Solomon algebras of $`\mathcal{A}'`, $`\mathcal{A}` and $`\mathcal{A}''` with the short exact sequence from the first induction.
The subtle point is that this comparison takes place in a quotient of modules, not of rings.

*What follows.*
{ref "multiplicities"}[The ranks] of all the groups are computed by a deletion–restriction recursion, and {ref "projective"}[the projective theorem] is deduced from the affine theorem applied to the central cone.
