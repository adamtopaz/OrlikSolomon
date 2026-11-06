/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual
open OrlikSolomonBook

#doc (Manual) "The cohomology axioms" =>
%%%
tag := "axioms"
file := "axioms"
%%%

This chapter is the trust boundary of the project: everything else is proved from what is listed here.
Each axiom must hold in real theories, since a structure with unsatisfiable axioms would make the main theorem vacuous.

*A long exact sequence in disguise.*
For a smooth divisor $`D` in $`X` with open complement $`U`, the usual localization sequence is
$$`\cdots\to H^{p-2,w-1}(D)\to H^{p,w}(X)\to H^{p,w}(U)\to H^{p-1,w-1}(D)\to H^{p+1,w}(X)\to\cdots.`
Taking direct sums over all $`(p,w)` turns this into three maps between total cohomology rings, a Gysin map $`g` of shift $`(2,1)`, the open pullback $`j^*`, and a residue $`r` of shift $`(-1,-1)`, with exactness at each of the three places.
The three exactness statements together encode the whole long exact sequence.
They do _not_ say that any sequence is short exact.
Working only with the diagonal $`\bigoplus_q H^{q,q}` from the start would lose the off-diagonal Gysin terms and could assume their vanishing by accident, and that vanishing is something the proof has to earn.

No Künneth theorem, Poincaré duality, weights, resolution of singularities, or dimension bound for general smooth affine schemes is needed.

:::node "def:cohomology" (decl := OrlikSolomon.OrdinaryTheory) (decl := OrlikSolomon.OrdinaryTheory.gradeZeroEquiv) (decl := OrlikSolomon.OrdinaryTheory.subsingleton_obj_of_subsingleton) (decl := OrlikSolomon.OrdinaryTheory.pointEquiv) (decl := OrlikSolomon.OrdinaryTheory.algebraMap_mem_grading_point_iff) (decl := OrlikSolomon.OrdinaryTheory.exists_algebraMap_eq_of_mem_grading_point) (decl := OrlikSolomon.OrdinaryTheory.polynomialEquiv) (decl := OrlikSolomon.OrdinaryTheory.map_compl_map_j) (remaining := "the sentence of C3 that iterating affine-line invariance gives the same conclusion for affine spaces, which is not yet stated at the level of cohomology (issue 13, through complement_empty_induction)")
The structure consists of the following data and axioms.
 * *C1.* A weight-graded commutative $`R`-algebra $`B=\bigoplus_w B_w`, with $`R` identified with $`B_0`, and for each $`X` an internally bigraded ring $`C(X)` that is a $`B`-algebra, with central $`B`-action and $`B_w` landing in bidegree $`(0,w)`.
 * *C2.* Functorial pullbacks, which are unital $`B`-algebra maps preserving bidegree, with homogeneous classes supercommuting according to cohomological degree.
 * *C3.* The point has cohomology $`B`, entirely in cohomological degree zero, and pullback along $`X\times\mathbb{A}^1\to X` is an isomorphism.
 * *C4.* For every certified smooth-divisor pair $`i:D\to X`, $`j:U\to X`, there are $`B`-linear maps $`g:C(D)\to C(X)` of shift $`(2,1)` and $`r:C(U)\to C(D)` of shift $`(-1,-1)`, with $`\operatorname{im}g=\ker j^*`, $`\operatorname{im}j^*=\ker r` and $`\operatorname{im}r=\ker g`.
 * *C5.* These maps commute with transverse pullback, and the boundary projection formula $`r(\alpha\,j^*\beta)=r(\alpha)\,i^*\beta` holds for $`\alpha` of bidegree $`(1,1)`.

The design for the formalization is that the total cohomology is a functor on smooth $`k`-algebras and that transverse pullbacks allow a unit multiple of the equation.
No axiom about the empty object is needed, because the pair $`(A,1)` already forces the zero ring to have zero cohomology.
:::

:::node "lem:standard-bridge"
A cohomology presented in the familiar degreewise way, with products, twists, the point dimension axiom, affine-line invariance, localization with supports, oriented divisor purity, transverse naturality and the boundary projection formula, gives an instance of the structure.
Its degreewise long exact sequence is recovered from the three total exactness statements by {bp "lem:extraction"}[homogeneous extraction].
:::
