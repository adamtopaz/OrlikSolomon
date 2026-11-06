/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "Logarithmic classes" =>
%%%
tag := "logarithms"
file := "logarithms"
htmlSplit := .never
%%%

Logarithmic classes are not part of the axioms.
This chapter constructs them, and shows that $`f\mapsto[f]` behaves as a logarithm should.
Everything that later chapters know about the classes $`[f_H]` is proved here.

# The class on the multiplicative group

Apply the axioms to the single divisor pair $`(\mathbb{A}^1,0,\mathbb{G}_m)`.
By the dimension axiom and affine-line invariance, the cohomology of both $`0` and $`\mathbb{A}^1` is $`B`, concentrated in cohomological degree zero.
The Gysin map has shift $`(2,1)`, so it sends cohomological degree zero to degree two, where the target vanishes.
So the Gysin map is zero, for degree reasons alone, in this one case.
Exactness then makes the residue surjective and the pullback from $`\mathbb{A}^1` injective.

So $`1\in B` has a preimage under the residue, and by {bp "lem:extraction"}[homogeneous extraction] it has one in bidegree $`(1,1)`.
That preimage is unique.
Two choices differ by an element of the kernel of the residue, which is the image of the pullback, and that image lies in cohomological degree zero.
Their difference has cohomological degree one, so it is zero, and the class $`\tau` is determined by the axioms with no choice.

Subtracting $`\tau` times the residue splits the sequence, so $`C(\mathbb{G}_m)=B\oplus\tau B`, with nothing outside cohomological degrees zero and one.

*Why $`\tau^2=0`.*
Graded commutativity gives only $`\tau^2=-\tau^2`, that is $`2\tau^2=0`, which says nothing in characteristic two or in the presence of $`2`-torsion.
The right reason is the description just given: $`\tau^2` has cohomological degree two, and $`C(\mathbb{G}_m)` has nothing there.
Every square-zero statement about logarithmic classes is a pullback of this one, and it is why the main theorem holds with coefficients in $`\mathbb{Z}/2`.

:::node "lem:gm" (decl := OrlikSolomon.OrdinaryTheory.existsUnique_tau) (decl := OrlikSolomon.OrdinaryTheory.tau) (decl := OrlikSolomon.OrdinaryTheory.gmEquiv) (decl := OrlikSolomon.OrdinaryTheory.gmEquiv_apply) (decl := OrlikSolomon.OrdinaryTheory.gmEquiv_mem_grading_zero_iff) (decl := OrlikSolomon.OrdinaryTheory.gmEquiv_mem_grading_one_iff) (decl := OrlikSolomon.OrdinaryTheory.eq_zero_of_mem_grading_gm) (decl := OrlikSolomon.OrdinaryTheory.tau_mul_tau)
There is a unique $`\tau` in $`C(\mathbb{G}_m)` of bidegree $`(1,1)` with residue $`1` at the origin.
The map $`(a,b)\mapsto a+\tau b` is a $`B`-linear equivalence from $`B\oplus B` to $`C(\mathbb{G}_m)`, with the second summand shifted by $`(1,1)`, and in particular $`\tau^2=0`.

The formalization states the shift degree by degree: the piece of bidegree $`(0,w)` is $`B_w` in the first summand, the piece of bidegree $`(1,w)` is $`B_{w-1}` in the second summand, and every other cohomological degree vanishes.
:::

# Logarithms

A unit $`u` of a smooth algebra $`A` is the same thing as a regular map $`\operatorname{Spec}A\to\mathbb{G}_m`, so it pulls $`\tau` back to a class $`[u]` of bidegree $`(1,1)`.

:::node "def:log" (decl := OrlikSolomon.OrdinaryTheory.logClass) (decl := OrlikSolomon.OrdinaryTheory.logClass_mem_grading)
For an invertible regular function $`f` on $`X`, viewed as a map to $`\mathbb{G}_m`, set $`[f]=f^*\tau`, a class of bidegree $`(1,1)` in $`C(X)`.

In the formalization, an invertible regular function on $`X=\operatorname{Spec}A` is a unit of $`A`.
:::

Functoriality gives naturality at once.
A constant in $`k^\times` factors through the point, where there is nothing in cohomological degree one, so its class vanishes.
And $`[f]^2=f^*(\tau^2)=0`.

:::node "lem:log-basic" (decl := OrlikSolomon.OrdinaryTheory.map_logClass) (decl := OrlikSolomon.OrdinaryTheory.logClass_units_map_algebraMap) (decl := OrlikSolomon.OrdinaryTheory.logClass_mul_self)
Logarithmic classes commute with pullback, $`[c]=0` for $`c\in k^\times`, and $`[f]^2=0`.
:::

*Additivity without Künneth.*
One could try to prove $`[fg]=[f]+[g]` by computing the cohomology of $`\mathbb{G}_m^2` with a Künneth formula, but the axioms provide none.
Instead, the proof compares two transverse maps.
On $`\mathbb{A}^1_x\times\mathbb{G}_{m,y}`, with divisor $`x=0` and complement $`\mathbb{G}_m^2`, both $`x` and $`xy` are transverse pullbacks of the standard pair, because $`xy` is a unit multiple of $`x`.
So by naturality of the residue, $`[x]` and $`[xy]` both have residue $`1` along $`x=0`.
Their difference has residue zero, so it is the restriction of a class on $`\mathbb{A}^1\times\mathbb{G}_m`.
By affine-line invariance, that class is pulled back from $`\mathbb{G}_{m,y}`, so it is determined by restricting to the section $`x=1`.
There, $`[xy]-[x]` becomes $`[y]-[1]=[y]`.
Hence $`[xy]=[x]+[y]`, and pulling back along $`(f,g)` gives the formula in general.

The library runs this argument over an arbitrary smooth algebra $`A` with a unit $`y`, on the pair $`(A[x],A,A[x,x^{-1}],x)`, which saves one pullback and needs no information about the degree of the auxiliary class.

:::node "lem:log-mul" (decl := OrlikSolomon.OrdinaryTheory.logClass_mul) (decl := OrlikSolomon.OrdinaryTheory.logClass_div) (decl := OrlikSolomon.OrdinaryTheory.logClass_units_map_algebraMap_mul)
For invertible regular functions $`f` and $`g` and $`c\in k^\times`, we have $`[fg]=[f]+[g]`, $`[f/g]=[f]-[g]` and $`[cf]=[f]`.
:::

# Residues of equations

The residue of a logarithm is what connects logarithms to the deletion sequence.
If $`f_H` cuts out $`D` in $`X`, then $`f_H` is a transverse pullback of the coordinate on $`\mathbb{A}^1`, so naturality gives $`r[f_H]=1`.
Combining this with the boundary projection formula gives the formula on which both inductions are built:
$$`r([f_H]\,j^*\beta)=i^*\beta.`
It says that multiplication by $`[f_H]` splits the residue, on the classes that come from $`X`.
The class $`[f_H]` must stay on the left, because moving it introduces a sign.

:::node "lem:log-residue" (decl := OrlikSolomon.OrdinaryTheory.residue_logClass_eqnUnit) (decl := OrlikSolomon.OrdinaryTheory.residue_logClass_eqnUnit_mul) (decl := OrlikSolomon.OrdinaryTheory.deletionResidue_logClass) (decl := OrlikSolomon.OrdinaryTheory.deletionResidue_logClass_mul)
In a deletion pair, the residue of $`[f_H]` is $`1`, and $`r([f_H]\,j^*\beta)=i^*\beta` for every $`\beta` in $`C(U_{\mathcal{A}'})`.

The formalization proves both formulas for every divisor pair, with $`f_H` the equation of the pair, and then for deletion pairs, with $`f_H` any equation of $`H`, typed by the complements themselves.
:::
