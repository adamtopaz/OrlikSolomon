/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "The cohomology axioms" =>
%%%
tag := "axioms"
file := "axioms"
htmlSplit := .never
%%%

This chapter is the trust boundary of the project: everything else is proved from what is listed here.
The hypothesis of the main theorem is a value of the structure {name OrlikSolomon.OrdinaryTheory}`OrdinaryTheory`.
A structure in Lean is a package of data and properties, and its components are called fields.
So the fields below are the axioms, and the theorem holds for every value of the structure.

# A long exact sequence in disguise

For a smooth divisor $`D` in $`X` with open complement $`U`, the usual localization sequence is
$$`\cdots\to H^{p-2,w-1}(D)\to H^{p,w}(X)\to H^{p,w}(U)\to H^{p-1,w-1}(D)\to H^{p+1,w}(X)\to\cdots.`
Taking direct sums over all $`(p,w)` turns this into three maps between total cohomology rings, a Gysin map $`g` of shift $`(2,1)`, the open pullback $`j^*`, and a residue $`r` of shift $`(-1,-1)`, with exactness at each of the three places.
The three exactness statements together encode the whole long exact sequence.
They do _not_ say that any sequence is short exact.

Working only with the diagonal $`\bigoplus_q H^{q,q}` from the start would be simpler, and wrong.
The Gysin map of shift $`(2,1)` moves the diagonal off the diagonal, so a theory restricted to the diagonal would not see it, and could assume its vanishing by accident.
That vanishing is something the proof has to earn.
This is why the axioms are stated for the total cohomology, over all bidegrees.

# The fields of the structure

The structure has the following parameters: a commutative ring $`k`, which is a field in the theorems about arrangements; a commutative ring $`R`; a commutative $`R`-algebra $`B`; and its weight grading, with pieces `ℬ w` $`=B_w`.
The fields fall into six groups, which follow the blueprint's list C1 to C5.
For each group the paragraph also says what it means in the model that was used to check it by hand, $`H^{p,w}(X)=H^p(X(\mathbb{C});R)\,t^w` with $`B=R[t,t^{-1}]` and $`B_w=Rt^w`.

 * *Coefficients (C1).* {name OrlikSolomon.OrdinaryTheory.bijective_algebraMap_gradeZero}`bijective_algebraMap_gradeZero` says that the structure map identifies $`R` with $`B_0`. The other pieces $`B_w` play the role of Tate lines, and no generator of them is ever chosen. In the model, the map is $`R\to Rt^0`.
 * *Total cohomology (C1).* {name OrlikSolomon.OrdinaryTheory.C}`C` is a functor from {name OrlikSolomon.SmoothAlg}`SmoothAlg` `k` to $`B`-algebras, which need not be commutative, since cup products of odd classes are not. Being a $`B`-algebra includes that the $`B`-action is central. {name OrlikSolomon.OrdinaryTheory.grading}`grading` gives the pieces $`H^{p,w}(X)` as $`R`-submodules, {name OrlikSolomon.OrdinaryTheory.gradedAlgebra}`gradedAlgebra` says that $`C(X)` is their internal direct sum compatibly with products, and {name OrlikSolomon.OrdinaryTheory.algebraMap_mem_grading}`algebraMap_mem_grading` says that $`B_w` lands in bidegree $`(0,w)`. The fields {name OrlikSolomon.OrdinaryTheory.algebra}`algebra` and {name OrlikSolomon.OrdinaryTheory.isScalarTower}`isScalarTower` make the $`R`-action the one induced from $`B`.
 * *Pullbacks and products (C2).* Pullbacks are the morphisms of the functor, so they are unital $`B`-algebra maps. {name OrlikSolomon.OrdinaryTheory.isHomogeneousOfShift_map}`isHomogeneousOfShift_map` says that they preserve the bidegree, and {name OrlikSolomon.OrdinaryTheory.isGradedCommutative}`isGradedCommutative` says that homogeneous classes supercommute with a sign depending only on $`p`. It does not follow that an odd class squares to zero, and {ref "algebra"}[no argument assumes this].
 * *The point and the affine line (C3).* {name OrlikSolomon.OrdinaryTheory.bijective_algebraMap_point}`bijective_algebraMap_point` and {name OrlikSolomon.OrdinaryTheory.eq_zero_of_mem_grading_point}`eq_zero_of_mem_grading_point` say that the cohomology of the point is $`B`, entirely in cohomological degree zero. {name OrlikSolomon.OrdinaryTheory.bijective_map_polynomialC}`bijective_map_polynomialC` says that pullback along $`X\times\mathbb{A}^1\to X` is an isomorphism for every smooth $`X`. In the model, these are the cohomology of a point and homotopy invariance for the factor $`\mathbb{C}`.
 * *Localization (C4).* For every divisor pair, {name OrlikSolomon.OrdinaryTheory.gysin}`gysin` and {name OrlikSolomon.OrdinaryTheory.residue}`residue` are $`B`-linear maps, of shifts $`(2,1)` and $`(-1,-1)` by {name OrlikSolomon.OrdinaryTheory.isHomogeneousOfShift_gysin}`isHomogeneousOfShift_gysin` and {name OrlikSolomon.OrdinaryTheory.isHomogeneousOfShift_residue}`isHomogeneousOfShift_residue`. The three fields {name OrlikSolomon.OrdinaryTheory.exact_gysin_map}`exact_gysin_map`, {name OrlikSolomon.OrdinaryTheory.exact_map_residue}`exact_map_residue` and {name OrlikSolomon.OrdinaryTheory.exact_residue_gysin}`exact_residue_gysin` say that $`\operatorname{im}g=\ker j^*`, $`\operatorname{im}j^*=\ker r` and $`\operatorname{im}r=\ker g`. In the model, the Gysin map is the Thom isomorphism followed by forgetting supports, times $`t`, and the residue is the connecting map followed by the inverse Thom isomorphism, times $`t^{-1}`, which accounts for the shifts.
 * *Naturality and the projection formula (C5).* {name OrlikSolomon.OrdinaryTheory.gysin_map}`gysin_map` and {name OrlikSolomon.OrdinaryTheory.residue_map}`residue_map` say that these maps commute with transverse pullback, and {name OrlikSolomon.OrdinaryTheory.residue_mul_map}`residue_mul_map` is the boundary projection formula $`r(\alpha\,j^*\beta)=r(\alpha)\,i^*\beta` for $`\alpha` of bidegree $`(1,1)`. The proof uses the residue square and not the Gysin square, which is there because C5 asks for the whole sequence to commute.

The projection formula is asked for only in bidegree $`(1,1)`, the one case that the proof uses, because a weaker hypothesis gives a stronger theorem.
No axiom about the empty scheme is needed: the divisor pair $`(A,1)` has an empty divisor, and it already forces the zero ring to have zero cohomology.

What is not a field matters as much.
There is no field for logarithmic classes, for generation, for the vanishing of any arrangement class, for surjectivity of residues, for vanishing of Gysin maps, for short exactness, for freeness, or for the theorem itself.
The class $`\tau` of the next chapter is constructed from the fields above.
No Künneth theorem, Poincaré duality, weights, resolution of singularities, or dimension bound for general smooth affine schemes is assumed.

:::node "def:cohomology" (decl := OrlikSolomon.OrdinaryTheory) (decl := OrlikSolomon.OrdinaryTheory.gradeZeroEquiv) (decl := OrlikSolomon.OrdinaryTheory.subsingleton_obj_of_subsingleton) (decl := OrlikSolomon.OrdinaryTheory.pointEquiv) (decl := OrlikSolomon.OrdinaryTheory.algebraMap_mem_grading_point_iff) (decl := OrlikSolomon.OrdinaryTheory.exists_algebraMap_eq_of_mem_grading_point) (decl := OrlikSolomon.OrdinaryTheory.polynomialEquiv) (decl := OrlikSolomon.OrdinaryTheory.map_compl_map_j) (decl := OrlikSolomon.OrdinaryTheory.affineSpaceEquiv) (decl := OrlikSolomon.OrdinaryTheory.bijective_map_fromPoint_affineSpace) (decl := OrlikSolomon.OrdinaryTheory.eq_zero_of_mem_grading_affineSpace) (decl := OrlikSolomon.OrdinaryTheory.algebraMap_mem_grading_affineSpace_iff)
The structure consists of the following data and axioms.
 * *C1.* A weight-graded commutative $`R`-algebra $`B=\bigoplus_w B_w`, with $`R` identified with $`B_0`, and for each $`X` an internally bigraded ring $`C(X)` that is a $`B`-algebra, with central $`B`-action and $`B_w` landing in bidegree $`(0,w)`.
 * *C2.* Functorial pullbacks, which are unital $`B`-algebra maps preserving bidegree, with homogeneous classes supercommuting according to cohomological degree. The empty object has zero cohomology.
 * *C3.* The point has cohomology $`B`, entirely in cohomological degree zero, and pullback along $`X\times\mathbb{A}^1\to X` is an isomorphism, which by iteration gives the same conclusion for affine spaces.
 * *C4.* For every certified smooth-divisor pair $`i:D\to X`, $`j:U\to X`, there are $`B`-linear maps $`g:C(D)\to C(X)` of shift $`(2,1)` and $`r:C(U)\to C(D)` of shift $`(-1,-1)`, with $`\operatorname{im}g=\ker j^*`, $`\operatorname{im}j^*=\ker r` and $`\operatorname{im}r=\ker g`.
 * *C5.* These maps commute with transverse pullback, and the boundary projection formula $`r(\alpha\,j^*\beta)=r(\alpha)\,i^*\beta` holds for $`\alpha` of bidegree $`(1,1)`.

In the formalization the total cohomology is a functor on smooth $`k`-algebras, and transverse pullbacks allow a unit multiple of the equation.
The statements about the empty object and about affine spaces are consequences of the fields, not fields, and they are among the declarations below.
:::

# How the axioms have been checked, and how they have not

A structure with unsatisfiable axioms would make the main theorem vacuous, so each field has to hold in real theories.
Here is the exact state of that check.

*In Lean, there is one nonzero instance.*
For every field $`k` of characteristic zero, {name OrlikSolomon.DeRham.ordinaryTheory}`DeRham.ordinaryTheory` `k` is a value of the structure: algebraic de Rham cohomology, with $`R=k` and $`B=k[t,t^{-1}]`, constructed in {ref "de-rham"}[its own chapter].
Its coefficient ring and its cohomology of the point are nonzero, and every field is proved for it, none weakened, so the axioms are not vacuous.
The other values of the structure constructed in Lean are the zero theories {name OrlikSolomon.Sanity.zeroTheory}`zeroTheory` and {name OrlikSolomon.Sanity.zeroBridgeTheory}`zeroBridgeTheory`, with zero coefficients, the second built by the bridge below from zero degreewise data.

```lean -show
noncomputable section
open OrlikSolomon CategoryTheory
universe u v w z t
```

```lean
example (k : Type u) [Field k] [CharZero k] :
    OrdinaryTheory k (laurentGrading k) :=
  DeRham.ordinaryTheory k

example (k : Type u) [CommRing k] :
    OrdinaryTheory.{u, v, w, z} k
      Sanity.zeroWeight.{v, w} :=
  Sanity.zeroTheory k
```

The zero theories test the zero-ring edge case.
They say nothing about the substantive axioms, all of which hold in them trivially.
For the model of singular cohomology below, the one thing checked in Lean is its coefficient axiom $`R\simeq B_0` for $`B=R[t,t^{-1}]`, which is {name OrlikSolomon.Sanity.bijective_algebraMap_laurentWeight}`bijective_algebraMap_laurentWeight`.

*By hand, for singular cohomology.*
Every field has been checked by hand against complex singular cohomology, in the model above, for a field with a chosen embedding in $`\mathbb{C}`.
The topological inputs are the long exact sequence of the pair $`(X(\mathbb{C}),U(\mathbb{C}))` and the Thom isomorphism of the complex normal line of $`D`.
The comments on the fields of the structure record the outcome, and you can read them by opening the declarations of {bp "def:cohomology"}[its box].
This is a mathematical argument, not a formal one.

*By hand, for $`\ell`-adic cohomology.*
The analogous interpretation uses $`H^p(X_{k^{\mathrm{sep}}};\mathbb{Z}_\ell(w))`, with $`\ell` invertible in $`k`, and oriented divisor purity with the same shift of twist.
The source comments record this too, and they also record what a Lean instance would still have to supply: passing from finite-coefficient localization to an integral $`\ell`-adic theory, and implementing coherent twists with strict products.

*Which theories are intended, and which are not.*
Geometric Betti and $`\ell`-adic cohomology are the intended ordinary instances, and rigid cohomology is a further intended example, with its localization and purity theorems to be supplied when building an instance.
Algebraic de Rham cohomology in characteristic zero is the one such example built in Lean, and instantiating the main theorems at it gives {bp "cor:dr-affine"}[] and {bp "cor:dr-projective"}[].
Ordinary crystalline cohomology of a nonproper variety is not automatically an instance, because affine-line invariance fails in the naive theory.
Arithmetic cohomology over a nonclosed field generally has higher Galois cohomology at the point and fails the dimension axiom.
None of this is formalized: these are the boundaries of application, not extra hypotheses of the theorem.

# The bridge from a degreewise theory

The structure above is convenient for proofs and unfamiliar as an input.
A standard cohomology theory is usually presented degree by degree, so the library also provides a constructor from that presentation.
Its input has two parts.

{name OrlikSolomon.DegreewiseTheory}`DegreewiseTheory` is the part about products and functoriality.
It supplies the groups $`H^{p,w}(X)` indexed by bidegree, the indexed cup products, the pullbacks, the coefficient maps $`B_w\to H^{0,w}(X)`, and the point and affine-line conditions in each bidegree.
Its products supercommute according to cohomological degree.

{name OrlikSolomon.SupportsAndPurity}`SupportsAndPurity` is the part about localization.
It supplies the groups with supports $`H_D^{p,w}(X)`, for every divisor pair, with the maps
$$`H_D^{p,w}(X)\to H^{p,w}(X),\qquad H^{p,w}(U)\to H_D^{p+1,w}(X),\qquad H^{p,w}(D)\xrightarrow{\ \sim\ }H_D^{p+2,w+1}(X),`
which are forgetting supports, the connecting map, and oriented purity.
Its exactness fields are the localization sequence with supports, degree by degree.
It also supplies transverse pullback on supports, compatible with all three maps, and the product of a supported class with an ambient class, with the usual identities for purity and for the boundary.

From these, {name OrlikSolomon.ofSupportsAndPurity}`ofSupportsAndPurity` builds a value of the structure.

```lean
example {k : Type u} [CommRing k]
    {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (D : DegreewiseTheory.{u, v, w, z} k ℬ)
    (S : SupportsAndPurity.{u, v, w, z, t} D) :
    OrdinaryTheory.{u, v, w, z} k ℬ :=
  ofSupportsAndPurity D S
```

The total cohomology is the direct sum over all bidegrees, with its grading by the summands.
The Gysin map is purity followed by forgetting supports, and the residue is the connecting map followed by inverse purity.
All three total exactness statements are proved, from the degreewise sequence and finite support, so neither the structure nor total exactness is among the inputs.
The degreewise product identities are given for arbitrary homogeneous factors, as the blueprint allows, and they also prove linearity of the Gysin and residue maps over all of $`B`, including coefficients of nonzero weight.

*What it would take to instantiate the theorem.*
For a named theory, say Betti cohomology, you would construct a {name OrlikSolomon.DegreewiseTheory}`DegreewiseTheory` and a {name OrlikSolomon.SupportsAndPurity}`SupportsAndPurity` from that theory's groups, products, localization sequence and Thom isomorphism, for all certified pairs on smooth $`k`-algebras.
This requires the theory itself in Lean, with coherent twists and strict indexed products.
The bridge removes the need to reason about total cohomology, but it supplies none of these.
It does not construct singular, de Rham or étale cohomology.

:::node "lem:standard-bridge" (decl := OrlikSolomon.DegreewiseTheory) (decl := OrlikSolomon.SupportsAndPurity) (decl := OrlikSolomon.ofSupportsAndPurity) (decl := OrlikSolomon.ofSupportsAndPurity_exact_gysin_map) (decl := OrlikSolomon.ofSupportsAndPurity_exact_map_residue) (decl := OrlikSolomon.ofSupportsAndPurity_exact_residue_gysin)
A cohomology presented in the familiar degreewise way, with products, twists, the point dimension axiom, affine-line invariance, localization with supports, oriented divisor purity, transverse naturality and the boundary projection formula, gives an instance of the structure.
Its degreewise long exact sequence is recovered from the three total exactness statements by {bp "lem:extraction"}[homogeneous extraction].
:::
