/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "Arrangements on schemes (planned)" =>
%%%
tag := "geometric"
file := "geometric"
htmlSplit := .never
%%%

*Only the foundations of this chapter and the projective complements are formalized.*
It presents the plan in the project's [third blueprint](https://github.com/adamtopaz/OrlikSolomon/blob/main/blueprint/geometric_refactor_blueprint.tex), which is tracked as the milestone "M6 Geometric refactor".
Of its 42 nodes, six are formalized and one partly, under the namespace `OrlikSolomon.Geometric`: {bp "def:geo-domain"}[admissible domains], the four nodes of {ref "geo-affine"}[affine duality], namely the equivalence between smooth algebras and smooth affine schemes, zero schemes and basic opens, products with the affine line and the multiplicative group, and units as maps to the multiplicative group, and the two nodes on {bp "def:geo-projective"}[projective space and its complements], of which {bp "thm:geo-projective-geometry"}[the second] is formalized except where it refers to the planned affine complements.
None of them mentions cohomology, and no structure theorem on schemes is formalized.
Every other box below is marked as planned, and for those the blueprint's proposed names under `OrlikSolomon.Geometric` do not exist yet, so this chapter does not list them.
The statements and arguments in the planned boxes are the blueprint's, and no machine has checked them.
The {ref "status"}[status page] counts these nodes apart from those of the main theorem and of the de Rham instance.
Neither of those depends on anything here: the plan is built on them, and the dependence runs the other way.

# What the refactor is for

The theorems of this book are proved, but they are stated in the language of algebras.
An object is a smooth $`k`-algebra, the complement $`U_{\mathcal{A}}` is given by its coordinate ring, and a cohomology theory is a _covariant_ functor on {name OrlikSolomon.SmoothAlg}`SmoothAlg` `k`, as {ref "geometry"}[the chapter on geometry] explains.
The proof loses nothing by this.
But it is not the language in which a geometer states the theorem, nor the one in which the standard cohomology theories are defined: singular cohomology of the complex points and $`\ell`-adic cohomology are theories on schemes.
To apply the existing theorem to such a theory, one must first build from it a value of the algebraic structure, by evaluating it on spectra of algebras and checking every field there, and then identify the spectrum of the coordinate ring of a complement with the open complement itself.

The third blueprint plans to remove that translation.
Its public objects are open subschemes of affine and projective space, and a cohomology theory becomes a _contravariant_ functor on a category of smooth $`k`-schemes.
A theory that is already defined on all smooth schemes, or on all smooth separated schemes of finite type, would then apply to the arrangement theorems directly.
Its user would supply no affine comparison theorem, no descent axiom and no auxiliary algebraic theory.
No conclusion of either structure theorem changes, and no new hypothesis on an arrangement appears.

The plan does not redo the proof.
Every proved algebraic result is reused through the equivalence between smooth $`k`-algebras and smooth affine $`k`-schemes, given by $`\operatorname{Spec}` in one direction and global sections $`\Gamma` in the other.
The existing structure {name OrlikSolomon.OrdinaryTheory}`OrdinaryTheory` stays as the kernel of the proof.
A geometric theory restricts to a value of it, the existing theorems are applied to that value, and their conclusions are transported to the actual open subschemes.

*Still conditional.*
Like the existing theorems, the planned geometric theorems would be conditional.
They would hold for every value of a geometric structure of axioms, and say nothing about a particular cohomology theory until someone constructs such a value for it.
The blueprint constructs one, algebraic de Rham cohomology of smooth affine schemes over a field of characteristic zero, from the de Rham instance that is already formalized.
For singular and $`\ell`-adic cohomology it records checks by hand, with the same standing as the checks of the existing axioms, and no formal instance.

# Admissible domains and hypotheses

In the plan a cohomology theory is defined on an _admissible domain_: a full subcategory of smooth $`k`-schemes, closed under isomorphism, that contains every smooth affine scheme and is closed under products with the affine line and with $`\mathbb{G}_m`.
Three domains are named: all smooth schemes, smooth separated schemes of finite type, and smooth affine schemes.
The domain is a parameter of the structure, and the theorems are stated for every domain.

This is what lets a theory on all smooth schemes apply directly.
Restricting a theory to a smaller domain needs no input: every field holds at the same objects, pairs and morphisms, and no cohomology is compared across a covering.
This is {bp "lem:geo-restriction"}[].
The hand checks for Betti and $`\ell`-adic cohomology use the domain of smooth separated schemes of finite type, which for Betti cohomology avoids treating the complex points of an arbitrary nonseparated scheme as a Hausdorff manifold.
The affine domain is where the de Rham instance lives.

The blueprint weighs this choice against two simpler ones.
Working on all smooth schemes only would force the de Rham instance through hypercohomology, which is a separate and substantial project.
Working on smooth affine schemes only would reuse the existing proofs most directly, but every user of a global theory would have to restrict it by hand.
The domain parameter costs one restriction constructor and some bookkeeping of variance.
It is a property of objects in a fixed category of schemes, not an abstract geometry with the desired theorems as fields: every geometric operation below is constructed on actual schemes.

*Hypotheses.*
The base $`k` is an arbitrary commutative ring in the categorical and sheaf constructions.
The arrangement theorems keep their hypotheses that $`k` is a field and that the ambient vector space is finite-dimensional, and the de Rham instance keeps characteristic zero.
The coefficient rings $`R` and $`B` are independent of $`k`, and may be zero.
The projective theorem keeps the nonempty arrangement: the complement of the empty projective arrangement is projective space itself, which is usually not affine and has different cohomology.

:::node "def:geo-domain" (decl := OrlikSolomon.Geometric.SmoothDomain) (decl := OrlikSolomon.Geometric.SmoothDomain.all) (decl := OrlikSolomon.Geometric.SmoothDomain.aff) (decl := OrlikSolomon.Geometric.SmoothDomain.sft) (decl := OrlikSolomon.Geometric.SmoothDomain.ofAffine) (decl := OrlikSolomon.Geometric.SmoothDomain.spec) (decl := OrlikSolomon.Geometric.SmoothDomain.prodAffineLine) (decl := OrlikSolomon.Geometric.SmoothDomain.prodGm) (decl := OrlikSolomon.Geometric.SmoothDomain.aff_le) (decl := OrlikSolomon.Geometric.SmoothDomain.le_all)
Let $`S=\operatorname{Spec}k`, let $`\mathsf{Sm}_k` be the full subcategory of schemes over $`S` whose structure morphism is smooth, and let $`\mathsf{Sm}_k^{\mathrm{aff}}` be its full subcategory of affine schemes.
An _admissible domain_ $`\mathcal{D}` is a full subcategory of $`\mathsf{Sm}_k`, closed under isomorphism, that contains every smooth affine $`k`-scheme and is closed under $`X\mapsto X\times_S\mathbb{A}^1_S` and $`X\mapsto X\times_S\mathbb{G}_m`.
Its morphisms are all morphisms over $`S` between its objects, which need not be smooth, flat, dominant or of constant relative dimension.
The canonical domains are $`\mathcal{D}_{\mathrm{all}}=\mathsf{Sm}_k`, $`\mathcal{D}_{\mathrm{aff}}=\mathsf{Sm}_k^{\mathrm{aff}}`, and the domain $`\mathcal{D}_{\mathrm{sft}}` of smooth separated schemes of finite type over $`S`.

The empty scheme is smooth and affine, so it lies in every domain, and no domain imposes irreducibility or nonemptiness.
:::

# Affine duality
%%%
tag := "geo-affine"
%%%

Everything rests on the classical anti-equivalence between smooth $`k`-algebras and smooth affine $`k`-schemes.
The blueprint states it with every compatibility that the transport of the proof needs: over the base, for closed subschemes and basic opens, and for products with $`\mathbb{A}^1` and $`\mathbb{G}_m`.
These are uses of Mathlib's existing theory of $`\operatorname{Spec}`, global sections and smoothness, not a new construction.

Arrows reverse.
An algebra map $`A\to A'` is a morphism of schemes $`\operatorname{Spec}A'\to\operatorname{Spec}A`, so pullback along a morphism of schemes is the value of the theory on a morphism of the opposite category.
In Lean the value at $`X` is planned as `T.C.obj (op X)`, not `T.C.obj X`.
The objects of a domain already form the category `D.Obj`, and `D.specFunctor` sends a smooth algebra `A` to `op (Spec A)` in its opposite, so a theory on $`\mathcal{D}` will be evaluated on algebras through it.

One result here is not about affine schemes: units of global sections are the same as morphisms to $`\mathbb{G}_m`, for every scheme.
This is what will let logarithmic classes be defined on objects of a domain that are not affine.

:::node "thm:geo-affine-duality" (decl := OrlikSolomon.Geometric.smoothAffineEquivalence) (decl := OrlikSolomon.Geometric.globalSections) (decl := OrlikSolomon.Geometric.specHomEquiv) (decl := OrlikSolomon.Geometric.affineHomEquiv) (decl := OrlikSolomon.Geometric.globalSectionsSpecIso) (decl := OrlikSolomon.Geometric.specGlobalSectionsIso) (decl := OrlikSolomon.Geometric.globalSectionsSpecIso_naturality) (decl := OrlikSolomon.Geometric.specGlobalSectionsIso_naturality) (decl := OrlikSolomon.Geometric.specGlobalSectionsIso_hom_spec) (decl := OrlikSolomon.Geometric.globalSectionsMap_specGlobalSectionsIso_hom) (decl := OrlikSolomon.Geometric.smooth_hom_iff)
Spectrum and global sections are inverse equivalences
$$`\mathsf{SmoothAlg}_k\simeq(\mathsf{Sm}_k^{\mathrm{aff}})^{\mathrm{op}},\qquad A\longmapsto\operatorname{Spec}A,\qquad X\longmapsto\Gamma(X,\mathcal{O}_X).`
For affine $`X` and $`Y` over $`S`, morphisms correspond as
$$`\operatorname{Hom}_S(X,Y)\simeq\operatorname{Hom}_{k\text{-alg}}\bigl(\Gamma(Y,\mathcal{O}_Y),\Gamma(X,\mathcal{O}_X)\bigr).`
The isomorphisms $`\eta_A:A\to\Gamma(\operatorname{Spec}A,\mathcal{O})` and $`\epsilon_X:\operatorname{Spec}\Gamma(X,\mathcal{O}_X)\to X` are natural, respect the structures over $`k`, and satisfy the triangle identities.
This includes the zero ring, whose spectrum is the empty scheme.
:::

:::node "lem:geo-affine-pairs" (decl := OrlikSolomon.Geometric.zeroScheme) (decl := OrlikSolomon.Geometric.zeroSchemeι) (decl := OrlikSolomon.Geometric.ker_zeroSchemeι) (decl := OrlikSolomon.Geometric.zeroSchemeIsoSpec) (decl := OrlikSolomon.Geometric.zeroSchemeIsoSpec_hom_comp) (decl := OrlikSolomon.Geometric.basicOpenIsoSpec) (decl := OrlikSolomon.Geometric.basicOpenIsoSpec_hom_comp) (decl := OrlikSolomon.Geometric.IsRegularSection) (decl := OrlikSolomon.Geometric.isRegularSection_iff) (decl := OrlikSolomon.Geometric.smooth_basicOpen) (decl := OrlikSolomon.Geometric.smooth_zeroScheme_iff)
Let $`X` be affine over $`S`, let $`A=\Gamma(X,\mathcal{O}_X)`, and let $`f\in A`.
Under $`\epsilon_X`, the closed subscheme $`Z_X(f)` cut out by $`f` is $`\operatorname{Spec}(A/(f))`, and the open subscheme $`X_f` on which $`f` is invertible is $`\operatorname{Spec}A_f`, compatibly with the immersions into $`X`.
Multiplication by $`f` is injective on $`\mathcal{O}_X` if and only if it is injective on $`A`.
If $`X` is smooth, then $`X_f` is smooth, and $`Z_X(f)` is smooth exactly when $`A/(f)` is smooth over $`k`.

The comparisons need no condition on $`f`, so they cover units and the zero ring.
:::

:::node "lem:geo-products" (decl := OrlikSolomon.Geometric.affineLine) (decl := OrlikSolomon.Geometric.gm) (decl := OrlikSolomon.Geometric.specPolynomialIso) (decl := OrlikSolomon.Geometric.specLaurentIso) (decl := OrlikSolomon.Geometric.specPolynomialIso_hom_fst) (decl := OrlikSolomon.Geometric.specLaurentIso_hom_fst) (decl := OrlikSolomon.Geometric.specMap_polynomialAlgLift_zero_comp_specPolynomialIso_hom) (decl := OrlikSolomon.Geometric.specMap_laurentAlgLift_one_comp_specLaurentIso_hom) (decl := OrlikSolomon.Geometric.specMap_polynomialAlgToLaurent_comp_specPolynomialIso_hom) (decl := OrlikSolomon.Geometric.specMap_polynomialAlgMap_comp_specPolynomialIso_hom) (decl := OrlikSolomon.Geometric.specMap_laurentAlgMap_comp_specLaurentIso_hom) (decl := OrlikSolomon.Geometric.specPolynomialIso_hom_appTop_prodCoord) (decl := OrlikSolomon.Geometric.SmoothDomain.specPolynomialIso) (decl := OrlikSolomon.Geometric.SmoothDomain.specLaurentIso)
Put $`\mathbb{A}^1_S=\operatorname{Spec}k[z]` and $`\mathbb{G}_m=\operatorname{Spec}k[z,z^{-1}]`.
For $`X=\operatorname{Spec}A` there are natural isomorphisms over $`S`
$$`\operatorname{Spec}A[z]\simeq X\times_S\mathbb{A}^1_S,\qquad\operatorname{Spec}A[z,z^{-1}]\simeq X\times_S\mathbb{G}_m,`
under which the inclusions of $`A` are the first projections, evaluation at $`0` or at $`1` gives the corresponding section, and $`A[z]\to A[z,z^{-1}]` is the open immersion.
So the standard pair of the existing proof becomes
$$`X\xrightarrow{\ z=0\ }X\times_S\mathbb{A}^1_S\xleftarrow{\ j\ }X\times_S\mathbb{G}_m.`
:::

:::node "thm:geo-units" (decl := OrlikSolomon.Geometric.unitsEquivHomGm) (decl := OrlikSolomon.Geometric.unitsEquivHomGm_comp) (decl := OrlikSolomon.Geometric.lift_unitsEquivHomGm_comp_mul) (decl := OrlikSolomon.Geometric.unitsEquivHomGm_comp_inv) (decl := OrlikSolomon.Geometric.toUnit_comp_one)
For every scheme $`X` over $`S`, affine or not, there is a natural bijection
$$`\Gamma(X,\mathcal{O}_X)^\times\simeq\operatorname{Hom}_S(X,\mathbb{G}_m),\qquad u\longmapsto\widehat{u},`
under which multiplication, inverses and the unit $`1` correspond to the group structure of $`\mathbb{G}_m`.
For $`g:X'\to X`, one has $`\widehat{g^*u}=\widehat{u}\circ g`.
Neither affineness, nor smoothness, nor a rational point is needed.
:::

# Principal smooth divisor pairs

The localization axioms need a divisor together with an equation.
The plan keeps the existing choice: a pair has a global regular function $`f` on its ambient scheme, which cuts out a smooth closed subscheme $`D` with open complement $`U`.
As for the existing {name OrlikSolomon.DivisorPair}`DivisorPair`, the pair certifies that its objects are the zero scheme and the open part, instead of being those schemes literally, so that actual arrangement complements can form a pair with no transport.

*Why principal.*
A global regular equation trivializes the ideal sheaf of $`D` on the whole ambient scheme, while a trivialization of the normal bundle of $`D` is a statement on $`D` only, and is weaker.
A rational point of $`\mathbb{P}^1_k` has a trivial normal bundle, but it is not the zero scheme of any global regular function, because the only global functions on $`\mathbb{P}^1_k` are constants: a nonzero constant cuts out nothing, and zero cuts out everything.
The constants are computed in {bp "prop:geo-nonaffine"}[].
A general Cartier divisor would need its own purity statement, which the existing instance does not supply, so the blueprint leaves it for later.
A principal equation is not an axiom that Gysin maps vanish.

*Morphisms reverse.*
A morphism of the existing algebraic pairs is a map of ambient algebras, and the corresponding morphism of schemes goes the other way.
The plan defines morphisms of geometric pairs in the geometric direction, so the duality between the two kinds of pairs reverses morphisms.
The unit relating the two equations lives on the source scheme, which is the target of the ring map.

*Transversality without flatness.*
The condition on morphisms, that the pulled-back equation is a unit multiple of the equation of the source, says exactly that the source divisor is the scheme-theoretic preimage of the target divisor.
That is the transversality needed for oriented divisor purity, and it does not require the ambient map to be flat.
{bp "prop:geo-nonflat"}[] tests this with a morphism that is not flat.

:::node "def:geo-divisor-pair"
A _principal smooth divisor pair_ in $`\mathcal{D}` consists of objects $`X`, $`D` and $`U` of $`\mathcal{D}`, morphisms $`i:D\to X` and $`j:U\to X`, and $`f\in\Gamma(X,\mathcal{O}_X)`, such that
 * multiplication by $`f` on $`\mathcal{O}_X` is a monomorphism,
 * $`i` identifies $`D` with the closed subscheme $`Z_X(f)`, and
 * $`j` identifies $`U` with the open subscheme $`X_f`.

Smoothness of the three schemes is their membership in $`\mathcal{D}`.
A unit $`f` and an empty ambient scheme are allowed.
:::

:::node "def:geo-pair-hom"
A morphism $`g:P\to Q` of pairs consists of morphisms $`g_X:X_P\to X_Q`, $`g_D:D_P\to D_Q` and $`g_U:U_P\to U_Q` such that
$$`g_X\,i_P=i_Q\,g_D,\qquad g_X\,j_P=j_Q\,g_U,\qquad g_X^*f_Q=u\,f_P\quad\text{for some }u\in\Gamma(X_P,\mathcal{O})^\times.`
Only the existence of the multiplier $`u` is required, and it is not part of the data.
Identities and composition are those of schemes, and $`g_D` and $`g_U` are determined by $`g_X`.
:::

:::node "thm:geo-cartesian"
Let $`P` and $`Q` be pairs and $`g_X:X_P\to X_Q`.
The condition $`g_X^*f_Q=u\,f_P` for some unit $`u` holds if and only if
$$`D_P\simeq X_P\times_{X_Q}D_Q`
as closed subschemes of $`X_P`, and then also $`U_P\simeq X_P\times_{X_Q}U_Q`.
The closed square is Tor-independent, and its conormal map is an isomorphism of line bundles.
Flatness of the ambient map is not required.

This compares subschemes: equality of the underlying closed sets would not suffice, as the doubled point of {bp "prop:geo-exclusions"}[] shows.
:::

:::node "thm:geo-pair-duality"
Geometric pairs whose ambient scheme is affine are anti-equivalent to the existing algebraic pairs {name OrlikSolomon.DivisorPair}`DivisorPair` `k`.
The equivalence preserves the two immersions, the equation and its unit on the open part, the standard pairs and changes of equation, and it reverses the direction of morphisms.
:::

# The geometric structure of axioms

The planned structure has exactly the fields of {bp "def:cohomology"}[], with the arrows in geometric directions.
Pullbacks are contravariant, affine-line invariance says that the projection $`X\times\mathbb{A}^1\to X` induces an isomorphism, and Gysin and residue maps exist for every geometric pair in the domain.
No field is added: there is no axiom about the empty scheme and no Künneth axiom, and none of the conclusions of the proof is assumed.

*The kernel interface.*
{bp "thm:geo-to-algebraic"}[] restricts a geometric theory on any domain to a value $`T_{\mathrm{alg}}` of the existing structure, by evaluating it on spectra.
{bp "thm:geo-from-algebraic"}[] goes back, but only to the affine domain: a value of the existing structure gives a theory on smooth affine schemes, by evaluating it on global sections.
The two transports are inverse up to canonical isomorphisms that commute with all the structure maps.
For a theory on a larger domain only its affine restriction is recovered, and nothing is claimed about extending a theory from affine schemes to others.
This is how the existing proofs are reused: the geometric structure theorem applies the existing one to $`T_{\mathrm{alg}}`, and composes with the comparison between an open complement and the spectrum of its coordinate ring.

*The bridge, and the checks by hand.*
The degreewise bridge carries over with the geometric objects substituted, and its algebraic lemmas are reused: see {bp "def:geo-supports"}[] and {bp "thm:geo-bridge"}[].
The blueprint records how the fields would be checked against the standard realizations.
For Betti cohomology of the complex points, after choosing an embedding of $`k` in $`\mathbb{C}` and on smooth separated schemes of finite type, the inputs are relative cohomology and the Thom isomorphism of the complex normal line.
For geometric $`\ell`-adic cohomology, with $`\ell` invertible in $`k` and on the same domain, they are localization with supports and oriented purity.
For de Rham cohomology on the affine domain, the fields follow unconditionally from the instance at the end of this chapter.
The first two are interpretations, which assume the foundational purity theorems of those theories: they are not formal instances, and they are not claimed as results of the refactor.

:::node "def:geo-theory"
Fix the coefficient data $`R`, $`B` and $`\mathcal{B}` of {bp "def:cohomology"}[] and an admissible domain $`\mathcal{D}`.
A _geometric ordinary theory_ is a functor
$$`C:\mathcal{D}^{\mathrm{op}}\longrightarrow\mathsf{AlgCat}_B,\qquad g^*=C(g^{\mathrm{op}})\quad\text{for }g:X\to Y,`
with exactly the fields of the existing structure, with the same scalar and grading conventions and the arrows in geometric directions.
In particular:
 * each pullback $`g^*:C(Y)\to C(X)` preserves the bigrading, and homogeneous classes commute up to the sign $`(-1)^{pq}` of their cohomological degrees;
 * the map $`B\to C(S)` is bijective, $`C(S)_{p,w}=0` for $`p\ne0`, and the projection $`\pi:X\times_S\mathbb{A}^1\to X` induces a bijection $`\pi^*` for every $`X` in $`\mathcal{D}`;
 * every pair $`P` in $`\mathcal{D}` has $`B`-linear maps $`G_P:C(D_P)\to C(X_P)` of shift $`(2,1)` and $`r_P:C(U_P)\to C(D_P)` of shift $`(-1,-1)`, with $`\operatorname{im}G_P=\ker j_P^*`, $`\operatorname{im}j_P^*=\ker r_P` and $`\operatorname{im}r_P=\ker G_P`;
 * for a morphism $`g:P\to Q`, one has $`G_P\,g_D^*=g_X^*\,G_Q` and $`r_P\,g_U^*=g_D^*\,r_Q`;
 * $`r_P(\alpha\,j_P^*\beta)=r_P(\alpha)\,i_P^*\beta` for $`\alpha\in C(U_P)_{1,1}` and every $`\beta\in C(X_P)`.

There is no axiom about the empty scheme, about any particular arrangement, or about logarithmic generation, vanishing, freeness or short exact deletion sequences, and there is no Künneth axiom.
The values stay possibly noncommutative $`B`-algebras graded by $`R`-submodules, since the cohomology ring is only graded commutative and multiplication by $`B_w` changes the weight.
:::

:::node "lem:geo-restriction"
An inclusion $`\mathcal{D}_1\subseteq\mathcal{D}_2` of admissible domains restricts a theory on $`\mathcal{D}_2` to a theory on $`\mathcal{D}_1`, and every field restricts.
In particular a theory on all smooth schemes gives a theory on the affine domain with no further input.
Restriction is compatible with the canonical isomorphisms of products and points when the two domains use different chosen models of them.
:::

:::node "thm:geo-to-algebraic"
Every geometric theory $`T` on an admissible domain gives a value $`T_{\mathrm{alg}}` of the existing structure, with
$$`T_{\mathrm{alg}}(A)=C(\operatorname{Spec}A),\qquad T_{\mathrm{alg}}(\phi)=(\operatorname{Spec}\phi)^*,`
whose Gysin and residue maps are the geometric maps of the spectrum of each pair.
All 22 fields hold, with exactly their existing degrees and signs.
:::

:::node "thm:geo-from-algebraic"
Every value $`E` of the existing structure gives a geometric theory $`E_{\mathrm{aff}}` on the affine domain, with
$$`E_{\mathrm{aff}}(X)=E\bigl(\Gamma(X,\mathcal{O}_X)\bigr),\qquad g^*=E\bigl(\Gamma(g)\bigr),`
whose Gysin and residue maps are those of the pair of global sections.
The two transports are inverse up to canonical isomorphisms of graded $`B`-algebras that commute with pullback, Gysin, residue and coefficient maps.
For a theory on a larger domain only its restriction to affine schemes is recovered: no extension from affine schemes to others is asserted.
:::

:::node "lem:geo-empty"
Every geometric theory has $`C(\varnothing)=0`.
A pair with a unit equation has $`D=\varnothing` and $`U\simeq X`, and its Gysin and residue maps are zero.

The proof applies exactness to the pair $`(X,\varnothing,X,1)`, so no axiom about the empty scheme is needed, and it holds for zero coefficients too.
:::

:::node "def:geo-supports"
A geometric degreewise theory has $`R`-modules $`H^{p,w}(X)`, indexed products, graded commutativity by $`p`, contravariant pullbacks that preserve degrees, and the degreewise coefficient, point and affine-line conditions of the existing bridge, with morphisms of schemes in place of algebra maps and the projection from $`X\times_S\mathbb{A}^1` in place of the polynomial inclusion.
For a pair, a package of supports and purity consists of $`R`-modules $`H_D^{p,w}(X)` and maps
$$`a:H_D^{p,w}(X)\to H^{p,w}(X),\qquad\delta:H^{p,w}(U)\to H_D^{p+1,w}(X),\qquad\vartheta:H^{p,w}(D)\xrightarrow{\ \sim\ }H_D^{p+2,w+1}(X),`
exact at the three consecutive places, with transverse pullbacks of supported classes that commute with $`a`, $`\delta` and $`\vartheta`, and a right product of a supported class by an ambient class satisfying
$$`a(x\cdot y)=a(x)\,y,\qquad\vartheta(x\,i^*y)=\vartheta(x)\cdot y,\qquad\delta(x\,j^*y)=\delta(x)\cdot y.`
The last formula has no sign.
:::

:::node "thm:geo-bridge"
These data give a geometric ordinary theory with
$$`C(X)=\bigoplus_{p,w}H^{p,w}(X),\qquad G=a\vartheta,\qquad r=\vartheta^{-1}\delta,`
and the construction commutes with restriction of domains and with affine duality.
The proofs are those of {bp "lem:standard-bridge"}[], whose algebraic lemmas are reused.
:::

# Complements as open subschemes

Here the plan makes the objects of the theorem what a geometer means by them.
Affine space is $`\mathbb{A}_V=\operatorname{Spec}\operatorname{Sym}(V^*)`, with no basis chosen.
The complement $`U_{\mathcal{A}}` is the open subscheme of $`\mathbb{A}_V` on which no equation of $`\mathcal{A}` vanishes, with the restricted structure sheaf.
It is never the set of its $`k`-points, which can be empty for a nonempty scheme, as {bp "prop:geo-finite-field"}[] shows over $`\mathbb{F}_2`.

The hyperplanes, their incidences and the restriction arrangement remain linear-algebra data, as they are now, since whether affine equations over $`k` have a common solution is a question of linear algebra over $`k`.
The new layer attaches to each hyperplane its closed subscheme, and it never tests an equality of morphisms of schemes on $`k`-points.

The link to the existing proof is a canonical isomorphism $`s_{\mathcal{A}}` from $`U_{\mathcal{A}}` to the spectrum of the existing coordinate ring {name OrlikSolomon.Arrangement.ComplementRing}`ComplementRing` of the complement.
The complement is the basic open of any product of equations, one for each hyperplane, but the comparison does not depend on which product is used.
Deletion becomes a statement about schemes: the complement of the restriction is the scheme-theoretic intersection of $`U_{\mathcal{A}'}` with $`H`, not only the underlying set of that intersection.

*Projective complements.*
For a finite set $`\mathcal{P}` of hyperplanes, $`U_{\mathcal{P}}` is the open subscheme of $`\operatorname{Proj}\operatorname{Sym}(W^*)` on which no equation of $`\mathcal{P}` vanishes.
It makes sense for empty $`\mathcal{P}`, where it is all of projective space.
That it is affine, and its comparison with the spectrum of the existing ring, are asserted only for nonempty $`\mathcal{P}`.
That comparison is the existing {name OrlikSolomon.ProjectiveArrangement.complementOpenIso}`complementOpenIso`, which {ref "projective"}[the projective chapter] describes, and {name OrlikSolomon.Geometric.projectiveComplementIsoSpec}`projectiveComplementIsoSpec` upgrades it with the certificate {name OrlikSolomon.Geometric.complementOpenIso_hom_specMap}`complementOpenIso_hom_specMap` that it is a morphism over $`k`, instead of proving it again.

:::node "def:geo-affine-space"
For a finite-dimensional vector space $`V` over a field $`k`, put $`\mathbb{A}_V=\operatorname{Spec}\operatorname{Sym}_k(V^*)`.
An affine function $`f:V\to k` gives the global function $`\widetilde{f}=\iota(f_{\mathrm{lin}})+f(0)`, and an affine map $`a:W\to V` gives a morphism $`\mathbb{A}_a:\mathbb{A}_W\to\mathbb{A}_V`.
For a hyperplane $`H`, let $`I_H` be the ideal generated by the functions of all its equations, and let $`\mathbf{H}=\operatorname{Spec}(\operatorname{Sym}(V^*)/I_H)`, with its closed immersion into $`\mathbb{A}_V`.

Two equations of $`H` differ by a unit of $`k`, so $`I_H=(\widetilde{f}_H)` for every equation $`f_H`.
A basis of $`V^*` proves that $`\mathbb{A}_V` is smooth, but no basis enters the definition.
:::

:::node "def:geo-complement"
For an arrangement $`\mathcal{A}` in $`V`, the complement $`U_{\mathcal{A}}` is the open subscheme of $`\mathbb{A}_V` on the intersection of the open sets $`\mathbb{A}_V\setminus|\mathbf{H}|` for $`H\in\mathcal{A}`, with the restricted structure sheaf and its open immersion $`j_{\mathcal{A}}:U_{\mathcal{A}}\to\mathbb{A}_V`.
It is a scheme, not a set of $`k`-points.
For the empty arrangement it is all of $`\mathbb{A}_V`.
:::

:::node "thm:geo-complement-spec"
The complement is smooth and affine, and there is a canonical isomorphism over $`\mathbb{A}_V`
$$`s_{\mathcal{A}}:U_{\mathcal{A}}\xrightarrow{\ \sim\ }\operatorname{Spec}\mathcal{O}(U_{\mathcal{A}})`
onto the spectrum of the existing coordinate ring of the complement.
For every product $`F=\prod_{H\in\mathcal{A}}\widetilde{f}_H` of equations, $`U_{\mathcal{A}}` is the basic open $`D(F)`, whose ring is the localization at $`F`, and $`s_{\mathcal{A}}` does not depend on $`F`.
Under $`s_{\mathcal{A}}`, each equation unit of the existing ring is the restriction of the corresponding function.
The comparison is compatible with inclusions of arrangements and with the pullbacks along affine maps that the existing theory of complements covers, including maps whose source has no rational points.
:::

:::node "thm:geo-deletion"
Let $`H\in\mathcal{A}` with an equation $`f_H`, let $`\mathcal{A}'=\mathcal{A}\setminus\{H\}`, and let $`\mathcal{A}''` be the existing restriction to $`H`.
On $`X=U_{\mathcal{A}'}` the restriction of $`\widetilde{f}_H` is regular, and
$$`Z_X(f_H)=X\times_{\mathbb{A}_V}\mathbf{H}\simeq U_{\mathcal{A}''},\qquad X_{f_H}\simeq U_{\mathcal{A}}.`
This is a geometric divisor pair whose pair of global sections is the existing deletion pair, up to the canonical comparisons, and its residue and Gysin maps do not depend on the equation.
The fiber product is scheme-theoretic: it is not only an equality of supports.
:::

:::node "thm:geo-small-targets"
The two auxiliary targets of {bp "lem:small-targets"}[] become complements $`Y` that are smooth affine schemes, with morphisms $`U_{\mathcal{A}}\to Y`.
For an empty intersection of $`s` hyperplanes, the coordinate functions pull back to $`f_1,\ldots,f_s`, and the ambient affine space of $`Y` has dimension at most $`s-1`.
For a dependent nonempty intersection of $`s+1` hyperplanes, the normalized slice has dimension at most $`s-1`, and the coordinate functions pull back to $`f_i/f_0` for $`1\le i\le s`.
These are identities of global functions, and none of them involves a rational point.
:::

:::node "def:geo-projective" (decl := OrlikSolomon.Geometric.projectiveSpace) (decl := OrlikSolomon.Geometric.projectiveComplement) (decl := OrlikSolomon.Geometric.projectiveComplementι) (decl := OrlikSolomon.ProjectiveArrangement.complementOpen_eq_iInf) (decl := OrlikSolomon.ProjectiveArrangement.complementOpen_eq_iInf_basicOpen) (decl := OrlikSolomon.ProjectiveArrangement.basicOpen_coord_eq_of_ker_eq) (decl := OrlikSolomon.ProjectiveArrangement.complementOpen_eq_top) (decl := OrlikSolomon.Geometric.isIso_projectiveComplementι) (decl := OrlikSolomon.Geometric.isEmpty_projectiveSpace_left) (decl := OrlikSolomon.Geometric.smooth_projectiveSpace_hom) (decl := OrlikSolomon.projIsoMvPolynomial)
For a finite-dimensional vector space $`W`, put $`\mathbb{P}(W)=\operatorname{Proj}\operatorname{Sym}(W^*)`, with the existing grading by degree.
For a finite set $`\mathcal{P}` of linear hyperplanes of $`W`, the complement $`U_{\mathcal{P}}` is the intersection of the open subschemes $`D_+(\ell_H)`, for equations $`\ell_H` of all the hyperplanes of $`\mathcal{P}`.
This makes sense for empty $`\mathcal{P}`, where it is all of $`\mathbb{P}(W)`.
If $`\dim W=0`, then $`\mathbb{P}(W)` is empty.
:::

:::node "thm:geo-projective-geometry" (decl := OrlikSolomon.Geometric.projectiveComplementIsoSpec) (decl := OrlikSolomon.Geometric.complementOpenIso_hom_specMap) (decl := OrlikSolomon.Geometric.projectiveComplementIsoSpec_inv_left_comp_ι) (decl := OrlikSolomon.Geometric.isAffine_projectiveComplement_left) (decl := OrlikSolomon.Geometric.smooth_projectiveComplement_hom) (decl := OrlikSolomon.Geometric.SmoothDomain.projectiveComplement) (decl := OrlikSolomon.Geometric.SmoothDomain.projectiveComplementIsoSpec) (decl := OrlikSolomon.Geometric.projectiveDeconeIso) (decl := OrlikSolomon.Geometric.projectiveDeconeIso_hom_appTop) (decl := OrlikSolomon.Geometric.coneProjection) (decl := OrlikSolomon.Geometric.coneProjection_comp_projectiveComplementIsoSpec_hom) (decl := OrlikSolomon.Geometric.coneIsoProdGm) (decl := OrlikSolomon.Geometric.coneIsoProdGm_hom_fst) (decl := OrlikSolomon.Geometric.coneIsoProdGm_hom_snd) (decl := OrlikSolomon.Geometric.specUnit_coneUnit) (decl := OrlikSolomon.Geometric.projectiveRatio) (decl := OrlikSolomon.Geometric.coe_projectiveRatio) (decl := OrlikSolomon.Geometric.SmoothDomain.coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom) (remaining := "the decone and cone isomorphisms with the open subschemes of affine space; their affine sides are formalized as the spectra of the existing coordinate rings of the decone and the cone, and need the comparison of thm:geo-complement-spec")
Suppose that $`\mathcal{P}` is nonempty.
Then $`U_{\mathcal{P}}` is smooth and affine, and the existing comparison gives a canonical isomorphism $`s_{\mathcal{P}}` from $`U_{\mathcal{P}}` to the spectrum of the existing ring $`\mathcal{O}(U_{\mathcal{P}})`.
For every equation $`\ell_0` of a member of $`\mathcal{P}` there are isomorphisms
$$`U_{\mathcal{P}}\simeq U_{\operatorname{decone}_{\ell_0}\mathcal{P}},\qquad V_{\mathcal{P}}:=U_{c\mathcal{P}}\simeq U_{\mathcal{P}}\times_S\mathbb{G}_m.`
The projection $`q:V_{\mathcal{P}}\to U_{\mathcal{P}}` is canonical and corresponds to the existing inclusion of the fractions of degree zero, while the product decomposition depends on $`\ell_0`, which is its second coordinate.
On $`V_{\mathcal{P}}` one has $`\ell_i=\ell_0\,q^*(\ell_i/\ell_0)`, and the ratios $`\ell_i/\ell_j` are global units on $`U_{\mathcal{P}}`.
:::

# Logarithms and the geometric structure theorems

The logarithmic class of a unit would be defined on every object of the domain, affine or not.
The class $`\tau` on $`\mathbb{G}_m` is transported from the existing one, and for a unit $`u` of the global functions on $`X`, the class $`[u]` is the pullback of $`\tau` along the morphism $`\widehat{u}:X\to\mathbb{G}_m` that $`u` defines.
Its identities follow by pulling back the existing identities on the affine schemes $`\mathbb{G}_m` and $`\mathbb{G}_m^2`.
In particular $`[u]^2=0` comes from $`\tau^2=0`, and not from graded commutativity, which would require dividing by $`2`.

The structure theorems are then the existing ones composed with the comparisons:
$$`\Phi^{\mathrm{geo}}_{\mathcal{A}}=s_{\mathcal{A}}^*\circ\Phi^{T_{\mathrm{alg}}}_{\mathcal{A}},`
and the same with $`s_{\mathcal{P}}` in the projective case.
They hold for a theory on every admissible domain, because the complements are smooth and affine and therefore belong to every domain.
The arguments about arrangements are not rerun: the existing inductions and calculations of relations are used as theorems, and no conclusion becomes an axiom.

:::node "def:geo-log"
For a geometric theory $`T`, let $`\tau\in C(\mathbb{G}_m)_{1,1}` be the transport of the class of {bp "lem:gm"}[], the unique class with residue $`1` in the standard pair.
For a unit $`u\in\Gamma(X,\mathcal{O}_X)^\times`, put
$$`[u]_T=\widehat{u}^*\tau\in C(X)_{1,1}.`
This applies to every object of the domain, including schemes that are not affine, and it involves no choice.
:::

:::node "thm:geo-log-laws"
For a morphism $`g:X'\to X`, units $`u` and $`v` on $`X`, and $`c\in k^\times`,
$$`g^*[u]=[g^*u],\qquad[c]=0,\qquad[u]^2=0,\qquad[uv]=[u]+[v],\qquad[u^{-1}]=-[u].`
For every pair with equation $`f`, one has $`r_P([f|_U])=1` and $`r_P([f|_U]\,j^*\beta)=i^*\beta`.
On affine schemes these classes and identities agree with the existing ones under affine duality.
:::

:::node "thm:geo-gm-product"
For every $`X` in the domain, the standard pair gives an isomorphism of graded $`B`-modules, natural in $`X`,
$$`C(X)\oplus C(X)[(1,1)]\xrightarrow{\ \sim\ }C(X\times_S\mathbb{G}_m),\qquad(a,b)\longmapsto\pi^*a+[z]\,\pi^*b,`
where the second summand is shifted by $`(1,1)`.
Its inverse is $`x\mapsto(s_1^*x,r(x))`, with $`s_1` the section at $`1`.
This is the geometric form of {bp "lem:gm-product"}[], and it holds for objects that are not affine as well.
It is not a statement about an ungraded tensor product of algebras.
:::

:::node "thm:geo-affine"
For every arrangement $`\mathcal{A}` in a finite-dimensional $`k`-vector space, and every geometric ordinary theory on any admissible domain, there is a canonical isomorphism of $`B`-algebras preserving the bigrading
$$`\Phi_{\mathcal{A}}:\operatorname{OS}_B(\mathcal{A})\xrightarrow{\ \sim\ }C(U_{\mathcal{A}}),\qquad e_H\longmapsto[f_H|_{U_{\mathcal{A}}}].`
Its diagonal and component forms, its independence of the equations, uniqueness on generators, naturality for inclusions of arrangements and for affine equivalences, and compatibility with the residue of a deletion are the geometric transports of {bp "thm:affine"}[] and {bp "cor:ordinary"}[].
In particular
$$`H^{p,w}(U_{\mathcal{A}})\simeq_R\operatorname{OS}_R^p(\mathcal{A})\otimes_RB_{w-p}\quad(p\ge0),\qquad\operatorname{OS}_R(\mathcal{A})\simeq_R\bigoplus_{q\ge0}H^{q,q}(U_{\mathcal{A}}).`
The same vanishing bounds, recursive monomial bases and integer Betti and Möbius formulas hold, and no restriction on the characteristic of $`k` or of $`R` is added.
:::

:::node "thm:geo-projective"
For nonempty $`\mathcal{P}` there are canonical graded isomorphisms
$$`\overline{\operatorname{OS}}_B(\mathcal{P})\xrightarrow{\ \sim\ }C(U_{\mathcal{P}}),\qquad\overline{\operatorname{OS}}_R(\mathcal{P})\xrightarrow{\ \sim\ }\bigoplus_{q\ge0}H^{q,q}(U_{\mathcal{P}}),\qquad e_i-e_j\longmapsto[\ell_i/\ell_j],`
where $`\overline{\operatorname{OS}}` is the existing kernel of the boundary on the cone, not a new presentation.
They do not depend on the equations or on a hyperplane at infinity, they commute with pullback along the projection from the cone, and every component and multiplicity statement of {bp "thm:projective"}[] and {bp "cor:projective-betti"}[] carries over.
:::

# De Rham cohomology of smooth affine schemes

The planned instance is algebraic de Rham cohomology on the affine domain.
For a smooth affine scheme $`X`, its de Rham cohomology is the cohomology of the complex of global differential forms, which is the existing de Rham cohomology {name OrlikSolomon.DeRham.Cohomology}`DeRham.Cohomology` of the algebra $`\Gamma(X,\mathcal{O}_X)`.
The instance is the {ref "de-rham"}[existing one], transported by {bp "thm:geo-from-algebraic"}[], so none of its fields is proved again.
The existing unconditional corollaries then become statements about the actual open subschemes.

The blueprint also constructs the sheaf of differential forms on every scheme over $`k`, compares it with the existing forms on affine open subschemes, and proves the logarithmic residue sequence and comparison as statements about complexes of sheaves on any smooth scheme.
This reuses the existing algebra, and the new work is compatibility with sheaves, pullback and the affine comparison.
The polynomial presentation of the differential, the conormal calculation, the integration homotopy and the pole-order contraction are not redone.
The sheaf statements are an input to a future instance on schemes that are not affine, and they are not such an instance.

*Why the instance stays on affine schemes.*
The definition by global forms is right only for affine schemes.
On the projective line over a field of characteristic zero, the only global functions are constants and there are no nonzero global one-forms, so the complex of global forms has cohomology $`k` in degree zero and nothing else.
The usual answer has cohomology $`k` in degrees zero and two.
The Čech–de Rham complex of the two standard charts computes the usual answer, and {bp "prop:geo-nonaffine"}[] shows that any extension of the affine theory with the usual Mayer–Vietoris sequence for two opens must give it.
So extending the instance to all smooth schemes needs hypercohomology of the de Rham complex, and the blueprint lists what that requires:
 * a functorial hypercohomology with pullbacks, cup products, unit and graded commutativity, and invariance under quasi-isomorphism;
 * acyclicity of quasi-coherent sheaves on affine schemes, so that hypercohomology of an affine scheme is the cohomology of its global forms, and independence of the cover for the resulting Čech complexes;
 * the comparison of $`j_*\Omega_U^\bullet` with $`Rj_*\Omega_U^\bullet` for the principal open $`j`, after which the sheaf residue sequence gives the global localization sequence;
 * affine-line invariance through covers, which needs more than finite affine covers on schemes that are not separated;
 * naturality and the projection formula at the level of hypercohomology, and agreement with the affine instance.

These are substantive prerequisites, which is why non-affine de Rham cohomology is a separate project and not part of this plan.
The planned geometric theorem would accept such an instance with no change, on the domain of all smooth schemes or of smooth separated schemes of finite type, and nothing in the plan depends on it.

:::node "lem:geo-module-gluing"
For a commutative ring $`A` and an $`A`-module $`M`, the rule $`D(a)\mapsto M_a` on basic opens, with the localization maps as restrictions, defines the associated sheaf $`\widetilde{M}` on $`\operatorname{Spec}A`, with $`\Gamma(\operatorname{Spec}A,\widetilde{M})\simeq M` naturally in $`A` and $`M`.
Associated sheaves preserve exact sequences.
This includes the zero ring and modules that are not finitely generated.

It says nothing about vanishing of higher sheaf cohomology, and Mathlib already provides associated sheaves and their global sections.
:::

:::node "def:geo-forms-sheaf"
For a scheme $`X` over $`S`, let $`\Omega^n_{X/k}` be the sheafification of the presheaf
$$`V\longmapsto\Omega^n_{\Gamma(V,\mathcal{O}_X)/k}`
on the open subsets of $`X`, in $`k`-modules and keeping the structure of $`\mathcal{O}_X`-module, and put $`\Omega^n_{X/k}=0` for $`n<0`.
Sheafifying the existing differential and wedge product makes $`\Omega^\bullet_{X/k}` a sheaf of dg algebras.
Its differential is a map of sheaves of $`k`-modules, and in general not of $`\mathcal{O}_X`-modules.

On an affine open $`\operatorname{Spec}A`, sheafification does not change the value: by {bp "lem:dr-localization"}[] and {bp "lem:geo-module-gluing"}[], the sheaf there is the one associated with $`\Omega^n_{A/k}`.
:::

:::node "thm:geo-forms-comparison"
For affine $`X` with $`A=\Gamma(X,\mathcal{O}_X)` there is a canonical isomorphism of dg algebras
$$`\Omega^\bullet_{A/k}\xrightarrow{\ \sim\ }\Gamma(X,\Omega^\bullet_{X/k}).`
Every morphism $`g:X\to Y` over $`S` induces a functorial map $`g^{-1}\Omega^\bullet_{Y/k}\to\Omega^\bullet_{X/k}` of complexes of sheaves of $`k`-modules that preserves products, and in degree $`n` it is the usual pullback of forms.
For affine $`X` and $`Y`, the induced map on global forms is the existing map of forms along $`\Gamma(g)`.
No flatness of $`g` is used.
:::

:::node "thm:geo-log-sheaves"
Let $`k` be a field of characteristic zero and $`P=(X,D,U,f)` a geometric pair on any domain.
Put $`\theta=df/f` on $`U`, and inside $`j_*\Omega^n_{U/k}` put $`L^n=\Omega^n_{X/k}+\theta\wedge\Omega^{n-1}_{X/k}`.
Regular forms inject into $`j_*\Omega^\bullet_{U/k}`, $`L^\bullet` is a sheaf of dg subalgebras, and there is a degreewise short exact sequence of complexes of sheaves of $`k`-modules
$$`0\longrightarrow\Omega^\bullet_{X/k}\longrightarrow L^\bullet\xrightarrow{\ \rho\ }i_*\Omega^\bullet_{D/k}[-1]\longrightarrow0,\qquad\rho(\omega+\theta\wedge\eta)=\eta|_D,`
where the shifted complex has differential $`-d`.
The inclusion $`L^\bullet\to j_*\Omega^\bullet_{U/k}` is a quasi-isomorphism of complexes of sheaves.
All these maps are natural for morphisms of pairs, with the projection identity on forms and exactly the existing signs.

This is a statement about sheaves.
It does not identify $`j_*` with $`Rj_*`, and it does not say that the global sections of the residue sequence are exact on a scheme that is not affine.
:::

:::node "def:geo-dr-cohomology"
For a smooth affine scheme $`X`, put
$$`H^n_{\mathrm{dR}}(X/k)=H^n\bigl(\Gamma(X,\Omega^\bullet_{X/k})\bigr),\qquad H^\bullet_{\mathrm{dR}}(X/k)=\bigoplus_{n\ge0}H^n_{\mathrm{dR}}(X/k),`
with the product induced by the wedge product and pullbacks induced by {bp "thm:geo-forms-comparison"}[].
The plan implements the total algebra as the existing de Rham cohomology of the algebra $`\Gamma(X,\mathcal{O}_X)`, with this display as its specification.
The formula is not used to define de Rham cohomology of a scheme that is not affine.
:::

:::node "thm:geo-dr-instance"
Let $`k` be a field of characteristic zero, $`B=k[t,t^{-1}]` and $`\mathcal{B}_w=k\,t^w`.
There is a geometric ordinary theory on the affine domain with
$$`C(X)=B\otimes_kH^\bullet_{\mathrm{dR}}(X/k),\qquad C(X)_{p,w}=t^w\otimes H^p_{\mathrm{dR}}(X/k),`
obtained by applying {bp "thm:geo-from-algebraic"}[] to the existing instance {name OrlikSolomon.DeRham.ordinaryTheory}`DeRham.ordinaryTheory` `k`.
On each affine pair its Gysin and residue maps are those of the global logarithmic sequence, twisted:
$$`G(t^w\otimes y)=t^{w+1}\otimes G_{\mathrm{dR}}(y),\qquad r(t^w\otimes x)=t^{w-1}\otimes r_{\mathrm{dR}}(x).`
Its coefficients and its value at $`S` are nonzero, and $`[u]_T=t\otimes[du/u]`.
:::

:::node "cor:geo-dr-arrangements"
For a field $`k` of characteristic zero, with complements the open subschemes defined above, there are isomorphisms of graded $`k`-algebras
$$`\operatorname{OS}_k(\mathcal{A})\xrightarrow{\ \sim\ }H^\bullet_{\mathrm{dR}}(U_{\mathcal{A}}/k),\qquad e_H\longmapsto\Bigl[\frac{df_H}{f_H}\Bigr],`
and, for nonempty $`\mathcal{P}`,
$$`\overline{\operatorname{OS}}_k(\mathcal{P})\xrightarrow{\ \sim\ }H^\bullet_{\mathrm{dR}}(U_{\mathcal{P}}/k),\qquad e_i-e_j\longmapsto\Bigl[\frac{d(\ell_i/\ell_j)}{\ell_i/\ell_j}\Bigr],`
with the same canonicity, component isomorphisms, direct sums and dimension statements as {bp "cor:dr-affine"}[] and {bp "cor:dr-projective"}[].
:::

# Worked regressions

These test the places where a statement about schemes could quietly differ from its algebraic version.

:::node "prop:geo-finite-field"
For the hyperplanes $`0` and $`1` of $`\mathbb{A}^1_{\mathbb{F}_2}`, the complement is
$$`U=D\bigl(x(x-1)\bigr)\simeq\operatorname{Spec}\mathbb{F}_2\Bigl[x,\frac{1}{x(x-1)}\Bigr].`
It is a nonempty smooth affine scheme with no $`\mathbb{F}_2`-points: $`\operatorname{Hom}_{\mathbb{F}_2}(\operatorname{Spec}\mathbb{F}_2,U)` is empty.
Its Poincaré polynomial is $`1+2z`, and every theory has the corresponding two basis words of length one, with the same qualifications for zero coefficients as before.

This is the example that {ref "organization"}[the chapter on the organization of the proof] follows, stated for the scheme.
:::

:::node "prop:geo-degenerate"
The unit pair is $`(X,\varnothing,X,1)`, and $`\operatorname{Spec}0` is the empty smooth affine scheme, whose de Rham cohomology is zero.
The disconnected smooth scheme $`X=\operatorname{Spec}k\amalg\mathbb{A}^1_k`, with the function $`f=(1,z)`, has $`D\simeq\operatorname{Spec}k` on the second component and $`U\simeq\operatorname{Spec}k\amalg\mathbb{G}_m`.
In characteristic zero, its untwisted de Rham cohomology is $`H^0(X)=k\times k` and $`H^{>0}(X)=0`, while $`H^0(U)=k\times k`, $`H^1(U)=k\,[(0,dz/z)]` and $`H^{>1}(U)=0`.
The residue of $`(0,dz/z)` is $`1`, and there is no global derivation $`v` with $`v(f)=1`.
:::

:::node "prop:geo-exclusions"
Each of the following is excluded, for a different reason.
 * On $`\operatorname{Spec}(k\times k)`, the function $`f=(1,0)` is not regular. Treating its second component as a smooth divisor of codimension one would make the shifts of the localization sequence false for de Rham or singular cohomology.
 * On $`\mathbb{A}^2_k`, the function $`f=xy` is regular, but $`D=\operatorname{Spec}k[x,y]/(xy)` is not smooth, and the residue sequence of a single smooth divisor fails.
 * The map $`\mathbb{A}^1_x\to\mathbb{A}^1_z` given by $`z\mapsto x^2` is not a morphism between the pairs with equations $`x` and $`z`. The pulled-back divisor is the doubled point, not the reduced one, and the residue of $`d(x^2)/x^2` is $`2`, while the transverse formula would give $`1`.
:::

:::node "prop:geo-nonflat"
The ring map $`k[z,v]\to k[x,y,y^{-1}]` given by $`z\mapsto xy` and $`v\mapsto0` defines a transverse morphism of pairs
$$`\bigl(\operatorname{Spec}k[x,y,y^{-1}],\,x\bigr)\longrightarrow\bigl(\mathbb{A}^2_{z,v},\,z\bigr).`
It is not flat, and both naturality identities hold for it.
The simpler map from $`\operatorname{Spec}k[x,y,y^{-1}]` to $`\mathbb{A}^1_z` is flat, and it is an example with different ambient dimensions.
:::

:::node "prop:geo-nonaffine"
The projective line $`\mathbb{P}^1_k` is an object of the domains of all smooth schemes and of smooth separated schemes of finite type, and it is not affine.
For every geometric theory on either domain, the pair
$$`\bigl(\mathbb{P}^1_k\times\mathbb{A}^1,\ \mathbb{P}^1_k\times\{0\},\ \mathbb{P}^1_k\times\mathbb{G}_m,\ z\bigr)`
is allowed, and it satisfies {bp "thm:geo-gm-product"}[].
The affine de Rham instance does not claim to evaluate this object.

For a field of characteristic zero, the complex of global de Rham forms on $`\mathbb{P}^1_k` has cohomology $`k` in degree zero and zero otherwise.
The total complex of the Čech–de Rham double complex of the two standard charts has cohomology $`k` in degrees zero and two and zero otherwise.
Any extension that agrees with the affine de Rham theory and has the usual Mayer–Vietoris triangle for two opens must give the second answer, so the affine definition by global sections would be wrong for all schemes.
:::

The punctured line, the two-dimensional torus and the obstructions in positive characteristic are the existing de Rham regressions, transported to the actual schemes $`\mathbb{G}_m`, $`\mathbb{G}_m^2` and $`\mathbb{A}^1` by the comparison of forms.
They are collected in {bp "prop:geo-affine-regressions"}[] below.
Single projective hyperplanes, points of the projective line, zero coefficients and ambient dimension zero keep their existing tests.

# The intended interface

The blueprint gives schematic Lean signatures, which are proposals and have not been elaborated.
It asks that named geometric objects, pairs, functors and theories be definitions with comparison lemmas, as the existing library does for the same reasons, that the typed wrappers of the residue and Gysin maps be kept, and that one set of naturality lemmas for the comparisons $`s_{\mathcal{A}}` and $`s_{\mathcal{P}}` be proved and used, instead of rewriting through $`\operatorname{Spec}` and $`\Gamma` each time.
Membership of a smooth affine scheme in a domain should be supplied automatically, and never become a hypothesis on an arrangement.

Its acceptance tests include a file that states the affine and projective theorems for a theory on all smooth schemes using only the geometric statements, with no affine comparison supplied by the user, and a file that states the two de Rham corollaries for the open subschemes, with no theory and no Laurent variable in them.
Both naturality fields are to be tested on the morphism of {bp "prop:geo-nonflat"}[], which is not flat, and the comparisons with spectra on all three maps of a deletion pair, not only on the open inclusion.

:::node "prop:geo-affine-regressions"
Over a field of characteristic zero, $`H^\bullet_{\mathrm{dR}}(\mathbb{G}_m)=k\oplus k\,[dx/x]`, with a generator of degree one, of square zero and with residue $`1`, and
$$`H^\bullet_{\mathrm{dR}}(\mathbb{G}_m^2)=\textstyle\bigwedge_k(e_x,e_y),\qquad e_x=[dx/x],\quad e_y=[dy/y].`
In the smooth pairs with ambient $`\mathbb{A}^1_x\times\mathbb{G}_{m,y}` and $`\mathbb{G}_{m,x}\times\mathbb{A}^1_y`, the residues of $`e_xe_y` are $`e_y` and $`-e_x`.
In characteristic $`p>0`, the nonconstant closed function $`x^p` and the nonexact form $`x^{p-1}dx` on $`\mathbb{A}^1` prevent the cohomology of global forms from satisfying affine-line invariance.
:::

# Transport of every existing statement

The blueprint classifies each of the 105 nodes of the first two blueprints.
Pure algebra and incidence are unchanged: gradings, exterior words, hyperplanes and deletion, the Orlik–Solomon algebra and its quotients, the boundary, the polynomial recursion, the Möbius formulas, and the three general lemmas of the de Rham blueprint on exterior algebra, contraction and reduction along a filtration.
The remaining algebraic de Rham constructions are retained as they are, in full generality, and gain companions on schemes.
Every statement that mentions cohomology or a complement is restated for schemes by the rule below.
The six deferred nodes of {ref "generalized"}[the stable extension] stay unchanged and deferred.
All existing declarations remain, as compatibility interfaces, with their general hypotheses.

:::node "thm:geo-transport-all"
Write $`\mathsf{G}` for the following substitution in a statement about a value of the existing structure and its named smooth objects.
 * Replace a smooth algebra $`A` by $`\Gamma(X,\mathcal{O}_X)` for a smooth affine scheme $`X`, an algebra map by the pullback along a morphism of schemes in the opposite direction, and a certified pair by its dual geometric pair, reversing morphisms of pairs.
 * Replace each named affine space, arrangement complement or nonempty projective complement by the scheme defined in this chapter, together with its comparison with a spectrum, and replace polynomial and Laurent extensions by products with $`\mathbb{A}^1` and $`\mathbb{G}_m`. Labels, words, incidence data and Orlik–Solomon algebras are unchanged.
 * Replace the value of the theory at $`A` by its value at $`X`, and the map induced by an algebra map by the pullback along its spectrum, conjugated by the comparisons. Replace units by units of global functions, logarithmic classes by those of {bp "def:geo-log"}[], and residue and Gysin maps by the geometric ones, with no change of sign.
 * For a statement about de Rham cohomology, use the comparisons of forms and of cohomology on affine schemes instead of a theory, and keep its hypotheses on coefficients and characteristic.

Every existing proof, with these substitutions, proves the $`\mathsf{G}`-restatement of its statement, with all its hypotheses and conclusions.
For the named arrangement objects the theory may be on any admissible domain, while for arbitrary objects the rule gives only the affine version.
:::

# Order of work

The blueprint orders the work in stages, each with a condition for completion.

:::table +header
*
 * Stage
 * Deliverable
 * Prerequisites
*
 * G0
 * domains of smooth schemes, the duality between $`\operatorname{Spec}` and $`\Gamma`, and principal pairs
 * the existing smooth algebras and Mathlib's schemes
*
 * G1
 * the contravariant structure and both transports
 * G0
*
 * G2
 * affine and projective complements as open subschemes, and their comparisons
 * G0 and the existing geometry
*
 * G3
 * geometric logarithms and the public structure theorems
 * G1 and G2
*
 * G4
 * sheaves of forms and their evaluation on affine schemes
 * the existing de Rham algebra and Mathlib's sheaves
*
 * G5
 * the de Rham instance on smooth affine schemes and its corollaries
 * G1, G3, G4 and the existing instance
*
 * G6
 * the logarithmic comparison for sheaves
 * G0, G4 and the existing logarithmic and pole-order results
:::

After G0, the stages G1 and G2 are independent, and G4 can proceed alongside them.
G6 is not needed for the affine instance, but it is part of the blueprint and has its own node.
The existing algebra and combinatorics must not depend on the new layer, and the existing public theorems remain available throughout: the geometric theorems are additional entries, not replacements.
A box in this chapter becomes formalized only when its declarations are proved and review finds that they cover it.

# Where each hypothesis is used

 * *A commutative base ring* suffices for the equivalence between algebras and affine schemes and for the sheaf of forms.
 * *A field and a finite-dimensional vector space* enter only through the unchanged arguments about incidence and the smoothness of $`\mathbb{A}_V`.
 * *No hypothesis on the characteristic* is added by the geometric structure theorems.
 * *Smoothness of the ambient scheme and of the divisor* is used for the local residue and comparison theorems of de Rham cohomology.
 * *Regularity of the equation* gives the correct codimension, injectivity of restriction to the open part, and the Tor-independent square.
 * *Invertibility of positive integers* enters only through the existing integration and pole-order arguments, and characteristic zero supplies it for the instance.
 * *Separatedness* is not used by the transport, the affine instance or the sheaf construction. It is useful for the standard Betti domain, and for a future construction of hypercohomology by finite affine covers.
 * *Finite type* holds automatically for affine objects, through the existing smooth algebras, and is not imposed on every object of the domain of all smooth schemes.
 * *No connectedness, integrality or rational point* is assumed for a pair, and the hyperplanes still form a finite arrangement split over $`k`.
