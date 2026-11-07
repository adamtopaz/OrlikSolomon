/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

#doc (Manual) "A de Rham instance of the axioms" =>
%%%
tag := "de-rham"
file := "de-rham"
htmlSplit := .never
%%%

*The de Rham instance is constructed in Lean.*
This chapter follows the project's [second blueprint](https://github.com/adamtopaz/OrlikSolomon/blob/main/blueprint/de_rham_instance_blueprint.tex).
For every field $`k` of characteristic zero, {name OrlikSolomon.DeRham.ordinaryTheory}`DeRham.ordinaryTheory` `k` is a value of the structure of axioms: algebraic de Rham cohomology, with coefficients $`k[t,t^{-1}]`.
Its coefficient ring and its cohomology of the point are nonzero, and every field of the structure is proved for it, none weakened and none replaced by a hypothesis.
This is {bp "thm:dr-instance"}[].

The exterior calculus and the de Rham dg algebra of an arbitrary algebra, including its differential and cohomology algebra, are formalized, together with forms on localizations and principal quotients.
The polynomial decomposition of forms and the integration homotopy are formalized as well, including the cohomology equivalence whose inverse is induced by evaluation at zero.
Projectivity in every form degree, injectivity of regular scalar multiplication and of restriction into localization, conormal splitting, global and localized normal derivations, and wedge exactness modulo the divisor are also formalized, as are logarithmic forms and the residue sequence of a smooth divisor.
Cartan calculus, the pole filtration, contraction of its positive quotients, and finite reduction to logarithmic cohomology are formalized.
The residue and Gysin maps before the twist, their long exact sequence and projection formula, and their naturality for morphisms that need not be flat are formalized too.
So are the Laurent-twisted functor, the twisted Gysin and residue maps, and every field of the structure of axioms.
What remains planned is {bp "lem:dr-tau"}[], which identifies the logarithmic classes of the instance with the classes of the forms $`da/a`, the corollaries {bp "cor:dr-affine"}[] and {bp "cor:dr-projective"}[], which instantiate the main theorems at it.
Each box shows its own status and the Lean statements proved so far; a planned box remains a mathematical statement whose proof has not been formalized.
The {ref "status"}[status page] counts these nodes apart from those of the main theorem, which does not depend on them.

# What the instance is for

The main theorem of this book is conditional.
It holds for every value of the structure of axioms in {bp "def:cohomology"}[], and by itself it says nothing about any particular cohomology theory.
Apart from zero theories, with zero coefficients, the library contains one value of that structure: algebraic de Rham cohomology of smooth algebras over a field $`k` of characteristic zero.
It serves two purposes.

*Showing that the axioms are not vacuous.*
{bp "thm:dr-instance"}[] gives a value of the structure whose coefficient ring and whose cohomology of the point are nonzero.
So the axioms are known in Lean to have a nonzero model, with every field proved and none weakened.
Its only hypotheses are that $`k` is a field and has characteristic zero:

```lean -show
noncomputable section
open OrlikSolomon
universe u
```

```lean
example (k : Type u) [Field k] [CharZero k] :
    OrdinaryTheory k (laurentGrading k) :=
  DeRham.ordinaryTheory k
```

It depends only on the standard axioms of Lean's logic, and the build fails if this output changes:

```lean (name := axiomsOfDeRhamOrdinaryTheory)
#print axioms DeRham.ordinaryTheory
```
```leanOutput axiomsOfDeRhamOrdinaryTheory
'OrlikSolomon.DeRham.ordinaryTheory' depends on axioms: [propext, Classical.choice, Quot.sound]
```

*Giving an unconditional corollary.*
{bp "cor:dr-affine"}[], which is still planned, will instantiate {bp "thm:affine"}[] to give, for every split affine arrangement $`\mathcal{A}` over such a field,
$$`\operatorname{OS}_k(\mathcal{A})\simeq_k\bigoplus_{q\ge0}H^q_{\mathrm{dR}}(U_{\mathcal{A}}/k),\qquad e_H\longmapsto[df_H/f_H],`
a statement with no hypothetical cohomology theory in it.
{bp "cor:dr-projective"}[] will do the same for nonempty split projective arrangements.
The proof about arrangements is not repeated, and the construction of the instance does not mention arrangements at all: they enter only when the existing theorems are instantiated.

This is one theory.
It gives no theorem about singular, $`\ell`-adic or rigid cohomology.
For those the main theorem remains conditional, the checks of its axioms against singular and $`\ell`-adic cohomology remain arguments by hand, and the main theorem stays stated for every value of the structure.

# The strategy: no coordinate cover
%%%
tag := "de-rham-strategy"
%%%

The construction has four main pieces: the de Rham differential with no basis of differentials, polynomial homotopy invariance for the affine-line axiom, the residue sequence of a smooth divisor, and a global contracting homotopy on each positive pole-order quotient.
The last two supply the ingredients for the remaining localization axiom for a divisor pair, in which $`f` is a non-zero-divisor of a smooth algebra $`A`, the quotient $`S=A/(f)` is smooth, and $`A_f=A[1/f]`.

The construction splits this axiom in two.
Put $`\theta=df/f`, and let $`L^n=\Omega_A^n+\theta\wedge\Omega_A^{n-1}` be the logarithmic forms inside $`\Omega_{A_f}^n`.
Taking the residue $`\rho(\omega+\theta\wedge\eta)=\eta|_S` gives a short exact sequence of complexes
$$`0\longrightarrow\Omega_A^\bullet\longrightarrow L^\bullet\xrightarrow{\ \rho\ }\Omega_S^\bullet[-1]\longrightarrow0,`
whose long exact sequence has the cohomology of $`L^\bullet` where the axiom wants that of $`A_f`.
The pole-order comparison identifies the cohomology of $`L^\bullet` with that of $`\Omega_{A_f}^\bullet` through this inclusion.

The pole-order proof uses no chart in which $`f` is a coordinate, no cover of $`\operatorname{Spec}A`, no gluing of cohomology, no basis of $`\Omega_A^1` and no chosen dimension.
It never treats de Rham cohomology as an $`A`-module, which it generally is not.
The whole argument runs on a single global derivation, in the following steps.

 * *A derivation normal to the divisor.* Smoothness of $`S` splits $`A/(f^2)\to S`, and since $`f` is a non-zero-divisor this gives a derivation $`A\to S` taking $`f` to $`1`. Projectivity of $`\Omega_A^1` lifts it to a global $`k`-derivation $`v:A\to A` with $`v(f)=1+fh`. The form $`df` need not be unimodular on all of $`\operatorname{Spec}A`, only along the divisor, and the congruence $`v(f)\equiv1` modulo $`f` is all that is used. The elements $`f` and $`v(f)` do generate the unit ideal, so they define a cover by two open sets, but the blueprint does not glue over it. See {bp "lem:dr-normal-derivation"}[].
 * *An Euler contraction.* Set $`E=fv`. Contraction by $`E` sends logarithmic forms to regular forms and descends to a map $`J` of degree $`-1` on $`V^\bullet=L^\bullet/fL^\bullet`. With $`W` the wedge by the class of $`\theta`, it satisfies $`\bar dJ+J\bar d=0` and $`WJ+JW=1`. See {bp "lem:dr-euler"}[].
 * *A filtration by pole order.* The modules $`F_m=f^{-m}L^\bullet` are subcomplexes that exhaust $`\Omega_{A_f}^\bullet`, while the unadjusted $`f^{-m}\Omega_A^\bullet` need not be subcomplexes. Each quotient $`F_m/F_{m-1}` is $`V^\bullet` with the differential $`D_m=\bar d-mW`. See {bp "lem:dr-pole-quotient"}[].
 * *One calculation.* When $`m\ge1` is invertible in $`k`, the operator $`h_m=-J/m` contracts the quotient, because $`D_mh_m+h_mD_m=-\tfrac1m\bigl(\bar dJ+J\bar d-m(WJ+JW)\bigr)=1`. See {bp "thm:dr-pole-contraction"}[].
 * *Finite reduction.* Every localized form has a finite pole order, and a contractible quotient lowers the pole order of a cocycle, or of a primitive, by one step. Both directions are finite inductions on a natural number, so no spectral sequence and no limit is needed. See {bp "thm:dr-comparison"}[].

The derivation $`v` is used only to prove bijectivity: the comparison map and its inverse are canonical.
This canonical comparison is used below to define the residue on localization cohomology.

# Why characteristic zero is needed

The construction uses rational scalars in exactly two places.
The first is the integration $`z^m\mapsto z^{m+1}/(m+1)` in {bp "thm:dr-homotopy"}[], which gives the affine-line axiom.
The second is the factor $`1/m` in $`h_m`, for every $`m\ge1`, in {bp "thm:dr-pole-contraction"}[], which gives the localization axiom.

Both are real requirements, because the conclusions themselves fail in characteristic $`p>0`.
By {bp "prop:dr-characteristic-p"}[], the form $`z^{p-1}dz` is a nonzero class on the affine line and $`z^p` is a nonconstant cocycle of degree zero, so $`k\to k[z]` is not a cohomology isomorphism and the affine-line axiom fails.
The pole argument fails too: for $`f=z`, the closed form $`z^{-p-1}dz` is not exact and cannot be represented by a logarithmic form, so the quotient at $`m=p` cannot be contracted as above.

This hypothesis belongs to the instance and not to the main theorem, whose base field stays arbitrary.
The instance simply provides no model in positive characteristic.

# Conventions

Fix $`A` and $`f`, and write $`A_f=A[1/f]` and $`S=A/(f)`.
Until a section says otherwise, the base $`k` is an arbitrary commutative ring.
All algebra maps are unital $`k`-algebra maps, including maps to the zero ring.
All de Rham differentials and complexes are $`k`-linear, not $`A`-linear, and complexes are extended by zero in negative degrees.
The theory is de Rham cohomology with a formal Laurent variable $`t` recording the twist, independent of any geometric coordinate:
$$`B=k[t,t^{-1}],\qquad\mathcal{B}_w=k\,t^w,\qquad C(A)=\Bigl(\bigoplus_{p\ge0}H^p_{\mathrm{dR}}(A/k)\Bigr)\otimes_kB.`
The component of bidegree $`(p,w)` is $`H^p_{\mathrm{dR}}(A/k)t^w`.
Coefficients have cohomological degree zero, so the ordinary tensor product of algebras has the correct multiplication.
The untwisted residue $`r` and Gysin map $`G` become the maps of the structure by $`x\,t^w\mapsto r(x)t^{w-1}` and $`y\,t^w\mapsto G(y)t^{w+1}`.

Signs are fixed once.
The shifted complex is $`(K[-1])^n=K^{n-1}` with differential $`-d_K`, and residues put $`df/f` on the left.
So the unshifted form residue anticommutes with $`d`, and the residue into $`\Omega_S^\bullet[-1]` is a chain map.
Cohomology of the shifted complex is identified with that of $`\Omega_S^\bullet` by the identity on cocycles and boundaries, with no scalar depending on the degree.

The construction is made first for the canonical quotient and localization, and is then transported to a divisor pair along the pair's own maps $`i` and $`j`.
These transport maps are determined by $`i` and $`j`, and every naturality statement below is expressed through them, so the statements survive transport.

# Exterior algebra

The construction needs two facts about exterior algebras, over any commutative ring and without dividing by two.

:::node "lem:dr-exterior" (decl := OrlikSolomon.DeRham.powerBaseChangeEquiv) (decl := OrlikSolomon.DeRham.powerBaseChangeEquiv_tmul) (decl := OrlikSolomon.DeRham.powerBaseChangeEquiv_symm_ιMulti) (decl := OrlikSolomon.DeRham.powerBaseChangeEquiv_naturality) (decl := OrlikSolomon.DeRham.powerQuotientEquiv) (decl := OrlikSolomon.DeRham.powerQuotientEquiv_mk) (decl := OrlikSolomon.DeRham.map_wedgeSubmodule_succ) (decl := OrlikSolomon.DeRham.wedgeSubmodule_zero) (decl := OrlikSolomon.DeRham.span_word_ι_length) (decl := OrlikSolomon.DeRham.mul_self_eq_zero_of_mem_exteriorPower_one) (decl := OrlikSolomon.DeRham.mul_comm_of_mem_exteriorPower)
Let $`M` be an $`A`-module with a submodule $`N`, and let $`A\to A'` be a map of commutative algebras.
There are natural identifications
$$`A'\otimes_A\bigwedge_A^nM\simeq\bigwedge_{A'}^n(A'\otimes_AM),\qquad\bigwedge_A^n(M/N)\simeq\bigwedge_A^nM\,/\,\bigl(N\wedge\bigwedge_A^{n-1}M\bigr).`
Exterior words span, each element of degree one squares to zero, and homogeneous elements of degrees $`p` and $`q` commute up to the sign $`(-1)^{pq}`.
:::

:::node "lem:dr-contraction" (decl := OrlikSolomon.DeRham.exteriorContraction) (decl := OrlikSolomon.DeRham.exteriorContraction_ιMulti) (decl := OrlikSolomon.DeRham.exteriorContraction_mem_exteriorPower) (decl := OrlikSolomon.DeRham.exteriorContraction_eq_zero_of_mem_exteriorPower_zero) (decl := OrlikSolomon.DeRham.exteriorContraction_mul_of_mem_exteriorPower) (decl := OrlikSolomon.DeRham.exteriorContraction_ι_mul_add) (decl := OrlikSolomon.DeRham.ker_wedgeLeft_succ) (decl := OrlikSolomon.DeRham.ker_wedgeLeft_zero)
An $`A`-linear map $`\lambda:M\to A` gives an $`A`-linear operator $`\iota_\lambda` of degree $`-1` on $`\bigwedge_AM` with
$$`\iota_\lambda(\alpha\wedge\beta)=\iota_\lambda\alpha\wedge\beta+(-1)^p\alpha\wedge\iota_\lambda\beta,\qquad\iota_\lambda(e\wedge\alpha)+e\wedge\iota_\lambda\alpha=\lambda(e)\alpha,`
for $`\alpha` of degree $`p`.
If $`\lambda(e)=1`, then the kernel of $`e\wedge-` on $`\bigwedge^nM` is $`e\wedge\bigwedge^{n-1}M`.
:::

# A de Rham dg algebra without a basis of differentials

The operator $`d` is not $`A`-linear, so it cannot be obtained as an $`A`-linear lift of $`a\mapsto da` to the exterior algebra, for the usual $`A`-module structure on forms, and defining it that way would be incorrect.
The blueprint constructs it on a polynomial ring, where differentials have a basis, and descends it to an arbitrary $`A` through a canonical polynomial presentation.
Nothing in this section needs smoothness or a hypothesis on the characteristic.

The library proves the same statements by a shorter construction, which uses no polynomial ring and no basis at all.
Let $`\sigma` be the grade involution, and consider pairs $`x+\varepsilon u` of forms, for an odd variable $`\varepsilon` with $`\varepsilon^2=0`:
$$`(x+\varepsilon u)(y+\varepsilon v)=xy+\varepsilon\bigl(\sigma(x)v+uy\bigr).`
The signed Leibniz rule says exactly that $`x\mapsto x+\varepsilon\,dx` is a ring map.
This ring is an $`A`-algebra through $`a\mapsto a+\varepsilon\,da`, whose image is central because $`da` anticommutes with odd forms, and for this twisted structure $`a\mapsto da` is a derivation, because $`da\wedge db+db\wedge da=0`.
So the universal properties of Kähler differentials and of the exterior algebra produce the map, and its second component is $`d`.
The polynomial formula and the presentation below are then theorems about this operator, and {bp "lem:dr-presentation"}[] shows that the operator descended from the presentation is the same one.

:::node "def:dr-forms" (decl := OrlikSolomon.DeRham.Forms) (decl := OrlikSolomon.DeRham.diff) (decl := OrlikSolomon.DeRham.mem_exteriorPower_zero_iff) (decl := OrlikSolomon.DeRham.mem_exteriorPower_one_iff) (decl := OrlikSolomon.DeRham.span_word_diff) (decl := OrlikSolomon.DeRham.Forms.induction_exteriorPower) (decl := OrlikSolomon.DeRham.Forms.induction)
For a commutative $`k`-algebra $`A`, put $`\Omega_A^0=A`, put $`\Omega_A^n=\bigwedge_A^n\Omega^1_{A/k}` for $`n>0`, and put $`\Omega_A^n=0` for $`n<0`.
Their direct sum is the exterior algebra under wedge multiplication, and every form is a finite sum of expressions $`a_0\,da_1\wedge\cdots\wedge da_n`.
:::

:::node "lem:dr-polynomial-dga" (decl := KaehlerDifferential.mvPolynomialBasis) (decl := OrlikSolomon.DeRham.d) (decl := OrlikSolomon.DeRham.d_mem_exteriorPower) (decl := OrlikSolomon.DeRham.d_smul_word_X) (decl := OrlikSolomon.DeRham.d_smul_word_X_eq_finsum) (decl := OrlikSolomon.DeRham.finite_support_pderiv_smul) (decl := OrlikSolomon.DeRham.eq_d_of_smul_word_X) (decl := OrlikSolomon.DeRham.d_d) (decl := OrlikSolomon.DeRham.d_mul_of_mem_exteriorPower)
For a polynomial ring $`P=k[X_i\mid i\in I]`, even with $`I` infinite, $`\Omega_P^1` is free on the $`dX_i`, and there is a $`k`-linear operator of degree one with
$$`d(p\,dX_{i_1}\wedge\cdots\wedge dX_{i_n})=\sum_{j\in I}\partial_j(p)\,dX_j\wedge dX_{i_1}\wedge\cdots\wedge dX_{i_n},`
where the sum has finite support.
It satisfies $`d^2=0` and the signed Leibniz rule, in every characteristic.
:::

:::node "lem:dr-presentation" (decl := OrlikSolomon.DeRham.presentationHom) (decl := OrlikSolomon.DeRham.presentationHom_X) (decl := OrlikSolomon.DeRham.presentationHom_surjective) (decl := OrlikSolomon.DeRham.differentialIdeal) (decl := OrlikSolomon.DeRham.differentialIdealPower) (decl := OrlikSolomon.DeRham.differentialIdealPower_zero) (decl := OrlikSolomon.DeRham.differentialIdealPower_succ) (decl := OrlikSolomon.DeRham.mem_differentialIdealPower_iff) (decl := OrlikSolomon.DeRham.mul_mem_differentialIdeal_left) (decl := OrlikSolomon.DeRham.mul_mem_differentialIdeal_right) (decl := OrlikSolomon.DeRham.d_mem_differentialIdeal) (decl := OrlikSolomon.DeRham.Forms.map_eq_zero_iff_of_surjective) (decl := OrlikSolomon.DeRham.quotientEquiv) (decl := OrlikSolomon.DeRham.quotientEquiv_mk) (decl := OrlikSolomon.DeRham.quotientEquiv_mk_mul) (decl := OrlikSolomon.DeRham.quotientPowerEquiv) (decl := OrlikSolomon.DeRham.quotientPowerEquiv_mk) (decl := OrlikSolomon.DeRham.presentationEquiv) (decl := OrlikSolomon.DeRham.presentationEquiv_dQuotient)
Let $`P_A=k[X_a\mid a\in A]`, let $`\epsilon:P_A\to A` send $`X_a` to $`a`, and let $`I=\ker\epsilon`.
The homogeneous ideal
$$`J^n=I\,\Omega_{P_A}^n+\operatorname{span}_{P_A}\{dh\wedge\eta:h\in I,\ \eta\in\Omega_{P_A}^{n-1}\}`
is stable under $`d`, and the quotient graded algebra is canonically $`\bigoplus_n\Omega_A^n`.
:::

:::node "def:dr-complex" (decl := OrlikSolomon.DeRham.d) (decl := OrlikSolomon.DeRham.presentationEquiv_dQuotient) (decl := OrlikSolomon.DeRham.powerD) (decl := OrlikSolomon.DeRham.complex)
The de Rham dg algebra of $`A/k` is $`\Omega_A^\bullet` with the differential descended from {bp "lem:dr-presentation"}[] and the wedge product.
The library constructs this differential directly, as described at the start of this section, and proves that it agrees with the descended one.
:::

:::node "thm:dr-dga" (decl := OrlikSolomon.DeRham.d_smul_word) (decl := OrlikSolomon.DeRham.d_d) (decl := OrlikSolomon.DeRham.d_mul_of_mem_exteriorPower) (decl := OrlikSolomon.DeRham.d_mul) (decl := OrlikSolomon.DeRham.isGradedCommutative_forms) (decl := OrlikSolomon.DeRham.Forms.map) (decl := OrlikSolomon.DeRham.Forms.map_smul_word) (decl := OrlikSolomon.DeRham.Forms.map_d) (decl := OrlikSolomon.DeRham.Forms.map_mem_exteriorPower) (decl := OrlikSolomon.DeRham.Forms.map_id) (decl := OrlikSolomon.DeRham.Forms.map_map) (decl := OrlikSolomon.DeRham.eq_d_of_smul_word) (decl := OrlikSolomon.DeRham.eq_d_of_leibniz)
For every commutative $`k`-algebra, $`d(a_0\,da_1\wedge\cdots\wedge da_n)=da_0\wedge da_1\wedge\cdots\wedge da_n`.
The operator squares to zero and satisfies the signed Leibniz rule, and the wedge product is associative, unital and graded commutative.
A $`k`-algebra map $`\phi:A\to A'` induces a dg algebra map $`\phi_*`, sending $`a_0\,da_1\cdots da_n` to $`\phi(a_0)\,d\phi(a_1)\cdots d\phi(a_n)`, compatibly with identities and composition.

The displayed formula also shows that the differential is unique with these properties, so it does not depend on the presentation.
:::

:::node "lem:dr-localization" (decl := OrlikSolomon.DeRham.isLocalizedModule_powerMap_kaehlerMap) (decl := OrlikSolomon.DeRham.powerLocalizationEquiv) (decl := OrlikSolomon.DeRham.powerLocalizationEquiv_mk_pow) (decl := OrlikSolomon.DeRham.mapPower_powerLocalizationEquiv) (decl := OrlikSolomon.DeRham.d_invSelf_pow_smul) (decl := OrlikSolomon.DeRham.d_invSelf_pow_smul_map) (decl := OrlikSolomon.DeRham.d_invSelf_smul_diff) (decl := OrlikSolomon.DeRham.Forms.mapPower_eq_zero_iff_of_isLocalizationAway)
For any $`A` and $`f\in A`, there are natural identifications $`\Omega_{A_f}^n\simeq(\Omega_A^n)_f`, and for $`m\ge0`
$$`d(f^{-m}\omega)=f^{-m}d\omega-mf^{-m-1}df\wedge\omega.`
In particular $`d(df/f)=0`.
None of this requires the localization map to be injective.
:::

:::node "lem:dr-quotient" (decl := OrlikSolomon.DeRham.Forms.mapPower_surjective) (decl := OrlikSolomon.DeRham.Forms.mapPower_powerD) (decl := OrlikSolomon.DeRham.principalQuotientPowerEquiv) (decl := OrlikSolomon.DeRham.principalQuotientPowerEquiv_mk) (decl := OrlikSolomon.DeRham.differentialIdealPower_span_singleton_zero) (decl := OrlikSolomon.DeRham.differentialIdealPower_span_singleton_succ) (decl := OrlikSolomon.DeRham.principalConormalMap) (decl := OrlikSolomon.DeRham.principalConormalMap_self) (decl := OrlikSolomon.DeRham.exact_principalConormalMap) (decl := KaehlerDifferential.mapBaseChange_surjective)
For $`S=A/(f)`, the restriction maps are surjective in each degree and commute with $`d`, and
$$`\Omega_S^n\simeq\Omega_A^n\,/\,\bigl(f\Omega_A^n+df\wedge\Omega_A^{n-1}\bigr).`
In particular there is a right exact conormal sequence
$$`(f)/(f^2)\longrightarrow\Omega_A^1\otimes_AS\longrightarrow\Omega_S^1\longrightarrow0,\qquad f\bmod f^2\longmapsto df\bmod f.`
Injectivity on the left is not claimed at this stage.
:::

:::node "def:dr-cohomology" (decl := OrlikSolomon.DeRham.cycles) (decl := OrlikSolomon.DeRham.boundaries) (decl := OrlikSolomon.DeRham.mem_boundaries) (decl := OrlikSolomon.DeRham.Cohomology) (decl := OrlikSolomon.DeRham.Cohomology.mk) (decl := OrlikSolomon.DeRham.Cohomology.mk_eq_mk_iff) (decl := OrlikSolomon.DeRham.Cohomology.mk_mul) (decl := OrlikSolomon.DeRham.Cohomology.mk_one) (decl := OrlikSolomon.DeRham.Cohomology.degree) (decl := OrlikSolomon.DeRham.Cohomology.mem_degree_iff) (decl := OrlikSolomon.DeRham.Cohomology.gradedAlgebraDegree) (decl := OrlikSolomon.DeRham.Cohomology.rangeD) (decl := OrlikSolomon.DeRham.Cohomology.degreeEquiv) (decl := OrlikSolomon.DeRham.Cohomology.coe_degreeEquiv_mk) (decl := OrlikSolomon.DeRham.homologyIso) (decl := OrlikSolomon.DeRham.coe_homologyIso_hom_homologyπ) (decl := OrlikSolomon.DeRham.Cohomology.isGradedCommutative_degree) (decl := OrlikSolomon.DeRham.Cohomology.map) (decl := OrlikSolomon.DeRham.Cohomology.map_mk) (decl := OrlikSolomon.DeRham.Cohomology.map_id) (decl := OrlikSolomon.DeRham.Cohomology.map_comp) (decl := OrlikSolomon.DeRham.Cohomology.map_mem_degree) (decl := OrlikSolomon.DeRham.cohomologyFunctor)
Define $`H^n_{\mathrm{dR}}(A/k)=\ker(d:\Omega_A^n\to\Omega_A^{n+1})/\operatorname{im}(d:\Omega_A^{n-1}\to\Omega_A^n)`.
The wedge product induces a unital, graded-commutative $`k`-algebra structure on the direct sum, covariantly functorial in $`A`.

Boundaries form an ideal in the algebra of cycles, not in the algebra of all forms, so the quotient has to be built from the cycles.
The library builds the total algebra first, as the quotient of the closed forms by the exact forms, and then identifies each degree piece with this quotient of $`\Omega_A^n` and with the homology of the de Rham complex.
:::

# Polynomial homotopy invariance

This section supplies the affine-line axiom.
It contains the first use of rational scalars, and it uses no smoothness.

:::node "lem:dr-polynomial-splitting" (decl := OrlikSolomon.DeRham.coefficientDerivative_single) (decl := OrlikSolomon.DeRham.coefficientDerivative_coeff) (decl := OrlikSolomon.DeRham.polynomialCoefficientD_single) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition_symm_apply) (decl := OrlikSolomon.DeRham.polynomialPowerDecomposition) (decl := OrlikSolomon.DeRham.polynomialPowerDecomposition_coe) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition_fst_mem) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition_snd_mem) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition_snd_eq_zero) (decl := OrlikSolomon.DeRham.polynomialFormInclusion_single) (decl := OrlikSolomon.DeRham.polynomialFormDecomposition_d)
For every $`A`, with new variable $`z`, each form on $`A[z]` decomposes uniquely as $`\omega=\alpha(z)+dz\wedge\beta(z)` with $`\alpha\in\Omega_A^n[z]` and $`\beta\in\Omega_A^{n-1}[z]`, where polynomials with coefficients in a module are finite sums.
The differential is
$$`d\omega=d_A\alpha+dz\wedge(\partial_z\alpha-d_A\beta).`
:::

:::node "thm:dr-homotopy" (decl := OrlikSolomon.DeRham.integrationScalar) (decl := OrlikSolomon.DeRham.mul_integrationScalar) (decl := OrlikSolomon.DeRham.polynomialEvaluationAtZero) (decl := OrlikSolomon.DeRham.coefficientIntegral) (decl := OrlikSolomon.DeRham.coefficientIntegral_single) (decl := OrlikSolomon.DeRham.coefficientIntegral_coeff_zero) (decl := OrlikSolomon.DeRham.coefficientIntegral_coeff_succ) (decl := OrlikSolomon.DeRham.coefficientDerivative_coefficientIntegral) (decl := OrlikSolomon.DeRham.coefficientIntegral_coefficientDerivative) (decl := OrlikSolomon.DeRham.mapCoefficients_coefficientIntegral) (decl := OrlikSolomon.DeRham.polynomialHomotopy) (decl := OrlikSolomon.DeRham.polynomialHomotopy_components) (decl := OrlikSolomon.DeRham.polynomialHomotopy_identity) (decl := OrlikSolomon.DeRham.polynomialHomotopy_mem_exteriorPower) (decl := OrlikSolomon.DeRham.polynomialHomotopy_eq_zero) (decl := OrlikSolomon.DeRham.polynomialCohomologyEquiv) (decl := OrlikSolomon.DeRham.polynomialCohomologyEquiv_apply) (decl := OrlikSolomon.DeRham.polynomialCohomologyEquiv_symm_apply) (decl := OrlikSolomon.DeRham.polynomialCohomologyEquiv_mem_degree_iff) (decl := OrlikSolomon.DeRham.bijective_cohomologyMap_C)
Suppose every positive integer is invertible in $`k`.
For every commutative $`k`-algebra $`A`, the inclusion $`A\to A[z]` is a cohomology isomorphism, with inverse induced by evaluation at $`z=0`.
A chain homotopy between the identity and evaluation followed by inclusion is
$$`K(\alpha+dz\wedge\beta)=I\beta,\qquad I\Bigl(\sum_{m\ge0}z^m\beta_m\Bigr)=\sum_{m\ge0}\frac{z^{m+1}}{m+1}\beta_m,`
so that $`dK+Kd=1-\operatorname{inc}\circ\operatorname{ev}_0`.
:::

# The algebra of a smooth principal pair

In this section $`f` is a non-zero-divisor of $`A`, and both $`A` and $`S=A/(f)` are formally smooth over $`k`.
No connectedness is assumed and the ring may be zero: the structure quantifies over disconnected algebras and the zero algebra, and over pairs whose equation is a unit.
The results here supply the global derivation of {ref "de-rham-strategy"}[the strategy].

:::node "lem:dr-projective" (decl := Algebra.FormallySmooth.projective_kaehlerDifferential) (decl := OrlikSolomon.DeRham.projective_exteriorPower) (decl := OrlikSolomon.DeRham.isSMulRegular_forms) (decl := OrlikSolomon.DeRham.Forms.injective_mapPower_of_isLocalizationAway)
If $`A` is formally smooth over $`k`, then $`\Omega_A^1` and every $`\Omega_A^n` are projective $`A`-modules.
If $`f` is a non-zero-divisor, then multiplication by $`f` is injective on each $`\Omega_A^n`, and $`\Omega_A^n\to\Omega_{A_f}^n` is injective.
:::

:::node "lem:dr-conormal" (decl := OrlikSolomon.DeRham.principalCotangentEquiv) (decl := OrlikSolomon.DeRham.conormalFunctional) (decl := OrlikSolomon.DeRham.conormalFunctional_df) (decl := OrlikSolomon.DeRham.conormalMap_apply) (decl := OrlikSolomon.DeRham.exact_conormalMap) (decl := OrlikSolomon.DeRham.conormalMap_injective) (decl := OrlikSolomon.DeRham.splitConormalSequence) (decl := OrlikSolomon.DeRham.splitConormalSequence_apply) (decl := OrlikSolomon.DeRham.splitConormalSequence_symm_apply_zero)
Put $`\overline{M}=\Omega_A^1\otimes_AS` and $`e=df\bmod f`.
There is an $`S`-linear map $`\lambda:\overline{M}\to S` with $`\lambda(e)=1`, so
$$`0\longrightarrow S\xrightarrow{\ 1\mapsto e\ }\overline{M}\longrightarrow\Omega_S^1\longrightarrow0`
is split exact.

The non-zero-divisor hypothesis identifies the conormal line, and smoothness of $`S` supplies the section of $`A/(f^2)\to S`.
Smoothness of $`A` is not needed for this lemma, and no basis or constant rank is assumed.
:::

:::node "lem:dr-normal-derivation" (decl := OrlikSolomon.DeRham.exists_normalDerivation_modulo) (decl := OrlikSolomon.DeRham.span_pair_eq_top_of_normalDerivationModulo) (decl := OrlikSolomon.DeRham.exists_localized_normalDerivation)
There exist a $`k`-derivation $`v:A\to A` and an element $`h\in A` with $`v(f)=1+fh`.
If $`g=v(f)`, then $`(f,g)=A`, and on $`A_g` the extended derivation $`v/g` takes $`f` to $`1`.
:::

:::node "lem:dr-modf-koszul" (decl := OrlikSolomon.DeRham.ker_wedgeLeft_df_mod_succ) (decl := OrlikSolomon.DeRham.ker_wedgeLeft_df_mod_zero) (decl := OrlikSolomon.DeRham.powerMap_eq_zero_of_wedgeLeft_df_eq_smul) (decl := OrlikSolomon.DeRham.powerMap_eq_zero_of_wedgeLeft_df_mem_smul)
If $`\eta\in\Omega_A^q` satisfies $`df\wedge\eta\in f\Omega_A^{q+1}`, then its image in $`\Omega_S^q` is zero.
Equivalently, modulo $`f`, the kernel of $`e\wedge-` on $`\bigwedge_S^q\overline{M}` is the image of $`e\wedge-` from the preceding degree.

This is a global calculation in an $`S`-module, by contraction with the functional of {bp "lem:dr-conormal"}[].
:::

# Logarithmic forms and the residue sequence

From here on, regular forms are identified with their images in $`\Omega_{A_f}^\bullet`, using {bp "lem:dr-projective"}[], and $`\theta=df/f`.
In Lean, a regular form is written as its image, and {bp "lem:dr-projective"}[] says that this loses nothing.
Everything here is stated for a surjection $`A\to S` with kernel $`(f)` and a certified localization away from $`f`, so it applies to a divisor pair directly.
The degrees $`L^n` are pieces of the algebra of all logarithmic forms, on which the residue $`\rho` is also defined.

:::node "def:dr-log" (decl := OrlikSolomon.DeRham.theta) (decl := OrlikSolomon.DeRham.theta_eq_dlog) (decl := OrlikSolomon.DeRham.regularPower) (decl := OrlikSolomon.DeRham.logPower) (decl := OrlikSolomon.DeRham.mem_logPower_zero) (decl := OrlikSolomon.DeRham.mem_logPower_succ) (decl := OrlikSolomon.DeRham.logPower_le_exteriorPower) (decl := OrlikSolomon.DeRham.powerToLog_zero_surjective) (decl := OrlikSolomon.DeRham.logForms) (decl := OrlikSolomon.DeRham.logMk) (decl := OrlikSolomon.DeRham.logComplex)
The logarithmic forms are the $`A`-submodule $`L^n=\Omega_A^n(\log f)=\Omega_A^n+\theta\wedge\Omega_A^{n-1}` of $`\Omega_{A_f}^n`.
In degree zero this is $`A`, and it is zero in negative degrees.
:::

:::node "lem:dr-log-dga" (decl := OrlikSolomon.DeRham.logForms) (decl := OrlikSolomon.DeRham.logMk_mul_logMk) (decl := OrlikSolomon.DeRham.gradedMonoid_logPower) (decl := OrlikSolomon.DeRham.logPower_eq_inf) (decl := OrlikSolomon.DeRham.iSup_logPower) (decl := OrlikSolomon.DeRham.d_add_theta_mul) (decl := OrlikSolomon.DeRham.d_mem_logForms) (decl := OrlikSolomon.DeRham.d_mem_logPower) (decl := OrlikSolomon.DeRham.logD) (decl := OrlikSolomon.DeRham.logPowerD) (decl := OrlikSolomon.DeRham.logComplex) (decl := OrlikSolomon.DeRham.d_self_smul) (decl := OrlikSolomon.DeRham.logIdeal) (decl := OrlikSolomon.DeRham.mul_mem_logIdeal_left) (decl := OrlikSolomon.DeRham.mul_mem_logIdeal_right) (decl := OrlikSolomon.DeRham.exists_coe_exteriorProj_eq_of_mem_logIdeal) (decl := OrlikSolomon.DeRham.logD_mem_logIdeal) (decl := OrlikSolomon.DeRham.exists_d_self_smul_eq_of_mem_logPower) (decl := OrlikSolomon.DeRham.logQuotientD) (decl := OrlikSolomon.DeRham.logQuotientD_mk)
The modules $`L^n` form a dg subalgebra of $`\Omega_{A_f}^\bullet`, with
$$`d(\omega+\theta\wedge\eta)=d\omega-\theta\wedge d\eta.`
The graded ideal $`fL^\bullet` is also a subcomplex, so $`L^\bullet/fL^\bullet` has an induced differential.
That is something to prove, since $`d` is not $`A`-linear.
:::

:::node "lem:dr-regularity" (decl := OrlikSolomon.DeRham.IsSmoothPrincipalPair) (decl := OrlikSolomon.DeRham.IsSmoothPrincipalPair.theta_mul_map_mem_regularPower_iff) (decl := OrlikSolomon.DeRham.IsSmoothPrincipalPair.exists_map_eq_theta_mul_map_iff) (decl := OrlikSolomon.DeRham.theta_mul_map_of_eq) (decl := OrlikSolomon.DeRham.Forms.map_eq_zero_of_diff_mul_eq_smul) (decl := OrlikSolomon.DeRham.IsSmoothPrincipalPair.map_injective)
For $`\eta\in\Omega_A^{n-1}`, the form $`\theta\wedge\eta` is regular if and only if $`\eta|_S=0`.

{bp "prop:dr-crossing-example"}[] shows that this fails for a crossing divisor, which is not smooth.
:::

:::node "def:dr-residue" (decl := OrlikSolomon.DeRham.logResidue) (decl := OrlikSolomon.DeRham.logResidue_logMk) (decl := OrlikSolomon.DeRham.logResidue_eq_of_coe_eq) (decl := OrlikSolomon.DeRham.logResidue_smul) (decl := OrlikSolomon.DeRham.logResidueₗ) (decl := OrlikSolomon.DeRham.logResidue_mem_exteriorPower) (decl := OrlikSolomon.DeRham.logResidue_eq_zero_of_mem_logPower_zero) (decl := OrlikSolomon.DeRham.logPowerResidue) (decl := OrlikSolomon.DeRham.coe_logPowerResidue) (decl := OrlikSolomon.DeRham.logPowerResidue_smul)
The form residue $`\rho:L^n\to\Omega_S^{n-1}` is $`\rho(\omega+\theta\wedge\eta)=\eta|_S`.
It is well defined by {bp "lem:dr-regularity"}[], and it is $`A`-linear with $`A` acting on the target through $`S`.
:::

:::node "thm:dr-residue-sequence" (decl := OrlikSolomon.DeRham.shiftedComplex) (decl := OrlikSolomon.DeRham.shiftedComplex_d_succ) (decl := OrlikSolomon.DeRham.regularToLog) (decl := OrlikSolomon.DeRham.logResidueHom) (decl := OrlikSolomon.DeRham.logResidueShortComplex) (decl := OrlikSolomon.DeRham.logResidueShortExact) (decl := OrlikSolomon.DeRham.logResidue_logD) (decl := OrlikSolomon.DeRham.logPowerResidue_logPowerD) (decl := OrlikSolomon.DeRham.IsSmoothPrincipalPair.ofRegular_injective) (decl := OrlikSolomon.DeRham.exact_ofRegular_logResidue) (decl := OrlikSolomon.DeRham.logResidue_surjective) (decl := OrlikSolomon.DeRham.powerToLog_injective) (decl := OrlikSolomon.DeRham.exact_powerToLog_logPowerResidue) (decl := OrlikSolomon.DeRham.logPowerResidue_surjective)
There is a degreewise short exact sequence of complexes of $`k`-modules
$$`0\longrightarrow\Omega_A^\bullet\longrightarrow L^\bullet\xrightarrow{\ \rho\ }\Omega_S^\bullet[-1]\longrightarrow0.`
Equivalently, on the unshifted target, $`\rho d=-d\rho`.
:::

:::node "lem:dr-form-projection" (decl := OrlikSolomon.DeRham.logResidue_mul_ofRegular)
For $`\alpha\in L^n` and $`\beta\in\Omega_A^q`, we have $`\rho(\alpha\wedge\beta)=\rho(\alpha)\wedge(\beta|_S)`.
There is no sign in this formula, because no factor moves across $`\theta`.
This fixes the convention needed later for the boundary projection formula of the structure.
:::

# The global pole-order comparison
%%%
tag := "de-rham-pole"
%%%

This is the pole-order argument outlined in {ref "de-rham-strategy"}[the strategy].
The assumptions on the smooth pair continue to hold, and from the contraction step onwards every positive integer is assumed invertible in $`k`.

:::node "lem:dr-cartan" (decl := OrlikSolomon.DeRham.formContraction) (decl := OrlikSolomon.DeRham.formContraction_diff) (decl := OrlikSolomon.DeRham.formContraction_mul_of_mem_exteriorPower) (decl := OrlikSolomon.DeRham.formContraction_mem_exteriorPower) (decl := OrlikSolomon.DeRham.formContraction_eq_zero) (decl := OrlikSolomon.DeRham.lieDerivative) (decl := OrlikSolomon.DeRham.cartanFormula) (decl := OrlikSolomon.DeRham.lieDerivative_mul) (decl := OrlikSolomon.DeRham.lieDerivative_mem_exteriorPower) (decl := OrlikSolomon.DeRham.lieDerivative_algebraMap) (decl := OrlikSolomon.DeRham.lieDerivative_diff) (decl := OrlikSolomon.DeRham.localizedDerivation) (decl := OrlikSolomon.DeRham.map_formContraction_localizedDerivation) (decl := OrlikSolomon.DeRham.map_lieDerivative_localizedDerivation) (decl := OrlikSolomon.DeRham.formContraction_smul)
For a $`k`-derivation $`v:A\to A`, contraction $`\iota_v` is defined by the functional $`da\mapsto v(a)` on $`\Omega_A^1`, and it is an $`A`-linear signed derivation of degree $`-1`.
The operator $`\mathcal{L}_v=d\iota_v+\iota_vd` is a $`k`-linear derivation of degree zero, with $`\mathcal{L}_v(a)=v(a)` and $`\mathcal{L}_v(da)=d(v(a))`.
These constructions extend to localizations, and $`\iota_{av}=a\iota_v`.
:::

:::node "lem:dr-euler" (decl := OrlikSolomon.DeRham.logEulerDerivation) (decl := OrlikSolomon.DeRham.logEulerContraction) (decl := OrlikSolomon.DeRham.logEulerContraction_logMk) (decl := OrlikSolomon.DeRham.logEulerContraction_mem_logIdeal) (decl := OrlikSolomon.DeRham.logQuotientEulerContraction) (decl := OrlikSolomon.DeRham.logQuotientThetaWedge) (decl := OrlikSolomon.DeRham.logQuotientPowerEulerContraction) (decl := OrlikSolomon.DeRham.logQuotientEulerContraction_eq_zero) (decl := OrlikSolomon.DeRham.formContraction_logEulerDerivation_mem_regularPower) (decl := OrlikSolomon.DeRham.logQuotientEulerContraction_anticommute) (decl := OrlikSolomon.DeRham.logQuotientThetaWedge_euler_identity)
Choose $`v` and $`h` as in {bp "lem:dr-normal-derivation"}[], and set $`E=fv`.
On $`L^\bullet`, the operator $`\iota_E` takes values in regular forms, preserves $`fL^\bullet`, and descends to a map $`J` of degree $`-1` on $`V^\bullet=L^\bullet/fL^\bullet`.
If $`\bar d` is the differential of $`V^\bullet` and $`W` is left wedge multiplication by the class of $`\theta`, then
$$`\bar dJ+J\bar d=0,\qquad WJ+JW=1.`
The proof uses only the congruence of $`v(f)` to $`1` modulo $`f`, and does not assert that $`v(f)=1` in $`A`.
:::

:::node "def:dr-pole-filtration" (decl := OrlikSolomon.DeRham.poleForms) (decl := OrlikSolomon.DeRham.poleFiltration) (decl := OrlikSolomon.DeRham.poleForms_zero) (decl := OrlikSolomon.DeRham.poleFiltration_zero) (decl := OrlikSolomon.DeRham.poleFiltration_monotone) (decl := OrlikSolomon.DeRham.iSup_poleFiltration) (decl := OrlikSolomon.DeRham.mem_poleFiltration_iff) (decl := OrlikSolomon.DeRham.d_invSelf_pow_smul_eq_theta) (decl := OrlikSolomon.DeRham.d_mem_poleFiltration) (decl := OrlikSolomon.DeRham.poleComplex) (decl := OrlikSolomon.DeRham.poleInclusion) (decl := OrlikSolomon.DeRham.poleToLocalization)
For $`m\in\mathbb{N}`, put $`F_m^n=f^{-m}L^n\subseteq\Omega_{A_f}^n`.
Then $`F_0=L`, the filtration is increasing and exhaustive, and every $`F_m` is a subcomplex.
The logarithmic forms are essential here, because the modules $`f^{-m}\Omega_A^\bullet` need not be subcomplexes.
:::

:::node "lem:dr-pole-quotient" (decl := OrlikSolomon.DeRham.poleQuotientEquiv) (decl := OrlikSolomon.DeRham.poleQuotientEquiv_mk) (decl := OrlikSolomon.DeRham.poleQuotientPowerEquiv) (decl := OrlikSolomon.DeRham.poleQuotientDifferential) (decl := OrlikSolomon.DeRham.poleQuotientD_poleQuotientEquiv)
For $`m\ge1`, the map $`\bar\xi\mapsto\overline{f^{-m}\xi}` is a graded $`k`-linear isomorphism from $`V^\bullet` to $`F_m^\bullet/F_{m-1}^\bullet`.
Under it, the differential on the right becomes $`D_m=\bar d-mW`.
Lean indexes the positive pole order as $`m+1`; the quotient identification is in fact linear over $`A`, while its differential is linear over $`k`.
:::

:::node "thm:dr-pole-contraction" (decl := OrlikSolomon.DeRham.positivePoleHomotopy) (decl := OrlikSolomon.DeRham.positivePoleQuotientContractible) (decl := OrlikSolomon.DeRham.poleQuotientHomotopy) (decl := OrlikSolomon.DeRham.poleQuotientD_homotopy_add) (decl := OrlikSolomon.DeRham.positivePoleHomotopy_mem_logQuotientPower) (decl := OrlikSolomon.DeRham.positivePoleHomotopy_eq_zero) (decl := OrlikSolomon.DeRham.poleQuotientHomotopy_mem_poleQuotientPower) (decl := OrlikSolomon.DeRham.poleQuotientHomotopy_eq_zero)
If $`m\ge1` is invertible in $`k`, then $`h_m=-\tfrac1mJ` is a contracting homotopy for $`(V^\bullet,D_m)`, and hence for $`F_m/F_{m-1}`, that is, $`D_mh_m+h_mD_m=1`.
This is the second use of rational scalars, and it is an equation of operators in each degree, not only a statement that cohomology vanishes.
:::

:::node "lem:dr-filtration-reduction" (decl := OrlikSolomon.exists_cocycle_reduction) (decl := OrlikSolomon.exists_primitive_reduction) (decl := OrlikSolomon.exists_cocycle_reduction_of_contractible_quotient) (decl := OrlikSolomon.exists_primitive_reduction_of_contractible_quotient) (decl := OrlikSolomon.DeRham.exists_pole_cocycle_reduction) (decl := OrlikSolomon.DeRham.exists_pole_primitive_reduction)
Suppose $`F_{m-1}\subseteq F_m` is an inclusion of complexes with contractible quotient.
Every cocycle in $`F_m^n` is cohomologous in $`F_m` to one in $`F_{m-1}^n`, and a cocycle in $`F_{m-1}^n` that is a boundary in $`F_m` is already a boundary in $`F_{m-1}`.
:::

:::node "thm:dr-comparison" (decl := OrlikSolomon.DeRham.exists_closed_logForm_sub_d_eq) (decl := OrlikSolomon.DeRham.exists_logPrimitive_of_exists) (decl := OrlikSolomon.DeRham.logToLocalizationQuasiIso) (decl := OrlikSolomon.DeRham.logToLocalizationEquiv) (decl := OrlikSolomon.DeRham.logToLocalizationEquiv_apply) (decl := OrlikSolomon.DeRham.logToLocalizationDegreeEquiv) (decl := OrlikSolomon.DeRham.coe_logToLocalizationDegreeEquiv) (decl := OrlikSolomon.DeRham.coe_logToLocalizationDegreeEquiv_symm) (decl := OrlikSolomon.DeRham.logToLocalizationGradingEquiv) (decl := OrlikSolomon.DeRham.logToLocalizationEquiv_isHomogeneous) (decl := OrlikSolomon.DeRham.logToLocalizationEquiv_symm_isHomogeneous) (decl := OrlikSolomon.DeRham.logToLocalizationEquiv_eq)
If $`k` contains $`\mathbb{Q}` and $`(A,f)` is a smooth principal pair, the inclusion $`L^\bullet\hookrightarrow\Omega_{A_f}^\bullet` induces an isomorphism in every cohomological degree, and an algebra equivalence on total cohomology.

Applying {bp "lem:dr-filtration-reduction"}[] successively gives surjectivity and injectivity by finite inductions on the pole bound.
:::

# Cohomological residue, Gysin and signs

These are the maps that the structure asks for, before the twist by $`t`.
The sign of the connecting map is fixed here by a formula on representatives, and a connecting map taken from a library has to be reconciled with this formula.

:::node "def:dr-gysin" (decl := OrlikSolomon.DeRham.gysin) (decl := OrlikSolomon.DeRham.gysin_mk_of_logResidue_eq) (decl := OrlikSolomon.DeRham.residue) (decl := OrlikSolomon.DeRham.residue_toCohomology) (decl := OrlikSolomon.DeRham.LogCohomology.residue) (decl := OrlikSolomon.DeRham.LogCohomology.residue_mk)
The residue $`r^n:H^n_{\mathrm{dR}}(A_f)\to H^{n-1}_{\mathrm{dR}}(S)` is the map induced by $`\rho`, after the inverse of {bp "thm:dr-comparison"}[the logarithmic comparison].
The Gysin map $`G^q:H^q_{\mathrm{dR}}(S)\to H^{q+2}_{\mathrm{dR}}(A)` is the connecting map, with the convention that $`G^q([\gamma])=[d\lambda]` for closed $`\gamma` and $`\lambda\in L^{q+1}` with $`\rho\lambda=\gamma`.
Here $`d\lambda` is regular by exactness.
:::

:::node "lem:dr-exactness" (decl := OrlikSolomon.DeRham.exact_gysin_map) (decl := OrlikSolomon.DeRham.exact_map_residue) (decl := OrlikSolomon.DeRham.exact_residue_gysin) (decl := OrlikSolomon.DeRham.isHomogeneousOfShift_gysin) (decl := OrlikSolomon.DeRham.isHomogeneousOfShift_residue) (decl := OrlikSolomon.DeRham.map_eq_zero_iff_of_mem_grading) (decl := OrlikSolomon.DeRham.residue_eq_zero_iff_of_mem_grading) (decl := OrlikSolomon.DeRham.gysin_eq_zero_iff_of_mem_grading) (decl := OrlikSolomon.DeRham.residue_mk_add_theta_mul) (decl := OrlikSolomon.DeRham.gysin_mk_of_map_eq) (decl := OrlikSolomon.DeRham.exists_mem_exteriorPower_map_eq_neg_theta_mul)
The sequence
$$`\cdots\to H^{n-2}_{\mathrm{dR}}(S)\xrightarrow{G}H^n_{\mathrm{dR}}(A)\xrightarrow{j_*}H^n_{\mathrm{dR}}(A_f)\xrightarrow{r}H^{n-1}_{\mathrm{dR}}(S)\xrightarrow{G}H^{n+1}_{\mathrm{dR}}(A)\to\cdots`
is exact.
For a closed logarithmic representative, $`r([\omega+\theta\wedge\eta])=[\eta|_S]`.
For a closed $`\gamma\in\Omega_S^q` and any regular lift $`\eta\in\Omega_A^q`, we have $`G([\gamma])=[-\theta\wedge d\eta]`, and the form inside the brackets is regular.
These formulas introduce no further factor of $`(-1)^q`.
:::

:::node "thm:dr-projection" (decl := OrlikSolomon.DeRham.residue_mul_map) (decl := OrlikSolomon.DeRham.LogCohomology.residue_mul_ofCohomology)
For $`a\in H^n_{\mathrm{dR}}(A_f)` and $`b\in H^q_{\mathrm{dR}}(A)`, we have $`r(a\,j_*b)=r(a)\,i_*b`.
In particular this has the exact sign that the structure requires when $`n=1`.
:::

# Naturality for associated equations

A morphism of divisor pairs sends the equation of its source to a unit multiple of the equation of its target.
The proofs of these two theorems do not tensor an exact sequence along the map, so they need no flatness.

:::node "thm:dr-log-naturality" (decl := OrlikSolomon.DivisorPair.Hom.isPairHom) (decl := OrlikSolomon.DeRham.IsPairHom) (decl := OrlikSolomon.DeRham.IsPairHom.of_associated) (decl := OrlikSolomon.DeRham.IsPairHom.map_theta) (decl := OrlikSolomon.DeRham.IsPairHom.map_mem_logForms) (decl := OrlikSolomon.DeRham.IsPairHom.map_mem_logPower) (decl := OrlikSolomon.DeRham.logMap) (decl := OrlikSolomon.DeRham.logMap_logD) (decl := OrlikSolomon.DeRham.logMap_ofRegular) (decl := OrlikSolomon.DeRham.logResidue_logMap) (decl := OrlikSolomon.DeRham.logResidueShortComplexMap)
Let $`(A,f)` and $`(A',f')` be smooth principal pairs, and let $`\phi:A\to A'` satisfy $`\phi(f)=uf'` for a unit $`u` of $`A'`, with induced maps $`\psi:S\to S'` and $`\chi:A_f\to A'_{f'}`.
Then $`\chi_*` takes logarithmic forms to logarithmic forms, commutes with their differentials, and satisfies $`\rho'\chi_*=\psi_*\rho`, so that with $`\phi_*` it is a morphism of the short exact sequences of complexes.

The point is that $`\chi_*\theta=\theta'+du/u`, whose second term is regular on $`A'`.
:::

:::node "thm:dr-naturality" (decl := OrlikSolomon.DeRham.residue_map) (decl := OrlikSolomon.DeRham.gysin_map) (decl := OrlikSolomon.DeRham.residue_eq_of_associated) (decl := OrlikSolomon.DeRham.gysin_eq_of_associated) (decl := OrlikSolomon.DeRham.logForms_eq_of_associated)
Under the same hypotheses, $`r'\chi_*=\psi_*r` and $`G'\psi_*=\phi_*G`.
The constructions are unchanged on replacing $`f` by an associated equation in the same ambient algebra, and the normal derivations chosen to prove the comparison play no role in these maps.
:::

# The instance and its corollaries

This section assembles the theory and instantiates the main theorem.
The blueprint's checklist covers all 22 fields of the structure `OrdinaryTheory` and names the node that proves each one.
No field may be weakened, and neither the comparison, nor exactness, nor affine-line invariance may become a hypothesis of the instance.

:::node "def:dr-twisted-functor" (decl := OrlikSolomon.laurentGrading) (decl := OrlikSolomon.gradedAlgebraLaurentGrading) (decl := OrlikSolomon.mem_laurentGrading_iff) (decl := OrlikSolomon.DeRham.TwistedCohomology) (decl := OrlikSolomon.DeRham.TwistedCohomology.grading) (decl := OrlikSolomon.DeRham.TwistedCohomology.gradedAlgebraGrading) (decl := OrlikSolomon.DeRham.TwistedCohomology.mem_grading_iff) (decl := OrlikSolomon.DeRham.TwistedCohomology.grading_of_neg) (decl := OrlikSolomon.DeRham.TwistedCohomology.map) (decl := OrlikSolomon.DeRham.TwistedCohomology.map_tmul) (decl := OrlikSolomon.DeRham.twistedCohomologyFunctor) (decl := OrlikSolomon.DeRham.twistedCohomologyFunctor_map_tmul) (decl := OrlikSolomon.DeRham.instAlgebraObjTwistedCohomologyFunctor) (decl := OrlikSolomon.DeRham.instIsScalarTowerObjTwistedCohomologyFunctor)
Let $`k` be a field of characteristic zero and $`B=k[t,t^{-1}]`.
For each smooth $`k`-algebra, put $`C(A)=H^\bullet_{\mathrm{dR}}(A/k)\otimes_kB` with $`C(A)_{p,w}=H^p_{\mathrm{dR}}(A/k)t^w`, which is zero for $`p<0`, and put $`\mathcal{B}_w=k\,t^w`.
A map $`\phi` acts by $`C(\phi)=H^\bullet(\phi_*)\otimes1`.
The $`B`-algebra structure uses the coefficient factor, and the $`k`-algebra structure is its restriction.
:::

:::node "lem:dr-ordinary-basic" (decl := OrlikSolomon.bijective_algebraMap_laurentGrading_zero) (decl := OrlikSolomon.DeRham.TwistedCohomology.algebraMap_mem_grading) (decl := OrlikSolomon.DeRham.isHomogeneousOfShift_twistedCohomologyFunctor_map) (decl := OrlikSolomon.DeRham.TwistedCohomology.isGradedCommutative_grading) (decl := OrlikSolomon.DeRham.bijective_algebraMap_twistedCohomologyFunctor_point) (decl := OrlikSolomon.DeRham.TwistedCohomology.eq_zero_of_mem_grading_point) (decl := OrlikSolomon.DeRham.bijective_twistedCohomologyFunctor_map_polynomialC)
This functor and grading satisfy every field of the structure that precedes the Gysin and residue maps.
In particular the map $`B\to C(k)` is bijective, the point has no cohomology in nonzero cohomological degrees, and $`C(A)\to C(A[z])` is bijective for every smooth $`A`.
:::

:::node "def:dr-twisted-maps" (decl := OrlikSolomon.DeRham.TwistedCohomology.twistMap) (decl := OrlikSolomon.DeRham.TwistedCohomology.gysin) (decl := OrlikSolomon.DeRham.TwistedCohomology.residue) (decl := OrlikSolomon.DeRham.gysin_twistedClass) (decl := OrlikSolomon.DeRham.residue_twistedClass)
For a fixed divisor pair, the canonical construction is transported along the maps of the pair, and $`G` and $`r` are extended $`B`-linearly by
$$`g(y\,t^w)=G(y)t^{w+1},\qquad R(x\,t^w)=r(x)t^{w-1}.`
These are the proposed Gysin and residue fields of the structure.

In Lean nothing needs to be transported: a divisor pair is itself a smooth principal pair, with its open part as the localization.
:::

:::node "thm:dr-ordinary-localization" (decl := OrlikSolomon.DeRham.TwistedCohomology.isHomogeneousOfShift_gysin) (decl := OrlikSolomon.DeRham.TwistedCohomology.isHomogeneousOfShift_residue) (decl := OrlikSolomon.DeRham.TwistedCohomology.exact_gysin_map) (decl := OrlikSolomon.DeRham.TwistedCohomology.exact_map_residue) (decl := OrlikSolomon.DeRham.TwistedCohomology.exact_residue_gysin) (decl := OrlikSolomon.DeRham.TwistedCohomology.gysin_map) (decl := OrlikSolomon.DeRham.TwistedCohomology.residue_map) (decl := OrlikSolomon.DeRham.TwistedCohomology.residue_mul_map)
The maps $`g` and $`R` have shifts $`(2,1)` and $`(-1,-1)`.
They satisfy $`\operatorname{im}g=\ker C(j)`, $`\operatorname{im}C(j)=\ker R` and $`\operatorname{im}R=\ker g`, and they commute with every morphism of divisor pairs.
Moreover $`R(\alpha\,C(j)\beta)=R(\alpha)\,C(i)\beta` for $`\alpha\in C(A_f)_{1,1}` and $`\beta\in C(A)`.

In Lean the exactness comes from flatness: $`k[t,t^{-1}]` is free over $`k`, so tensoring with it preserves exactness, and $`t^w` is a unit.
The projection formula is proved for every $`\alpha`, with no condition on its degree.
:::

:::node "thm:dr-instance" (decl := OrlikSolomon.DeRham.ordinaryTheory) (decl := OrlikSolomon.DeRham.nontrivial_coefficients) (decl := OrlikSolomon.DeRham.nontrivialOrdinaryTheoryObjPoint)
For every field $`k` of characteristic zero, this data defines a value of the structure `OrdinaryTheory`, with $`R=k` and $`B=k[t,t^{-1}]`.
The coefficient ring and the cohomology of the point are nonzero.
All fields hold for every smooth algebra and every divisor pair, without assuming anything about arrangements, connectedness or nonemptiness, or flatness of morphisms.

The theorem does not say that $`C(A)` is nonzero for every $`A`: the zero algebra is a valid object, and its cohomology is zero.
:::

:::node "lem:dr-tau"
For the standard pair $`(k[x],x)`, the normalized class $`\tau` of {bp "lem:gm"}[] is $`[dx/x]\,t` in $`C(k[x,x^{-1}])_{1,1}`.
For a unit $`a` on any smooth algebra, the logarithmic class of {bp "def:log"}[] is $`[da/a]\,t`.
:::

:::node "cor:dr-affine"
For every split affine hyperplane arrangement $`\mathcal{A}` over a field $`k` of characteristic zero,
$$`\operatorname{OS}_k(\mathcal{A})\simeq_k\bigoplus_{q\ge0}H^q_{\mathrm{dR}}(U_{\mathcal{A}}/k),\qquad e_H\longmapsto[df_H/f_H].`
It comes from instantiating {bp "thm:affine"}[] and removing the powers of $`t` from the diagonal, and no part of the proof about arrangements is repeated.
:::

:::node "cor:dr-projective"
For a nonempty split projective arrangement $`\mathcal{P}` in $`\mathbb{P}^n_k`, with $`k` as above,
$$`\overline{\operatorname{OS}}_k(\mathcal{P})\simeq_k\bigoplus_{q\ge0}H^q_{\mathrm{dR}}(U_{\mathcal{P}}/k),\qquad e_i-e_j\longmapsto\Bigl[\frac{d(\ell_i/\ell_j)}{\ell_i/\ell_j}\Bigr],`
independently of the equations and of the hyperplane chosen at infinity.
It comes from instantiating {bp "thm:projective"}[].
The empty projective arrangement needs a separate calculation and is not included.
:::

# Worked regressions and excluded cases

These calculations test the maps and the signs, and not just the dimension of the answer.
Unless stated otherwise, $`k` is a field of characteristic zero.

:::node "prop:dr-gm-example" (decl := OrlikSolomon.DeRham.Examples.laurentThetaClass) (decl := OrlikSolomon.DeRham.Examples.gmCohomologyEquiv) (decl := OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_apply) (decl := OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_zero_iff) (decl := OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_one_iff) (decl := OrlikSolomon.DeRham.Examples.gm_eq_zero_of_mem_degree_succ_succ) (decl := OrlikSolomon.DeRham.Examples.gm_residue_theta) (decl := OrlikSolomon.DeRham.Examples.gm_normalized_tau)
For $`A=k[x]` and $`f=x`, we have $`H^0_{\mathrm{dR}}(A_f)=k`, $`H^1_{\mathrm{dR}}(A_f)=k[dx/x]` and $`H^n_{\mathrm{dR}}(A_f)=0` for $`n>1`.
Moreover $`r([dx/x])=1`, and the twisted normalized class is $`[dx/x]\,t`.
:::

:::node "prop:dr-unit-example" (decl := IsLocalization.atUnit) (decl := OrlikSolomon.Sanity.zeroDerivation_unit_normal) (decl := OrlikSolomon.DeRham.Examples.unit_closed_subsingleton) (decl := OrlikSolomon.DeRham.Examples.unit_logForms_eq_top) (decl := OrlikSolomon.DeRham.Examples.unit_twistedCohomologyMap_bijective) (decl := OrlikSolomon.DeRham.Examples.unit_gysin_eq_zero) (decl := OrlikSolomon.DeRham.Examples.unit_residue_eq_zero) (decl := OrlikSolomon.DeRham.Examples.unit_twistedGysin_eq_zero) (decl := OrlikSolomon.DeRham.Examples.unit_twistedResidue_eq_zero)
If $`f` is a unit in a smooth $`A`, then $`S=0`, $`A_f\simeq A` and $`L^\bullet=\Omega_A^\bullet`.
Residue and Gysin are both zero, and all the exactness fields reduce to the identity isomorphism on $`C(A)`.
In the contraction one may take $`v=0` and $`h=-f^{-1}`, which confirms that no step assumed a nonempty divisor.
:::

:::node "prop:dr-product-example" (decl := OrlikSolomon.Sanity.productPolynomialQuotientEquiv) (decl := OrlikSolomon.DeRham.Examples.productLocalizationEquiv) (decl := OrlikSolomon.DeRham.Examples.productLaurentCohomologyEquiv) (decl := OrlikSolomon.DeRham.Examples.productCohomologyEquiv) (decl := OrlikSolomon.DeRham.Examples.productCohomologyEquiv_mem_degree_iff) (decl := OrlikSolomon.DeRham.Examples.product_eq_zero_of_mem_degree_succ_succ) (decl := OrlikSolomon.DeRham.Examples.productCohomologyEquiv_generator) (decl := OrlikSolomon.DeRham.Examples.product_residue_generator) (decl := OrlikSolomon.Sanity.productPolynomialNormal_equation) (decl := OrlikSolomon.Sanity.productPolynomial_no_global_normal)
For $`A=k\times k[z]` and $`f=(1,z)`, we have $`S\simeq k`, $`A_f\simeq k\times k[z,z^{-1}]`, $`H^0_{\mathrm{dR}}(A_f)=k\times k` and $`H^1_{\mathrm{dR}}(A_f)=k[(0,dz/z)]`.
All higher groups vanish, and the residue takes $`(0,dz/z)` to $`1` on $`S`.

This divisor lies on one connected component, and it is why the derivation is only normal modulo $`f`.
Taking $`v=(0,\partial_z)` gives $`v(f)=(0,1)=1+f(-1,0)`, while $`df=(0,dz)` is not unimodular on all of $`A`.
:::

:::node "prop:dr-zero-example" (decl := OrlikSolomon.smooth_punit) (decl := OrlikSolomon.SmoothAlg.zero) (decl := OrlikSolomon.Sanity.zero_exists_normalDerivation_modulo) (decl := OrlikSolomon.DeRham.Examples.isSmoothPrincipalPair_of_subsingleton) (decl := OrlikSolomon.DeRham.Examples.zero_form_eq_zero) (decl := OrlikSolomon.DeRham.Examples.zero_cohomology_eq_zero) (decl := OrlikSolomon.DeRham.Examples.zero_twistedCohomology_eq_zero) (decl := OrlikSolomon.DeRham.ordinaryTheory)
For $`A=0`, every form and cohomology module is zero, $`C(A)` is the zero $`B`-algebra, and the fields for divisor pairs hold for its unique equation.
The zero algebra is formally smooth and finitely presented, so it really is an object of the category, and no nontriviality can be imposed on general objects.
:::

:::node "prop:dr-crossing-example" (decl := OrlikSolomon.DeRham.Examples.crossingEquation_mem_nonZeroDivisors) (decl := OrlikSolomon.DeRham.Examples.crossingDivisor_not_formallySmooth) (decl := OrlikSolomon.DeRham.Examples.crossing_kaehler_restriction_ne_zero) (decl := OrlikSolomon.DeRham.Examples.crossing_theta_mul) (decl := OrlikSolomon.DeRham.Examples.crossing_logMk_eq) (decl := OrlikSolomon.DeRham.Examples.crossing_no_residue)
For $`A=k[x,y]` and $`f=xy`, the element $`f` is a non-zero-divisor but $`S=A/(xy)` is not smooth.
The regularity criterion fails: with $`\eta=y\,dx`, the form $`\frac{d(xy)}{xy}\wedge\eta=dy\wedge dx` is regular, while $`\eta|_S\ne0` in $`\Omega_S^1`.
So the same logarithmic form has two presentations whose proposed residues disagree, which is the exact way in which this divisor is excluded.
:::

:::node "prop:dr-morphism-examples" (decl := OrlikSolomon.DeRham.Examples.unitChangeHom) (decl := OrlikSolomon.DeRham.Examples.flat_unitChangeHom_ambient) (decl := OrlikSolomon.DeRham.Examples.unitChange_residue_theta) (decl := OrlikSolomon.DeRham.Examples.nonFlatHom) (decl := OrlikSolomon.DeRham.Examples.not_flat_nonFlatAmbient) (decl := OrlikSolomon.DeRham.Examples.nonFlatHom_gysin_map) (decl := OrlikSolomon.DeRham.Examples.nonFlatHom_residue_map) (decl := OrlikSolomon.DeRham.Examples.ramifiedAmbient_not_pairHom) (decl := OrlikSolomon.DeRham.Examples.ramified_map_theta) (decl := OrlikSolomon.DeRham.Examples.ramified_residue_theta) (decl := OrlikSolomon.DeRham.Examples.ramified_logResidue_theta_ne_one)
These test the precise condition on morphisms.
 * For $`k[z]\to k[x,y,y^{-1}]` with $`z\mapsto xy` and target equation $`f'=x`, the residue of $`d(xy)/(xy)` is $`1`. This map is flat.
 * A morphism of admissible pairs that is not flat is $`(k[z,v],z)\to(k[x,y,y^{-1}],x)` with $`z\mapsto xy` and $`v\mapsto0`, and residue and Gysin naturality still hold.
 * The map $`(k[z],z)\to(k[x],x)` with $`z\mapsto x^2` is not a morphism of pairs, since $`x^2` is not a unit multiple of $`x`. Its pulled-back logarithmic form has residue $`2`, not $`1`.
:::

:::node "prop:dr-torus-example" (decl := OrlikSolomon.DeRham.Examples.torusX) (decl := OrlikSolomon.DeRham.Examples.torusY) (decl := OrlikSolomon.DeRham.Examples.torusCohomologyEquiv) (decl := OrlikSolomon.DeRham.Examples.torusCohomologyEquiv_apply) (decl := OrlikSolomon.DeRham.Examples.torusCohomologyEquiv_mem_grading_iff) (decl := OrlikSolomon.DeRham.Examples.torus_eq_zero_of_mem_degree_succ_succ_succ) (decl := OrlikSolomon.DeRham.Examples.torusX_mul_self) (decl := OrlikSolomon.DeRham.Examples.torusY_mul_self) (decl := OrlikSolomon.DeRham.Examples.torus_anticommute) (decl := OrlikSolomon.DeRham.Examples.torusResidueX_top) (decl := OrlikSolomon.DeRham.Examples.torus_residue_inner_mul_outer)
For $`T=k[x^{\pm1},y^{\pm1}]`, put $`e_x=dx/x` and $`e_y=dy/y`.
Then $`H^0_{\mathrm{dR}}(T)=k`, $`H^1_{\mathrm{dR}}(T)=k[e_x]\oplus k[e_y]` and $`H^2_{\mathrm{dR}}(T)=k[e_x\wedge e_y]`, with all higher groups zero and the exterior multiplication on these generators.
The residue along $`x=0` in the ambient $`k[x,y^{\pm1}]` sends $`[e_x\wedge e_y]` to $`[e_y]`.
Along $`y=0`, it sends the same ordered class to $`-[e_x]`.
No Künneth theorem is used.
:::

:::node "prop:dr-characteristic-p" (decl := OrlikSolomon.DeRham.Examples.d_algebraMap_X_pow_charP) (decl := OrlikSolomon.DeRham.Examples.X_pow_ne_C) (decl := OrlikSolomon.DeRham.Examples.not_surjective_twisted_map_C_of_charP) (decl := OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm_class_ne_zero) (decl := OrlikSolomon.DeRham.Examples.laurentCharacteristicForm_eq_T_smul_diff) (decl := OrlikSolomon.DeRham.Examples.laurentCharacteristicForm_class_ne_zero) (decl := OrlikSolomon.DeRham.Examples.laurentCharacteristicForm_not_cohomologous_log) (decl := OrlikSolomon.DeRham.Examples.not_surjective_logToLocalization_of_charP)
If $`k` is a field of characteristic $`p>0`, the affine-line axiom fails for this model.
In $`k[z]`, the form $`z^{p-1}dz` is a nonzero cohomology class, and $`z^p` is a nonconstant cocycle of degree zero.
The pole argument fails as well: for $`f=z`, the closed form $`z^{-p-1}dz` is not exact and cannot be represented by a logarithmic form.
:::

# Where each hypothesis is used

The proofs are arranged so that each use of a hypothesis can be isolated in one lemma.

 * *A commutative base ring* suffices for the construction and functoriality of the dg algebra, the formulas for quotients and localizations, the exterior calculus and all signs at the level of forms.
 * *Formal smoothness of the ambient algebra* supplies projectivity of $`\Omega_A^1`, hence torsion-freeness with respect to $`f` of its exterior powers, and the lift of a normal functional to an $`A`-valued derivation.
 * *Formal smoothness of the divisor* supplies the section of $`A/(f^2)\to S`, hence the split conormal line and the normal functional modulo $`f`.
 * *The equation being a non-zero-divisor* identifies $`(f)/(f^2)` with $`S`, and ensures that regular forms inject into localized forms.
 * *Invertibility of positive integers* is used in the integration homotopy, in $`h_m` for every $`m\ge1`, and in the explicit regressions in characteristic zero.
 * *The base being a field of characteristic zero* guarantees those invertibilities and nonzero coefficients, with no separate geometric use.
 * *Finite presentation* is needed only to belong to the category of smooth algebras.
 * *Associated equations for a morphism of pairs* give $`\phi(f)=uf'` with $`du/u` regular in the target, hence the exact normalization of the residue and its naturality.

The blueprint also notes that the proofs work over a nonzero commutative $`\mathbb{Q}`-algebra with the same assumptions.
This is a reading of the proofs, and not a proposed change to the structure.
