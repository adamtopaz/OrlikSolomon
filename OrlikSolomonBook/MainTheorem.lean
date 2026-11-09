/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import OrlikSolomonBook.Node
import OrlikSolomon.MainTheorem

open Verso.Genre Manual InlineLean
open OrlikSolomonBook

set_option verso.docstring.elabMarkdown false

#doc (Manual) "The main theorem" =>
%%%
tag := "main-theorem"
file := "main-theorem"
htmlSplit := .never
%%%

The public projective theorem is in one file, [OrlikSolomon/MainTheorem.lean](https://github.com/adamtopaz/OrlikSolomon/blob/main/OrlikSolomon/MainTheorem.lean).
Its definitions and theorem statements use Mathlib and earlier public declarations of that file.
The library supplies the proofs through private imports.
This chapter quotes the interface so that a reader can inspect the mathematical objects, the hypotheses and the conclusion together.
The later chapters explain the proof and its affine and de Rham forms.

There is a distinction to keep throughout.
The theorem holds for every supplied theory on any class of smooth schemes satisfying the conditions below, including the class of all smooth schemes.
The verified nonzero example is algebraic de Rham cohomology on *smooth affine schemes* over a field of characteristic zero.
The project does not construct a cohomology theory on all smooth schemes.
Singular cohomology is an intended mathematical example of the axioms in its usual setting, but no singular-cohomology instance is verified in Lean.

This is an interface to the existing results, not a fourth mathematical blueprint.
It adds no nodes to the three status counts on the first page.

# What a theory supplies

Fix a field $`k`.
The class $`\mathcal D` consists of schemes over $`\operatorname{Spec}k`; all morphisms over the base between its members are allowed.
It is closed under isomorphism, every member is smooth, every smooth affine scheme is a member, and $`X\times_k\mathbb A^1` belongs whenever $`X` does.
These are the four conditions of the following structure, shown with its fields.

{docstring OrlikSolomon.MainTheorem.SmoothSchemeClass +hideStructureConstructor}

The named choices are {name OrlikSolomon.MainTheorem.SmoothSchemeClass.allSmooth}`allSmooth` and {name OrlikSolomon.MainTheorem.SmoothSchemeClass.smoothAffine}`smoothAffine`.
The theorem is quantified over every such class.
A theory on a larger class restricts to a smaller class satisfying the same four conditions; the affine class asks the least of a theory.
The complement of a nonempty projective arrangement is affine, so it belongs to every class.

A principal smooth divisor is an actual pair of schemes: $`i:D\to X` is the closed subscheme cut out by one global function $`f`, and $`j:U\to X` is its open complement.
The function is a non-zero-divisor on *every open* of $`X`.
The divisor may be empty, and the ambient scheme may be empty or disconnected.

{docstring OrlikSolomon.MainTheorem.PrincipalSmoothDivisor +hideStructureConstructor}

A morphism of these pairs consists of three commuting maps over the base, whose ambient pullback takes one equation to a unit multiple of the other.
The closed and open subschemes are thus pulled back scheme-theoretically, rather than only as sets of rational points.

{docstring OrlikSolomon.MainTheorem.PrincipalSmoothDivisor.Hom +hideStructureConstructor}

The coefficient ring $`R` is arbitrary.
The point cohomology $`B=\bigoplus_w B_w` is a commutative $`R`-algebra graded by weight, with $`R\simeq B_0` supplied by the first field of the theory.
Neither ring is required to be nonzero, and $`2` is not required to be invertible.
The value $`C(X)` is a $`B`-algebra internally graded by $`(p,w)\in\mathbb Z^2`, with cohomological degree first.
Pullback along $`f:X\to Y` is `T.C.map f.op`.

Here is the full cohomology structure.
Its fields are the axioms C1–C5: products and gradings, the point and affine-line axioms, the long exact divisor sequence, and its naturality and projection formula.
They do not assume the structure theorem or any intermediate arrangement conclusion.
In particular, logarithmic generation, residue surjectivity and Gysin vanishing are proved later.

{docstring OrlikSolomon.MainTheorem.CohomologyTheory +hideStructureConstructor}

The sign rule is $`xy=(-1)^{pq}yx` for classes of cohomological degrees $`p,q`.
The Gysin and residue shifts are $`(2,1)` and $`(-1,-1)`.
The three exactness fields form a long exact sequence; a short exact deletion sequence is an output of the proof.
The projection formula assumes that its left factor has bidegree $`(1,1)`, as in C5.

# The actual projective complement

Projective space is Mathlib's $`\operatorname{Proj}k[x_0,\ldots,x_n]` with its grading by total degree, viewed over $`\operatorname{Spec}k`.
The following checked equation displays its definition, including the structure map to the base.
An equation proved by `rfl` checks that the displayed expression is the public definition, up to definitional equality.

```lean -show
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.MainTheorem
open scoped Polynomial LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u v w z
variable {k : Type u} [Field k] {n : ℕ}
```

```lean
example : projectiveSpace k n =
    Over.mk (Proj.toSpecZero (degreeGrading k n) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap k (degreeGrading k n 0)))) := rfl
```

A hyperplane is a subset of the *scheme points* of this projective space, with a nonzero homogeneous linear equation.
It is not a subset of the finite set of rational points when $`k` is finite.
The equation predicate is explicit:

{docstring OrlikSolomon.MainTheorem.IsEquation +hideStructureConstructor}

{docstring OrlikSolomon.MainTheorem.Hyperplane}

{docstring OrlikSolomon.MainTheorem.HyperplaneArrangement}

The hyperplanes form a finite set, so repeated equations cannot add repeated hyperplanes to the arrangement.
Equations of one hyperplane differ by a unique nonzero scalar, including when $`n=0`.
A list of hyperplanes is dependent when some choice of its equations is linearly dependent; then every choice is.
This is {name OrlikSolomon.MainTheorem.IsDependent}`IsDependent`.

The complement is literally the open subscheme on $`\mathbb P^n_k\setminus\bigcup_{H\in\mathcal A}H`, with its inherited map to the base.
The public definitions specify its open set and its scheme:

{docstring OrlikSolomon.MainTheorem.complementOpens}

```lean
example (𝒜 : HyperplaneArrangement k n) :
    complement 𝒜 =
      Over.mk ((complementOpens 𝒜).ι ≫ (projectiveSpace k n).hom) := rfl
```

For a nonempty arrangement this complement is affine and smooth.
Consequently {name OrlikSolomon.MainTheorem.complementObj}`complementObj` puts it in any class $`\mathcal D`.

{docstring OrlikSolomon.MainTheorem.complement_isAffine_smooth}

The projective dimension may be zero: $`\mathbb P^0` is a point, its unique hyperplane is the empty subset $`V_+(x_0)`, and the complement of that nonempty arrangement is the point.
Over finite fields a complement may have no rational points; it is still the actual open scheme.
The empty *arrangement* is excluded from the main theorem, since its complement is all of projective space and the axioms do not include a projective bundle formula.

# The algebra in the statement

Let $`e_H` be the exterior generator indexed by a hyperplane.
For an ordered list $`S=(H_0,\ldots,H_{s-1})`, its word is $`e_S=e_{H_0}\cdots e_{H_{s-1}}`, with signed boundary
$$`\partial e_S=\sum_{j=0}^{s-1}(-1)^j e_{H_0}\cdots\widehat{e_{H_j}}\cdots e_{H_{s-1}}.`
The affine central-cone Orlik–Solomon algebra is the quotient by these boundaries for dependent lists without repetitions.
All cone intersections contain the origin, so there is no empty-intersection relation in this presentation.
The exterior algebra enforces square-zero generators even in characteristic two.

{docstring OrlikSolomon.MainTheorem.exteriorWordBoundary}

{docstring OrlikSolomon.MainTheorem.orlikSolomonRel}

```lean
example (B : Type w) [CommRing B] (𝒜 : HyperplaneArrangement k n) :
    OrlikSolomonAlgebra B 𝒜 = RingQuot (orlikSolomonRel B 𝒜) := rfl
```

The projective algebra is the subalgebra generated by *all* differences $`e_H-e_K`.
There is no chosen hyperplane at infinity in this definition.

```lean
example (B : Type w) [CommRing B] (𝒜 : HyperplaneArrangement k n) :
    projectiveOrlikSolomonAlgebra B 𝒜 =
      Algebra.adjoin B
        (Set.range fun HK : 𝒜 × 𝒜 ↦
          generator B 𝒜 HK.1 - generator B 𝒜 HK.2) := rfl
```

Give each $`e_H` bidegree $`(1,1)` and $`b\in B_a` bidegree $`(0,a)`.
The piece $`(p,w)` is the $`R`-span of $`b e_S` with $`|S|=p` and $`b\in B_{w-p}`; for $`p<0` this span is zero.
The projective pieces are the preimages of these spans under its inclusion.
These are the precise submodules used in the theorem:

{docstring OrlikSolomon.MainTheorem.orlikSolomonGrading}

{docstring OrlikSolomon.MainTheorem.projectiveOrlikSolomonGrading}

# The class and the map are characterized

The standard divisor is $`\{0\}\subset\mathbb A^1`, with complement $`\mathbb G_m=\operatorname{Spec}k[T,T^{-1}]` and equation $`X`.
Its closed map is induced by evaluation $`X\mapsto0`; its open map by $`X\mapsto T`.

{docstring OrlikSolomon.MainTheorem.standardDivisor}

The fundamental class $`\tau` is characterized by bidegree $`(1,1)` and residue $`1` at this divisor.
There exists exactly one such class for every supplied theory.

{docstring OrlikSolomon.MainTheorem.CohomologyTheory.IsFundamentalClass}

{docstring OrlikSolomon.MainTheorem.existsUnique_fundamentalClass}

If $`\ell,\ell'` are equations of two members of the arrangement, the function $`\ell/\ell'` on the complement is the restriction of a degree-zero homogeneous fraction from the chart $`D_+(\ell')`.
The public {name OrlikSolomon.MainTheorem.ratio}`ratio` definition also allows any homogeneous linear numerator, including zero; the assertions about units and maps to $`\mathbb G_m` require both forms to be equations.

{docstring OrlikSolomon.MainTheorem.ratio}

There is exactly one map $`g:U_{\mathcal A}\to\mathbb G_m` pulling the coordinate $`T` back to this ratio.
This characterizes the map as a morphism over $`\operatorname{Spec}k`, with no choice of a rational point.

{docstring OrlikSolomon.MainTheorem.existsUnique_hom_ratio}

# The theorem

For every supplied theory and every nonempty arrangement there is an isomorphism of $`B`-algebras
$$`\Phi:\overline{\operatorname{OS}}_B(\mathcal A)\xrightarrow{\sim}C(U_{\mathcal A})`
with two properties.
For every choice of equations, the unique fundamental class $`\tau` and the unique map $`g` just described, it sends $`e_H-e_K` to $`g^*\tau`.
It sends the piece of every bidegree $`(p,w)` *onto* the corresponding cohomology piece, for all integers $`p,w`.
The set-image equality in the Lean statement asserts this onto property, rather than only preservation of degrees.

{docstring OrlikSolomon.MainTheorem.orlikSolomon}

The generator formula determines the algebra map, since the source is generated by these differences.
Its assertion for every equation makes the resulting map independent of the equations.
The preceding existence and uniqueness results ensure that the classes and morphisms appearing in this characterization exist.
The hypothesis that a cohomology theory has been supplied remains a mathematical hypothesis.

# A verified nonzero example

Over a field of characteristic zero, the library constructs a theory on the class of smooth affine schemes.
Its coefficients are $`k[T,T^{-1}]`, and its values are the weight-twisted algebraic de Rham cohomology of the schemes.
The coefficient ring is nonzero, and the point axiom identifies it with the cohomology of $`\operatorname{Spec}k`.
Thus this is a nonzero model of the axioms.

{docstring OrlikSolomon.MainTheorem.nonempty_cohomologyTheory}

The class in this statement is `smoothAffine k`, not `allSmooth k`.
It does not construct de Rham cohomology of arbitrary non-affine schemes or identify underived global forms with their hypercohomology.
The unconditional de Rham isomorphisms, with generators represented by $`df/f`, are explained in {ref "de-rham"}[the de Rham chapter] and {ref "geometric"}[the chapter on schemes].

# How to audit this file

Read the public definitions of Part I and the public statements of Part II.
Check that the scheme, divisor and algebra definitions describe the intended mathematical objects, that the fields ask only for C1–C5, and that the theorem has the claimed generator formula and onto pieces.
These mathematical judgements require reading; the automated audit checks where the formal types and data come from.

The physical order of the file is Part I (public definitions), a private proof region with clear opening and closing markers telling readers to skip it, Part II (public statements), then the axiom reports.
The proof region is `OrlikSolomon.MainTheorem.Proof` and comes before Part II because Lean checks declarations in dependency order and does not allow forward references.
The public statements use that region for their proofs.
This placement does not change which definitions and statements constitute the interface.
The library imports are private: an exposed public type or data definition cannot refer to them, while a proof may use library theorems.
The interface audit independently inspects the compiled types and data definitions and follows references to other declarations of this file.
The types of theorem declarations are checked; their proof terms may use the library.

After building, the following commands run the interface audit on its own and then the complete library checks:

```text
lake exe audit --interface
scripts/check.sh
scripts/replay.sh
```

The file ends with `#print axioms` on each of the five public theorems.
The output below is checked when this chapter is built.
Only `propext`, `Classical.choice` and `Quot.sound` occur; the cohomology theory is an explicit argument to the conditional theorems, rather than a hidden logical axiom.

```lean (name := interfaceAxioms)
#print axioms OrlikSolomon.MainTheorem.complement_isAffine_smooth
#print axioms OrlikSolomon.MainTheorem.existsUnique_fundamentalClass
#print axioms OrlikSolomon.MainTheorem.existsUnique_hom_ratio
#print axioms OrlikSolomon.MainTheorem.orlikSolomon
#print axioms OrlikSolomon.MainTheorem.nonempty_cohomologyTheory
```
```leanOutput interfaceAxioms
'OrlikSolomon.MainTheorem.complement_isAffine_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrlikSolomon.MainTheorem.existsUnique_fundamentalClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrlikSolomon.MainTheorem.existsUnique_hom_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrlikSolomon.MainTheorem.orlikSolomon' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrlikSolomon.MainTheorem.nonempty_cohomologyTheory' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Neither an axiom list nor a provenance check proves that the chosen formal statement is the intended mathematics.
That is why the interface is written out with Mathlib objects and why the surrounding prose is reviewed separately from the kernel's checks.
