# Architecture

This file records how the blueprint is realized in Lean. The blueprint is authoritative
for mathematics and this file for Lean design. Change this file in the same PR as any
design change, and say so in the PR description.

## Namespaces and layout

All declarations live under the namespace `OrlikSolomon`. Do not create a sub-namespace
called `Algebra`, `Module`, `Polynomial`, or anything else that shadows a root name that
we use: inside `namespace OrlikSolomon`, `OrlikSolomon.Algebra` would capture `Algebra`.
The blueprint's `ArrangementCohomology.Algebra.RelationQuotient` is therefore
`OrlikSolomon.RelationQuotient`.

| Module under `OrlikSolomon/`   | Blueprint labels |
| ------------------------------ | ---------------- |
| `Grading/Basic`                | `def:grading`, `lem:extraction` |
| `Algebra/RelationQuotient`     | `def:twosided`, `lem:quotient-api` |
| `Algebra/ExteriorWords`        | `lem:exterior-words`, `lem:boundary-expansion` |
| `Algebra/Exact`                | `lem:basis-ses`, `lem:comparison` |
| `Geometry/Arrangement`         | `def:arrangement`, `lem:equations`, `def:deletion`, the incidence part of `lem:restriction-geometry` |
| `Geometry/SmoothAlg`           | `def:geometry-interface` |
| `Geometry/CoordinateRing`      | coordinate rings and complements |
| `Geometry/Deletion`            | the ring part of `lem:restriction-geometry` |
| `Geometry/RelationTargets`     | `lem:small-targets` |
| `Geometry/Projective`          | `def:projective`, `lem:decone` |
| `Cohomology/Axioms`            | `def:cohomology` |
| `Cohomology/Bridge`            | `lem:standard-bridge` |
| `Cohomology/Logarithms`        | `lem:gm`, `def:log`, `lem:log-basic`, `lem:log-mul`, `lem:log-residue`, `lem:gm-product` |
| `Cohomology/Deletion`          | `lem:restriction-surj`, `lem:ses`, `thm:generation`, `thm:cohom-basis` |
| `Presentation/Basic`           | `def:os`, `lem:os-basic` |
| `Presentation/Realization`     | `lem:empty-relation`, `lem:dependent-relation`, `def:realization`, `lem:realization-basic` |
| `Presentation/Cokernel`        | `lem:representatives`, `def:lift-map`, `lem:lift-surj` |
| `Presentation/Structure`       | `lem:comparison-residue`, `thm:affine`, `cor:ordinary` |
| `Presentation/Projective`      | `lem:central-boundary`, `lem:projective-algebra`, `thm:projective` |
| `Combinatorics/Betti`          | `def:polynomials`, `lem:polynomial-recursion`, `thm:betti`, `lem:mobius`, `cor:projective-betti` |
| `Examples/Sanity`              | the blueprint's regression examples |

`lem:geometry-adapter` has no module of its own: see the next section.

## Geometry is concrete: no abstract interface

**This departs from the blueprint's module map.** The blueprint proposes a structure
`ArrangementGeometry` with many fields, later discharged by `localizationGeometry`. We
skip the indirection and state everything on one concrete category, which the blueprint
already names as the economical implementation.

- `SmoothAlg k` is the category of smooth (hence finitely presented) commutative
  `k`-algebras, a full subcategory of `CommAlgCat k`. It is `Spec`-dual to smooth affine
  `k`-schemes. Cohomology is a **covariant** functor on `SmoothAlg k`, so "pullback along
  `X → Y`" is the image of the algebra map `O(Y) → O(X)`.
- The fields of `ArrangementGeometry` become ordinary definitions and lemmas, so
  `lem:geometry-adapter` is discharged by construction across `Geometry/`.

The reasons are that the public theorem is then about actual arrangements with no
leftover hypothesis, that units replace maps to `G_m` (`logClass` takes `u : Aˣ`), and
that one family of pairs (below) covers every standard pair.

### Divisor pairs

`DivisorPair k` is the blueprint's "certified smooth-divisor pair":

- objects `ambient`, `closed` and `compl` of `SmoothAlg k`;
- maps `i : ambient ⟶ closed` and `j : ambient ⟶ compl`;
- an element `eqn` of `ambient` such that `i` is surjective with kernel `(eqn)`, `j`
  exhibits `compl` as `IsLocalization.Away eqn`, and `eqn` is a **non-zero-divisor**.

Certifying instead of using `A ⧸ (f)` and `Localization.Away f` literally lets
`O(U_𝒜')`, `O(U_𝒜'')` and `O(U_𝒜)` form a pair directly, with no transport.

**The non-zero-divisor condition is essential, not cosmetic.** For `eqn = 0` the open part
is empty and exactness would force a bijective Gysin map of shift `(2, 1)` on every smooth
algebra, which contradicts the dimension axiom.

A *transverse morphism* of pairs `P → Q` is a triple of maps commuting with `i` and `j`
such that the ambient map sends `P.eqn` to a **unit multiple** of `Q.eqn`. The unit is
what makes `lem:log-mul` work, where `z ↦ xy` pulls back to the divisor `x = 0`.

**Pairs needed:** for any smooth `A`, the pair `(A[t], A, A[t;t⁻¹], t)` serves as the
standard pair (`A = k`), the pair in `lem:log-mul` (`A = k[y;y⁻¹]`) and the pair in
`lem:gm-product`. The only other family is the deletion pair
`(O(U_𝒜'), O(U_𝒜''), O(U_𝒜), f_H)`.

### Coordinate rings and arrangements

- `V` is a finite-dimensional `k`-vector space in `Type u`, with `k : Type u`. Induction
  statements quantify over all such `V`, because restriction changes the ambient space.
- An arrangement is a `Finset (AffineSubspace k V)` of hyperplanes, with classical
  decidable equality. Generators are indexed by its subtype, and signed words use `List`.
- `O(V)` is `SymmetricAlgebra k (Module.Dual k V)`. An affine function `f` maps to
  `ι f.linear + algebraMap (f 0)`, and affine maps induce algebra maps by
  `SymmetricAlgebra.lift`. Prefer such coordinate-free arguments. For example, get
  `O(V) ⧸ (f_H) ≃ O(H)` from universal properties and a retraction `V → H` rather than
  from a basis. `SymmetricAlgebra.equivMvPolynomial` is available when coordinates are
  really needed, such as for smoothness.
- `O(U_𝒜)` is a localization of `O(V)` at the equations of the hyperplanes. **It is never
  a subset of `V`**, since a complement can have no `k`-points (blueprint §3).
- The restriction arrangement lives on `H.direction`, identified with `H` through a base
  point chosen once, inside the definition.

## Algebra

- **Bigrading:** use Mathlib's `GradedAlgebra (𝒜 : ℤ × ℤ → Submodule R T)`. Do not add a
  new class. It does not require commutativity, which matters because cohomology and the
  Orlik–Solomon algebra are only graded commutative.
- **Shifted maps:** state lemmas for a general additive group of degrees, then specialize.
- **Signs:** use `Int.negOnePow` (`ℤ → ℤˣ`) acting by scalars, so graded commutativity
  reads `x * y = (p * q).negOnePow • (y * x)`.
- **Equivalences:** use `AlgEquiv` plus a separate grading statement, not a new category
  of graded algebras.
- **Relation quotients:** `RelationQuotient ℛ` takes no ring of scalars. It is an
  `S`-algebra for every `S` over which `T` is an algebra, so one type carries both the
  `B`-algebra structure and the grading by `R`-submodules. It is the `RingCon.Quotient` of
  `TwoSidedIdeal.span ℛ`, the same shape as Mathlib's `TensorAlgebra` and `CliffordAlgebra`,
  and the congruence is not exposed to importers. Descend non-multiplicative maps with
  `liftLinear` and `mapLinear`.

## The cohomology structure

`OrdinaryTheory` (blueprint `def:cohomology`) has these features:

- Its parameters are `k`, `R`, a commutative `R`-algebra `B`, and its weight grading
  `ℬ : ℤ → Submodule R B`, with `R` identified with `ℬ 0`.
- Its total cohomology is a functor `SmoothAlg k ⥤ AlgCat B`, with each value internally
  bigraded by `R`-submodules. `AlgCat` is not commutative, as required.
- The dimension axiom says `B → C(k)` is bijective and carries `ℬ w` onto degree `(0, w)`,
  with every other degree zero.
- Affine-line invariance is stated for `A → A[t]` over every smooth `A`.
- The residue and Gysin maps of C4 and C5 exist for every `DivisorPair`, and residue
  naturality is stated for every transverse morphism.
- The boundary projection formula is stated only for `α` of degree `(1, 1)`, as the
  blueprint allows. A weaker hypothesis gives a stronger theorem.
- It has no axiom for the empty object: the pair `(A, 1)` already forces the zero ring to
  have zero cohomology.

Every field must hold in real theories, so check each one against singular cohomology when
you add it. An unsatisfiable structure would make the main theorem vacuous.
`Examples/Sanity` should contain the zero theory as a basic consistency check.

## Exposition

The Verso book in `OrlikSolomonBook/` is tied to the code at build time, while the library
itself has no dependency on Verso and no project-specific attributes:

- Each blueprint node in the book names its Lean declarations in a custom directive. The
  build **fails** if a name does not resolve or the declaration depends on `sorryAx`, so
  the text cannot drift from the code.
- Lean snippets in the text are elaborated against the library.
- A completeness check compares blueprint labels with the labels the book covers.

## Scope

In scope: the ordinary affine and projective theorems, their combinatorial corollaries,
the bridge from a standard degreewise theory, and the exposition. The stable extension
(blueprint §9, milestones 5b and 6) is **deferred** unless Adam asks for it.
