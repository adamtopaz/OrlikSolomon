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
| `Geometry/Hyperplane`          | hyperplanes and equations of `def:arrangement`, `lem:equations` |
| `Geometry/Chart`               | identifying `H` with `H.direction` in `def:deletion`, the incidence part of `lem:restriction-geometry` for one hyperplane |
| `Geometry/Arrangement`         | `def:arrangement`, `def:deletion`, the incidence part of `lem:restriction-geometry` for arrangements |
| `Geometry/SmoothAlg`           | `def:geometry-interface` |
| `Geometry/CoordinateRing`      | coordinate rings of vector spaces, part of `lem:geometry-adapter` |
| `Geometry/Complement`          | coordinate rings of arrangement complements, part of `lem:geometry-adapter` |
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

**Objects are `def`s.** An object of `SmoothAlg k` that lemmas will mention should be a `def`
built from `SmoothAlg.of`, as `point`, `polynomial` and `laurent` are, and not an `abbrev`.
`simp` indexes the source and target of a coerced morphism, and a reducible object produces keys
that differ between when a lemma is added and when a goal is matched, so a lemma about such a
coercion silently never fires. See the implementation notes in `Geometry/SmoothAlg`.

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
  `Arrangement.ComplementRing` inverts all equations of all hyperplanes rather than a chosen
  product, so its definition involves no choice. `ComplementRing.isLocalizationAway` gives
  `O(V)[1/P]` for any product `P` of equations, one for each hyperplane, and
  `ComplementRing.isLocalization_of_exists_dvd` recognizes the ring as a localization at any other
  submonoid with the same saturation. The object of `SmoothAlg k` is `SmoothAlg.complement 𝒜`.
- `𝒜.Covers L` says that `L` is empty or a hyperplane of `𝒜`. An affine function whose zero locus
  is covered is a unit on `U_𝒜`, namely `SmoothAlg.complementUnit`. An affine map `φ` induces
  `O(U_𝒜) ⟶ O(U_ℬ)` when `ℬ` covers the preimage of every hyperplane of `𝒜`, by
  `SmoothAlg.complementMap`.
- Maps that are not affine are built on the ring level with `CoordinateRing.fraction`, which is
  `v ↦ G v / u` for an affine `G` and a unit `u`, with `liftChart` to land in an affine subspace and
  `ComplementRing.lift` to pass to a complement, and are then wrapped with `SmoothAlg.ofHom`.
- The restriction arrangement lives on `H.direction`, identified with `H` through a base
  point chosen once, inside the definition. That definition is `chart H : H.direction →ᵃ[k] V`,
  which is `@[no_expose]`. Move subspaces with `K.comap (chart H)` and `M.map (chart H)`, and
  state results through `map_chart_comap_chart`, whose value is `H ⊓ K`, rather than through the
  base point. `chart H 0` still names that point, but nothing says which one it is, so a condition
  such as `0 ∈ L` for `L` in a restriction cannot be decided and must not define "central".
- Intersections are lattice operations on `AffineSubspace k V`, and "empty" is `⊥`:
  `⨅ i, H i` for families, `sInf S` for sets, and `Arrangement.inter I` for a list `I : List 𝒜`.
  `codim X` is the dimension of `V ⧸ X.direction`, and `Module.finrank k X.direction` is the
  dimension of `X`. Both are natural numbers, as exponents require, and they are meaningful only
  for `X ≠ ⊥`, so test for emptiness first: `codim_bot` gives `codim ⊥ = finrank k V`. Mathlib's
  `AffineSubspace.finDim : WithBot ℕ` is the same dimension with `⊥` as its value on `⊥`
  (`AffineSubspace.finDim_eq_finrank`, `AffineSubspace.finDim_bot`).
- `Arrangement.comap φ 𝒜` is the pullback along any affine map, keeping the preimages that are
  hyperplanes, and `𝒜.restriction H` is `𝒜.comap (chart H)`. It is a total function of `H`, with
  `Arrangement.mem_restriction` giving the blueprint's description when `H` is a hyperplane, and
  `H` need not belong to `𝒜`, which covers the slice in deconing.
- Induct over all `V` with `Arrangement.induction`, or by strong induction on `Arrangement.card`
  using `Arrangement.card_deletion_lt` and `Arrangement.card_restriction_lt`.

## Algebra

- **Bigrading:** use Mathlib's `GradedAlgebra (𝒜 : ℤ × ℤ → Submodule R T)`. Do not add a
  new class. It does not require commutativity, which matters because cohomology and the
  Orlik–Solomon algebra are only graded commutative.
- **Graded modules:** use `DirectSum.Decomposition ℳ` where only the module structure
  matters. Some graded objects, such as the cokernel in `def:lift-map`, are not algebras.
- **Shifted maps:** `IsHomogeneousOfShift ℳ 𝒩 a f` says that `f` sends `ℳ i` into
  `𝒩 (i + a)`. It is a predicate on plain functions, like `Function.Exact`, because the
  grading pieces are `R`-submodules while the maps are `B`-linear. State lemmas for a
  general additive group of degrees, then specialize. Name a target degree by an equation
  `i + a = j` rather than computing `j - a`, which avoids transport at literal bidegrees.
- **Signs:** use `Int.negOnePow` (`ℤ → ℤˣ`) acting by scalars, so graded commutativity
  reads `x * y = (p * q).negOnePow • (y * x)`. This is `IsGradedCommutative 𝒜 Prod.fst`.
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
  build **fails** if a name does not resolve or the declaration depends on `sorryAx`, or on
  any axiom other than `propext`, `Classical.choice` and `Quot.sound`, so the text cannot
  drift from the code.
- Lean snippets in the text are elaborated against the library.
- A completeness check compares blueprint labels with the labels the book covers.

**This is the whole of what the build checks about a node.** It does not check that the named
declarations cover the node's statement, and it would accept any proved declaration on any box. It
does not check prose, inside or outside the boxes. Both are the responsibility of review: a reviewer
of a change that names declarations must read them against the statement. The book tells its
readers this on its first page and its status page.

A node is presented like this, with its label as the first argument:

```
:::node "lem:gm" (decl := OrlikSolomon.gmDecomposition)
Prose about the lemma.
:::
```

- With no `decl`, the node renders as **planned**. With `+deferred`, it renders as
  **deferred**, for what "Scope" below leaves out. Naming declarations is the only way to
  make a node render as formalized.
- If the declarations cover only part of a node, say so with `(remaining := "...")`, and it
  renders as partly formalized. A node split across modules should use this until it is
  finished.
- The role `{bp "lem:gm"}[text]` links to a node and shows its status, so that a reference
  in the prose cannot claim more than the node's own box. Empty text shows the node's name.
- `{statusSummary}` and `{statusOverview}` are generated from what the directives recorded.

Nodes are the theorem-like environments of `blueprint/*.tex` with their `\label`s, so section
labels are not nodes. The parser rejects a `\label` that is on neither such an environment
nor a section, and a theorem-like environment with no `\label`, so that a node cannot drop out
of the check unnoticed. A label used twice is rejected too, including across files, since a
copied label would otherwise add a node with no new coverage obligation. If a blueprint starts
using, say, labelled equations, extend the parser in `OrlikSolomonBook/Blueprint.lean`.

Some choices here are deliberate:

- **Book files are not Lean `module`s**, unlike the library. A plain `import` loads the
  private level of the library's data. Under `module`, a batch build does not see declaration
  ranges or docstrings, which the book renders. Axiom checks work either way, and a proof that
  changes to `sorry` rebuilds the book across module boundaries, with no statement changing.
  A chapter should import `OrlikSolomon` rather than Mathlib directly, because a plain import
  of Mathlib produces a warning.
- **The executable links the library natively, and with it Mathlib's closure.** This is the
  standard Verso setup, and the alternative of loading the chapters at run time needs
  `unsafe`. With a closure of 2542 modules, compiling the objects took 25 core-minutes and
  the binary was 149 MB. The objects are shared between worktrees and cached by the `Book`
  workflow. Use `lake build OrlikSolomonBook` to check the book without linking.
- **`lake exe book` has checks of its own**: unresolved cross-references and the completeness
  check, which reads the blueprint afresh. `scripts/check-book-output.mjs` then checks the
  generated pages. Verso renders formulas with `throwOnError: false`, so without this script a
  bad formula would only appear as red text on the site.

The `Book` workflow runs all of this on pull requests and deploys `main` to
<https://adamtopaz.github.io/OrlikSolomon/>. Links to the source use the commit that
`git rev-parse HEAD` reports when the book is rendered.

## Scope

In scope: the ordinary affine and projective theorems, their combinatorial corollaries,
the bridge from a standard degreewise theory, and the exposition. The stable extension
(blueprint §9, milestones 5b and 6) is **deferred** unless Adam asks for it.
