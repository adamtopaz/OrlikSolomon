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
| `Grading/Diagonal`             | the diagonal `⨁ 𝒜 (q, q)` of a bigrading, and homogeneous bases, for `cor:ordinary` and `thm:betti` |
| `Grading/DirectSum`            | external direct sums in `lem:standard-bridge` |
| `Grading/LinearImage`          | image decompositions for homogeneous module quotients |
| `Grading/Restriction`          | inherited internal gradings on homogeneous submodules and subalgebras |
| `Grading/TensorProduct`        | product gradings, transport and the weighted tensor grading of `lem:os-basic` |
| `Algebra/RelationQuotient`     | `def:twosided`, `lem:quotient-api` |
| `Algebra/ExteriorWords`        | `lem:exterior-words`, `lem:boundary-expansion` |
| `Algebra/ExteriorBoundary`     | the exterior-algebra operator and signed Leibniz rule of `lem:central-boundary` |
| `Algebra/Exact`                | `lem:basis-ses`, `lem:comparison` |
| `Algebra/SymmetricGrading`     | the degree grading of `O(W)`, used by `def:projective` |
| `Geometry/Hyperplane`          | hyperplanes and equations of `def:arrangement`, `lem:equations` |
| `Geometry/Chart`               | identifying `H` with `H.direction` in `def:deletion`, the incidence part of `lem:restriction-geometry` for one hyperplane |
| `Geometry/Arrangement`         | `def:arrangement`, `def:deletion`, the incidence part of `lem:restriction-geometry` for arrangements, the central arrangements of `lem:central-boundary` |
| `Geometry/SmoothAlg`           | `def:geometry-interface` |
| `Geometry/CoordinateRing`      | coordinate rings of vector spaces, part of `lem:geometry-adapter` |
| `Geometry/Complement`          | coordinate rings of arrangement complements, part of `lem:geometry-adapter` |
| `Geometry/Deletion`            | the ring part of `lem:restriction-geometry`, the deletion pairs of `lem:geometry-adapter` |
| `Geometry/RelationTargets`     | `lem:small-targets` |
| `Geometry/ProjectiveArrangement` | `def:projective`, the incidence part of `lem:decone` |
| `Geometry/ProjectiveRing`      | the ring `O(U_P)` of `def:projective` |
| `Geometry/Projective`          | `lem:decone`, the objects of `SmoothAlg k` and the cone and decone part of `lem:geometry-adapter` |
| `Geometry/ProjectiveScheme`    | `O(U_P)` as the complement in Mathlib's `Proj` |
| `Cohomology/Axioms`            | `def:cohomology` |
| `Cohomology/BridgeData/Basic`   | degreewise products, coefficients and pullbacks for `lem:standard-bridge` |
| `Cohomology/BridgeData/Supports` | degreewise localization with supports and oriented purity for `lem:standard-bridge` |
| `Cohomology/DeletionPair`      | `lem:log-residue` for deletion pairs, and the residue and Gysin maps of a deletion, typed |
| `Cohomology/Bridge`            | `lem:standard-bridge` |
| `Cohomology/Logarithms`        | `lem:gm`, `def:log`, `lem:log-basic`, `lem:log-mul`, `lem:log-residue`, `lem:gm-product` |
| `Cohomology/Deletion`          | `lem:restriction-surj`, `lem:ses`, `thm:generation`, `thm:cohom-basis`, the count of basis words in `thm:betti`, the last sentence of C3 in `def:cohomology` |
| `Presentation/Basic`           | `def:os`, the ordinary grading and deletion map of `lem:os-basic` |
| `Presentation/BaseChange`      | coefficient base change in `lem:os-basic` |
| `Presentation/Generators`      | degree-one generator independence in the blueprint's proof of `cor:projective-betti` |
| `Presentation/Grading`         | the weighted bigrading and component formula in `lem:os-basic` |
| `Presentation/Boundary`        | the descended central boundary of `lem:central-boundary` |
| `Presentation/ProjectiveAlgebra` | the graded kernel, difference generators and shifted module decomposition of `lem:projective-algebra` |
| `Presentation/Realization`     | `lem:empty-relation`, `lem:dependent-relation`, `def:realization`, `lem:realization-basic` |
| `Presentation/RepresentativeRelations` | the representative identities of `lem:representatives` |
| `Presentation/CokernelData/Basic` | the module quotient and full-context linear descent in `def:lift-map` |
| `Presentation/CokernelData/Words` | same-trace replacement and empty-trace vanishing in old word contexts |
| `Presentation/Cokernel`        | the choice-independent map of `def:lift-map` and `lem:lift-surj` |
| `Presentation/CokernelGrading` | the quotient decomposition and shift `(1,1)` in `def:lift-map` |
| `Presentation/Structure`       | `lem:comparison-residue`, `thm:affine` |
| `Presentation/Ordinary`        | `cor:ordinary`, and the direct sums and diagonal basis in `thm:betti` |
| `Presentation/Projective`      | the total bigraded equivalence of `thm:projective` |
| `Presentation/ProjectiveGrading` | ordinary degree and coefficient extension on the projective kernel |
| `Presentation/ProjectiveOrdinary` | the diagonal equivalence of `thm:projective` |
| `Combinatorics/AlternatingSum` | duplicate-fiber and empty-trace cancellation in `lem:polynomial-recursion` |
| `Combinatorics/Betti`          | `def:polynomials`, `lem:polynomial-recursion`, `lem:mobius` |
| `Combinatorics/ProjectiveBetti` | pure cone/decone intersection sums and polynomials of `cor:projective-betti` |
| `Combinatorics/Multiplicities` | cohomological pieces and decone word counts of `cor:projective-betti` |
| `Examples/AffineLines`        | concurrent lines and the triangle, including the nonempty-intersection guard |
| `Examples/Bridge`             | zero degreewise inputs, the standard bridge and same-ring components |
| `Examples/CoordinatePolynomials` | the coordinate-arrangement polynomial regression |
| `Examples/Cokernel`            | a nonzero singleton cokernel, empty and duplicate traces, characteristic two and zero coefficients |
| `Examples/Degenerate`        | coefficient cohomology of empty complements and nonunique zero-ring basis sizes |
| `Examples/Exterior`          | full exterior algebras for singletons and coordinate arrangements |
| `Examples/Ordinary`            | the structure theorem at `R = ℤ`, `ZMod 2`, two points over `F₂`, dimension zero, zero coefficients and `R = B` |
| `Examples/Polynomials`         | polynomial regression examples |
| `Examples/Sanity`              | the blueprint's regression examples |
| `Examples/Presentation`        | two points of the affine line, the affine boundary guard, characteristic two and degenerate coefficients |
| `Examples/Parallel`            | two parallel affine lines: product zero, generator difference nonzero and polynomial `1 + 2 X` |
| `Examples/ProjectiveAlgebra`   | central boundary and kernel regressions, including the obstruction for noncentral arrangements |
| `Examples/ProjectiveOrdinary` | single-hyperplane cohomology, points of the projective line and diagonal consumers |
| `Examples/Realization`         | the realization map on two points over `F₂`, three concurrent lines, dimension zero, zero coefficients and `R = B` |

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

**The non-zero-divisor condition is essential, not cosmetic.** If `eqn = 0` were allowed on
a nonzero ambient ring, the open part would be empty and exactness would force a bijective
Gysin map of shift `(2, 1)` on that ring. For the ambient ring `k` this contradicts the
dimension axiom of a **nonzero** theory. It does not contradict the zero theory, and `0` is a
non-zero-divisor of the zero ring, which stays allowed. No stronger condition is needed: units
are allowed (the empty divisor `emptyDivisor`, cut out by `1`), and so is the zero ambient ring.

A *transverse morphism* of pairs `P → Q` is a triple of maps commuting with `i` and `j`
such that the ambient map sends `P.eqn` to a **unit multiple** of `Q.eqn`. The unit is
what makes `lem:log-mul` work, where `z ↦ xy` pulls back to the divisor `x = 0`.

**Pairs needed:** for any smooth `A`, the pair `(A[t], A, A[t;t⁻¹], t)` serves as the
standard pair (`A = k`), the pair in `lem:log-mul` (any `A` with a unit `y`, the blueprint's
universal case being `A = k[y;y⁻¹]`) and the pair in `lem:gm-product`. The only other family is the
deletion pair `(O(U_𝒜'), O(U_𝒜''), O(U_𝒜), f_H)`.

**Objects and pairs are `def`s.** An object of `SmoothAlg k` that lemmas will mention should be a
`def` built from `SmoothAlg.of`, as `point`, `polynomial` and `laurent` are, and not an `abbrev`.
`simp` indexes the source and target of a coerced morphism, and a reducible object produces keys
that differ between when a lemma is added and when a goal is matched, so a lemma about such a
coercion silently never fires. See the implementation notes in `Geometry/SmoothAlg`.

The same holds for pairs: `standardPair` and the deletion pair stay `def`s. With
`abbrev standardPair` the library still builds, but a `simp` lemma about the residue of a standard
pair silently never fires. The friction this leaves is that `(standardPair A).closed` is `A` only
at default transparency, so `rw` and `simp` cannot work under `T.residue (standardPair A)`. Handle
it with **typed wrappers**, not with `change`: `T.stdResidue A : C (laurent A) →ₗ[B] C A` and
`T.stdGysin A : C A →ₗ[B] C (polynomial A)`, with lemmas stated about them. A new family of pairs
used this way needs its own wrappers.

**The deletion pair** is `DivisorPair.deletionPair 𝒜 hH hf`, for `hH : H ∈ 𝒜` and any equation
`hf : IsEquation f H`. Only its `eqn` depends on `f`. Use the typed names of its parts:
`complementRestriction 𝒜 hH'` for `i`, where `hH' : IsHyperplane H`,
`complementInclusion (𝒜.deletion_le H)` for `j`, and `complementUnit 𝒜 f (hf.covers hH)` for
`eqnUnit`. Its wrappers are `T.deletionResidue hH` and `T.deletionGysin hH`, in the module
`Cohomology/DeletionPair`, since `Geometry` does not import `Cohomology`. They take **no equation**:
by `residue_deletionPair` and `gysin_deletionPair` they are the maps of the pair of every equation,
which is naturality along `deletionPairHom`, the transverse morphism that is the identity on all
three rings. State results for every equation of `H`.

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
  `SmoothAlg.complementMap`. An affine equivalence that identifies the hyperplanes of `𝒜` and `ℬ` by
  pullback gives the isomorphism `SmoothAlg.complementIso`.
- Maps that are not affine are built on the ring level with `CoordinateRing.fraction`, which is
  `v ↦ G v / u` for an affine `G` and a unit `u`, with `liftChart` to land in an affine subspace and
  `ComplementRing.lift` to pass to a complement, and are then wrapped with `SmoothAlg.ofHom`.
- The restriction arrangement lives on `H.direction`, identified with `H` through a base
  point chosen once, inside the definition. That definition is `chart H : H.direction →ᵃ[k] V`,
  which is `@[no_expose]`. Move subspaces with `K.comap (chart H)` and `M.map (chart H)`, and
  state results through `map_chart_comap_chart`, whose value is `H ⊓ K`, rather than through the
  base point. `chart H 0` still names that point, but nothing says which one it is, so a condition
  such as `0 ∈ L` for `L` in a restriction cannot be decided and must not define "central".
- "Central" is `Arrangement.IsCentral`: the hyperplanes have a common point. It does not mention the
  origin, so it applies to restrictions. `IsCentral.inter_ne_bot` says that all intersections are
  nonempty. It is in `Geometry/Arrangement`, so the presentation does not depend on projective
  geometry, and the cone is central by `ProjectiveArrangement.cone_isCentral`.
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

### Projective arrangements and their complements

- `P : ProjectiveArrangement k W` is a `Finset (Submodule k W)` of coatoms. The symbol `𝒫` is
  Mathlib's notation for the power set, so the code writes `P`.
- An equation is a linear form: `LinearMap.ker ℓ ∈ P` says that `ℓ` is an equation of a hyperplane
  of `P`, and it implies `ℓ ≠ 0`. `P.cone` is the central cone, an `Arrangement k W`.
  `P.decone ℓ₀` is `P.cone.restriction (slice ℓ₀)`, where `slice ℓ₀` is `ℓ₀ = 1`, on the vector
  space `(slice ℓ₀).direction`. It is indexed by `ℓ₀` and not by `H₀`, since the slice depends on
  `ℓ₀`.
- `O(U_P)` is `P.ComplementRing`, Mathlib's
  `HomogeneousLocalization (symmetricGrading k (Dual k W)) P.cone.equationSubmonoid`. It is the
  degree-zero part of `O(V_P)`, so it involves no hyperplane at infinity and no choice of equations.
  The comparison with the complement in `P^n` is a theorem: `complementOpenIso` identifies `Spec` of
  this ring with the open subscheme of `Proj Sym(W*)` of the points on no hyperplane of `P`, and
  `projIsoMvPolynomial` identifies `Proj Sym(W*)` with `Proj k[x_i]` in a basis of `W*`.
- Do not replace it by the subalgebra generated by the ratios `ℓ_i / ℓ_j` of equations. That is
  wrong unless the equations span the dual of `W`: for one hyperplane in dimension at least two, it
  is `k`, whereas the complement is an affine space (`ratio_notMem_adjoin_ratioUnit`). With all
  linear forms as numerators it is right (`range_toCone_eq_adjoin`).
- `P` empty is excluded by `[Nonempty P]` on the object `SmoothAlg.projectiveComplement P`. A
  statement that uses a hyperplane at infinity takes `hℓ₀ : LinearMap.ker ℓ₀ ∈ P` instead. For empty
  `P` the ring is `k` and it is not used, because it does not correspond to the complement, all of
  `Proj Sym(W*)`, in general. For `W` of dimension at least two, `k` is the ring of global functions
  of a projective space that is not affine. For dimension one, the complement is the point `P⁰`,
  whose ring is `k`. For `W = 0`, `Proj Sym(W*)` is empty, so its ring is zero and not `k`.
- Consumers use `SmoothAlg.coneIso`, `SmoothAlg.deconeIso` and `SmoothAlg.projectiveRatioUnit`. The
  formula `ℓ_i = t (ℓ_i / ℓ_0)` is `mapUnits_coneIso_hom_complementUnit`.
- `Geometry/ProjectiveScheme` is the only module that imports Mathlib's schemes. It adds about 250
  Mathlib modules to the closure of the root and of the book, about 11%. It is a leaf: nothing else
  in the library may import it, so the proof of the structure theorem stays free of schemes.

### Projective structure maps

`OrdinaryTheory.projectiveEquiv P` identifies the boundary kernel over `B` with the total
cohomology of `projectiveComplement P`. It is the unique descent of affine realization on the
cone along the injective map `projectiveToCone`; no hyperplane or equation is a parameter.
`projectiveEquiv_eq_map_section` computes it using every hyperplane at infinity, and
`projectiveEquiv_difference` and `logClass_projectiveRatioUnit_eq_of_ker_eq` give the ratio formula
for arbitrary equations and its equation independence. `projectiveComponentEquiv` restricts the
bigrading-preserving equivalence to actual `R`-submodule pieces.

`OSAlgebra.projectiveDegree` is the inherited ordinary grading on the boundary kernel, and
`projectiveCoefficientMap` extends coefficients there. `OrdinaryTheory.projectiveDegreeEquiv`
identifies degree `q` over `R` with `H^{q,q}`; `projectiveDiagonalEquiv` assembles these into the
canonical graded `R`-algebra equivalence with the external diagonal direct sum. Surjectivity is
proved on the cone using the affine degree equivalence and the injectivity of coefficient
extension to detect a zero boundary; no flatness assumption is introduced. The integer scalar
conversions documented for `Presentation/Ordinary` apply here as well.

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
  `liftLinear` and `mapLinear`. Each semireducible `def` type wrapper needs its own `SMul`
  transport, declared before its `Ring` instance, to preserve the scalar-action coherence
  needed by canonical integer-coefficient base change.
- **Affine presentation:** `OSAlgebra B 𝒜` has square-zero generators indexed by `𝒜`.
  `Arrangement.IsDependent` includes the nonempty-intersection guard. Use the quotient,
  generator, word and lift APIs instead of the underlying exterior quotient. `degree B 𝒜`
  is the ordinary grading by `B`-submodules. For a weight grading `ℬ` of `B` over `R`,
  `OSAlgebra.bigrading 𝒜 ℬ` has `R`-submodule pieces. It transports the weighted tensor
  grading along `OSAlgebra.baseChangeEquiv R B 𝒜`; `bigradingComponentEquiv` gives exterior
  degree `n` over `R` tensored with coefficient weight `w - n`. No flatness is assumed.
- **Realization:** `T.realization 𝒜 : OSAlgebra B 𝒜 →ₐ[B] T.C.obj (complement 𝒜)` is `@[no_expose]`.
  Its `simp` lemma on generators uses the chosen equations, and `realization_generator_of_isEquation`
  gives any other. The label of a generator is its hyperplane, so relabeling is an equality of
  arrangements or, in general, a bijection of hyperplanes by pullback along an affine equivalence,
  which is what `OSAlgebra.comapEquiv` and `SmoothAlg.complementIso` take.
- **Central boundary and projective algebra:** `Arrangement.IsCentral` means that the hyperplanes
  have a common point; it does not depend on an origin chosen for a chart. The contraction-backed
  `exteriorBoundary` and its sign lemmas live in `Algebra/ExteriorBoundary`, which imports
  `Algebra/ExteriorWords`. On a central arrangement it descends to the `B`-linear
  `OSAlgebra.boundary`, with weighted shift `(-1, -1)`. Its kernel is the graded `B`-subalgebra
  `projectiveAlgebra`. Choosing a hyperplane gives `projectiveDecomposition`, a module equivalence
  from two copies of the kernel, with the second copy shifted by `(1, 1)`. This is a module
  decomposition; no ordinary ungraded tensor-product algebra decomposition is asserted.
- **Deletion cokernel:** `OSAlgebra.DeletionCokernel B 𝒜 H` is the quotient of the
  `B`-module `OSAlgebra B 𝒜` by `deletionRange B 𝒜 H`, with quotient map `cokernelMk`.
  It carries module structures over coefficient scalar rings, but no quotient-algebra
  structure. `restrictionToCokernelOfRepresentatives` uses `liftLinear` after proving
  vanishing on every full relation context; `restrictionToCokernel` is its canonical,
  choice-independent version. Surjectivity uses word spanning, without a basis theorem.
  The image pieces `cokernelGrading` form a `DirectSum.Decomposition`, and the restriction
  map has shift `(1,1)`. The files under `CokernelData/` separate quotient and word
  plumbing from the public construction. The range and quotient are reducible abbreviations,
  so the linear lift composes directly with the generic `cokernelComparison` API.
- **The structure theorem:** `T.affineEquiv 𝒜 : OSAlgebra B 𝒜 ≃ₐ[B] T.C.obj (complement 𝒜)` is the
  total-ring form. It is `AlgEquiv.ofBijective` of `T.realization 𝒜`, with the grading statements
  `isHomogeneousOfShift_affineEquiv` and `isHomogeneousOfShift_affineEquiv_symm`. The forms with
  coefficients in `R` go through `T.realizationOverR 𝒜`: `T.ordinaryComponentEquiv` for `H^{p, w}`
  and `T.diagonalEquiv` for the diagonal. The target of the latter is the external direct sum
  `⨁ q : ℕ, diagonalGrading (T.grading A) q`, which is the blueprint's display and which embeds in
  `T.C.obj A` by `DirectSum.coeAlgHom`. `diagonalAlgEquiv` in `Grading/Diagonal` needs only an
  algebra map that is bijective on each diagonal piece, so `thm:projective` can use it too.

## The cohomology structure

`OrdinaryTheory` (blueprint `def:cohomology`) has these features:

- Its parameters are `k`, `R`, a commutative `R`-algebra `B`, and its weight grading
  `ℬ : ℤ → Submodule R B`, with `R` identified with `ℬ 0`.
- Its total cohomology is a functor `SmoothAlg k ⥤ AlgCat B`, with each value internally
  bigraded by `R`-submodules. `AlgCat` is not commutative, as required.
- Each value also carries an `R`-algebra structure as a field, tied to `B` by `IsScalarTower`, so
  that a direct sum can keep the structure it already has. So at `R = B` the two `B`-module
  structures agree only propositionally, and a term mixing a `B`-linear map with the grading pieces
  fails with an instance mismatch. Prove statements with `R` and `B` separate and specialize, or use
  the wrappers `T.mapOverR`, `T.gysinOverR` and `T.residueOverR`. The same happens at `R = ℤ`, where
  a literal `≃ₗ[ℤ]` or `≃ₐ[ℤ]` picks the canonical `ℤ`-structure of a piece rather than the one from
  the field. The specialized statements still apply: `Examples/Ordinary` shows how to get the literal
  forms, through `AddEquiv.toIntLinearEquiv` and `RingEquiv.toIntAlgEquiv` and a coercion.
- The dimension axiom says `B → C(k)` is bijective, with every degree `(p, w)` for `p ≠ 0` zero.
  C1 sends `ℬ w` into degree `(0, w)` for every `A`, and it follows that `B → C(k)` carries `ℬ w`
  onto degree `(0, w)` (`algebraMap_mem_grading_point_iff`).
- Affine-line invariance is stated for `A → A[t]` over every smooth `A`.
- The residue and Gysin maps of C4 and C5 exist for every `DivisorPair`, and residue and Gysin
  naturality are stated for every transverse morphism. The proof uses only the residue square; the
  Gysin square is there because C5 asks for the whole sequence to commute.
- The boundary projection formula is stated only for `α` of degree `(1, 1)`, as the
  blueprint allows. A weaker hypothesis gives a stronger theorem.
- It has no axiom for the empty object: the pair `emptyDivisor A D`, which is `(A, 1)` for a zero
  ring `D`, already forces the zero ring to have zero cohomology
  (`subsingleton_obj_of_subsingleton`).

Every field must hold in real theories, so check each one against singular cohomology when
you add it. An unsatisfiable structure would make the main theorem vacuous. The docstrings of
`OrdinaryTheory` record that check, which is by hand: only the coefficient axiom
`R ≃ ℬ 0` of the model `B = R[t, t⁻¹]` is checked in Lean.

`Cohomology/Deletion` is the first real audit of these axioms, and it does not import the
presentation. `Generated`, `Bounded` and `IsDeletionShortExact` are predicates proved there for every
arrangement, never fields. The basis is the structure `LogMonomialBasis` of `thm:cohom-basis`, which
holds a finite index type, words and a `B`-basis of monomials. A basis does not determine how many of
its words have a given length, since over the zero ring every family is a basis, so
`exists_logMonomialBasis` also records that its recursive basis has `bettiNumber q` words of length
`q`. **So `Cohomology/Deletion` imports `Combinatorics/Betti`, which must stay free of cohomology**,
and what `cor:projective-betti` says about cohomology goes in `Combinatorics/Multiplicities`, above
the structure theorems. What `thm:betti` says about cohomology is in `Presentation/Ordinary`, since
it extracts the homogeneous pieces of a basis, which `cor:ordinary` needs anyway.

`Combinatorics/ProjectiveBetti` defines the polynomial and natural Betti numbers of a nonempty
projective arrangement without importing cohomology. `poincarePolynomial_eq_decone` identifies
it with every decone. The generic `intersectionSum_cone_eq` pairs subsets with and without a
hyperplane at infinity for any compatible weights and additive map, without finite-dimensionality.
Its polynomial instances give the factors `1 + X` for the Poincaré polynomial and `X - 1` for
the characteristic polynomial. The affine degree-one coefficient count lives in `Combinatorics/Betti`.

`Combinatorics/Multiplicities` identifies actual projective pieces with decone pieces through
`OrdinaryTheory.projectiveDeconeComponentEquiv`. `exists_logMonomialBasis_decone` retains a
recursive logarithmic basis of every decone together with its number of words of each length,
which equals `P.bettiNumber q`. The module and diagonal-basis statements follow with these indices.
Over zero coefficients the bare module and basis statements hold for every cardinality, so they
do not determine the numbers; the separate assertion about words and polynomial coefficients
preserves the count. No unique basis cardinality is inferred from a zero module.

The nine required mathematical regressions and their declarations are indexed in
[`docs/REGRESSIONS.md`](REGRESSIONS.md).

`Examples/Sanity` contains the zero theory as a basic consistency check. It must have zero
coefficients, because `R ≃ ℬ 0` and `B ≃ C(k)` must still hold. It tests the zero-ring edge case,
not the substantive axioms.

### The degreewise bridge

`DegreewiseTheory` supplies the groups `H A (p,w)`, Mathlib's indexed `GRing` and `GAlgebra`
products, degreewise pullbacks, and homogeneous coefficient maps `ℬ w →ₗ[R] H A (0,w)`.
The point and affine-line conditions are also degreewise. The coefficient maps extend along
`DirectSum.decomposeAlgEquiv ℬ` to a central map from `B` to the external direct sum; their
centrality follows from supercommutativity in cohomological degree zero.

`SupportsAndPurity` supplies groups `H_D^{p,w}(X)`, support-forgetting, the localization boundary
of shift `(1,0)`, and oriented purity `H^{p,w}(D) ≃ₗ[R] H_D^{p+2,w+1}(X)`. Its three exactness
fields are the degreewise localization sequence with supports. Transverse support pullbacks,
mixed supported/ambient products, and the usual purity and boundary product identities complete
the input. The product identities are given for arbitrary homogeneous factors, as allowed by the
blueprint, and imply linearity of Gysin and residue over all of `B`.

`ofSupportsAndPurity` takes the external direct sum over every bidegree. Gysin is purity followed
by forgetting supports, and residue is the connecting map followed by inverse purity. It proves
all three total exactness statements from the degreewise sequence and finite support. No
`OrdinaryTheory`, total exactness, or arrangement-theoretic conclusion is an input. The internal
grading is `directSumGrading`, the ranges of the summand inclusions, with its decomposition and
algebra structure proved in `Grading/DirectSum`.

The bridge helpers live in `BridgeData/`, beside the public entry `Bridge.lean`, to avoid putting
a `Foo.lean` module beside a `Foo/` directory. This is a file-layout choice, not a mathematical
departure from the blueprint. `Examples/Bridge` tests the constructor on zero degreewise input;
it does not construct a nonzero standard cohomology theory.

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
