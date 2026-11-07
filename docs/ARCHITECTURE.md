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
| `Grading/Laurent`              | the weight grading `ℬ w = R T^w` of `R[T;T⁻¹]`, for `def:dr-twisted-functor`, and evaluation at `T = 1` |
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
| `Combinatorics/Betti`          | `def:polynomials`, `lem:polynomial-recursion` |
| `Combinatorics/Moebius`         | the finite nonempty intersection poset, its Mathlib Möbius function and both formulas of `lem:mobius`; pure combinatorics |
| `Combinatorics/ProjectiveBetti` | pure cone/decone intersection sums and polynomials of `cor:projective-betti` |
| `Combinatorics/Multiplicities` | cohomological pieces and decone word counts of `cor:projective-betti` |
| `DeRham/Cohomology/Basic`      | `def:dr-cohomology`: `cycles`, `boundaries`, `Cohomology`, classes, functoriality and chain homotopies |
| `DeRham/Cohomology/Degree`     | `def:dr-cohomology`: the degree pieces, `ker d / im d`, graded commutativity and the grading by `ℤ` |
| `DeRham/Cohomology/Point`      | `H⁰`, and the fact `H^*(k) = k` used by `lem:dr-ordinary-basic` |
| `DeRham/Cohomology`            | the comparison with Mathlib's homology of `complex k A`; the module to import |
| `DeRham/Complex/Forms`         | `def:dr-forms`: `Forms`, the universal differential `diff`, and induction on the words `a₀ da₁ ∧ ⋯ ∧ daₙ` |
| `DeRham/Complex/Differential`  | `d`, the characterizing formula, `d² = 0`, signed Leibniz and uniqueness, for `def:dr-complex` and `thm:dr-dga` |
| `DeRham/Complex/Functoriality` | `Forms.map`, with identity and composition, in `thm:dr-dga`, and the bridge to `exteriorMap` |
| `DeRham/Complex/Polynomial`    | the formula of `lem:dr-polynomial-dga` |
| `DeRham/Complex/Presentation`  | `lem:dr-presentation`, for any surjection of algebras and for the canonical presentation |
| `DeRham/Complex`               | `complex`, the cochain complex of `def:dr-complex`, and its functoriality; the module to import |
| `DeRham/Exterior/Basic`        | exterior words, signs and homogeneous components, and the maps `⋀_A M → ⋀_S M'` along a change of rings, for `lem:dr-exterior` and `thm:dr-dga` |
| `DeRham/Exterior/Contraction`  | `lem:dr-contraction`, naturality of contraction for `lem:dr-cartan`, and the decomposition `M = K ⊕ A e` for `lem:dr-polynomial-splitting` |
| `DeRham/Exterior/Projective`   | exterior powers of any projective module are projective, used by `lem:dr-projective` |
| `DeRham/Exterior/BaseChange`   | base change in `lem:dr-exterior`, for any `IsBaseChange`, including localizations |
| `DeRham/Exterior/Quotient`     | the quotient formula in `lem:dr-exterior` |
| `DeRham/Exterior`              | the kernel of `⋀_A^n M → ⋀_S^n M'` for surjections of rings and of modules, the form used by `lem:dr-presentation` and `lem:dr-quotient`; the module to import |
| `DeRham/Homotopy/Polynomial`  | the cotangent splitting and total polynomial-form decomposition of `lem:dr-polynomial-splitting` |
| `DeRham/Homotopy/Degree`      | the degreewise decomposition and its agreement with total forms |
| `DeRham/Homotopy/Integration` | coefficientwise differentiation and integration over a ring in which positive integers are units |
| `DeRham/Homotopy/Differential` | the differential matrix in `lem:dr-polynomial-splitting` |
| `DeRham/Homotopy`             | the explicit integration homotopy and canonical cohomology equivalence of `thm:dr-homotopy`; the module to import |
| `DeRham/Instance/Twisted`      | `def:dr-twisted-functor` on the algebra `TwistedCohomology k A = k[T;T⁻¹] ⊗[k] H^•`, for any `k`-algebra: the `(p, w)` grading, the point, affine-line invariance, and the removal of powers of `T` for `cor:dr-affine` |
| `DeRham/Instance/Basic`        | the functor of `def:dr-twisted-functor` on `SmoothAlg k`, and every field of `lem:dr-ordinary-basic` |
| `DeRham/Localization`          | `lem:dr-localization`, for any `IsLocalization`; `dlog`, and the extension of derivations |
| `DeRham/Log/Basic`             | `def:dr-log`, `lem:dr-log-dga`: `theta`, `logForms`, `logPower`, `logMk`, the differential and the ideal `f L^•`; no smoothness |
| `DeRham/Log/Residue`           | `IsSmoothPrincipalPair`, `lem:dr-regularity`, `def:dr-residue`, `thm:dr-residue-sequence` on elements, `lem:dr-form-projection` |
| `DeRham/Log`                   | `logComplex`, `shiftedComplex`, `logResidueShortExact` of `thm:dr-residue-sequence`, and `DivisorPair.isSmoothPrincipalPair`; the module to import |
| `DeRham/PrincipalQuotient`     | `lem:dr-quotient`, for any surjection of algebras with principal kernel |
| `DeRham/SmoothPair/Koszul`    | `lem:dr-modf-koszul`: wedge exactness modulo a smooth principal divisor in every degree |
| `DeRham/SmoothPair/Projective` | `lem:dr-projective`: projectivity in every form degree, regular scalar action and injectivity into localization |
| `DeRham/SmoothPair`           | the conormal splitting of `lem:dr-conormal`, and the global and localized derivations of `lem:dr-normal-derivation` |
| `Examples/AffineLines`        | concurrent lines and the triangle, including the nonempty-intersection guard |
| `Examples/Bridge`             | zero degreewise inputs, the standard bridge and same-ring components |
| `Examples/CoordinatePolynomials` | the coordinate-arrangement polynomial regression |
| `Examples/Cokernel`            | a nonzero singleton cokernel, empty and duplicate traces, characteristic two and zero coefficients |
| `Examples/DeRhamCohomology`    | exact forms are not an ideal of all forms, `X²` in characteristic two, the point over `ℤ` and `ZMod 2`, the zero algebra |
| `Examples/DeRhamComplex`     | `d` is not linear over the algebra, characteristic two and the zero algebra |
| `Examples/DeRhamHomotopy`     | rational dual numbers, zero coefficients, homotopy normalization and failure of the integration hypothesis in characteristic two |
| `Examples/DeRhamInstance`     | the fields of `lem:dr-ordinary-basic` fit the structure; consumers of the theory; signs by cohomological degree, the zero algebra and characteristic two |
| `Examples/DeRhamLocalization` | nilpotent, zero and unit equations; a conormal map that is not injective over `ZMod 2` |
| `Examples/DeRhamLog`         | signs of the projection formulas; unit, zero-algebra, disconnected and divisor-pair consumers of `DeRham/Log` |
| `Examples/DeRhamSmoothPair`  | unit, zero-algebra and disconnected one-form consumers for `DeRham/SmoothPair`; a disconnected equation for which no derivation has value one globally |
| `Examples/Degenerate`        | coefficient cohomology of empty complements and nonunique zero-ring basis sizes |
| `Examples/Exterior`          | full exterior algebras for singletons and coordinate arrangements |
| `Examples/Ordinary`            | the structure theorem at `R = ℤ`, `ZMod 2`, two points over `F₂`, dimension zero, zero coefficients and `R = B` |
| `Examples/Polynomials`         | polynomial regression examples |
| `Examples/Moebius`             | Möbius sums for concurrent lines, the triangle and parallel lines, including the odd-degree sign |
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
for arbitrary equations and its equation independence. `toAlgHom_projectiveEquiv_unique` also
characterizes the map solely by ratios for any family of equations of the hyperplane labels.
`projectiveComponentEquiv` restricts the
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
do not determine the numbers, and neither does the existence of a word family. The numbers are
the polynomial coefficients, and the link to the words is the recursive construction:
`LogMonomialBasis.empty`, `ofDeletion` and their `wordCount` lemmas. No unique basis cardinality
is inferred from a zero module.

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
- A box collapses its declarations under one line, which opens when a link points inside it, and
  `:::statement "Title"` sets a main theorem apart. A statement is not a node and has no status, so
  anything in it that claims to be formalized must be elaborated Lean or a `bp` link.

Nodes are the theorem-like environments of `blueprint/*.tex` with their `\label`s, so section
labels are not nodes. The parser rejects a `\label` that is on neither such an environment
nor a section, and a theorem-like environment with no `\label`, so that a node cannot drop out
of the check unnoticed. A label used twice is rejected too, including across files, since a
copied label would otherwise add a node with no new coverage obligation. If a blueprint starts
using, say, labelled equations, extend the parser in `OrlikSolomonBook/Blueprint.lean`.

Each node records the blueprint file it comes from, and `{statusSummary}` and `{statusOverview}`
count each file separately, so that planned nodes of one blueprint never lower the counts of
another. `blueprintName` in `OrlikSolomonBook/Node.lean` names a file for readers. A file with no
name there is listed under its file name, not added to another's count.

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
the bridge from a standard degreewise theory, the de Rham instance, and the exposition.

The de Rham instance is planned in its own blueprint, `blueprint/de_rham_instance_blueprint.tex`,
and tracked by the GitHub milestone "M5 De Rham instance". See the next section.

The stable extension is **deferred** unless Adam asks for it. It is §11 of
`blueprint/arrangement_cohomology_lean_blueprint.tex`, the second half of that blueprint's
Milestone 5 and its Milestone 6. Those are the blueprint's own numbers, unrelated to the GitHub
milestone M5.

## The de Rham instance

`blueprint/de_rham_instance_blueprint.tex` is authoritative for the mathematics of this part. It
constructs a nonzero value of `OrdinaryTheory`, with `k` a field of characteristic zero, `R = k` and
`B = k[t, t⁻¹]`, and instantiates the affine and projective theorems. The "fixed interface" it
refers to is `OrdinaryTheory` in `Cohomology/Axioms`, whose fields match its checklist of 22. No
field may be weakened, and no comparison or exactness statement may become a hypothesis. Its
declaration names are proposals, as with the first blueprint.

The namespace is `OrlikSolomon.DeRham`. Exterior calculus, the dg algebra and its differential,
its cohomology algebra, polynomial-form decomposition and homotopy invariance, forms on
localizations and principal quotients, projectivity and regular scalar action in every form degree,
injectivity into localization, conormal splitting, global and localized normal derivations, wedge
exactness modulo the divisor, logarithmic forms with their residue sequence, and the Laurent-twisted
functor with the fields preceding Gysin and residue exist; the other parts below remain planned.
The table groups modules by issues #72–#83. The conormal and normal-derivation results need only
Mathlib's Kähler differentials and formal-smoothness lifts. Normalizing a derivation on
`A[v(f)⁻¹]` uses Mathlib's localization of Kähler differentials, and wedge exactness uses exterior
contraction; neither requires the de Rham differential.

| Module under `OrlikSolomon/` | Blueprint labels |
| ---------------------------- | ---------------- |
| `DeRham/Exterior`            | `lem:dr-exterior`, `lem:dr-contraction` |
| `DeRham/Complex`             | `def:dr-forms`, `lem:dr-polynomial-dga`, `lem:dr-presentation`, `def:dr-complex`, `thm:dr-dga` |
| `DeRham/Localization`, `DeRham/PrincipalQuotient` | `lem:dr-localization`, `lem:dr-quotient` |
| `DeRham/Cohomology`          | `def:dr-cohomology` |
| `DeRham/Homotopy`            | `lem:dr-polynomial-splitting`, `thm:dr-homotopy` |
| `DeRham/SmoothPair`          | `lem:dr-conormal`, `lem:dr-normal-derivation` |
| `DeRham/SmoothPair/Projective` | `lem:dr-projective` |
| `DeRham/SmoothPair/Koszul`   | `lem:dr-modf-koszul` |
| `DeRham/Log`                 | `def:dr-log`, `lem:dr-log-dga`, `lem:dr-regularity`, `def:dr-residue`, `thm:dr-residue-sequence`, `lem:dr-form-projection` |
| `DeRham/Pole`                | `lem:dr-cartan`, `lem:dr-euler`, `def:dr-pole-filtration`, `lem:dr-pole-quotient`, `thm:dr-pole-contraction`, `lem:dr-filtration-reduction`, `thm:dr-comparison` |
| `DeRham/Maps`                | `def:dr-gysin`, `lem:dr-exactness`, `thm:dr-projection`, `thm:dr-log-naturality`, `thm:dr-naturality` |
| `DeRham/Instance/Twisted`, `DeRham/Instance/Basic` | `def:dr-twisted-functor`, `lem:dr-ordinary-basic` |
| `DeRham/Instance`            | `def:dr-twisted-maps`, `thm:dr-ordinary-localization`, `thm:dr-instance` |
| `DeRham/Corollaries`         | `lem:dr-tau`, `cor:dr-affine`, `cor:dr-projective` |
| `Examples/DeRham`, `Examples/DeRhamSmoothPair` | `prop:dr-gm-example`, `prop:dr-unit-example`, `prop:dr-product-example`, `prop:dr-zero-example`, `prop:dr-crossing-example`, `prop:dr-morphism-examples`, `prop:dr-torus-example`, `prop:dr-characteristic-p` |

The rule at the top of this file applies to the namespace. These module names are file names only:
a declaration or sub-namespace `OrlikSolomon.DeRham.Localization` would capture Mathlib's
`Localization`, and `OrlikSolomon.DeRham.Complex` would capture `Complex`.

### Forms and the differential

- **The total algebra is primary.** `Forms k A` is a reducible abbreviation of
  `ExteriorAlgebra A Ω[A⁄k]`. Mathlib's `⋀[A]^n M` is by definition a submodule of the exterior
  algebra, so a form of degree `n` is `x : Forms k A` with `x ∈ ⋀[A]^n Ω[A⁄k]`, and there are no
  casts between degrees. The differential `d k : Forms k A →ₗ[k] Forms k A` is an operator on the
  total algebra. A signed rule takes the degree as a hypothesis, as `d_mul_of_mem_exteriorPower` does.
  On all forms, `d_mul` uses the grade involution instead of a sign, so state a fact about a closed
  form of no particular degree with that. Blueprint degree zero is `algebraMap A (Forms k A)` and
  degree one is `ι A`, and `mem_exteriorPower_zero_iff` and `mem_exteriorPower_one_iff` say so.
- **Typed maps only where a complex needs them.** `powerD k A n : ⋀^n → ⋀^(n+1)` and
  `Forms.mapPower φ n : ⋀^n → ⋀^n` are the same operators with their types restricted, and
  `coe_powerD` and `coe_mapPower` pass between the two. `complex k A` is a
  `CochainComplex (ModuleCat k) ℕ`, and `complexMap` and `complexFunctor` are its functoriality.
  Nothing is indexed by `ℤ`. Extending by zero to `ℤ` is for the module that needs it.
- **Scalars.** Forms are `A`-modules, `d` is only `k`-linear, and `Forms.map φ` for
  `φ : A →ₐ[k] A'` is a `k`-algebra map that is semilinear over `φ` (`Forms.map_smul`, or
  `Forms.mapₛₗ` when a bundled map is needed). It takes an `AlgHom`, because the instance requires it
  on `SmoothAlg k`. When `S` is an `A`-algebra instance and the exterior algebra API of `DeRham/Exterior`
  is wanted, for base change or for kernels, `Forms.map_toAlgHom` and `Forms.mapPower_toAlgHom`
  identify `Forms.map` with `exteriorMap` and `powerMap` along `KaehlerDifferential.map`.
- **Normal form.** `diff k : Derivation k A (Forms k A)` is `a ↦ da`, so `Derivation.leibniz`,
  `Derivation.leibniz_pow` and `Derivation.leibniz_of_mul_eq_one` apply to it. The normal form of a
  word is `a₀ • word (diff k) [a₁, …, aₙ]`, and `Forms.induction` and
  `Forms.induction_exteriorPower` are the induction principles on it. `word_cons` unfolds a word on
  an explicit list, and `simp` handles those through `d_smul`, `d_diff_mul`, `Forms.map_smul` and
  `Forms.map_diff`. `exteriorContraction_diff` is the contraction of the normal form.
- **The construction of `d` departs from the blueprint's proof, not from its statements.** The
  blueprint constructs `d` on `k[X_a | a ∈ A]` and descends it, and warns that an `A`-linear lift of
  `a ↦ da` is wrong. That lift is wrong for the usual `A`-module structure on forms. Instead, let
  `OddDual` be the ring of `x + ε u`, for an odd `ε` with `ε² = 0`, so that
  `(x + ε u) * (y + ε v) = x y + ε (σ x * v + u * y)`, with `σ` the grade involution. Signed Leibniz
  says exactly that `x ↦ x + ε d x` is a ring map. Making `OddDual` an `A`-algebra through
  `a ↦ a + ε da` makes that map `A`-linear, and `ExteriorAlgebra.lift` and
  `Derivation.liftKaehlerDifferential` then produce it. All of this is private to
  `DeRham/Complex/Differential`, and `d` is `@[no_expose]`. No polynomial ring is involved, and no
  basis of any differentials.
- **`d` is characterized by its formula.** `d_smul_word` is
  `d (a₀ da₁ ∧ ⋯ ∧ daₙ) = da₀ ∧ da₁ ∧ ⋯ ∧ daₙ`. `eq_d_of_smul_word` and `eq_d_of_leibniz` are
  uniqueness. Prove things about `d` through these and through `d_mul`, and do not look for a
  presentation. `lem:dr-polynomial-dga` and `lem:dr-presentation` are theorems about this operator.
  `presentationEquiv_dQuotient` says that the operator descended from `k[X_a | a ∈ A]`, which is how
  the blueprint defines the differential, is `d`.
- **Differential ideals.** `differentialIdeal k I` is `I Ω^• + dI ∧ Ω^•` for any ideal. For a
  surjection `φ` it is the kernel of `Forms.map φ` (`Forms.map_eq_zero_iff_of_surjective`), and
  `quotientEquiv` and `quotientPowerEquiv` are the quotients. `lem:dr-presentation` is the case of
  `presentationHom k A`, and `lem:dr-quotient` is the case of `A → A ⧸ (f)`, with
  `differentialIdealPower_span` for its generators. The quotient is stated as `k`-linear equivalences
  and the kernel of an algebra map, with no quotient ring.

The conormal splitting requires only formal smoothness of `A/(f)`;
`exists_normalDerivation_modulo` additionally uses formal smoothness of `A`. Both allow unit
equations, the zero ring and disconnected algebras. The latter asserts `v(f) = 1 + f*h`, with
normalization to one only after localizing at `v(f)`.

`DeRham/Exterior/Projective` proves that exterior powers of an arbitrary projective module are
projective: apply `exteriorPower.map` to its free-module splitting and use Mathlib's freeness of
exterior powers of free modules. `DeRham/SmoothPair/Projective` combines this instance with
`Algebra.FormallySmooth.projective_kaehlerDifferential`. Its regularity and localization
injectivity lemmas assume only projectivity of `Ω[A⁄k]`, which formal smoothness supplies.
`isSMulRegular_forms` reuses flat-module regularity, and
`Forms.injective_mapPower_of_isLocalizationAway` uses the criterion that some power of the equation
kills a form in the localization kernel. All form degrees, unit equations and the zero algebra are
included, without finite presentation or smoothness of a quotient.

### Forms on localizations and on quotients

- **Certified pairs.** `DeRham/Localization` takes `[Algebra A T] [IsScalarTower k A T]` and
  `[IsLocalization M T]`, or `[IsLocalization.Away f T]`, and never mentions `Localization`. For a
  `DivisorPair`, these are instances of `P.ambient` and `P.compl`, and
  `IsScalarTower.toAlgHom k P.ambient P.compl` is `algHom P.j` by `rfl`. `DeRham/PrincipalQuotient`
  takes `φ : A →ₐ[k] S` with `Function.Surjective φ` and `RingHom.ker φ = Ideal.span {f}`, the shape
  of `surjective_i` and `ker_i`.
- **The identification is the predicate.** `Ω_A^n → Ω_T^n` is the `A`-linear map
  `powerMap T (KaehlerDifferential.map k k A T) n`, the same as `Forms.mapPower` by
  `Forms.mapPower_toAlgHom`. The primary statement is the instance that it is `IsLocalizedModule M`.
  Prefer `IsLocalizedModule` and the consequences `Forms.map_eq_zero_iff_of_isLocalizationAway` and
  `Forms.exists_eq_invSelf_pow_smul_map_of_mem`. `powerLocalizationEquiv`, whose source is Mathlib's
  `LocalizedModule`, is the literal statement of the blueprint.
- **The form `θ`.** `dlog k u` is `u⁻¹ • du` for a unit `u`, so for a divisor pair
  `θ = dlog k P.eqnUnit`, and `dlog_eq_invSelf_smul` compares it with `invSelf`. `dlog_mul` and
  `Forms.map_dlog` are the unit changes of `thm:dr-log-naturality`. `d_val_inv_pow_smul` and
  `d_val_smul` are the formulas that `def:dr-pole-filtration` and `lem:dr-log-dga` use.
- **The denominator.** `f Ω_A^n + df ∧ Ω_A^(n-1)` is `differentialIdealPower k (Ideal.span {f}) n`,
  and `differentialIdealPower_span_singleton_zero` and `_succ` say so. There is no separate
  definition. Its quotient is taken by the `A`-submodule itself, so that it is an `A`-module, and
  `principalQuotientPowerEquiv` is `k`-linear and semilinear over `φ`.
- **The conormal map.** `principalConormalMap k f` is the blueprint's map, with source `(f)/(f²)`
  and no regularity of `f`. It is for the literal quotient `A ⧸ (f)`, like `conormalMap` of
  `DeRham/SmoothPair`, whose source is `A ⧸ (f)` itself. `principalConormalMap_smul_self` and
  `principalConormalMap_principalCotangentEquiv` relate the two, and
  `exact_principalConormalMap` is deduced from `exact_conormalMap`. So `DeRham/PrincipalQuotient`
  imports `DeRham/SmoothPair`, which uses only Mathlib. `Examples/DeRhamLocalization` shows that the
  map need not be injective.

### Logarithmic forms and the residue

- **The hypotheses are one `Prop`.** `IsSmoothPrincipalPair f φ` bundles the regularity of `f`, the
  surjectivity of `φ : A →ₐ[k] S`, `RingHom.ker φ = Ideal.span {f}` and the formal smoothness of `A`
  and `S`. `DivisorPair.isSmoothPrincipalPair` is the case of a pair, and
  `IsSmoothPrincipalPair.of_quotient` that of the literal quotient. The localization `T` stays an
  instance of `IsLocalization.Away f T`. `DeRham/Log/Basic` does not need the hypotheses: logarithmic
  forms and their dg algebra exist for any `f`.
- **Regular forms are written as their images.** The blueprint identifies `Ω_A` with its image in
  `Ω_T`. Here that image is `Forms.map (IsScalarTower.toAlgHom k A T)`, typed by `ofRegular` and
  `powerToLog`, and `IsSmoothPrincipalPair.map_injective` justifies the identification.
- **The total algebra is primary, again.** `logForms k f T` is an `A`-subalgebra of `Forms k T`, and
  `logMk k f T (ω, η)` is its normal form `ω + θ ∧ η`, a surjective `A`-linear map. So
  `obtain ⟨⟨ω, η⟩, rfl⟩ := logMk_surjective k f T x` starts a proof, and `logMk_mul_logMk`,
  `logD_logMk` and `logResidue_logMk` compute. The module `logPower k f T n` is the blueprint's literal
  sum, and `logPower_eq_inf` says that it is the part of `logForms` of degree `n`, which is where the
  graded structure comes from. The form `θ` is `theta k f T`, and `theta_eq_dlog` compares it with
  `dlog k u` for any unit that is the image of `f`.
- **The residue.** `logResidue T h : logForms k f T →ₛₗ[φ] Forms k S` is defined on all logarithmic
  forms, by descent along `logMk`, and `@[no_expose]`. Use `logResidue_logMk` and
  `logResidue_eq_of_coe_eq`, which is independence of the decomposition. `logResidueₗ` is its
  `k`-linear form, and `logPowerResidue T h n : L^(n+1) →ₗ[k] Ω_S^n` is its form typed by degree, with
  no degree-zero version, since the target is zero there.
- **The shift.** Complexes are indexed by `ℕ`, so `shiftedComplex k S` is `Ω_S^n` in degree `n + 1`
  with differential `-d`, and `PUnit` in degree zero. This is the blueprint's `Ω_S^•[-1]`, whose
  terms in negative degrees vanish. `logResidueShortExact` says the sequence is short exact, in
  Mathlib's sense. It is not a substitute for the elementwise statements `logResidue_logD`,
  `exact_powerToLog_logPowerResidue` and `logResidue_surjective`, which fix the sign of
  `def:dr-gysin` without reference to a library connecting map.

### Cohomology

- **Total cohomology comes first, and its degrees are submodules of it.** `Cohomology k A` is one
  type and `Cohomology.degree k A n` is a `k`-submodule. The reason is the design of `d`: it is an
  operator on the total algebra, and the two facts that make the quotient exist, `d_mul` and
  `mul_d_of_d_eq_zero`, have no degree hypothesis. Building the degrees first would need a product
  `H^p × H^q → H^(p+q)` with casts along `p + q`, and then a direct sum with the same structure,
  which `OrdinaryTheory` only wants as an internal grading of one type in any case.
- **The quotient.** `cycles k A` is a `k`-subalgebra of forms, and `boundaries k A` is a
  `TwoSidedIdeal` of it. It is not an ideal of all forms: `not_exists_d_eq_X_smul_diff_X` is the
  counterexample. `Cohomology k A` is the `RelationQuotient` of that ideal used as its own set of
  relators, and `mem_relationSubmodule_coe_twoSidedIdeal` says that this adds nothing. Those
  relators are not homogeneous, since a sum of boundaries in two degrees is a boundary, so the
  grading uses `RelationQuotient.gradedAlgebraOfIsHomogeneous`, whose hypothesis is on `J(ℛ)` and not
  on `ℛ`. Like `OSAlgebra`, it is a `def` with its own `SMul` transport.
- **Classes.** A class is `Cohomology.mk x hx`, with `hx : d k x = 0`. `simp` combines operations
  into one class, as in `mk_mul : mk x hx * mk y hy = mk (x * y) _`, because the other direction is
  not a rewrite rule: `x * y` can be closed when `x` and `y` are not. Use `mk_eq_zero_iff`,
  `mk_eq_mk_iff`, `Cohomology.induction`, `induction_degree`, `lift` and `liftLinear`, and do not
  unfold the quotient.
- **Degrees.** `Cohomology.degree k A n` is indexed by `ℕ`, with `gradedAlgebraDegree` and
  `decompose_mk`. `Cohomology.grading k A p` is the same grading indexed by `ℤ`, with
  `grading_natCast` and `grading_of_neg`: it is `coarsenGrading` along `ℕ → ℤ`, so that the signs
  of `isGradedCommutative_grading` and the first index of a bigrading agree. `degreeEquiv` and
  `homologyIso` say that a piece is `ker d / im d`, respectively Mathlib's homology of `complex k A`,
  and `coe_homologyIso_hom_homologyπ` says which map that is. `rangeD k A n` is the image of `d`,
  with degree `-1` being zero, so `n = 0` is no exception. A homogeneous exact form has a homogeneous
  primitive, by `mk_eq_zero_iff_of_mem_exteriorPower_succ`.
- **Chain homotopies.** `map_eq_map_of_homotopy` takes an additive operator `K` on total forms with
  `φ_* - ψ_* = d K + K d`, for `thm:dr-homotopy`. `lem:dr-filtration-reduction` is an argument about
  submodules of forms and their quotients, and it needs nothing from this module.
- **For the instance.** See "The Laurent-twisted theory" below.
- **The cohomology of a dg subalgebra `L` of forms,** as in `thm:dr-comparison`, is not generic here,
  since a shared layer would wrap every lemma above for one other use. It takes about 30 lines with
  the same tools: the subalgebra `L ⊓ cycles k A`, the `TwoSidedIdeal` of the `d y` for `y ∈ L`, its
  `RelationQuotient`, and `RelationQuotient.liftAlgHom` of `Cohomology.mkₐ` for the map to
  `Cohomology k A`. The only hypothesis is `involute x ∈ L` for `x ∈ L`, for `x ∧ dy = d (σ x ∧ y)`,
  and it holds because `L` is homogeneous. `homogeneousSubalgebraGradedAlgebra` and
  `gradedAlgebraOfIsHomogeneous` give its grading, and `RelationQuotient.liftLinear` gives `H(ρ)`.

### Polynomial homotopy

`DeRham/Homotopy` requires only commutative rings and a `k`-algebra `A`. The cotangent splitting
uses the Jacobi–Zariski sequence for `k → A → A[X]` and formal smoothness of the polynomial
extension over `A`, without assuming smoothness of `A` over `k`. Exterior base change and the
existing line-splitting API give `polynomialFormDecomposition` on total forms. Its degreewise
restriction `polynomialPowerDecomposition`, the coefficient-degree lemmas and the vanishing of
the variable component in degree zero give exactly `lem:dr-polynomial-splitting`.

The differential matrix is `d_A α + dX ∧ (∂_X α - d_A β)`. Coefficientwise integration is only
`k`-linear, as is `d_A`. It needs the hypothesis `∀ n : ℕ, IsUnit (n + 1 : k)` and includes zero
coefficients. `polynomialHomotopy` is the actual degree-lowering operator `K(α + dX ∧ β) = Iβ`,
with `polynomialHomotopy_identity` proving `dK + Kd = id - inc ∘ ev₀`. The algebra equivalence
`polynomialCohomologyEquiv` is induced by inclusion of constants, with inverse induced by
`polynomialEvaluationAtZero`; its public formulas fix both maps and its degree lemma records
preservation and reflection of the grading. `bijective_cohomologyMap_C` is the input for the
polynomial axiom of the instance. The rational dual-number and zero-ring regressions require no
smoothness of the coefficient algebra.

### The Laurent-twisted theory

- **The coefficient is on the left.** `TwistedCohomology k A` is `k[T;T⁻¹] ⊗[k] Cohomology k A`, a
  reducible abbreviation, for any `k`-algebra `A`. This departs from the order the blueprint writes:
  Mathlib's `B`-algebra structure on a tensor product is on the left factor. The `k`-algebra structure
  is `Algebra.TensorProduct.leftAlgebra`, and there is no competing one, since `R ≠ B`:
  `Examples/DeRhamInstance` tests the forms that fail at `R = B`.
- **The bigrading is `(p, w)`.** `TwistedCohomology.grading k A` is
  `coarsenGrading (tensorProductGrading ℬ (Cohomology.grading k A)) swap`, for
  `swap : (w, p) ↦ (p, w)`. Do not look through it: `mem_grading_iff` says that the piece `(p, w)`
  consists of the `T w ⊗ₜ c` with `c ∈ H^p`, with no sum and no span, and `T_tmul_inj` says that `c`
  is unique. The sign `isGradedCommutative_grading` is by `Prod.fst`, the cohomological degree.
- **`evalOne` forgets the weight.** `evalOne k A` is the `k`-algebra map sending `T` to `1`, so
  `evalOne (T w ⊗ₜ c) = c`. On a homogeneous `x` it recovers `c`: `T_tmul_evalOne_of_mem_grading`.
  `gradingEquiv` and `degreeEquiv` are the resulting identifications of `H^p` and `H^n` with a piece.
  `diagonal k A` is the `k`-algebra map `x ↦ T^q x` on `H^q`, which is the blueprint's inverse in
  `cor:dr-affine`, and `diagonalEquiv k A` is `H^• ≃ₐ[k] ⨁ q : ℕ, C(A)_{q, q}`, with its target in
  the form of `OrdinaryTheory.diagonalEquiv`. Its inverse is `evalOne`, by
  `diagonalEquiv_symm_apply`.
- **Computing through the functor.** `twistedCohomologyFunctor k` is a `def`, like objects and pairs.
  So `(twistedCohomologyFunctor k).obj A` is `TwistedCohomology k A` only at default transparency, and
  a value `T` of the structure with `T.C` this functor must stay a `def` too: with an `abbrev`, the
  generic lemmas about `T.C` stop firing, for the reason in "Objects and pairs are `def`s". So `rw` and
  `simp` do not see the tensor product in `T.C.obj A`: they cannot rewrite with a lemma about
  `TwistedCohomology` there, and they leave a goal with identical sides of different types. State and
  prove computations on `TwistedCohomology k A`, and pass between the two once, with `exact` or
  `change`. The maps `T.C.map f (b ⊗ₜ c)` and membership in `T.grading A i` are `rfl`-compatible with
  `TwistedCohomology.map` and `TwistedCohomology.grading`. `Examples/DeRhamInstance` has
  `RemainingFields.theory`, which fills the structure with these fields and the remaining ones as
  arguments, and builds the equivalence of `cor:dr-affine` on it. A value of the structure can also
  add typed wrappers, as the deletion pair does, if this becomes frequent.

The chapter `OrlikSolomonBook/DeRham.lean` records the current status of each node. Its opening
names the exterior calculus, dg algebra, cohomology algebra, polynomial homotopy, forms on
localizations and quotients, projectivity and regularity of forms, injectivity into localization,
conormal splitting, normal derivations, modulo-divisor wedge exactness, logarithmic forms with
their residue sequence, and the Laurent-twisted functor with the first fields of the structure as
formalized, and lists what remains. The first page, `Organization` and the
chapter on the axioms say the instance is in progress. No nonzero value of `OrdinaryTheory` has been
constructed. The build does not check that prose, so keep it current as nodes land. The PR
that proves `thm:dr-instance` must update the sentences saying that no nonzero value
of the structure has been constructed: on the first page, in the chapter on the axioms, on the
status page and in `README.md`.
