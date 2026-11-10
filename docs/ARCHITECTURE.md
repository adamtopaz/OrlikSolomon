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
| `Algebra/HomogeneousRelations` | lowest-degree relation spans and their exterior-quotient kernel specialization, for M8 node `A02` (`thm:a02`) |
| `Algebra/Exact`                | `lem:basis-ses`, `lem:comparison` |
| `Algebra/FinsuppKernel`        | the generic discard-and-merge kernel calculation used in `lem:l01`, without its trace geometry |
| `Algebra/UnitTransfer`        | the three-equation unit-cancellation calculation used in `lem:l04`, over arbitrary commutative rings |
| `Algebra/ComplexReduction`     | cocycle and primitive reduction through a contractible quotient, for arbitrary-shaped complexes and square-zero total operators; `lem:dr-filtration-reduction` |
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
| `Geometry/ProjectiveScheme`    | `O(U_P)` as the complement in Mathlib's `Proj`, its independence of equations, and the intersection of charts in `def:geo-projective` |
| `Cohomology/Axioms`            | `def:cohomology` |
| `Cohomology/BridgeData/Basic`   | degreewise products, coefficients and pullbacks for `lem:standard-bridge` |
| `Cohomology/BridgeData/Category` | category-independent degreewise products, coefficients, pullbacks, total algebra and point/line comparisons for `lem:standard-bridge` and `thm:geo-bridge` |
| `Cohomology/BridgeData/CategorySupports` | generic pair diagrams, supports and purity; shared total exactness, shifts, coefficient linearity, naturality and projection for `lem:standard-bridge` and `thm:geo-bridge` |
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
| `DeRham/Corollaries`           | `dlogClass`, `lem:dr-tau`, `cor:dr-affine` and `cor:dr-projective`: the structure theorems for `H^•_dR`, with no cohomology theory as a parameter |
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
| `DeRham/Instance/Maps`         | `def:dr-twisted-maps` and `thm:dr-ordinary-localization` for a smooth principal pair: `twistMap`, the twisted Gysin map and residue, their shifts, exactness, naturality and projection formula |
| `DeRham/Instance`              | `thm:dr-instance`: the value `ordinaryTheory k`, its nonvanishing, and `twistedClass`, the typed form in which to compute in it; the module to import |
| `DeRham/Localization`          | `lem:dr-localization`, for any `IsLocalization`; `dlog`, and the extension of derivations |
| `DeRham/Log/Basic`             | `def:dr-log`, `lem:dr-log-dga`: `theta`, `logForms`, `logPower`, `logMk`, the differential and the ideal `f L^•`; no smoothness |
| `DeRham/Log/Cohomology`        | `LogCohomology`, its grading, and the algebra maps `H^•(A) → H^•(L) → H^•(T)`, for `thm:dr-comparison` and `lem:dr-exactness`; no smoothness |
| `DeRham/Log/Residue`           | `IsSmoothPrincipalPair`, `lem:dr-regularity`, `def:dr-residue`, `thm:dr-residue-sequence` on elements, `lem:dr-form-projection` |
| `DeRham/Log`                   | `logComplex`, `shiftedComplex`, `logResidueShortExact` of `thm:dr-residue-sequence`, and `DivisorPair.isSmoothPrincipalPair`; the module to import |
| `DeRham/Maps/Gysin`            | `def:dr-gysin`, `lem:dr-exactness` and `thm:dr-projection` for `H^•(L)`: `LogCohomology.residue`, `gysin`, its explicit formulas, exactness and the shifts |
| `DeRham/Maps/Naturality`       | `thm:dr-log-naturality`, and `thm:dr-naturality` for `H^•(L)`: `IsPairHom`, `logMap`, `logResidueShortComplexMap`, `gysin_map`, `DivisorPair.Hom.isPairHom` and associated equations |
| `DeRham/Pole/Cartan`           | `lem:dr-cartan`: contraction, Lie derivative and localization |
| `DeRham/Pole/Euler`            | `lem:dr-euler`: actual Euler contraction, the quotient `L/fL` and its homogeneous pieces |
| `DeRham/Pole/Filtration`       | `def:dr-pole-filtration`: increasing, exhaustive pole stages and their differential |
| `DeRham/Pole/Complex`          | pole stages and their inclusions as complexes of `k`-modules |
| `DeRham/Pole/Quotient`         | `lem:dr-pole-quotient`: the successive quotient and its actual differential |
| `DeRham/Pole/Contraction`      | `thm:dr-pole-contraction`: the explicit contracting operator and its degree |
| `DeRham/Pole/Reduction`        | finite cocycle and primitive reduction for `thm:dr-comparison` |
| `DeRham/Pole/Comparison`       | `thm:dr-comparison`: bijectivity of the canonical map and its algebra equivalence |
| `DeRham/Pole/Degree`           | natural and integer degree equivalences, preservation, reflection, certificate independence, and `logToLocalization_quasiIso` |
| `DeRham/Pole`                 | global logarithmic comparison; the module to import |
| `DeRham/Maps`                  | `residue` on `H^•(T)`, through `thm:dr-comparison`: exactness in each degree, `thm:dr-projection` and `residue_map`; the module to import |
| `DeRham/PrincipalQuotient`     | `lem:dr-quotient`, for any surjection of algebras with principal kernel |
| `DeRham/SmoothPair/Koszul`    | `lem:dr-modf-koszul`: wedge exactness modulo a smooth principal divisor in every degree |
| `DeRham/SmoothPair/Projective` | `lem:dr-projective`: projectivity in every form degree, regular scalar action and injectivity into localization |
| `DeRham/SmoothPair`           | the conormal splitting of `lem:dr-conormal`, and the global and localized derivations of `lem:dr-normal-derivation` |
| `Examples/AffineLines`        | concurrent lines and the triangle, including the nonempty-intersection guard |
| `Examples/Bridge`             | zero degreewise inputs, the standard bridge and same-ring components; `simp` on the component formulas of both bridges |
| `Examples/CoordinatePolynomials` | the coordinate-arrangement polynomial regression |
| `Examples/Cokernel`            | a nonzero singleton cokernel, empty and duplicate traces, characteristic two and zero coefficients |
| `Examples/DeRham`             | umbrella for the de Rham worked regressions and excluded cases; the module to import |
| `Examples/DeRhamCalculations` | umbrella for the worked de Rham cohomology calculations |
| `Examples/DeRhamCalculations/Basic` | unit and zero algebras and the disconnected complement with its idempotent cohomology splitting |
| `Examples/DeRhamCalculations/Torus` | the punctured-line and two-torus calculations, exterior products, and the opposite signs of the two residues |
| `Examples/DeRhamCharacteristic` | actual characteristic-`p` failures of affine-line invariance and logarithmic comparison, with nonzero polynomial and Laurent classes |
| `Examples/DeRhamCohomology`    | exact forms are not an ideal of all forms, `X²` in characteristic two, the point over `ℤ` and `ZMod 2`, the zero algebra |
| `Examples/DeRhamComplex`     | `d` is not linear over the algebra, characteristic two and the zero algebra |
| `Examples/DeRhamCorollaries` | the de Rham corollaries for one point and two rational points of `𝔸¹` and two points of `ℙ¹`: values on generators, nonvanishing, independence, a zero product and dimensions |
| `Examples/DeRhamCrossing`     | the nonsmooth crossing divisor, a regular logarithmic wedge with nonzero proposed residue, and the resulting contradiction between presentations |
| `Examples/DeRhamHomotopy`     | rational dual numbers, zero coefficients, homotopy normalization and failure of the integration hypothesis in characteristic two |
| `Examples/DeRhamInstance`     | the instance is not a zero theory: its point, its residue and `τ` are nonzero; consumers of the instance; signs by cohomological degree, the zero algebra and characteristic two |
| `Examples/DeRhamLocalization` | nilpotent, zero and unit equations; a conormal map that is not injective over `ZMod 2` |
| `Examples/DeRhamLog`         | signs of the projection formulas; unit, zero-algebra, disconnected and divisor-pair consumers of `DeRham/Log` |
| `Examples/DeRhamMaps`        | signs of the residue and Gysin maps; the empty divisor, divisor-pair consumers, and the morphism that is not flat, with its proof |
| `Examples/DeRhamMorphisms`    | the flat unit change, genuinely nonflat naturality, and the excluded squaring map with residue two |
| `Examples/DeRhamPole`        | logarithmic comparison with zero coefficients, unit equations and a disconnected rational smooth pair |
| `Examples/DeRhamSmoothPair`  | unit, zero-algebra and disconnected one-form consumers for `DeRham/SmoothPair`; a disconnected equation for which no derivation has value one globally |
| `Examples/Degenerate`        | coefficient cohomology of empty complements and nonunique zero-ring basis sizes |
| `Examples/Exterior`          | full exterior algebras for singletons and coordinate arrangements |
| `Examples/FinsuppKernel`     | empty retained labels, discarded and merged labels, characteristic two and zero coefficients for the generic trace-kernel helper |
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
- `Geometry/ProjectiveScheme` and the scheme layer `Geometry/Schemes/` of milestone M6 are the only
  modules that import Mathlib's schemes. `Geometry/ProjectiveScheme` alone added about 250 Mathlib
  modules to the closure of the root and of the book, about 11%. It is a leaf for
  the algebraic development: the proof of the structure theorems, the algebra, the combinatorics and
  the algebraic de Rham instance may not import it, so they stay free of schemes. The scheme layer of
  milestone M6 is the exception: `Geometry/Schemes/Projective` imports it, and so may the modules
  built on that. See "The geometric refactor" below.

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
- **Lowest-degree relations:** `Algebra/HomogeneousRelations` uses an ordinary
  `GradedAlgebra (𝒜 : ℕ → Submodule R T)` on a possibly noncommutative ring. If every
  relator is homogeneous in some degree at least `d`, its relation submodule intersected
  with `𝒜 d` is spanned by the degree-`d` relators with degree-zero contexts. The contexts
  reduce to scalars only under the explicit hypothesis
  `𝒜 0 ≤ (Algebra.linearMap R T).range`. This does not require an injective scalar map or
  nonzero coefficients. `exteriorAlgebra_quotient_ker_eq_comap_span` discharges that
  hypothesis for exterior algebras and identifies the restricted quotient kernel.
  The application at `d = 2` still needs the geometric identification of the relators in
  M8 node `A02`; this generic helper does not certify that node.
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
the bridge from a standard degreewise theory, the de Rham instance, the geometric refactor,
the planned cohomological hyperplane reconstruction (M8), and the exposition.

The de Rham instance has its own blueprint, `blueprint/de_rham_instance_blueprint.tex`, and is
tracked by the GitHub milestone "M5 De Rham instance". See the next section.

The geometric refactor, milestone M6, has its own blueprint,
`blueprint/geometric_refactor_blueprint.tex`, and is tracked by the GitHub milestone
"M6 Geometric refactor". It restates the affine and projective theorems for cohomology theories on
smooth schemes, with complements as open subschemes, and transports the de Rham instance to smooth
affine schemes. It builds on the algebraic development and the de Rham instance and changes
neither. A de Rham instance on schemes that are not affine is not part of it. See "The geometric
refactor" below.

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
exactness modulo the divisor, logarithmic forms with their residue sequence, global logarithmic
comparison, the residue and Gysin maps with their long exact sequence, projection formula and
naturality, the Laurent-twisted functor, the instance `ordinaryTheory k` with all 22 fields,
`lem:dr-tau` and the two corollaries `cor:dr-affine` and `cor:dr-projective` exist. All eight
worked regression nodes are formalized.
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
| `DeRham/Instance/Maps`, `DeRham/Instance` | `def:dr-twisted-maps`, `thm:dr-ordinary-localization`, `thm:dr-instance` |
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

### The residue, the Gysin map and naturality

- **On elements, with no connecting map.** `gysin T h` is defined by the blueprint's formula, as a
  `k`-linear map on closed forms that descends, and `gysin_mk_of_logResidue_eq` is that formula:
  `G[γ] = [dλ]` for `ρ λ = γ`, with `dλ` the image of a regular form. Exactness is three short proofs
  on representatives. So Mathlib's connecting map for `logResidueShortExact`, which would need
  `H^(n+1)(shiftedComplex k S) ≃ H^n(Ω_S)` and a lemma reconciling its sign, is not used anywhere.
  `gysin_mk_of_map_eq` is `G[γ] = [-θ ∧ dη]`, and `gysin_mk_of_d_eq` is the same class without `T`.
- **Layers.** Everything in `DeRham/Maps/Gysin` and `DeRham/Maps/Naturality` is about `H^•(L)` and
  needs no comparison and no hypothesis on `k`: `LogCohomology.residue T h` is `H(ρ)`, and exactness
  has `LogCohomology.ofCohomology` in the place of `j_*`. `gysin` also needs no comparison, since its
  target is `H^•(A)`. `DeRham/Maps` is the one file that uses `thm:dr-comparison`: `residue T hUnits h`
  is `H(ρ)` after the inverse of `logToLocalizationEquiv`, and its public face is
  `residue_toCohomology` and `residue_mk_of_mem_logForms`. Its proofs transport the statements about
  `H^•(L)` along that equivalence, so no argument on forms is repeated there.
- **Degrees.** The maps are on total cohomology, with the shifts `isHomogeneousOfShift_gysin` and
  `LogCohomology.isHomogeneousOfShift_residue` for `Cohomology.grading`, so that negative degrees need
  no case analysis. Exactness in a degree follows from total exactness by
  `IsHomogeneousOfShift.exact_iff_forall_mem`.
- **Maps of pairs are one `Prop`.** `IsPairHom f π f' π' φ ψ χ` says that `φ`, `ψ` and `χ` commute with
  the structure maps and that `φ f` is associated to `f'`. It does not require any pair to be smooth,
  so that `logMap` and `IsPairHom.map_theta` make sense for any localization. No flatness appears, and
  no exact sequence is tensored. `DivisorPair.Hom.isPairHom` is the case of a morphism of divisor
  pairs, and `IsPairHom.of_associated` is the existence of `ψ` and `χ` for any `φ`, unique by
  `IsPairHom.closed_eq` and `IsPairHom.compl_eq`. `IsPairHom.of_associated_id` is how a statement
  becomes one about associated equations.

### Pole order and logarithmic comparison

`DeRham/Pole/Cartan` defines contraction by a derivation, its Lie derivative, and their extension
to arbitrary localizations. `Pole/Euler` restricts contraction by `E = f v` to logarithmic forms
and descends it to the actual `A`-module quotient `V = L / f L`. Normality is the precise
congruence `v(f) = 1 + f h`; it gives `dJ + Jd = 0` and `WJ + JW = id` on `V`. Smoothness is not
needed for these operator identities. `logQuotientPower` is the image of the homogeneous
logarithmic piece, with typed restrictions of `d`, `J`, and `W`.

`Pole/Filtration` defines actual submodules of localized forms: `poleForms m = f⁻ᵐ L` and
`poleFiltration m n = f⁻ᵐ Lⁿ`. Pole stages increase and exhaust total forms and each exterior
degree; `Pole/Complex` packages their restricted differentials and inclusions as complexes and
chain maps. The filtration and its quotient identifications require neither regularity nor
smoothness, because denominator clearing happens in the localized module itself.
`Pole/Quotient` uses successor indexing: `PoleQuotient m = F_(m+1) / F_m`. Multiplication by
`f⁻⁽ᵐ⁺¹⁾` gives `poleQuotientEquiv : V ≃ₗ[A] PoleQuotient m`, preserving homogeneous pieces.
`poleQuotientProjection` is the canonical surjection from the upper stage to `V`, with kernel
the preceding stage, and intertwines `d` with `poleQuotientDifferential = d̄ − (m+1) W`.

`Pole/Contraction` uses only `IsUnit (m+1 : k)` and a normal derivation to construct the actual
operator `−(m+1)⁻¹ J`; its homotopy identity is proved on `V` and on the actual pole quotient,
with degree lowering and degree-zero vanishing. `Algebra/ComplexReduction` is independent of
forms and proves both cocycle and primitive reduction for arbitrary short exact sequences of
complexes over any ring, plus a total-module formulation for a square-zero differential.
`Pole/Reduction` applies that formulation and finite induction on a pole bound.
`Pole/Comparison` proves bijectivity of the inclusion-induced total cohomology map and packages
it as `logToLocalizationEquiv`. Its forward map is canonical; the normal derivation occurs only
in the proof of bijectivity. Positive integers need only be units in `k`, so neither a field nor
a nonzero coefficient ring is assumed. A smooth principal pair supplies the normal derivation.

`Pole/Degree` proves preservation and reflection of the natural and integer gradings and gives
`logToLocalizationDegreeEquiv` and `logToLocalizationGradingEquiv`. Their forward and inverse
formulas identify the canonical map in each degree. The full algebra equivalence is independent
of the coefficient-unit proofs and the chosen closed-divisor presentation or certificate.
It also packages the algebraic comparison as the chain-map statement
`DeRham.logToLocalization_quasiIso`.

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
- **The cohomology of the logarithmic forms** is `LogCohomology k f T`, in `DeRham/Log/Cohomology`.
  It is not generic in a dg subalgebra, since a shared layer would wrap every lemma above for one
  other use. It is built the same way: `logCycles k f T` is the subalgebra `L ⊓ cycles k T`,
  `logBoundaries k f T` is the `TwoSidedIdeal` of the `d y` for `y ∈ L`, and it is their
  `RelationQuotient`. The grade involution preserves `L`, which gives `x ∧ dy = d (σ x ∧ y)`, and `L`
  is homogeneous, which gives the grading. A class is `LogCohomology.mk x hx`, with
  `x : logForms k f T` and `hx : logD k f T x = 0`, since that is the type `logResidue` takes. The
  map of `thm:dr-comparison` is `LogCohomology.toCohomology k f T`, and
  `bijective_toCohomology_of_forall` says what its bijectivity means for forms.

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
  `TwistedCohomology.map` and `TwistedCohomology.grading`.
- **The twisted maps.** `TwistedCohomology.twistMap w f` is `T^w` times `f.baseChange k[T;T⁻¹]`, for
  any `k`-linear map of `k`-modules. `TwistedCohomology.gysin L h` and
  `TwistedCohomology.residue L hUnits h` are the twists by `T` and `T⁻¹` of the maps of `DeRham/Maps`,
  for any commutative ring `k` in which positive integers are units, with no `SmoothAlg` and no
  `DivisorPair`. Exactness is `exact_twistMap`: `k[T;T⁻¹]` is free over `k`, hence flat, and `T^w` is
  a unit, so no bidegree-by-bidegree argument and no field are needed. `residue_mul_map` holds for
  every `α`, with no degree hypothesis, since `T` is central.
- **The instance.** `ordinaryTheory k`, in `DeRham/Instance`, has exactly the hypotheses
  `[Field k] [CharZero k]`, and they enter only through `isUnit_natCast_add_one`. Its fields at a
  divisor pair `P` are the twisted maps at `P.compl`, with `P.isSmoothPrincipalPair` and, for a
  morphism `F`, `F.isPairHom`: nothing is transported. It is a `def`, for the reason above. To compute
  in it, use `twistedClass w c : (ordinaryTheory k).C.obj A`, the class `T w ⊗ₜ c` typed in the
  theory, which is `rfl` to it by `twistedClass_apply`: `mem_grading_ordinaryTheory_iff`,
  `map_twistedClass`, `twistedClass_mul_twistedClass`, `gysin_twistedClass`, `residue_twistedClass`,
  `stdResidue_twistedClass` and `evalOne_twistedClass` let `simp` compute with no change of type.
  `ordinaryTheory_gysin` and the lemmas after it identify the fields with the twisted maps by `rfl`.
  `Examples/DeRhamInstance` checks this, and builds the equivalence of `cor:dr-affine` on the
  instance.

### The corollaries

- **No theory in the statements.** `DeRham/Corollaries` states the structure theorems for
  `DeRham.Cohomology k A` and its degrees `Cohomology.degree k A q`. The corollary statements mention
  neither `OrdinaryTheory` nor `k[T;T⁻¹]`, except `affineEquiv_apply` and `projectiveEquiv_apply`,
  which say how the maps are built. The hypotheses are `[Field k] [CharZero k]` and those of the
  arrangement, and nothing else.
- **Total cohomology first, the direct sum second.** `affineEquiv 𝒜 : OSAlgebra k 𝒜 ≃ₐ[k]
  Cohomology k (complement 𝒜)` is the primary form, as total cohomology is everywhere in
  `DeRham`, with `affineEquiv_mem_degree_iff` for the grading. `affineDirectSumEquiv` is the
  blueprint's display `⨁ q, H^q_dR`, obtained by composing with `decomposeAlgEquiv`, and
  `affineDegreeEquiv q` is the piece of degree `q`. The projective forms are the same with
  `projective` in their names. Each is the main theorem's diagonal equivalence followed by the
  inverse of `TwistedCohomology.diagonalEquiv`.
- **The class `[du/u]`.** `dlogClass k u` is `Cohomology.mk (dlog k u) _`, for any algebra over any
  commutative ring, with `k` and `u` explicit. The generator formulas are stated with it:
  `affineEquiv_generator` (`simp`, the chosen equation), `affineEquiv_generator_zeroLocus`
  (`simp high`) and `affineEquiv_generator_of_isEquation` (any equation), as for
  `OrdinaryTheory.realizationOverR`, and `projectiveEquiv_difference` and its `_of_ker_eq` form.
- **`lem:dr-tau`.** `ordinaryTheory_tau` is proved by `eq_tau_of_mem_grading` from
  `residue_dlogClass`, the residue of `[df/f]` for any smooth principal pair. Since
  `(standardPair A).compl` is `laurent A` only at default transparency, its last step is an `exact`.
  `ordinaryTheory_logClass` is naturality. It is not a `simp` lemma: `simp` rewrites arguments first,
  and the generic lemmas about `logClass`, such as `residue_logClass_eqnUnit`, would stop firing on
  the instance. `evalOne_logClass` is the `simp` form used to remove `t`.

The chapter `OrlikSolomonBook/DeRham.lean` records the current status of each node. Its opening
says that the instance, the two corollaries and all eight worked regressions are formalized, and
names what they rest on. The first page, `Organization`, the chapter on the
axioms, the status page and `README.md` describe the resulting state: one nonzero value of
`OrdinaryTheory` is constructed, the de Rham instance for fields of characteristic zero; the affine
and projective theorems hold unconditionally for algebraic de Rham cohomology over such fields, as
`DeRham.affineEquiv` and `DeRham.projectiveEquiv`; the theorems remain conditional for every other
theory; and the checks against singular and `ℓ`-adic cohomology are by hand. The first page shows
the two corollaries as elaborated Lean, with `#print axioms`. The docstrings of `OrdinaryTheory`,
`BridgeData/Basic` and `Examples/Sanity` also name the instance. The build does not check that
prose, so keep it current as nodes land.

## The geometric refactor

`blueprint/geometric_refactor_blueprint.tex` is authoritative for the mathematics of milestone M6.
It makes cohomology a contravariant functor on a category of smooth `k`-schemes, makes the
complements the actual open subschemes of `Spec Sym(V*)` and `Proj Sym(W*)`, and reuses every proved
algebraic result through the equivalence between smooth algebras and smooth affine schemes. It adds
no field to the axioms, keeps the hypotheses of both structure theorems, and changes no conclusion.
Stage G0 (#107, #108) is formalized to the extent indicated below: `def:geo-domain`, `thm:geo-affine-duality`,
`lem:geo-affine-pairs`, `lem:geo-products` and `thm:geo-units`, described in "Schemes, domains and
affine duality" below, and `def:geo-divisor-pair`, `def:geo-pair-hom`, `thm:geo-cartesian` and
`thm:geo-pair-duality`, described in "Principal pairs" below. The Cartesian node remains partly
formalized: its Tor-sheaf and conormal comparisons are not stated. Stage G1 is formalized:
`def:geo-theory`, `lem:geo-restriction`, `lem:geo-empty`, `thm:geo-to-algebraic` and
`thm:geo-from-algebraic` (#109), described in "Geometric cohomology and affine transport" below,
and `def:geo-supports` and `thm:geo-bridge` (#110), described in "Geometric supports and purity"
below. Stage G2 is
formalized: `def:geo-affine-space`, `def:geo-complement`, `thm:geo-complement-spec`, `thm:geo-deletion`
and `thm:geo-small-targets` (#111), described in "Arrangement complements on schemes", and
`def:geo-projective` and `thm:geo-projective-geometry` (#112, with its affine sides from #111),
described in "Projective complements on schemes". Stage G3 is formalized: the logarithms
`def:geo-log`, `thm:geo-log-laws` and `thm:geo-gm-product` (#113), described in "Geometric
logarithms" below, and the structure theorems `thm:geo-affine` and `thm:geo-projective` (#114),
described in "The geometric structure theorems" below. The transport rule `thm:geo-transport-all`
is partly formalized, by the comparison `transportAffineDevelopment` and its laws, since a rule
about every old statement is not one Lean statement. Stage G4 (#115), `lem:geo-module-gluing`,
`def:geo-forms-sheaf` and `thm:geo-forms-comparison`, is formalized as described in "Relative
forms as sheaves". Stage G5 (#116) is formalized as described in "The de Rham instance on affine
schemes": `def:geo-dr-cohomology`, `cor:geo-dr-arrangements` and `thm:geo-dr-instance`.
Stage G6 (#117), `thm:geo-log-sheaves`, proves the logarithmic sheaf sequence and local comparison,
including agreement of the instance's Gysin and residue maps on global sheaf representatives.
The worked geometric regressions and acceptance consumers of #118 use the actual scheme
objects and sheaf maps. They include the two-chart Čech complex of the projective line; no
non-affine de Rham instance or arbitrary-cover independence is asserted.

The namespace is `OrlikSolomon.Geometric`. Inside it, the proposed names `OrdinaryTheory`,
`DivisorPair` and `DeRham` resolve to the geometric declarations rather than to the existing ones,
so refer to the existing ones by their full names, as the blueprint's signatures do:
`OrlikSolomon.OrdinaryTheory`, `OrlikSolomon.DivisorPair`, `OrlikSolomon.DeRham.ordinaryTheory`.

### Decisions

- **Admissible domains.** A theory takes a domain (`def:geo-domain`): a full, isomorphism-closed
  subcategory of smooth schemes over `Spec k` that contains every smooth affine scheme and is closed
  under products with `𝔸¹` and `𝔾ₘ`. Its morphisms are all morphisms over `Spec k`, with no
  smoothness or flatness condition. The canonical domains are all smooth schemes, smooth separated
  schemes of finite type, and smooth affine schemes. A theory restricts to a smaller domain with no
  input (`lem:geo-restriction`), so a theory on all smooth schemes applies directly. Membership of
  smooth affine schemes is supplied by instances, never by a hypothesis on an arrangement.
- **Contravariance.** The value at `X` is `T.C.obj (op X)` and pullback along `g` is `T.C.map g.op`.
  The blueprint suggests the abbreviations `obj T X` and `pull T g`, so that user lemmas do not show
  coercions of opposite objects.
- **Principal pairs, with reversed morphisms.** `Geometric.DivisorPair` keeps a global regular
  equation, certified as in the algebraic `DivisorPair`, and is not a general Cartier divisor
  (`def:geo-divisor-pair`). Its morphisms run in the geometric direction: `g : P ⟶ Q` has scheme
  maps from the parts of `P` to those of `Q`, and the unit `u` in `g_X^* f_Q = u f_P` is a global
  unit on the source `X_P`. Its existence is a `Prop`, not data. So the anti-equivalence with
  algebraic pairs (`thm:geo-pair-duality`) reverses morphisms. The condition on equations says that
  the source divisor is the scheme-theoretic pullback of the target divisor, and it needs no
  flatness (`thm:geo-cartesian`).
- **The algebraic structure stays the kernel interface.** `OrlikSolomon.OrdinaryTheory` is not
  retired. `toAlgebraic` restricts a geometric theory on any domain to it, by evaluating on spectra
  (`thm:geo-to-algebraic`), and `ofAlgebraic` transports a value of it to the affine domain, by
  evaluating on global sections (`thm:geo-from-algebraic`). The geometric theorems apply the
  existing ones to `T.toAlgebraic` and compose with the comparisons `s_𝒜` and `s_P` of a complement
  with the spectrum of its existing ring: the public `affineEquiv_apply` is `Φ^geo = s_𝒜^* ∘ Φ`,
  where `Φ` is the existing equivalence for `T.toAlgebraic`. Any other construction is identified
  with it by the uniqueness on generators. The existing public theorems remain, and the geometric
  ones are additional entries.
- **The de Rham instance is on the affine domain.** It is `ofAlgebraic (DeRham.ordinaryTheory k)`
  (`thm:geo-dr-instance`), and its cohomology is `OrlikSolomon.DeRham.Cohomology` of the global
  sections, with the comparison to the cohomology of global forms as its specification
  (`def:geo-dr-cohomology`). The sheaf of forms and the sheaf logarithmic comparison
  (`thm:geo-log-sheaves`) are in scope for every scheme, but they are inputs to an instance on
  schemes that are not affine, not such an instance. That instance needs hypercohomology, as the
  example of `ℙ¹` in `prop:geo-nonaffine` shows, and it is a separate project, not part of M6.
- **`Geometry/ProjectiveScheme` stops being a leaf for the new consumers.**
  `Geometry/Schemes/Projective` and the modules built on it may import it. The algebra, the
  combinatorics, the proof of the structure theorems and the algebraic de Rham instance still may
  not import it or anything in the scheme layer, which depends on them and not conversely.
- **The implementation traps carry over.** Keep named geometric objects, pairs, functors and
  theories as `def`s with comparison and `simp` lemmas, keep typed residue and Gysin wrappers, keep
  `mapOverR`, `gysinOverR` and `residueOverR` for the case `R = B`, and keep the coefficient on the
  left in `TwistedCohomology`. Prove one set of naturality lemmas for `s_𝒜` and `s_P` and use them,
  rather than rewriting through `Spec` and `Γ`.

### Schemes, domains and affine duality

These are the conventions of `Geometry/Schemes/`, on which every later stage builds.

- **Schemes over the base.** `S = Spec k` is `Spec (.of k)` for a commutative ring `k : Type u`, with
  no other hypothesis, and an `S`-scheme is an object of `Over (Spec (.of k))`. Products are Mathlib's
  cartesian monoidal product `⊗` on `Over S`, which is `Limits.pullback`, with projections `fst` and
  `snd`. `Geometric.spec A : Over S` is `Spec A` for a `k`-algebra `A`; it is Mathlib's `algSpec`
  (`specFunctor_eq_algSpec`), restated so that its components unfold (next item). `specMap φ` is
  `Spec` of a map of algebras, contravariant.
- **Named objects are `@[implicit_reducible] def`s.** Lean now checks implicit arguments, including
  the source and target objects of a morphism, at *implicit* transparency, while `simp` indexes and
  matches explicit arguments at reducible transparency. A plain `def` such as `(spec A).left` is
  not unfolded in the first check, so `rw` and `simp` fail on `g ≫ (spec A).hom` with the message
  that the target "is not type-correct under the `implicit` transparency level"; an `abbrev` is
  unfolded in the second, which is the old failure of `simp` indexing recorded under "Objects and
  pairs are `def`s". `@[implicit_reducible]` is unfolded in the first and not in the second, so it
  is the right annotation for objects and object-valued functors: `spec`, `affineLine`, `gm`,
  `affineSpace`, `complement`, `projectiveComplement`, `specFunctor`, `globalSectionsFunctor`,
  `SmoothDomain.specFunctor` and `affineGlobalSectionsFunctor`. Mathlib marks `Over.mk`,
  `ObjectProperty.homMk` and `ObjectProperty.lift` the same way. Mathlib's `algSpec` is marked too,
  but its object passes through functors that are not, which is why `spec` restates it. Morphisms
  are ordinary `def`s.
- **Objects of a domain and `globalSections` are `@[instance_reducible] def`s** (#128). These are
  the `D.Obj` wrappers of an `S`-scheme, `SmoothDomain.ofAffine`, `spec`, `point`, `affineLine`,
  `gm`, `prodAffineLine`, `prodGm`, `affineSpace`, `complement` and `projectiveComplement`. That
  level also unfolds at instance transparency, where type class search and `rw` work, and still not
  at the reducible transparency at which `simp` indexes lemmas. So `Γ((D.spec A).obj.left, ⊤)`,
  `Γ((spec A.obj).left, ⊤)` and `globalSections (D.spec A).obj` are one type for `Units.map`,
  products and `algebraMap`, while every `simp` key is unchanged: the keys of all `simp` lemmas
  and instances of the library were identical before and after the change. `@[reducible]` is wrong
  here, because it changes the keys: a reducible `globalSections` loses its `k`-algebra instance,
  and reducible domain objects make `simp only [SmoothDomain.gmHom_appTop_gmCoord]` silently stop
  firing. A new object of a domain built from a scheme gets `@[instance_reducible]`; the
  regression `example`s at the ends of `Geometry/Schemes/Basic`, `Units` and `Complement/Basic`
  check the rule.
- **Global sections are bundled.** `globalSections X : CommAlgCat k` is `Γ(X, 𝒪_X)` with the
  structure map `k ≅ Γ(S) → Γ(X)`; its carrier is `Γ(X.left, ⊤)` at instance transparency, so an
  element of one is an element of the other, and `algebraMap k (globalSections X) c * f` elaborates
  for `f : Γ(X.left, ⊤)`. It is not an instance on `Γ(X.left, ⊤)`: Mathlib has an instance for
  affine `X`, built through `X.isoSpec`, that agrees with it only propositionally. Pullback is
  `globalSectionsMap g`, with `globalSectionsMap_apply`.
- **Domains.** `SmoothDomain k` holds an `ObjectProperty` of `Over S` and the closure proofs of
  `def:geo-domain`; `D.Obj` is its full subcategory, so morphisms are all `S`-morphisms, and
  domains are ordered by inclusion, with `aff k ≤ D ≤ all k`. The canonical domains are `all`, `aff`
  and `sft`; finite type is `QuasiCompact`, since smooth morphisms are locally of finite
  presentation. Smooth affine schemes enter any domain through `D.ofAffine X`, whose membership is
  found from the instances `[IsAffine X.left] [Smooth X.hom]`, and `D.spec A` for `A : SmoothAlg k`
  needs no proof at all. The base is `D.point`, terminal, with `D.specPointIso` from `Spec k`.
  `D.specFunctor : SmoothAlg k ⥤ D.Objᵒᵖ` is fully faithful; it is the functor through which
  `toAlgebraic` evaluates a theory, so a geometric theory's `T.C.obj (op (D.spec A))` is the
  algebraic theory's value at `A`.
- **Affine duality.** `specHomEquiv X A : (X ⟶ spec A) ≃ (A ⟶ globalSections X)` holds for every
  `S`-scheme `X`; it is built from `Scheme.toSpecΓ`, with explicit formulas
  (`specHomEquiv_apply_apply`, `specHomEquiv_symm_left`), not from Mathlib's
  `algΓAlgSpecAdjunction`, whose unit and counit come with no formulas. Use `hom_ext_spec` to
  compare maps into `Spec A`. The equivalence `smoothAffineEquivalence k : SmoothAlg k ≌ (aff k).Objᵒᵖ`
  has functor `(aff k).specFunctor`, unit `η⁻¹ = globalSectionsSpecIso` (from `ΓSpecIso`) and counit
  `ε = specGlobalSectionsIso` (from `Scheme.isoSpec`), each with named naturality and triangle
  lemmas. `affineHomEquiv` is pullback of global sections for an affine target.
- **Zero schemes and basic opens.** `zeroScheme f` is the closed subscheme of Mathlib's ideal sheaf
  `principalIdealSheaf f = ofIdealTop (Ideal.span {f})`, not the fiber product `X ×_{𝔸¹} 0`, because
  Mathlib's closed subschemes are phrased through kernels (`Scheme.Hom.ker`,
  `IsClosedImmersion.lift`, `IsClosedImmersion.isIso_lift`). So the certificate of a closed map in
  `def:geo-divisor-pair` can be the proposition `IsClosedImmersion i ∧ i.ker = principalIdealSheaf f`,
  translated on affine schemes by `ker_eq_principalIdealSheaf_iff`, and that of an open map
  `IsOpenImmersion j ∧ j.opensRange = X.basicOpen f`, with Mathlib's `X.basicOpen f`. Regularity is
  `IsRegularSection f`: multiplication by `f` is injective over every open (`isRegularSection_iff`
  on affine schemes).
- **Products, sections and units.** `affineLine k` and `gm k` are `spec` of `k[X]` and `k[T;T⁻¹]`;
  `gm k` is a commutative group object through Mathlib's Hopf algebra on Laurent polynomials. Maps
  to them are functions and units for every `S`-scheme (`homAffineLineEquiv`, and the group
  isomorphism `unitsEquivHomGm`, inverse to pullback of `gmCoord`); compare maps into them with
  `homAffineLineEquiv.injective` and `hom_ext_gm`. The comparisons `specPolynomialIso` and
  `specLaurentIso` of `lem:geo-products` are built from these universal properties rather than from
  pushouts of rings. They hold for every `A : CommAlgCat k`, with the algebras `polynomialAlg A` and
  `laurentAlg A` and their maps `polynomialAlgC`, `polynomialAlgLift`, `laurentAlgLift`,
  `polynomialAlgToLaurent`. `SmoothDomain.specPolynomialIso` and `specLaurentIso` specialize them to
  `A : SmoothAlg k`, with every compatibility restated for the existing `polynomialC`,
  `polynomialLift`, `laurentSection` and `polynomialToLaurent`, so that an algebraic axiom is the
  conjugate of a geometric one (`SmoothDomain.specPolynomialIso_hom_prodAffineLineFst`). The
  geometric standard pair is `zeroSection X`, `X ◁ gmToAffineLine k` and the coordinate `prodCoord X`,
  for every `S`-scheme `X`.

### Principal pairs

These are the conventions of `Geometry/Schemes/PrincipalPair`, which the cohomological stages use for
the Gysin and residue maps.

- **The record.** `Geometric.DivisorPair D` has objects `ambient`, `closed`, `compl` of `D.Obj`,
  maps `i : closed ⟶ ambient` and `j : compl ⟶ ambient`, an equation `eqn : Γ(ambient.obj.left, ⊤)`,
  and the data-free certificates `isRegularSection_eqn`, `[IsClosedImmersion i.hom.left]` with
  `ker_i : i.hom.left.ker = principalIdealSheaf eqn`, and `[IsOpenImmersion j.hom.left]` with
  `opensRange_j : j.hom.left.opensRange = ambient.obj.left.basicOpen eqn`. The field names are those
  of the algebraic `OrlikSolomon.DivisorPair`. The universal properties are `closedLift` and
  `complLift`, and `eqnUnit` is the equation as a unit on `compl`. A unit equation is allowed: then
  `closed` is empty (`isEmpty_closed_of_isUnit`) and `j` is an isomorphism (`isIso_j_of_isUnit`).
- **Morphisms.** `g : P ⟶ Q` has `ambient`, `closed`, `compl` in the geometric direction, with
  `i_comp : P.i ≫ g.ambient = g.closed ≫ Q.i`, `j_comp` likewise, and
  `associated_eqn : Associated (g.ambient.hom.left.appTop Q.eqn) P.eqn`, which is literally the field
  of the algebraic morphism `Γ(Q) ⟶ Γ(P)`; `Hom.exists_unit_mul` restates it as the blueprint's
  `g^* f_Q = u f_P`. A morphism is determined by its ambient map (`hom_ext`), and `homOfAmbient`
  builds one from a map of ambients. Pullback of functions along a composite is
  `SmoothDomain.appTop_comp_apply`.
- **Cartesian squares.** `associated_iff_ker_pullback_fst` and `associated_iff_isPullback` are
  `thm:geo-cartesian`, through the scheme-level `associated_iff_principalIdealSheaf_eq` (local ratios
  glue by regularity) and `ker_pullback_fst_of_ker_eq`. Every morphism has Cartesian squares
  (`Hom.isPullback_closed`, `Hom.isPullback_compl`) and a regular pulled-back equation
  (`Hom.isRegularSection_appTop`), which is the Tor-independence. Conormal sheaves are not formalized:
  the conormal isomorphism of the blueprint is the unit of `Hom.exists_unit_mul`.
- **Named pairs** are `@[implicit_reducible] def`s whose object equations (`standardPair_ambient`,
  `spec_closed`, ...) are not `simp` lemmas, while those of their maps and equations are:
  `withEqn` (a unit multiple of the equation, with `withEqnIso` given by identities), `ofLE` and
  `functorOfLE` (a pair in a larger domain), `standardPair D X` (for every object `X`, affine or not,
  with `standardPairMap`, `standardPairFunctor`), `spec D P` and `globalSections P`. The morphism
  `toStandard P : P ⟶ standardPair D D.point` is `z ↦ f` with multiplier `1`, the geometric
  `fromStandard`, with `toStandard_compl` the map of the unit `f|_U`.
- **Duality.** `DivisorPair.specFunctor D : OrlikSolomon.DivisorPair k ⥤ (DivisorPair D)ᵒᵖ` sends a
  pair to `spec D P` and `F` to `(specMap D F).op`, whose components are
  `(D.specFunctor.map F.ambient).unop` and so on: a geometric theory on `D` evaluates algebraic pairs
  and morphisms through it, and `spec_eq_ofLE` says the result does not depend on the domain. For a
  pair in `aff k`, `globalSections P` has components `(affineGlobalSectionsFunctor k).obj (op _)` and
  maps `(affineGlobalSectionsFunctor k).map P.i.op`; `globalSectionsFunctor k` is functorial. The
  equivalence `affinePairEquivalence k : OrlikSolomon.DivisorPair k ≌ (DivisorPair (aff k))ᵒᵖ` has
  unit `unitIso P` with components `(smoothAffineUnitIso k).hom.app _` and counit
  `(counitIso Q).op` with components `((smoothAffineCounitIso k).hom.app (op _)).unop`, so the pair
  isomorphisms needed by `thm:geo-from-algebraic` have the objectwise `η` and `ε` as components.
  `specStandardPairIso D A` identifies `spec D (standardPair A)` with `standardPair D (D.spec A)`
  through `D.specPolynomialIso A`, `𝟙` and `D.specLaurentIso A`. Inside
  `namespace OrlikSolomon.Geometric.DivisorPair` the pair-level `spec`, `specMap`, `specFunctor`,
  `globalSections`, `globalSectionsMap` and `globalSectionsFunctor` shadow the object-level names, so
  write `Geometric.spec` and so on there.

### Arrangement complements on schemes

These are the conventions of `Geometry/Schemes/Complement` (#111), on which the geometric affine
structure theorem builds.

- **Affine space.** `affineSpace k V` is `spec (CommAlgCat.of k (CoordinateRing k V))` for every
  `V`, smooth for finite-dimensional `V`. The function of an affine function is
  `affineSpaceCoord f`, the morphism of an affine map is `affineSpaceMap k a`, `Spec` of
  `CoordinateRing.pull a`, and maps into `𝔸_V` are compared with `hom_ext_affineSpace`. The
  hyperplane scheme `hyperplaneScheme H` is `Spec` of the quotient by `hyperplaneIdeal H`, the ideal
  of all equations, so it involves no choice; `ker_hyperplaneι` holds for every equation, and
  `hyperplaneSchemeIso hH : 𝔸_{H.direction} ≅ 𝐇` turns the immersion into `𝔸_{chart H}`. A basis
  enters only `affineSpaceIsoAffineSpace`, the comparison with Mathlib's `𝔸(ι; Spec k)`.
- **The complement.** `complement 𝒜` is the open subscheme of `𝔸_V` on `complementOpens 𝒜`, the
  intersection of the complements `hyperplaneComplement H` of the supports of the hyperplane
  schemes, and `complementι 𝒜` is its open immersion. It is the basic open of every product of
  equations (`complementOpens_eq_basicOpen`), and all of `𝔸_V` for the empty arrangement. It needs
  no finite dimension; smoothness does. In a domain, `D.complement 𝒜` needs
  `[FiniteDimensional k V]` and no hypothesis on `𝒜`.
- **The comparison `s_𝒜`.** `complementIsoSpec 𝒜 : complement 𝒜 ≅ spec (CommAlgCat.of k 𝒜.ComplementRing)`
  is over `𝔸_V` (`complementIsoSpec_hom_comp`) and is the only such isomorphism
  (`eq_complementIsoSpec`), so it involves no equations. `D.complementIsoSpec 𝒜` has target
  `D.spec (SmoothAlg.complement 𝒜)`, where a geometric theory restricts to the algebraic one: the
  affine structure theorem on `U_𝒜` is the existing one composed with pullback along it. Its
  generators correspond by `D.complementIsoSpec_hom_appTop_complementUnit`: the existing
  `SmoothAlg.complementUnit 𝒜 f hf` is the restriction `Geometric.complementUnit 𝒜 f hf` of `f̃`, as
  an equation of global sections, and as an equation of units by
  `D.map_complementIsoSpec_hom_complementUnit`.
- **Maps of complements.** Each is `complementHom F` for a map `F` of the existing rings, that is,
  `s_𝒜 ≫ Spec F ≫ s_ℬ⁻¹`, so one set of naturality lemmas serves them all
  (`complementHom_comp_complementIsoSpec_hom`, `complementHom_comp_complementι`,
  `complementHom_appTop`): `complementMap`, `complementInclusion`, `complementIso`,
  `complementRestriction`, `affineImageMap` and `normalizedSliceMap`. The affine ones are
  determined by their composite with `complementι` (`hom_ext_complement`,
  `complementMap_comp_complementι`). Their domain forms are `ObjectProperty.homMk` and `isoMk`, and
  their squares with `D.complementIsoSpec` are stated with `D.specFunctor.map` of the existing
  `SmoothAlg` maps, such as `SmoothDomain.complementMap_comp_complementIsoSpec_hom`.
- **The deletion pair.** `DivisorPair.deletionPair D 𝒜 hH hf` has objects `D.complement` of
  `𝒜.deletion H`, `𝒜.restriction H` and `𝒜`, maps `D.complementRestriction` and
  `D.complementInclusion`, and equation `f̃_H|_{U_𝒜'}`. Its certificates are transported from
  `spec D` of the existing deletion pair along the comparisons by `DivisorPair.ofIso`, not proved
  again. `deletionPairIsoSpec` is the isomorphism with `spec D (OrlikSolomon.DivisorPair.deletionPair
  𝒜 hH hf)` whose components are `(D.complementIsoSpec _).hom`, so a theory's residue and Gysin maps
  on the geometric pair are the existing ones by naturality along it, and `deletionPairIso` changes
  the equation by identities. The certificates without a domain are `isRegularSection_deletion`,
  `ker_complementRestriction` and `opensRange_complementInclusion_deletion`, and
  `isPullback_complementRestriction` is the scheme-theoretic fiber product `U_𝒜' ×_{𝔸_V} 𝐇`.
- **Names.** `Geometric.complement`, `complementUnit`, `complementMap`, `complementInclusion`,
  `complementIso` and `complementRestriction` share their last component with `SmoothAlg`
  declarations, so the scheme layer does not open `SmoothAlg`. `Geometric.complementι` clashes with
  `ProjectiveArrangement.complementι` under `open ProjectiveArrangement`, which is why the cone and
  decone composites are in `Geometry/Schemes/Decone` and not in `Geometry/Schemes/Projective`.

### Projective complements on schemes

These are the conventions of `Geometry/Schemes/Projective` (#112).

- **The objects.** `projectiveSpace k W` is `Proj Sym(W*)` over `S`, with the structure map
  `projToSpec` through Mathlib's `Proj.toSpecZero`. `projectiveComplement P` is the open subscheme
  `complementOpen P` of it, for every `P`, and is not an object of any domain in general. It is the
  intersection of the charts `D₊(ℓ)` of all equations (`complementOpen_eq_iInf`), which depend only
  on the kernel (`basicOpen_coord_eq_of_ker_eq`), and for empty `P` its open immersion is an
  isomorphism (`isIso_projectiveComplementι`). `ℙ(W)` is smooth for finite-dimensional `W`
  (`smooth_projectiveSpace_hom`), so `U_P` is smooth for every `P`, and empty when `W = 0`.
- **The comparison `s_P`.** `projectiveComplementIsoSpec P` is `complementOpenIso P` with the
  certificate `complementOpenIso_hom_specMap` that it is over `S`, for `[Nonempty P]` and any `W`.
  Its target is `spec (CommAlgCat.of k P.ComplementRing)`. It does not depend on the equations
  chosen inside `complementOpenIso` (`projectiveComplementIsoSpec_inv_left_comp_ι`, from
  `complementι_eq_awayι_of_ker_eq`). `formProduct` is `@[implicit_reducible]` so that the chart of
  `complementOpen P` and the ring of `awayEquiv` agree at implicit transparency.
- **In a domain.** `D.projectiveComplement P` needs `[FiniteDimensional k W] [Nonempty P]` and no
  proof. `D.projectiveComplementIsoSpec P` has target exactly
  `D.spec (SmoothAlg.projectiveComplement P)`, the object at which a geometric theory restricts to
  the algebraic one, so the projective structure theorem on `U_P` is the existing one composed with
  pullback along it. The domain maps are `ObjectProperty.isoMk` and `homMk` of the maps over `S`,
  and their lemmas are transferred with `ObjectProperty.hom_ext`.
- **The cone and the decone.** In `Geometry/Schemes/Projective`, `V_P` and `U_{decone P}` are the
  spectra of the existing rings `P.cone.ComplementRing` and `(P.decone ℓ₀).ComplementRing`.
  `Geometry/Schemes/Decone` composes them with `s_𝒜` to the actual complements:
  `coneComplementProjection`, `coneComplementIsoProdGm` and `projectiveDeconeComplementIso`, with
  their domain forms and squares with `s`. The projection
  `coneProjection P : V_P → U_P` is `Spec` of `toCone` followed by `s_P⁻¹`, with no choice; the
  square with `SmoothAlg.projectiveToCone` is
  `SmoothDomain.coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom`.
  `coneIsoProdGm hℓ₀` has first coordinate `coneProjection P` and second coordinate `ℓ₀`.
- **Functions.** `projectiveRatio hℓ hℓ'` is the unit `ℓ / ℓ'` of `Γ(U_P)`, the pullback along `s_P`
  of `ratioUnit`, and `specUnit u`, in `Geometry/Schemes/Units`, is the unit of `Spec A` given by
  `u : Aˣ`. Lemmas about functions in a domain are stated as equations of global sections, such as
  `SmoothDomain.coe_projectiveRatio`, with unit forms such as
  `SmoothDomain.map_projectiveComplementIsoSpec_hom_projectiveRatioUnit`, proved by `Units.ext`.
  Since the objects of a domain unfold at instance transparency (above),
  `Units.map g.hom.left.appTop.hom (specUnit u)` for `g : X ⟶ D.spec A`, and products across
  `Γ((D.spec A).obj.left, ⊤)` and `Γ((spec A.obj).left, ⊤)`, elaborate.

### Geometric cohomology and affine transport

`Cohomology/Geometric/Axioms` defines `Geometric.OrdinaryTheory D ℬ` with exactly the old 22 fields.
Its `C` is `D.Objᵒᵖ ⥤ AlgCat B`; `obj X` is `C.obj (op X)` and `pull f` is `C.map f.op` as an algebra
map. The `R`-algebra structure remains a field with scalar-tower coherence, and the grading uses
`R`-submodules with the sign `Prod.fst`. `mapOverR`, `gysinOverR` and `residueOverR` retain the
specified scalar structure when `R = B`. `standardResidue` and `standardGysin` are typed by
`D.prodGm X`, `X` and `D.prodAffineLine X`, with typed shift, exactness and projection lemmas.
`restrict h` copies all fields along `ObjectProperty.ιOfLE h`; the point and product schemes agree
by construction.

`Cohomology/Geometric/Transport` defines `toAlgebraic` by `D.specFunctor ⋙ T.C` and `ofAlgebraic E`
by `affineGlobalSectionsFunctor k ⋙ E.C`. The point and affine-line conditions use the canonical
comparison isomorphisms, including an explicit `Γ(X)[z] ≅ Γ(X × 𝔸¹)` respecting constants. The pair
fields are precisely those of `DivisorPair.spec` or `DivisorPair.globalSections`, so both
naturalities reverse correctly with no flatness assumption and no change of sign.

`algebraicRoundTripEquiv E A` is cohomology of `A ≅ Γ(Spec A)`; `affineRoundTripEquiv T X` is
pullback along `Spec Γ(X) ≅ X` and recovers only `T.restrict (aff_le D)`. Their membership lemmas
preserve and reflect every bidegree. The public `map`/`pull`, `gysin`, `residue` and `algebraMap`
lemmas give all commuting squares, and the two `triangle` lemmas identify the comparisons as
compatible inverses. `toAlgebraic_standardResidue` and `toAlgebraic_standardGysin` compare the
standard maps via the polynomial and Laurent isomorphisms. `emptySubsingleton` derives vanishing
for every empty scheme from the algebraic empty-divisor consequence of exactness; a unit equation
therefore has zero Gysin and residue. No empty-scheme axiom is added. Transport of the existing
nonzero de Rham theory is a geometric theory on affines, identified with the cohomology of global
sheaf forms in "The de Rham instance on affine schemes".

### Geometric supports and purity

The supports-and-purity bridge shares a category-independent covariant core in
`BridgeData/Category` and `BridgeData/CategorySupports`. The original `DegreewiseTheory` and
`SupportsAndPurity` record declarations remain intact. Their `toCore` adapters and thin wrappers
retain the existing constructors, projections, method names, statements and simp API. Direct-sum
algebra, exactness, shifts, coefficient linearity, naturality and projection are proved once in
the common core. `CovariantPairDiagram` supplies the three object functors and the closed/open
natural transformations. The geometric inputs use this core on `D.Objᵒᵖ` and
`(DivisorPair D)ᵒᵖ`, so the constructed theory works on every admissible domain, including
non-affines. Public component formulas identify pullback, Gysin and residue with the original
degreewise maps and prove compatibility with domain restriction and affine transport. No total
exactness or arrangement conclusion is assumed.

The constructions on this path are `@[implicit_reducible]`, like the named objects of the scheme
layer: both `ofSupportsAndPurity`, `CategoricalDegreewiseTheory.functor`, the algebraic
`DegreewiseTheory.functor`, and the two `DegreewiseTheory.toCore` adapters. A component formula
such as `ofSupportsAndPurity_pull_incl` is an equation in the carrier of
`(ofSupportsAndPurity E S).obj X`, but its right side is an element of `E.Total X`, and the two
types agree only by unfolding these definitions. When `simp` or `rw` instantiates a rule, Lean
compares the type of each term assigned to a variable of the rule with the type of that variable
at implicit transparency. Without the attribute, `simp` therefore rewrote the left side and then
could not close the resulting goal `a = a` with `eq_self` (#132). `Examples/Bridge` checks the
formulas for pullback and Gysin with plain `simp`. Simp keys are computed at reducible
transparency and type class search runs at instance transparency, so neither sees through these
definitions.

### Geometric logarithms

`Cohomology/Geometric/Logarithms` (#113) constructs logarithmic classes for a geometric theory on
every object of its domain, affine or not, and reuses the algebraic `Cohomology/Logarithms` through
`toAlgebraic` rather than reproving it.

- **The class `τ`.** `T.tau` lives on `D.gm`, which is the same scheme as
  `D.spec (SmoothAlg.gm k)`, where `T.toAlgebraic` has its class; `SmoothDomain.specGmIso` is the
  identity between them, and `T.tau` is the pullback of `T.toAlgebraic.tau` along it. The standard
  pair of the base has open part `S ×_S 𝔾ₘ`, so the normalization reads
  `T.standardResidue D.point (T.pull (D.prodGmSnd D.point) T.tau) = 1`, proved by
  `toAlgebraic_standardResidue` and the naturality of the residue for
  `standardPairMap D.specPointIso.hom`; `eq_tau_of_mem_grading` is uniqueness.
- **The class `[u]`.** `T.logClass u = T.pull (D.gmHom u) T.tau`, where `D.gmHom u : X ⟶ D.gm`
  is `unitsEquivHomGm` in the domain. Pullback is `pull_logClass`, with
  `Units.map g.hom.left.appTop.hom`. `[uv] = [u] + [v]` is pulled back from the old identity on
  `𝔾ₘ² = Spec k[s, s⁻¹][t, t⁻¹]` along the map of `(u, v)` built with `specHomEquiv`;
  `[u]² = 0` is pulled back from `τ² = 0`; the class of a constant `c ∈ kˣ` vanishes because its
  map factors through `D.point` (`logClass_eq_zero_of_coe_eq_algebraMap`, stated with the function
  of the unit, and `logClass_units_map_algebraMap`), so units that differ by a constant have the
  same class (`logClass_eq_of_coe_eq_algebraMap_mul`, `logClass_units_map_algebraMap_mul`). The
  residue formulas hold for every pair, by `residue_pull` along `DivisorPair.toStandard`.
  Restriction to a smaller domain does not change classes (`restrict_logClass`, by `rfl`).
- **Comparisons.** `pull_toAlgebraic_logClass_eq g u` computes `g^*` of the old class `[u]` of
  `T.toAlgebraic`, for any `g : X ⟶ D.spec A`, as the class of the unit
  `Units.map g.hom.left.appTop.hom (specUnit u)`, and `pull_toAlgebraic_logClass g u hv` as the
  class of any unit `v` with `(v : Γ(X)) = g^*(u)`. They are the lemmas to compose with `s_𝒜` and
  `s_P` for the generator formulas of the structure theorems, followed by
  `D.map_complementIsoSpec_hom_complementUnit` or
  `D.map_projectiveComplementIsoSpec_hom_projectiveRatioUnit`. On `D.spec A` itself,
  `toAlgebraic_logClass_eq` states it with `specUnit u`. `ofAlgebraic_logClass` identifies the
  classes of `ofAlgebraic E` on an affine `X` with the old classes of `E` on `Γ(X)`, through
  `algebraicRoundTripEquiv_logClass`.
- **The product with `𝔾ₘ`.** The coordinate of `X ×_S 𝔾ₘ` is the unit `D.prodGmCoord X`, equal
  to the equation of `standardPair D X` (`standardPair_eqnUnit`), and `[z]` is
  `T.logClass (D.prodGmCoord X)`. `gmProductEquiv X : (C(X) × C(X)) ≃ₗ[B] C(X ×_S 𝔾ₘ)` is
  `@[no_expose]`, like the algebraic one, and is described by `gmProductEquiv_apply`,
  `gmProductEquiv_symm_apply` (the section `z = 1` and the standard residue),
  `gmProductEquiv_mem_grading_iff` and the naturality `pull_prodGmMap_gmProductEquiv`. Its proof
  uses only the axioms for the standard pair of `X`.

### The geometric structure theorems

`Presentation/Geometric` (#114) is the public facade of the structure theorems on schemes. It
reuses the existing theorems and proves nothing about arrangements again.

- **The transport.** `transportAffineDevelopment T e : T.toAlgebraic.C.obj A ≃ₐ[B] T.obj X`, for
  `e : X ≅ D.spec A`, is pullback along `e`, and its laws are the base cases of the blueprint's
  induction on expressions: bidegrees (`transportAffineDevelopment_mem_grading_iff`,
  `transportAffineDevelopmentComponentEquiv`), logarithmic classes
  (`transportAffineDevelopment_logClass` and `transportAffineDevelopment_logClass_eq`, from
  `pull_toAlgebraic_logClass`) and compatible pullbacks (`transportAffineDevelopment_map`, whose
  hypothesis is a square with `D.specFunctor.map`, the form of the naturality lemmas of `s_𝒜` and
  `s_P`). Residue and Gysin are compared by `residue_pull` along a pair isomorphism with
  `DivisorPair.spec`, as `transportAffineDevelopment_deletionResidue` does along
  `deletionPairIsoSpec`. This is the Lean form of `thm:geo-transport-all`, which stays partly
  formalized.
- **The theorems.** `affineEquiv 𝒜 = (T.toAlgebraic.affineEquiv 𝒜).trans
  (transportAffineDevelopment T (D.complementIsoSpec 𝒜))`, so `affineEquiv_apply` is
  `Φ^geo = s_𝒜^* ∘ Φ`, and `projectiveEquiv P` is the same with `D.projectiveComplementIsoSpec P`,
  for `[Nonempty P]`. Every other declaration is the existing one composed with the transport:
  generators, independence of the equations and uniqueness, the bigrading, naturality for
  `D.complementInclusion` and `D.complementIso`, the cone projection `D.coneComplementProjection`,
  the deletion residue, the components, the diagonals over `R` (through `diagonalAlgEquiv` and the
  transported `BijOn`), vanishing, bases and Betti numbers. The names are those of the existing
  declarations, in `namespace OrlikSolomon.Geometric.OrdinaryTheory`; `logMonomial`, the typed
  `deletionResidue` and `deletionGysin`, and `residueComparison` are the geometric ones.
- **No second structure map.** `ofAlgebraic_affineEquiv` and `ofAlgebraic_projectiveEquiv` say
  that for an algebraic theory `E` the geometric theorems of `ofAlgebraic E` are the existing ones
  for `E`, followed by `E` of the ring isomorphism `O(U) ≅ Γ(U)`. The de Rham corollaries on
  schemes are compared with the existing ones through them (`affineEquiv_eq_map`).
- **Elaboration.** In `T.logClass u` the object is implicit, and Lean cannot solve it from a unit
  `u : Γ((complement 𝒜).left, ⊤)ˣ`, since that would mean inverting the projection `X.obj`. No
  transparency setting changes this. When the expected type does not fix it, write
  `T.logClass (X := D.complement 𝒜) u`, as in `logClass_complementUnit_eq_of_isEquation` and
  `isFamily_logClass_complementUnit`, or ascribe the unit the type
  `Γ((D.complement 𝒜).obj.left, ⊤)ˣ`.

### Relative forms as sheaves

`Geometry/Schemes/ModuleGluing`, in `OrlikSolomon.Geometric`, reuses Mathlib's `tilde.functor`,
`tilde.isoTop` and distinguished-open localization maps. Its additional results identify the
maps on distinguished opens with localized linear maps, prove preservation of monomorphisms and
homology, and give `tilde_map_exact` for arbitrary module sequences. There is no finite-
generation or nonzero-ring assumption, and no higher-cohomology vanishing assertion.
It also provides the generic stalk/basis criteria for quasi-isomorphisms and coherent
inverse-image identity/composition maps. The old de Rham names are deprecated aliases, and
callers use the canonical `OrlikSolomon.Geometric` names.

The `DeRham/Schemes/Forms` umbrella and its `Presheaf`, `Sheaf`, `Affine`, `Associated` and
`Pullback` files use `OrlikSolomon.Geometric.DeRham` and import no G0 module. They work over any
commutative base ring and on any object of `Over (Spec k)`. `sectionAlgebra k X U` bundles regular functions with
the base-ring action; `formsPresheaf` applies the existing exterior-power forms and their
functorial maps to it. `formsSheaf` sheafifies in `k`-modules. Mathlib's presheaf-of-modules
sheafification equips the same underlying additive carriers with their structure-sheaf actions
as `formsModuleSheaf`; public carrier and base-linear isomorphisms compare the two views.

`formsSheafMul`, `formsSheafWedge` and `formsSheafOne` extend the existing algebraic operations
by the sheafification universal property. Their public formulas prove associativity, units,
graded commutativity and signed Leibniz on these carriers. `formsSheafZeroIso` identifies degree
zero with the structure sheaf, and multiplication by a degree-zero function agrees with the
retained module action. `formsSheafD` is only base-ring linear. `formsComplexNat` packages the
nonnegative complex; `formsComplex` extends it by zero to integers, with negative terms proved
zero.

`formsSheafPullback` is the adjoint pushforward form of pullback along every base-scheme
morphism. It preserves products, commutes with the differential, and has identity and
composition lemmas. `formsComplexNatPullback` and `formsComplexNatInverseImage` package the maps
of nonnegative complexes. Degreewise, `formsModuleSheafPullback` and
`formsModuleSheafInverseImage` give the equivalent structure-sheaf-linear formulation, compared
publicly with the same base-linear maps. No flatness is assumed, and the differential is not
asserted to be a map of structure-sheaf modules.

`Forms/Affine` compares the distinguished-open restrictions with Mathlib's associated module
sheaf using the existing localization theorem for algebraic forms. `specFormsSheafAssociatedIso`
exposes the associated-sheaf identification after forgetting scalar actions, with its
localization formula. The literal `formsSheafUnit` is invertible on each distinguished open of a
spectrum and on every affine open of an arbitrary ambient scheme, including global sections of
every affine scheme. `affineFormsComparison` is the canonical global comparison for an affine
scheme, with differential, wedge, unit and pullback formulas; `affineOpenFormsComparison` gives
the affine-open evaluation. `Forms/Associated` provides the structure-sheaf-linear comparison
`specFormsModuleSheafAssociatedIso`, its distinguished-open fraction formulas, and
`affineOpenModuleFormsComparison`. Open restrictions agree through `formsSheafRestrictionIso`.
The private affine transport uses Mathlib's `Scheme.isoSpec`, retaining independence from the
geometric-domain layer. Its global function algebra is the bundled `sectionAlgebra k X ⊤`; any
other bundled presentation is compared by its algebra isomorphism. These results do not identify
underived global sections with hypercohomology and do not construct an instance on non-affine
schemes.

### The de Rham instance on affine schemes

`DeRham/Schemes/GlobalSections`, `DeRham/Schemes/Affine`, `DeRham/Schemes/Instance` and
`DeRham/Schemes/Corollaries` (#116) use `OrlikSolomon.Geometric.DeRham`. Inside it, `Cohomology`,
`ordinaryTheory`, `twistedClass`, `gysin`, `residue`, `affineEquiv` and `projectiveEquiv` are the
geometric declarations; write the existing ones with `OrlikSolomon.DeRham.`. A file that opens both
`OrlikSolomon` and `OrlikSolomon.Geometric` must qualify `DeRham.` names, which are ambiguous there.

- **Two presentations of `Γ(X, 𝒪_X)`.** `globalSections X` of G0 and `sectionAlgebra k X ⊤` of the
  sheaves of forms have the same carrier, but their structure maps differ by
  `presheaf.map (𝟙 _)`. `globalSectionsAlgEquiv X` is the identity between them; it intertwines
  `globalSectionsMap` and `sectionPullbackTop` by `rfl`. Everything public is stated over
  `globalSections X`, through `globalFormsEquiv X n`, which is `affineFormsComparison` after
  `Forms.mapPower` of that equivalence. These live in the leaf `DeRham/Schemes/GlobalSections`,
  which imports only `DeRham/Schemes/Forms` and `Geometry/Schemes/Basic`, so that the sheaf
  logarithmic comparison (#117) can reuse them.
- **`Γ(X, Ω^•_{X/k})` and the comparison.** `globalFormsComplex k X` is the functor
  `sheafToPresheaf ⋙ evaluation (op ⊤)` applied to `formsComplexNat k X`, for every scheme
  (`sheafSections` has no additivity instance). For affine `X`, `complexIsoGlobalFormsComplex X`
  identifies it with `OrlikSolomon.DeRham.complex k (globalSections X)` degree by degree, and
  `globalFormsHomologyIso X n` is Mathlib's homology in degree `n` of `Γ(X, Ω^•_{X/k})`, isomorphic
  to `Cohomology.degree k (globalSections X) n`. The direct sum is formed afterwards
  (`Cohomology.directSumEquiv`), so global sections never meet an infinite direct sum of sheaves.
- **Classes.** `globalClass X n ω hω` is the class of a closed global sheaf form, and is the public
  specification of products (`globalClass_wedge`), pullbacks (`globalClass_pull`,
  `Cohomology.pull_globalClass`), exactness (`globalClass_eq_zero_iff`) and surjectivity
  (`globalClass_surjective`). Closedness of a wedge or a pullback is supplied by named lemmas
  (`formsSheafD_wedge_eq_zero`, `formsSheafD_pullbackTop_eq_zero`) that appear in the statements.
- **`Cohomology X`** is a reducible abbreviation for `OrlikSolomon.DeRham.Cohomology k
  (globalSections X.obj)`, for `X : (SmoothDomain.aff k).Obj` only, so that the existing API and
  instances apply; `Cohomology.degree X n` likewise. `Cohomology.pull f` is the map induced by
  `globalSectionsMap f.hom`. Nothing defines de Rham cohomology of a scheme that is not affine.
- **The instance.** `ordinaryTheory k` is the `@[implicit_reducible] def`
  `ofAlgebraic (OrlikSolomon.DeRham.ordinaryTheory k)`, with hypotheses `[Field k] [CharZero k]`
  used only by the existing instance. As for that instance, compute with `twistedClass w c`, the
  class `t^w ⊗ c` typed in `(ordinaryTheory k).obj X`: `objEquiv` is `C(X) = B ⊗[k] Cohomology X`,
  `mem_grading_iff` and `gradingEquiv` give the bigrading, and `pull_twistedClass`,
  `gysin_twistedClass`, `residue_twistedClass` and `twistedClass_mul_twistedClass` are `simp`. The
  maps `gysin P` and `residue P` are the existing de Rham Gysin map and residue of the algebraic
  pair `DivisorPair.globalSections P`, the maps of its global logarithmic sequence
  (`residue_mk_add_theta_mul`, `gysin_mk_of_logResidue_eq`). Their statements name the algebraic
  pair's components, not `globalSections P.ambient.obj`, since the algebra instance
  `P.ambient → P.compl` of an algebraic pair is only found on those: instance search retrieves it
  by its key `DivisorPair.ambient`, which no transparency setting changes (#128). `logClass_eq` is
  `[u]_T = t ⊗ [du/u]`, from `ofAlgebraic_logClass` and `ordinaryTheory_logClass`; like the existing
  lemma it is not `simp`.
- **The corollaries.** `affineEquiv 𝒜 : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology ((aff k).complement 𝒜)` and
  `projectiveEquiv P` are the geometric diagonal theorems for `ordinaryTheory k` followed by the
  inverse of `TwistedCohomology.diagonalEquiv`, as in `DeRham/Corollaries`, with the same API.
  `affineEquiv_eq_map` and `projectiveEquiv_eq_map` identify them with the existing corollaries
  for the coordinate rings, through `ofAlgebraic_affineEquiv` and `ofAlgebraic_projectiveEquiv`.
  To remove the powers of `t` from a class of the instance, use `untwist X`, which is
  `TwistedCohomology.evalOne k (globalSections X.obj)` typed on `(ordinaryTheory k).obj X`, with
  `untwist_twistedClass`, `untwist_logClass` and `untwist_pull`; or state `evalOne` with the
  explicit algebra `globalSections X.obj`, as `affineEquiv_apply` does. With `_`, the algebra
  elaborates to `(affineGlobalSectionsFunctor k).obj (op X)`, and `rw` with `evalOne_logClass` no
  longer matches, because `(ordinaryTheory k).obj X` is `TwistedCohomology k _` only at default
  transparency.

### Logarithmic forms on schemes

The `DeRham/Schemes/Log` umbrella and the modules listed below use
`OrlikSolomon.Geometric.DeRham` and depend on G0, forms sheaves and the existing algebraic
log/pole APIs, independently of arrangements and the OS presentation.
`logSheaf P n` is the categorical image of the regular-plus-left-theta map into `j_*Ω_U^n`.
Its public inclusion and affine comparison hide the image construction. Sections of a sheaf
image are identified with the corresponding module image only through the affine
associated-module proof.

`logComplexNat` uses the base-linear differential. `shiftedClosedComplexNat` has zero degree
zero, `i_*Ω_D^n` in degree `n + 1`, and differential `-d`. Residue is normalized by
`ρ(ω + θ ∧ η) = i^*η`, satisfies `ρd = -dρ`, and satisfies the right projection formula without
a sign. The residue sequence works over a commutative base ring.

`affineLogComparison`, `affineLogComplexIso` and `affineLogResidueShortComplexIso` identify the
three terms and both maps of the affine global sequence with the existing algebraic sequence.
Their representative formulas identify the old algebraic logarithmic sequence with the actual affine
global sheaf sequence. In `Schemes/Instance`, `residue_globalClass` and
`gysin_globalClass_of_logResidue_eq` identify its residue and Gysin on these sheaf representatives.
Gysin retains the representative convention
`[γ] ↦ [dλ]`; a generic connecting-map convention is not assumed.

Positive-integer inverses enter only in `Comparison`, where `logSheafComparison` proves that
inclusion into the ordinary direct-image de Rham complex is a quasi-isomorphism on stalks. Neither
this result nor the sheaf short exact sequence is passed through underived global sections on a
non-affine scheme.

### Modules

The paths began with the blueprint's proposals for #107–#118; the table also records approved
follow-ups. A PR that splits a row into other files updates this table.

`Log/Sections` displays complement and divisor section carriers on their inverse-image opens.
Its typed maps and the explicit identity reindexing support simplification without unfolding
direct images. The named module `logSheafPullbackSections` keeps identity preimages stable
under `simp`, including coercions, inverse reindexing, addition and scalar multiplication.
Its `@[instance_reducible]` attribute lets instance search combine pulled-back and ordinary
sections on the same open, following the wrapper rule of #128.
The legacy raw sheaf equations remain available. On affine pairs,
`affineGlobalLogToOpen_quasiIso` follows from the canonical algebraic chain-map comparison
`DeRham.logToLocalization_quasiIso`; the old
`Geometric.DeRham.algebraicLogToLocalization_quasiIso` is a deprecated alias.
Global residue lifts and their regular differentials exist by the affine exact sequence.
These are statements about affine global sections;
no exactness of non-affine global sections is asserted.

| Module under `OrlikSolomon/` | Blueprint labels | Issue |
| ---------------------------- | ---------------- | ----- |
| `Geometry/Schemes/Basic` | `def:geo-domain`: `S`-schemes, `spec`, `globalSections`, `affineLine`, `gm`, `SmoothDomain` and its three canonical values | #107 |
| `Geometry/Schemes/AffineDuality` | `thm:geo-affine-duality`: `specHomEquiv`, `η`, `ε`, the smoothness criterion and `smoothAffineEquivalence` | #107 |
| `Geometry/Schemes/AffinePairs` | `lem:geo-affine-pairs`: zero schemes, basic opens and regular sections | #107 |
| `Geometry/Schemes/Units` | `thm:geo-units`, and functions as maps to `𝔸¹` | #107 |
| `Geometry/Schemes/Products` | `lem:geo-products`, and the geometric standard pair | #107 |
| `Geometry/Schemes/PrincipalPair` | the module to import for the four files below | #108 |
| `Geometry/Schemes/PrincipalPair/Certificates` | the certificates of a pair on any scheme: universal properties, base change, unit multiples, locality of regularity, and the translation to algebraic certificates on affine schemes and spectra | #108 |
| `Geometry/Schemes/PrincipalPair/Basic` | `def:geo-divisor-pair`, `def:geo-pair-hom`, `thm:geo-cartesian`: `DivisorPair`, its morphisms, `homOfAmbient`, `withEqn`, `ofLE` and the Cartesian squares | #108 |
| `Geometry/Schemes/PrincipalPair/Standard` | the certificates of the geometric standard pair on every scheme, `standardPair`, its functoriality and `toStandard` | #108 |
| `Geometry/Schemes/PrincipalPair/Duality` | `thm:geo-pair-duality`: `spec`, `globalSections`, `affinePairEquivalence` and `specStandardPairIso` | #108 |
| `Cohomology/Geometric/Axioms`, `Cohomology/Geometric/Transport` | `def:geo-theory`, `lem:geo-restriction`, `lem:geo-empty`, `thm:geo-to-algebraic`, `thm:geo-from-algebraic` | #109 |
| `Cohomology/Geometric/Bridge` | `def:geo-supports`, `thm:geo-bridge` | #110 |
| `Geometry/Schemes/Complement` | the module to import for the four files below | #111 |
| `Geometry/Schemes/Complement/AffineSpace` | `def:geo-affine-space`: `affineSpace`, `affineSpaceCoord`, `affineSpaceMap`, hyperplane schemes and the comparison with Mathlib's `AffineSpace` | #111 |
| `Geometry/Schemes/Complement/Basic` | `def:geo-complement`, `thm:geo-complement-spec`: `complement`, `complementIsoSpec`, `complementHom` and the maps of complements | #111 |
| `Geometry/Schemes/Complement/Deletion` | `thm:geo-deletion`: `DivisorPair.ofIso`, `DivisorPair.deletionPair` and the fiber product with `𝐇` | #111 |
| `Geometry/Schemes/Complement/Targets` | `thm:geo-small-targets`: `affineImageMap`, `normalizedSliceMap` | #111 |
| `Geometry/Schemes/Projective` | `def:geo-projective`, `thm:geo-projective-geometry` | #112 |
| `Geometry/Schemes/Decone` | the affine sides of `thm:geo-projective-geometry`: the cone and the decone as actual complements | #111 |
| `Cohomology/Geometric/Logarithms` | `def:geo-log`, `thm:geo-log-laws`, `thm:geo-gm-product` | #113 |
| `Presentation/Geometric`, the module to import, over `Presentation/Geometric/Transport` | `thm:geo-transport-all`: `transportAffineDevelopment` and its laws | #114 |
| `Presentation/Geometric/Affine`, `Presentation/Geometric/Ordinary` | `thm:geo-affine`: `affineEquiv` and its API, and the forms over `R` | #114 |
| `Presentation/Geometric/Projective` | `thm:geo-projective`: `projectiveEquiv`, its diagonal and multiplicities | #114 |
| `Geometry/Schemes/ModuleGluing` | `lem:geo-module-gluing`: associated-module exactness, generic stalk/basis comparison and inverse-image coherence, with no forms | #115, #137 |
| `DeRham/Schemes/Forms`, the module to import, over `DeRham/Schemes/Forms/Presheaf`, `DeRham/Schemes/Forms/Sheaf`, `DeRham/Schemes/Forms/Affine` and `DeRham/Schemes/Forms/Pullback` | `def:geo-forms-sheaf`, `thm:geo-forms-comparison` | #115 |
| `DeRham/Schemes/GlobalSections` | the two presentations of `Γ(X, 𝒪_X)`, the complex `Γ(X, Ω^•_{X/k})` and its affine comparison with algebraic forms, for `def:geo-dr-cohomology` and `thm:geo-log-sheaves` | #116 |
| `DeRham/Schemes/Affine` | `def:geo-dr-cohomology`: `Cohomology`, `globalFormsHomologyIso`, `globalClass` and the direct sum | #116 |
| `DeRham/Schemes/Instance` | `thm:geo-dr-instance`: `ordinaryTheory`, `twistedClass`, the twisted Gysin and residue, `logClass_eq` | #116 |
| `DeRham/Schemes/Corollaries` | `cor:geo-dr-arrangements`: `affineEquiv`, `projectiveEquiv` and their API | #116 |
| `DeRham/Schemes/Forms/Associated` | structure-sheaf-linear associated-module comparison and distinguished-open fraction formulas, extending `thm:geo-forms-comparison` | #117 |
| `DeRham/Schemes/Log`, the module to import | `thm:geo-log-sheaves`: umbrella for the files below | #117 |
| `DeRham/Schemes/Log/Basic` | the global theta section, regular-plus-left-theta map, its image sheaf, complex and signed closed shift | #117 |
| `DeRham/Schemes/Log/Algebra` | wedge products and dg algebra identities on the logarithmic image sheaves, descended from local normal forms and characterized by the actual complement inclusion | #117 |
| `DeRham/Schemes/Log/AffineImage` | exact associated-module image comparison on spectra and transport of logarithmic images along pair isomorphisms | #117 |
| `DeRham/Schemes/Log/Affine` | affine-neighborhood pairs, associated-module image comparison and affine cochain isomorphisms | #117 |
| `DeRham/Schemes/Log/RestrictionImage` | exact image transport for open restrictions, retaining regular, theta and differential compatibility | #117 |
| `DeRham/Schemes/Log/Sections` | typed complement/residue section maps and explicit identity reindexing; imports only Naturality | #137 |
| `DeRham/Schemes/Log/Restriction` | restriction to affine neighborhoods, their global logarithmic and open-form complexes, and the inclusion comparison | #117 |
| `DeRham/Schemes/Log/Residue` | residue descent, signs and the short exact sequence of sheaf complexes | #117 |
| `DeRham/Schemes/Log/ResidueAffine` | affine residue comparison, global exactness and lifts, and domain-general closure of representatives | #117, #137 |
| `DeRham/Schemes/Log/Comparison` | stalkwise and affine-global quasi-isomorphisms from the algebraic pole theorem; deprecated aliases for moved helpers | #117, #137 |
| `DeRham/Schemes/Log/Projection` | the form-level right projection identity, with logarithmic factor on the left and no sign | #117 |
| `DeRham/Schemes/Log/Naturality` | transverse maps, unit changes of equation, and typed inverse-image section carriers | #117, #137 |
| `Examples/Geometric` | umbrella, geometric bridge and ring-rewriting acceptance consumers, and `prop:geo-finite-field` | #118 |
| `Examples/Geometric/Acceptance`, `Examples/Geometric/DeRhamAcceptance` | consumers importing only the geometric public facade or its unconditional de Rham corollaries | #118 |
| `Examples/Geometric/Degenerate` | `prop:geo-degenerate`: actual empty, unit and disconnected pairs, their forms, cohomology and residue | #118 |
| `Examples/Geometric/LogSheaf` | strict consumers of typed section maps, signed theta differentiation, affine comparison and lifts, characteristic two and zero base | #137 |
| `Examples/Geometric/Morphisms`, `Examples/Geometric/Exclusions` | `prop:geo-nonflat`, `prop:geo-exclusions`: actual non-flat transverse and ramified maps, the regularity shift obstruction, and the crossing sheaf/stalk obstruction | #118 |
| `Examples/Geometric/AffineDeRham` | `prop:geo-affine-regressions`: actual punctured line, torus, both residue signs and positive-characteristic obstructions | #118 |
| `Examples/Geometric/NonAffine` | `prop:geo-nonaffine`: facade for the projective-line example | #118 |
| `Examples/Geometric/NonAffine/Geometry`, `Charts`, `Overlap`, `Sections`, `ChartForms` | actual projective line, standard pair, two-open cover, polynomial/Laurent coordinates, section comparisons and chain-level restriction squares | #118 |
| `Examples/Geometric/NonAffine/MatchingForms`, `GlobalForms` | matching polynomial forms, actual sheaf gluing, global functions and the global-forms complex of the projective line | #118 |
| `Examples/Geometric/NonAffine/Fiber`, `ChartSum` | example-only homotopy-fiber and chart-sum constructions, natural in the restriction diagram | #118 |
| `Examples/Geometric/NonAffine/Cech`, `CechZero`, `SheafCech` | polynomial/Laurent computation and transport to the actual two-chart Čech–de Rham complex, with its nonzero logarithmic degree-two class | #118 |
| `Examples/Geometric/NonAffine/MayerVietoris` | the conditional computation from the actual chart/overlap de Rham homology and sheaf restrictions; affine calculations derive the scalar normalization, with no cohomology conclusion as input | #118 |

`Geometry/Schemes/ModuleGluing` is generic and uses the namespace `OrlikSolomon.Geometric`.
`DeRham/Schemes/Forms`, `DeRham/Schemes/Log` and their submodules, together with the four
`DeRham/Schemes` modules of #116, use `OrlikSolomon.Geometric.DeRham`.

`Presentation/Geometric` is a facade: the blueprint's acceptance test is a consumer that imports
only it and states both theorems for a theory on all smooth schemes. The blueprint's stages fix the
order. Stage G0 is #107 and #108. After it, stage G1 (#109) and stage G2 (#111, #112) are
independent, and the geometric bridge #110 needs only #109. Stage G3 (#113, #114) needs G1 and G2.
Stage G4 (#115) is independent of G0–G3, stage G5 (#116) needs G1, G3 and G4, and stage G6 (#117)
needs G0 and G4. Parts of #118 land with the modules they test.

The chapter `OrlikSolomonBook/Geometric.lean` presents its 42 nodes, and its opening lists the ones
that are formalized. When nodes land, update that opening, the paragraph "A planned third part"
on the first page, the row in `Organization`, the sentence on the status page, the pointers in
`Geometry`, `Axioms` and `Projective`, and the line in `README.md`. The build does not check this
prose.

## Interface

`OrlikSolomon/MainTheorem.lean` (#140) states the main theorem with Mathlib terms only and imports
the library privately. The bridge modules `Interface/*`, in the namespace `OrlikSolomon.Interface`,
relate its terms to the library. They state their results about the same Mathlib terms, so that the
proofs of the interface connect them by `rfl` or `exact`. Where the interface defines data that the
library needs as one of its own terms, such as a divisor pair, the bridge module repeats the body
of the interface's definition, and the assembly identifies the two by unfolding. Keep such bodies
identical to the interface's. Inside `namespace OrlikSolomon.Interface`, the names `DivisorPair`
and `OrdinaryTheory` resolve to the algebraic declarations, so write `Geometric.DivisorPair` and
`Geometric.OrdinaryTheory`.

| Module under `OrlikSolomon/` | Blueprint labels | Issue |
| ---------------------------- | ---------------- | ----- |
| `MainTheorem` | audited Mathlib-only projective Orlik–Solomon interface; the theorem for every smooth-scheme class and affine de Rham non-vacuity | #140 |
| `Interface/Logarithms` | the interface's `standardDivisor` as the library pair `Interface.standardPair D`, its isomorphism `standardPairIso` with `standardPair D D.point` and the residue comparison; `τ` as the unique class of bidegree `(1, 1)` with residue `1` at the origin (`def:geo-log`); a map to `𝔾ₘ` pulling the coordinate back to `f` exists exactly when `f` is a unit, is then unique, and pulls `τ` back to `[f]` (`thm:geo-units`) | #143 |
| `Interface/OSAlgebra` | generic RingQuot presentation, central OS comparison, projective difference subalgebra and weighted grading compatibility for M7 | #142 |
| `Interface/ProjectiveSpace` | Mathlib projective space and linear forms; scheme-hyperplane equation uniqueness; index equivalences with the linear arrangement and its central cone; dependence agreement (`def:geo-projective`, `def:os`) | #141 |
| `Interface/ProjectiveComplement` | actual open-complement comparison over Spec k; affineness and smoothness for nonempty arrangements; compatibility of equation ratios and global units (`def:geo-projective`, `thm:geo-projective-geometry`) | #141 |

`Interface/OSAlgebra` makes library-side copies of the approved main-theorem presentation over
an arbitrary index type and dependence predicate, with bodies identical to the skeleton's Mathlib
terms. Given an equivalence with a central arrangement and dependence compatibility on lists
without repetitions, its algebra equivalence identifies the RingQuot presentation with
`OSAlgebra`. Its restriction identifies the subalgebra generated by all differences with
`projectiveAlgebra` for a nonempty index type; the explicit word-span pieces correspond to
`bigrading` and `projectiveBigrading`, including negative cohomological degrees. The bridge uses
only the algebraic presentation modules (plus Mathlib's RingQuot), not cohomology or scheme
modules, and permits arbitrary commutative coefficient rings, including the zero ring. It does
not import or modify `MainTheorem.lean`.

`Interface/ProjectiveSpace` repeats the approved skeleton's projective space, equation predicate and
arrangement definitions. It compares Proj of the polynomial ring with Proj of the symmetric algebra
by the coordinate basis. Scheme-point zero loci determine the linear kernels, including in dimension
zero and over finite fields, so the induced arrangement and its cone have canonical index
equivalences and the same dependence predicate. `Interface/ProjectiveComplement` is a size-only leaf
over that module. It repeats the skeleton's open complement and fraction-ratio definitions and
identifies them with the library's actual open projective complement and ratio units. No approved
MainTheorem statement changes. Since the two equation predicates are separately declared structures,
the assembly uses their fieldwise logical equivalence and reindexes the hyperplane Finset,
preserving each underlying set by rfl.

`MainTheorem.lean` separates the public definitions and theorem statements from library-backed
proofs in `OrlikSolomon.MainTheorem.Proof`. Public types and data use only Mathlib and earlier
public declarations of the file; the library is imported privately. The physical order is Part I
(definitions), a clearly delimited private proof region marked for readers to skip, Part II
(public statements), then `#print axioms`. Lean requires the proofs before the statements that use
them because it does not allow forward references. This placement does not change the audit
boundary. `lake exe audit --interface` checks that boundary, and `#print axioms` on the public
theorems records their logical dependencies. `OrlikSolomonBook/MainTheorem` quotes the interface
and explains its hypotheses, the generator formula, onto grading pieces and the verified de Rham
instance on `smoothAffine` in characteristic zero. `README.md` links to this file and chapter.
M7 introduces no blueprint nodes.

## Cohomological hyperplane reconstruction (M8)

`blueprint/cohomological_hyperplane_gt_blueprint.tex` is authoritative for the mathematics.
This section records the approved design, implemented generic helpers and blueprint statements.
G01–G06, A01–A04, C01–C04, U01–U05, L01–L05, P01–P02, I01–I04 and S01–S05 are formalized, including U04's actual universal
configuration equations and paired diagram invariance. Pure coordinate reconstruction C01–C03 holds over arbitrary fields.
Cohomological reconstruction remains planned. The book records complete-statement status.
The generic lowest-degree relation helper is implemented in `Algebra/HomogeneousRelations`, as
described under Algebra above; `HyperplaneGT/Algebra/QuadraticKernel` applies it to the actual OS
quotient and identifies its full degree-two kernel.
The [parent issue #151](https://github.com/adamtopaz/OrlikSolomon/issues/151),
[approved plan](https://github.com/adamtopaz/OrlikSolomon/issues/151#issuecomment-6750159326)
and [child-issue index](https://github.com/adamtopaz/OrlikSolomon/issues/151#issuecomment-6750266079)
track implementation. Governance is [#153](https://github.com/adamtopaz/OrlikSolomon/issues/153);
PR [#152](https://github.com/adamtopaz/OrlikSolomon/pull/152) supplies the authoritative TeX
and initial book chapter. The TeX must remain byte-identical.

The reconstruction layer lives under `OrlikSolomon/HyperplaneGT/`, in namespace
`OrlikSolomon.HyperplaneGT`. File-path components such as `Algebra` do not introduce namespaces
that shadow Mathlib names. The layer reuses the existing affine-hyperplane type, finite
arrangements, OS algebra and grading. It introduces no new cohomology theory and adds no fields
to the existing one.

The core stores explicit finite free modules, exterior-square relation spans, cofinal stable
arrangements and tagged marking arrows. There is one common target for all markings.
Automorphisms preserve the entire quadratic relation submodule by equality and commute with
the specified arrows. Arbitrary coordinate projections are derived using P01–P02, not added
as arrows. The universal module is a Finsupp module; its algebraic dual is the full product.
The left action on the dual uses the inverse linear equivalence. Finite-stage and annihilator
calculations provide the required identifications without a reflexivity assumption.

Pure algebra is stated over arbitrary commutative coefficient rings where valid, including the
zero ring. Nontriviality/locality or the integral-domain hypothesis enters where reconstruction
uses it. The coefficient ring and geometric fields have independent universes, and the core
requires no field-algebra structure on the coefficient ring. Pure coordinate reconstruction
takes an arbitrary field and the specified frame. Algebraicity is used for finite Galois orbits;
perfect-field/algebraic-closure assumptions appear at the public geometric theorem matching the
blueprint. The reconstruction theorem retains `n ≥ 2`.

The Galois action is semilinear on geometric coordinates and is constructed on OS generators by
preservation of all defining relations. It is not passed to an API for a `k`-linear affine map.
`Diagram/GaloisAction/Stage` restricts the label permutation to a stable arrangement and checks
both fields of `OSAlgebra.IsFamily` in every length: empty-intersection products and guarded
dependent boundaries. `galoisOSAlgebraEquiv` is an equivalence of the actual full quotient,
preserving every ordinary degree submodule by equality and commuting with inclusions.
The `Diagram/GaloisAction` facade uses the existing `GradedDiagramAut` constructor to package
these components and identity on the one common target. Its marking squares agree on both
ordered generators and hence on the full target algebra. `galoisGradedAction` records the group
law. No algebraicity, perfectness, dimension lower bound or nonzero-coefficient condition is
required. The later comparison `galoisGradedAut_toGalois` belongs to
`Reconstruction/LocalRing` and is not part of this independent construction.
Classification first concerns the explicit quadratic diagram. Extension to full graded
automorphisms follows classification, rather than an assumption that the OS algebra is
quadratic. The graded diagram uses the diagonal components indexed by degree. Fraction-field
descent uses finite free modules and relation spans, not an unproved localization property of
a cohomology theory.

Only the `HyperplaneGT/Cohomology/*` leaves import the geometric ordinary theory, its structure
theorem or the de Rham instance. A04 compares generator bases and the complete cup-product kernel,
including alternation in characteristic two, through the existing OS theorem. It does not infer
alternation from graded commutativity alone. E01–E03 transport the classified diagrams through
these comparisons. The de Rham specialization is `k`-linear on logarithmic generators, as in the
blueprint. The M7 `MainTheorem.lean` interface remains unchanged.

The following modules give the approved layout, relative to `OrlikSolomon/`; they are planned
except where identified as implemented or formalized. Their work-item IDs are those of the
approved plan; the issue links identify the implementation work.

| Module | Responsibility | Work item and issue |
| --- | --- | --- |
| `Algebra/HomogeneousRelations` | Implemented generic lowest-degree relation spans, with explicit degree-zero assumptions and an exterior-quotient kernel consumer; used by A02 | W02, [#154](https://github.com/adamtopaz/OrlikSolomon/issues/154) |
| `Algebra/FinsuppKernel` | Implemented generic kernel calculation for maps that discard labels and merge equal retained labels; applied by L01 | W10, [#162](https://github.com/adamtopaz/OrlikSolomon/issues/162) |
| `HyperplaneGT/Geometry/Coordinates` | Formalized G01–G03 facade joining the coefficient, graph and strict-incidence APIs | W03, [#155](https://github.com/adamtopaz/OrlikSolomon/issues/155) |
| `HyperplaneGT/Geometry/Coordinates/Equations` | Coefficient tuples of affine forms and the coefficient-point equivalence, G01 | W03, [#155](https://github.com/adamtopaz/OrlikSolomon/issues/155) |
| `HyperplaneGT/Geometry/Coordinates/Incidence` | Strict parallelism, guarded dependent triples, normal-form dichotomy, equation/point/trace criteria, G02 | W03, [#155](https://github.com/adamtopaz/OrlikSolomon/issues/155) |
| `HyperplaneGT/Geometry/Coordinates/Graphs` | Equation-independent verticality, unique graph equations, affine projection equivalences and exact projected traces, G03 | W03, [#155](https://github.com/adamtopaz/OrlikSolomon/issues/155) |
| `HyperplaneGT/Geometry/Galois`, with `CoordinateAction`, `Action`, `Orbits`, `System`, `Markings` and `AlgebraicMaps` leaves | G04–G06, formalized: coefficient action, finite orbits, cofinal systems, tagged fixed fibers and actual marking maps | W04, [#156](https://github.com/adamtopaz/OrlikSolomon/issues/156) |
| `HyperplaneGT/Algebra/DegreeOne` | A01, formalized: canonical degree-one equivalence, basis, coordinates, inclusion naturality and full algebra generation | W05, [#157](https://github.com/adamtopaz/OrlikSolomon/issues/157) |
| `HyperplaneGT/Algebra/LowDegrees`, with a `QuadraticKernel` leaf | A02, formalized: exact degree-two kernel of the actual quotient, parallel-pair and guarded dependent-triple spans, generator formulas and inclusion naturality | W06, [#158](https://github.com/adamtopaz/OrlikSolomon/issues/158) |
| `HyperplaneGT/Diagram/Basic` | A03, formalized: explicit marked quadratic and full graded automorphism groups, with faithful degree-one restriction | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `HyperplaneGT/Diagram/Basic/MarkingMaps` | Canonical ordered linear and full OS marking maps, target kernel and degree-one comparison | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `HyperplaneGT/Diagram/Basic/Quadratic` | Whole-Q image equality, one shared target, exact arrow squares and the quadratic subgroup API | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `HyperplaneGT/Diagram/Basic/Graded` | Full OS algebra subgroup preserving every degree and the inclusion/marking squares | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `HyperplaneGT/Diagram/Basic/Restriction` | Faithful group homomorphism from full graded to quadratic automorphisms using A01–A02 | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `HyperplaneGT/Diagram/Universal`, with `Support`, `Lift`, `Relations`, and `Automorphisms` leaves | U01–U02, formalized: literal universal Finsupp module, supported stage images and universal lift, global relation span and common stage witnesses, and induced diagram action retaining its common target | W08, [#160](https://github.com/adamtopaz/OrlikSolomon/issues/160) |
| `HyperplaneGT/Algebra/Dual` | U03–U05 facade: generic dual and primitive APIs, actual universal-Q configuration tests and paired diagram action | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Algebra/Dual/Coordinates` | Full-product dual coordinates, evaluation separation and inverse-precomposition automorphism homomorphism, U03 | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Algebra/Dual/Primitive` | Surjective primitive functionals and the local-ring unit-coordinate criterion, U05 | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Algebra/Dual/Alternating` | Determinant exterior lift, explicit-Q centralizer, coordinate tests and generic paired invariance, U04 | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Algebra/Dual/Configurations` | U04: determinant tests for the literal global parallel-pair/guarded-triple relation span, without cofinal-system hypotheses | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Algebra/Dual/DiagramAction` | U04: actual DiagramAut contragredient homomorphism, paired commuting invariance and centralizer image equality | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `HyperplaneGT/Reconstruction/Trace` | L01–L03, formalized: exact trace kernel, inertia/decomposition, evaluation annihilators and actual graph restriction | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Geometry` | Intrinsic labels through the existing chart, optional actual traces and geometric label surjectivity | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Map` | Literal supported domain, canonical free-module coordinates and surjective trace map | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Kernel` | Actual ambient kernel and exact strict-parallel / guarded-triple generator span | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Decomposition` | Coordinate delta inertia, coordinate-defined decomposition and explicit full-product equivalence | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Annihilators` | Four direct evaluation-annihilator equalities and the actual-Q unit-delta centralizer | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `HyperplaneGT/Reconstruction/Trace/Projection` | Derived vertical-trace bijection, supported vertical module and actual dual restriction, including low dimensions | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `Algebra/UnitTransfer` | Generic three-equation unit cancellation over arbitrary commutative rings, used by L04 | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `HyperplaneGT/Reconstruction/Local` | L04–L05, formalized: actual centralizer restriction, local transfer and unique unit-supported graph detection | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `HyperplaneGT/Reconstruction/Local/Geometry` | Distinct parallel and meeting graphs and the two guarded vertical transfer triples, over arbitrary fields | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `HyperplaneGT/Reconstruction/Local/Transfer` | Literal actual-Q centralizer restriction and L04 over arbitrary commutative coefficient rings | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `HyperplaneGT/Reconstruction/Local/Detection` | L05 equivalence, coordinate-independent unique graph/unit pair and actual decomposition centralizer | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `HyperplaneGT/Reconstruction/Projections` | P01–P02, formalized: intrinsic coordinate-span recognition and actual equivariant vertical restrictions | W13, [#165](https://github.com/adamtopaz/OrlikSolomon/issues/165) |
| `HyperplaneGT/Reconstruction/Projections/Geometry` | Coordinate level labels and guarded equation-span/trace-exclusion geometry for P01 | W13, [#165](https://github.com/adamtopaz/OrlikSolomon/issues/165) |
| `HyperplaneGT/Reconstruction/Projections/Recognition` | Arbitrary supported restriction, actual coordinate planes, trace-functional coefficient detector and full P01 iff | W13, [#165](https://github.com/adamtopaz/OrlikSolomon/issues/165) |
| `HyperplaneGT/Reconstruction/Projections/Invariance` | Actual marking-plane image equality, P02 induction, restricted universal/dual action homomorphisms and actual restriction square | W13, [#165](https://github.com/adamtopaz/OrlikSolomon/issues/165) |
| `HyperplaneGT/Reconstruction/Incidence` | I01–I04, formalized: canonical inertia permutation, actual trace/incidence transport, projective action and individually fixed marked frame | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Reconstruction/Incidence/Inertia` | Derive every actual L05 hypothesis from graph restriction, the P02 square and common-target marking planes | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Reconstruction/Incidence/Permutation` | Canonical unique labels and dual units, inverse primal scalar, inertia/decomposition/generator images and group laws | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Reconstruction/Incidence/Relations` | Actual trace-domain/kernel images and strict parallel/dependent-triple equivalences in both directions | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Reconstruction/Incidence/Projective` | Arbitrary-field coefficient-point extension, exact line images and the actual projective group action | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Reconstruction/Incidence/Markings` | One common target excludes uniform exchange, fixes each marked fiber and supplies all basis/difference frame points | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `HyperplaneGT/Geometry/Collineation`, with `Span`, `Chart`, and `Field` leaves | C01–C03, formalized: arbitrary projective spans, coordinatewise affine charts, and a unique field automorphism from the prescribed frame | W15, [#167](https://github.com/adamtopaz/OrlikSolomon/issues/167) |
| `HyperplaneGT/Reconstruction/Galois` | C04, S01, formalized: actual Galois extraction and its unique common primal scalar kernel | W16, [#168](https://github.com/adamtopaz/OrlikSolomon/issues/168) |
| `HyperplaneGT/Reconstruction/Galois/Geometry` | Pure intersecting-triple and transverse-parallel-pair witnesses, guarded connectivity over arbitrary fields | W16, [#168](https://github.com/adamtopaz/OrlikSolomon/issues/168) |
| `HyperplaneGT/Reconstruction/Galois/Extraction` | Actual fixed-frame field extraction, marked-constant and field-generation descent, Galois homomorphism and recovered action | W16, [#168](https://github.com/adamtopaz/OrlikSolomon/issues/168) |
| `HyperplaneGT/Reconstruction/Galois/Scalar` | Actual trace-kernel unit equality, connectivity, all-stage/common-target scalar identities and uniqueness | W16, [#168](https://github.com/adamtopaz/OrlikSolomon/issues/168) |
| `HyperplaneGT/Diagram/GaloisAction`, with a `Stage` leaf | S02, formalized: direct coefficient-linear action on full OS algebras, every-degree image equality, inclusion and marking squares, group laws and identity common target | W17, [#169](https://github.com/adamtopaz/OrlikSolomon/issues/169) |
| `HyperplaneGT/Reconstruction/LocalRing` | S03–S04 formalized: actual quadratic/full graded classification, degree powers and both canonical central scalar quotients with explicit inverse sections | W18–W19, [#170](https://github.com/adamtopaz/OrlikSolomon/issues/170), [#171](https://github.com/adamtopaz/OrlikSolomon/issues/171) |
| `HyperplaneGT/Reconstruction/LocalRing/Scalar` | Pure unit-scalar families, whole relation-image equality, common-target formulas, injective homomorphism and literal central range over arbitrary commutative rings | W18, [#170](https://github.com/adamtopaz/OrlikSolomon/issues/170) |
| `HyperplaneGT/Reconstruction/LocalRing/Splitting` | Canonical restriction of the existing S02 action, actual generator/target formulas, comparison with C04 extraction and literal scalar-kernel equality | W18, [#170](https://github.com/adamtopaz/OrlikSolomon/issues/170) |
| `HyperplaneGT/Reconstruction/LocalRing/Quadratic` | Right-normalized primal scalar, canonical multiplicative equivalence, both inverse equations and actual stage/universal/common-target/marking/dual formulas | W18, [#170](https://github.com/adamtopaz/OrlikSolomon/issues/170) |
| `HyperplaneGT/Reconstruction/LocalRing/GradedScalar` | Pure scaling of all OS relators and ordinary components, full scalar families with actual arrows/common target, faithful scalar restriction and literal central range | W19, [#171](https://github.com/adamtopaz/OrlikSolomon/issues/171) |
| `HyperplaneGT/Reconstruction/LocalRing/Graded` | Existing degree-one restriction as a MulEquiv after S03, explicit full scalar/Galois inverse, generator/degree/target formulas and actual marking squares | W19, [#171](https://github.com/adamtopaz/OrlikSolomon/issues/171) |
| `HyperplaneGT/Reconstruction/LocalRing/Quotient` | Normality of both literal scalar ranges, canonical quotient maps and Galois sections, both quotient-to-Galois MulEquivs/inverse laws and restriction compatibility | W19, [#171](https://github.com/adamtopaz/OrlikSolomon/issues/171) |
| `HyperplaneGT/Reconstruction/Domain` | S05 formalized: arbitrary integral-domain quadratic/full graded classification, both literal scalar quotients and agreement with local classification | W20, [#172](https://github.com/adamtopaz/OrlikSolomon/issues/172) |
| `HyperplaneGT/Reconstruction/Domain/LinearExtension` | Pure free-module coefficient extension, matrix/inverse and naturality identities, using Mathlib free-module maps | W20, #172 |
| `HyperplaneGT/Reconstruction/Domain/Relations` | Exterior coefficient maps and coefficient-extended span witnesses for both actual A02 relation families | W20, #172 |
| `HyperplaneGT/Reconstruction/Domain/Diagram` | Actual quadratic diagram coefficient extension, single common target, group laws and faithfulness for injective coefficient maps | W20, #172 |
| `HyperplaneGT/Reconstruction/Domain/Descent` | Fraction-field classification, original scalar/inverse matrix-entry descent and canonical quadratic formulas | W20, #172 |
| `HyperplaneGT/Reconstruction/Domain/Graded` | Classified full scalar/Galois extension, actual degree-one restriction equivalence and whole-degree formulas | W20, #172 |
| `HyperplaneGT/Reconstruction/Domain/Quotient` | Both literal scalar quotients, explicit sections, restriction square and agreement with local classification | W20, #172 |
| `HyperplaneGT/Cohomology/Adapter` | A04, formalized: facade comparing actual degree-one/cup-kernel and full diagonal-cohomology diagrams with A03 | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/Maps` | One actual scheme target, tagged scheme marking maps, localization and unit/logarithm squares, actual component and diagonal pullbacks | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/DegreeOne` | Canonical actual logarithmic bases and ordered target coordinates, with actual inclusion/marking comparison squares | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/CupKernel` | Actual multiplication, OS-derived alternation including characteristic two, complete cup-kernel equality and whole target kernel | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/Quadratic` | Actual H11 automorphism subgroup preserving whole cup-kernel images and all actual inclusion/marking arrows | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/Graded` | Actual diagonal-cohomology automorphism subgroup preserving every actual summand by equality and all actual arrows | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/Comparison` | Two-way quadratic/full graded group equivalences, full diagonal naturality, scalar transport and faithful literal degree-one restriction | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Adapter/Examples` | Supplied-theory zero/characteristic-two, dimension-zero target and point-free binary-target consumers, plus inherited carrier-instance pins | W21, [#173](https://github.com/adamtopaz/OrlikSolomon/issues/173) |
| `HyperplaneGT/Cohomology/Main` | E01–E02 | W22, [#174](https://github.com/adamtopaz/OrlikSolomon/issues/174) |
| `HyperplaneGT/Cohomology/DeRham` | E03 | W23, [#175](https://github.com/adamtopaz/OrlikSolomon/issues/175) |
| `HyperplaneGT`, `HyperplaneGT/Cohomology` | Pure-core facade and conditional-cohomology facade; de Rham remains an explicit import | W22–W23, [#174](https://github.com/adamtopaz/OrlikSolomon/issues/174), [#175](https://github.com/adamtopaz/OrlikSolomon/issues/175) |
| `Examples/HyperplaneGT`, with small topic leaves | Coefficient, dimension, marking, cofinality, generator and transport acceptance consumers | W24, [#176](https://github.com/adamtopaz/OrlikSolomon/issues/176) |
| `Examples/HyperplaneGT/DegreeOne` | Formalized A01 consumers: zero coefficients, empty arrangements, dimensions zero and one, and zero new coordinates after inclusion | W05, [#157](https://github.com/adamtopaz/OrlikSolomon/issues/157) |
| `Examples/HyperplaneGT/Collineation` | Formalized C01–C03 consumers: identity extraction, dimension-zero charts, characteristic-two zero sums and points at infinity | W15, [#167](https://github.com/adamtopaz/OrlikSolomon/issues/167) |
| `Examples/HyperplaneGT/GaloisReconstruction` | C04/S01 consumers: guarded binary connectivity, actual scalar kernels over `ZMod 5`/`ZMod 4`, composition and necessary field generation | W16, [#168](https://github.com/adamtopaz/OrlikSolomon/issues/168) |
| `Examples/HyperplaneGT/Coordinates` | G01–G03 consumers: dimension zero, parallel points, inverse chart and coefficient formulas, zero-ring coordinate splitting, and concurrent/empty triples over `𝔽₂` | W03, [#155](https://github.com/adamtopaz/OrlikSolomon/issues/155) |
| `Examples/HyperplaneGT/Dual` | Full infinite dual coordinates, primitive edge tests, actual universal-Q characteristic-two configurations, zero/dimension-zero centralizers and non-involutive scalar DiagramAut action over ZMod 5 | W09, [#161](https://github.com/adamtopaz/OrlikSolomon/issues/161) |
| `Examples/HyperplaneGT/QuadraticKernel` | A02 consumers: empty and dimension-zero arrangements, zero coefficients, disjoint points, characteristic-two concurrent relations and the zero quadratic kernel of the empty triangle | W06, [#158](https://github.com/adamtopaz/OrlikSolomon/issues/158) |
| `Examples/HyperplaneGT/Galois` | G04–G06 consumers: public point maps, finite stable enlargement, actual inclusions, dimension zero and characteristic-two orbits | W04, [#156](https://github.com/adamtopaz/OrlikSolomon/issues/156) |
| `Examples/HyperplaneGT/Universal` | U01–U02 consumers: common vector/relator stages, zero coefficients, independent-universe linear lifts and the essential common-target component in dimension zero | W08, [#160](https://github.com/adamtopaz/OrlikSolomon/issues/160) |
| `Examples/HyperplaneGT/GaloisAction` | S02 consumers: all-length relators, zero coefficients, dimension zero, full marking squares, a characteristic-two cubic relation and nontrivial complex conjugation on an integral OS generator | W17, [#169](https://github.com/adamtopaz/OrlikSolomon/issues/169) |
| `Examples/HyperplaneGT/Diagram` | A03 consumers: concrete constructors, zero coefficients, characteristic-two relations, Laurent-polynomial marking maps, and dimension-zero target interchange | W07, [#159](https://github.com/adamtopaz/OrlikSolomon/issues/159) |
| `Examples/HyperplaneGT/Trace` | L01–L03 consumers: discarded/merged traces, empty-triangle guard, zero and nilpotent coefficients, low dimensions and a nonzero actual vertical target | W11, [#163](https://github.com/adamtopaz/OrlikSolomon/issues/163) |
| `Examples/HyperplaneGT/Local` | L04–L05 consumers: zero-ring transfer, a nonzero actual vertical target over `ZMod 4`, characteristic-two dual numbers with nonzero nilpotents and a dimension-one counterexample satisfying all four actual conditions | W12, [#164](https://github.com/adamtopaz/OrlikSolomon/issues/164) |
| `Examples/HyperplaneGT/Projections` | P01–P02 consumers: characteristic-two geometry with a nilpotent `ZMod 4` detector, a nonvacuous `ZMod 2` coefficient recognition test, semiring restriction, zero/low-dimensional/full-coordinate cases, both inverse cancellations and inverse-three vertical dual action over `ZMod 5` | W13, [#165](https://github.com/adamtopaz/OrlikSolomon/issues/165) |
| `Examples/HyperplaneGT/Incidence` | I01–I04 consumers: actual primal/dual units and group cancellation, nonfield local coefficients, characteristic-two exchanged-triple obstruction and the complete fixed frame | W14, [#166](https://github.com/adamtopaz/OrlikSolomon/issues/166) |
| `Examples/HyperplaneGT/LocalClassification` | S03 consumers: independent-universe components, both inverse equations/cancellation, actual markings, primal two/dual three over `ZMod 5`, nilpotents in nonfield local `ZMod 4`, nontrivial complex conjugation and retained target at dimension zero/zero coefficients | W18, [#170](https://github.com/adamtopaz/OrlikSolomon/issues/170) |
| `Examples/HyperplaneGT/GradedClassification` | S04 consumers: nonzero degree-two powers, characteristic-two nilpotent units, exact full markings and inverse cancellation, dimension-zero common target and nontrivial conjugation classes in both scalar quotients | W19, [#171](https://github.com/adamtopaz/OrlikSolomon/issues/171) |
| `Examples/HyperplaneGT/DomainClassification` | Independent-universe, nonlocal integer coefficient, original unit-entry, quotient inverse, whole-degree, local overlap, noninjective coefficient-change and map-to-zero consumers | W20, #172 |

`HyperplaneGT/Algebra/LowDegrees` joins `DegreeOne` and `QuadraticKernel`. The latter restricts
the actual exterior quotient to `osExteriorSquareMap`, surjective onto the existing internal
degree-two submodule. Its generic finite-dimensional extraction `osExteriorSquareMap_ker_eq`
uses homogeneous projection and the existing minimum lengths of empty and guarded dependent
lists. Relators in two different degrees are zero, so the proof works over the zero ring.
`quadraticKernel_eq_span` identifies the complete kernel with `quadraticRelationSpan`, using
all strict parallel pairs and all guarded dependent triples on the hyperplane labels. The
public exterior-pair and difference-pair formulas hide subtype representatives. Exterior-square
label inclusion commutes with the quotient and preserves the full quadratic relation span.
There is no assertion that the higher OS relations are generated by the quadratic kernel.

`HyperplaneGT/Geometry/Coordinates` is a facade over three leaves. `Equations` represents affine
forms by their constant and normal coefficients, using Mathlib's affine-map decomposition,
standard-coordinate equivalence and `Fin.consLinearEquiv`. These form calculations work over
commutative rings. Over a field, `coefficientPointEquiv` identifies the existing affine-subspace
hyperplanes with all projective coefficient points except the constant point, with representative
and inverse computation lemmas. `Incidence` uses strict `Parallel` and guarded `DependentTriple`
predicates; it reuses the existing kernel-comparison and codimension lemmas to identify normal,
equation, projective-point and nonempty-trace criteria. `Graphs` uses finite coordinate sets with
their member subtypes, has an equation-independent verticality test, and normalizes each
nonvertical hyperplane to a unique graph. `graphProjectionEquiv` has an explicit inverse and
`map_graphSubspace_inf` computes the projected intersection exactly. The facade supplies the
strict-parallel graph wrapper. These statements have no characteristic or dimension lower bound
and import no cohomology theory. The empty-triangle regression over `𝔽₂` tests the nonemptiness
guard even though the conventional codimension of the empty plane subspace is two.

`Dual/Coordinates`, `Dual/Primitive` and `Dual/Alternating` supply generic APIs with
coefficient, index and ambient-module universes independent. Their imports remain free of
hyperplane geometry and diagrams. The `Algebra/Dual` facade also re-exports the specialized
`Configurations` and `DiagramAction` leaves described below.
`dualCoordinates` reverses Mathlib's `Finsupp.llift` equivalence;
its inverse evaluates a finite sum, and the dual is the full function product. Evaluation
separates both vectors and functionals. `dualAction` is the homomorphism sending `g` to
`g.symm.dualMap`, so simultaneous action preserves evaluation. No reflexivity or finite-index
assumption is used. `map_dualCoannihilator_dualAction` transports evaluation coannihilators
through the paired action without any double-dual identification. These APIs work over
commutative semirings.
`unit_smul_lapply_eq_iff` separates unit multiples of coordinate functionals over a nontrivial
commutative semiring, independently of any chosen geometric coordinate projection.

`Primitive` means literal surjectivity. It is invariant under precomposition by every linear
equivalence. A unit coordinate is sufficient over any commutative semiring; the converse uses
`IsLocalRing`, which already includes nontriviality. The proof uses only the finite support of a
preimage of one and Mathlib's local-ring unit-sum theorem. The empty-index zero-ring consumer is
surjective with no coordinate witness, and the nonlocal integer consumer has coordinates two
and three and is surjective with neither coordinate a unit. No infinite-product residue-field
criterion replaces this definition.

Over commutative rings, `dualDeterminant` reuses Mathlib's alternating exterior-dual pairing.
`Commutes Q` means that this map kills an explicit `Q : Submodule R (⋀[R]^2 M)`, and
`centralizer Q` is the comap of its dual annihilator along the determinant map linear in the
second functional. Pair and difference-vector formulas give the generic coordinate equations.
`commutes_dualAction_iff` assumes equality of the exterior-square image of Q with Q and proves
both directions, including inverse preservation. There is no new diagram or relation structure.
`Dual/Configurations` uses exactly `Diagram/Universal/Relations`'s
`universalQuadraticRelationSpan` on the literal free module `Hyperplane k n →₀ R`. Its
commuting and centralizer membership tests are the determinant equations on all strict
parallel pairs and guarded dependent triples, reusing the generic determinant and
span-annihilation APIs. `Dual/DiagramAction` composes the generic contragredient homomorphism
with `DiagramAut.universalAction`. Its map is inverse precomposition through `universalEquiv`;
equality preserving the entire global relation span gives paired commuting invariance in both
directions and equality of the centralizer images. These specialization leaves introduce no
second relation module, universal module or diagram structure. They require only commutative
coefficient rings and the existing field/cofinal-system parameters, with no nonzero, local,
perfect, algebraic or dimension assumption.

`Configurations` imports only the specific generic `Dual/Alternating` and
`Diagram/Universal/Relations` leaves. `DiagramAction` imports it and
`Diagram/Universal/Automorphisms`. The generic leaves do not import either specialization or a
diagram facade, and `Diagram/Universal/*` does not import the `Algebra/Dual` facade. This keeps
the dependency graph acyclic and adds no cohomology or de Rham import. Durable consumers test
actual parallel points and a guarded concurrent triple over `𝔽₂`, zero coefficients, dimension
zero and a scalar-two marked diagram over `ℤ/5`, whose dual scalar is three.

`HyperplaneGT/Diagram/Universal` uses the literal module `Hyperplane k n →₀ R`.
`Support` includes every finite arrangement by `finiteStageMap`, exactly extension by zero
along the existing `arrangementHyperplane` label map. Its range is Mathlib's supported
submodule, and cofinality supplies simultaneous representatives and common-stage equality
witnesses for any chosen family. `Lift` gives the explicit linear direct-limit universal
property for compatible stage maps into any coefficient module; it stores no second diagram.
`Relations` defines `universalQuadraticRelationSpan` as the span of all parallel-pair and
guarded dependent-triple wedges. It proves containment of each actual finite relation-span
image and finite-stage witnesses for every global relation and finite family of relations,
without degree-two injectivity. `Automorphisms` applies this universal property to the existing
`DiagramAut`, preserving the whole global span and each stage image by equality. Its universal
action and one common target action jointly determine the original family. No union closure,
perfectness, algebraicity, positive dimension or nonzero coefficients are assumed here.
The generic Dual leaves remain independent of this layer.

`osDegreeOneEquiv R 𝒜 : (𝒜 →₀ R) ≃ₗ[R] OSAlgebra.degree R 𝒜 1` is the canonical finite
linear combination of the hyperplane generators. Its inverse and `osDegreeOneBasis` expose
coordinates without unfolding the construction. `osDegreeOneMap` restricts presentation
inclusions to degree one, with identity, composition and generator formulas;
`osDegreeOneEquiv_naturality` and `osDegreeOneEquiv_symm_map` identify these maps with extension
of coefficients along the label inclusion. The equivalence assumes a finite-dimensional ambient
space, as does the existing generator independence theorem. Full algebra generation
(`exists_os_word_sum`, `adjoin_range_osGenerator`) and the typed inclusion maps do not require
finite-dimensionality. All these statements allow the zero coefficient ring and import no
cohomology theory.

`Geometry/Collineation` is a pure facade over three size leaves. `Span` defines
`PreservesProjectiveLines` as exact image equality for the projective span of each distinct
pair, with identity, inverse and composition lemmas; `collineation_preserves_span` derives
image equality for arbitrary spans. `Chart` constructs the actual normalized chart permutation
and its axis bijections without a dimension bound. `Field` retains `2 ≤ n` and the explicit
fixed points `[eᵢ - e₀]` and `[eᵢ - eⱼ]`; the first family fixes minus one and is separate from
the coordinate points. Sum-line calculations use an affine point and a point at infinity, so
zero sums cause no coincident-endpoint argument. `coordinateFieldEquiv_mk` covers nonzero
homogeneous vectors in both the affine chart and the hyperplane at infinity, and
`existsUnique_coordinateFieldEquiv` supplies uniqueness. All leaves import only Mathlib and
their preceding pure collineation leaves. `Examples/HyperplaneGT/Collineation` checks the
identity extraction, dimension-zero charts, characteristic-two zero sums and infinity.

`Geometry/Galois` is a pure facade over six leaves. `CoordinateAction` transports affine
subspaces by a coordinatewise field automorphism and proves intersection, empty-subspace and
codimension preservation; its additive point equivalence reuses Mathlib's product equivalence
and works without downstream inverse-pair instances. `fieldCoordinateLinearMap` exposes semilinear scalar transport without inverse-pair instances;
a private semilinear equivalence is used only for the rank comparison. `Action` constructs the genuine Galois action on
hyperplanes. `Orbits` bounds conjugates of a fixed equation by finite minimal-polynomial root
sets, constructs the least stable finite enlargement and the full cofinal system. Only this
finite-orbit construction requires algebraicity; no leaf assumes perfectness or normality.

`System` permits arbitrary chosen cofinal families, not just the full family. Common upper
stages follow from cofinality rather than union closure. `StableArrangement` and
`CofinalSystem.Stage` are intentionally `@[reducible] def` subtype synonyms: their inherited
inclusion order and thin-category instances require full transparency at the type head;
`@[instance_reducible]` alone does not synthesize the stage order. `Markings` uses tagged
coordinate translates and increasing coordinate differences, proves that every base-field
fiber is individually fixed, and supplies ordered zero/one labels compatible with inclusions.
`AlgebraicMaps` constructs one common `markingTarget k`, independent of the tag or stage, and
actual `SmoothAlg.complementMap` pullbacks satisfying the inclusion square and the two unit
formulas. These algebra maps have the variance opposite to the geometric arrows. A04 performs
the later scheme-open and theory transport. `Examples/HyperplaneGT/Galois` exercises independent
field universes, dimension zero, characteristic two and actual stage morphisms.

`Diagram/Basic` is a facade over four size leaves. `MarkingMaps` reuses the ordered fiber
labels and the one existing `twoPunctureArrangement k`. Its injective `Marking.basisMap`
carries the entire target exterior square into `quadraticRelationSpan`; the actual ordered
target exterior-square quotient is zero. `Marking.osMap` checks the full target presentation,
preserves every OS degree and agrees with the linear arrow in degree one. `Quadratic` defines
`DiagramAut` by equality of the entire Q images and exactly the inclusion/marking squares.
`Graded` uses existing OS AlgEquivs preserving every homogeneous component by image equality.
`Restriction` proves `GradedDiagramAut.toQuadratic` is faithful, using the actual quotient
kernel and full generation in degree one. It claims no extension or reconstruction theorem.

`QuadraticAutFamily`, `DiagramAut`, `GradedAutFamily` and `GradedDiagramAut` are named
`@[reducible] def` product/subtype synonyms. The attempted `@[instance_reducible]` product
synonym does not expose its carrier to the inherited product `Group` instance when forming
the subgroup. Full transparency inherits the literal product/subgroup instances and operations
without duplicate transport instances, matching the `StableArrangement`/`Stage` convention.
Constructors, projections, `simp` and `ext` lemmas hide that representation from consumers.
One target component is shared by all tags and stages and retained in extensionality;
`Examples/HyperplaneGT/Diagram` shows that in dimension zero it can be nontrivial even when all
stage maps are identities. Its other concrete consumers cover zero, characteristic-two and
`LaurentPolynomial ℤ` coefficients. These APIs assume arbitrary commutative coefficient
rings and independent field universes, with no dimension bound, condition on the marking
constants, algebraicity/perfectness assumption or union-closure requirement on the cofinal
family. They import no cohomology theory.

`Cohomology/Adapter` is a facade over six size leaves, with all theory imports confined
inside the existing cohomology boundary. `Maps` uses the actual `D.complementMap` and
`D.complementInclusion` morphisms; its localization square compares a tagged scheme marking
with the existing `Marking.algebraicMap`. The two ordered target units pull back to the actual
fiber equations. `DegreeOne` composes A01 coordinates with the existing `T.degreeEquiv` and
proves both actual arrow squares. `CupKernel` transports square-zero from the full OS algebra,
so alternation holds in characteristic two without cancelling 2. Its whole kernel is exactly
the image of A02's parallel-pair/guarded-triple span; the whole target exterior square is kernel.

The actual `Cohomology.DiagramAut` and `Cohomology.GradedDiagramAut` are subgroups on actual
H11 modules and actual diagonal direct sums. They are not defined as normalized presentation
models. `Comparison` proves membership in the actual subgroups equivalent to membership in
A03's subgroups under canonical conjugation, giving two-way `MulEquiv`s and forward/inverse
component formulas. The existing `T.diagonalEquiv` commutes with all actual inclusion and
tagged marking pullbacks. Restriction is constructed through those canonical comparisons and
then identified with literal action on both actual degree-one summands. It is faithful.
Scalar transport characterizes multiplication by the same fixed unit in degree one and its
q-th power in every degree, at stages and the common target, without assuming classification.

The four actual product/subgroup carriers use the same named `@[reducible] def` exception
as their A03 counterparts, solely to inherit literal group instances and operations.
The actual `diagonal` carrier is also `@[reducible] def`: a strict probe with
`@[instance_reducible]` failed to inherit even `AddCommMonoid`, `Module`, `Ring` and `Algebra`
from its direct-sum carrier, while the transparent synonym inherited all four. No duplicate
transport instances are introduced. The definition docstrings and committed instance
consumers record this approved exception. The other actual degree-one and degree-two
submodule definitions retain ordinary transparency.

`Adapter/Examples` stays within the same import boundary and imports no de Rham instance.
Its zero-coefficient, characteristic-two, dimension-zero nonidentity-target and binary-target
basis consumers are conditional statements with a supplied full `Geometric.OrdinaryTheory`.
They do not construct or assert the existence of a nonzero mod-2 realization. The binary
coordinate target has no rational point, and its ordered cohomology basis still follows
from a supplied theory. A04 adds no theory record, axiom or extra coefficient/field/cofinality
hypothesis, and constructs no new nonzero theory instance. The reconstruction conclusions
and the de Rham specialization remain separate later work.

The generic helper modules use namespace `OrlikSolomon` and carry no hyperplane/cohomology
hypotheses. Check Mathlib and existing repository lemmas before adding any helper. Split modules
before approximately 800 lines; list size-only splits within the approved import boundaries in
the PR body. Public named objects follow the existing transparency conventions, with `simp`,
`ext` and generator lemmas so consumers do not rely on unfolding. Each PR names its blueprint
labels, proves strict downstream consumers and adds new library modules to the sorted root
import list.

`Algebra/FinsuppKernel` (#162) implements the optional-label map `finsuppOptionMap` as Mathlib's
domain pushforward followed by restriction to `some` labels. The map, its `simp` formula on
single vectors and its surjectivity theorem work over any semiring. Over any ring,
`ker_finsuppOptionMap` identifies the kernel with `finsuppOptionRelationSpan`: discarded basis
vectors and differences of basis vectors with the same retained label. Commutativity,
nontriviality, finite label types and surjectivity are not assumptions of that identity.
`ker_finsuppOptionMap_le_iff` and `ker_finsuppOptionMap_le_ker_iff` let consumers test containment
and annihilation of this kernel without unfolding the relation span. Representatives are chosen
only inside the proof, not in the public API. `Examples/FinsuppKernel` exercises an empty target,
discarded and duplicate labels, characteristic two and zero coefficients through these APIs.
`Reconstruction/Trace` applies this generic kernel theorem to the actual trace labels. Its six
leaves separate geometry, the map, the kernel, decomposition coordinates, annihilators and graph
restriction. `IntrinsicHyperplane H` is an `@[instance_reducible] def` synonym for the existing
hyperplanes in `H.val.direction`, represented through `chart H.val`. The affine retraction
proves label surjectivity without redefining arrangement machinery for torsors. `traceDomain`
is the literal supported Finsupp submodule with coefficient at H zero; `traceKernel` is the
actual kernel embedded in the universal module. Its exact generators are strict parallel
singles and guarded dependent-triple differences, over arbitrary rings; the map and its
surjectivity already work over semirings.

`inertia` is the span of the actual delta functional and `decomposition` is defined by its
parallel/triple coordinate conditions. `decompositionEquiv` identifies it with the distinguished
value and the full function space on intrinsic traces. Coordinate delta and trace indicators
prove all four evaluation-annihilator equalities directly, with no reflexivity assumption.
`centralizer_unit_smul_delta` uses the actual global Q tests in every position and only unit
cancellation. `Projection` derives the bijection between vertical labels and actual intrinsic
traces from graph projection and the chart; `verticalRestriction` is restriction to the actual
supported vertical module. Its image on decomposition is the full dual and its kernel is
inertia. The decomposition results hold over arbitrary commutative rings, including zero,
with independent coefficient and geometric-field universes and exactly the omitted-coordinate
and nonvertical hypotheses. No theory imports are added. The durable examples pin the empty
triangle guard, characteristic two, a unit over `ZMod 4`, zero coefficients, dimension zero,
dimension-one `D = I`, and a nonzero actual vertical coordinate and its extension.

`Reconstruction/Local` separates generic arithmetic, pure graph witnesses, actual transfer and
local detection according to the [approved refinement](https://github.com/adamtopaz/OrlikSolomon/issues/164#issuecomment-6754221916).
`Algebra/UnitTransfer` imports only Mathlib and cancels a supplied unit in three equations over
any commutative ring. `Local/Geometry` imports only the pure coordinate facade: graph-function
differences give two distinct actual vertical labels and their guarded dependent triples.
Adding one gives a parallel graph; a remaining coordinate gives a meeting graph when `2 ≤ n`.
`Local/Transfer` imports these helpers, `Dual/Configurations` and `Trace/Projection`; its
`centralizerVerticalRestriction` is literal restriction of the actual universal-Q centralizer
to the dual of the actual supported vertical module. L04 adds no nonzero, locality or domain
hypothesis on the coefficients and no dimension lower bound beyond its omitted coordinate.
It uses no quotient-isomorphism assumption.
`Local/Detection` adds the generic primitive criterion and `Trace/Annihilators`. L05 retains
`IsLocalRing R` (including nontriviality), `2 ≤ n` and all four primitive/vertical/zero-graph/
centralizer-surjectivity conditions. It returns the unique actual graph/unit pair and equality
of its actual centralizer with decomposition. The generic coordinate-functional uniqueness iff
lives in the existing geometry-free `Dual/Coordinates` leaf. The facade reexports detection;
no earlier geometry or algebra leaf imports it, and no cohomology or extra diagram data enters.
The durable consumers use `ZMod 4`, characteristic-two dual numbers with a nonzero square-zero
scalar part, an actual nonzero vertical target, and zero-ring transfer. An actual two-supported
functional in dimension one satisfies all four conditions but is no unit delta, pinning the
necessary dimension bound.

`Reconstruction/Projections` reuses `Trace/Projection`'s literal `verticalModule R z` and
actual `verticalRestriction R z` for arbitrary finite coordinate subsets. `Geometry` supplies
coordinate level labels and the guarded equation-span/trace-exclusion facts for P01.
`Recognition` uses the existing supported Finsupp retraction for restriction surjectivity,
Mathlib's evaluation annihilator kernel, and L02 trace functionals to prove the full
commuting-functional recognition criterion over every commutative coefficient ring.
`Invariance` derives each marking-plane image equality from the existing common-target
marking square, then proves coordinate-span invariance using P01 and only `0 ∈ S`.
The induced dual equivalence is inverse precomposition through the actual invariant
supported submodule, with action homomorphisms and a proved restriction square. These leaves
introduce no competing universal module, relation span, diagram structure or projection-naturality
assumption, and import no cohomology or de Rham theory. Coefficients and both fields have
independent universes; no algebraicity, perfectness, local/nonzero coefficient condition or
dimension lower bound is imposed. The durable examples include a genuine nonzero nilpotent
coefficient detector over characteristic-two geometry, a nonvacuous recognition test with
`ZMod 2` coefficients, and an inverse-three vertical dual
coordinate for an actual scalar-two marked diagram over `ZMod 5`.

`Reconstruction/Incidence` derives the hyperplane permutation from L05 applied to the actual
contragredient images of deltas. `Inertia` obtains every detection hypothesis from the existing
graph restriction, P02 square and actual common-target marking planes. `Permutation` constructs
the unique label permutation, its dual-unit cocycle and inverse primal scalar, and proves the
actual inertia, decomposition and generator-line image equalities. `Relations` transports the
existing trace submodules by evaluation coannihilators and derives strict parallelism and guarded
dependent triples in both directions. Unit-weighted trace differences have a common retained
label and equal units; empty traces cannot be substituted. `Projective` extends the label
permutation through the existing coefficient-point equivalence, fixes the constant point, and
proves the existing exact projective-line image property. Its pure geometric assertions work
over arbitrary fields and in every dimension. `Markings` uses the single common target to fix
every marked zero/one fiber individually: its one matrix coefficient makes a possible exchange
uniform, and the actual dependent zero triple and empty one triangle exclude it even in
characteristic two. It exposes the full fixed basis/difference frame for later field
reconstruction. Diagram results retain only the explicit local/nonzero, dimension-at-least-two
and `0 ∈ S` hypotheses, with independent coefficient/field universes. No field automorphism,
scalar-kernel classification, arbitrary-projection arrow or cohomology/de Rham import enters.
The facade reexports the five approved leaves; no preceding leaf imports it.

`Reconstruction/Galois` derives its field equivalence by applying C03 to the actual incidence
permutation and the fixed frame already proved in I04. `Extraction` compares actual coordinate
fibers to fix every element of `S` and uses Mathlib's field-closure equality to descend to `k₀`;
the all-point projective formula gives the group homomorphism. No extracted field equivalence
is stored in diagram data. `Geometry` supplies the two pure connectivity witnesses with exact
nonempty/distinctness guards and arbitrary-codomain constancy along guarded dependent triples.
It imports only pure coordinate and local geometry, without diagram or cohomology dependencies.
`Scalar` uses I02's actual trace-kernel transport and its unit-weighted retained-trace test to
equate generator units, then the proved universal/stage/marking squares to include every stage
and the original common target. The common scalar is primal; I01's dual unit is its inverse.
The local/nonzero coefficient, `2 ≤ n`, `0 ∈ S` and subfield-generation hypotheses remain
explicit, with independent coefficient/field universes. These leaves construct neither a
splitting nor a cohomology realization and import no cohomology or de Rham module. The facade
reexports the three leaves; no earlier leaf imports it. Durable examples use the genuine
scalar-two and scalar-three diagrams over `ZMod 5` and the nonfield local ring `ZMod 4`,
characteristic-two guarded connectivity with a point-free complement, and complex conjugation
fixing `{0}` without fixing the entire base field, so field generation cannot be dropped.

`Reconstruction/LocalRing` classifies the existing marked quadratic diagram in S03 before
graded extension. `Scalar` constructs unit multiplication at every finite stage and the one
common target over arbitrary commutative rings; exterior-square unit multiplication preserves
each full relation submodule, and linearity makes its injective homomorphism range central.
`Splitting` restricts the existing S02 action through A03 and proves its comparison with the
C04 Galois projection; semilinear geometric coordinates are never passed to an ordinary
linear pullback API. `Quadratic` applies S01 to `g` times the inverse of its recovered Galois
factor on the right, producing a unique primal unit. The resulting `quadraticAutEquiv` is a
`MulEquiv` from coefficient units times the base-field automorphism group to the literal
`DiagramAut`, with both explicit inverse equations and all component formulas retaining the
common target. The forward and inverse expansion lemmas are ordinary rewrite rules, so
Mathlib's two-sided equivalence cancellation remains available to `simp`.
The reconstruction hypotheses are exactly a nonzero local coefficient ring, `2 ≤ n`,
`0 ∈ S` and `Subfield.closure S = ⊤`, together with the supplied arbitrary cofinal system.
Fields and coefficients have independent universes. No perfectness, algebraicity,
coefficient-field structure, union closure, scalar/monomiality premise, arbitrary projection
arrow or cohomology import is introduced. The scalar subgroup is the actual homomorphism
range, contained in Mathlib's center; no competing classification group is defined. The three leaves and final statements
have [Claude's explicit S03 approval](https://github.com/adamtopaz/OrlikSolomon/issues/170#issuecomment-6755665076).
S05 domain descent remains separate.


`GradedScalar` scales each full OS generator and checks both complete defining relator
families. Its `OSAlgebra.scalarEquiv` acts by the q-th scalar power on every ordinary degree-q
component, including degree zero and the one common target; the inclusion and tagged marking
squares are the actual OS maps. Restriction gives the existing quadratic scalar family, so
faithfulness proves full scalar injectivity and centrality over arbitrary commutative
coefficients. `Graded` uses S03 to extend only the classified scalar/Galois families. Its
`gradedAutEquiv` is directed from the literal full graded group to the quadratic group,
with exactly the existing `toQuadratic` as its forward map and an explicit scalar/Galois
inverse. Generation proves the original faithfulness; no quadratic presentation or arbitrary-Q
lifting principle enters. The forward expansion lemmas are plain rewrite rules, preserving
ordinary two-sided equivalence cancellation under `simp`. `Quotient` uses Mathlib's actual
quotient groups and the literal scalar homomorphism ranges, with one normality instance for
each central range. Both `scalarQuotientEquiv` constructions use the existing direct Galois
section as their explicit inverse. Quotient projection formulas, both inverse laws and the
square with actual graded restriction are exposed. These subgroups are scalar ranges;
no equality with the full group centers is asserted. The classified hypotheses are unchanged
from S03, and field/coefficient universes remain independent. The core imports no cohomology
or de Rham module and introduces no new carrier exception. The three leaves and final
statements have [Claude's explicit S04 approval](https://github.com/adamtopaz/OrlikSolomon/issues/171#issuecomment-6755893648).
Durable `Examples/HyperplaneGT/GradedClassification` pins a nonzero degree-two binary triangle
boundary with distinct scalar two and scalar-square four over `ZMod 5`, a nonidentity unit
with square one over characteristic-two dual numbers, the actual full restriction inverse
over nonfield local `ZMod 4`, zero coefficients, the retained target
in dimension zero, exact full marking squares and ordinary inverse cancellation. Complex
conjugation gives nonidentity elements in both actual scalar quotients, including on the
constructed full cofinal system. The degree-two consumer reuses the existing affine-triangle
regression, whose imports are confined to the example module rather than the pure core.

`Reconstruction/Domain` extends the matrices of the actual finite quadratic diagram along
coefficient maps, including the one common marking target and both explicit A02 relation
families. The extension uses Mathlib's free-module linear combinations and coefficient maps;
inverse matrix identities remain valid even for noninjective maps and maps to the zero ring.
Over an integral domain it applies the local theorem to the canonical fraction field and
descends the scalar and its inverse by injectivity of the coefficient map. The (0,0) entries
of the original forward and inverse common-target matrices recover the two coefficients in
the original ring; their product is one. Faithfulness descends equality of all stage and
target components. This proves the canonical quadratic and full graded classifications,
both literal central-scalar quotients with the existing Galois class sections, and agreement
with local classification on the overlap. Whole-degree formulas use the q-th power of the
primal unit, while the full-dual coordinate formula uses its inverse and the same covariant
Galois label. Forward expansion lemmas are plain rewrite rules, as in S03–S04, preserving
ordinary two-sided equivalence cancellation under `simp`. Pure coefficient extension needs
no injectivity or nonzero-ring hypothesis. No scalar extension or exactness statement about
an arbitrary cohomology theory is used; the core imports neither cohomology nor de Rham.
The six size-oriented leaves and final statements have
[Claude's explicit S05 approval](https://github.com/adamtopaz/OrlikSolomon/issues/172#issuecomment-6756221663).
Durable examples pin a nonidentity diagram over the nonlocal ring `ℤ`, recovered units in
that ring, both explicit quotient inverse laws, all-degree action, local/domain overlap,
noninjective reduction modulo two and the whole-target square after passage to zero.

The [supervisor's statement-review condition](https://github.com/adamtopaz/OrlikSolomon/issues/151#issuecomment-6750174454)
requires Claude's approval before proofs are finalized only for S03–S05, E01–E03 and statements
that deviate from the blueprint. Non-author Codex reviewers check intermediate statements
against the blueprint. Claude checks statements, scope, CI and book honesty before every M8
merge and decides every merge. Substantive mathematical gaps follow the existing blueprint-gap
process; only Claude scopes a request to Astra.

The book tracks 41 separately labelled statements under 38 logical node IDs. U01, U04 and L02
each have a definition and a lemma, with separate adjacent boxes. The current M8 count is
38 formalized and 3 planned, separate from the other blueprints. Each
mathematical PR names declarations only on the boxes it actually covers and records remaining
work for partial coverage. Keep the prose honest about local/domain hypotheses and conditional
versus unconditional realizations. W24 adds regression and acceptance coverage incrementally
and completes the final exposition checks.
