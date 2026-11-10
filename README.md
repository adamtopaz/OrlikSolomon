# OrlikSolomon

A Lean 4 and Mathlib formalization of the Orlik–Solomon structure theorem for the
cohomology of complements of hyperplane arrangements in affine and projective space.

The cohomology theory is not fixed. It is a structure whose fields are the standard
axioms: products, a dimension axiom at the point, affine-line invariance, and compatible
localization and divisor purity. From these, the library constructs a canonical
bigraded algebra isomorphism between the Orlik–Solomon algebra and the cohomology of the
complement. The base field is arbitrary, coefficients need not form a field, and Tate
twists stay explicit.

**Status:** the affine and projective structure theorems and their corollaries are proved,
for any structure satisfying the axioms. A nonzero instance of that structure is constructed in
Lean: algebraic de Rham cohomology over a field of characteristic zero, so the axioms are not
vacuous. Instantiated there, the theorems become unconditional statements about algebraic de Rham
cohomology, shown below. For any other cohomology theory, such as singular or ℓ-adic cohomology,
the theorems remain conditional: the axioms have been checked by hand against singular cohomology,
and interpreted by hand for ℓ-adic cohomology, but not in Lean. The empty projective arrangement
is excluded. The [book](https://adamtopaz.github.io/OrlikSolomon/) states the theorems and has the
details.

**Milestone M8 in progress:** cohomological hyperplane reconstruction is tracked by
[#151](https://github.com/adamtopaz/OrlikSolomon/issues/151) and its
[child issues](https://github.com/adamtopaz/OrlikSolomon/issues/151#issuecomment-6750266079),
under the [approved implementation plan](https://github.com/adamtopaz/OrlikSolomon/issues/151#issuecomment-6750159326).
Its [blueprint](blueprint/cohomological_hyperplane_gt_blueprint.tex) has 41 labelled statements:
32 formalized and 9 planned. Coefficient points, hyperplane incidence
and coordinate graphs (G01–G03) are proved over arbitrary fields. G04–G06 construct the
coefficient Galois action, finite stable enlargements over algebraic extensions, and cofinal
systems with actual marking maps to one common target. The canonical degree-one OS basis,
its inclusion naturality and algebra generation (A01), and the exact degree-two quotient kernel
(A02), are proved over arbitrary commutative coefficient rings, including zero coefficients.
A03 defines the marked quadratic and full graded automorphism groups, with one common target
and faithful degree-one restriction, over those same coefficient rings.
S02 constructs the direct Galois action on the full graded diagram using all defining OS
relations, with identity on its one common target.
U01–U02 give the universal free module, its finite-stage universal property and quadratic
relation witnesses, and the induced diagram action retaining the common target component.
Pure coordinate reconstruction (C01–C03) is also proved over arbitrary fields in dimension at least
two, with the prescribed fixed projective frame.
Full-dual coordinates and the local primitive-coordinate criterion
(U03, U05) are proved for arbitrary index types. The determinant and centralizer are defined
for any explicit relation submodule. U04 gives the exact universal parallel-pair and guarded
dependent-triple equations and paired diagram invariance, including equality of centralizer
images. L01–L03 prove the surjective trace map and its full kernel, the explicit decomposition
product and annihilator identities, the unit-delta centralizer, and graph restriction to the
actual vertical module with inertia kernel. L04 transfers graph coefficients by cancelling a specified
unit over any commutative ring. L05 detects a unique unit-supported graph functional over a
nonzero local ring in dimension at least two, from the four literal primitive, vertical, zero-coordinate
and centralizer-surjectivity conditions. P01–P02 recognize all coordinate-supported spans
using commuting functionals and derive their invariance and actual full-dual restriction
equivariance from the marking squares. I01–I04 recover the canonical hyperplane permutation,
preserve actual affine and projective incidence, and fix every marked fiber and the full
projective frame over nonzero local coefficients in dimension at least two, assuming zero
among the marking constants. The planned classification studies automorphisms of marked
degree-one/cup-kernel and diagonal graded cohomology diagrams in dimension at least two,
with nonzero local or integral-domain coefficients. The theory-level results will be conditional
on the existing axioms, with an unconditional characteristic-zero de Rham specialization.
The [book chapter](https://adamtopaz.github.io/OrlikSolomon/hyperplane-gt/) tracks the proved
and planned statements; the reconstruction theorem has not yet been formalized.

**The public theorem in one file.**
[`OrlikSolomon/MainTheorem.lean`](OrlikSolomon/MainTheorem.lean) is the auditable projective
interface. Its public definitions and theorem statements use Mathlib objects: hyperplanes are
subsets of `Proj k[x₀, …, xₙ]`, and their complement is the actual open subscheme. For every
supplied cohomology theory on a suitable class of smooth schemes, the theorem gives the
Orlik–Solomon isomorphism, sends `e_H - e_K` to `g^*τ` for the ratio map `g`, and maps every
bigraded piece onto the corresponding cohomology piece. The coefficients may be the zero ring.
The theorem allows the class of all smooth schemes; the verified nonzero de Rham example is
on smooth affine schemes in characteristic zero. No nonzero instance on all smooth schemes is
constructed. [The book chapter](https://adamtopaz.github.io/OrlikSolomon/main-theorem/) quotes
the interface and explains how to audit it.

The file is organized as public definitions (Part I), a clearly delimited private proof region
that readers may skip, public statements (Part II), then `#print axioms` on the five theorems.
The proof region precedes Part II because Lean does not allow forward references. After building,
`lake exe audit --interface` checks the provenance of the public types and data. The logical
axiom reports, `scripts/check.sh` and `scripts/replay.sh` give the accompanying trust checks.
The mathematical blueprints retain their separate status counts; this interface adds no
blueprint nodes.

**The theorems for algebraic de Rham cohomology.** For every field `k` of characteristic zero,
every arrangement `𝒜` of affine hyperplanes in a finite-dimensional `k`-vector space `V`, and every
nonempty arrangement `P` of hyperplanes in the projective space of `W`, there are isomorphisms of
graded `k`-algebras

```text
OS_k(𝒜) ≃ ⨁_q H^q_dR(U_𝒜/k),   e_H ↦ [df_H/f_H],
pOS_k(P) ≃ ⨁_q H^q_dR(U_P/k),   e_i - e_j ↦ [d(ℓ_i/ℓ_j)/(ℓ_i/ℓ_j)],
```

for all equations `f_H` and `ℓ_i`. No cohomology theory is a parameter. In Lean:

```lean
open OrlikSolomon OrlikSolomon.SmoothAlg OrlikSolomon.OSAlgebra
open scoped DirectSum

variable {k : Type u} [Field k] [CharZero k]
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V)
  {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

-- `cor:dr-affine`, graded by `DeRham.affineEquiv_mem_degree_iff`
example : OSAlgebra k 𝒜 ≃ₐ[k] DeRham.Cohomology k (complement 𝒜) :=
  DeRham.affineEquiv 𝒜

example : OSAlgebra k 𝒜 ≃ₐ[k] ⨁ q : ℕ, DeRham.Cohomology.degree k (complement 𝒜) q :=
  DeRham.affineDirectSumEquiv 𝒜

example {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    DeRham.affineEquiv 𝒜 (generator k 𝒜 H) =
      DeRham.dlogClass k (complementUnit 𝒜 f (hf.covers H.2)) :=
  DeRham.affineEquiv_generator_of_isEquation H hf

-- `cor:dr-projective`, graded by `DeRham.projectiveEquiv_mem_degree_iff`
example :
    projectiveAlgebra k P.cone_isCentral ≃ₐ[k] DeRham.Cohomology k (projectiveComplement P) :=
  DeRham.projectiveEquiv P

example {ℓ ℓ' : Module.Dual k W} (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    DeRham.projectiveEquiv P (projectiveDifference k P.cone_isCentral
        (P.coneHyperplaneEquiv ⟨_, hℓ⟩) (P.coneHyperplaneEquiv ⟨_, hℓ'⟩)) =
      DeRham.dlogClass k (projectiveRatioUnit hℓ hℓ') :=
  DeRham.projectiveEquiv_difference hℓ hℓ'
```

Here `DeRham.Cohomology k X` is the algebraic de Rham cohomology `H^•_dR(X/k)`, the cohomology of
the complex of Kähler differential forms of the coordinate ring of `X`, and `DeRham.dlogClass k u`
is the class `[du/u]` of a unit `u`. These declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The build of the book checks this every time it runs, and its
first page shows the statements, elaborated, with the output of `#print axioms`.

- Exposition, tied to the code: <https://adamtopaz.github.io/OrlikSolomon/>
- Mathematical plan: [`blueprint/`](blueprint/arrangement_cohomology_lean_blueprint.tex)
- De Rham instance of the axioms:
  [`blueprint/`](blueprint/de_rham_instance_blueprint.tex)
- Milestone M6, the theorems on smooth schemes, with affine duality, divisor pairs,
  affine and projective complements, geometric axioms, affine transports, the supports-and-purity
  bridge, logarithmic classes, sheaves of forms with affine evaluation, the affine and projective
  structure theorems on schemes, and the de Rham instance on smooth affine schemes with the
  unconditional de Rham theorems for the actual open subschemes, together with the logarithmic
  sheaf residue sequence, its local comparison, worked geometric regressions and acceptance
  consumers, formalized to the extent indicated in their book boxes:
  [`blueprint/`](blueprint/geometric_refactor_blueprint.tex)
- Auditable public projective theorem: [`MainTheorem.lean`](OrlikSolomon/MainTheorem.lean)
- Milestone M8, cohomological hyperplane reconstruction in progress:
  [`blueprint/`](blueprint/cohomological_hyperplane_gt_blueprint.tex)
- Design decisions: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
- Contribution rules: [`AGENTS.md`](AGENTS.md) and [`docs/TEAM.md`](docs/TEAM.md)

## Building

The project tracks Mathlib `master`; `lake-manifest.json` pins the exact commit.

```bash
lake exe cache get
lake build
```

This builds only the library, which does not depend on Verso. To build the book and write
the site to `_out/book/html-multi`:

```bash
lake build OrlikSolomonBook book
lake exe book --output _out/book
node scripts/check-book-output.mjs _out/book/html-multi
```

On NixOS, run the commands for the book inside `nix develop`, which provides the `cc` that
Verso's native dependency needs.

`scripts/check.sh` runs the build with warnings as errors, an audit of the root imports and
of the axioms that the library depends on, and the environment linters that `#lint` runs.
CI runs it and then `scripts/replay.sh`, which replays the library's proofs through the
kernel.

## License

Apache 2.0. See [`LICENSE`](LICENSE).
