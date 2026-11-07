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
- Milestone M6, the theorems on smooth schemes, planned, with affine duality, divisor pairs and
  projective complements formalized to the extent indicated in their book boxes:
  [`blueprint/`](blueprint/geometric_refactor_blueprint.tex)
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
