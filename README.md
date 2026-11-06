# OrlikSolomon

A Lean 4 and Mathlib formalization of the Orlik–Solomon structure theorem for the
cohomology of complements of hyperplane arrangements in affine and projective space.

The cohomology theory is not fixed. It is a structure whose fields are the standard
axioms: products, a dimension axiom at the point, affine-line invariance, and compatible
localization and divisor purity. From these, the library constructs a canonical
bigraded algebra isomorphism between the Orlik–Solomon algebra and the cohomology of the
complement. The base field is arbitrary, coefficients need not form a field, and Tate
twists stay explicit.

**Status:** the affine structure theorem and its corollaries are proved, for any structure
satisfying the axioms. No nonzero instance of that structure is constructed in Lean, so the
library is not yet a theorem about any named cohomology theory. The projective theorem is in
progress. The [status page](https://adamtopaz.github.io/OrlikSolomon/status/) of the book
has the details.

- Exposition, tied to the code: <https://adamtopaz.github.io/OrlikSolomon/>
- Mathematical plan: [`blueprint/`](blueprint/arrangement_cohomology_lean_blueprint.tex)
- Plan for a de Rham instance of the axioms, not yet formalized:
  [`blueprint/`](blueprint/de_rham_instance_blueprint.tex)
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
