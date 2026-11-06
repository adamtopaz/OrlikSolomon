# Rules for agents working on OrlikSolomon

## Goal

Formalize the Orlik–Solomon structure theorem for the cohomology of complements of
hyperplane arrangements, in affine space and in `P^n`, from axioms on the cohomology
theory. The deliverables are a reusable library that others can rely on and a Verso
exposition, tied to the code and published on GitHub Pages.

Read these before working:

- `blueprint/arrangement_cohomology_lean_blueprint.tex`: authoritative for mathematics.
- `docs/ARCHITECTURE.md`: authoritative for Lean design, names and module layout. The
  blueprint says its own Lean names and signatures are only proposals.

## Hard rules

1. **Only this repository.** The only repository anything may change is
   <https://github.com/adamtopaz/OrlikSolomon>. Never create, modify or comment on
   anything elsewhere on GitHub: no issues, PRs, forks or gists on Mathlib, Verso or any
   other project. Never edit files under `.lake/packages`. If a dependency has a bug or a
   gap, work around it here and record it in an issue on this repository.
2. **No new blueprints.** Never write a mathematical blueprint. Fill in routine detail
   directly, which is always preferred. If substantive mathematics is missing, follow the
   `blueprint-gap` skill: the supervisor passes a precise scope to Adam, who supplies the
   blueprint.
3. **This project stands alone.** Do not read or borrow from other directories under
   `~/projects/autoformalization/`. Search only this repository and its dependencies.
4. **No unproved mathematics on `main`.** No `sorry`, `admit`, `axiom`, `native_decide`
   or `unsafe`. Do not weaken a statement to make it provable. A branch may contain
   `sorry` while in progress, but a PR may not.
5. **Conclusions are never assumptions.** The cohomology structure holds only the axioms
   the blueprint lists (C1–C5). No field may assert logarithmic generation, arrangement
   vanishing, surjectivity of residues, vanishing of Gysin maps, a short exact deletion
   sequence, freeness, or the structure theorem.
6. **Never read secrets**: tokens, keys, `gh` credentials, or environment variables that
   hold them.
7. **Do not change repository settings** unless the supervisor explicitly asked you to.

## How work is organized

- A supervisor plans the work and is the only one who merges. Subagents do the work and
  report back to the supervisor, who is the only one talking to Adam.
- All work is tracked by a GitHub issue. Every change reaches `main` through a PR that
  closes its issue, with one concern per PR.
- A PR needs CI passing and an approving review from an agent that did not write it. All
  agents share Adam's GitHub account, so `gh pr review --approve` is rejected: reviewers
  post a comment review whose first line is `Verdict: APPROVE` or
  `Verdict: CHANGES REQUESTED`.
- Branch names are `<issue-number>-<short-slug>`.
- End every commit message with:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
- End every PR description with:
  `🤖 Generated with [Claude Code](https://claude.com/claude-code)`
- Project skills are in `.claude/skills/`. If you cannot invoke one by name, read its
  `SKILL.md` and follow it.

## Environment

- **Work in a git worktree, never in the main checkout.** First run
  `scripts/setup-worktree.sh`, which shares the built dependencies through a symlink.
- Because that directory is shared, **never run `lake update` or `lake clean`, and never
  delete anything under `.lake/packages`.** Only the `bump-mathlib` skill changes
  dependency versions.
- While developing, build single modules: `lake build OrlikSolomon.Grading.Basic`. Run the
  full build only before opening a PR. Several agents share this machine, so do not start
  a full build while one of yours is still running.
- This is NixOS. Anything that compiles Verso's native dependency needs `cc`, so run it as
  `nix develop --command lake ...`. Ordinary library builds do not need this.
- Search Mathlib locally with `grep` under `.lake/packages/mathlib/Mathlib`.

## Lean standards

The bar is Mathlib quality: someone should be able to depend on this library.

- **Style:** follow Mathlib's style and naming conventions. The Mathlib linters are on and
  CI treats warnings as errors.
- **File header:**
  ```lean
  /-
  Copyright (c) 2026 Adam Topaz. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Adam Topaz, Claude
  -/
  ```
  Next come the imports, then a module docstring with a title, a summary, the main
  definitions and results, and the blueprint labels covered.
- **Imports:** import specific Mathlib modules, never all of `Mathlib`. Add each new module
  to `OrlikSolomon.lean`, keeping the list sorted.
- **Docstrings:** every public definition, structure and main theorem has one. Name the
  blueprint label when there is one, as in ``Blueprint: `lem:gm`.`` Docstrings explain the
  mathematics rather than the tactic steps.
- **Generality:** state results in their natural generality, with no unused hypotheses.
  Purely algebraic lemmas must not mention arrangements or cohomology.
- **Reuse:** look in Mathlib before defining anything. Do not duplicate what exists.
- **API:** hide implementation choices behind lemmas, such as how a quotient is built. Give
  new definitions `simp` and `ext` lemmas, and do not make users rely on definitional
  unfolding.
- **Proofs:** prefer `simp only` or a terminal `simp`. Avoid `erw` and `open Classical`
  (use `classical` inside proofs). Factor out long proofs into named lemmas, and split
  files before they reach about 800 lines. Any `set_option maxHeartbeats` needs a comment
  saying why.
- **Edge cases:** the blueprint's regression list covers `ℤ/2` coefficients, the zero
  coefficient ring, dimension zero, and complements with no `k`-points. Never assume 2 is
  invertible, that coefficients are nontrivial, or that a complement has rational points.
