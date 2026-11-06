---
name: bump-mathlib
description: Update OrlikSolomon to the most recent Mathlib, keeping Verso on a compatible Lean toolchain. Use when asked to bump dependencies.
---

# Bumping Mathlib

This project tracks the most recent Mathlib. A bump is a PR like any other.

Do not run `lake update` in a worktree, because worktrees share `.lake/packages` with the
main checkout. Use a fresh clone in your scratchpad directory:

1. Read the `lean-toolchain` of Mathlib `master`, with `gh api` against the
   `leanprover-community/mathlib4` contents endpoint (read-only).
2. Find a Verso tag or commit on the same toolchain. If there is none, stop and report:
   Verso's toolchain constrains the bump, and pinning Mathlib to the newest compatible
   commit is the fallback.
3. In the clone, update `lean-toolchain` and the Verso `rev` in `lakefile.toml` if needed,
   then run `lake update` and `lake exe cache get`.
4. Run `lake build --wfail` and fix any breakage in this repository. Do not touch anything
   in `.lake/packages`.
5. Open the PR, stating the old and new Mathlib commits and what had to change.

After merging, the supervisor updates the main checkout with `lake exe cache get`, so
that all worktrees see the new dependencies. Coordinate this with in-progress work, since
open branches will then need a rebase.
