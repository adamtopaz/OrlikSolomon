---
name: pr-checklist
description: Final checks and steps for opening a pull request on OrlikSolomon. Use when a change is ready for review.
---

# Opening a PR

1. Rebase on `origin/main`: `git fetch origin && git rebase origin/main`.
2. Add new modules to `OrlikSolomon.lean`, keeping the list sorted.
3. Run `scripts/check.sh` if it exists. Otherwise run
   `lake build --wfail OrlikSolomon` and confirm that it passes with no warnings.
4. Confirm the trust boundary on your main declarations by running `#print axioms` on them
   in a scratch file outside the repository, or in the checks above. Only `propext`,
   `Classical.choice` and `Quot.sound` are acceptable.
5. Read your own diff as a reviewer would. Remove debris, scratch lemmas and commented-out
   code. Check that everything public has a docstring and that imports are minimal.
6. Commit with a descriptive message ending in the `Co-Authored-By` line from `AGENTS.md`.
7. Push the branch and open the PR with `gh pr create`. Its description must contain:
   - `Closes #<issue>`;
   - what was added, with blueprint labels and Lean names;
   - any departure from the blueprint or from `docs/ARCHITECTURE.md`, and why;
   - the checks you actually ran and their results;
   - the attribution line from `AGENTS.md` at the very end.
8. Check that CI started with `gh pr checks <n>`. Do not merge.
