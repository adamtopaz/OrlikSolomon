---
name: pr-checklist
description: Final checks and steps for opening a pull request on OrlikSolomon. Use when a change is ready for review.
---

# Opening a PR

1. Update your branch: `git fetch origin && git merge origin/main`. Never force-push.
2. Add new modules to `OrlikSolomon.lean`, keeping the list sorted.
3. Run `scripts/check.sh`: the build with warnings as errors, the audit, and the
   environment linters of `#lint`. Fix what the linters report. Use `@[nolint]` only for a
   false positive, with a comment saying why. CI also runs `scripts/replay.sh`, the kernel
   replay. It takes seconds, so run it too if you added or moved modules.
4. Confirm the trust boundary on your main declarations by running `#print axioms` on them
   in a scratch file outside the repository, or in the checks above. Only `propext`,
   `Classical.choice` and `Quot.sound` are acceptable.
5. Read your own diff as a reviewer would. Remove debris, scratch lemmas and commented-out
   code. Check that everything public has a docstring and that imports are minimal.
6. Commit with a descriptive message ending in the attribution lines described in
   `AGENTS.md`.
7. Push the branch and open the PR with `gh pr create`. Its description must contain:
   - `Closes #<issue>`;
   - what was added, with blueprint labels and Lean names;
   - any departure from the blueprint or from `docs/ARCHITECTURE.md`, and why;
   - the checks you actually ran and their results;
   - any attribution lines `AGENTS.md` requires, at the very end.
8. Check that CI started with `gh pr checks <n>`. Do not merge.
