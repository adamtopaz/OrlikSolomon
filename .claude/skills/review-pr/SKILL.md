---
name: review-pr
description: How to review an OrlikSolomon pull request and post the verdict. Use when asked to review a PR.
---

# Reviewing a PR

Read the whole diff with `gh pr diff <n>`, then check it out in your own worktree
(`scripts/setup-worktree.sh`, `gh pr checkout <n>`) and build it. Do not rely on the
author's claims.

## What to check, in priority order

**1. Is the mathematics right?** This matters most. A wrong definition can compile
forever.
- Compare each statement with its blueprint label. Hypotheses must be no stronger and
  conclusions no weaker. Any difference must be justified.
- Do the definitions mean what they should? Work through the blueprint's regression
  examples by hand where relevant, including `ℤ/2`, the zero ring, dimension zero, and two
  parallel lines (where `e₁e₂ = 0` but `e₂ - e₁ ≠ 0`).
- Can any definition be accidentally trivial, or any hypothesis unsatisfiable?

**2. Is the trust boundary intact?**
- No `sorry`, `axiom`, `native_decide` or `unsafe`. Run `#print axioms` on the main results.
- For structure fields, check that none asserts a conclusion (`AGENTS.md` rule 5) and that
  each holds in singular cohomology.

**3. Is it a good library?**
- Could this use something in Mathlib? Search for it; duplication is a blocking issue.
- Is it stated in natural generality, with no unused hypotheses?
- Will the API serve the modules that depend on it? Look ahead at the blueprint for how
  this will be used.
- Are the names and docstrings up to Mathlib's standard?
- Are the proofs robust rather than relying on fragile `simp` or definitional unfolding?

**4. Does it follow the process?** Does CI pass, does the PR close its issue, and does it
match `docs/ARCHITECTURE.md`, or update it when the design changed?

## Posting the verdict

Post with `gh pr review <n> --comment --body-file <file>`. Do not use `--approve`, which
GitHub rejects because all agents share one account. The first line must be exactly one of:

```
Verdict: APPROVE
Verdict: CHANGES REQUESTED
```

Then list findings, most severe first, each with `file:line`, what is wrong, and a concrete
consequence. Mark each as `blocking` or `nit`. Approve only if there are no blocking
findings. If you found nothing, say what you checked. Do not invent problems to look
thorough, and do not soften real ones.
