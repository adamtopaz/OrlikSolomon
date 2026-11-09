---
name: blueprint-gap
description: What to do when the blueprint seems wrong or is missing mathematics. Use when a statement appears false or a proof needs substantive mathematics the blueprint does not supply.
---

# Handling a blueprint gap

GPT-6-Astra writes all new mathematical blueprints in `blueprint/`. No other agent,
including supervisors, formalizers, reviewers and the Verso author, writes blueprints.
Never quietly substitute your own mathematics for a missing blueprint.

## First decide whether it really is a gap

- **Not a gap: fill it in directly.** Routine detail the blueprint leaves implicit, such as
  standard algebra, Lean plumbing, or a lemma you can prove straightforwardly. This is the
  normal case and is preferred.
- **A gap.** A statement appears false, a proof step does not go through, a hypothesis is
  missing, or the proof needs a substantial development that the blueprint does not
  describe.

Before calling something false, try to confirm it with a concrete counterexample.

## Reporting a gap

Report to the supervisor who launched you in your final message. If it blocks your work,
stop that part and finish what you can. Give all of the following:

- **Where:** the blueprint label and line.
- **What is wrong or missing,** precisely, with a counterexample if you have one.
- **What the blueprint would need to cover:** the statements required and the context they
  will be used in. Describe the scope, without drafting the mathematics.
- **What is blocked,** and what can continue in the meantime.

## Scoping and committing a blueprint

Codex relays gaps from its team to the Claude supervisor. Only Claude sends blueprint
requests to Astra, giving a precise scope of what must be covered and pointers into this
repository. Other agents do not contact Astra or send it formalization work.

Astra drafts the blueprint in `blueprint/`. Its role is blueprint writing only: it does
no formalization and does not commit, push or open PRs. Claude checks with Adam before
committing any blueprint Astra writes.
