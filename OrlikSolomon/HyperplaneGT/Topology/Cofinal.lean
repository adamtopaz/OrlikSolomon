/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Cofinal.Restriction

/-!
# Topological independence of supplied cofinal stages

Literal stage restriction embeds the original quadratic and full graded topologies,
retaining the same common target. The exact M8 local and domain cofinal equivalences and
their induced actual scalar quotients become topological equivalences. Unrelated supplied
families compare through the union of their selected families. No field-extension condition,
arrangement-union closure or topology transport is used. Importing this facade activates
no scope or instance.

Blueprint: T12 (`thm:t12`).
-/

@[expose] public section
