/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main
public import OrlikSolomon.HyperplaneGT.Topology

/-!
# Topological reconstruction for a supplied cohomology theory

This optional facade adds the direct actual-theory diagram topologies, canonical adapters,
reconstruction, scalar quotients, restriction maps and realization comparisons to the pure
topological development. Every assertion retains its supplied eligible theory and the
precise hypotheses of the corresponding public map.

The constructed ordinary de Rham specialization and Examples are separate imports. This
facade activates no topology scope and changes no existing algebraic facade or instance.

Blueprint: the actual-theory portions of T01–T02 (`def:t01`, `lem:t02`) and T14–T16
(`thm:t14`, `thm:t15`, `thm:t16`).
-/

@[expose] public section
