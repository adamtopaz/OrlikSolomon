/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Comparison
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Quotient

/-!
# Direct actual-theory topology and canonical adapter homeomorphisms

The actual complete-component topology has the original stage-and-target neighborhood
basis. The old quadratic, graded and scalar-quotient comparisons are topological group
isomorphisms for the direct group topologies and Mathlib quotient topologies.

This optional facade activates no scope and imports no concrete realization.
Blueprint: the actual-theory clauses of T01–T02 and T14 (`def:t01`, `lem:t02`, `thm:t14`).
-/

@[expose] public section
