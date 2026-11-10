/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient

/-!
# Topological reconstruction for actual supplied cohomology theories

The existing actual local/domain quadratic and graded classifiers and scalar quotients
retain their exact algebraic maps and acquire continuity in both directions. Pointwise
classifiers and degree-one restrictions need no field-extension hypothesis; Krull wrappers
state the exact fixing condition or algebraicity. No ordinary de Rham instance is imported,
and importing this optional facade activates no topology scope.

Blueprint: the classification and degree-one restriction clauses of T15 (`thm:t15`).
-/

@[expose] public section
