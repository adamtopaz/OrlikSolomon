/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Classification.Graded
public import OrlikSolomon.HyperplaneGT.Topology.Classification.Quadratic

/-!
# Topological reconstruction for the pure diagrams

This optional facade exports the exact local and domain quadratic and full graded
classifications with pointwise continuity, together with explicit-condition and algebraic
Krull wrappers. Graded restriction uses the original direct topologies and needs no
field-extension hypothesis. Importing the facade activates no topology scope or instance.

Blueprint: T09 (`thm:t09`) and T10 (`cor:t10`).
-/

@[expose] public section
