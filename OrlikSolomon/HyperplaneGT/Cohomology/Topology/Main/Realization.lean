/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Realization.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Realization.Compatibility

/-!
# Topological independence of eligible cohomology realizations

The four existing realization comparisons are homeomorphisms for the direct actual group
and literal scalar-quotient topologies over every commutative coefficient ring. Their whole
stage and common-target formulas, inverses and cocycles retain the original maps.
Classification and cofinal compatibility use exactly the existing local/domain hypotheses;
only comparison with a Krull classifier introduces its fixing condition or algebraicity.
This explicit facade activates no topology scope.

Blueprint: T16 (`thm:t16`).
-/

@[expose] public section
