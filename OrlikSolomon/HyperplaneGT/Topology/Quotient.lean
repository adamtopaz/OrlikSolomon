/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Quotient.Domain
public import OrlikSolomon.HyperplaneGT.Topology.Quotient.Local

/-!
# Profinite scalar quotients in topological reconstruction

The original local-ring and domain quadratic and graded scalar quotients carry their
actual Mathlib quotient topologies. Their old Galois classifications and degree-one
restriction gain both continuity proofs. The quotients are compact, Hausdorff and totally
separated under the original hypotheses; only the separate Krull upgrades require the
fixing condition or algebraicity. Importing this facade activates no topology scope.

Blueprint: T11 (`thm:t11`).
-/

@[expose] public section
