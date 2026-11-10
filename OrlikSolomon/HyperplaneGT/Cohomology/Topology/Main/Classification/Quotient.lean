/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient.Domain
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Quotient.Local

/-!
# Actual scalar quotient classifiers and degree-one restrictions

The exact existing local and domain classifiers use the literal actual scalar quotients,
with pointwise and explicitly conditioned Krull conclusions. Actual quotient degree-one
restriction needs no field-extension hypothesis. Importing this facade activates no scope.

Blueprint: the actual scalar-quotient clauses of T15 (`thm:t15`).
-/

@[expose] public section
