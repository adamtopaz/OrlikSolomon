/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull.Domain
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification.Krull.Local

/-!
# Krull classifiers for actual supplied cohomology theories

The local and domain leaves upgrade the exact old classifiers under the explicit fixing
condition or algebraicity. Their literal parameter product uses discrete units and the
actual global Mathlib Krull topology. Importing the facade activates no topology scope.

Blueprint: the Krull reconstruction clauses of T15 (`thm:t15`).
-/

@[expose] public section
