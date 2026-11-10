/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Classification
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal

/-!
# Topological reconstruction for actual supplied cohomology theories

The exact existing local/domain classifiers, degree-one and cofinal equivalences acquire
continuity in both directions for the independent actual diagram topologies. Scalar
quotients retain their literal Mathlib topology and original scalar ranges. Pointwise
results and cofinality require no field-extension condition; Krull classifiers state the
precise fixing condition or algebraicity separately. This optional facade activates no
scope and imports no ordinary de Rham instance or Examples.

Blueprint: T15 (`thm:t15`). T16 supplies the separate two-theory realization interfaces.
-/

@[expose] public section
