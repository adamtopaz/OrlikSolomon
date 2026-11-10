/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Compact.Finite

/-!
# Closed diagram groups and finite-coefficient profiniteness

The original quadratic and full graded diagram subgroups are closed for every commutative
coefficient ring. Finite coefficients make both groups compact in their exact finite-stage
topologies; the scoped Hausdorff and total-separation instances therefore give profiniteness.
The common target remains part of the original product in every dimension.

Blueprint: T03 (`prop:t03`).
-/

@[expose] public section
