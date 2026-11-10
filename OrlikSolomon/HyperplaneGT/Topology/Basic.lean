/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Basic.Components
public import OrlikSolomon.HyperplaneGT.Topology.Basic.Neighborhoods

/-!
# Direct finite-stage topologies

The existing pure quadratic and full graded diagram groups carry the induced topology from
complete discrete stage automorphism groups and their one complete common target. Opening
`OrlikSolomon.HyperplaneGT.FiniteStageTopology` activates the corresponding group,
Hausdorff and total-separation instances. Complete-stage-and-target kernels form an identity
neighborhood basis, without coefficient nontriviality, dimension bounds or classification.

Blueprint: the pure portions of T01 (`def:t01`) and T02 (`lem:t02`).
-/

@[expose] public section
