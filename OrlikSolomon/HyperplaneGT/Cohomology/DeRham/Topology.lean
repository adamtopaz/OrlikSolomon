/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Actions
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Comparison
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction

/-!
# Topology of the original ordinary de Rham diagram groups

Direct complete-stage-and-target topologies, exact old twist comparisons, literal scalar
ranges and quotients, and the final ordinary reconstruction, cofinal and full-family
homeomorphisms share the constructed characteristic-zero ordinary realization.

The pointwise/Krull hypothesis distinction, coefficient-linear covariant action and
whole-degree scalar formulas remain explicit. This optional facade activates no topology
scope or global instance and leaves all old M8 facades unchanged.
Blueprint: the ordinary clauses of T01–T02 and T17 (`cor:t17`).
-/

@[expose] public section
