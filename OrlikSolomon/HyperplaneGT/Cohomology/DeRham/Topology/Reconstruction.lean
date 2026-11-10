/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Consequences
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Full
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Krull
public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Topology.Reconstruction.Quotient

/-!
# Ordinary de Rham topological reconstruction

The exact M8 ordinary reconstruction maps, degree-one restriction, literal scalar quotients
and new cofinal wrappers are topological group isomorphisms for the directly defined
finite-stage topologies. Pointwise statements retain the original generating-marking and
dimension hypotheses; Krull statements explicitly require the fixing condition or
algebraicity. Full-family wrappers retain algebraicity for the old family constructor.

The whole ordinary algebra, full H¹/cup kernel, actual scheme arrows and single common
target are unchanged. The characteristic-zero ordinary groups are locally compact and
noncompact; both original scalar quotients have the explicit profinite property package,
without any field-extension condition on a supplied stable system.

This optional facade activates no scope and changes no old M8 facade, carrier or instance.
Blueprint: T17 (`cor:t17`).
-/

@[expose] public section
