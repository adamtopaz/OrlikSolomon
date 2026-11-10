/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Krull.Comparison
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Hyperplanes
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Pointwise

/-!
# Pointwise convergence and the Krull topology

This optional facade exports the arrangement-free pointwise topology, finite normalized
hyperplane tests, selected-stage kernel comparison, and the exact finite-intermediate-field
criterion for equality with Mathlib's global Krull topology. Algebraicity is a sufficient
condition; neither normality nor separability is required.

Importing this facade activates no scope and changes no carrier or field topology.
Blueprint: T05–T06 (`lem:t05`, `thm:t06`).
-/

@[expose] public section
