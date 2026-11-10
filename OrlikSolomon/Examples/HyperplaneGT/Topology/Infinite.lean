/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.Infinite.Acceptance
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Infinite.Frobenius

/-!
# An actual infinite compact nondiscrete Galois group

This example facade reexports the distinct Frobenius powers on the canonical algebraic
closure of every prime field, named pointwise and existing Krull compactness and
nondiscreteness, and proper clopen permutation kernels in the actual full stable system.
No example is a premise of the core topology theorems, and no topology or compactness
instance is installed.

Blueprint: the required infinite-Galois regression for T02, T05–T07.
-/

@[expose] public section
