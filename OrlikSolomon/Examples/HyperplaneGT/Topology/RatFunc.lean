/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.RatFunc.Counterexample

/-!
# The rational-function Krull counterexample

The actual field automorphisms, finite stable cofinal system and M8 quadratic diagram
provide a counterexample to replacing pointwise convergence by Mathlib's Krull topology
without the finite-intermediate-field fixing condition. The actual forward Galois and
classification maps are noncontinuous. All topology choices remain explicit.

Blueprint: T08 (`prop:t08`).
-/

@[expose] public section
