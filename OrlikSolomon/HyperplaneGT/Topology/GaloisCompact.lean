/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact.FiniteOrbits
public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact.Stages

/-!
# Compactness of the pointwise Galois group

Finite actual scalar orbits make the existing pointwise automorphism group compact.
Together with T05 this gives a profinite group. Supplied stable cofinal systems in positive
dimension and arbitrary algebraic extensions separately imply the finite-orbit hypothesis.
The general finite-orbit theorem is arrangement-free, and no global instance is activated.

Blueprint: T07 (`prop:t07`).
-/

@[expose] public section
