/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois.Scalar

/-!
# Galois extraction and its scalar kernel

This facade exposes the field automorphism extracted from the actual marked incidence
permutation, its base-field descent and homomorphism, and the unique common primal scalar
in its kernel. The scalar acts on every selected stage and the original common target;
it is inverse to the dual inertia unit.

Blueprint: C04 (`prop:c04`) and S01 (`lem:s01`). No splitting or classification is asserted.
-/

@[expose] public section
