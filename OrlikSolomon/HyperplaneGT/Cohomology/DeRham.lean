/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Reconstruction

/-!
# Reconstruction from actual ordinary algebraic de Rham cohomology

This explicit realization facade exports ordinary H¹/cup-kernel and full graded diagram
automorphisms, their diagonal comparisons, and unconditional reconstruction over a
characteristic-zero field. The action is coefficient-linear with covariant Galois labels,
including the single actual marking target. The conditional cohomology facade does not
import this constructed realization.

Blueprint: E03 (`cor:e03`).
-/

@[expose] public section
