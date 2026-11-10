/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Comparison

/-!
# Actual cohomology and marked presentation diagrams

This facade exposes the canonical comparison of actual degree-one cup-kernel and full
marked diagonal-cohomology automorphism groups with the corresponding OS presentation
diagrams. The actual scheme maps, entire cup kernels, all graded components, common target,
scalar families and faithful degree-one restriction are preserved. It uses the existing
full geometric ordinary theory and its structure theorem, without new theory axioms.

Blueprint: A04 (`thm:a04`).
-/

@[expose] public section
