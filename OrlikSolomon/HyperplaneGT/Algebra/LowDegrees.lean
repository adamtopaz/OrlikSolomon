/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.DegreeOne
public import OrlikSolomon.HyperplaneGT.Algebra.QuadraticKernel

/-!
# Low-degree Orlik–Solomon coordinates

This facade combines the canonical degree-one basis with the exact degree-two kernel of the
actual exterior-algebra quotient. The kernel is the span of parallel-pair wedges and guarded
dependent-triple difference wedges, over arbitrary commutative coefficient rings.

The degree-one equivalence and degree-two quotient commute with inclusions of arrangements.
Full algebra generation is included; no quadratic-presentation assertion is made.

Blueprint: A01 (`lem:a01`) and A02 (`thm:a02`).
-/

@[expose] public section
