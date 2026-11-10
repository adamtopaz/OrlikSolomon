/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quadratic

/-!
# Local-ring classification of the marked quadratic diagram

The actual quadratic automorphism group is canonically the direct product of coefficient
units and base-field automorphisms. The equivalence retains the common marking target,
has an explicit primal scalar/Galois inverse, and gives the actual finite-stage, universal,
marking and contragredient formulas. Unit scalar families are injective and central over
arbitrary commutative rings before the local-ring reconstruction hypotheses are imposed.

Blueprint: S03 (`thm:s03`). Graded extension and quotient classification remain separate.
-/

@[expose] public section
