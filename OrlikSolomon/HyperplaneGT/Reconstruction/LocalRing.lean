/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quotient

/-!
# Local-ring classification of the marked quadratic and full graded diagrams

The actual quadratic automorphism group is canonically the direct product of coefficient
units and base-field automorphisms. The equivalence retains the common marking target,
has an explicit primal scalar/Galois inverse, and gives the actual finite-stage, universal,
marking and contragredient formulas. Unit scalar families are injective and central over
arbitrary commutative rings before the local-ring reconstruction hypotheses are imposed.

The existing degree-one restriction becomes a multiplicative equivalence after quadratic
classification. Its inverse is the full scalar action times the direct Galois action; each
ordinary degree-q component is multiplied by the q-th scalar power. Both literal groups
modulo their central scalar ranges are canonically the Galois group, with explicit direct
Galois sections and inverse laws. The full OS relators and single common target are retained;
no quadratic presentation of the OS algebra is assumed.

Blueprint: S03–S04 (`thm:s03`, `thm:s04`). Domain descent and cohomology transport are separate.
-/

@[expose] public section
