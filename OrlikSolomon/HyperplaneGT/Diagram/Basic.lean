/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Restriction

/-!
# The explicit marked quadratic and full graded diagrams

The canonical finite-stage modules and relation spans, one common two-puncture target, and
tagged marking arrows define the quadratic automorphism group `DiagramAut`. The full
`GradedDiagramAut` uses the existing Orlik–Solomon algebras and every homogeneous degree.
Both groups preserve exactly the inclusion and marking squares. No reconstruction theorem
or quadratic presentation of the full algebras is assumed. Canonical degree-one restriction
is a faithful group homomorphism from the full graded to the quadratic automorphism group.

Blueprint: A03 (`def:a03`).
-/

@[expose] public section
