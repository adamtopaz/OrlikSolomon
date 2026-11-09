/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Field

/-!
# Coordinate reconstruction of projective collineations

This facade exposes the pure projective geometry of M8 nodes `C01`–`C03`, over an arbitrary
field and independently of arrangements, coefficient rings and cohomology.

* `collineation_preserves_span` preserves arbitrary projective spans.
* `collineation_coordinate_functions` gives the coordinate bijections of the affine chart.
* `coordinateFieldEquiv` extracts the field automorphism from the prescribed fixed frame.
* `coordinateFieldEquiv_mk` and `existsUnique_coordinateFieldEquiv` give its homogeneous
  action, including infinity, and uniqueness.

Blueprint: `lem:c01`, `lem:c02`, `thm:c03`.
-/

@[expose] public section
