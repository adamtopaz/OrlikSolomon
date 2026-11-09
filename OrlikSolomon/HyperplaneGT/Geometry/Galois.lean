/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Galois.AlgebraicMaps
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits

/-!
# Galois actions, cofinal arrangements and marking arrows

The coefficient action is a genuine action on the existing affine hyperplanes. It preserves
intersections, codimensions and incidence. Algebraicity supplies finite orbits and a full
cofinal system; arbitrary chosen cofinal systems have common upper stages without being
closed under unions.

Tagged coordinate markings have individually fixed zero and one fibers. Their actual
coordinate-algebra maps all share one two-puncture target, commute with inclusions, and send
the ordered units `t`, `t - 1` to the corresponding marking units. This facade imports no
cohomology theory; the scheme and theory comparisons are separate.

Blueprint: G04–G06 (`lem:g04`, `lem:g05`, `def:g06`).
-/

@[expose] public section
