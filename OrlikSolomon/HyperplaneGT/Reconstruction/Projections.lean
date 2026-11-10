/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Geometry
public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Invariance
public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Recognition

/-!
# Intrinsic coordinate spans and equivariant vertical restrictions

The commuting-functional criterion recognizes every supported coordinate span in the
literal universal free module. Actual marking squares and this criterion make those spans
invariant under the existing diagram group. Restricting the universal equivalence gives
an action on each span and its full dual, with the actual restriction square.

The three leaves separate coordinate/trace geometry, coefficient detection and recognition,
and diagram invariance. No projection arrows or dual exactness assumptions are introduced.

Blueprint: P01–P02 (`lem:p01`, `prop:p02`).
-/

@[expose] public section
