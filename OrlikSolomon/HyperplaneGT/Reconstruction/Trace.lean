/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Annihilators
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Projection

/-!
# Hyperplane traces, inertia and decomposition

The actual surjective trace map on the universal free module has the exact parallel/triple
kernel. Its full dual gives coordinate-defined inertia and decomposition, the explicit
decomposition product and all four evaluation-annihilator identities. The universal-relation
centralizer of a unit multiple of delta is decomposition. Restriction to the actual vertical
free span is surjective on decomposition for a graph, with kernel inertia.

The intrinsic geometry reuses the existing affine chart rather than redefining arrangements
on torsors. No rational-point, nontrivial coefficient, locality, domain, reflexivity or lower
dimension hypothesis is added. Blueprint: L01–L03 (`lem:l01`, `def:l02`, `lem:l02`, `lem:l03`).
-/

@[expose] public section
