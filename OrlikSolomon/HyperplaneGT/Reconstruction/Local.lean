/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Local.Detection

/-!
# Local transfer and unit-supported hyperplane detection

The transfer calculation works over every commutative coefficient ring by cancelling only
a specified unit. In dimension at least two over a nonzero local ring, literal primitivity,
vertical vanishing, a zero graph coordinate and surjectivity of the actual centralizer
restriction detect a unique unit multiple of a graph delta. Its actual universal-Q centralizer
is decomposition. The public target is the dual of the actual supported vertical module.

The generic arithmetic, geometric witnesses, transfer and local detection are separated into
the approved leaves, without additional diagram data or cohomology hypotheses.
Blueprint: L04–L05 (`lem:l04`, `thm:l05`).
-/

@[expose] public section
