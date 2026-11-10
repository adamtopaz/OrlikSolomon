/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Markings

/-!
# Recovering the actual hyperplane permutation and its fixed frame

The contragredient diagram action determines one unique label permutation and one dual unit
at each hyperplane. Its primal action uses the same permutation and the inverse unit. The
actual trace kernels recover strict parallelism and guarded dependent triples, hence give a
projective line-preserving action after fixing the constant coefficient point. The single
common target fixes every marked zero and one fiber individually, supplying the entire
projective frame needed for subsequent field reconstruction.

## Main definitions and results

* `DiagramAut.hyperplanePerm`, `DiagramAut.hyperplaneUnit` and `DiagramAut.hyperplaneAction`
  recover the actual inertia labels and their composition laws.
* `DiagramAut.map_traceKernel` and the two incidence equivalences transport actual traces.
* `DiagramAut.projectivePerm` preserves exact projective line images in both directions.
* `DiagramAut.hyperplanePerm_marking_zero`, `DiagramAut.hyperplanePerm_marking_one` and the
  basis/difference-point lemmas give the individually fixed marked frame.

Diagram reconstruction retains nonzero local coefficients, ambient dimension at least two
and zero among the marking constants. Pure geometric helpers work over arbitrary fields;
trace coefficient tests need only a nonzero ring. No new diagram data, field automorphism or
scalar classification is assumed. Blueprint: I01–I04 (`prop:i01`, `lem:i02`–`lem:i04`).
-/

@[expose] public section
