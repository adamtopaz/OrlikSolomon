/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Actions
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification.Compatibility
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Cofinal
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Realization

/-!
# Actual cohomological reconstruction and independence

An existing C1–C5 ordinary theory has the proved local/domain classification of its actual
marked degree-one/cup-kernel and full ordinary diagonal diagram groups. The same primal unit
acts at every stage and the common target; its degree-q action is the q-th power, and the
Galois factor is coefficient-linear presentation transport. Literal central-scalar quotients,
actual degree-one restriction, classified cofinal restriction and canonical comparison of
two independently sized eligible realizations all commute.

The supplied-cofinal-system results use only their displayed field/algebra hypotheses.
They assert no automatic existence of such a system for an arbitrary extension and introduce
no theory axioms or semilinear geometric pullback claim. The de Rham specialization remains
an explicit separate import.

Blueprint: E01–E02 (`thm:e01`, `cor:e02`).
-/

@[expose] public section
