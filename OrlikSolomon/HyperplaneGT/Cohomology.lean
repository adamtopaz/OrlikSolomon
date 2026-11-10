/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter
public import OrlikSolomon.HyperplaneGT.Cohomology.Main

/-!
# Conditional cohomology reconstruction facade

This facade reexports the actual C1–C5 ordinary-theory diagram comparison and its
local/domain reconstruction, cofinal independence and canonical realization independence.
No new theory instance is assumed as a field or constructed here. Import the de Rham
specialization explicitly when that named realization is needed.

Blueprint: A04 and E01–E02 (`thm:a04`, `thm:e01`, `cor:e02`).
-/

@[expose] public section
