/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Automorphisms

/-!
# The universal module of the marked quadratic diagram

The literal free module on all affine hyperplanes contains the finite-stage modules by
extension by zero. The chosen cofinal stages satisfy the explicit linear universal property,
and the global quadratic relation span has common finite-stage witnesses. The actual
quadratic diagram automorphism group acts on this module, preserving the whole relation span
and each stage image. Its universal action and common target action jointly determine the
original family.

Blueprint: U01–U02 (`def:u01`, `lem:u01`, `lem:u02`).
-/

@[expose] public section
