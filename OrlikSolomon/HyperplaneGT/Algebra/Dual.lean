/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Alternating
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Primitive

/-!
# Algebraic dual coordinates, primitive functionals and relation centralizers

This facade supplies full product coordinates on the dual of any free module, the
contragredient linear action, literal surjectivity as primitivity and its local-ring coordinate
criterion, and determinant centralizers for an arbitrary explicit exterior-square relation
submodule. No diagram or cohomology theory is required.

Blueprint: `lem:u03`, `lem:u05`, and the generic portion of `def:u04`, `lem:u04`.
-/

@[expose] public section
