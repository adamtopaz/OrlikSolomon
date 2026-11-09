/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Alternating
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Configurations
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.DiagramAction
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Primitive

/-!
# Algebraic dual coordinates, primitive functionals and relation centralizers

This facade supplies full product coordinates on the dual of any free module, the
contragredient linear action, literal surjectivity as primitivity and its local-ring coordinate
criterion, and determinant centralizers for an arbitrary explicit exterior-square relation
submodule. These generic leaves remain independent of geometry and diagrams. The specialized
leaves give the determinant tests for the actual global hyperplane relation span and its
contragredient diagram action, including equality of the paired centralizer images.
No cohomology theory is imported.

Blueprint: `lem:u03`, `def:u04`, `lem:u04`, `lem:u05`.
-/

@[expose] public section
