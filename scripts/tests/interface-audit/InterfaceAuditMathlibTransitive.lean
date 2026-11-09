/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
Positive fixture: definitions from transitive Mathlib imports remain available. The linear-map
identity is defined in a module imported transitively by the sole explicit Mathlib import above.
-/

@[expose] public section

/-- A linear identity using data from a transitive Mathlib import. -/
def identityLinearMap (k : Type) [Field k] : k →ₗ[k] k := LinearMap.id
