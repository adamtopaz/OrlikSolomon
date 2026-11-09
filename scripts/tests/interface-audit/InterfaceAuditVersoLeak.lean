/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Verso.Doc

/-!
Negative fixture: importing a dependency does not make its data part of the Mathlib boundary.
-/

@[expose] public section

/-- A data value from a dependency outside Mathlib's import closure. -/
def leakedGenre : Verso.Doc.Genre := Verso.Doc.Genre.none
