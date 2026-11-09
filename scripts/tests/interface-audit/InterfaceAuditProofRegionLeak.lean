/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
Negative fixture: private data escapes the exempt proof namespace in the same module.

The library is imported publicly so the module-system boundary does not perform this test.
-/

@[expose] public section

namespace OrlikSolomon.MainTheorem.Proof
private def hiddenData : Nat := 1
end OrlikSolomon.MainTheorem.Proof
private def leakedData : Nat := OrlikSolomon.MainTheorem.Proof.hiddenData
