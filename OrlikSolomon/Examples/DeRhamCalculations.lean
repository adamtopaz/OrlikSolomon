/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.DeRhamCalculations.Basic
public import OrlikSolomon.Examples.DeRhamCalculations.Torus

/-!
# Worked de Rham calculations

This umbrella imports the unit and zero-algebra cases and the disconnected-divisor calculation
from `DeRhamCalculations/Basic`, together with the punctured-line and two-torus calculations
from `DeRhamCalculations/Torus`. All maps are the actual de Rham maps of the library.

Blueprint: `prop:dr-gm-example`, `prop:dr-unit-example`, `prop:dr-product-example`,
`prop:dr-zero-example`, and `prop:dr-torus-example`.
-/

@[expose] public section
