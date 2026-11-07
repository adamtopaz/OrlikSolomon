/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.DeRhamCalculations
public import OrlikSolomon.Examples.DeRhamCharacteristic
public import OrlikSolomon.Examples.DeRhamCohomology
public import OrlikSolomon.Examples.DeRhamComplex
public import OrlikSolomon.Examples.DeRhamCrossing
public import OrlikSolomon.Examples.DeRhamHomotopy
public import OrlikSolomon.Examples.DeRhamInstance
public import OrlikSolomon.Examples.DeRhamLocalization
public import OrlikSolomon.Examples.DeRhamLog
public import OrlikSolomon.Examples.DeRhamMaps
public import OrlikSolomon.Examples.DeRhamMorphisms
public import OrlikSolomon.Examples.DeRhamPole
public import OrlikSolomon.Examples.DeRhamSmoothPair

/-!
# De Rham regressions

This umbrella collects the worked examples and excluded cases of the de Rham instance:
unit and zero algebras, disconnected divisors, morphisms that need not be flat, a singular
crossing divisor, positive-characteristic obstructions, and the concrete cohomology calculations.
The individual modules retain the more general statements valid over arbitrary coefficient rings.

Blueprint: the worked regressions `prop:dr-gm-example`, `prop:dr-unit-example`,
`prop:dr-product-example`, `prop:dr-zero-example`, `prop:dr-crossing-example`,
`prop:dr-morphism-examples`, `prop:dr-torus-example`, and `prop:dr-characteristic-p`.
-/

@[expose] public section
