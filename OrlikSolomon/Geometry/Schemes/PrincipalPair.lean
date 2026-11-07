/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Duality

/-!
# Principal smooth divisor pairs on schemes

This is the module to import for the geometric divisor pairs of stage G0 of the geometric refactor
blueprint. It imports the four files below, whose headers list their results.

* `Geometry/Schemes/PrincipalPair/Certificates`: what the certificates of a pair mean on any
  scheme, and their translation to algebraic certificates on affine schemes.
* `Geometry/Schemes/PrincipalPair/Basic`: `def:geo-divisor-pair`, `def:geo-pair-hom` and
  `thm:geo-cartesian`: `Geometric.DivisorPair`, its morphisms in the geometric direction,
  `DivisorPair.homOfAmbient`, and the Cartesian characterization
  `DivisorPair.associated_iff_ker_pullback_fst`.
* `Geometry/Schemes/PrincipalPair/Standard`: the geometric standard pair
  `DivisorPair.standardPair D X` of every object `X` of a domain, affine or not.
* `Geometry/Schemes/PrincipalPair/Duality`: `thm:geo-pair-duality`, the anti-equivalence
  `Geometric.affinePairEquivalence` with the algebraic pairs `OrlikSolomon.DivisorPair k`.
-/
