/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Pole.Cartan
public import OrlikSolomon.DeRham.Pole.Comparison
public import OrlikSolomon.DeRham.Pole.Complex
public import OrlikSolomon.DeRham.Pole.Contraction
public import OrlikSolomon.DeRham.Pole.Degree
public import OrlikSolomon.DeRham.Pole.Euler
public import OrlikSolomon.DeRham.Pole.Filtration
public import OrlikSolomon.DeRham.Pole.Quotient
public import OrlikSolomon.DeRham.Pole.Reduction

/-!
# Global logarithmic comparison by pole order

Cartan calculus and the logarithmic Euler contraction identify the differential on a successive
pole quotient as `d̄ − m W`. If the positive pole order `m` is a unit in `k`, the explicit
operator `−m⁻¹ J` contracts that quotient. Finite induction on the pole bound then identifies
logarithmic cohomology with the de Rham cohomology of the localization.

The pole filtration and its quotient identifications need neither regularity nor smoothness.
Contraction and reduction use a derivation normal to `f` modulo `f`. A smooth principal pair
supplies one, and the resulting comparison map on cohomology is induced by inclusion, independently
of that auxiliary choice. The construction also allows zero coefficient rings and unit divisors.

## Main definitions and results

* `OrlikSolomon.DeRham.formContraction`, `OrlikSolomon.DeRham.lieDerivative`, and
  `OrlikSolomon.DeRham.cartanFormula`: Cartan calculus, including localization.
* `OrlikSolomon.DeRham.logQuotientEulerContraction` and
  `OrlikSolomon.DeRham.logQuotientThetaWedge`: the operators `J` and `W` on `L / f L`.
* `OrlikSolomon.DeRham.poleFiltration` and `OrlikSolomon.DeRham.poleComplex`: pole stages and their
  complexes, increasing and exhaustive.
* `OrlikSolomon.DeRham.poleQuotientEquiv` and
  `OrlikSolomon.DeRham.poleQuotientD_poleQuotientEquiv`: the quotient identification and its
  differential.
* `OrlikSolomon.DeRham.positivePoleQuotientContractible` and
  `OrlikSolomon.DeRham.poleQuotientD_homotopy_add`: the actual contraction identities.
* `OrlikSolomon.DeRham.exists_closed_logForm_sub_d_eq` and
  `OrlikSolomon.DeRham.exists_logPrimitive_of_exists`: the finite reductions of cocycles and
  primitives to logarithmic forms.
* `OrlikSolomon.DeRham.logToLocalizationQuasiIso` and
  `OrlikSolomon.DeRham.logToLocalizationEquiv`: the canonical total cohomology comparison.
* `OrlikSolomon.DeRham.logToLocalizationDegreeEquiv` and
  `OrlikSolomon.DeRham.logToLocalizationGradingEquiv`: the canonical comparison in every natural
  and integer degree, including the negative degrees.

Blueprint: `lem:dr-cartan`, `lem:dr-euler`, `def:dr-pole-filtration`, `lem:dr-pole-quotient`,
`thm:dr-pole-contraction`, `lem:dr-filtration-reduction`, and `thm:dr-comparison`.
-/

@[expose] public section
