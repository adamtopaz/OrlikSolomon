/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Presentation.Geometric.Affine
public import OrlikSolomon.Presentation.Geometric.Ordinary
public import OrlikSolomon.Presentation.Geometric.Projective
public import OrlikSolomon.Presentation.Geometric.Transport

/-!
# The geometric structure theorems

This is the public facade of stage G3 of the geometric refactor blueprint: the Orlik–Solomon
structure theorems for a cohomology theory on smooth schemes, with the complements as actual open
subschemes of affine and projective space. A consumer imports only this module. A theory on any
admissible domain applies, for example one on all smooth schemes, with no affine comparison, descent
axiom or hypothesis on the arrangement supplied by the user.

* `Presentation/Geometric/Transport`: `thm:geo-transport-all`, the comparison
  `transportAffineDevelopment` of the old theory `T.toAlgebraic` at `A` with `T` at an object
  `X ≅ Spec A`, and its laws.
* `Presentation/Geometric/Affine`: `thm:geo-affine`, `OrdinaryTheory.affineEquiv :
  OS_B(𝒜) ≃ₐ[B] C(U_𝒜)`, with its generators, uniqueness, independence of equations, bigrading,
  naturality and deletion residue.
* `Presentation/Geometric/Ordinary`: the forms of `thm:geo-affine` with coefficients in `R`: the
  groups `H^{p, w}(U_𝒜)`, the diagonal `OS_R(𝒜) ≃ ⨁_q H^{q, q}(U_𝒜)`, vanishing, bases and Betti
  numbers.
* `Presentation/Geometric/Projective`: `thm:geo-projective`, `OrdinaryTheory.projectiveEquiv :
  OS̄_B(P) ≃ₐ[B] C(U_P)` for nonempty `P`, its diagonal and multiplicities.

Each theorem is the existing one for `T.toAlgebraic`, composed with pullback along the comparison
`s_𝒜` or `s_P` of the complement with the spectrum of its coordinate ring, so no argument about
arrangements is repeated. The existing theorems remain available, and these are additional
public entries.

Blueprint: `thm:geo-affine`, `thm:geo-projective`, `thm:geo-transport-all`.
-/
