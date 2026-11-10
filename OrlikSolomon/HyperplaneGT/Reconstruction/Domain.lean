/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Quotient

/-!
# Integral-domain classification of the marked quadratic and full graded diagrams

Pure coefficient extension carries the actual finite-stage matrices, both explicit quadratic
relation families and the single common marking target along any commutative coefficient map.
No injectivity or nonzero-ring hypothesis is needed for extension itself.

Over an integral domain, classification over its fraction field recovers a primal scalar
and its inverse from entries of the original common-target matrices. Injectivity descends
all components to the original ring. The main equivalence `coefficientDomainAutEquiv` has
explicit inverse coordinates and stage, target, marking and full-dual formulas.
`coefficientDomainGradedAutEquiv` is the original degree-one restriction, now with its full
scalar/Galois inverse; `coefficientDomainGradedClassificationEquiv` gives scalar powers in
every ordinary degree. Both literal central-scalar quotients are canonically Galois, with
the existing direct Galois sections as inverses. All classifications and quotient maps agree
with their local versions when the domain is also local.

Blueprint: S05 (`thm:s05`). The pure core imports no cohomology or de Rham module and proves
no localization statement for an arbitrary cohomology theory.
-/

@[expose] public section
