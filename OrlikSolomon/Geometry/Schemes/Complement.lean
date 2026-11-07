/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Complement.AffineSpace
public import OrlikSolomon.Geometry.Schemes.Complement.Basic
public import OrlikSolomon.Geometry.Schemes.Complement.Deletion
public import OrlikSolomon.Geometry.Schemes.Complement.Targets

/-!
# Affine spaces, arrangement complements, deletion and relation targets as schemes

This is the module to import for stage G2 of the geometric refactor blueprint on the affine side:
`def:geo-affine-space`, `def:geo-complement`, `thm:geo-complement-spec`, `thm:geo-deletion` and
`thm:geo-small-targets`.

* `Geometry/Schemes/Complement/AffineSpace`: `𝔸_V = Spec Sym(V*)`, the functions of affine
  functions, the morphisms of affine maps, hyperplane schemes, and the comparison with Mathlib's
  `AffineSpace`.
* `Geometry/Schemes/Complement/Basic`: the complement `U_𝒜` as an open subscheme of `𝔸_V`, the
  comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` and its naturality.
* `Geometry/Schemes/Complement/Deletion`: the geometric deletion pair and the fiber product
  `U_𝒜'' = U_𝒜' ×_{𝔸_V} 𝐇`.
* `Geometry/Schemes/Complement/Targets`: the two relation targets as scheme morphisms.

A consumer that transports an existing theorem about `SmoothAlg.complement 𝒜` to the scheme `U_𝒜`
in a domain `D` composes with pullback along `SmoothDomain.complementIsoSpec D 𝒜`, and uses
`SmoothDomain.complementIsoSpec_hom_appTop_complementUnit` for generators,
`SmoothDomain.complementMap_comp_complementIsoSpec_hom` and its variants for naturality, and
`DivisorPair.deletionPairIsoSpec` for residues.
-/
