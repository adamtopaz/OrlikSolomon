/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Affine
public import OrlikSolomon.DeRham.Schemes.Log.AffineImage
public import OrlikSolomon.DeRham.Schemes.Log.Algebra
public import OrlikSolomon.DeRham.Schemes.Log.Basic
public import OrlikSolomon.DeRham.Schemes.Log.Comparison
public import OrlikSolomon.DeRham.Schemes.Log.Naturality
public import OrlikSolomon.DeRham.Schemes.Log.Projection
public import OrlikSolomon.DeRham.Schemes.Log.Residue
public import OrlikSolomon.DeRham.Schemes.Log.ResidueAffine
public import OrlikSolomon.DeRham.Schemes.Log.Restriction
public import OrlikSolomon.DeRham.Schemes.Log.RestrictionImage
public import OrlikSolomon.DeRham.Schemes.Log.Sections

/-!
# Logarithmic forms, residue and local comparison on schemes

This is the module to import for `thm:geo-log-sheaves`. For a geometric principal pair
`P = (X, D, U, f)`, the logarithmic sheaf is the image of regular forms and their left
products with `df/f` inside the ordinary direct image of forms on `U`.

The constructions over a commutative base ring give an injective regular inclusion, wedge
products and differential, the signed divisor shift, and a short exact residue sequence of
sheaf complexes. Transverse pullback is arbitrary, including non-flat morphisms. Associated
equations give canonical comparisons, and the right form projection formula has no sign.

On affine pairs, the complex of global logarithmic sections and its residue sequence agree
with the existing algebraic complexes, including the convention `G[γ] = [dλ]`. Restriction to
affine neighborhoods and the existing pole theorem prove the sheaf quasi-isomorphism when
positive integers are units, in particular over a characteristic-zero field.

## Main constructions and results

* `logSheaf`, `logComplexNat`, `logToOpenComplexNat`: logarithmic forms and their inclusion;
* `logSheafWedge`, `logSheafWedge_leibniz`: wedge multiplication and the signed dg rules;
* `logResidueShortComplexNat_shortExact`: the sheaf residue sequence with differential `-d`
  on the shifted divisor forms;
* `logSheafComparison`: the stalkwise quasi-isomorphism over a characteristic-zero field;
* `affineLogResidueShortComplexIso`: the affine comparison of all three complexes and arrows;
* `affineGlobalLogToOpen_quasiIso`, `logResidueSheafTop_surjective`,
  `exact_regularToLogTop_logResidueSheafTop`: affine global comparison, residue lifts and exactness;
* `logToOpenSheafAt`, `logResidueSheafAt`, `logSheafIdentitySectionsEquiv`: the typed section
  operations from `Log/Sections`, including simplification through identity reindexing;
* `logSheafPullback`, `logSheafWithEqnIso`, `logResidueSheaf_right_projection`: naturality,
  independence of an associated equation and the signless right projection formula.

The comparison target is the ordinary direct image, not a derived direct image. No exactness
or quasi-isomorphism assertion is passed through underived global sections on a non-affine
scheme. No arrangement or Orlik–Solomon presentation is imported by this module.

Blueprint: `thm:geo-log-sheaves`.
-/
