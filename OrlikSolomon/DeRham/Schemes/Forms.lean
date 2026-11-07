/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Forms.Presheaf
public import OrlikSolomon.DeRham.Schemes.Forms.Pullback
public import OrlikSolomon.DeRham.Schemes.Forms.Sheaf
public import OrlikSolomon.Geometry.Schemes.ModuleGluing

/-!
# Relative forms on schemes

Relative forms are sheafified in base-ring modules and retain the natural structure-sheaf
module action. The algebraic differential gives a complex with zero negative terms, and arbitrary
maps over the base induce pullback maps commuting with the differential.

## Main definitions and results

* `OrlikSolomon.Geometric.DeRham.formsSheaf`: relative forms as sheaves of base-ring modules.
* `OrlikSolomon.Geometric.DeRham.formsModuleSheaf`: the compatible structure-sheaf module.
* `OrlikSolomon.Geometric.DeRham.formsComplex`: the relative de Rham complex.
* `OrlikSolomon.Geometric.DeRham.formsSheafPullback`: pullback along arbitrary maps over the base.
* `OrlikSolomon.Geometric.tilde_map_exact`: exactness of associated module sheaves, reusing
  Mathlib's existing tilde construction.

No smoothness, affineness, nonemptiness or flatness hypothesis is used in these constructions.
The multiplicative structure and affine comparison are developed separately.

Blueprint: `lem:geo-module-gluing` and the constructions in `def:geo-forms-sheaf` and
`thm:geo-forms-comparison`.
-/
