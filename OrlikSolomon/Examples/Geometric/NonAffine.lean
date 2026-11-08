/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.GlobalForms
public import OrlikSolomon.Examples.Geometric.NonAffine.MayerVietoris
public import OrlikSolomon.Examples.Geometric.NonAffine.SheafCech

/-!
# The non-affine projective-line regression

This facade exposes the actual projective line, its smooth-domain membership and standard
pair, its two affine charts and Laurent overlap, and both computations of differential forms.
Global forms give `k` in degree zero only. The actual two-chart Čech–de Rham complex gives
`k` in degrees zero and two over a characteristic-zero field, with generator `[dT/T]`.
`ProjectiveLineMayerVietorisData` also proves the same answer for every graded family fitting
the Mayer–Vietoris long exact sequence on the actual affine-chart and overlap homology.
No non-affine cohomology instance is constructed or assumed.

Main results: `projectiveLineScope`, `projectiveLineGlobalFormsComplexIso`,
`projectiveLineSheafCechIso`, the degreewise homology comparisons and vanishing results,
and `projectiveLineGlobalForms_not_quasiIso`.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section
