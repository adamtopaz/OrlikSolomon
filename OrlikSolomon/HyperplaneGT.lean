/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual
public import OrlikSolomon.HyperplaneGT.Algebra.LowDegrees
public import OrlikSolomon.HyperplaneGT.Diagram.Basic
public import OrlikSolomon.HyperplaneGT.Diagram.Cofinal
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction
public import OrlikSolomon.HyperplaneGT.Diagram.Universal
public import OrlikSolomon.HyperplaneGT.Geometry.Collineation
public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates
public import OrlikSolomon.HyperplaneGT.Geometry.Galois
public import OrlikSolomon.HyperplaneGT.Reconstruction.Cofinal
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain
public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois
public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence
public import OrlikSolomon.HyperplaneGT.Reconstruction.Local
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing
public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace

/-!
# Pure hyperplane-diagram reconstruction facade

The geometry, free modules, full OS presentations, marked diagrams and local/domain
classification are independent of any cohomology theory. Cofinal restriction has its literal
stagewise forward map and a classified inverse. This pure-core facade imports neither the
conditional cohomology adapter/main layer nor any de Rham realization.

Blueprint: the pure G/A/U/L/P/I/C/S nodes and pure restriction step of E02 (`cor:e02`).
-/

@[expose] public section
