/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Collineation
public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import OrlikSolomon.Examples.HyperplaneGT.DeRhamReconstruction
public import OrlikSolomon.Examples.HyperplaneGT.DegreeOne
public import OrlikSolomon.Examples.HyperplaneGT.Diagram
public import OrlikSolomon.Examples.HyperplaneGT.Disconnected
public import OrlikSolomon.Examples.HyperplaneGT.DomainClassification
public import OrlikSolomon.Examples.HyperplaneGT.Dual
public import OrlikSolomon.Examples.HyperplaneGT.FinalCoefficients
public import OrlikSolomon.Examples.HyperplaneGT.Galois
public import OrlikSolomon.Examples.HyperplaneGT.GaloisAction
public import OrlikSolomon.Examples.HyperplaneGT.GaloisReconstruction
public import OrlikSolomon.Examples.HyperplaneGT.GradedClassification
public import OrlikSolomon.Examples.HyperplaneGT.Incidence
public import OrlikSolomon.Examples.HyperplaneGT.Local
public import OrlikSolomon.Examples.HyperplaneGT.LocalClassification
public import OrlikSolomon.Examples.HyperplaneGT.Projections
public import OrlikSolomon.Examples.HyperplaneGT.QuadraticKernel
public import OrlikSolomon.Examples.HyperplaneGT.TheoryReconstruction
public import OrlikSolomon.Examples.HyperplaneGT.Trace
public import OrlikSolomon.Examples.HyperplaneGT.Universal

/-!
# Hyperplane reconstruction acceptance examples

Collect the durable coefficient, dimension, generator, incidence, full-dual, marking,
cofinality and classification regressions. The final coefficient leaves retain binary
and nonfield nilpotent local coefficients, actual scalar quotients and the common target.
The disconnected example constructs a genuine full product-coefficient diagram outside
the local/domain classification, rather than assuming its relation preservation.

Each topic keeps its own hypotheses. In particular, examples taking a supplied ordinary
theory do not construct a new nonzero characteristic-two cohomology realization. This
example umbrella changes no pure-core, conditional-theory or explicit de Rham facade.

Blueprint: milestone M8 regression and completion checklist.
-/

@[expose] public section
