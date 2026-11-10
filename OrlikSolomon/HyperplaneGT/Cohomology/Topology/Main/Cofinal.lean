/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Basic
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Compatibility.Groups
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Compatibility.Quotients
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Quotient
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Main.Cofinal.Restriction

/-!
# Topological cofinal independence for actual supplied theories

Literal actual stage selection is an inducing embedding over arbitrary coefficients and
in every dimension. Under exactly the existing reconstruction hypotheses, the four old
group equivalences and four new induced quotient equivalences are homeomorphisms. The
single common target, all classifier and degree-one squares and unrelated-family union
comparisons remain unchanged. No field-extension condition or union closure is added.
Importing this optional facade activates no topology scope.

Blueprint: the cofinal clauses of T15 (`thm:t15`).
-/

@[expose] public section
