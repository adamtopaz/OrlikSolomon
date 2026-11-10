/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.Coefficients
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Infinite
public import OrlikSolomon.Examples.HyperplaneGT.Topology.RatFunc
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Realizations
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Realizations.Ordinary
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Realizations.Reconstruction
public import OrlikSolomon.Examples.HyperplaneGT.Topology.Systems

/-!
# Examples for topological hyperplane reconstruction

This acceptance umbrella gathers coefficient and system regressions, canonical actual-theory
comparisons, the genuine infinite Frobenius example, and the rational-function counterexample
to replacing pointwise convergence by Krull without its comparison hypothesis.

The fixtures use the library's actual diagrams, original common targets, scalar quotients
and selected cofinal systems. Conditional nonfield-coefficient theory assertions remain
distinct from the constructed characteristic-zero ordinary de Rham specialization. Zero
coefficients and dimension zero are used only by the applicable unclassified interfaces.

These Examples remain outside the library core. Importing this umbrella activates no
topology scope or global coefficient/automorphism topology instance.

Blueprint: T08 (`prop:t08`) and the required M9 coefficient, system, Galois and realization
regressions accompanying T01–T17.
-/

@[expose] public section
