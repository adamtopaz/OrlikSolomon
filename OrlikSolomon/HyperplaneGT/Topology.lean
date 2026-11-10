/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Topology.Classification
public import OrlikSolomon.HyperplaneGT.Topology.Cofinal
public import OrlikSolomon.HyperplaneGT.Topology.Compact
public import OrlikSolomon.HyperplaneGT.Topology.Consequences
public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact
public import OrlikSolomon.HyperplaneGT.Topology.Krull
public import OrlikSolomon.HyperplaneGT.Topology.Quotient
public import OrlikSolomon.HyperplaneGT.Topology.Restriction

/-!
# Topological reconstruction for the pure hyperplane diagrams

This optional facade exposes the direct finite-stage topologies, separation and compactness
results, degree-one and cofinal restrictions, exact pointwise and Krull classifiers, and
literal scalar quotients. It imports no cohomology theory, de Rham realization or Examples.

Importing this module activates no scope. Use the deliberately named topology scopes when
needed; Mathlib's global Krull topology and existing coefficient topologies remain intact.
The Krull wrappers retain their explicit fixing-condition or algebraicity hypotheses.

Blueprint: the pure portions of T01–T02 (`def:t01`, `lem:t02`), T03–T07
(`prop:t03`, `lem:t04`, `lem:t05`, `thm:t06`, `prop:t07`) and T09–T13
(`thm:t09`, `cor:t10`, `thm:t11`, `thm:t12`, `cor:t13`). The T08 rational-function
counterexample is available separately in the Examples development.
-/

@[expose] public section
