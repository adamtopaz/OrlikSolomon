/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Graphs
public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Incidence

/-!
# Hyperplane coefficients, incidence and coordinate graphs

The leaves provide the coefficient-point equivalence, the parallel-pair and dependent-triple
criteria, and normalized graph charts. This facade joins the graph and incidence APIs.

## Main results

* `coefficientPointEquiv` identifies hyperplanes with projective coefficient points other than
  the constant point.
* `parallel_iff_normal_proportional` detects parallelism from any equations.
* `existsUnique_graph_of_not_isVertical` and `graphProjectionEquiv` give the unique graph chart.
* `parallel_graphHyperplane_of_sub_eq_const` expresses the constant-difference graph branch
  in terms of strict parallelism.

Blueprint: `lem:g01`, `lem:g02`, `lem:g03`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

variable {k : Type*} [Field k] {n : ℕ}

/-- Graphs whose functions differ by a nonzero constant are strictly parallel.

Blueprint: `lem:g03`. -/
theorem parallel_graphHyperplane_of_sub_eq_const (i : Fin n)
    {h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k} {c : k}
    (hc : c ≠ 0) (hconst : h₁ - h₀ = AffineMap.const k _ c) :
    Parallel (graphHyperplane i h₀) (graphHyperplane i h₁) := by
  refine ⟨?_, graphSubspace_inf_eq_bot_of_sub_eq_const i hc hconst⟩
  intro h
  exact graphSubspace_ne_of_sub_eq_const i hc hconst (congrArg Subtype.val h)

end OrlikSolomon.HyperplaneGT
