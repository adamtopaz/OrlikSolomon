/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# A three-equation unit transfer calculation

Two proportionality equations with a common unit coefficient, together with one translated
equation, force equality of the other two coefficients. Only the specified unit is cancelled;
no domain, nonzero-ring, local-ring or invertibility-of-two hypothesis is used.

This generic calculation supplies the coefficient step in L04 (`lem:l04`), independently
of its hyperplane geometry and centralizer-surjectivity hypotheses.
-/

@[expose] public section

namespace OrlikSolomon

/-- Two equations sharing a unit coefficient and their translated comparison force equality
of the remaining coefficients. Blueprint: the ring calculation in `lem:l04`. -/
theorem eq_of_unit_transfer {R : Type*} [CommRing R] (u : Rˣ)
    (a₁ a₂ b₀ b₁ b₂ : R)
    (h₀₁ : (u : R) * b₁ = a₁ * b₀)
    (h₀₂ : (u : R) * b₂ = a₂ * b₀)
    (h₁₂ : a₁ * (b₂ - 1) = a₂ * (b₁ - 1)) : a₁ = a₂ := by
  have hmul : a₁ * b₂ = a₂ * b₁ := by
    apply u.isUnit.mul_left_cancel
    calc
      (u : R) * (a₁ * b₂) = a₁ * ((u : R) * b₂) := by ring
      _ = a₁ * (a₂ * b₀) := congrArg (a₁ * ·) h₀₂
      _ = a₂ * (a₁ * b₀) := by ring
      _ = a₂ * ((u : R) * b₁) := congrArg (a₂ * ·) h₀₁.symm
      _ = (u : R) * (a₂ * b₁) := by ring
  have hsub : a₁ * b₂ - a₁ = a₂ * b₁ - a₂ := by
    simpa only [mul_sub, mul_one] using h₁₂
  rw [hmul] at hsub
  exact sub_right_inj.mp hsub

end OrlikSolomon
