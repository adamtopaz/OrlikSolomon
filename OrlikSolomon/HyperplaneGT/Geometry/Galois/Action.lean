/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Galois.CoordinateAction
public import Mathlib.Algebra.Algebra.Equiv

/-!
# The coefficient Galois action on affine hyperplanes

Automorphisms of the geometric field over its base field act on hyperplanes by applying the
automorphism to equation coefficients. This is the same as coordinatewise transport of the
underlying affine subspace. It preserves strict parallelism, guarded dependent triples and
coordinate verticality; the coordinate-action leaf preserves all intersections and codimensions.

## Main results

* `galoisAction` constructs the group action.
* `coefficientPoint_galois_smul` identifies it on projective equation coefficients.
* `parallel_galois_smul_iff`, `dependentTriple_galois_smul_iff` and
  `isVertical_galois_smul_iff` preserve the three incidence predicates in both directions.

Blueprint: `lem:g04`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}

/-- The genuine group action of field automorphisms on affine hyperplanes.
It is constructed from coefficient transport, not assumed as naturality of a cohomology theory.

Blueprint: `lem:g04`. -/
instance galoisAction : MulAction (k ≃ₐ[k₀] k) (Hyperplane k n) where
  smul σ H := fieldHyperplaneEquiv σ.toRingEquiv H
  one_smul H := Subtype.ext (fieldAffineSubspace_refl H.val)
  mul_smul σ τ H := Subtype.ext (fieldAffineSubspace_trans τ.toRingEquiv σ.toRingEquiv H.val)

@[simp]
theorem galois_smul_val (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    (σ • H).val = fieldAffineSubspace σ.toRingEquiv H.val := rfl

/-- Coefficient points intertwine the Galois action and its projective semilinear action.
-/
theorem coefficientPoint_galois_smul (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    coefficientPoint (σ • H) = fieldCoefficientPoint σ.toRingEquiv (coefficientPoint H) :=
  coefficientPoint_fieldHyperplaneEquiv σ.toRingEquiv H

@[simp]
theorem parallel_galois_smul_iff (σ : k ≃ₐ[k₀] k) (H K : Hyperplane k n) :
    Parallel (σ • H) (σ • K) ↔ Parallel H K :=
  parallel_fieldHyperplaneEquiv_iff σ.toRingEquiv H K

@[simp]
theorem dependentTriple_galois_smul_iff (σ : k ≃ₐ[k₀] k) (H K L : Hyperplane k n) :
    DependentTriple (σ • H) (σ • K) (σ • L) ↔ DependentTriple H K L :=
  dependentTriple_fieldHyperplaneEquiv_iff σ.toRingEquiv H K L

@[simp]
theorem isVertical_galois_smul_iff (σ : k ≃ₐ[k₀] k)
    (J : Finset (Fin n)) (H : Hyperplane k n) :
    IsVertical J (σ • H) ↔ IsVertical J H :=
  isVertical_fieldHyperplaneEquiv_iff σ.toRingEquiv J H

end OrlikSolomon.HyperplaneGT
