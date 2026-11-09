/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Coordinates
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Primitive functionals on arbitrary free modules

A primitive functional is literally a surjective linear map to the coefficient ring.
Precomposition by a linear equivalence preserves this property. Over a nonzero local ring,
primitivity on a free module is equivalent to a unit value on some standard basis vector.
The index type need not be finite. No residue-field or maximal-ideal product criterion is used.

Blueprint: `lem:u05`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u v w w'

variable {R : Type u} [CommSemiring R]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {M' : Type w'} [AddCommMonoid M'] [Module R M']

/-- A functional is primitive when it is surjective onto the coefficient ring.
This definition also applies to zero rings and empty free bases. Blueprint: `lem:u05`. -/
def Primitive (φ : Module.Dual R M) : Prop := Function.Surjective φ

/-- A change of basis preserves primitive functionals. Blueprint: `lem:u05`. -/
theorem primitive_comp_linearEquiv_iff (φ : Module.Dual R M) (g : M' ≃ₗ[R] M) :
    Primitive (φ.comp g.toLinearMap) ↔ Primitive φ :=
  Function.Surjective.of_comp_iff φ g.surjective

@[simp]
theorem primitive_dualAction_iff (g : M ≃ₗ[R] M) (φ : Module.Dual R M) :
    Primitive (dualAction g φ) ↔ Primitive φ :=
  primitive_comp_linearEquiv_iff φ g.symm

variable {ι : Type v}

/-- A unit coordinate gives a preimage of every scalar, over any commutative semiring.
Blueprint: the sufficient direction of `lem:u05`. -/
theorem primitive_of_isUnit_coordinate (φ : Module.Dual R (ι →₀ R)) (i : ι)
    (hi : IsUnit (φ (Finsupp.single i 1))) : Primitive φ := by
  obtain ⟨u, hu⟩ := hi
  intro r
  refine ⟨(r * (u⁻¹ : Rˣ)) • Finsupp.single i 1, ?_⟩
  rw [map_smul, ← hu, smul_eq_mul]
  simp [mul_assoc]

/-- Over a local ring, a surjective functional on any free module has a unit coordinate.
Mathlib's `IsLocalRing` includes nontriviality. Blueprint: `lem:u05`. -/
theorem primitive_iff_unit_coordinate [IsLocalRing R] (φ : Module.Dual R (ι →₀ R)) :
    Primitive φ ↔ ∃ i, IsUnit (φ (Finsupp.single i 1)) := by
  constructor
  · intro hφ
    obtain ⟨m, hm⟩ := hφ 1
    have hsum : IsUnit (m.sum (fun i r ↦ r * φ (Finsupp.single i 1))) := by
      rw [← dual_apply_eq_sum, hm]
      exact isUnit_one
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hsum
    exact ⟨i, isUnit_of_mul_isUnit_right hi⟩
  · rintro ⟨i, hi⟩
    exact primitive_of_isUnit_coordinate φ i hi

end OrlikSolomon.HyperplaneGT
