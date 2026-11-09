/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual
public import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Algebra.Group.Int.Units

/-!
# Full-dual and primitive-functional regressions

These consumers distinguish the full algebraic product from a finitely supported dual,
check inverse precomposition on a three-cycle, and test primitive functionals over empty
bases, the zero ring, a local ring with nilpotents and a nonlocal ring. Characteristic-two
determinants and a centralizer calculation use the public exterior-square API.

Blueprint: `lem:u03`, `lem:u05`, and the generic calculations of `lem:u04`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DualExamples

/-- The dual contains an infinite coordinate function with every coefficient equal to one. -/
theorem infinite_all_ones :
    Set.Infinite {i : ℕ | dualCoordinates
      (dualCoordinates.symm (fun _ : ℕ ↦ (1 : ℤ))) i ≠ 0} := by
  simpa using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

/-- Inverse precomposition moves a coordinate functional along a non-involutive permutation. -/
theorem three_cycle_action :
    dualAction (R := ℤ)
      (Finsupp.domLCongr ((Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2))
      (Finsupp.lapply 0) (Finsupp.single 1 1) = 1 := by
  simp only [dualAction_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single,
    Finsupp.lapply_apply]
  have h : ((Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2).symm 1 = 0 := by decide
  rw [h]
  simp

/-- The unique functional on the empty free module over the zero ring is surjective, although
it has no basis coordinate. Thus the local-ring unit-coordinate criterion must exclude this ring.
-/
theorem empty_zero_ring_counterexample :
    Primitive (0 : Module.Dual (ZMod 1) (Empty →₀ ZMod 1)) ∧
      ¬∃ i : Empty, IsUnit ((0 : Module.Dual (ZMod 1) (Empty →₀ ZMod 1))
        (Finsupp.single i 1)) := by
  constructor
  · intro r
    exact ⟨0, Subsingleton.elim _ _⟩
  · rintro ⟨i, -⟩
    exact i.elim

/-- Over a nonzero local ring an empty basis admits no primitive functional. -/
theorem not_primitive_empty (R : Type*) [CommSemiring R] [IsLocalRing R]
    (φ : Module.Dual R (Empty →₀ R)) : ¬Primitive φ := by
  rw [primitive_iff_unit_coordinate]
  simp

/-- The coordinate criterion's sufficient direction works over semirings without subtraction. -/
theorem natural_coordinate_primitive :
    Primitive (Finsupp.lapply (0 : ℕ) : Module.Dual ℕ (ℕ →₀ ℕ)) := by
  apply primitive_of_isUnit_coordinate _ 0
  simp

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- A unit coordinate gives a primitive functional on an infinite free module over the local
ring `ℤ/4`, whose nonzero element `2` is nilpotent. -/
theorem primitive_mod_four :
    Primitive (dualCoordinates.symm (fun _ : ℕ ↦ (3 : ZMod 4))) := by
  apply primitive_of_isUnit_coordinate _ 0
  simpa using (ZMod.isUnit_iff_coprime 3 4).mpr (by decide)

/-- A functional with every coordinate equal to the nonunit `2` is not primitive over `ℤ/4`. -/
theorem not_primitive_twice_mod_four :
    ¬Primitive (dualCoordinates.symm (fun _ : ℕ ↦ (2 : ZMod 4))) := by
  rw [primitive_iff_unit_coordinate]
  rintro ⟨i, hi⟩
  have hn : ¬IsUnit (2 : ZMod 4) := (ZMod.isUnit_iff_coprime 2 4).not.mpr (by decide)
  exact hn (by simpa using hi)

/-- An integer-valued functional with coordinates `3` and `2`. -/
def bezoutFunctional : Module.Dual ℤ (Bool →₀ ℤ) :=
  dualCoordinates.symm (fun b ↦ if b then 2 else 3)

/-- The nonlocal ring `ℤ` admits a primitive functional with no unit coordinate: `3 - 2 = 1`. -/
theorem primitive_without_unit_coordinate :
    Primitive bezoutFunctional ∧ ¬∃ i, IsUnit (bezoutFunctional (Finsupp.single i 1)) := by
  constructor
  · intro r
    refine ⟨Finsupp.single false r - Finsupp.single true r, ?_⟩
    simp [bezoutFunctional]
    ring
  · rintro ⟨i, hi⟩
    cases i <;> simp [bezoutFunctional, Int.isUnit_iff] at hi

/-- The determinant pairing is nonzero in characteristic two. Alternation is not obtained by
cancelling a factor of two. -/
theorem determinant_mod_two :
    dualDeterminant (R := ZMod 2) (Finsupp.lapply false) (Finsupp.lapply true)
      (exteriorPower.ιMulti (ZMod 2) 2 ![Finsupp.single false 1, Finsupp.single true 1]) = 1 := by
  simp

/-- The difference-vector determinant formula also detects a triple relation in characteristic
two, without changing the signs of the defining formula. -/
theorem difference_determinant_mod_two :
    dualDeterminant (R := ZMod 2) (Finsupp.lapply (0 : Fin 3)) (Finsupp.lapply 1)
      (exteriorPower.ιMulti (ZMod 2) 2
        ![Finsupp.single 0 1 - Finsupp.single 2 1,
          Finsupp.single 1 1 - Finsupp.single 2 1]) = 1 := by simp

/-- A centralizer for one relation is an actual linear condition on the second functional,
over every commutative ring, including the zero ring. -/
theorem mem_pair_centralizer_iff (R : Type*) [CommRing R]
    (ψ : Module.Dual R (Bool →₀ R)) :
    ψ ∈ centralizer
      (Submodule.span R (Set.singleton (exteriorPower.ιMulti R 2
        ![Finsupp.single false 1, Finsupp.single true 1]))) (Finsupp.lapply false) ↔
      dualCoordinates ψ true = 0 := by
  rw [mem_centralizer_iff, commutes_span_iff]
  constructor
  · intro h
    have hw := h _ rfl
    simpa using hw
  · intro h q hq
    change q = _ at hq
    subst q
    simpa using h

/-- Equality-preservation of the full relation submodule gives the centralizer equivalence
through the public paired-action API. -/
theorem full_relation_centralizer_action (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (g : M ≃ₗ[R] M) (φ ψ : Module.Dual R M) :
    dualAction g ψ ∈ centralizer ⊤ (dualAction g φ) ↔ ψ ∈ centralizer ⊤ φ := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  apply commutes_dualAction_iff
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (exteriorPower.map_surjective g.surjective)

end OrlikSolomon.HyperplaneGT.DualExamples
