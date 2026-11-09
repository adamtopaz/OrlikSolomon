/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Algebra.Group.Int.Units

/-!
# Full-dual, primitive-functional and configuration regressions

These consumers distinguish the full algebraic product from a finitely supported dual,
check inverse precomposition on a three-cycle, and test primitive functionals over empty
bases, the zero ring, a local ring with nilpotents and a nonlocal ring. Characteristic-two
determinants and a centralizer calculation use the public exterior-square API. The actual
global quadratic relation span is tested on parallel points and concurrent lines, including
characteristic two, zero coefficients and dimension zero. A scalar diagram over `ℤ/5`
checks that the actual contragredient action uses the inverse scalar and carries the full
universal centralizer onto its image.

Blueprint: `lem:u03`, `lem:u05`, `lem:u04`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DualExamples

universe u v

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

/-- The zero point of the affine line over `𝔽₂`. -/
def binaryZero : Hyperplane (ZMod 2) 1 :=
  graphHyperplane 0 (AffineMap.const _ _ 0)

/-- The one point of the affine line over `𝔽₂`. -/
def binaryOne : Hyperplane (ZMod 2) 1 :=
  graphHyperplane 0 (AffineMap.const _ _ 1)

/-- Two actual parallel labels impose a nontrivial global determinant equation in
characteristic two. -/
theorem parallel_coordinate_functionals_not_commute :
    ¬Commutes (universalQuadraticRelationSpan (ZMod 2))
      (Finsupp.lapply binaryZero) (Finsupp.lapply binaryOne) := by
  intro h
  have hparallel : Parallel binaryZero binaryOne := CoordinateExamples.parallel_points
  have hdet := (commutes_universalQuadraticRelationSpan_iff _ _).mp h |>.1 _ _ hparallel
  simp [dualCoordinates_apply, Finsupp.lapply_apply, hparallel.1, hparallel.1.symm] at hdet

/-- A genuine concurrent triple imposes its difference-coordinate relation, also in
characteristic two. -/
theorem concurrent_coordinate_functionals_not_commute :
    ¬Commutes (universalQuadraticRelationSpan (ZMod 2))
      (Finsupp.lapply (CoordinateExamples.xLine (ZMod 2)))
      (Finsupp.lapply (CoordinateExamples.yLine (ZMod 2))) := by
  intro h
  have hdep : DependentTriple (CoordinateExamples.xLine (ZMod 2))
      (CoordinateExamples.yLine (ZMod 2)) (CoordinateExamples.diagonalLine 0) :=
    (dependentTriple_iff_trace_eq _ _ _ CoordinateExamples.xLine_ne_yLine
      (CoordinateExamples.xLine_ne_diagonalLine 0)
      (CoordinateExamples.yLine_ne_diagonalLine 0)).mpr CoordinateExamples.concurrent_traces
  have hdet := (commutes_universalQuadraticRelationSpan_iff _ _).mp h |>.2 _ _ _ hdep
  simp [dualCoordinates_apply, Finsupp.lapply_apply, CoordinateExamples.xLine_ne_yLine,
    CoordinateExamples.xLine_ne_diagonalLine, CoordinateExamples.yLine_ne_diagonalLine,
    ne_comm] at hdet

/-- Over the zero coefficient ring the actual universal centralizer is the whole dual. -/
theorem zero_ring_universal_centralizer (k : Type u) [Field k] (n : ℕ)
    (φ : Module.Dual (ZMod 1) (Hyperplane k n →₀ ZMod 1)) :
    centralizer (universalQuadraticRelationSpan (ZMod 1)) φ = ⊤ := by
  ext ψ
  simp only [Submodule.mem_top, iff_true]
  rw [mem_centralizer_universalQuadraticRelationSpan_iff]
  constructor <;> intros <;> exact Subsingleton.elim _ _

/-- In dimension zero there are no geometric labels, so every universal centralizer is full.
The geometric field and coefficient ring have independent universes. -/
theorem dimension_zero_universal_centralizer (k : Type u) (R : Type v) [Field k] [CommRing R]
    (φ : Module.Dual R (Hyperplane k 0 →₀ R)) :
    centralizer (universalQuadraticRelationSpan R) φ = ⊤ := by
  ext ψ
  simp only [Submodule.mem_top, iff_true]
  rw [mem_centralizer_universalQuadraticRelationSpan_iff]
  constructor <;> intro H <;> exact ((CoordinateExamples.dimension_zero (k := k)).false H).elim

/-- The scalar two is a unit with inverse three in `ℤ/5`. -/
def scalarTwoUnit : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

/-- Scalar multiplication by two acts by four on the exterior square over `ℤ/5`. -/
theorem exterior_scalar_two (M : Type*) [AddCommGroup M] [Module (ZMod 5) M] :
    exteriorPower.map 2 (LinearEquiv.smulOfUnit (M := M) scalarTwoUnit).toLinearMap =
      (4 : ZMod 5) • (LinearMap.id : (⋀[ZMod 5]^2 M) →ₗ[ZMod 5] ⋀[ZMod 5]^2 M) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  change exteriorPower.ιMulti (ZMod 5) 2 (fun i ↦ (2 : ZMod 5) • v i) =
    (4 : ZMod 5) • exteriorPower.ιMulti (ZMod 5) 2 v
  rw [AlternatingMap.map_smul_univ]
  norm_num

/-- Multiplication by four is invertible, so the scalar-two exterior map preserves every
relation submodule by equality. -/
theorem scalar_two_exterior_preserves (M : Type*) [AddCommGroup M] [Module (ZMod 5) M]
    (Q : Submodule (ZMod 5) (⋀[ZMod 5]^2 M)) :
    Q.map (exteriorPower.map 2
      (LinearEquiv.smulOfUnit (M := M) scalarTwoUnit).toLinearMap) = Q := by
  rw [exterior_scalar_two]
  apply le_antisymm
  · rintro q ⟨p, hp, rfl⟩
    exact Q.smul_mem 4 hp
  · intro q hq
    refine ⟨4 • q, Q.smul_mem 4 hq, ?_⟩
    change (4 : ZMod 5) • ((4 : ZMod 5) • q) = q
    rw [smul_smul, show (4 : ZMod 5) * 4 = 1 from by decide, one_smul]

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}

/-- Scalar multiplication by two gives an actual marked diagram automorphism over `ℤ/5`.
All finite-stage, common-target and marking squares are retained. -/
def scalarTwoDiagram (C : CofinalSystem k₀ k n) (S : Set k₀) : DiagramAut (ZMod 5) C S := by
  refine DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.smulOfUnit scalarTwoUnit)
    (LinearEquiv.smulOfUnit scalarTwoUnit)
    (fun A ↦ scalar_two_exterior_preserves _ (quadraticRelationSpan (ZMod 5) A.val.val)) ?_ ?_
  · intro A B h
    apply LinearMap.ext
    intro x
    change (2 : ZMod 5) • Finsupp.lmapDomain (ZMod 5) (ZMod 5) (Arrangement.inclusion h) x =
      Finsupp.lmapDomain (ZMod 5) (ZMod 5) (Arrangement.inclusion h) ((2 : ZMod 5) • x)
    exact (map_smul _ _ _).symm
  · intro A w hw
    apply LinearMap.ext
    intro x
    change (2 : ZMod 5) • w.basisMap (ZMod 5) hw x =
      w.basisMap (ZMod 5) hw ((2 : ZMod 5) • x)
    exact (map_smul _ _ _).symm

/-- The universal map induced by the scalar diagram has the same scalar on every label. -/
theorem scalarTwoDiagram_universal_apply (C : CofinalSystem k₀ k n) (S : Set k₀)
    (m : Hyperplane k n →₀ ZMod 5) :
    (scalarTwoDiagram C S).universalEquiv m = (2 : ZMod 5) • m := by
  obtain ⟨A, a, rfl⟩ := C.exists_stage_vector (ZMod 5) m
  rw [DiagramAut.universalEquiv_finiteStageMap]
  change finiteStageMap (ZMod 5) A.val.val ((2 : ZMod 5) • a) =
    (2 : ZMod 5) • finiteStageMap (ZMod 5) A.val.val a
  exact map_smul _ _ _

/-- The actual contragredient diagram action uses the inverse scalar, which is three rather
than two in `ℤ/5`. This distinguishes inverse precomposition from direct precomposition. -/
theorem scalarTwo_dual_coordinate (C : CofinalSystem k₀ k n) (S : Set k₀)
    (H : Hyperplane k n) :
    DiagramAut.dualAction (scalarTwoDiagram C S) (Finsupp.lapply H)
      (Finsupp.single H 1) = 3 := by
  rw [DiagramAut.dualAction_apply]
  have hinv : (scalarTwoDiagram C S).universalEquiv.symm (Finsupp.single H 1) =
      (3 : ZMod 5) • Finsupp.single H 1 := by
    apply (scalarTwoDiagram C S).universalEquiv.injective
    rw [LinearEquiv.apply_symm_apply, scalarTwoDiagram_universal_apply]
    rw [smul_smul, show (2 : ZMod 5) * 3 = 1 from by decide, one_smul]
  rw [hinv]
  simp

/-- A concrete characteristic-two geometric label with `ℤ/5` coefficients detects the
inverse action through a nonempty set of marking constants. -/
theorem binary_scalar_two_inverse_action :
    DiagramAut.dualAction
      (scalarTwoDiagram (fullCofinalSystem (ZMod 2) (ZMod 2) 1) {0, 1})
      (Finsupp.lapply binaryZero) (Finsupp.single binaryZero 1) = 3 :=
  scalarTwo_dual_coordinate _ _ _

/-- The actual scalar diagram maps the whole universal centralizer onto the transformed
centralizer. This consumes the submodule equality, rather than only one implication. -/
theorem scalar_two_centralizer_image (C : CofinalSystem k₀ k n) (S : Set k₀)
    (φ : Module.Dual (ZMod 5) (Hyperplane k n →₀ ZMod 5)) :
    (centralizer (universalQuadraticRelationSpan (ZMod 5)) φ).map
        (DiagramAut.dualAction (scalarTwoDiagram C S)).toLinearMap =
      centralizer (universalQuadraticRelationSpan (ZMod 5))
        (DiagramAut.dualAction (scalarTwoDiagram C S) φ) :=
  DiagramAut.map_centralizer_dualAction _ _

end OrlikSolomon.HyperplaneGT.DualExamples
