/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Automorphisms
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central scalar automorphisms of the marked quadratic diagram

A coefficient unit acts by the same scalar on every finite-stage module and on the one
common marking target. Its exterior-square action preserves every relation submodule by
equality. These families form an injective central subgroup of the actual `DiagramAut`,
over every commutative coefficient ring, including the zero ring and in dimension zero.

Blueprint: the scalar family in S03 (`thm:s03`); no classification is asserted here.
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

/-- The exterior square of a unit scalar preserves every submodule by image equality,
since its action is multiplication by the square of that unit. -/
theorem map_exteriorPower_smulOfUnit (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (a : Rˣ) (Q : Submodule R (⋀[R]^2 M)) :
    Q.map (exteriorPower.map 2 (LinearEquiv.smulOfUnit (M := M) a).toLinearMap) = Q := by
  have he : exteriorPower.map 2 (LinearEquiv.smulOfUnit (M := M) a).toLinearMap =
      (a : R) ^ 2 • (LinearMap.id : (⋀[R]^2 M) →ₗ[R] ⋀[R]^2 M) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
      LinearMap.smul_apply, LinearMap.id_apply]
    change exteriorPower.ιMulti R 2 (fun i ↦ (a : R) • v i) =
      (a : R) ^ 2 • exteriorPower.ιMulti R 2 v
    rw [AlternatingMap.map_smul_univ]
    simp
  rw [he]
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact Q.smul_mem _ hq
  · intro q hq
    refine ⟨((a⁻¹ : Rˣ) : R) ^ 2 • q, Q.smul_mem _ hq, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← mul_pow]
    simp

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Multiplication by one coefficient unit on every stage and on the common marking target.
The whole relation submodule is preserved, without a nonzero or local-ring hypothesis.
Blueprint: S03 (`thm:s03`). -/
def scalarQuadraticAut (a : Rˣ) : DiagramAut R C S := by
  refine DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.smulOfUnit a)
    (LinearEquiv.smulOfUnit a)
    (fun A ↦ map_exteriorPower_smulOfUnit R _ a (quadraticRelationSpan R A.val.val)) ?_ ?_
  · intro A B h
    apply LinearMap.ext
    intro x
    change (a : R) • Finsupp.lmapDomain R R (Arrangement.inclusion h) x =
      Finsupp.lmapDomain R R (Arrangement.inclusion h) ((a : R) • x)
    exact (map_smul _ _ _).symm
  · intro A w hw
    apply LinearMap.ext
    intro x
    change (a : R) • w.basisMap R hw x = w.basisMap R hw ((a : R) • x)
    exact (map_smul _ _ _).symm

/-- Every finite-stage component of the scalar family is multiplication by its unit. -/
@[simp]
theorem scalarQuadraticAut_stageEquiv_apply (a : Rˣ) (A : C.Stage)
    (x : A.val.val →₀ R) :
    (scalarQuadraticAut R C S a).stageEquiv A x = (a : R) • x := rfl

/-- The inverse stage component acts by the inverse coefficient unit. -/
@[simp]
theorem scalarQuadraticAut_stageEquiv_symm_apply (a : Rˣ) (A : C.Stage)
    (x : A.val.val →₀ R) :
    ((scalarQuadraticAut R C S a).stageEquiv A).symm x = (↑a⁻¹ : R) • x := rfl

/-- The same unit acts on the one common target, even when there are no available markings. -/
@[simp]
theorem scalarQuadraticAut_targetEquiv_apply (a : Rˣ) (x : Fin 2 →₀ R) :
    (scalarQuadraticAut R C S a).targetEquiv x = (a : R) • x := rfl

/-- The inverse common-target component acts by the inverse coefficient unit. -/
@[simp]
theorem scalarQuadraticAut_targetEquiv_symm_apply (a : Rˣ) (x : Fin 2 →₀ R) :
    (scalarQuadraticAut R C S a).targetEquiv.symm x = (↑a⁻¹ : R) • x := rfl

/-- Gluing the scalar family gives scalar multiplication on the literal universal module. -/
@[simp]
theorem scalarQuadraticAut_universalEquiv_apply (a : Rˣ) (x : Hyperplane k n →₀ R) :
    (scalarQuadraticAut R C S a).universalEquiv x = (a : R) • x := by
  obtain ⟨A, y, rfl⟩ := C.exists_stage_vector R x
  rw [DiagramAut.universalEquiv_finiteStageMap, scalarQuadraticAut_stageEquiv_apply,
    map_smul]

/-- The scalar family of the unit element is the identity diagram automorphism. -/
@[simp]
theorem scalarQuadraticAut_one : scalarQuadraticAut R C S 1 = 1 := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    intro x
    simp
  · apply LinearEquiv.ext
    intro x
    simp

/-- Multiplication of units agrees with composition of the scalar diagram families. -/
theorem scalarQuadraticAut_mul (a b : Rˣ) :
    scalarQuadraticAut R C S (a * b) = scalarQuadraticAut R C S a *
      scalarQuadraticAut R C S b := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    intro x
    simp [smul_smul, mul_comm]
  · apply LinearEquiv.ext
    intro x
    simp [smul_smul, mul_comm]

/-- Units embed as uniform scalar families in the actual marked quadratic diagram group.
Blueprint: S03 (`thm:s03`). -/
def scalarQuadraticAction : Rˣ →* DiagramAut R C S where
  toFun := scalarQuadraticAut R C S
  map_one' := scalarQuadraticAut_one R C S
  map_mul' := scalarQuadraticAut_mul R C S

@[simp]
theorem scalarQuadraticAction_apply (a : Rˣ) :
    scalarQuadraticAction R C S a = scalarQuadraticAut R C S a := rfl

/-- Inverting a scalar diagram family inverts its coefficient unit. -/
@[simp]
theorem scalarQuadraticAut_inv (a : Rˣ) :
    scalarQuadraticAut R C S a⁻¹ = (scalarQuadraticAut R C S a)⁻¹ :=
  (scalarQuadraticAction R C S).map_inv a

/-- The inverse universal family acts by the inverse coefficient unit. This pointwise
formula also keeps both inverse-cancellation forms available to `simp`. -/
@[simp]
theorem scalarQuadraticAut_inv_universalEquiv_apply (a : Rˣ) (x : Hyperplane k n →₀ R) :
    (scalarQuadraticAut R C S a)⁻¹.universalEquiv x = (↑a⁻¹ : R) • x := by
  rw [← scalarQuadraticAut_inv, scalarQuadraticAut_universalEquiv_apply]

/-- The common two-generator target detects the scalar unit over every coefficient ring. -/
theorem scalarQuadraticAction_injective : Function.Injective (scalarQuadraticAction R C S) := by
  intro a b hab
  apply Units.ext
  have h := congrArg (fun g : DiagramAut R C S ↦
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0) hab
  simpa using h

/-- Every stage and common-target map is linear, so uniform scalars commute with every
quadratic diagram automorphism. -/
theorem scalarQuadraticAut_commute (a : Rˣ) (g : DiagramAut R C S) :
    Commute (scalarQuadraticAut R C S a) g := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    intro x
    simp
  · apply LinearEquiv.ext
    intro x
    simp

namespace DiagramAut

/-- The actual subgroup of uniform scalar families, defined as the scalar homomorphism range.
Blueprint: S03 (`thm:s03`). -/
def scalarSubgroup : Subgroup (DiagramAut R C S) := (scalarQuadraticAction R C S).range

/-- Scalar families form a central subgroup, with no reconstruction hypotheses. -/
theorem scalarSubgroup_le_center : scalarSubgroup R C S ≤ Subgroup.center (DiagramAut R C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarQuadraticAut_commute R C S a g).eq.symm

end DiagramAut

end OrlikSolomon.HyperplaneGT
