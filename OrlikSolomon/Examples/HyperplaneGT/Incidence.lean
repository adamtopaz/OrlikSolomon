/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Markings
public import OrlikSolomon.Examples.HyperplaneGT.Dual

/-!
# Recovered inertia, projective incidence and fixed-marking consumers

The actual diagram APIs support independent field/coefficient universes, coordinate-delta
and primal-generator rewrites, both label/projective inverse cancellations and every point
of the prescribed frame. A non-involutive scalar-two diagram recovers dual unit three over
`ℤ/5`. A nontrivial scalar-three diagram over the nonfield local ring `ℤ/4` fixes its marked
fibers and acts on nonzero nilpotent coefficients. Actual zero marking fibers are dependent
over `𝔽₂`, while their one fibers have empty intersection, excluding a uniform exchange.
Pure dimension-zero extension and zero-coefficient marking consumers retain their weaker
hypotheses without extending local reconstruction to those excluded cases.

Blueprint: regression consumers for I01–I04 (`prop:i01`, `lem:i02`, `lem:i03`, `lem:i04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.IncidenceExamples

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  {R : Type w} [CommRing R] [IsLocalRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The same-label primal and dual formulas cancel the opposite units under actual evaluation.
The three universes are independent and no field structure on the coefficients is used. -/
theorem generator_delta_evaluation (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    DiagramAut.dualAction g (Finsupp.lapply H)
      (g.universalEquiv (Finsupp.single H 1)) = 1 := by
  rw [g.universalEquiv_single hS hn H, g.dualAction_delta hS hn H]
  simp

/-- Both ordinary equivalence and inverse-family label cancellations simplify. -/
theorem label_inverse_cancellation (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    (g.hyperplanePerm hS hn).symm (g.hyperplanePerm hS hn H) = H ∧
      g.hyperplanePerm hS hn ((g.hyperplanePerm hS hn).symm H) = H ∧
      (g⁻¹).hyperplanePerm hS hn (g.hyperplanePerm hS hn H) = H ∧
      g.hyperplanePerm hS hn ((g⁻¹).hyperplanePerm hS hn H) = H := by simp

/-- Both ordinary equivalence and inverse-family projective cancellations simplify. -/
theorem projective_inverse_cancellation (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (p : Projectivization k (Fin (n + 1) → k)) :
    (g.projectivePerm hS hn).symm (g.projectivePerm hS hn p) = p ∧
      g.projectivePerm hS hn ((g.projectivePerm hS hn).symm p) = p ∧
      (g⁻¹).projectivePerm hS hn (g.projectivePerm hS hn p) = p ∧
      g.projectivePerm hS hn ((g⁻¹).projectivePerm hS hn p) = p := by simp

/-- Label and projective composition have the same covariant order. -/
theorem composition_order (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) (p : Projectivization k (Fin (n + 1) → k)) :
    (g * h).hyperplanePerm hS hn H = g.hyperplanePerm hS hn (h.hyperplanePerm hS hn H) ∧
      (g * h).projectivePerm hS hn p = g.projectivePerm hS hn (h.projectivePerm hS hn p) := by
  simp

/-- The actual trace kernel is transported through two successive universal actions in
both directions, without substituting an abstract relation space. -/
theorem nested_trace_kernel (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) (x : Hyperplane k n →₀ R) :
    g.universalEquiv (h.universalEquiv x) ∈
        traceKernel R (g.hyperplanePerm hS hn (h.hyperplanePerm hS hn H)) ↔
      x ∈ traceKernel R H := by simp

/-- Every basis point and every ordered difference point is fixed, with no omitted
initial-coordinate or reversed-order frame cases. -/
theorem entire_fixed_frame (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (∀ i : Fin (n + 1), g.projectivePerm hS hn (projectiveBasisPoint k i) =
      projectiveBasisPoint k i) ∧
      ∀ (i j : Fin (n + 1)) (hij : i ≠ j),
        g.projectivePerm hS hn (projectiveDifferencePoint k i j hij) =
          projectiveDifferencePoint k i j hij := by
  constructor <;> intros <;> simp

/-- The actual primal marked generator stays on its individually fixed zero fiber, with
its proved inverse-dual-unit scalar. -/
theorem marked_generator (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (w : Marking S n) :
    g.universalEquiv (Finsupp.single (w.fiber (k := k) 0) 1) =
      (((g.hyperplaneUnit hS hn (w.fiber 0))⁻¹ : Rˣ) : R) •
        Finsupp.single (w.fiber 0) 1 := by
  rw [g.universalEquiv_single hS hn]
  simp

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- An existing scalar-two marked diagram has identity recovered label permutation and
DUAL unit three, rather than two, over `ℤ/5`. -/
theorem scalar_two_recovered (C : CofinalSystem k₀ k n) (S : Set k₀)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) :
    (DualExamples.scalarTwoDiagram C S).hyperplanePerm hS hn H = H ∧
      (DualExamples.scalarTwoDiagram C S).hyperplaneUnit hS hn H =
        DualExamples.scalarTwoUnit⁻¹ := by
  let g := DualExamples.scalarTwoDiagram C S
  have hδ : DiagramAut.dualAction g (Finsupp.lapply H) =
      ((DualExamples.scalarTwoUnit⁻¹ : (ZMod 5)ˣ) : ZMod 5) • Finsupp.lapply H := by
    apply LinearMap.ext
    intro x
    rw [DiagramAut.dualAction_apply]
    have hinv : g.universalEquiv.symm x = (3 : ZMod 5) • x := by
      apply g.universalEquiv.injective
      rw [LinearEquiv.apply_symm_apply, DualExamples.scalarTwoDiagram_universal_apply]
      rw [smul_smul, show (2 : ZMod 5) * 3 = 1 from by decide, one_smul]
    rw [hinv]
    simp [DualExamples.scalarTwoUnit]
  exact (unit_smul_lapply_eq_iff _ _ _ _).mp ((g.dualAction_delta hS hn H).symm.trans hδ)

/-- A concrete geometric label and nonempty marking system distinguish actual primal value
two from dual value three by the recovered I01 formulas. -/
theorem binary_scalar_two_values :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let g := DualExamples.scalarTwoDiagram C ({0, 1} : Set (ZMod 2))
    let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
    (g.universalEquiv (Finsupp.single H 1)) H = 2 ∧
      DiagramAut.dualAction g (Finsupp.lapply H) (Finsupp.single H 1) = 3 ∧
      (3 : ZMod 5) ≠ 2 := by
  dsimp only
  obtain ⟨hp, hu⟩ := scalar_two_recovered
    (fullCofinalSystem (ZMod 2) (ZMod 2) 2) ({0, 1} : Set (ZMod 2)) (by simp) (by decide)
    (coordinateHyperplane (0 : Fin 2) (0 : ZMod 2))
  rw [DiagramAut.universalEquiv_single _ (by simp) (by decide),
    DiagramAut.dualAction_delta _ (by simp) (by decide), hp, hu]
  simp [DualExamples.scalarTwoUnit, show (3 : ZMod 5) ≠ 2 from by decide]

/-- The unit three is its own inverse in the nonfield local ring `ℤ/4`. -/
def scalarThreeUnit : (ZMod 4)ˣ := ⟨3, 3, by decide, by decide⟩

/-- Scalar three acts as the identity on every exterior square over `ℤ/4`. -/
theorem exterior_scalar_three (M : Type*) [AddCommGroup M] [Module (ZMod 4) M] :
    exteriorPower.map 2 (LinearEquiv.smulOfUnit (M := M) scalarThreeUnit).toLinearMap =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.id_apply]
  change exteriorPower.ιMulti (ZMod 4) 2 (fun i ↦ (3 : ZMod 4) • v i) =
    exteriorPower.ιMulti (ZMod 4) 2 v
  rw [AlternatingMap.map_smul_univ, show (∏ _ : Fin 2, (3 : ZMod 4)) = 1 from by decide,
    one_smul]

/-- An actual marked diagram over `ℤ/4` multiplies every finite stage and its common target
by three. Its exterior-square map is the identity, so it preserves the whole actual Q. -/
def scalarThreeDiagram (C : CofinalSystem k₀ k n) (S : Set k₀) : DiagramAut (ZMod 4) C S := by
  refine DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.smulOfUnit scalarThreeUnit)
    (LinearEquiv.smulOfUnit scalarThreeUnit) (fun A ↦ ?_) ?_ ?_
  · rw [exterior_scalar_three, Submodule.map_id]
  · intro A B h
    apply LinearMap.ext
    intro x
    change (3 : ZMod 4) • Finsupp.lmapDomain (ZMod 4) (ZMod 4) (Arrangement.inclusion h) x =
      Finsupp.lmapDomain (ZMod 4) (ZMod 4) (Arrangement.inclusion h) ((3 : ZMod 4) • x)
    exact (map_smul _ _ _).symm
  · intro A w hw
    apply LinearMap.ext
    intro x
    change (3 : ZMod 4) • w.basisMap (ZMod 4) hw x =
      w.basisMap (ZMod 4) hw ((3 : ZMod 4) • x)
    exact (map_smul _ _ _).symm

/-- The actual universal action of the nonfield diagram is scalar three on every vector. -/
theorem scalarThreeDiagram_universal_apply (C : CofinalSystem k₀ k n) (S : Set k₀)
    (x : Hyperplane k n →₀ ZMod 4) :
    (scalarThreeDiagram C S).universalEquiv x = (3 : ZMod 4) • x := by
  obtain ⟨A, a, rfl⟩ := C.exists_stage_vector (ZMod 4) x
  rw [DiagramAut.universalEquiv_finiteStageMap]
  exact map_smul (finiteStageMap (ZMod 4) A.val.val) 3 a

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- Over a nonfield local ring the actual difference marking's two fibers are fixed, the
common-target map is nontrivial, and the nonzero nilpotent coefficient two is still detected.
-/
theorem mod_four_fixed_marking :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let g := scalarThreeDiagram C ({0} : Set (ZMod 2))
    let w : Marking ({0} : Set (ZMod 2)) 2 := .difference 0 1 (by decide)
    g.hyperplanePerm (by simp) (by decide) (w.fiber (k := ZMod 2) 0) = w.fiber 0 ∧
      g.hyperplanePerm (by simp) (by decide) (w.fiber (k := ZMod 2) 1) = w.fiber 1 ∧
      (g.universalEquiv (Finsupp.single (w.fiber 0) 2)) (w.fiber 0) = 2 ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 := by
  dsimp only
  refine ⟨by simp, by simp, ?_, ?_, by decide, by decide⟩
  · rw [scalarThreeDiagram_universal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
    decide
  · change ((3 : ZMod 4) • Finsupp.single (0 : Fin 2) 1) 0 = 3
    simp

/-- Actual zero marking fibers form a guarded dependent triple over `𝔽₂`; the matching
one fibers have empty triple intersection, despite the characteristic. -/
theorem binary_marking_swap_obstruction :
    let wx : Marking ({0} : Set (ZMod 2)) 2 := .coordinate 0 ⟨0, by simp⟩
    let wy : Marking ({0} : Set (ZMod 2)) 2 := .coordinate 1 ⟨0, by simp⟩
    let wd : Marking ({0} : Set (ZMod 2)) 2 := .difference 0 1 (by decide)
    DependentTriple (wx.fiber (k := ZMod 2) 0) (wy.fiber 0) (wd.fiber 0) ∧
      (wx.fiber (k := ZMod 2) 1).val ⊓ (wy.fiber 1).val ⊓ (wd.fiber 1).val = ⊥ := by
  dsimp only
  refine ⟨dependentTriple_marking_coordinate_zero (by simp) 0 1 (by decide), ?_⟩
  apply le_bot_iff.mp
  intro x hx
  have hi : x 0 = 1 := by simpa using hx.1.1
  have hj : x 1 = 1 := by simpa using hx.1.2
  have hd : x 0 - x 1 = 1 := by simpa using hx.2
  simp [hi, hj] at hd

/-- A pure extension in dimension zero remains defined and acts identically. This does
not invoke the local reconstruction theorem with an invalid dimension hypothesis. -/
theorem dimension_zero_extension (k : Type u) [Field k]
    (π : Equiv.Perm (Hyperplane k 0)) (p : Projectivization k (Fin 1 → k)) :
    projectiveExtension π p = p := by
  let := CoordinateExamples.dimension_zero (k := k)
  have hπ : π = 1 := Subsingleton.elim _ _
  simp [hπ]

/-- The pure common-target marking formula remains available with zero coefficients and
without any local-ring, dimension or generating-set reconstruction hypotheses. -/
theorem zero_coeff_marking_square {k : Type u} {k₀ : Type v} [Field k] [Field k₀]
    [Algebra k₀ k] {n : ℕ} {C : CofinalSystem k₀ k n} {S : Set k₀}
    (g : DiagramAut (ZMod 1) C S) (w : Marking S n) (a : Fin 2) :
    g.universalEquiv (Finsupp.single (w.fiber (k := k) (a.val : k₀)) 1) = 0 := by
  have h₀ : (g.targetEquiv (Finsupp.single a 1)) 0 = 0 := Subsingleton.elim _ _
  have h₁ : (g.targetEquiv (Finsupp.single a 1)) 1 = 0 := Subsingleton.elim _ _
  rw [g.universalEquiv_marking_single, h₀, h₁, zero_smul, zero_smul, add_zero]

end OrlikSolomon.HyperplaneGT.IncidenceExamples
