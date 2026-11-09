/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Field.ZMod
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Alternating
public import OrlikSolomon.HyperplaneGT.Diagram.Universal

/-!
# Universal module and diagram-action consumers

Finite supports and relation sums acquire common-stage representatives in any chosen
cofinal family. A compatible family recovers every linear map on the universal module,
with independent universes for the two fields, coefficients and target module. The APIs
also accept zero coefficients and dimension zero.

In dimension zero, a nontrivial swap at the common target can accompany identity stage
maps. Its universal map is identity, so the common target hypothesis in diagram-family
extensionality is essential. This tests the arithmetic diagram rather than replacing it
by an automorphism group of the universal relation span alone.

Blueprint: U01–U02 (`def:u01`, `lem:u01`, `lem:u02`).
-/

@[expose] public section

noncomputable section

universe u v w z

namespace OrlikSolomon.HyperplaneGT.UniversalExamples

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
variable (R : Type w) [CommRing R] {n : ℕ} (C : CofinalSystem k₀ k n)

/-- Two universal vectors can be represented simultaneously without union closure of stages.
-/
theorem common_vector_representatives (x y : Hyperplane k n →₀ R) :
    ∃ 𝒜 : C.Stage, ∃ a b : 𝒜.val.val →₀ R,
      finiteStageMap R 𝒜.val.val a = x ∧ finiteStageMap R 𝒜.val.val b = y := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_vectors R {x, y}
  obtain ⟨a, ha⟩ := h𝒜 x (by simp)
  obtain ⟨b, hb⟩ := h𝒜 y (by simp)
  exact ⟨𝒜, a, b, ha, hb⟩

/-- A sum of geometric relators has a witness in one actual finite-stage quadratic span. -/
theorem relation_sum (H K L P Q : Hyperplane k n) (hHK : Parallel H K)
    (hLPQ : DependentTriple L P Q) (r : R) :
    ∃ 𝒜 : C.Stage, ∃ a ∈ quadraticRelationSpan R 𝒜.val.val,
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) a =
        universalExteriorPair R H K + r • universalExteriorDifferencePair R L P Q := by
  apply (C.mem_universalQuadraticRelationSpan_iff R _).mp
  exact Submodule.add_mem _ (universalExteriorPair_mem R H K hHK)
    (Submodule.smul_mem _ r (universalExteriorDifferencePair_mem R L P Q hLPQ))

/-- The literal global difference wedge plugs directly into the existing determinant API. -/
theorem difference_determinant (H K L : Hyperplane k n)
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) :
    dualDeterminant φ ψ (universalExteriorDifferencePair R H K L) =
      (dualCoordinates φ H - dualCoordinates φ L) *
          (dualCoordinates ψ K - dualCoordinates ψ L) -
        (dualCoordinates φ K - dualCoordinates φ L) *
          (dualCoordinates ψ H - dualCoordinates ψ L) :=
  dualDeterminant_sub_single φ ψ H K L

/-- The finite-stage witness theorem requires no nonzero-coefficient hypothesis. -/
theorem zero_coefficient_relations (q : ⋀[ZMod 1]^2 (Hyperplane k n →₀ ZMod 1)) :
    q ∈ universalQuadraticRelationSpan (ZMod 1) ↔
      ∃ 𝒜 : C.Stage, ∃ a ∈ quadraticRelationSpan (ZMod 1) 𝒜.val.val,
        exteriorPower.map 2 (finiteStageMap (ZMod 1) 𝒜.val.val) a = q :=
  C.mem_universalQuadraticRelationSpan_iff (ZMod 1) q

/-- In dimension zero the literal universal hyperplane module is zero. -/
theorem dimension_zero_vector (x : Hyperplane k 0 →₀ R) : x = 0 := by
  ext H
  exact (not_isHyperplane_of_subsingleton H.val H.property).elim

variable {N : Type z} [AddCommMonoid N] [Module R N]

/-- Every linear map is recovered by gluing its finite-stage restrictions, with an independent
target-module universe. -/
theorem universalLift_restrict (l : (Hyperplane k n →₀ R) →ₗ[R] N) :
    ∃ hf, C.universalLift R (fun 𝒜 ↦ l.comp (finiteStageMap R 𝒜.val.val)) hf = l := by
  have hf : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (l.comp (finiteStageMap R ℬ.val.val)).comp
        (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
      l.comp (finiteStageMap R 𝒜.val.val) := by
    intro 𝒜 ℬ h
    rw [LinearMap.comp_assoc, finiteStageMap_comp_inclusion]
  refine ⟨hf, Eq.symm ((C.universalLift_unique R _ hf l).mp ?_)⟩
  intro 𝒜
  rfl

variable {R C} {S : Set k₀}

/-- The universal action is equivariant for a marking on every target vector. -/
theorem marking_equivariance (g : DiagramAut R C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) (x : Fin 2 →₀ R) :
    g.universalEquiv (finiteStageMap R 𝒜.val.val (w.basisMap R hw x)) =
      finiteStageMap R 𝒜.val.val (w.basisMap R hw (g.targetEquiv x)) :=
  DFunLike.congr_fun (g.universalEquiv_marking 𝒜 w hw) x

/-- The inverse family inverts the universal action pointwise. -/
theorem inverse_action (g : DiagramAut R C S) (x : Hyperplane k n →₀ R) :
    g⁻¹.universalEquiv (g.universalEquiv x) = x := by
  rw [← DiagramAut.universalEquiv_symm, LinearEquiv.symm_apply_apply]

variable (R) (C₀ : CofinalSystem k₀ k 0) (S)

/-- In dimension zero any common-target equivalence accompanies identity stage maps because
there are no markings. This is a fixture in the actual `DiagramAut` subgroup. -/
def targetOnly (t : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) : DiagramAut R C₀ S :=
  DiagramAut.ofEquivs (fun 𝒜 ↦ LinearEquiv.refl R (𝒜.val.val →₀ R)) t
    (by
      intro 𝒜
      change (quadraticRelationSpan R 𝒜.val.val).map (exteriorPower.map 2 LinearMap.id) = _
      rw [exteriorPower.map_id, Submodule.map_id])
    (by intros; rfl)
    (by intro 𝒜 w hw; exact False.elim (isEmptyElim w))

/-- The target-only family induces the identity on the universal module. -/
theorem targetOnly_universalEquiv (t : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) :
    (targetOnly R S C₀ t).universalEquiv = 1 := by
  apply LinearEquiv.ext
  intro x
  rw [dimension_zero_vector R x, map_zero, map_zero]

/-- The common target component is retained exactly. -/
@[simp]
theorem targetOnly_targetEquiv (t : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) :
    (targetOnly R S C₀ t).targetEquiv = t := rfl

/-- A nontrivial common-target component gives a nontrivial diagram family. -/
theorem targetOnly_ne_one (t : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) (ht : t ≠ 1) :
    targetOnly R S C₀ t ≠ 1 := by
  intro h
  apply ht
  have he := congrArg (fun g : DiagramAut R C₀ S ↦ g.targetEquiv) h
  rw [targetOnly_targetEquiv, DiagramAut.targetEquiv_one] at he
  exact he

/-- A concrete nontrivial swap of the two ordered target basis vectors over `ℤ`. -/
def swapTarget : (Fin 2 →₀ ℤ) ≃ₗ[ℤ] (Fin 2 →₀ ℤ) :=
  Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1)

/-- The swap is detected by its value on the zeroth target basis vector. -/
theorem swapTarget_ne_one : swapTarget ≠ 1 := by
  intro h
  have he := congrArg (fun e : (Fin 2 →₀ ℤ) ≃ₗ[ℤ] (Fin 2 →₀ ℤ) ↦
    e (Finsupp.single 0 1) 1) h
  norm_num [swapTarget, Finsupp.domLCongr_single] at he

/-- The universal map alone does not determine the original family: the common target must
be retained in U02's extensionality theorem. -/
theorem common_target_essential :
    ∃ g : DiagramAut ℤ C₀ S, g.universalEquiv = 1 ∧ g ≠ 1 :=
  ⟨targetOnly ℤ S C₀ swapTarget, targetOnly_universalEquiv ℤ S C₀ swapTarget,
    targetOnly_ne_one ℤ S C₀ swapTarget swapTarget_ne_one⟩

end OrlikSolomon.HyperplaneGT.UniversalExamples
