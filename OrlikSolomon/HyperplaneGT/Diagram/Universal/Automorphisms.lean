/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Quadratic
public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Lift
public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Relations

/-!
# Universal actions of the actual quadratic diagram automorphisms

The existing `DiagramAut` family glues to a linear equivalence of the literal free module
on all hyperplanes. Compatibility and the common-stage universal property make the gluing
independent of every stage choice. The inverse family gives the inverse universal map.

This action preserves the global quadratic relation span and every finite-stage image by
equality. The marked maps remain equivariant from their one common target. The universal
equivalence together with that target equivalence determines the original family; no
converse assertion about arbitrary relation-preserving universal maps is made.

Blueprint: U02 (`lem:u02`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT.DiagramAut

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}
variable {R : Type w} [CommRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The stagewise linear action glued to the universal free hyperplane module. -/
def universalMap (g : DiagramAut R C S) : (Hyperplane k n →₀ R) →ₗ[R] (Hyperplane k n →₀ R) :=
  C.universalLift R (fun 𝒜 ↦ (finiteStageMap R 𝒜.val.val).comp (g.stageEquiv 𝒜).toLinearMap)
    (by
      intro 𝒜 ℬ h
      rw [LinearMap.comp_assoc, g.inclusion_naturality h, ← LinearMap.comp_assoc,
        finiteStageMap_comp_inclusion])

/-- The universal map restricts to the prescribed finite-stage component. -/
theorem universalMap_comp_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage) :
    g.universalMap.comp (finiteStageMap R 𝒜.val.val) =
      (finiteStageMap R 𝒜.val.val).comp (g.stageEquiv 𝒜).toLinearMap :=
  C.universalLift_comp_finiteStageMap R _ _ 𝒜

/-- Evaluating a universal action on a stage vector gives its stagewise action. -/
@[simp]
theorem universalMap_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage)
    (a : 𝒜.val.val →₀ R) :
    g.universalMap (finiteStageMap R 𝒜.val.val a) =
      finiteStageMap R 𝒜.val.val (g.stageEquiv 𝒜 a) :=
  DFunLike.congr_fun (g.universalMap_comp_finiteStageMap 𝒜) a

/-- Gluing the inverse family gives a left inverse to the glued linear map. -/
theorem universalMap_inv_comp (g : DiagramAut R C S) :
    g⁻¹.universalMap.comp g.universalMap = LinearMap.id := by
  apply C.linearMap_ext R
  intro 𝒜
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, universalMap_finiteStageMap, stageEquiv_inv,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

/-- Gluing the inverse family also gives a right inverse to the glued linear map. -/
theorem universalMap_comp_inv (g : DiagramAut R C S) :
    g.universalMap.comp g⁻¹.universalMap = LinearMap.id := by
  apply C.linearMap_ext R
  intro 𝒜
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, universalMap_finiteStageMap, stageEquiv_inv,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]

/-- A quadratic diagram automorphism induces a linear equivalence of the universal module.
Its inverse is obtained from the inverse family, without any choice of a preferred stage.

Blueprint: U02 (`lem:u02`). -/
def universalEquiv (g : DiagramAut R C S) :
    (Hyperplane k n →₀ R) ≃ₗ[R] (Hyperplane k n →₀ R) :=
  { g.universalMap with
    invFun := g⁻¹.universalMap
    left_inv := fun x ↦ DFunLike.congr_fun (universalMap_inv_comp g) x
    right_inv := fun x ↦ DFunLike.congr_fun (universalMap_comp_inv g) x }

/-- The universal equivalence has exactly the glued linear map as its underlying map. -/
@[simp]
theorem universalEquiv_toLinearMap (g : DiagramAut R C S) :
    g.universalEquiv.toLinearMap = g.universalMap := rfl

/-- The universal equivalence restricts to the prescribed action at every selected stage. -/
theorem universalEquiv_comp_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage) :
    g.universalEquiv.toLinearMap.comp (finiteStageMap R 𝒜.val.val) =
      (finiteStageMap R 𝒜.val.val).comp (g.stageEquiv 𝒜).toLinearMap :=
  g.universalMap_comp_finiteStageMap 𝒜

/-- The universal equivalence agrees pointwise with each finite-stage component. -/
@[simp]
theorem universalEquiv_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage)
    (a : 𝒜.val.val →₀ R) :
    g.universalEquiv (finiteStageMap R 𝒜.val.val a) =
      finiteStageMap R 𝒜.val.val (g.stageEquiv 𝒜 a) :=
  g.universalMap_finiteStageMap 𝒜 a

/-- Inverting the diagram family inverts the induced universal equivalence. -/
@[simp]
theorem universalEquiv_symm (g : DiagramAut R C S) :
    g.universalEquiv.symm = g⁻¹.universalEquiv := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- The identity family induces the identity universal equivalence. -/
@[simp]
theorem universalEquiv_one : (1 : DiagramAut R C S).universalEquiv = 1 := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨𝒜, a, rfl⟩ := C.exists_stage_vector R x
  rw [universalEquiv_finiteStageMap, stageEquiv_one]
  rfl

/-- Diagram multiplication is carried to multiplication of universal equivalences. -/
theorem universalEquiv_mul (g h : DiagramAut R C S) :
    (g * h).universalEquiv = g.universalEquiv * h.universalEquiv := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨𝒜, a, rfl⟩ := C.exists_stage_vector R x
  simp only [mul_apply_eq_comp, universalEquiv_finiteStageMap, stageEquiv_mul]

/-- The induced universal action is a group homomorphism.

Blueprint: the group law in U02 (`lem:u02`). -/
def universalAction : DiagramAut R C S →*
    ((Hyperplane k n →₀ R) ≃ₗ[R] (Hyperplane k n →₀ R)) where
  toFun := universalEquiv
  map_one' := universalEquiv_one
  map_mul' := universalEquiv_mul

@[simp]
theorem universalAction_apply (g : DiagramAut R C S) : universalAction g = g.universalEquiv := rfl

/-- The exterior-square universal action intertwines finite-stage exterior-square actions. -/
theorem exteriorPower_universalEquiv_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage)
    (a : ⋀[R]^2 (𝒜.val.val →₀ R)) :
    exteriorPower.map 2 g.universalEquiv.toLinearMap
        (exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) a) =
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val)
        (exteriorPower.map 2 (g.stageEquiv 𝒜).toLinearMap a) := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, universalEquiv_comp_finiteStageMap,
    exteriorPower.map_comp, LinearMap.comp_apply]

private theorem universalEquiv_mem_relations (g : DiagramAut R C S)
    {q : ⋀[R]^2 (Hyperplane k n →₀ R)} (hq : q ∈ universalQuadraticRelationSpan R) :
    exteriorPower.map 2 g.universalEquiv.toLinearMap q ∈ universalQuadraticRelationSpan R := by
  obtain ⟨𝒜, a, ha, rfl⟩ := (C.mem_universalQuadraticRelationSpan_iff R q).mp hq
  rw [exteriorPower_universalEquiv_finiteStageMap]
  apply map_quadraticRelationSpan_finiteStageMap_le R 𝒜.val.val
  refine ⟨_, ?_, rfl⟩
  rw [← g.map_quadraticRelationSpan 𝒜]
  exact ⟨a, ha, rfl⟩

/-- The universal action preserves the entire global quadratic relation span by equality.
The reverse containment uses the inverse diagram family.

Blueprint: U02 (`lem:u02`). -/
theorem map_universalQuadraticRelationSpan (g : DiagramAut R C S) :
    (universalQuadraticRelationSpan R).map (exteriorPower.map 2 g.universalEquiv.toLinearMap) =
      universalQuadraticRelationSpan R := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact universalEquiv_mem_relations g hq
  · intro q hq
    refine ⟨exteriorPower.map 2 g.universalEquiv.symm.toLinearMap q, ?_, ?_⟩
    · rw [universalEquiv_symm]
      exact universalEquiv_mem_relations g⁻¹ hq
    · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearEquiv.comp_symm,
        exteriorPower.map_id, LinearMap.id_apply]

/-- Each selected finite-stage submodule is preserved by the universal action in both
directions, not merely mapped into some larger stage. -/
theorem map_range_finiteStageMap (g : DiagramAut R C S) (𝒜 : C.Stage) :
    (LinearMap.range (finiteStageMap R 𝒜.val.val)).map g.universalEquiv.toLinearMap =
      LinearMap.range (finiteStageMap R 𝒜.val.val) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨g.stageEquiv 𝒜 a, g.universalEquiv_finiteStageMap 𝒜 a |>.symm⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨finiteStageMap R 𝒜.val.val ((g.stageEquiv 𝒜).symm a), ⟨_, rfl⟩, ?_⟩
    simp only [LinearEquiv.toLinearMap_eq_ofClass, LinearMap.coe_ofClass,
      universalEquiv_finiteStageMap, LinearEquiv.apply_symm_apply]

/-- Universal marking maps remain equivariant from the one retained common target. -/
theorem universalEquiv_marking (g : DiagramAut R C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    g.universalEquiv.toLinearMap.comp ((finiteStageMap R 𝒜.val.val).comp (w.basisMap R hw)) =
      ((finiteStageMap R 𝒜.val.val).comp (w.basisMap R hw)).comp g.targetEquiv.toLinearMap := by
  rw [← LinearMap.comp_assoc, universalEquiv_comp_finiteStageMap, LinearMap.comp_assoc,
    g.marking_naturality, ← LinearMap.comp_assoc]

/-- The universal map and the one common target component jointly determine the diagram
family. The target hypothesis is retained, in particular when dimension zero has no markings.

Blueprint: U02 (`lem:u02`). -/
theorem ext_of_universalEquiv {g h : DiagramAut R C S}
    (hM : g.universalEquiv = h.universalEquiv) (hT : g.targetEquiv = h.targetEquiv) : g = h := by
  apply DiagramAut.ext
  · intro 𝒜
    apply LinearEquiv.ext
    intro a
    apply finiteStageMap_injective R 𝒜.val.val
    have he := congrArg (fun e : (Hyperplane k n →₀ R) ≃ₗ[R] (Hyperplane k n →₀ R) ↦
      e (finiteStageMap R 𝒜.val.val a)) hM
    simpa only [universalEquiv_finiteStageMap] using he
  · exact hT

end OrlikSolomon.HyperplaneGT.DiagramAut
