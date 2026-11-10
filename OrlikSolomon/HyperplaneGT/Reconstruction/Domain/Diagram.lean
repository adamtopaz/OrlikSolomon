/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Quadratic
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Relations

/-!
# Coefficient extension of the actual marked quadratic diagram

Extend every stage matrix and the one common-target matrix along the coefficient algebra
map. Both matrix inverses extend, and both explicit quadratic relation families remain in
the full relation span. The original inclusion and marking equations extend to the same
equations over the new coefficient ring. This defines a group homomorphism, faithful when
the coefficient map is injective.

Blueprint: the actual base-changed diagram in S05 (`thm:s05`). Pure extension uses arbitrary
commutative coefficients, including noninjective coefficient maps and zero rings.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

open Module

universe u v r s

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)
  (A : Type s) [CommRing A] [Algebra R A]

/-- Extending the literal marking matrix keeps its ordered zero and one labels. -/
@[simp]
theorem Marking.coefficientExtend_basisMap {𝒜 : Arrangement k (Fin n → k)}
    (w : Marking S n) (hw : w.Available 𝒜) :
    coefficientExtendLinearMap R A (w.basisMap R hw) = w.basisMap A hw :=
  coefficientExtendLinearMap_lmapDomain R A (w.fiberLabel hw)

namespace DiagramAut

/-- The extended stage and its extended inverse preserve the entire actual quadratic
relation span by image equality. -/
theorem coefficientExtend_map_quadraticRelationSpan (g : DiagramAut R C S)
    (B : C.Stage) :
    (quadraticRelationSpan A B.val.val).map
        (exteriorPower.map 2 (coefficientExtendLinearEquiv R A (g.stageEquiv B)).toLinearMap) =
      quadraticRelationSpan A B.val.val := by
  have hle (h : DiagramAut R C S) :
      (quadraticRelationSpan A B.val.val).map
          (exteriorPower.map 2 (coefficientExtendLinearMap R A (h.stageEquiv B).toLinearMap)) ≤
        quadraticRelationSpan A B.val.val :=
    coefficientExtendLinearMap_preserves_quadraticRelationSpan R A B.val.val
      (h.stageEquiv B).toLinearMap (h.map_quadraticRelationSpan B).le
  apply le_antisymm (hle g)
  intro y hy
  refine ⟨exteriorPower.map 2
    (coefficientExtendLinearMap R A (g.stageEquiv B).symm.toLinearMap) y, ?_, ?_⟩
  · exact hle g⁻¹ ⟨y, hy, rfl⟩
  · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
      ← coefficientExtendLinearMap_comp, LinearEquiv.comp_symm,
      coefficientExtendLinearMap_id, exteriorPower.map_id, LinearMap.id_apply]

/-- Extend the matrices of the original diagram, preserving its entire relation spans and
all actual inclusion/marking arrows with one common target. Blueprint: S05 (`thm:s05`). -/
def coefficientExtend : DiagramAut R C S →* DiagramAut A C S where
  toFun g := ofEquivs
    (fun B ↦ coefficientExtendLinearEquiv R A (g.stageEquiv B))
    (coefficientExtendLinearEquiv R A g.targetEquiv)
    (coefficientExtend_map_quadraticRelationSpan R C S A g)
    (by
      intro B D h
      have he := congrArg (coefficientExtendLinearMap R A) (g.inclusion_naturality h)
      simpa only [coefficientExtendLinearEquiv_toLinearMap,
        coefficientExtendLinearMap_comp, coefficientExtendLinearMap_lmapDomain]
        using he)
    (by
      intro B w hw
      have he := congrArg (coefficientExtendLinearMap R A) (g.marking_naturality B w hw)
      simpa only [coefficientExtendLinearEquiv_toLinearMap,
        coefficientExtendLinearMap_comp, Marking.coefficientExtend_basisMap]
        using he)
  map_one' := by
    apply DiagramAut.ext
    · intro B
      exact coefficientExtendLinearEquiv_refl R A
    · exact coefficientExtendLinearEquiv_refl R A
  map_mul' g h := by
    apply DiagramAut.ext
    · intro B
      exact coefficientExtendLinearEquiv_mul R A (g.stageEquiv B) (h.stageEquiv B)
    · exact coefficientExtendLinearEquiv_mul R A g.targetEquiv h.targetEquiv

/-- A coefficient-extended stage is exactly the extended original matrix. -/
@[simp]
theorem coefficientExtend_stageEquiv (g : DiagramAut R C S) (B : C.Stage) :
    (coefficientExtend R C S A g).stageEquiv B =
      coefficientExtendLinearEquiv R A (g.stageEquiv B) := rfl

/-- All extended markings share the extension of the original common target matrix. -/
@[simp]
theorem coefficientExtend_targetEquiv (g : DiagramAut R C S) :
    (coefficientExtend R C S A g).targetEquiv =
      coefficientExtendLinearEquiv R A g.targetEquiv := rfl

/-- Stagewise coefficient inclusion commutes with the actual extended diagram action on
every original vector, not only its basis vectors. -/
theorem coefficientExtend_stage_mapRange (g : DiagramAut R C S) (B : C.Stage)
    (x : B.val.val →₀ R) :
    (coefficientExtend R C S A g).stageEquiv B
        (Finsupp.mapRange.linearMap (Algebra.linearMap R A) x) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A) (g.stageEquiv B x) := by
  rw [coefficientExtend_stageEquiv]
  exact coefficientExtendLinearEquiv_mapRange R A (g.stageEquiv B) x

/-- Coefficient inclusion commutes with the SAME common-target map for every marking. -/
theorem coefficientExtend_target_mapRange (g : DiagramAut R C S) (x : Fin 2 →₀ R) :
    (coefficientExtend R C S A g).targetEquiv
        (Finsupp.mapRange.linearMap (Algebra.linearMap R A) x) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A) (g.targetEquiv x) := by
  rw [coefficientExtend_targetEquiv]
  exact coefficientExtendLinearEquiv_mapRange R A g.targetEquiv x

/-- The extended stage column is the coefficient image of the actual original column. -/
theorem coefficientExtend_stage_single (g : DiagramAut R C S) (B : C.Stage)
    (H : B.val.val) :
    (coefficientExtend R C S A g).stageEquiv B (Finsupp.single H 1) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A)
        (g.stageEquiv B (Finsupp.single H 1)) := by
  change coefficientExtendLinearMap R A (g.stageEquiv B).toLinearMap _ = _
  rw [coefficientExtendLinearMap_single, one_smul]
  rfl

/-- The extended common-target column is the coefficient image of the original column. -/
theorem coefficientExtend_target_single (g : DiagramAut R C S) (i : Fin 2) :
    (coefficientExtend R C S A g).targetEquiv (Finsupp.single i 1) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A)
        (g.targetEquiv (Finsupp.single i 1)) := by
  change coefficientExtendLinearMap R A g.targetEquiv.toLinearMap _ = _
  rw [coefficientExtendLinearMap_single, one_smul]
  rfl

/-- Faithfulness of an injective coefficient map descends through every original diagram
component, including the retained common target. -/
theorem coefficientExtend_injective (hRA : Function.Injective (algebraMap R A)) :
    Function.Injective (coefficientExtend R C S A) := by
  intro g h he
  apply DiagramAut.ext
  · intro B
    apply coefficientExtendLinearEquiv_injective R A hRA
    simpa only [coefficientExtend_stageEquiv] using
      congrArg (fun f : DiagramAut A C S ↦ f.stageEquiv B) he
  · apply coefficientExtendLinearEquiv_injective R A hRA
    simpa only [coefficientExtend_targetEquiv] using
      congrArg (fun f : DiagramAut A C S ↦ f.targetEquiv) he

end DiagramAut

end OrlikSolomon.HyperplaneGT
