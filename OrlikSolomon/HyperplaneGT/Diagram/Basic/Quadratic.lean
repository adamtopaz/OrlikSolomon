/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.MarkingMaps
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Automorphisms of the marked quadratic diagram

The automorphism group is the subgroup of the product of the finite-stage linear
automorphism groups and one common two-generator automorphism group. Its elements preserve
the whole explicit quadratic relation spans by equality and commute with every inclusion and
tagged marking map. Inverse naturality follows from the same forward squares.

Blueprint: A03 (`def:a03`). No arithmetic reconstruction conclusion is stored as data.
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Module

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The ambient product of stage automorphisms and the one common target automorphism.
This is a transparent product synonym so the existing product group instance is inherited;
`instance_reducible` does not expose it to that instance search. -/
@[reducible]
def QuadraticAutFamily :=
  (∀ 𝒜 : C.Stage, (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) ×
    ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R))

/-- The subgroup defining the marked quadratic diagram. The entire relation image is equal
to the original submodule; containment alone would not suffice for closure under inverse.
Blueprint: A03 (`def:a03`). -/
def quadraticDiagramAutSubgroup : Subgroup (QuadraticAutFamily R C) where
  carrier := {g | (∀ 𝒜 : C.Stage, (quadraticRelationSpan R 𝒜.val.val).map
      (exteriorPower.map 2 (g.1 𝒜).toLinearMap) = quadraticRelationSpan R 𝒜.val.val) ∧
    (∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g.1 ℬ).toLinearMap.comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
        (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp (g.1 𝒜).toLinearMap) ∧
    ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g.1 𝒜).toLinearMap.comp (w.basisMap R hw) =
        (w.basisMap R hw).comp g.2.toLinearMap}
  one_mem' := by
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ h ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (quadraticRelationSpan R 𝒜.val.val).map
        (exteriorPower.map 2 LinearMap.id) = _
      simp
    · rfl
    · rfl
  mul_mem' := by
    rintro g h ⟨hgQ, hgi, hgm⟩ ⟨hhQ, hhi, hhm⟩
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (quadraticRelationSpan R 𝒜.val.val).map
        (exteriorPower.map 2 ((g.1 𝒜).toLinearMap.comp (h.1 𝒜).toLinearMap)) = _
      rw [exteriorPower.map_comp, Submodule.map_comp, hhQ, hgQ]
    · change ((g.1 ℬ).toLinearMap.comp (h.1 ℬ).toLinearMap).comp
          (Finsupp.lmapDomain R R (Arrangement.inclusion hi)) =
        (Finsupp.lmapDomain R R (Arrangement.inclusion hi)).comp
          ((g.1 𝒜).toLinearMap.comp (h.1 𝒜).toLinearMap)
      rw [LinearMap.comp_assoc, hhi, ← LinearMap.comp_assoc, hgi, LinearMap.comp_assoc]
    · change ((g.1 𝒜).toLinearMap.comp (h.1 𝒜).toLinearMap).comp (w.basisMap R hw) =
        (w.basisMap R hw).comp (g.2.toLinearMap.comp h.2.toLinearMap)
      rw [LinearMap.comp_assoc, hhm, ← LinearMap.comp_assoc, hgm, LinearMap.comp_assoc]
  inv_mem' := by
    rintro g ⟨hgQ, hgi, hgm⟩
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (quadraticRelationSpan R 𝒜.val.val).map
        (exteriorPower.map 2 (g.1 𝒜).symm.toLinearMap) = _
      calc
        _ = ((quadraticRelationSpan R 𝒜.val.val).map
            (exteriorPower.map 2 (g.1 𝒜).toLinearMap)).map
              (exteriorPower.map 2 (g.1 𝒜).symm.toLinearMap) := by rw [hgQ]
        _ = _ := by rw [← Submodule.map_comp, ← exteriorPower.map_comp,
          LinearEquiv.symm_comp, exteriorPower.map_id, Submodule.map_id]
    · apply LinearMap.ext
      intro x
      change (g.1 ℬ).symm (Finsupp.lmapDomain R R (Arrangement.inclusion hi) x) =
        Finsupp.lmapDomain R R (Arrangement.inclusion hi) ((g.1 𝒜).symm x)
      apply (g.1 ℬ).injective
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply] using
        (DFunLike.congr_fun (hgi 𝒜 ℬ hi) ((g.1 𝒜).symm x)).symm
    · apply LinearMap.ext
      intro x
      change (g.1 𝒜).symm (w.basisMap R hw x) = w.basisMap R hw (g.2.symm x)
      apply (g.1 𝒜).injective
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply] using
        (DFunLike.congr_fun (hgm 𝒜 w hw) (g.2.symm x)).symm

/-- Automorphisms of the explicit marked quadratic diagram. There is one common target
component for every marking, independently of the chosen stage. This transparent subgroup
subtype synonym inherits the existing group operations without new transport instances;
the product carrier documents why `instance_reducible` is insufficient for these wrappers.
Blueprint: A03 (`def:a03`). -/
@[reducible]
def DiagramAut := ↥(quadraticDiagramAutSubgroup R C S)

namespace DiagramAut

variable {R C S}

/-- The linear equivalence at a finite stage of a quadratic diagram automorphism. -/
def stageEquiv (g : DiagramAut R C S) (𝒜 : C.Stage) :
    (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) := g.val.1 𝒜

/-- The one linear equivalence at the common two-generator target. -/
def targetEquiv (g : DiagramAut R C S) : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R) := g.val.2

/-- Every stage equivalence preserves the whole quadratic relation span by image equality. -/
theorem map_quadraticRelationSpan (g : DiagramAut R C S) (𝒜 : C.Stage) :
    (quadraticRelationSpan R 𝒜.val.val).map
      (exteriorPower.map 2 (g.stageEquiv 𝒜).toLinearMap) =
        quadraticRelationSpan R 𝒜.val.val := g.property.1 𝒜

/-- Stage equivalences commute with each arrangement inclusion. -/
theorem inclusion_naturality (g : DiagramAut R C S) {𝒜 ℬ : C.Stage} (h : 𝒜 ≤ ℬ) :
    (g.stageEquiv ℬ).toLinearMap.comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
      (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp (g.stageEquiv 𝒜).toLinearMap :=
  g.property.2.1 𝒜 ℬ h

/-- Every tagged marking square uses the same target equivalence. -/
theorem marking_naturality (g : DiagramAut R C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    (g.stageEquiv 𝒜).toLinearMap.comp (w.basisMap R hw) =
      (w.basisMap R hw).comp g.targetEquiv.toLinearMap := g.property.2.2 𝒜 w hw

/-- Package a family satisfying precisely relation-image equality and the specified arrow
squares. No reconstruction or arbitrary-projection condition is required. -/
def ofEquivs (g : ∀ 𝒜 : C.Stage, (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R))
    (gT : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R))
    (hQ : ∀ 𝒜, (quadraticRelationSpan R 𝒜.val.val).map
      (exteriorPower.map 2 (g 𝒜).toLinearMap) = quadraticRelationSpan R 𝒜.val.val)
    (hi : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g ℬ).toLinearMap.comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
        (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp (g 𝒜).toLinearMap)
    (hm : ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g 𝒜).toLinearMap.comp (w.basisMap R hw) = (w.basisMap R hw).comp gT.toLinearMap) :
    DiagramAut R C S := ⟨(g, gT), hQ, hi, hm⟩

@[simp]
theorem stageEquiv_ofEquivs (g gT hQ hi hm) (𝒜 : C.Stage) :
    (ofEquivs (R := R) (C := C) (S := S) g gT hQ hi hm).stageEquiv 𝒜 = g 𝒜 := rfl

@[simp]
theorem targetEquiv_ofEquivs (g gT hQ hi hm) :
    (ofEquivs (R := R) (C := C) (S := S) g gT hQ hi hm).targetEquiv = gT := rfl

/-- A quadratic diagram automorphism is determined by its stage and common target maps. -/
@[ext]
theorem ext {g h : DiagramAut R C S} (hstage : ∀ 𝒜, g.stageEquiv 𝒜 = h.stageEquiv 𝒜)
    (htarget : g.targetEquiv = h.targetEquiv) : g = h := by
  apply Subtype.ext
  exact Prod.ext (funext hstage) htarget

@[simp]
theorem stageEquiv_one (𝒜 : C.Stage) :
    (1 : DiagramAut R C S).stageEquiv 𝒜 = LinearEquiv.refl R _ := rfl

@[simp]
theorem targetEquiv_one :
    (1 : DiagramAut R C S).targetEquiv = LinearEquiv.refl R _ := rfl

@[simp]
theorem stageEquiv_mul (g h : DiagramAut R C S) (𝒜 : C.Stage) :
    (g * h).stageEquiv 𝒜 = g.stageEquiv 𝒜 * h.stageEquiv 𝒜 := rfl

@[simp]
theorem targetEquiv_mul (g h : DiagramAut R C S) :
    (g * h).targetEquiv = g.targetEquiv * h.targetEquiv := rfl

@[simp]
theorem stageEquiv_inv (g : DiagramAut R C S) (𝒜 : C.Stage) :
    g⁻¹.stageEquiv 𝒜 = (g.stageEquiv 𝒜).symm := rfl

@[simp]
theorem targetEquiv_inv (g : DiagramAut R C S) :
    g⁻¹.targetEquiv = g.targetEquiv.symm := rfl

end DiagramAut

end OrlikSolomon.HyperplaneGT
