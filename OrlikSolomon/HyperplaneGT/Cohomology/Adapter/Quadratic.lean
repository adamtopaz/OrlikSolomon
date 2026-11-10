/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.CupKernel

/-!
# Automorphisms of the actual degree-one and cup-kernel diagram

The ambient product consists of actual degree-one cohomology equivalences at all selected
stages and one equivalence at the common actual two-puncture target. Its subgroup preserves
the entire actual cup kernel and commutes with the actual scheme inclusion and marking
pullbacks. No normalized combinatorial carrier or new cohomology record is substituted.

Blueprint: the actual quadratic diagram in A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Module

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The ambient product of stage automorphisms and the one common target automorphism.
This is a transparent product synonym so the existing product group instance is inherited;
`instance_reducible` does not expose it to that instance search. -/
@[reducible]
def QuadraticAutFamily :=
  (∀ 𝒜 : C.Stage, (degreeOne T 𝒜.val.val) ≃ₗ[R] (degreeOne T 𝒜.val.val)) ×
    ((degreeOne T (twoPunctureArrangement k)) ≃ₗ[R] (degreeOne T (twoPunctureArrangement k)))

private theorem map_exteriorPower_symm {M : Type*} [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) (Q : Submodule R (⋀[R]^2 M))
    (hQ : Q.map (exteriorPower.map 2 e.toLinearMap) = Q) :
    Q.map (exteriorPower.map 2 e.symm.toLinearMap) = Q := by
  calc
    _ = (Q.map (exteriorPower.map 2 e.toLinearMap)).map
        (exteriorPower.map 2 e.symm.toLinearMap) := congrArg _ hQ.symm
    _ = _ := by rw [← Submodule.map_comp, ← exteriorPower.map_comp,
      LinearEquiv.symm_comp, exteriorPower.map_id, Submodule.map_id]

/-- The subgroup defining the actual cohomology diagram. The entire cup-kernel image is equal
to the original submodule; containment alone would not suffice for closure under inverse.
Blueprint: A04 (`thm:a04`). -/
def quadraticDiagramAutSubgroup : Subgroup (QuadraticAutFamily T C) where
  carrier := {g | (∀ 𝒜 : C.Stage, (LinearMap.ker (cupMap T 𝒜.val.val)).map
      (exteriorPower.map 2 (g.1 𝒜).toLinearMap) = LinearMap.ker (cupMap T 𝒜.val.val)) ∧
    (∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g.1 ℬ).toLinearMap.comp (componentPull T (D.complementInclusion h) 1) =
        (componentPull T (D.complementInclusion h) 1).comp (g.1 𝒜).toLinearMap) ∧
    ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g.1 𝒜).toLinearMap.comp (componentPull T (w.schemeMap D hw) 1) =
        (componentPull T (w.schemeMap D hw) 1).comp g.2.toLinearMap}
  one_mem' := by
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ h ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (LinearMap.ker (cupMap T 𝒜.val.val)).map
        (exteriorPower.map 2 LinearMap.id) = _
      simp
    · rfl
    · rfl
  mul_mem' := by
    rintro g h ⟨hgQ, hgi, hgm⟩ ⟨hhQ, hhi, hhm⟩
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (LinearMap.ker (cupMap T 𝒜.val.val)).map
        (exteriorPower.map 2 ((g.1 𝒜).toLinearMap.comp (h.1 𝒜).toLinearMap)) = _
      rw [exteriorPower.map_comp, Submodule.map_comp, hhQ, hgQ]
    · apply LinearMap.ext
      intro x
      change g.1 ℬ (h.1 ℬ (componentPull T (D.complementInclusion hi) 1 x)) =
        componentPull T (D.complementInclusion hi) 1 (g.1 𝒜 (h.1 𝒜 x))
      calc
        _ = g.1 ℬ (componentPull T (D.complementInclusion hi) 1 (h.1 𝒜 x)) :=
          congrArg (g.1 ℬ) (DFunLike.congr_fun (hhi 𝒜 ℬ hi) x)
        _ = _ := DFunLike.congr_fun (hgi 𝒜 ℬ hi) (h.1 𝒜 x)
    · apply LinearMap.ext
      intro x
      change g.1 𝒜 (h.1 𝒜 (componentPull T (w.schemeMap D hw) 1 x)) =
        componentPull T (w.schemeMap D hw) 1 (g.2 (h.2 x))
      calc
        _ = g.1 𝒜 (componentPull T (w.schemeMap D hw) 1 (h.2 x)) :=
          congrArg (g.1 𝒜) (DFunLike.congr_fun (hhm 𝒜 w hw) x)
        _ = _ := DFunLike.congr_fun (hgm 𝒜 w hw) (h.2 x)
  inv_mem' := by
    rintro g ⟨hgQ, hgi, hgm⟩
    refine ⟨fun 𝒜 ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · exact map_exteriorPower_symm (g.1 𝒜) _ (hgQ 𝒜)
    · apply LinearMap.ext
      intro x
      change (g.1 ℬ).symm (componentPull T (D.complementInclusion hi) 1 x) =
        componentPull T (D.complementInclusion hi) 1 ((g.1 𝒜).symm x)
      apply (g.1 ℬ).injective
      have hh : g.1 ℬ (componentPull T (D.complementInclusion hi) 1
          ((g.1 𝒜).symm x)) = componentPull T (D.complementInclusion hi) 1
            (g.1 𝒜 ((g.1 𝒜).symm x)) :=
        DFunLike.congr_fun (hgi 𝒜 ℬ hi) ((g.1 𝒜).symm x)
      exact ((g.1 ℬ).apply_symm_apply _).trans
        (hh.trans (congrArg (componentPull T (D.complementInclusion hi) 1)
          ((g.1 𝒜).apply_symm_apply x))).symm
    · apply LinearMap.ext
      intro x
      change (g.1 𝒜).symm (componentPull T (w.schemeMap D hw) 1 x) =
        componentPull T (w.schemeMap D hw) 1 (g.2.symm x)
      apply (g.1 𝒜).injective
      have hh : g.1 𝒜 (componentPull T (w.schemeMap D hw) 1 (g.2.symm x)) =
          componentPull T (w.schemeMap D hw) 1 (g.2 (g.2.symm x)) :=
        DFunLike.congr_fun (hgm 𝒜 w hw) (g.2.symm x)
      exact ((g.1 𝒜).apply_symm_apply _).trans
        (hh.trans (congrArg (componentPull T (w.schemeMap D hw) 1)
          (g.2.apply_symm_apply x))).symm

/-- Automorphisms of the actual degree-one and cup-kernel diagram. There is one common target
component for every marking, independently of the chosen stage. This transparent subgroup
subtype synonym inherits the existing group operations without new transport instances;
the product carrier documents why `instance_reducible` is insufficient for these wrappers.
Blueprint: A04 (`thm:a04`). -/
@[reducible]
def DiagramAut := ↥(quadraticDiagramAutSubgroup T C S)

namespace DiagramAut

variable {T C S}

/-- The linear equivalence at a finite stage of a quadratic diagram automorphism. -/
def stageEquiv (g : DiagramAut T C S) (𝒜 : C.Stage) :
    (degreeOne T 𝒜.val.val) ≃ₗ[R] (degreeOne T 𝒜.val.val) := g.val.1 𝒜

/-- The one linear equivalence at the common two-generator target. -/
def targetEquiv (g : DiagramAut T C S) :
    (degreeOne T (twoPunctureArrangement k)) ≃ₗ[R]
      (degreeOne T (twoPunctureArrangement k)) := g.val.2

/-- Every stage equivalence preserves the whole actual cup kernel by image equality. -/
theorem map_cupKernel (g : DiagramAut T C S) (𝒜 : C.Stage) :
    (LinearMap.ker (cupMap T 𝒜.val.val)).map
      (exteriorPower.map 2 (g.stageEquiv 𝒜).toLinearMap) =
        LinearMap.ker (cupMap T 𝒜.val.val) := g.property.1 𝒜

/-- The common-target equivalence automatically preserves its whole actual cup kernel. -/
theorem map_target_cupKernel (g : DiagramAut T C S) :
    (LinearMap.ker (cupMap T (twoPunctureArrangement k))).map
      (exteriorPower.map 2 g.targetEquiv.toLinearMap) =
        LinearMap.ker (cupMap T (twoPunctureArrangement k)) := by
  rw [target_cupKernel_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (exteriorPower.map_surjective g.targetEquiv.surjective)

/-- Stage equivalences commute with actual scheme inclusion pullback. -/
theorem inclusion_naturality (g : DiagramAut T C S) {𝒜 ℬ : C.Stage} (h : 𝒜 ≤ ℬ) :
    (g.stageEquiv ℬ).toLinearMap.comp (componentPull T (D.complementInclusion h) 1) =
      (componentPull T (D.complementInclusion h) 1).comp (g.stageEquiv 𝒜).toLinearMap :=
  g.property.2.1 𝒜 ℬ h

/-- Every tagged marking square uses the same target equivalence. -/
theorem marking_naturality (g : DiagramAut T C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    (g.stageEquiv 𝒜).toLinearMap.comp (componentPull T (w.schemeMap D hw) 1) =
      (componentPull T (w.schemeMap D hw) 1).comp g.targetEquiv.toLinearMap := g.property.2.2 𝒜 w hw

/-- Package a family satisfying precisely whole-cup-kernel equality and the actual arrow
squares. No reconstruction or arbitrary-projection condition is required. -/
def ofEquivs (g : ∀ 𝒜 : C.Stage, (degreeOne T 𝒜.val.val) ≃ₗ[R] (degreeOne T 𝒜.val.val))
    (gT : (degreeOne T (twoPunctureArrangement k)) ≃ₗ[R]
      (degreeOne T (twoPunctureArrangement k)))
    (hQ : ∀ 𝒜 : C.Stage, (LinearMap.ker (cupMap T 𝒜.val.val)).map
      (exteriorPower.map 2 (g 𝒜).toLinearMap) = LinearMap.ker (cupMap T 𝒜.val.val))
    (hi : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g ℬ).toLinearMap.comp (componentPull T (D.complementInclusion h) 1) =
        (componentPull T (D.complementInclusion h) 1).comp (g 𝒜).toLinearMap)
    (hm : ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g 𝒜).toLinearMap.comp (componentPull T (w.schemeMap D hw) 1) =
        (componentPull T (w.schemeMap D hw) 1).comp gT.toLinearMap) :
    DiagramAut T C S := ⟨(g, gT), hQ, hi, hm⟩

@[simp]
theorem stageEquiv_ofEquivs (g gT hQ hi hm) (𝒜 : C.Stage) :
    (ofEquivs (T := T) (C := C) (S := S) g gT hQ hi hm).stageEquiv 𝒜 = g 𝒜 := rfl

@[simp]
theorem targetEquiv_ofEquivs (g gT hQ hi hm) :
    (ofEquivs (T := T) (C := C) (S := S) g gT hQ hi hm).targetEquiv = gT := rfl

/-- A quadratic diagram automorphism is determined by its stage and common target maps. -/
@[ext]
theorem ext {g h : DiagramAut T C S} (hstage : ∀ 𝒜, g.stageEquiv 𝒜 = h.stageEquiv 𝒜)
    (htarget : g.targetEquiv = h.targetEquiv) : g = h := by
  apply Subtype.ext
  exact Prod.ext (funext hstage) htarget

@[simp]
theorem stageEquiv_one (𝒜 : C.Stage) :
    (1 : DiagramAut T C S).stageEquiv 𝒜 = LinearEquiv.refl R _ := rfl

@[simp]
theorem targetEquiv_one :
    (1 : DiagramAut T C S).targetEquiv = LinearEquiv.refl R _ := rfl

@[simp]
theorem stageEquiv_mul (g h : DiagramAut T C S) (𝒜 : C.Stage) :
    (g * h).stageEquiv 𝒜 = g.stageEquiv 𝒜 * h.stageEquiv 𝒜 := rfl

@[simp]
theorem targetEquiv_mul (g h : DiagramAut T C S) :
    (g * h).targetEquiv = g.targetEquiv * h.targetEquiv := rfl

@[simp]
theorem stageEquiv_inv (g : DiagramAut T C S) (𝒜 : C.Stage) :
    g⁻¹.stageEquiv 𝒜 = (g.stageEquiv 𝒜).symm := rfl

@[simp]
theorem targetEquiv_inv (g : DiagramAut T C S) :
    g⁻¹.targetEquiv = g.targetEquiv.symm := rfl

end DiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology
