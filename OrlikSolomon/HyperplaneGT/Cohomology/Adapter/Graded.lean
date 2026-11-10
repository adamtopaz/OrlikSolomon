/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Quadratic

/-!
# Automorphisms of the actual diagonal cohomology diagram

The ambient product consists of algebra equivalences on the actual direct sum of diagonal
cohomology at every selected stage and the one common two-puncture target. The subgroup
preserves every actual homogeneous component and commutes with actual scheme inclusion and
tagged marking pullbacks. No objectwise normalized model replaces these actual carriers.

Blueprint: the full graded diagram in A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The ambient product of actual diagonal cohomology automorphisms and the common target
component.
This is a transparent product synonym so the existing product group instance is inherited;
`instance_reducible` does not expose it to that instance search. -/
@[reducible]
def GradedAutFamily :=
  (∀ 𝒜 : C.Stage, diagonal T (D.complement 𝒜.val.val) ≃ₐ[R] diagonal T (D.complement 𝒜.val.val)) ×
    (diagonal T (schemeMarkingTarget D) ≃ₐ[R] diagonal T (schemeMarkingTarget D))

/-- The subgroup preserving every homogeneous degree and all specified inclusion/marking
squares in the actual diagonal cohomology. Blueprint: A04 (`thm:a04`). -/
def gradedDiagramAutSubgroup : Subgroup (GradedAutFamily T C) where
  carrier := {g | (∀ (𝒜 : C.Stage) (q : ℕ),
      (diagonalDegree T (D.complement 𝒜.val.val) q).map (g.1 𝒜).toLinearMap =
        diagonalDegree T (D.complement 𝒜.val.val) q) ∧
    (∀ q : ℕ, (diagonalDegree T (schemeMarkingTarget D) q).map g.2.toLinearMap =
      diagonalDegree T (schemeMarkingTarget D) q) ∧
    (∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g.1 ℬ).toAlgHom.comp (diagonalPull T (D.complementInclusion h)) =
        (diagonalPull T (D.complementInclusion h)).comp (g.1 𝒜).toAlgHom) ∧
    ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g.1 𝒜).toAlgHom.comp (diagonalPull T (w.schemeMap D hw)) =
        (diagonalPull T (w.schemeMap D hw)).comp g.2.toAlgHom}
  one_mem' := by
    refine ⟨fun 𝒜 q ↦ ?_, fun q ↦ ?_, fun 𝒜 ℬ h ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (diagonalDegree T (D.complement 𝒜.val.val) q).map LinearMap.id = _
      exact Submodule.map_id _
    · change (diagonalDegree T (schemeMarkingTarget D) q).map LinearMap.id = _
      exact Submodule.map_id _
    · rfl
    · rfl
  mul_mem' := by
    rintro g h ⟨hgd, hgT, hgi, hgm⟩ ⟨hhd, hhT, hhi, hhm⟩
    refine ⟨fun 𝒜 q ↦ ?_, fun q ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (diagonalDegree T (D.complement 𝒜.val.val) q).map
        ((g.1 𝒜).toLinearMap.comp (h.1 𝒜).toLinearMap) = _
      rw [Submodule.map_comp, hhd, hgd]
    · change (diagonalDegree T (schemeMarkingTarget D) q).map
        (g.2.toLinearMap.comp h.2.toLinearMap) = _
      rw [Submodule.map_comp, hhT, hgT]
    · change ((g.1 ℬ).toAlgHom.comp (h.1 ℬ).toAlgHom).comp
          (diagonalPull T (D.complementInclusion hi)) =
        (diagonalPull T (D.complementInclusion hi)).comp ((g.1 𝒜).toAlgHom.comp (h.1 𝒜).toAlgHom)
      rw [AlgHom.comp_assoc, hhi, ← AlgHom.comp_assoc, hgi, AlgHom.comp_assoc]
    · change ((g.1 𝒜).toAlgHom.comp (h.1 𝒜).toAlgHom).comp (diagonalPull T (w.schemeMap D hw)) =
        (diagonalPull T (w.schemeMap D hw)).comp (g.2.toAlgHom.comp h.2.toAlgHom)
      rw [AlgHom.comp_assoc, hhm, ← AlgHom.comp_assoc, hgm, AlgHom.comp_assoc]
  inv_mem' := by
    rintro g ⟨hgd, hgT, hgi, hgm⟩
    refine ⟨fun 𝒜 q ↦ ?_, fun q ↦ ?_, fun 𝒜 ℬ hi ↦ ?_, fun 𝒜 w hw ↦ ?_⟩
    · change (diagonalDegree T (D.complement 𝒜.val.val) q).map
        (g.1 𝒜).toLinearEquiv.symm.toLinearMap = _
      calc
        _ = ((diagonalDegree T (D.complement 𝒜.val.val) q).map
            (g.1 𝒜).toLinearEquiv.toLinearMap).map
            (g.1 𝒜).toLinearEquiv.symm.toLinearMap := by rw [hgd]
        _ = _ := by rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
    · change (diagonalDegree T (schemeMarkingTarget D) q).map
        g.2.toLinearEquiv.symm.toLinearMap = _
      calc
        _ = ((diagonalDegree T (schemeMarkingTarget D) q).map g.2.toLinearEquiv.toLinearMap).map
            g.2.toLinearEquiv.symm.toLinearMap := by rw [hgT]
        _ = _ := by rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
    · apply AlgHom.ext
      intro x
      change (g.1 ℬ).symm (diagonalPull T (D.complementInclusion hi) x) =
        diagonalPull T (D.complementInclusion hi) ((g.1 𝒜).symm x)
      apply (g.1 ℬ).injective
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using
        (DFunLike.congr_fun (hgi 𝒜 ℬ hi) ((g.1 𝒜).symm x)).symm
    · apply AlgHom.ext
      intro x
      change (g.1 𝒜).symm (diagonalPull T (w.schemeMap D hw) x) =
        diagonalPull T (w.schemeMap D hw) (g.2.symm x)
      apply (g.1 𝒜).injective
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using
        (DFunLike.congr_fun (hgm 𝒜 w hw) (g.2.symm x)).symm

/-- Automorphisms of the actual full marked diagonal cohomology diagram, with the existing degree
grading and one shared two-puncture target. This transparent subgroup subtype synonym inherits
the existing group operations without new transport instances; the product carrier documents
why `instance_reducible` is insufficient for these wrappers. Blueprint: A04 (`thm:a04`). -/
@[reducible]
def GradedDiagramAut := ↥(gradedDiagramAutSubgroup T C S)

namespace GradedDiagramAut

variable {T C S}

/-- The full algebra equivalence at a selected finite stage. -/
def stageEquiv (g : GradedDiagramAut T C S) (𝒜 : C.Stage) :
    diagonal T (D.complement 𝒜.val.val) ≃ₐ[R] diagonal T (D.complement 𝒜.val.val) := g.val.1 𝒜

/-- The full algebra equivalence at the one common target. -/
def targetEquiv (g : GradedDiagramAut T C S) :
    diagonal T (schemeMarkingTarget D) ≃ₐ[R] diagonal T (schemeMarkingTarget D) :=
  g.val.2

/-- The whole homogeneous component of each stage is preserved by image equality. -/
theorem map_degree (g : GradedDiagramAut T C S) (𝒜 : C.Stage) (q : ℕ) :
    (diagonalDegree T (D.complement 𝒜.val.val) q).map (g.stageEquiv 𝒜).toLinearMap =
      diagonalDegree T (D.complement 𝒜.val.val) q :=
  g.property.1 𝒜 q

/-- The common target equivalence preserves every homogeneous component. -/
theorem map_target_degree (g : GradedDiagramAut T C S) (q : ℕ) :
    (diagonalDegree T (schemeMarkingTarget D) q).map g.targetEquiv.toLinearMap =
      diagonalDegree T (schemeMarkingTarget D) q := g.property.2.1 q

/-- The full stage equivalences commute with every actual scheme inclusion pullback. -/
theorem inclusion_naturality (g : GradedDiagramAut T C S) {𝒜 ℬ : C.Stage} (h : 𝒜 ≤ ℬ) :
    (g.stageEquiv ℬ).toAlgHom.comp (diagonalPull T (D.complementInclusion h)) =
      (diagonalPull T (D.complementInclusion h)).comp (g.stageEquiv 𝒜).toAlgHom :=
  g.property.2.2.1 𝒜 ℬ h

/-- Every full marking square uses the same common target equivalence. -/
theorem marking_naturality (g : GradedDiagramAut T C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    (g.stageEquiv 𝒜).toAlgHom.comp (diagonalPull T (w.schemeMap D hw)) =
      (diagonalPull T (w.schemeMap D hw)).comp g.targetEquiv.toAlgHom := g.property.2.2.2 𝒜 w hw

/-- Construct a full graded diagram automorphism from precisely the grading and specified
arrow equations. This constructor assumes no classification or reconstruction statement. -/
def ofEquivs (g : ∀ 𝒜 : C.Stage,
      diagonal T (D.complement 𝒜.val.val) ≃ₐ[R] diagonal T (D.complement 𝒜.val.val))
    (gT : diagonal T (schemeMarkingTarget D) ≃ₐ[R]
      diagonal T (schemeMarkingTarget D))
    (hd : ∀ (𝒜 : C.Stage) (q : ℕ),
      (diagonalDegree T (D.complement 𝒜.val.val) q).map (g 𝒜).toLinearMap =
        diagonalDegree T (D.complement 𝒜.val.val) q)
    (hT : ∀ q, (diagonalDegree T (schemeMarkingTarget D) q).map gT.toLinearMap =
      diagonalDegree T (schemeMarkingTarget D) q)
    (hi : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
      (g ℬ).toAlgHom.comp (diagonalPull T (D.complementInclusion h)) =
        (diagonalPull T (D.complementInclusion h)).comp (g 𝒜).toAlgHom)
    (hm : ∀ (𝒜 : C.Stage) (w : Marking S n) (hw : w.Available 𝒜.val.val),
      (g 𝒜).toAlgHom.comp (diagonalPull T (w.schemeMap D hw)) =
        (diagonalPull T (w.schemeMap D hw)).comp gT.toAlgHom) :
    GradedDiagramAut T C S := ⟨(g, gT), hd, hT, hi, hm⟩

@[simp]
theorem stageEquiv_ofEquivs (g gT hd hT hi hm) (𝒜 : C.Stage) :
    (ofEquivs (T := T) (C := C) (S := S) g gT hd hT hi hm).stageEquiv 𝒜 = g 𝒜 := rfl

@[simp]
theorem targetEquiv_ofEquivs (g gT hd hT hi hm) :
    (ofEquivs (T := T) (C := C) (S := S) g gT hd hT hi hm).targetEquiv = gT := rfl

/-- Full diagram automorphisms agree when all stage and common target equivalences agree. -/
@[ext]
theorem ext {g h : GradedDiagramAut T C S}
    (hstage : ∀ 𝒜, g.stageEquiv 𝒜 = h.stageEquiv 𝒜)
    (htarget : g.targetEquiv = h.targetEquiv) : g = h := by
  apply Subtype.ext
  exact Prod.ext (funext hstage) htarget

@[simp]
theorem stageEquiv_one (𝒜 : C.Stage) :
    (1 : GradedDiagramAut T C S).stageEquiv 𝒜 = AlgEquiv.refl := rfl

@[simp]
theorem targetEquiv_one : (1 : GradedDiagramAut T C S).targetEquiv = AlgEquiv.refl := rfl

@[simp]
theorem stageEquiv_mul (g h : GradedDiagramAut T C S) (𝒜 : C.Stage) :
    (g * h).stageEquiv 𝒜 = g.stageEquiv 𝒜 * h.stageEquiv 𝒜 := rfl

@[simp]
theorem targetEquiv_mul (g h : GradedDiagramAut T C S) :
    (g * h).targetEquiv = g.targetEquiv * h.targetEquiv := rfl

@[simp]
theorem stageEquiv_inv (g : GradedDiagramAut T C S) (𝒜 : C.Stage) :
    (g⁻¹).stageEquiv 𝒜 = (g.stageEquiv 𝒜).symm := rfl

@[simp]
theorem targetEquiv_inv (g : GradedDiagramAut T C S) :
    (g⁻¹).targetEquiv = g.targetEquiv.symm := rfl

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology
