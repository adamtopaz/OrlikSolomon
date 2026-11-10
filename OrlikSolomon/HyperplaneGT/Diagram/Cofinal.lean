/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.GradedScalar

/-!
# Restriction of marked diagrams to selected stages

An inclusion of selected stage families restricts an actual quadratic or full graded
family, retaining its one common target and every marking square. This construction is
valid over every commutative ring. It asserts no extension from a subsystem; invertibility
requires the later classification theorem.

Blueprint: the restriction maps in E02 (`cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}

namespace CofinalSystem

variable {C C' C'' : CofinalSystem k₀ k n}

/-- Include the stages of a subsystem without changing their stable arrangements. -/
def stageInclusion (hC : C'.stages ⊆ C.stages) (A : C'.Stage) : C.Stage :=
  ⟨A.val, hC A.property⟩

@[simp]
theorem stageInclusion_val (hC : C'.stages ⊆ C.stages) (A : C'.Stage) :
    (stageInclusion hC A).val = A.val := rfl

@[simp]
theorem stageInclusion_refl (A : C.Stage) : stageInclusion (Set.Subset.refl _) A = A := rfl

@[simp]
theorem stageInclusion_trans (hC : C'.stages ⊆ C.stages)
    (hC' : C''.stages ⊆ C'.stages) (A : C''.Stage) :
    stageInclusion hC (stageInclusion hC' A) = stageInclusion (hC'.trans hC) A := rfl

end CofinalSystem

variable (R : Type r) [CommRing R] (C C' : CofinalSystem k₀ k n) (S : Set k₀)

namespace DiagramAut

/-- Restrict the actual quadratic family to the chosen subsystem,
keeping its common target. No reconstruction hypothesis is used. Blueprint: E02 (`cor:e02`). -/
def restrictStages (hC : C'.stages ⊆ C.stages) :
    DiagramAut R C S →* DiagramAut R C' S where
  toFun g := ofEquivs (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A ↦ g.map_quadraticRelationSpan (CofinalSystem.stageInclusion hC A))
    (fun A B h ↦ g.inclusion_naturality
      (𝒜 := CofinalSystem.stageInclusion hC A) (ℬ := CofinalSystem.stageInclusion hC B) h)
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut R C S) (A : C'.Stage) :
    (restrictStages R C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages)
    (g : DiagramAut R C S) :
    (restrictStages R C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restriction to the original stage family is the identity. -/
@[simp]
theorem restrictStages_refl (g : DiagramAut R C S) :
    restrictStages R C C S (Set.Subset.refl _) g = g := by
  exact DiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive restrictions retain exactly the same components and common target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (g : DiagramAut R C S) :
    restrictStages R C' C'' S hC' (restrictStages R C C' S hC g) =
      restrictStages R C C'' S (hC'.trans hC) g := by
  exact DiagramAut.ext (fun _ ↦ rfl) rfl

end DiagramAut

namespace GradedDiagramAut

/-- Restrict the actual full graded family to the chosen subsystem,
keeping its common target. No reconstruction hypothesis is used. Blueprint: E02 (`cor:e02`). -/
def restrictStages (hC : C'.stages ⊆ C.stages) :
    GradedDiagramAut R C S →* GradedDiagramAut R C' S where
  toFun g := ofEquivs (fun A ↦ g.stageEquiv (CofinalSystem.stageInclusion hC A))
    g.targetEquiv
    (fun A q ↦ g.map_degree (CofinalSystem.stageInclusion hC A) q)
    (fun q ↦ g.map_target_degree q)
    (fun A B h ↦ g.inclusion_naturality
      (𝒜 := CofinalSystem.stageInclusion hC A) (ℬ := CofinalSystem.stageInclusion hC B) h)
    (fun A w hw ↦ g.marking_naturality (CofinalSystem.stageInclusion hC A) w hw)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem restrictStages_stageEquiv (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut R C S) (A : C'.Stage) :
    (restrictStages R C C' S hC g).stageEquiv A =
      g.stageEquiv (CofinalSystem.stageInclusion hC A) := rfl

@[simp]
theorem restrictStages_targetEquiv (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut R C S) :
    (restrictStages R C C' S hC g).targetEquiv = g.targetEquiv := rfl

/-- Restriction to the original stage family is the identity. -/
@[simp]
theorem restrictStages_refl (g : GradedDiagramAut R C S) :
    restrictStages R C C S (Set.Subset.refl _) g = g := by
  exact GradedDiagramAut.ext (fun _ ↦ rfl) rfl

/-- Successive restrictions retain exactly the same components and common target. -/
theorem restrictStages_trans (C'' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hC' : C''.stages ⊆ C'.stages)
    (g : GradedDiagramAut R C S) :
    restrictStages R C' C'' S hC' (restrictStages R C C' S hC g) =
      restrictStages R C C'' S (hC'.trans hC) g := by
  exact GradedDiagramAut.ext (fun _ ↦ rfl) rfl

end GradedDiagramAut

/-- Taking degree one commutes with literal restriction of stage families. -/
@[simp]
theorem GradedDiagramAut.toQuadratic_restrictStages (hC : C'.stages ⊆ C.stages)
    (g : GradedDiagramAut R C S) :
    GradedDiagramAut.toQuadratic R C' S (GradedDiagramAut.restrictStages R C C' S hC g) =
      DiagramAut.restrictStages R C C' S hC (GradedDiagramAut.toQuadratic R C S g) := by
  exact DiagramAut.ext (fun _ ↦ rfl) rfl

/-- The scalar family restricts with the same parameter and common target. -/
@[simp]
theorem DiagramAut.restrictStages_scalarQuadraticAut (hC : C'.stages ⊆ C.stages) (a : Rˣ) :
    DiagramAut.restrictStages R C C' S hC (scalarQuadraticAut R C S a) =
      scalarQuadraticAut R C' S a := by
  exact DiagramAut.ext (fun _ ↦ rfl) rfl

/-- The scalar family restricts with the same parameter and common target. -/
@[simp]
theorem GradedDiagramAut.restrictStages_scalarGradedAut (hC : C'.stages ⊆ C.stages) (a : Rˣ) :
    GradedDiagramAut.restrictStages R C C' S hC (scalarGradedAut R C S a) =
      scalarGradedAut R C' S a := by
  exact GradedDiagramAut.ext (fun _ ↦ rfl) rfl

/-- The Galois family restricts with the same parameter and common target. -/
@[simp]
theorem GradedDiagramAut.restrictStages_galoisGradedAut (hC : C'.stages ⊆ C.stages)
    (a : k ≃ₐ[k₀] k) :
    GradedDiagramAut.restrictStages R C C' S hC (galoisGradedAut R C S a) =
      galoisGradedAut R C' S a := by
  exact GradedDiagramAut.ext (fun _ ↦ rfl) rfl

end OrlikSolomon.HyperplaneGT
