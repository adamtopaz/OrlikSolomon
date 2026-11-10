/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import OrlikSolomon.Examples.HyperplaneGT.Incidence
public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.FieldTheory.PrimeField

/-!
# Galois extraction and scalar-kernel regressions

Concrete binary-field hyperplanes exercise both connectivity witnesses. The guarded triple
through the axes cannot be the empty triangle. A transverse hyperplane meets both members
of the parallel pair whose union contains every binary rational point of the plane.

The actual scalar diagrams over `ℤ/5` and `ℤ/4` exercise extraction and its unique common
scalar, including the retained target and the inverse dual convention. Complex conjugation
fixes the set `{0}` without fixing the base field, so the generation hypothesis cannot be
removed. The geometric statements use no coefficient ring or point of a complement.
Blueprint: C04 (`prop:c04`) and S01 (`lem:s01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.GaloisReconstructionExamples

/-- A guarded triple through the actual binary coordinate axes is different from the empty
binary triangle, whose conventional codimension alone would not detect the empty intersection.
-/
theorem binary_intersecting_triple :
    ∃ L : Hyperplane (ZMod 2) 2,
      DependentTriple (CoordinateExamples.xLine (ZMod 2))
        (CoordinateExamples.yLine (ZMod 2)) L ∧
        L ≠ CoordinateExamples.diagonalLine (1 : ZMod 2) := by
  obtain ⟨L, hL⟩ := exists_dependentTriple_of_inf_ne_bot
    (CoordinateExamples.xLine (ZMod 2)) (CoordinateExamples.yLine (ZMod 2))
    CoordinateExamples.xLine_ne_yLine CoordinateExamples.concurrent_traces.1
  refine ⟨L, hL, ?_⟩
  intro he
  exact CoordinateExamples.triangle_codim_but_not_dependent.2 (he ▸ hL)

/-- The second binary coordinate line, parallel to `x = 0`. -/
def binaryShiftedAxis : Hyperplane (ZMod 2) 2 :=
  graphHyperplane 0 (AffineMap.const _ _ 1)

/-- Membership in the shifted binary coordinate axis is the equation `x₀ = 1`. -/
@[simp]
theorem mem_binaryShiftedAxis (x : Fin 2 → ZMod 2) :
    x ∈ binaryShiftedAxis.val ↔ x 0 = 1 := by
  simp [binaryShiftedAxis]

/-- The two actual binary coordinate fibers are a strict parallel pair. -/
theorem binary_parallel_pair :
    Parallel (CoordinateExamples.xLine (ZMod 2)) binaryShiftedAxis := by
  apply parallel_graphHyperplane_of_sub_eq_const (c := 1) _ one_ne_zero
  ext x
  simp

/-- These two actual parallel hyperplanes cover all binary rational points, so their
complement supplies no rational point for the connectivity proof. -/
theorem binary_parallel_cover (x : Fin 2 → ZMod 2) :
    x ∈ (CoordinateExamples.xLine (ZMod 2)).val ∨ x ∈ binaryShiftedAxis.val := by
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases (x 0) with hx | hx
  · exact Or.inl ((CoordinateExamples.mem_xLine x).mpr hx)
  · exact Or.inr ((mem_binaryShiftedAxis x).mpr hx)

/-- Even this point-free-complement parallel pair has an actual transverse hyperplane
meeting each member nontrivially, distinct from both. -/
theorem binary_parallel_transverse :
    ∃ L : Hyperplane (ZMod 2) 2,
      CoordinateExamples.xLine (ZMod 2) ≠ L ∧ binaryShiftedAxis ≠ L ∧
        (CoordinateExamples.xLine (ZMod 2)).val ⊓ L.val ≠ ⊥ ∧
        binaryShiftedAxis.val ⊓ L.val ≠ ⊥ :=
  exists_hyperplane_meeting_parallel_pair (by decide) _ _ binary_parallel_pair

universe u v r

/-- Extracted composition has the same order as the actual diagram composition, and the
inverse family cancels on field elements. Field and coefficient universes are independent. -/
theorem extracted_composition {k : Type u} {k₀ : Type v} [Field k] [Field k₀]
    [Algebra k₀ k] {R : Type r} [CommRing R] [IsLocalRing R] {n : ℕ}
    {C : CofinalSystem k₀ k n} {S : Set k₀} (g h : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : k) :
    DiagramAut.toGalois R C S hS hgen hn (g * h) a =
        DiagramAut.toGalois R C S hS hgen hn g
          (DiagramAut.toGalois R C S hS hgen hn h a) ∧
      DiagramAut.toGalois R C S hS hgen hn g⁻¹
        (DiagramAut.toGalois R C S hS hgen hn g a) = a := by simp

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A genuine scalar-two diagram lies in the extracted kernel, whose unique scalar acts
on every stage and the common target. Its actual dual value is three, not two. -/
theorem scalar_two_extracted_kernel :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let g := DualExamples.scalarTwoDiagram C S
    let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    DiagramAut.toGalois (ZMod 5) C S (by simp [S]) hgen (by decide) g = 1 ∧
      (∃! u : (ZMod 5)ˣ,
        (∀ (A : C.Stage) (x : A.val.val →₀ ZMod 5), g.stageEquiv A x = (u : ZMod 5) • x) ∧
        (∀ x : Fin 2 →₀ ZMod 5, g.targetEquiv x = (u : ZMod 5) • x)) ∧
      (g.universalEquiv (Finsupp.single H 1)) H = 2 ∧
      DiagramAut.dualAction g (Finsupp.lapply H) (Finsupp.single H 1) = 3 ∧
      (3 : ZMod 5) ≠ 2 := by
  dsimp only
  let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
  let S : Set (ZMod 2) := {0}
  let g := DualExamples.scalarTwoDiagram C S
  let H := coordinateHyperplane (0 : Fin 2) (0 : ZMod 2)
  have hS : (0 : ZMod 2) ∈ S := by simp [S]
  have hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
  have hg : DiagramAut.toGalois (ZMod 5) C S hS hgen (by decide) g = 1 :=
    (g.toGalois_eq_one_iff_scalar hS hgen (by decide)).mpr
      ⟨DualExamples.scalarTwoUnit, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨hg, g.scalar_of_toGalois_eq_one hS hgen (by decide) hg, ?_, ?_, by decide⟩
  · rw [DualExamples.scalarTwoDiagram_universal_apply]
    simp
  · obtain ⟨hp, hu⟩ := IncidenceExamples.scalar_two_recovered C S hS (by decide) H
    rw [g.dualAction_delta hS (by decide), hp, hu]
    simp [DualExamples.scalarTwoUnit, H]

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- A nontrivial actual scalar diagram over the nonfield local ring `ℤ/4` is in the kernel.
The scalar-kernel conclusion retains every stage and the common target, while coefficients
still include the nonzero nilpotent two. No coefficient-field assumption is introduced. -/
theorem mod_four_extracted_kernel :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let g := IncidenceExamples.scalarThreeDiagram C S
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    DiagramAut.toGalois (ZMod 4) C S (by simp [S]) hgen (by decide) g = 1 ∧
      (∃! u : (ZMod 4)ˣ,
        (∀ (A : C.Stage) (x : A.val.val →₀ ZMod 4), g.stageEquiv A x = (u : ZMod 4) • x) ∧
        (∀ x : Fin 2 →₀ ZMod 4, g.targetEquiv x = (u : ZMod 4) • x)) ∧
      g.targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      (3 : ZMod 4) ≠ 1 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 := by
  dsimp only
  let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
  let S : Set (ZMod 2) := {0}
  let g := IncidenceExamples.scalarThreeDiagram C S
  have hS : (0 : ZMod 2) ∈ S := by simp [S]
  have hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
  have hg : DiagramAut.toGalois (ZMod 4) C S hS hgen (by decide) g = 1 :=
    (g.toGalois_eq_one_iff_scalar hS hgen (by decide)).mpr
      ⟨IncidenceExamples.scalarThreeUnit, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨hg, g.scalar_of_toGalois_eq_one hS hgen (by decide) hg, ?_,
    by decide, by decide, by decide⟩
  change ((3 : ZMod 4) • Finsupp.single (0 : Fin 2) 1) 0 = 3
  simp

/-- Fixing the marked set alone does not give descent without its field-generation
hypothesis: conjugation fixes `{0}` in `ℂ` but moves the imaginary unit of the same base
field. Its marked-set subfield closure is consequently proper. -/
theorem generation_hypothesis_needed :
    (∀ s ∈ ({0} : Set ℂ), Complex.conjAe.toRingEquiv s = s) ∧
      Complex.conjAe.toRingEquiv Complex.I ≠ Complex.I ∧
      Subfield.closure ({0} : Set ℂ) ≠ ⊤ := by
  have hfix : ∀ s ∈ ({0} : Set ℂ), Complex.conjAe.toRingEquiv s = s := by
    intro s hs
    simpa only [Set.mem_singleton_iff] using hs ▸ (map_zero Complex.conjAe)
  have hnot : Complex.conjAe.toRingEquiv Complex.I ≠ Complex.I := by
    intro he
    have him := congrArg Complex.im he
    norm_num at him
  refine ⟨hfix, hnot, fun hgen ↦ ?_⟩
  have he : Complex.conjAe.toRingHom = RingHom.id ℂ :=
    RingHom.eq_of_eqOn_of_field_closure_eq_top hgen hfix
  exact hnot (RingHom.congr_fun he Complex.I)

end OrlikSolomon.HyperplaneGT.GaloisReconstructionExamples
