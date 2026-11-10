/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Realization
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification.Compatibility
public import OrlikSolomon.Examples.HyperplaneGT.Coordinates
public import OrlikSolomon.Examples.HyperplaneGT.Incidence

/-!
# Actual reconstruction and cofinal-independence regressions

The explicit binary subsystem below is cofinal but not closed under unions. Its actual
restriction and inverse preserve every component, the common target and the complete
classification coordinates. Other consumers use independent theory universes, characteristic
two, nonfield local coefficients, nonlocal domain coefficients and zero-dimensional targets.
Theory-level examples explicitly take an existing eligible theory; they do not construct a
new nonzero realization or assert an unproved realization instance.

Blueprint: E01–E02 (`thm:e01`, `cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r b h b' h'

namespace OrlikSolomon.HyperplaneGT.TheoryReconstructionExamples

open CoordinateExamples

/-- Every binary arrangement is stable for automorphisms fixing the whole binary field. -/
def binaryStable (A : Arrangement (ZMod 2) (Fin 2 → ZMod 2)) :
    StableArrangement (ZMod 2) (ZMod 2) 2 := by
  refine ⟨A, ?_⟩
  intro σ H hH
  have hσ : σ = 1 := by
    ext x
    simpa using σ.commutes x
  simpa only [hσ, one_smul] using hH

/-- The actual pair of binary coordinate axes, used as the excluded finite stage. -/
def axes : Arrangement (ZMod 2) (Fin 2 → ZMod 2) := by
  classical
  exact Arrangement.ofFinset {(xLine (ZMod 2)).val, (yLine (ZMod 2)).val}

/-- The first actual singleton axis arrangement. -/
def xAxis : Arrangement (ZMod 2) (Fin 2 → ZMod 2) := by
  classical
  exact Arrangement.ofFinset {(xLine (ZMod 2)).val}

/-- The second actual singleton axis arrangement. -/
def yAxis : Arrangement (ZMod 2) (Fin 2 → ZMod 2) := by
  classical
  exact Arrangement.ofFinset {(yLine (ZMod 2)).val}

private theorem diagonal_notMem_axes : (diagonalLine (0 : ZMod 2)).val ∉ axes := by
  classical
  have hx : (diagonalLine (0 : ZMod 2)).val ≠ (xLine (ZMod 2)).val :=
    fun h ↦ xLine_ne_diagonalLine 0 (Subtype.ext h.symm)
  have hy : (diagonalLine (0 : ZMod 2)).val ≠ (yLine (ZMod 2)).val :=
    fun h ↦ yLine_ne_diagonalLine 0 (Subtype.ext h.symm)
  simp [axes, hx, hy]

/-- A genuine cofinal subsystem: exclude exactly the two-axis arrangement. Any finite
support can still be enlarged through a third actual binary hyperplane. -/
def nonUnionSystem : CofinalSystem (ZMod 2) (ZMod 2) 2 where
  stages := {A | A.val ≠ axes}
  cofinal s := by
    classical
    obtain ⟨A, -, hs⟩ := (fullCofinalSystem (ZMod 2) (ZMod 2) 2).cofinal
      (insert (diagonalLine (0 : ZMod 2)) s)
    refine ⟨A, ?_, fun H hH ↦ hs H (Finset.mem_insert_of_mem hH)⟩
    intro hA
    have hD := hs (diagonalLine 0) (Finset.mem_insert_self _ _)
    rw [hA] at hD
    exact diagonal_notMem_axes hD

/-- The explicit subsystem is nested in the actual full stable cofinal system. -/
theorem nonUnionSystem_subset : nonUnionSystem.stages ⊆
    (fullCofinalSystem (ZMod 2) (ZMod 2) 2).stages := fun A _ ↦ mem_fullCofinalSystem A

/-- Both singleton stages belong to the subsystem, their actual union is excluded.
This is a concrete witness that cofinality does not require closure under unions. -/
theorem nonUnionSystem_not_union_closed :
    binaryStable xAxis ∈ nonUnionSystem.stages ∧
    binaryStable yAxis ∈ nonUnionSystem.stages ∧
    binaryStable axes ∉ nonUnionSystem.stages ∧
    ∀ H : AffineSubspace (ZMod 2) (Fin 2 → ZMod 2),
      H ∈ axes ↔ H ∈ xAxis ∨ H ∈ yAxis := by
  classical
  have hxy : (xLine (ZMod 2)).val ≠ (yLine (ZMod 2)).val :=
    fun h ↦ xLine_ne_yLine (Subtype.ext h)
  have hx : xAxis ≠ axes := by
    intro h
    have hy : (yLine (ZMod 2)).val ∈ axes := by simp [axes, (yLine (ZMod 2)).property]
    rw [← h] at hy
    simp [xAxis, Ne.symm hxy] at hy
  have hy : yAxis ≠ axes := by
    intro h
    have hx : (xLine (ZMod 2)).val ∈ axes := by simp [axes, (xLine (ZMod 2)).property]
    rw [← h] at hx
    simp [yAxis, hxy] at hx
  refine ⟨hx, hy, not_not.mpr rfl, ?_⟩
  intro H
  simp only [axes, xAxis, yAxis, Arrangement.mem_ofFinset, Finset.mem_insert,
    Finset.mem_singleton, or_and_right]

section Actual

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {B' : Type b'} [CommRing B'] [Algebra R B']
  {ℬ' : ℤ → Submodule R B'} [GradedAlgebra ℬ'] {D' : Geometric.SmoothDomain k}
  (T' : Geometric.OrdinaryTheory.{u, r, b', h'} D' ℬ')
  {n : ℕ} (C C' : CofinalSystem k₀ k n) (S : Set k₀)

/-- Independently sized eligible theories retain the whole cup kernel under comparison,
without any localness or nonzero coefficient assumption. -/
theorem whole_cup_kernel (A : Arrangement k (Fin n → k)) :
    (LinearMap.ker (Cohomology.cupMap T A)).map
      (exteriorPower.map 2 (Cohomology.realizationDegreeOneEquiv T T' A).toLinearMap) =
    LinearMap.ker (Cohomology.cupMap T' A) :=
  Cohomology.realizationDegreeOneEquiv_cupKernel T T' A

/-- The two realizations commute with actual stage restriction, keeping the same target. -/
theorem actual_restriction_realization (hC : C'.stages ⊆ C.stages)
    (g : Cohomology.GradedDiagramAut T C S) :
    Cohomology.realizationGradedAutEquiv T T' C' S
      (Cohomology.GradedDiagramAut.restrictStages T C C' S hC g) =
    Cohomology.GradedDiagramAut.restrictStages T' C C' S hC
      (Cohomology.realizationGradedAutEquiv T T' C S g) :=
  Cohomology.realizationGradedAutEquiv_restrictStages T T' C S C' hC g

/-- Local actual reconstruction satisfies both bare inverse-cancellation forms. -/
theorem local_inverse_cancellation [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : Cohomology.GradedDiagramAut T C S) :
    (Cohomology.localGradedReconstruction T C S hS hgen hn).symm
      (Cohomology.localGradedReconstruction T C S hS hgen hn p) = p ∧
    Cohomology.localGradedReconstruction T C S hS hgen hn
      ((Cohomology.localGradedReconstruction T C S hS hgen hn).symm g) = g := by simp

/-- Domain actual reconstruction uses no local-ring instance and has the same inverse laws.
-/
theorem domain_inverse_cancellation [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) (g : Cohomology.DiagramAut T C S) :
    (Cohomology.domainQuadraticReconstruction T C S hS hgen hn).symm
      (Cohomology.domainQuadraticReconstruction T C S hS hgen hn p) = p ∧
    Cohomology.domainQuadraticReconstruction T C S hS hgen hn
      ((Cohomology.domainQuadraticReconstruction T C S hS hgen hn).symm g) = g := by simp


/-- Bare two-sided cancellation is retained for local pure cofinal restriction. -/
theorem pure_local_quadratic_cofinal_cancellation [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) (g' : DiagramAut R C' S) :
    (cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (cofinalRestrictionEquiv R C C' S hC hS hgen hn g) = g ∧
    cofinalRestrictionEquiv R C C' S hC hS hgen hn
      ((cofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for local pure cofinal restriction. -/
theorem pure_local_graded_cofinal_cancellation [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) (g' : GradedDiagramAut R C' S) :
    (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g) = g ∧
    gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
      ((gradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for domain pure cofinal restriction. -/
theorem pure_domain_quadratic_cofinal_cancellation [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) (g' : DiagramAut R C' S) :
    (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (domainCofinalRestrictionEquiv R C C' S hC hS hgen hn g) = g ∧
    domainCofinalRestrictionEquiv R C C' S hC hS hgen hn
      ((domainCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for domain pure cofinal restriction. -/
theorem pure_domain_graded_cofinal_cancellation [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) (g' : GradedDiagramAut R C' S) :
    (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm
      (domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn g) = g ∧
    domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn
      ((domainGradedCofinalRestrictionEquiv R C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for local actual cofinal restriction. -/
theorem actual_local_quadratic_cofinal_cancellation [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.DiagramAut T C S) (g' : Cohomology.DiagramAut T C' S) :
    (Cohomology.cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (Cohomology.cofinalRestrictionEquiv T C C' S hC hS hgen hn g) = g ∧
    Cohomology.cofinalRestrictionEquiv T C C' S hC hS hgen hn
      ((Cohomology.cofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for local actual cofinal restriction. -/
theorem actual_local_graded_cofinal_cancellation [IsLocalRing R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.GradedDiagramAut T C S) (g' : Cohomology.GradedDiagramAut T C' S) :
    (Cohomology.gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (Cohomology.gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn g) = g ∧
    Cohomology.gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
      ((Cohomology.gradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for domain actual cofinal restriction. -/
theorem actual_domain_quadratic_cofinal_cancellation [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.DiagramAut T C S) (g' : Cohomology.DiagramAut T C' S) :
    (Cohomology.domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (Cohomology.domainCofinalRestrictionEquiv T C C' S hC hS hgen hn g) = g ∧
    Cohomology.domainCofinalRestrictionEquiv T C C' S hC hS hgen hn
      ((Cohomology.domainCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g') = g' := by simp

/-- Bare two-sided cancellation is retained for domain actual cofinal restriction. -/
theorem actual_domain_graded_cofinal_cancellation [IsDomain R]
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.GradedDiagramAut T C S) (g' : Cohomology.GradedDiagramAut T C' S) :
    (Cohomology.domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm
      (Cohomology.domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn g) = g ∧
    Cohomology.domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn
      ((Cohomology.domainGradedCofinalRestrictionEquiv T C C' S hC hS hgen hn).symm g') = g' :=
  by simp

/-- Bare two-sided cancellation is retained for local actual degree-one restriction. -/
theorem actual_local_restriction_cancellation [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.GradedDiagramAut T C S) (f : Cohomology.DiagramAut T C S) :
    (Cohomology.localRestrictionEquiv T C S hS hgen hn).symm
      (Cohomology.localRestrictionEquiv T C S hS hgen hn g) = g ∧
    Cohomology.localRestrictionEquiv T C S hS hgen hn
      ((Cohomology.localRestrictionEquiv T C S hS hgen hn).symm f) = f := by simp

/-- Bare two-sided cancellation is retained for domain actual degree-one restriction. -/
theorem actual_domain_restriction_cancellation [IsDomain R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : Cohomology.GradedDiagramAut T C S) (f : Cohomology.DiagramAut T C S) :
    (Cohomology.domainRestrictionEquiv T C S hS hgen hn).symm
      (Cohomology.domainRestrictionEquiv T C S hS hgen hn g) = g ∧
    Cohomology.domainRestrictionEquiv T C S hS hgen hn
      ((Cohomology.domainRestrictionEquiv T C S hS hgen hn).symm f) = f := by simp

end Actual


section Nonfield

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

variable {B : Type b} [CommRing B] [Algebra (ZMod 4) B]
  {ℬ : ℤ → Submodule (ZMod 4) B} [GradedAlgebra ℬ]
  {D : Geometric.SmoothDomain (ZMod 2)}
  (T : Geometric.OrdinaryTheory.{0, 0, b, h} D ℬ)

/-- Conditional on an eligible theory over the nonfield local ring, the classified family
acts by three on the actual common-target coordinate. No new realization is constructed. -/
theorem mod_four_target_coordinate (r : ZMod 4) :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let g := Cohomology.localQuadraticReconstruction T C Set.univ
      (by simp) (by simp) (by decide) (IncidenceExamples.scalarThreeUnit, 1)
    (Cohomology.targetDegreeOneEquiv T).symm
      (g.targetEquiv (Cohomology.targetDegreeOneEquiv T (Finsupp.single 0 r))) 0 = 3 * r := by
  dsimp only
  rw [Cohomology.localQuadraticReconstruction_target, map_smul,
    LinearEquiv.symm_apply_apply]
  simp [IncidenceExamples.scalarThreeUnit, Finsupp.smul_single, smul_eq_mul]

/-- The nonzero square-zero coefficient survives the actual common-target action. -/
theorem mod_four_nilpotent :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let g := Cohomology.localQuadraticReconstruction T C Set.univ
      (by simp) (by simp) (by decide) (IncidenceExamples.scalarThreeUnit, 1)
    (Cohomology.targetDegreeOneEquiv T).symm
      (g.targetEquiv (Cohomology.targetDegreeOneEquiv T (Finsupp.single 0 2))) 0 = 2 ∧
      (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4)^2 = 0 := by
  refine ⟨(mod_four_target_coordinate T 2).trans (by decide), by decide, by decide⟩

/-- Actual cohomology restriction to the explicit subsystem is invertible, preserving the
same common target, despite the subsystem's failure of union closure. -/
theorem actual_nonUnion_restriction
    (g : Cohomology.DiagramAut T (fullCofinalSystem (ZMod 2) (ZMod 2) 2) Set.univ) :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let e := Cohomology.cofinalRestrictionEquiv T C nonUnionSystem Set.univ
      nonUnionSystem_subset (by simp) (by simp) (by decide)
    e g = Cohomology.DiagramAut.restrictStages T C nonUnionSystem Set.univ
        nonUnionSystem_subset g ∧
    e.symm (Cohomology.DiagramAut.restrictStages T C nonUnionSystem Set.univ
      nonUnionSystem_subset g) = g ∧
    (Cohomology.DiagramAut.restrictStages T C nonUnionSystem Set.univ
      nonUnionSystem_subset g).targetEquiv = g.targetEquiv := by
  exact ⟨Cohomology.cofinalRestrictionEquiv_apply ..,
    Cohomology.cofinalRestrictionEquiv_left_inv .., rfl⟩

/-- The explicit subsystem preserves the entire unit/Galois coordinate of actual graded
reconstruction, rather than merely an abstract isomorphism type. -/
theorem actual_nonUnion_coordinates (p : (ZMod 4)ˣ × (ZMod 2 ≃ₐ[ZMod 2] ZMod 2)) :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    Cohomology.gradedCofinalRestrictionEquiv T C nonUnionSystem Set.univ
      nonUnionSystem_subset (by simp) (by simp) (by decide)
      (Cohomology.localGradedReconstruction T C Set.univ (by simp) (by simp) (by decide) p) =
    Cohomology.localGradedReconstruction T nonUnionSystem Set.univ
      (by simp) (by simp) (by decide) p :=
  Cohomology.gradedCofinalRestrictionEquiv_classification ..

end Nonfield

/-- Pure restriction retains the common target even when every geometric stage is empty.
No dimension-zero classification is asserted. -/
theorem dimension_zero_target (R : Type r) [CommRing R]
    (C : CofinalSystem (ZMod 2) (ZMod 2) 0) (S : Set (ZMod 2))
    (g : DiagramAut R C S) :
    (DiagramAut.restrictStages R C C S (Set.Subset.refl _) g).targetEquiv = g.targetEquiv :=
  DiagramAut.restrictStages_targetEquiv ..

/-- Pure stage restriction is available over the zero ring on the genuine subsystem;
there is no nonzero or local-ring premise on this map. -/
theorem zero_ring_restriction
    (g : GradedDiagramAut (ZMod 1) (fullCofinalSystem (ZMod 2) (ZMod 2) 2) Set.univ) :
    (GradedDiagramAut.restrictStages (ZMod 1) _ nonUnionSystem Set.univ
      nonUnionSystem_subset g).targetEquiv = g.targetEquiv :=
  GradedDiagramAut.restrictStages_targetEquiv ..

section IntegerDomain

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {B : Type b} [CommRing B]
  {ℬ : ℤ → Submodule ℤ B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, 0, b, h} (R := ℤ) (B := B) D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- A supplied eligible integral-coefficient theory is covered without a local-ring
instance on the genuinely nonlocal domain of integers. -/
theorem integer_domain_classification (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : Cohomology.GradedDiagramAut T C S) :
    Cohomology.domainGradedReconstruction T C S hS hgen hn
      ((Cohomology.domainGradedReconstruction T C S hS hgen hn).symm g) = g := by simp

end IntegerDomain


section CharacteristicTwo

variable {k : Type u} [Field k]
  {B : Type b} [CommRing B] [Algebra (ZMod 2) B]
  {ℬ : ℤ → Submodule (ZMod 2) B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, 0, b, h} D ℬ)
  {B' : Type b'} [CommRing B'] [Algebra (ZMod 2) B']
  {ℬ' : ℤ → Submodule (ZMod 2) B'} [GradedAlgebra ℬ'] {D' : Geometric.SmoothDomain k}
  (T' : Geometric.OrdinaryTheory.{u, 0, b', h'} D' ℬ')
  {n : ℕ}

/-- Conditional characteristic-two realizations retain actual alternation and the entire
cup kernel. Alternation comes from the OS theorem, without cancellation of two. -/
theorem charTwo_alternation_and_kernel (A : Arrangement k (Fin n → k))
    (x : Cohomology.degreeOne T A) :
    (x : T.obj (D.complement A)) * (x : T.obj (D.complement A)) = 0 ∧
    (LinearMap.ker (Cohomology.cupMap T A)).map
      (exteriorPower.map 2 (Cohomology.realizationDegreeOneEquiv T T' A).toLinearMap) =
    LinearMap.ker (Cohomology.cupMap T' A) :=
  ⟨Cohomology.degreeOne_mul_self T A x, Cohomology.realizationDegreeOneEquiv_cupKernel T T' A⟩

end CharacteristicTwo

end OrlikSolomon.HyperplaneGT.TheoryReconstructionExamples
