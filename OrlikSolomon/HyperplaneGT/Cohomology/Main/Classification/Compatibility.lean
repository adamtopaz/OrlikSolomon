/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Cofinal

/-!
# Compatibility of actual reconstruction, restriction and scalar quotients

The two actual scalar quotients commute with literal degree-one restriction. Cofinal
restriction preserves their Galois coordinates and the same classified scalar/Galois pair.
These are consequences of reconstruction, not extension assumptions on arbitrary families.
This size leaf belongs to the E01 classification interface.

Blueprint: E01–E02 (`thm:e01`, `cor:e02`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

section
variable [IsLocalRing R]

/-- Actual degree-one restriction induces the canonical equivalence of the two literal
scalar quotients. Blueprint: E01 (`thm:e01`). -/
def localScalarQuotientRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃*
      (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :=
  (GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn).trans
    (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).symm

/-- On representatives, scalar-quotient restriction is the literal actual restriction. -/
@[simp]
theorem localScalarQuotientRestrictionEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientRestrictionEquiv T C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
    DiagramAut.scalarQuotientMap T C S (GradedDiagramAut.toQuadratic T C S g) := by
  apply (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).injective
  simp only [localScalarQuotientRestrictionEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, DiagramAut.localScalarQuotientEquiv_map,
    GradedDiagramAut.localScalarQuotientEquiv_map]
  obtain ⟨p, rfl⟩ := (localGradedReconstruction T C S hS hgen hn).surjective g
  rw [toQuadratic_localGradedReconstruction, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

/-- Both actual scalar-quotient classifications have the same Galois coordinate. -/
theorem localScalarQuotientEquiv_restriction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    DiagramAut.localScalarQuotientEquiv T C S hS hgen hn
      (localScalarQuotientRestrictionEquiv T C S hS hgen hn q) =
    GradedDiagramAut.localScalarQuotientEquiv T C S hS hgen hn q :=
  (DiagramAut.localScalarQuotientEquiv T C S hS hgen hn).apply_symm_apply _

/-- Literal degree-one restriction followed by its classified inverse recovers the entire
actual graded automorphism. -/
theorem localRestrictionEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (localRestrictionEquiv T C S hS hgen hn).symm
      (GradedDiagramAut.toQuadratic T C S g) = g := by
  rw [← localRestrictionEquiv_apply]
  exact (localRestrictionEquiv T C S hS hgen hn).symm_apply_apply g

/-- Classified extension followed by actual restriction recovers the whole quadratic family.
-/
theorem localRestrictionEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    GradedDiagramAut.toQuadratic T C S ((localRestrictionEquiv T C S hS hgen hn).symm g) = g := by
  rw [← localRestrictionEquiv_apply]
  exact (localRestrictionEquiv T C S hS hgen hn).apply_symm_apply g

/-- Cofinal restriction preserves the actual scalar-quotient Galois coordinate. -/
theorem DiagramAut.localScalarQuotientEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    localScalarQuotientEquiv T C' S hS hgen hn
      (scalarQuotientMap T C' S (restrictStages T C C' S hC g)) =
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) := by
  rw [localScalarQuotientEquiv_map, localScalarQuotientEquiv_map]
  have he := congrArg (localQuadraticReconstruction T C' S hS hgen hn).symm
    (restrictStages_localQuadraticReconstruction T C C' S hC hS hgen hn
      ((localQuadraticReconstruction T C S hS hgen hn).symm g))
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using congrArg Prod.snd he

/-- Cofinal restriction preserves the actual scalar-quotient Galois coordinate. -/
theorem GradedDiagramAut.localScalarQuotientEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientEquiv T C' S hS hgen hn
      (scalarQuotientMap T C' S (restrictStages T C C' S hC g)) =
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) := by
  rw [localScalarQuotientEquiv_map, localScalarQuotientEquiv_map]
  have he := congrArg (localGradedReconstruction T C' S hS hgen hn).symm
    (restrictStages_localGradedReconstruction T C C' S hC hS hgen hn
      ((localGradedReconstruction T C S hS hgen hn).symm g))
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using congrArg Prod.snd he

end

section
variable [IsDomain R]

/-- Actual degree-one restriction induces the canonical equivalence of the two literal
scalar quotients. Blueprint: E01 (`thm:e01`). -/
def domainScalarQuotientRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃*
      (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :=
  (GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).trans
    (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).symm

/-- On representatives, scalar-quotient restriction is the literal actual restriction. -/
@[simp]
theorem domainScalarQuotientRestrictionEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientRestrictionEquiv T C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap T C S g) =
    DiagramAut.scalarQuotientMap T C S (GradedDiagramAut.toQuadratic T C S g) := by
  apply (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).injective
  simp only [domainScalarQuotientRestrictionEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, DiagramAut.domainScalarQuotientEquiv_map,
    GradedDiagramAut.domainScalarQuotientEquiv_map]
  obtain ⟨p, rfl⟩ := (domainGradedReconstruction T C S hS hgen hn).surjective g
  rw [toQuadratic_domainGradedReconstruction, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

/-- Both actual scalar-quotient classifications have the same Galois coordinate. -/
theorem domainScalarQuotientEquiv_restriction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :
    DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn
      (domainScalarQuotientRestrictionEquiv T C S hS hgen hn q) =
    GradedDiagramAut.domainScalarQuotientEquiv T C S hS hgen hn q :=
  (DiagramAut.domainScalarQuotientEquiv T C S hS hgen hn).apply_symm_apply _

/-- Literal degree-one restriction followed by its classified inverse recovers the entire
actual graded automorphism. -/
theorem domainRestrictionEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (domainRestrictionEquiv T C S hS hgen hn).symm
      (GradedDiagramAut.toQuadratic T C S g) = g := by
  rw [← domainRestrictionEquiv_apply]
  exact (domainRestrictionEquiv T C S hS hgen hn).symm_apply_apply g

/-- Classified extension followed by actual restriction recovers the whole quadratic family.
-/
theorem domainRestrictionEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    GradedDiagramAut.toQuadratic T C S ((domainRestrictionEquiv T C S hS hgen hn).symm g) = g := by
  rw [← domainRestrictionEquiv_apply]
  exact (domainRestrictionEquiv T C S hS hgen hn).apply_symm_apply g

/-- Cofinal restriction preserves the actual scalar-quotient Galois coordinate. -/
theorem DiagramAut.domainScalarQuotientEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainScalarQuotientEquiv T C' S hS hgen hn
      (scalarQuotientMap T C' S (restrictStages T C C' S hC g)) =
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) := by
  rw [domainScalarQuotientEquiv_map, domainScalarQuotientEquiv_map]
  have he := congrArg (domainQuadraticReconstruction T C' S hS hgen hn).symm
    (restrictStages_domainQuadraticReconstruction T C C' S hC hS hgen hn
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g))
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using congrArg Prod.snd he

/-- Cofinal restriction preserves the actual scalar-quotient Galois coordinate. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_restrictStages (C' : CofinalSystem k₀ k n)
    (hC : C'.stages ⊆ C.stages) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientEquiv T C' S hS hgen hn
      (scalarQuotientMap T C' S (restrictStages T C C' S hC g)) =
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) := by
  rw [domainScalarQuotientEquiv_map, domainScalarQuotientEquiv_map]
  have he := congrArg (domainGradedReconstruction T C' S hS hgen hn).symm
    (restrictStages_domainGradedReconstruction T C C' S hC hS hgen hn
      ((domainGradedReconstruction T C S hS hgen hn).symm g))
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using congrArg Prod.snd he

end

end OrlikSolomon.HyperplaneGT.Cohomology
