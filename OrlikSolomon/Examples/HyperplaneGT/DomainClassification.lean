/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.Data.ZMod.Basic

/-!
# Integral coefficient and scalar quotient regressions

The original common-target matrix recovers a unit in the coefficient domain itself.
The integer-coefficient example is genuinely nonlocal and nonidentity, while geometric
characteristic two is harmless. Strict independent-universe consumers retain ordinary
inverse cancellation, both explicit scalar quotient sections, the actual quotient restriction
square, all-degree scalar powers and agreement with local classification.

Pure coefficient extension is also tested along noninjective reduction modulo two and the
map to the zero ring; these constructions do not require domain coefficients.

Blueprint: S05 (`thm:s05`) and its coefficient-change regression requirements.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DomainClassificationExamples

universe u v r
variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  {R : Type r} [CommRing R] [IsDomain R] {C : CofinalSystem k₀ k n} {S : Set k₀}
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Both primal coordinates cancel under the canonical classification. -/
theorem classification_left_inverse (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (coefficientDomainAutEquiv R C S hS hgen hn).symm
      (coefficientDomainAutEquiv R C S hS hgen hn p) = p := by simp

/-- The classified inverse recovers every component of an actual quadratic diagram. -/
theorem classification_right_inverse (g : DiagramAut R C S) :
    coefficientDomainAutEquiv R C S hS hgen hn
      ((coefficientDomainAutEquiv R C S hS hgen hn).symm g) = g := by simp

include hS hgen hn in
/-- An entry of the original common-target matrix is a unit of the original ring. -/
theorem original_target_entry_isUnit (g : DiagramAut R C S) :
    IsUnit (g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0) := by
  rw [← DiagramAut.domainScalarPart_val g hS hgen hn]
  exact Units.isUnit _

include hS hgen hn in
/-- The whole common target is scalar over the nonlocal coefficient ring of integers. -/
theorem integer_target_scalar (g : DiagramAut ℤ C S) :
    ∃ u : ℤˣ, ∀ x : Fin 2 →₀ ℤ, g.targetEquiv x = (u : ℤ) • x := by
  obtain ⟨⟨u, σ⟩, rfl⟩ := (coefficientDomainAutEquiv ℤ C S hS hgen hn).surjective g
  exact ⟨u, coefficientDomainAutEquiv_targetEquiv_apply ℤ C S hS hgen hn u σ⟩

/-- Local and domain classification agree as complete equivalences. -/
theorem local_overlap [IsLocalRing R] :
    coefficientDomainAutEquiv R C S hS hgen hn = quadraticAutEquiv R C S hS hgen hn := by
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv]

/-- The actual full cofinal system admits a nonidentity integer-coefficient scalar diagram.
The nonzero target entry detects it even though the geometric field has characteristic two.
-/
theorem integer_scalar_nonidentity :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    let g := coefficientDomainAutEquiv ℤ C S (by simp [S]) hgen (by decide)
      (-1, 1)
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 = -1 ∧ g ≠ 1 := by
  dsimp only
  let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
  let S : Set (ZMod 2) := {0}
  have hS : (0 : ZMod 2) ∈ S := by simp [S]
  have hg : Subfield.closure S = ⊤ := Subsingleton.elim _ _
  refine ⟨by simp, ?_⟩
  intro he
  have hv := congrArg (fun g : DiagramAut ℤ C S ↦
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0) he
  rw [coefficientDomainAutEquiv_targetEquiv_apply] at hv
  norm_num at hv

/-- The actual graded restriction and full classification retain bare simp cancellation. -/
theorem graded_cancellation (g : GradedDiagramAut R C S) (q : DiagramAut R C S)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (coefficientDomainGradedAutEquiv R C S hS hgen hn).symm
        (coefficientDomainGradedAutEquiv R C S hS hgen hn g) = g ∧
      coefficientDomainGradedAutEquiv R C S hS hgen hn
        ((coefficientDomainGradedAutEquiv R C S hS hgen hn).symm q) = q ∧
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm
        (coefficientDomainGradedClassificationEquiv R C S hS hgen hn p) = p ∧
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn
        ((coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm g) = g := by simp

/-- Both scalar quotients cancel their existing Galois sections in both directions. -/
theorem quotient_inverse_sections (σ : k ≃ₐ[k₀] k)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
    (r : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
        (DiagramAut.scalarQuotientSection R C S σ) = σ ∧
      DiagramAut.scalarQuotientSection R C S
        (DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn q) = q ∧
      GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
        (GradedDiagramAut.scalarQuotientSection R C S σ) = σ ∧
      GradedDiagramAut.scalarQuotientSection R C S
        (GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn r) = r := by
  exact ⟨DiagramAut.domainScalarQuotientEquiv_section R C S hS hgen hn σ,
    DiagramAut.domainScalarQuotientSection_equiv R C S hS hgen hn q,
    GradedDiagramAut.domainScalarQuotientEquiv_section R C S hS hgen hn σ,
    GradedDiagramAut.domainScalarQuotientSection_equiv R C S hS hgen hn r⟩

/-- Quotient restriction is the actual degree-one restriction, with the same Galois output.
-/
theorem quotient_restriction_square
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (domainScalarQuotientRestrictionEquiv R C S hS hgen hn q) =
        GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn q := by
  rw [domainScalarQuotientEquiv_restriction]

/-- The classified family scales the entire ordinary component, with independent universes.
-/
theorem whole_degree_action (a : Rˣ) (σ : k ≃ₐ[k₀] k) (B : C.Stage) (q : ℕ)
    (x : OSAlgebra R B.val.val) (hx : x ∈ OSAlgebra.degree R B.val.val q) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv B x =
      (a : R) ^ q • galoisOSAlgebraEquiv R B.val σ x := by
  rw [coefficientDomainGradedClassificationEquiv_stage_apply_of_mem_degree
    R C S hS hgen hn a σ B q x hx]

/-- Local and domain full classifications and both quotient equivalences agree exactly. -/
theorem full_local_overlap [IsLocalRing R] :
    coefficientDomainGradedAutEquiv R C S hS hgen hn = gradedAutEquiv R C S hS hgen hn ∧
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn =
        gradedClassificationEquiv R C S hS hgen hn ∧
      DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn =
        DiagramAut.scalarQuotientEquiv R C S hS hgen hn ∧
      GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn =
        GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn := by
  exact ⟨coefficientDomainGradedAutEquiv_eq_gradedAutEquiv R C S hS hgen hn,
    coefficientDomainGradedClassificationEquiv_eq_gradedClassificationEquiv R C S hS hgen hn,
    DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn,
    GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv R C S hS hgen hn⟩

/-- Reduction modulo two preserves the actual relation span without an injective coefficient
map. This consumer uses the original full quadratic relation equality. -/
theorem noninjective_coefficient_relations (g : DiagramAut ℤ C S) (B : C.Stage) :
    (quadraticRelationSpan (ZMod 2) B.val.val).map
      (exteriorPower.map 2
        ((DiagramAut.coefficientExtend ℤ C S (ZMod 2) g).stageEquiv B).toLinearMap) =
      quadraticRelationSpan (ZMod 2) B.val.val :=
  (DiagramAut.coefficientExtend ℤ C S (ZMod 2) g).map_quadraticRelationSpan B

/-- The whole-target coefficient square remains valid after passing to the zero ring. -/
theorem zero_coefficient_target (g : DiagramAut ℤ C S) (x : Fin 2 →₀ ℤ) :
    (DiagramAut.coefficientExtend ℤ C S (ZMod 1) g).targetEquiv
      (Finsupp.mapRange.linearMap (Algebra.linearMap ℤ (ZMod 1)) x) = 0 := by
  rw [DiagramAut.coefficientExtend_target_mapRange]
  exact Subsingleton.elim _ _

end OrlikSolomon.HyperplaneGT.DomainClassificationExamples
