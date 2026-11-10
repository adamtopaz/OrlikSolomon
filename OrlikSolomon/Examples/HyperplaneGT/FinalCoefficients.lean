/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quotient
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import OrlikSolomon.Examples.HyperplaneGT.Local
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Final classification over binary and nilpotent coefficients

These consumers instantiate the final quadratic and full graded classifications, their
literal degree-one restriction and both quotients by the actual scalar ranges over `𝔽₂`
and `𝔽₂[ε]/(ε²)`. The latter ring has a nonzero nilpotent and the nonidentity unit `1 + ε`.
The unit remains visible on the one common target, and its powers act in every ordinary
degree. Actual tagged marking maps are retained. Complex conjugation gives a genuinely
nonidentity class in each quotient, using the full stable cofinal system and the generating
marking set `univ`.

These are pure presentation-diagram consumers; no cohomology realization is assumed.
Blueprint: final coefficient regressions for S03–S04 and milestone acceptance.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.FinalCoefficientExamples

universe u v

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (C : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Both classifications and literal restriction have ordinary two-sided inverse laws
with binary coefficients. -/
theorem binary_classification_inverse_forms
    (p : (ZMod 2)ˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut (ZMod 2) C S)
    (f : GradedDiagramAut (ZMod 2) C S) :
    (quadraticAutEquiv (ZMod 2) C S hS hgen hn).symm
      (quadraticAutEquiv (ZMod 2) C S hS hgen hn p) = p ∧
    quadraticAutEquiv (ZMod 2) C S hS hgen hn
      ((quadraticAutEquiv (ZMod 2) C S hS hgen hn).symm g) = g ∧
    (gradedClassificationEquiv (ZMod 2) C S hS hgen hn).symm
      (gradedClassificationEquiv (ZMod 2) C S hS hgen hn p) = p ∧
    gradedClassificationEquiv (ZMod 2) C S hS hgen hn
      ((gradedClassificationEquiv (ZMod 2) C S hS hgen hn).symm f) = f ∧
    (gradedAutEquiv (ZMod 2) C S hS hgen hn).symm
      (gradedAutEquiv (ZMod 2) C S hS hgen hn f) = f ∧
    gradedAutEquiv (ZMod 2) C S hS hgen hn
      ((gradedAutEquiv (ZMod 2) C S hS hgen hn).symm g) = g := by simp

/-- Both literal scalar quotients retain their explicit Galois sections and both inverse
laws with binary coefficients. -/
theorem binary_quotient_sections (σ : k ≃ₐ[k₀] k)
    (q : DiagramAut (ZMod 2) C S ⧸ DiagramAut.scalarSubgroup (ZMod 2) C S)
    (t : GradedDiagramAut (ZMod 2) C S ⧸ GradedDiagramAut.scalarSubgroup (ZMod 2) C S) :
    DiagramAut.scalarQuotientEquiv (ZMod 2) C S hS hgen hn
      (DiagramAut.scalarQuotientSection (ZMod 2) C S σ) = σ ∧
    DiagramAut.scalarQuotientSection (ZMod 2) C S
      (DiagramAut.scalarQuotientEquiv (ZMod 2) C S hS hgen hn q) = q ∧
    GradedDiagramAut.scalarQuotientEquiv (ZMod 2) C S hS hgen hn
      (GradedDiagramAut.scalarQuotientSection (ZMod 2) C S σ) = σ ∧
    GradedDiagramAut.scalarQuotientSection (ZMod 2) C S
      (GradedDiagramAut.scalarQuotientEquiv (ZMod 2) C S hS hgen hn t) = t := by
  exact ⟨DiagramAut.scalarQuotientEquiv_section _ _ _ hS hgen hn σ,
    DiagramAut.scalarQuotientSection_equiv _ _ _ hS hgen hn q,
    GradedDiagramAut.scalarQuotientEquiv_section _ _ _ hS hgen hn σ,
    GradedDiagramAut.scalarQuotientSection_equiv _ _ _ hS hgen hn t⟩

/-- Both classifications and literal restriction have ordinary two-sided inverse laws
with characteristic-two dual-number coefficients. -/
theorem dual_number_classification_inverse_forms
    (p : (DualNumber (ZMod 2))ˣ × (k ≃ₐ[k₀] k)) (g : DiagramAut (DualNumber (ZMod 2)) C S)
    (f : GradedDiagramAut (DualNumber (ZMod 2)) C S) :
    (quadraticAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm
      (quadraticAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn p) = p ∧
    quadraticAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      ((quadraticAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm g) = g ∧
    (gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm
      (gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn p) = p ∧
    gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      ((gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm f) = f ∧
    (gradedAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm
      (gradedAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn f) = f ∧
    gradedAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      ((gradedAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn).symm g) = g := by simp

/-- Both literal scalar quotients retain their explicit Galois sections and both inverse
laws with characteristic-two dual-number coefficients. -/
theorem dual_number_quotient_sections (σ : k ≃ₐ[k₀] k)
    (q : DiagramAut (DualNumber (ZMod 2)) C S ⧸ DiagramAut.scalarSubgroup (DualNumber (ZMod 2)) C S)
    (t : GradedDiagramAut (DualNumber (ZMod 2)) C S
      ⧸ GradedDiagramAut.scalarSubgroup (DualNumber (ZMod 2)) C S) :
    DiagramAut.scalarQuotientEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (DiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) C S σ) = σ ∧
    DiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) C S
      (DiagramAut.scalarQuotientEquiv (DualNumber (ZMod 2)) C S hS hgen hn q) = q ∧
    GradedDiagramAut.scalarQuotientEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (GradedDiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) C S σ) = σ ∧
    GradedDiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) C S
      (GradedDiagramAut.scalarQuotientEquiv (DualNumber (ZMod 2)) C S hS hgen hn t) = t := by
  exact ⟨DiagramAut.scalarQuotientEquiv_section _ _ _ hS hgen hn σ,
    DiagramAut.scalarQuotientSection_equiv _ _ _ hS hgen hn q,
    GradedDiagramAut.scalarQuotientEquiv_section _ _ _ hS hgen hn σ,
    GradedDiagramAut.scalarQuotientSection_equiv _ _ _ hS hgen hn t⟩

/-- Binary full restriction is literally the existing degree-one map. -/
theorem binary_literal_restriction (g : GradedDiagramAut (ZMod 2) C S) :
    gradedAutEquiv (ZMod 2) C S hS hgen hn g =
      GradedDiagramAut.toQuadratic (ZMod 2) C S g := by rw [gradedAutEquiv_apply]

/-- Binary scalar-quotient restriction is induced by the literal full restriction. -/
theorem binary_quotient_restriction (g : GradedDiagramAut (ZMod 2) C S) :
    scalarQuotientRestrictionEquiv (ZMod 2) C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap (ZMod 2) C S g) =
    DiagramAut.scalarQuotientMap (ZMod 2) C S (GradedDiagramAut.toQuadratic (ZMod 2) C S g) := by
  rw [scalarQuotientRestrictionEquiv_map]

/-- The same actual square holds over the nonfield local dual-number ring. -/
theorem dual_number_quotient_restriction (g : GradedDiagramAut (DualNumber (ZMod 2)) C S) :
    scalarQuotientRestrictionEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap (DualNumber (ZMod 2)) C S g) =
    DiagramAut.scalarQuotientMap (DualNumber (ZMod 2)) C S
      (GradedDiagramAut.toQuadratic (DualNumber (ZMod 2)) C S g) := by
  rw [scalarQuotientRestrictionEquiv_map]

/-- The actual full common-target logarithmic class carries the nonidentity nilpotent unit.
No component of the target is replaced or discarded. -/
theorem dual_number_full_common_target (σ : k ≃ₐ[k₀] k) (H : twoPunctureArrangement k) :
    (gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (LocalExamples.dualNumberUnit, σ)).targetEquiv
        (OSAlgebra.generator (DualNumber (ZMod 2)) (twoPunctureArrangement k) H) =
    (LocalExamples.dualNumberUnit : DualNumber (ZMod 2)) •
      OSAlgebra.generator (DualNumber (ZMod 2)) (twoPunctureArrangement k) H := by
  obtain ⟨i, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
  exact gradedClassificationEquiv_target_generator _ _ _ hS hgen hn _ σ i

/-- The nilpotent unit acts by its degree power on the whole ordinary summand. -/
theorem dual_number_whole_degree (σ : k ≃ₐ[k₀] k) (A : C.Stage) (q : ℕ)
    (x : OSAlgebra (DualNumber (ZMod 2)) A.val.val)
    (hx : x ∈ OSAlgebra.degree (DualNumber (ZMod 2)) A.val.val q) :
    (gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (LocalExamples.dualNumberUnit, σ)).stageEquiv A x =
    (LocalExamples.dualNumberUnit : DualNumber (ZMod 2))^q •
      galoisOSAlgebraEquiv (DualNumber (ZMod 2)) A.val σ x := by
  rw [gradedClassificationEquiv_stage_apply_of_mem_degree
    (DualNumber (ZMod 2)) C S hS hgen hn LocalExamples.dualNumberUnit σ A q x hx]

/-- Every actual full tagged marking map uses the same common target under the nilpotent
coefficient classification. -/
theorem dual_number_marking (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : OSAlgebra (DualNumber (ZMod 2)) (twoPunctureArrangement k)) :
    (gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn
      (LocalExamples.dualNumberUnit, σ)).stageEquiv A (w.osMap (DualNumber (ZMod 2)) hw x) =
    w.osMap (DualNumber (ZMod 2)) hw
      ((gradedClassificationEquiv (DualNumber (ZMod 2)) C S hS hgen hn
        (LocalExamples.dualNumberUnit, σ)).targetEquiv x) := by
  rw [gradedClassificationEquiv_marking]

/-- Restriction is exactly the existing degree-one map over the nilpotent coefficient ring,
including the common target rather than merely the stage components. -/
theorem dual_number_literal_restriction (g : GradedDiagramAut (DualNumber (ZMod 2)) C S) :
    gradedAutEquiv (DualNumber (ZMod 2)) C S hS hgen hn g =
      GradedDiagramAut.toQuadratic (DualNumber (ZMod 2)) C S g := by
  rw [gradedAutEquiv_apply]

/-- The final classified common target detects the nonidentity nilpotent unit, even with
an explicit nontrivial geometric Galois factor. -/
theorem dual_number_common_target :
    let C := fullCofinalSystem ℝ ℂ 2
    let g := quadraticAutEquiv (DualNumber (ZMod 2)) C Set.univ
      (by trivial) (by simp) (by decide) (LocalExamples.dualNumberUnit, Complex.conjAe)
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 =
        (LocalExamples.dualNumberUnit : DualNumber (ZMod 2)) ∧
    g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 ≠ 1 ∧
    (DualNumber.eps : DualNumber (ZMod 2)) ≠ 0 ∧
    (DualNumber.eps : DualNumber (ZMod 2))^2 = 0 := by
  dsimp only
  rw [quadraticAutEquiv_targetEquiv_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  exact ⟨trivial, LocalExamples.dualNumberUnit_ne_one, LocalExamples.binary_dual_number_nilpotent⟩

private theorem conjugation_quotients (R : Type*) [CommRing R] [IsLocalRing R] :
    DiagramAut.scalarQuotientSection R (fullCofinalSystem ℝ ℂ 2) Set.univ Complex.conjAe ≠ 1 ∧
    GradedDiagramAut.scalarQuotientSection R (fullCofinalSystem ℝ ℂ 2) Set.univ
      Complex.conjAe ≠ 1 := by
  have hconj : Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) := by
    intro he
    have him := congrArg Complex.im (AlgEquiv.congr_fun he Complex.I)
    norm_num at him
  constructor
  · intro he
    apply hconj
    have h := DiagramAut.scalarQuotientEquiv_section R (fullCofinalSystem ℝ ℂ 2) Set.univ
      (by trivial) (by simp) (by decide) Complex.conjAe
    rw [he, map_one] at h
    exact h.symm
  · intro he
    apply hconj
    have h := GradedDiagramAut.scalarQuotientEquiv_section R (fullCofinalSystem ℝ ℂ 2) Set.univ
      (by trivial) (by simp) (by decide) Complex.conjAe
    rw [he, map_one] at h
    exact h.symm

/-- Complex conjugation remains nontrivial in both final scalar quotients with binary
coefficients, using genuine generating markings on the actual full cofinal system. -/
theorem binary_conjugation_quotients :
    DiagramAut.scalarQuotientSection (ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ
      Complex.conjAe ≠ 1 ∧
    GradedDiagramAut.scalarQuotientSection (ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ
      Complex.conjAe ≠ 1 := conjugation_quotients (ZMod 2)

/-- The same genuine Galois class survives both scalar quotients over the nonfield local
ring of characteristic-two dual numbers. -/
theorem dual_number_conjugation_quotients :
    DiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) (fullCofinalSystem ℝ ℂ 2) Set.univ
      Complex.conjAe ≠ 1 ∧
    GradedDiagramAut.scalarQuotientSection (DualNumber (ZMod 2)) (fullCofinalSystem ℝ ℂ 2) Set.univ
      Complex.conjAe ≠ 1 := conjugation_quotients (DualNumber (ZMod 2))

end OrlikSolomon.HyperplaneGT.FinalCoefficientExamples
