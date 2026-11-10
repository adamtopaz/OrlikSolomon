/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quotient
public import OrlikSolomon.Examples.AffineLines
public import OrlikSolomon.Examples.HyperplaneGT.Dual
public import OrlikSolomon.Examples.HyperplaneGT.Local
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Graded classification and scalar quotient regressions

A nonzero degree-two triangle boundary distinguishes the square of a non-involutive unit
from its degree-one scalar. Nilpotent local coefficients and characteristic-two dual
numbers retain the full scalar action. Pure scalar families retain the common target in
dimension zero and exist with zero coefficients. Both restriction and quotient equivalences
have ordinary two-sided cancellation, and complex conjugation gives a nonidentity class
in both actual scalar quotients. No trivial-Galois or nonzero-theory premise is substituted.

Blueprint: regression consumers for S04 (`thm:s04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.GradedClassificationExamples

open OSAlgebra

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  {R : Type w} [CommRing R] [IsLocalRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- Ordinary equivalence cancellation holds in both directions for restriction and the full
classification, with independent field/coefficient universes. -/
theorem restriction_classification_cancellation (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) (h : DiagramAut R C S) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (gradedAutEquiv R C S hS hgen hn).symm (gradedAutEquiv R C S hS hgen hn g) = g ∧
      gradedAutEquiv R C S hS hgen hn ((gradedAutEquiv R C S hS hgen hn).symm h) = h ∧
      (gradedClassificationEquiv R C S hS hgen hn).symm
        (gradedClassificationEquiv R C S hS hgen hn p) = p ∧
      gradedClassificationEquiv R C S hS hgen hn
        ((gradedClassificationEquiv R C S hS hgen hn).symm g) = g := by simp

/-- Both literal scalar quotients retain ordinary inverse cancellation and the explicit
direct Galois section. -/
theorem quotient_inverse_sections (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k)
    (q : DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S)
    (r : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    DiagramAut.scalarQuotientEquiv R C S hS hgen hn
        (DiagramAut.scalarQuotientSection R C S σ) = σ ∧
      DiagramAut.scalarQuotientSection R C S
        (DiagramAut.scalarQuotientEquiv R C S hS hgen hn q) = q ∧
      GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
        (GradedDiagramAut.scalarQuotientSection R C S σ) = σ ∧
      GradedDiagramAut.scalarQuotientSection R C S
        (GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn r) = r := by
  exact ⟨DiagramAut.scalarQuotientEquiv_section R C S hS hgen hn σ,
    DiagramAut.scalarQuotientSection_equiv R C S hS hgen hn q,
    GradedDiagramAut.scalarQuotientEquiv_section R C S hS hgen hn σ,
    GradedDiagramAut.scalarQuotientSection_equiv R C S hS hgen hn r⟩

/-- The actual full classified family uses one target on the entire tagged marking algebra.
-/
theorem full_marking_square (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤)
    (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv A (w.osMap R hw x) =
      w.osMap R hw ((gradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv x) := by
  rw [gradedClassificationEquiv_marking]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The nonzero signed degree-two boundary of the actual binary affine triangle. -/
def triangleBoundary :
    OSAlgebra (ZMod 5) (AffineLineExamples.triangle (ZMod 2)) :=
  wordBoundary (generator (ZMod 5) _) [AffineLineExamples.t1, AffineLineExamples.t2,
    AffineLineExamples.t3]

private theorem triangleBoundary_ne_zero : triangleBoundary ≠ 0 := by
  simpa only [triangleBoundary, wordBoundary_triple] using
    (AffineLineExamples.triangle_boundary_ne (k := ZMod 2) (ZMod 5))

private theorem triangleBoundary_mem_degree :
    triangleBoundary ∈ degree (ZMod 5) (AffineLineExamples.triangle (ZMod 2)) 2 :=
  wordBoundary_mem_degree (ZMod 5) _ [AffineLineExamples.t1, AffineLineExamples.t2,
    AffineLineExamples.t3]

/-- A genuine nonzero degree-two class is scaled by four, not two, by the scalar-two full
automorphism. This distinguishes ordinary degree scaling from uniform scaling of all elements.
-/
theorem nonzero_degree_two_square :
    scalarEquiv (ZMod 5) (AffineLineExamples.triangle (ZMod 2))
        DualExamples.scalarTwoUnit triangleBoundary = (4 : ZMod 5) • triangleBoundary ∧
      triangleBoundary ≠ 0 ∧
      (4 : ZMod 5) • triangleBoundary ≠ (2 : ZMod 5) • triangleBoundary := by
  refine ⟨?_, triangleBoundary_ne_zero, ?_⟩
  · rw [scalarEquiv_apply_of_mem_degree _ _ _ 2 _ triangleBoundary_mem_degree]
    rfl
  · intro he
    have hz : (2 : ZMod 5) • triangleBoundary = 0 := by
      have hsub : ((4 : ZMod 5) - 2) • triangleBoundary = 0 := by
        rw [sub_smul, he, sub_self]
      exact (show (4 : ZMod 5) - 2 = 2 from by decide) ▸ hsub
    have h := congrArg (fun x ↦ (3 : ZMod 5) • x) hz
    rw [smul_smul, show (3 : ZMod 5) * 2 = 1 from by decide, one_smul, smul_zero] at h
    exact triangleBoundary_ne_zero h

/-- A nontrivial characteristic-two dual-number unit squares to one. Its full action is
therefore the identity on every degree-two component, including over infinite-dimensional
geometry, while the coefficient unit itself is nonidentity and has a nonzero nilpotent part.
-/
theorem binary_nilpotent_degree_two {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] (A : Arrangement k V)
    (x : OSAlgebra (DualNumber (ZMod 2)) A)
    (hx : x ∈ degree (DualNumber (ZMod 2)) A 2) :
    scalarEquiv (DualNumber (ZMod 2)) A LocalExamples.dualNumberUnit x = x ∧
      (LocalExamples.dualNumberUnit : DualNumber (ZMod 2)) ≠ 1 := by
  refine ⟨?_, LocalExamples.dualNumberUnit_ne_one⟩
  rw [scalarEquiv_apply_of_mem_degree _ _ _ 2 _ hx]
  have hp : (LocalExamples.dualNumberUnit : DualNumber (ZMod 2)) ^ 2 = 1 := by
    ext <;> norm_num [LocalExamples.dualNumberUnit, pow_two]
    decide
  rw [hp, one_smul]

/-- The full scalar action fixes degree zero even with the zero coefficient ring. -/
theorem zero_coeff_degree_zero {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] (A : Arrangement k V)
    (a : (ZMod 1)ˣ) (x : OSAlgebra (ZMod 1) A) (hx : x ∈ degree (ZMod 1) A 0) :
    scalarEquiv (ZMod 1) A a x = x := by
  rw [scalarEquiv_apply_of_mem_degree _ _ _ 0 _ hx, pow_zero, one_smul]

local instance : IsLocalRing (ZMod 4) := by
  change IsLocalRing (ZMod (2 ^ 2))
  infer_instance

/-- The actual restriction inverse extends a nontrivial quadratic scalar over the nonfield
local ring `ℤ/4`, retaining its common target and the nonzero nilpotent coefficient two. -/
theorem mod_four_full_extension :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
    let S : Set (ZMod 2) := {0}
    let hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
    let g := (gradedAutEquiv (ZMod 4) C S (by simp [S]) hgen (by decide)).symm
      (scalarQuadraticAut (ZMod 4) C S LocalExamples.modFourUnit)
    g = scalarGradedAut (ZMod 4) C S LocalExamples.modFourUnit ∧
      (GradedDiagramAut.toQuadratic (ZMod 4) C S g).targetEquiv (Finsupp.single 0 1) 0 = 3 ∧
      g ≠ 1 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 := by
  dsimp only
  let C := fullCofinalSystem (ZMod 2) (ZMod 2) 2
  let S : Set (ZMod 2) := {0}
  have hS : (0 : ZMod 2) ∈ S := by simp [S]
  have hgen : Subfield.closure S = ⊤ := Subsingleton.elim _ _
  let e := gradedAutEquiv (ZMod 4) C S hS hgen (by decide)
  have hg : e.symm (scalarQuadraticAut (ZMod 4) C S LocalExamples.modFourUnit) =
      scalarGradedAut (ZMod 4) C S LocalExamples.modFourUnit := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (toQuadratic_scalarGradedAut (ZMod 4) C S LocalExamples.modFourUnit).symm
  refine ⟨hg, ?_, ?_, by decide, by decide⟩
  · rw [hg, toQuadratic_scalarGradedAut, scalarQuadraticAut_targetEquiv_apply]
    simp [LocalExamples.modFourUnit]
  · intro he
    have hv := congrArg (fun f : GradedDiagramAut (ZMod 4) C S ↦
      (GradedDiagramAut.toQuadratic (ZMod 4) C S f).targetEquiv
        (Finsupp.single (0 : Fin 2) 1) 0) he
    rw [hg, toQuadratic_scalarGradedAut] at hv
    have hz : (3 : ZMod 4) = 1 := by simpa [LocalExamples.modFourUnit] using hv
    exact (by decide : (3 : ZMod 4) ≠ 1) hz

/-- With no geometric labels in dimension zero, the same common target still detects the
nonidentity full scalar family. This uses only the pure construction, not reconstruction.
-/
theorem dimension_zero_common_target :
    let C := fullCofinalSystem (ZMod 2) (ZMod 2) 0
    let g := scalarGradedAut (ZMod 5) C ∅ DualExamples.scalarTwoUnit
    (GradedDiagramAut.toQuadratic (ZMod 5) C ∅ g).targetEquiv
        (Finsupp.single 0 1) 0 = 2 ∧ g ≠ 1 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [toQuadratic_scalarGradedAut, scalarQuadraticAut_targetEquiv_apply]
    simp [DualExamples.scalarTwoUnit]
  · intro he
    have hs : scalarGradedAction (ZMod 5) (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅
        DualExamples.scalarTwoUnit = scalarGradedAction (ZMod 5)
          (fullCofinalSystem (ZMod 2) (ZMod 2) 0) ∅ 1 := by simpa using he
    have hu := scalarGradedAction_injective _ _ _ hs
    have hv := congrArg Units.val hu
    exact (by decide : (2 : ZMod 5) ≠ 1) hv

/-- Complex conjugation gives a nonidentity element in each actual scalar quotient. The
explicit sections retain the nontrivial Galois factor, with a supplied cofinal system and
the genuinely generating marking set `univ`. -/
theorem conjugation_quotient_sections_nontrivial (C : CofinalSystem ℝ ℂ 2) :
    DiagramAut.scalarQuotientSection (ZMod 5) C Set.univ Complex.conjAe ≠ 1 ∧
      GradedDiagramAut.scalarQuotientSection (ZMod 5) C Set.univ Complex.conjAe ≠ 1 := by
  have hconj : Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) := by
    intro he
    have him := congrArg Complex.im (AlgEquiv.congr_fun he Complex.I)
    norm_num at him
  constructor
  · intro he
    apply hconj
    have h := DiagramAut.scalarQuotientEquiv_section (ZMod 5) C Set.univ
      (by trivial) (by simp) (by decide) Complex.conjAe
    rw [he, map_one] at h
    exact h.symm
  · intro he
    apply hconj
    have h := GradedDiagramAut.scalarQuotientEquiv_section (ZMod 5) C Set.univ
      (by trivial) (by simp) (by decide) Complex.conjAe
    rw [he, map_one] at h
    exact h.symm

/-- The nontrivial conjugation quotient test applies to the actual full cofinal system.
Existence of this system is supplied by the independent geometric construction. -/
theorem full_complex_quotient_sections_nontrivial :
    DiagramAut.scalarQuotientSection (ZMod 5) (fullCofinalSystem ℝ ℂ 2) Set.univ
        Complex.conjAe ≠ 1 ∧
      GradedDiagramAut.scalarQuotientSection (ZMod 5) (fullCofinalSystem ℝ ℂ 2) Set.univ
        Complex.conjAe ≠ 1 :=
  conjugation_quotient_sections_nontrivial _

end OrlikSolomon.HyperplaneGT.GradedClassificationExamples
