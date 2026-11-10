/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.NormNum

/-!
# Ordinary de Rham reconstruction consumers

These consumers use the actual ordinary H¹, cup kernels, total algebras and one common
target. They pin both reconstruction inverses and literal restriction, actual marking
pullbacks, nonzero target dlogs, and the empty dimension-zero arrangement boundary.

Complex conjugation moves `x₀ = I` in a genuine selected stable stage. The image logarithmic
class is nonzero, so the coefficient `I` distinguishes the classified complex-linear action
from conjugate-semilinear transport. The final classification is used only in dimension two.

Blueprint: E03 (`cor:e03`).
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Examples

open Cohomology.DeRham

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)
  (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- Both ordinary reconstruction inverses simplify without expanding their definitions. -/
theorem inverse_cancellations (p : kˣ × (k ≃ₐ[k₀] k))
    (g : GradedDiagramAut C S) (h : DiagramAut C S) :
    (gradedReconstruction C S hS hgen hn).symm
        (gradedReconstruction C S hS hgen hn p) = p ∧
      gradedReconstruction C S hS hgen hn
        ((gradedReconstruction C S hS hgen hn).symm g) = g ∧
      (quadraticReconstruction C S hS hgen hn).symm
        (quadraticReconstruction C S hS hgen hn p) = p ∧
      quadraticReconstruction C S hS hgen hn
        ((quadraticReconstruction C S hS hgen hn).symm h) = h ∧
      (restrictionEquiv C S hS hgen hn).symm
        (restrictionEquiv C S hS hgen hn g) = g ∧
      restrictionEquiv C S hS hgen hn
        ((restrictionEquiv C S hS hgen hn).symm h) = h := by simp

/-- Literal ordinary H¹ restriction retains both classified coordinates. -/
theorem restriction_coordinates (p : kˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic C S (gradedReconstruction C S hS hgen hn p) =
      quadraticReconstruction C S hS hgen hn p := by
  rw [← restrictionEquiv_apply C S hS hgen hn,
    restrictionEquiv_gradedReconstruction C S hS hgen hn]

/-- The actual ordinary marking map uses the same degree-power scalar on the one target. -/
theorem actual_marking (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (q : ℕ)
    (x : Geometric.DeRham.Cohomology.degree
      (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)) q) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap (Geometric.SmoothDomain.aff k) hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap (Geometric.SmoothDomain.aff k) hw)
        ((a : k)^q • (x : Geometric.DeRham.Cohomology _)) := by
  rw [gradedReconstruction_marking_degree C S hS hgen hn]

/-- Degree-zero units are fixed at every actual stage and the common target. -/
theorem degree_zero_unit (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A 1 = 1 ∧
      (gradedReconstruction C S hS hgen hn (a, σ)).targetEquiv 1 = 1 := by simp

omit [Field k₀] [Algebra k₀ k] in
/-- The actual degree-two map is multiplication of arbitrary ordinary degree-one classes. -/
theorem ordinary_cup_product {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (A : Arrangement k V) (x y : degreeOne A) :
    (cupMap A (exteriorPower.ιMulti k 2 ![x, y]) :
      Geometric.DeRham.Cohomology ((Geometric.SmoothDomain.aff k).complement A)) =
      (x : Geometric.DeRham.Cohomology _) * (y : Geometric.DeRham.Cohomology _) := by
  rw [coe_cupMap_pair]

omit [Field k₀] [Algebra k₀ k] in
/-- Ordinary logarithmic classes at the actual common target are nonzero. -/
theorem target_dlog_ne_zero (i : Fin 2) :
    OrlikSolomon.DeRham.dlogClass k
      (A := Geometric.globalSections
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)).obj)
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff k) i) ≠ 0 := by
  intro h
  have he : (targetDegreeOneEquiv (k := k) (Finsupp.single i (1 : k)) :
      Geometric.DeRham.Cohomology
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k))) = 0 := by
    simpa only [coe_targetDegreeOneEquiv_single, one_smul] using h
  have hs : (Finsupp.single i (1 : k)) = 0 :=
    (targetDegreeOneEquiv (k := k)).injective
      ((Subtype.ext he).trans (map_zero (targetDegreeOneEquiv (k := k))).symm)
  exact (one_ne_zero : (1 : k) ≠ 0)
    (by simpa using congrArg (fun c : Fin 2 →₀ k ↦ c i) hs)

omit [Field k₀] [Algebra k₀ k] in
/-- The two nonzero actual target dlogs have zero degree-two cup product, as required by
the whole target kernel rather than a claim about a quadratic presentation. -/
theorem target_dlog_product (i j : Fin 2) :
    OrlikSolomon.DeRham.dlogClass k
      (A := Geometric.globalSections
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)).obj)
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff k) i) *
    OrlikSolomon.DeRham.dlogClass k
      (A := Geometric.globalSections
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)).obj)
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff k) j) = 0 := by
  have h := coe_cupMap_pair (twoPunctureArrangement k)
    (targetDegreeOneEquiv (Finsupp.single i (1 : k)))
    (targetDegreeOneEquiv (Finsupp.single j (1 : k)))
  have hz := DFunLike.congr_fun (target_cupMap_eq_zero (k := k))
    (exteriorPower.ιMulti k 2
      ![targetDegreeOneEquiv (Finsupp.single i (1 : k)),
        targetDegreeOneEquiv (Finsupp.single j (1 : k))])
  have hc := congrArg (fun z : degreeTwo (twoPunctureArrangement k) ↦
    (z : Geometric.DeRham.Cohomology
      (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff k)))) hz
  simpa only [LinearMap.zero_apply, ZeroMemClass.coe_zero,
    coe_targetDegreeOneEquiv_single, one_smul] using h.symm.trans hc

omit [Field k₀] [Algebra k₀ k] in
/-- The ordinary H¹ of the empty dimension-zero arrangement is zero. This uses no final
classification outside its dimension bound. -/
theorem dimension_zero_empty (x : degreeOne (∅ : Arrangement k (Fin 0 → k))) : x = 0 := by
  apply (degreeOneEquiv (∅ : Arrangement k (Fin 0 → k))).symm.injective
  exact Subsingleton.elim _ _

/-- A genuine full cofinal stable system over the algebraic extension `ℂ/ℝ`. -/
def complexSystem : CofinalSystem ℝ ℂ 2 := fullCofinalSystem ℝ ℂ 2

/-- The hyperplane `x₀ = I`, moved by complex conjugation. -/
def imaginaryHyperplane : Hyperplane ℂ 2 := coordinateHyperplane (0 : Fin 2) Complex.I

/-- A selected stable stage containing `x₀ = I`; stability also contains its conjugate. -/
def imaginaryStage : complexSystem.Stage :=
  (complexSystem.exists_stage_containing {imaginaryHyperplane}).choose

/-- The concrete imaginary hyperplane is present in the selected actual stage. -/
theorem imaginaryHyperplane_mem : imaginaryHyperplane.val ∈ imaginaryStage.val.val :=
  (complexSystem.exists_stage_containing {imaginaryHyperplane}).choose_spec _ (by simp)

/-- The label of the imaginary hyperplane in that stage. -/
def imaginaryLabel : imaginaryStage.val.val := ⟨imaginaryHyperplane.val, imaginaryHyperplane_mem⟩

/-- The covariant conjugate label in the same actual stage. -/
def conjugateLabel : imaginaryStage.val.val :=
  galoisLabelEquiv imaginaryStage.val Complex.conjAe imaginaryLabel

/-- Complex conjugation actually moves the selected hyperplane. -/
theorem conjugateLabel_ne : conjugateLabel ≠ imaginaryLabel := by
  intro he
  have hp : Pi.single (0 : Fin 2) Complex.I ∈ imaginaryLabel.val := by
    simp [imaginaryLabel, imaginaryHyperplane, mem_coordinateHyperplane]
  rw [← congrArg Subtype.val he] at hp
  change Pi.single (0 : Fin 2) Complex.I ∈
    (galoisLabelEquiv imaginaryStage.val Complex.conjAe imaginaryLabel).val at hp
  rw [galoisLabelEquiv_val] at hp
  simp only [mem_fieldAffineSubspace, imaginaryLabel, imaginaryHyperplane,
    mem_coordinateHyperplane, fieldCoordinateAddEquiv_symm_apply, Pi.single_eq_same] at hp
  have him := congrArg Complex.im hp
  change (-1 : ℝ) = 1 at him
  norm_num at him

/-- An actual ordinary logarithmic generator in the selected complement. -/
def logarithm (H : imaginaryStage.val.val) :
    Geometric.DeRham.Cohomology
      ((Geometric.SmoothDomain.aff ℂ).complement imaginaryStage.val.val) :=
  degreeOneEquiv imaginaryStage.val.val (Finsupp.single H 1)

/-- The class is the existing geometric logarithmic realization, not a normalized carrier. -/
theorem logarithm_eq (H : imaginaryStage.val.val) :
    logarithm H = Geometric.DeRham.affineEquiv imaginaryStage.val.val
      (OSAlgebra.generator ℂ imaginaryStage.val.val H) := by
  rw [logarithm, coe_degreeOneEquiv, osDegreeOneEquiv_single, one_smul]

/-- Every such actual ordinary logarithmic class is nonzero. -/
theorem logarithm_ne_zero (H : imaginaryStage.val.val) : logarithm H ≠ 0 := by
  intro h
  have he : degreeOneEquiv imaginaryStage.val.val (Finsupp.single H 1) = 0 :=
    Subtype.ext h
  have hs : Finsupp.single H (1 : ℂ) = 0 :=
    (degreeOneEquiv imaginaryStage.val.val).injective
      (he.trans (map_zero (degreeOneEquiv imaginaryStage.val.val)).symm)
  exact (one_ne_zero : (1 : ℂ) ≠ 0)
    (by simpa using congrArg (fun c : imaginaryStage.val.val →₀ ℂ ↦ c H) hs)

/-- The actual complex-linear classified action corresponding to complex conjugation. -/
def conjugation : GradedDiagramAut complexSystem (Set.univ : Set ℝ) :=
  gradedReconstruction complexSystem Set.univ (by simp) (by simp) (by decide)
    (1, Complex.conjAe)

-- The actual ordinary class traverses the nested scheme/diagonal subgroup comparisons.
set_option maxRecDepth 2000 in
/-- The actual ordinary generator has the covariant conjugate label. -/
theorem conjugation_logarithm :
    conjugation.stageEquiv imaginaryStage (logarithm imaginaryLabel) =
      logarithm conjugateLabel := by
  rw [logarithm_eq, logarithm_eq]
  simpa only [conjugation, conjugateLabel, Units.val_one, one_smul] using
    gradedReconstruction_stage_generator complexSystem Set.univ
      (by simp) (by simp) (by decide) (1 : ℂˣ) Complex.conjAe imaginaryStage imaginaryLabel

/-- A nonzero moved logarithmic class distinguishes complex linearity from conjugate
semilinearity. The coefficient `I` is fixed by the classified action. -/
theorem linear_not_semilinear :
    conjugation.stageEquiv imaginaryStage (Complex.I • logarithm imaginaryLabel) =
        Complex.I • logarithm conjugateLabel ∧
      conjugation.stageEquiv imaginaryStage (Complex.I • logarithm imaginaryLabel) ≠
        Complex.conjAe Complex.I • logarithm conjugateLabel := by
  have h : conjugation.stageEquiv imaginaryStage (Complex.I • logarithm imaginaryLabel) =
      Complex.I • logarithm conjugateLabel := by rw [map_smul, conjugation_logarithm]
  refine ⟨h, ?_⟩
  intro he
  have hi := smul_left_injective ℂ (logarithm_ne_zero conjugateLabel) (h.symm.trans he)
  have him := congrArg Complex.im hi
  norm_num at him

/-- A nonidentity unit in the actual geometric coefficient field. -/
def complexTwo : ℂˣ := Units.mk0 2 (by norm_num)

/-- Both ordered actual target dlogs detect the same nonidentity primal unit, even with
a nontrivial field-automorphism parameter. -/
theorem target_two (i : Fin 2) :
    let e := fullGradedReconstruction (k₀ := ℝ) (k := ℂ) (n := 2)
      Set.univ (by simp) (by simp) (by decide)
    let x := OrlikSolomon.DeRham.dlogClass ℂ
      (A := Geometric.globalSections
        (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff ℂ)).obj)
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff ℂ) i)
    (e (complexTwo, Complex.conjAe)).targetEquiv x = (2 : ℂ) • x ∧
      (e (complexTwo, Complex.conjAe)).targetEquiv x ≠ x := by
  dsimp only
  have h := gradedReconstruction_target_dlog complexSystem Set.univ
    (by simp) (by simp) (by decide) complexTwo Complex.conjAe i
  change _ = (2 : ℂ) • _ at h
  refine ⟨h, ?_⟩
  intro he
  have hs : (2 : ℂ) • _ = (1 : ℂ) • _ := (h.symm.trans he).trans (one_smul ℂ _).symm
  have hc := smul_left_injective ℂ (target_dlog_ne_zero (k := ℂ) i) hs
  norm_num at hc

-- This actual scheme pullback passes through both nested reconstruction comparisons.
set_option maxRecDepth 2000 in
/-- A coordinate marking is available at an actual selected stable stage, and its two
ordinary pulled-back dlogs are fixed by the classified conjugation action. -/
theorem available_marking_fixed :
    let w : Marking (Set.univ : Set ℝ) 2 := .coordinate 0 ⟨0, Set.mem_univ _⟩
    ∃ (A : complexSystem.Stage) (hw : w.Available A.val.val), ∀ i : Fin 2,
      conjugation.stageEquiv A
        (Geometric.DeRham.Cohomology.pull
          (w.schemeMap (Geometric.SmoothDomain.aff ℂ) hw)
          (OrlikSolomon.DeRham.dlogClass ℂ
            (A := Geometric.globalSections
              (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff ℂ)).obj)
            (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff ℂ) i))) =
      Geometric.DeRham.Cohomology.pull
        (w.schemeMap (Geometric.SmoothDomain.aff ℂ) hw)
        (OrlikSolomon.DeRham.dlogClass ℂ
          (A := Geometric.globalSections
            (Cohomology.schemeMarkingTarget (Geometric.SmoothDomain.aff ℂ)).obj)
          (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff ℂ) i)) := by
  dsimp only
  let w : Marking (Set.univ : Set ℝ) 2 := .coordinate 0 ⟨0, Set.mem_univ _⟩
  obtain ⟨A, hw⟩ := complexSystem.exists_stage_marking w
  refine ⟨A, hw, fun i ↦ ?_⟩
  have h := gradedReconstruction_marking_degree complexSystem Set.univ
    (by simp) (by simp) (by decide) (1 : ℂˣ) Complex.conjAe A w hw 1
    ⟨OrlikSolomon.DeRham.dlogClass ℂ
      (Cohomology.schemeMarkingTargetUnit (Geometric.SmoothDomain.aff ℂ) i),
      OrlikSolomon.DeRham.dlogClass_mem_degree _⟩
  simpa only [conjugation, w, Units.val_one, one_pow, one_smul] using h

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Examples
