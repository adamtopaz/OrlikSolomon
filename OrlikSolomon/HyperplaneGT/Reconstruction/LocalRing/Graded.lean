/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.GradedScalar
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quadratic

/-!
# Graded restriction becomes an equivalence after classification

The existing faithful degree-one restriction is surjective because the quadratic
classification forces every automorphism to be a scalar times the direct Galois family.
Both factors have already been constructed on the full OS algebra, with every defining
relation and the one common target retained. This gives a multiplicative equivalence whose
forward map is exactly the existing restriction, with an explicit scalar/Galois inverse.

No quadratic presentation of the OS algebra or extension of arbitrary relation-preserving
linear maps is used. Blueprint: the graded restriction equivalence in S04 (`thm:s04`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

open OSAlgebra

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] [IsLocalRing R]
  (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Degree-one restriction is a multiplicative equivalence of the literal graded and
quadratic diagram groups. Surjectivity uses the already proved quadratic classification;
the common target is retained on both sides. Blueprint: S04 (`thm:s04`). -/
def gradedAutEquiv (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S ≃* DiagramAut R C S where
  toFun := GradedDiagramAut.toQuadratic R C S
  invFun g := scalarGradedAut R C S (g.scalarPart hS hgen hn) *
    galoisGradedAut R C S (DiagramAut.toGalois R C S hS hgen hn g)
  left_inv g := by
    apply GradedDiagramAut.toQuadratic_injective
    rw [map_mul, toQuadratic_scalarGradedAut]
    exact quadraticAutEquiv_right_inv R C S hS hgen hn _
  right_inv g := by
    rw [map_mul, toQuadratic_scalarGradedAut]
    exact quadraticAutEquiv_right_inv R C S hS hgen hn g
  map_mul' g h := (GradedDiagramAut.toQuadratic R C S).map_mul g h

/-- The equivalence's forward map is precisely the existing degree-one restriction. -/
theorem gradedAutEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    gradedAutEquiv R C S hS hgen hn g = GradedDiagramAut.toQuadratic R C S g := rfl

/-- The inverse is the actual full scalar family times the existing full Galois family. -/
theorem gradedAutEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (gradedAutEquiv R C S hS hgen hn).symm g =
      scalarGradedAut R C S (g.scalarPart hS hgen hn) *
        galoisGradedAut R C S (DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- Restricting and then extending a full diagram recovers every stage and the common target.
-/
theorem gradedAutEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    (gradedAutEquiv R C S hS hgen hn).symm (GradedDiagramAut.toQuadratic R C S g) = g :=
  (gradedAutEquiv R C S hS hgen hn).symm_apply_apply g

/-- Extending a classified quadratic diagram and restricting it recovers that diagram. -/
theorem gradedAutEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    GradedDiagramAut.toQuadratic R C S ((gradedAutEquiv R C S hS hgen hn).symm g) = g :=
  (gradedAutEquiv R C S hS hgen hn).apply_symm_apply g

/-- The full graded classification is the quadratic classification followed by the inverse
of the same degree-one restriction equivalence. Blueprint: S04 (`thm:s04`). -/
def gradedClassificationEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut R C S :=
  (quadraticAutEquiv R C S hS hgen hn).trans (gradedAutEquiv R C S hS hgen hn).symm

/-- The full classification has the same scalar/Galois product formula as its restriction. -/
theorem gradedClassificationEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    gradedClassificationEquiv R C S hS hgen hn (a, σ) =
      scalarGradedAut R C S a * galoisGradedAut R C S σ := by
  apply GradedDiagramAut.toQuadratic_injective
  change GradedDiagramAut.toQuadratic R C S
    ((gradedAutEquiv R C S hS hgen hn).symm (quadraticAutEquiv R C S hS hgen hn (a, σ))) = _
  rw [gradedAutEquiv_right_inv, map_mul, toQuadratic_scalarGradedAut,
    quadraticAutEquiv_apply]
  rfl

/-- The full classification restricts to the actual quadratic classification. -/
@[simp]
theorem toQuadratic_gradedClassificationEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    GradedDiagramAut.toQuadratic R C S
      (gradedClassificationEquiv R C S hS hgen hn (a, σ)) =
        quadraticAutEquiv R C S hS hgen hn (a, σ) :=
  gradedAutEquiv_right_inv R C S hS hgen hn _

/-- Each finite-stage generator is multiplied by the primal unit at its covariant Galois label.
-/
theorem gradedClassificationEquiv_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv A
      (generator R A.val.val H) =
        (a : R) • generator R A.val.val (galoisLabelEquiv A.val σ H) := by
  rw [gradedClassificationEquiv_apply, GradedDiagramAut.stageEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAut_generator, scalarGradedAut_stageEquiv, scalarEquiv_generator]

/-- The classified full action on every degree-q element is the q-th scalar power after
the actual Galois presentation action. Degree zero is therefore fixed. -/
theorem gradedClassificationEquiv_stage_apply_of_mem_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val) (hx : x ∈ degree R A.val.val q) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv A x =
      (a : R) ^ q • galoisOSAlgebraEquiv R A.val σ x := by
  rw [gradedClassificationEquiv_apply, GradedDiagramAut.stageEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAut_stageEquiv]
  exact scalarGradedAut_stage_apply_of_mem_degree R C S a A q _
    (galoisOSAlgebraEquiv_mem_degree R A.val σ hx)

/-- The Galois factor fixes the common target, where every degree-q element is multiplied
by the same q-th scalar power used at the stages. -/
theorem gradedClassificationEquiv_target_apply_of_mem_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : OSAlgebra R (twoPunctureArrangement k))
    (hx : x ∈ degree R (twoPunctureArrangement k) q) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv x = (a : R) ^ q • x := by
  rw [gradedClassificationEquiv_apply, GradedDiagramAut.targetEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAut_targetEquiv]
  exact scalarGradedAut_target_apply_of_mem_degree R C S a q x hx

/-- Both ordered common-target generators use the same primal unit, with no target-specific
scalar or Galois permutation. -/
theorem gradedClassificationEquiv_target_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv
      (generator R _ (twoPunctureLabel k i)) = (a : R) • generator R _ (twoPunctureLabel k i) := by
  rw [gradedClassificationEquiv_target_apply_of_mem_degree R C S hS hgen hn a σ 1 _
    (generator_mem_degree R _ _), pow_one]

/-- The full classified action respects the actual tagged marking map on every element,
using its single common-target component. -/
theorem gradedClassificationEquiv_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    (gradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv A (w.osMap R hw x) =
      w.osMap R hw ((gradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv x) :=
  DFunLike.congr_fun ((gradedClassificationEquiv R C S hS hgen hn (a, σ)).marking_naturality
    A w hw) x

end OrlikSolomon.HyperplaneGT
