/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Descent
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.GradedScalar

/-!
# Full graded classification over integral coefficients

After descent has classified every quadratic family, its primal scalar and direct Galois
factors extend to the full OS diagram. The existing faithful degree-one restriction is
therefore a multiplicative equivalence. The full action uses the corresponding scalar
power in every ordinary degree and on the single common target.

## Main definitions and results

* `coefficientDomainGradedAutEquiv`: the existing restriction with its classified inverse.
* `coefficientDomainGradedClassificationEquiv`: full scalar/Galois classification.
* `coefficientDomainGradedClassificationEquiv_stage_apply_of_mem_degree`: whole-degree action.

Blueprint: the full graded conclusions of S05 (`thm:s05`). No quadratic presentation of OS
or lifting principle for arbitrary relation-preserving maps is asserted.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

open OSAlgebra

universe u v r

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (R : Type r) [CommRing R] [IsDomain R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The actual faithful degree-one restriction becomes a multiplicative equivalence over
an integral domain after the quadratic descent theorem. Blueprint: S05 (`thm:s05`). -/
def coefficientDomainGradedAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S ≃* DiagramAut R C S where
  toFun := GradedDiagramAut.toQuadratic R C S
  invFun g := scalarGradedAut R C S (g.domainScalarPart hS hgen hn) *
    galoisGradedAut R C S (DiagramAut.domainToGalois R C S hS hgen hn g)
  left_inv g := by
    apply GradedDiagramAut.toQuadratic_injective
    rw [map_mul, toQuadratic_scalarGradedAut]
    exact coefficientDomainAutEquiv_right_inv R C S hS hgen hn _
  right_inv g := by
    rw [map_mul, toQuadratic_scalarGradedAut]
    exact coefficientDomainAutEquiv_right_inv R C S hS hgen hn g
  map_mul' g h := (GradedDiagramAut.toQuadratic R C S).map_mul g h

/-- The forward map is precisely the pre-existing degree-one restriction. -/
theorem coefficientDomainGradedAutEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    coefficientDomainGradedAutEquiv R C S hS hgen hn g =
      GradedDiagramAut.toQuadratic R C S g := rfl

/-- The inverse is the actual full scalar family times the direct Galois family. -/
theorem coefficientDomainGradedAutEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (coefficientDomainGradedAutEquiv R C S hS hgen hn).symm g =
      scalarGradedAut R C S (g.domainScalarPart hS hgen hn) *
        galoisGradedAut R C S (DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- Restriction followed by the classified lift recovers the original full diagram. -/
theorem coefficientDomainGradedAutEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedAutEquiv R C S hS hgen hn).symm
      (GradedDiagramAut.toQuadratic R C S g) = g :=
  (coefficientDomainGradedAutEquiv R C S hS hgen hn).symm_apply_apply g

/-- Classified lifting followed by restriction recovers the original quadratic diagram. -/
theorem coefficientDomainGradedAutEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    GradedDiagramAut.toQuadratic R C S
      ((coefficientDomainGradedAutEquiv R C S hS hgen hn).symm g) = g :=
  (coefficientDomainGradedAutEquiv R C S hS hgen hn).apply_symm_apply g

/-- The full diagram is canonically classified by primal coefficient units and Galois
automorphisms over an arbitrary integral domain. Blueprint: S05 (`thm:s05`). -/
def coefficientDomainGradedClassificationEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut R C S :=
  (coefficientDomainAutEquiv R C S hS hgen hn).trans
    (coefficientDomainGradedAutEquiv R C S hS hgen hn).symm

/-- The full classified family has the same scalar and Galois factors as its restriction. -/
theorem coefficientDomainGradedClassificationEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ) =
      scalarGradedAut R C S a * galoisGradedAut R C S σ := by
  apply GradedDiagramAut.toQuadratic_injective
  change GradedDiagramAut.toQuadratic R C S
    ((coefficientDomainGradedAutEquiv R C S hS hgen hn).symm
      (coefficientDomainAutEquiv R C S hS hgen hn (a, σ))) = _
  rw [coefficientDomainGradedAutEquiv_right_inv, map_mul, toQuadratic_scalarGradedAut,
    coefficientDomainAutEquiv_apply]
  rfl

/-- Full classification restricts to the same actual quadratic classification. -/
@[simp]
theorem toQuadratic_coefficientDomainGradedClassificationEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    GradedDiagramAut.toQuadratic R C S
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)) =
        coefficientDomainAutEquiv R C S hS hgen hn (a, σ) :=
  coefficientDomainGradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classified action has the primal coefficient at the covariant generator label.
-/
theorem coefficientDomainGradedClassificationEquiv_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (B : C.Stage) (H : B.val.val) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv B
      (generator R B.val.val H) =
        (a : R) • generator R B.val.val (galoisLabelEquiv B.val σ H) := by
  rw [coefficientDomainGradedClassificationEquiv_apply, GradedDiagramAut.stageEquiv_mul,
    AlgEquiv.mul_apply, galoisGradedAut_generator, scalarGradedAut_stageEquiv,
    scalarEquiv_generator]

/-- On the whole ordinary degree-q submodule the full action is the q-th scalar power
times the actual Galois action. In particular degree zero is fixed. -/
theorem coefficientDomainGradedClassificationEquiv_stage_apply_of_mem_degree
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (B : C.Stage) (q : ℕ)
    (x : OSAlgebra R B.val.val) (hx : x ∈ degree R B.val.val q) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv B x =
      (a : R) ^ q • galoisOSAlgebraEquiv R B.val σ x := by
  rw [coefficientDomainGradedClassificationEquiv_apply, GradedDiagramAut.stageEquiv_mul,
    AlgEquiv.mul_apply, galoisGradedAut_stageEquiv]
  exact scalarGradedAut_stage_apply_of_mem_degree R C S a B q _
    (galoisOSAlgebraEquiv_mem_degree R B.val σ hx)

/-- The same scalar degree power acts on the original common target. -/
theorem coefficientDomainGradedClassificationEquiv_target_apply_of_mem_degree
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ) (x : OSAlgebra R (twoPunctureArrangement k))
    (hx : x ∈ degree R (twoPunctureArrangement k) q) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv x =
      (a : R) ^ q • x := by
  rw [coefficientDomainGradedClassificationEquiv_apply, GradedDiagramAut.targetEquiv_mul,
    AlgEquiv.mul_apply, galoisGradedAut_targetEquiv]
  exact scalarGradedAut_target_apply_of_mem_degree R C S a q x hx

/-- The same primal coefficient acts on both ordered generators of the common target. -/
theorem coefficientDomainGradedClassificationEquiv_target_generator
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv
      (generator R _ (twoPunctureLabel k i)) =
        (a : R) • generator R _ (twoPunctureLabel k i) := by
  rw [coefficientDomainGradedClassificationEquiv_target_apply_of_mem_degree
    R C S hS hgen hn a σ 1 _ (generator_mem_degree R _ _), pow_one]

/-- The classified full family respects each actual tagged marking on the entire algebra.
-/
theorem coefficientDomainGradedClassificationEquiv_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (B : C.Stage) (w : Marking S n) (hw : w.Available B.val.val)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).stageEquiv B
      (w.osMap R hw x) =
        w.osMap R hw
          ((coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).targetEquiv x) :=
  DFunLike.congr_fun
    ((coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)).marking_naturality
      B w hw) x

end OrlikSolomon.HyperplaneGT
