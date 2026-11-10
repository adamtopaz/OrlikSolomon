/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Graded
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Graded
public import OrlikSolomon.HyperplaneGT.Topology.Classification.Quadratic
public import OrlikSolomon.HyperplaneGT.Topology.Restriction

/-!
# Topological graded restriction and reconstruction

`gradedAutContinuousEquiv` and `coefficientDomainGradedAutContinuousEquiv` adjoin both
continuity proofs to the existing literal degree-one restriction equivalences, with no
field-extension hypothesis. `gradedClassificationContinuousEquiv` and its domain version
upgrade the exact original product classifications for discrete units and pointwise Galois
automorphisms. Only their separate Krull wrappers require the fixing condition or algebraicity.

The direct whole-algebra stage-and-target topology is unchanged. All parameter topology
values and deliberate scopes come from T09; this leaf registers no topology or instance.
Underlying-map and inverse expansions are plain rewrites, preserving bare cancellation.
Whole-degree actions retain the primal scalar power, covariant labels and original common
target, together with the actual inclusion and marking equations. No quadratic-presentation
or unrestricted lifting assertion is used. Blueprint: T10 (`cor:t10`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open scoped DiscreteCoefficientUnits FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The exact existing local-ring graded restriction with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T10 (`cor:t10`). -/
def gradedAutContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := gradedAutEquiv R C S hS hgen hn
  continuous_toFun := GradedDiagramAut.continuous_toQuadratic R C S
  continuous_invFun := GradedDiagramAut.continuous_inverse_toQuadratic R C S _
    (gradedAutEquiv_right_inv R C S hS hgen hn)

/-- Forgetting continuity recovers the original graded restriction equivalence. -/
theorem gradedAutContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedAutContinuousEquiv R C S hS hgen hn).toMulEquiv = gradedAutEquiv R C S hS hgen hn := rfl

/-- The underlying function is the literal degree-one restriction. -/
theorem gradedAutContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedAutContinuousEquiv R C S hS hgen hn : GradedDiagramAut R C S → DiagramAut R C S) =
      GradedDiagramAut.toQuadratic R C S := rfl

/-- Applying the topological equivalence performs the existing restriction. -/
theorem gradedAutContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    gradedAutContinuousEquiv R C S hS hgen hn g = GradedDiagramAut.toQuadratic R C S g := rfl

/-- The inverse is the original classified scalar family times the full Galois family. -/
theorem gradedAutContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (gradedAutContinuousEquiv R C S hS hgen hn).symm g =
      scalarGradedAut R C S (g.scalarPart hS hgen hn) *
        galoisGradedAut R C S (DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- The exact existing domain graded restriction with both continuity proofs.
No field-extension hypothesis is required. Blueprint: T10 (`cor:t10`). -/
def coefficientDomainGradedAutContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S)
      (DiagramAut R C S) (DiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainGradedAutEquiv R C S hS hgen hn
  continuous_toFun := GradedDiagramAut.continuous_toQuadratic R C S
  continuous_invFun := GradedDiagramAut.continuous_inverse_toQuadratic R C S _
    (coefficientDomainGradedAutEquiv_right_inv R C S hS hgen hn)

/-- Forgetting continuity recovers the original graded restriction equivalence. -/
theorem coefficientDomainGradedAutContinuousEquiv_toMulEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).toMulEquiv =
      coefficientDomainGradedAutEquiv R C S hS hgen hn := rfl

/-- The underlying function is the literal degree-one restriction. -/
theorem coefficientDomainGradedAutContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn : GradedDiagramAut R C S →
      DiagramAut R C S) =
      GradedDiagramAut.toQuadratic R C S := rfl

/-- Applying the topological equivalence performs the existing restriction. -/
theorem coefficientDomainGradedAutContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn g = GradedDiagramAut.toQuadratic R
      C S g := rfl

/-- The inverse is the original classified scalar family times the full Galois family. -/
theorem coefficientDomainGradedAutContinuousEquiv_symm_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : DiagramAut R C S) :
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm g =
      scalarGradedAut R C S (g.domainScalarPart hS hgen hn) *
        galoisGradedAut R C S (DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- The two restriction homeomorphisms agree on the local/domain overlap. -/
theorem coefficientDomainGradedAutContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn =
      gradedAutContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro g
  rfl

section Pointwise

open scoped GaloisPointwise

/-- The exact local-ring full graded classifier with pointwise continuity in both
directions. No algebraicity is assumed. Blueprint: T10 (`cor:t10`). -/
def gradedClassificationContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := gradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((quadraticAutContinuousEquiv R C S hS hgen hn).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((quadraticAutContinuousEquiv R C S hS hgen hn).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting continuity recovers the exact original product classification. -/
theorem gradedClassificationContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn).toMulEquiv =
      gradedClassificationEquiv R C S hS hgen hn := rfl

/-- The underlying function is the original full graded classifier. -/
theorem gradedClassificationContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        gradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the pointwise wrapper retains the existing classifier. -/
theorem gradedClassificationContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedClassificationContinuousEquiv R C S hS hgen hn p = gradedClassificationEquiv R C S hS
      hgen hn p := rfl

/-- The inverse returns the old primal scalar and recovered automorphism of the restriction. -/
theorem gradedClassificationContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn).symm g =
      ((GradedDiagramAut.toQuadratic R C S g).scalarPart hS hgen hn,
        DiagramAut.toGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- The full graded classifier is the original scalar family times the covariant Galois family.
-/
theorem gradedClassificationContinuousEquiv_apply_pair [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ) =
      scalarGradedAut R C S a * galoisGradedAut R C S σ :=
  gradedClassificationEquiv_apply R C S hS hgen hn a σ

/-- The stage generator retains the primal coefficient and covariant geometric label. -/
theorem gradedClassificationContinuousEquiv_stage_generator [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A
        (OSAlgebra.generator R A.val.val H) =
      (a : R) • OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H) :=
  gradedClassificationEquiv_stage_generator R C S hS hgen hn a σ A H

/-- The whole degree-q submodule carries the q-th scalar power after the original Galois action.
This includes degree zero. -/
theorem gradedClassificationContinuousEquiv_stage_apply_of_mem_degree
    [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A x =
      (a : R) ^ q • galoisOSAlgebraEquiv R A.val σ x :=
  gradedClassificationEquiv_stage_apply_of_mem_degree R C S hS hgen hn a σ A q x hx

/-- Every homogeneous element of the single common target uses the same scalar degree power.
-/
theorem gradedClassificationContinuousEquiv_target_apply_of_mem_degree
    [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ) (x : OSAlgebra R (twoPunctureArrangement k))
    (hx : x ∈ OSAlgebra.degree R (twoPunctureArrangement k) q) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv x = (a : R) ^ q • x :=
  gradedClassificationEquiv_target_apply_of_mem_degree R C S hS hgen hn a σ q x hx

/-- Both ordered target generators use the same primal coefficient. -/
theorem gradedClassificationContinuousEquiv_target_generator [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv
        (OSAlgebra.generator R _ (twoPunctureLabel k i)) =
      (a : R) • OSAlgebra.generator R _ (twoPunctureLabel k i) :=
  gradedClassificationEquiv_target_generator R C S hS hgen hn a σ i

/-- The classified full algebra components commute with the actual presentation inclusion. -/
theorem gradedClassificationContinuousEquiv_inclusion [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) {A B : C.Stage} (h : A ≤ B) :
    ((gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv B).toAlgHom.comp
        (OSAlgebra.map R h) =
      (OSAlgebra.map R h).comp
        ((gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A).toAlgHom :=
  GradedDiagramAut.inclusion_naturality _ h

/-- The classified full action respects each actual marking on the entire target algebra. -/
theorem gradedClassificationContinuousEquiv_marking [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : OSAlgebra R (twoPunctureArrangement k)) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A (w.osMap R hw x) =
      w.osMap R hw ((gradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv x) :=
  gradedClassificationEquiv_marking R C S hS hgen hn a σ A w hw x

/-- The exact domain full graded classifier with pointwise continuity in both
directions. No algebraicity is assumed. Blueprint: T10 (`cor:t10`). -/
def coefficientDomainGradedClassificationContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisPointwiseTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainGradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutContinuousEquiv R C S hS hgen hn).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting continuity recovers the exact original product classification. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_toMulEquiv
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).toMulEquiv =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- The underlying function is the original full graded classifier. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_coe [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the pointwise wrapper retains the existing classifier. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_apply [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn p =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p := rfl

/-- The inverse returns the old primal scalar and recovered automorphism of the restriction. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_symm_apply
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).symm g =
      ((GradedDiagramAut.toQuadratic R C S g).domainScalarPart hS hgen hn,
        DiagramAut.domainToGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- The full graded classifier is the original scalar family times the covariant Galois family.
-/
theorem coefficientDomainGradedClassificationContinuousEquiv_apply_pair
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ) =
      scalarGradedAut R C S a * galoisGradedAut R C S σ :=
  coefficientDomainGradedClassificationEquiv_apply R C S hS hgen hn a σ

/-- The stage generator retains the primal coefficient and covariant geometric label. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_stage_generator
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A
        (OSAlgebra.generator R A.val.val H) =
      (a : R) • OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H) :=
  coefficientDomainGradedClassificationEquiv_stage_generator R C S hS hgen hn a σ A H

/-- The whole degree-q submodule carries the q-th scalar power after the original Galois action.
This includes degree zero. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_stage_apply_of_mem_degree
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A x =
      (a : R) ^ q • galoisOSAlgebraEquiv R A.val σ x :=
  coefficientDomainGradedClassificationEquiv_stage_apply_of_mem_degree R C S hS hgen hn a σ A q x hx

/-- Every homogeneous element of the single common target uses the same scalar degree power.
-/
theorem coefficientDomainGradedClassificationContinuousEquiv_target_apply_of_mem_degree
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ) (x : OSAlgebra R (twoPunctureArrangement k))
    (hx : x ∈ OSAlgebra.degree R (twoPunctureArrangement k) q) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv x =
      (a : R) ^ q • x :=
  coefficientDomainGradedClassificationEquiv_target_apply_of_mem_degree R C S hS hgen hn a σ q x hx

/-- Both ordered target generators use the same primal coefficient. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_target_generator
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).targetEquiv
        (OSAlgebra.generator R _ (twoPunctureLabel k i)) =
      (a : R) • OSAlgebra.generator R _ (twoPunctureLabel k i) :=
  coefficientDomainGradedClassificationEquiv_target_generator R C S hS hgen hn a σ i

/-- The classified full algebra components commute with the actual presentation inclusion. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_inclusion
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) {A B : C.Stage} (h : A ≤ B) :
    ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv
      B).toAlgHom.comp
        (OSAlgebra.map R h) =
      (OSAlgebra.map R h).comp
        ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv
          A).toAlgHom :=
  GradedDiagramAut.inclusion_naturality _ h

/-- The classified full action respects each actual marking on the entire target algebra. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_marking
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (a : Rˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (w : Marking S n)
    (hw : w.Available A.val.val) (x : OSAlgebra R (twoPunctureArrangement k)) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a, σ)).stageEquiv A
      (w.osMap R hw x) =
      w.osMap R hw ((coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn (a,
        σ)).targetEquiv x) :=
  coefficientDomainGradedClassificationEquiv_marking R C S hS hgen hn a σ A w hw x

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_gradedClassificationContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S (gradedClassificationContinuousEquiv R C S hS hgen hn p) =
      quadraticAutContinuousEquiv R C S hS hgen hn p :=
  gradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem gradedClassificationContinuousEquiv_trans_restriction [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationContinuousEquiv R C S hS hgen hn).trans (gradedAutContinuousEquiv R C S
      hS hgen hn) =
      quadraticAutContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_gradedClassificationContinuousEquiv R C S hS hgen hn p

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_coefficientDomainGradedClassificationContinuousEquiv
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S (coefficientDomainGradedClassificationContinuousEquiv R C S
      hS hgen hn p) =
      coefficientDomainAutContinuousEquiv R C S hS hgen hn p :=
  coefficientDomainGradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_trans_restriction
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn).trans
      (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn) =
      coefficientDomainAutContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn p

/-- The local and domain full classifiers agree on their simultaneous coefficient overlap. -/
theorem coefficientDomainGradedClassificationContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainGradedClassificationContinuousEquiv R C S hS hgen hn =
      gradedClassificationContinuousEquiv R C S hS hgen hn := by
  apply DFunLike.ext
  rintro ⟨a, σ⟩
  change coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ) =
    gradedClassificationEquiv R C S hS hgen hn (a, σ)
  rw [coefficientDomainGradedClassificationEquiv_apply, gradedClassificationEquiv_apply]

end Pointwise

/-- The exact full graded classifier for Mathlib's Krull topology under
the explicit finite-intermediate-field fixing condition. Blueprint: T10 (`cor:t10`). -/
def gradedClassificationKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := gradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((quadraticAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting Krull continuity recovers the exact old full graded classifier. -/
theorem gradedClassificationKrullContinuousEquiv_toMulEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
      gradedClassificationEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper retains the original underlying full graded function. -/
theorem gradedClassificationKrullContinuousEquiv_coe [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        gradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the exact existing full graded classifier. -/
theorem gradedClassificationKrullContinuousEquiv_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p = gradedClassificationEquiv R C
      S hS hgen hn p := rfl

/-- The Krull inverse uses the original primal scalar and recovered field automorphism. -/
theorem gradedClassificationKrullContinuousEquiv_symm_apply [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut R C S) :
    (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm g =
      ((GradedDiagramAut.toQuadratic R C S g).scalarPart hS hgen hn,
        DiagramAut.toGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_gradedClassificationKrullContinuousEquiv [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S (gradedClassificationKrullContinuousEquiv R C S hS hgen hn
      hK p) =
      quadraticAutKrullContinuousEquiv R C S hS hgen hn hK p :=
  gradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem gradedClassificationKrullContinuousEquiv_trans_restriction
    [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).trans (gradedAutContinuousEquiv
      R C S hS hgen hn) =
      quadraticAutKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p

/-- The exact full graded classifier for Mathlib's Krull topology under
the explicit finite-intermediate-field fixing condition. Blueprint: T10 (`cor:t10`). -/
def coefficientDomainGradedClassificationKrullContinuousEquiv [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainGradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting Krull continuity recovers the exact old full graded classifier. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_toMulEquiv
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).toMulEquiv =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper retains the original underlying full graded function. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_coe
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the exact existing full graded classifier. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_apply
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse uses the original primal scalar and recovered field automorphism. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_symm_apply
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).symm g =
      ((GradedDiagramAut.toQuadratic R C S g).domainScalarPart hS hgen hn,
        DiagramAut.domainToGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_coefficientDomainGradedClassificationKrullContinuousEquiv
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S (coefficientDomainGradedClassificationKrullContinuousEquiv
      R C S hS hgen hn hK p) =
      coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK p :=
  coefficientDomainGradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_trans_restriction
    [IsDomain R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    (coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK).trans
      (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn) =
      coefficientDomainAutKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK p

/-- The exact full graded classifier for Mathlib's Krull topology under
algebraicity, with no normality or separability. Blueprint: T10 (`cor:t10`). -/
def gradedClassificationKrullContinuousEquivOfIsAlgebraic
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := gradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).trans
    (gradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting Krull continuity recovers the exact old full graded classifier. -/
theorem gradedClassificationKrullContinuousEquivOfIsAlgebraic_toMulEquiv
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).toMulEquiv =
      gradedClassificationEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper retains the original underlying full graded function. -/
theorem gradedClassificationKrullContinuousEquivOfIsAlgebraic_coe
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        gradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the exact existing full graded classifier. -/
theorem gradedClassificationKrullContinuousEquivOfIsAlgebraic_apply
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p =
      gradedClassificationEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse uses the original primal scalar and recovered field automorphism. -/
theorem gradedClassificationKrullContinuousEquivOfIsAlgebraic_symm_apply
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm g =
      ((GradedDiagramAut.toQuadratic R C S g).scalarPart hS hgen hn,
        DiagramAut.toGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_gradedClassificationKrullContinuousEquivOfIsAlgebraic
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C
      S hS hgen hn p) =
      quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p :=
  gradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem gradedClassificationKrullContinuousEquivOfIsAlgebraic_trans_restriction
    [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).trans
      (gradedAutContinuousEquiv R C S hS hgen hn) =
      quadraticAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p

/-- The exact full graded classifier for Mathlib's Krull topology under
algebraicity, with no normality or separability. Blueprint: T10 (`cor:t10`). -/
def coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    @ContinuousMulEquiv (Rˣ × (k ≃ₐ[k₀] k))
      (coefficientGaloisKrullTopology R k₀ k)
      (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) _ _ where
  toMulEquiv := coefficientDomainGradedClassificationEquiv R C S hS hgen hn
  continuous_toFun := ((coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_toFun
  continuous_invFun := ((coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen
    hn).trans
    (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn).symm).continuous_invFun

/-- Forgetting Krull continuity recovers the exact old full graded classifier. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_toMulEquiv
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn).toMulEquiv =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- The Krull wrapper retains the original underlying full graded function. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_coe
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn :
      (Rˣ × (k ≃ₐ[k₀] k)) → GradedDiagramAut R C S) =
        coefficientDomainGradedClassificationEquiv R C S hS hgen hn := rfl

/-- Applying the Krull wrapper uses the exact existing full graded classifier. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_apply
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p := rfl

/-- The Krull inverse uses the original primal scalar and recovered field automorphism. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_symm_apply
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (g : GradedDiagramAut R C S) :
    (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn).symm
      g =
      ((GradedDiagramAut.toQuadratic R C S g).domainScalarPart hS hgen hn,
        DiagramAut.domainToGalois R C S hS hgen hn (GradedDiagramAut.toQuadratic R C S g)) := rfl

/-- Restricting the full classified family gives the exact quadratic topological classifier. -/
theorem toQuadratic_coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic R C S
      (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p)
      =
      coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn p :=
  coefficientDomainGradedAutEquiv_right_inv R C S hS hgen hn _

/-- The full classification and literal restriction form the original commuting square. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_trans_restriction
    [IsDomain R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen
      hn).trans (coefficientDomainGradedAutContinuousEquiv R C S hS hgen hn) =
      coefficientDomainAutKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  intro p
  exact toQuadratic_coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S
    hS hgen hn p

/-- The local and domain full classifiers agree on their simultaneous coefficient overlap. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquiv_eq_local
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    coefficientDomainGradedClassificationKrullContinuousEquiv R C S hS hgen hn hK =
      gradedClassificationKrullContinuousEquiv R C S hS hgen hn hK := by
  apply DFunLike.ext
  rintro ⟨a, σ⟩
  change coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ) =
    gradedClassificationEquiv R C S hS hgen hn (a, σ)
  rw [coefficientDomainGradedClassificationEquiv_apply, gradedClassificationEquiv_apply]

/-- The local and domain full classifiers agree on their simultaneous coefficient overlap. -/
theorem coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic_eq_local
    [IsDomain R] [IsLocalRing R] [Algebra.IsAlgebraic k₀ k] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainGradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn =
      gradedClassificationKrullContinuousEquivOfIsAlgebraic R C S hS hgen hn := by
  apply DFunLike.ext
  rintro ⟨a, σ⟩
  change coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ) =
    gradedClassificationEquiv R C S hS hgen hn (a, σ)
  rw [coefficientDomainGradedClassificationEquiv_apply, gradedClassificationEquiv_apply]

end OrlikSolomon.HyperplaneGT
