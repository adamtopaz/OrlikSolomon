/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Comparison
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.GradedScalar
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Splitting
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Scalar and Galois actions on the actual cohomology diagrams

Transport the existing pure actions through the proved degree-one/cup-kernel and full
ordinary-diagonal comparisons. These actions and their literal central scalar ranges exist
over every commutative coefficient ring. Field automorphisms act by coefficient-linear
presentation transport; no semilinear coordinate map is asserted to induce an ordinary
geometric pullback.

Blueprint: the action formulas in E01 (`thm:e01`).
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

/-- The scalar action on the actual degree-one/cup-kernel diagram,
transported through A04. Blueprint: E01 (`thm:e01`). -/
def scalarQuadraticAction : (Rˣ) →* DiagramAut T C S :=
  (degreeOneDiagramEquiv T C S).symm.toMonoidHom.comp (HyperplaneGT.scalarQuadraticAction R C S)

/-- The actual action has exactly the existing pure action in canonical coordinates. -/
@[simp]
theorem degreeOneDiagramEquiv_scalarQuadraticAction (a : Rˣ) :
    degreeOneDiagramEquiv T C S (scalarQuadraticAction T C S a) =
      HyperplaneGT.scalarQuadraticAction R C S a :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The Galois action on the actual degree-one/cup-kernel diagram,
transported through A04. Blueprint: E01 (`thm:e01`). -/
def galoisQuadraticAction : (k ≃ₐ[k₀] k) →* DiagramAut T C S :=
  (degreeOneDiagramEquiv T C S).symm.toMonoidHom.comp (HyperplaneGT.galoisQuadraticAction R C S)

/-- The actual action has exactly the existing pure action in canonical coordinates. -/
@[simp]
theorem degreeOneDiagramEquiv_galoisQuadraticAction (a : k ≃ₐ[k₀] k) :
    degreeOneDiagramEquiv T C S (galoisQuadraticAction T C S a) =
      HyperplaneGT.galoisQuadraticAction R C S a :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The actual scalar action is faithful, including its one common target. -/
theorem scalarQuadraticAction_injective : Function.Injective (scalarQuadraticAction T C S) :=
  (degreeOneDiagramEquiv T C S).symm.injective.comp
    (HyperplaneGT.scalarQuadraticAction_injective R C S)

/-- The actual scalar family commutes with every actual diagram automorphism. -/
theorem scalarQuadraticAction_commute (a : Rˣ) (g : DiagramAut T C S) :
    Commute (scalarQuadraticAction T C S a) g := by
  apply Commute.of_map (degreeOneDiagramEquiv T C S).injective
  simpa only [degreeOneDiagramEquiv_scalarQuadraticAction, MulEquiv.coe_toMonoidHom,
    HyperplaneGT.scalarQuadraticAction_apply] using
    HyperplaneGT.scalarQuadraticAut_commute R C S a (degreeOneDiagramEquiv T C S g)

/-- The literal range of uniform scalar families on the actual diagram. -/
def DiagramAut.scalarSubgroup : Subgroup (DiagramAut T C S) := (scalarQuadraticAction T C S).range

/-- The actual scalar range lies in the center; equality with the whole center is not needed.
-/
theorem DiagramAut.scalarSubgroup_le_center :
    scalarSubgroup T C S ≤ Subgroup.center (DiagramAut T C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarQuadraticAction_commute T C S a g).eq.symm

/-- Centrality makes the actual scalar range normal over arbitrary coefficients. -/
instance DiagramAut.scalarSubgroup_normal : (DiagramAut.scalarSubgroup T C S).Normal :=
  Subgroup.normal_of_le_center (DiagramAut.scalarSubgroup_le_center T C S)

/-- A04 carries the literal scalar range onto the literal pure scalar range. -/
theorem degreeOneDiagramEquiv_map_scalarSubgroup :
    (DiagramAut.scalarSubgroup T C S).map (degreeOneDiagramEquiv T C S).toMonoidHom =
      HyperplaneGT.DiagramAut.scalarSubgroup R C S := by
  ext g
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (degreeOneDiagramEquiv_scalarQuadraticAction T C S a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarQuadraticAction T C S a, ⟨a, rfl⟩,
      degreeOneDiagramEquiv_scalarQuadraticAction T C S a⟩

/-- The canonical quotient map by the actual scalar range. -/
def DiagramAut.scalarQuotientMap :
    DiagramAut T C S →* (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :=
  QuotientGroup.mk' (DiagramAut.scalarSubgroup T C S)

/-- The actual Galois family gives a canonical class in the actual scalar quotient. -/
def DiagramAut.scalarQuotientSection :
    (k ≃ₐ[k₀] k) →* (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) :=
  (DiagramAut.scalarQuotientMap T C S).comp (galoisQuadraticAction T C S)

/-- The scalar action on the actual full diagonal diagram,
transported through A04. Blueprint: E01 (`thm:e01`). -/
def scalarGradedAction : (Rˣ) →* GradedDiagramAut T C S :=
  (gradedDiagramEquiv T C S).symm.toMonoidHom.comp (HyperplaneGT.scalarGradedAction R C S)

/-- The actual action has exactly the existing pure action in canonical coordinates. -/
@[simp]
theorem gradedDiagramEquiv_scalarGradedAction (a : Rˣ) :
    gradedDiagramEquiv T C S (scalarGradedAction T C S a) =
      HyperplaneGT.scalarGradedAction R C S a :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The Galois action on the actual full diagonal diagram,
transported through A04. Blueprint: E01 (`thm:e01`). -/
def galoisGradedAction : (k ≃ₐ[k₀] k) →* GradedDiagramAut T C S :=
  (gradedDiagramEquiv T C S).symm.toMonoidHom.comp (HyperplaneGT.galoisGradedAction R C S)

/-- The actual action has exactly the existing pure action in canonical coordinates. -/
@[simp]
theorem gradedDiagramEquiv_galoisGradedAction (a : k ≃ₐ[k₀] k) :
    gradedDiagramEquiv T C S (galoisGradedAction T C S a) =
      HyperplaneGT.galoisGradedAction R C S a :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The actual scalar action is faithful, including its one common target. -/
theorem scalarGradedAction_injective : Function.Injective (scalarGradedAction T C S) :=
  (gradedDiagramEquiv T C S).symm.injective.comp
    (HyperplaneGT.scalarGradedAction_injective R C S)

/-- The actual scalar family commutes with every actual diagram automorphism. -/
theorem scalarGradedAction_commute (a : Rˣ) (g : GradedDiagramAut T C S) :
    Commute (scalarGradedAction T C S a) g := by
  apply Commute.of_map (gradedDiagramEquiv T C S).injective
  simpa only [gradedDiagramEquiv_scalarGradedAction, MulEquiv.coe_toMonoidHom,
    HyperplaneGT.scalarGradedAction_apply] using
    HyperplaneGT.scalarGradedAut_commute R C S a (gradedDiagramEquiv T C S g)

/-- The literal range of uniform scalar families on the actual diagram. -/
def GradedDiagramAut.scalarSubgroup : Subgroup (GradedDiagramAut T C S) :=
  (scalarGradedAction T C S).range

/-- The actual scalar range lies in the center; equality with the whole center is not needed.
-/
theorem GradedDiagramAut.scalarSubgroup_le_center :
    scalarSubgroup T C S ≤ Subgroup.center (GradedDiagramAut T C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarGradedAction_commute T C S a g).eq.symm

/-- Centrality makes the actual scalar range normal over arbitrary coefficients. -/
instance GradedDiagramAut.scalarSubgroup_normal : (GradedDiagramAut.scalarSubgroup T C S).Normal :=
  Subgroup.normal_of_le_center (GradedDiagramAut.scalarSubgroup_le_center T C S)

/-- A04 carries the literal scalar range onto the literal pure scalar range. -/
theorem gradedDiagramEquiv_map_scalarSubgroup :
    (GradedDiagramAut.scalarSubgroup T C S).map (gradedDiagramEquiv T C S).toMonoidHom =
      HyperplaneGT.GradedDiagramAut.scalarSubgroup R C S := by
  ext g
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (gradedDiagramEquiv_scalarGradedAction T C S a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAction T C S a, ⟨a, rfl⟩,
      gradedDiagramEquiv_scalarGradedAction T C S a⟩

/-- The canonical quotient map by the actual scalar range. -/
def GradedDiagramAut.scalarQuotientMap :
    GradedDiagramAut T C S →* (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :=
  QuotientGroup.mk' (GradedDiagramAut.scalarSubgroup T C S)

/-- The actual Galois family gives a canonical class in the actual scalar quotient. -/
def GradedDiagramAut.scalarQuotientSection :
    (k ≃ₐ[k₀] k) →* (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) :=
  (GradedDiagramAut.scalarQuotientMap T C S).comp (galoisGradedAction T C S)

/-- The actual degree-one scalar action multiplies every stage vector by the given unit. -/
@[simp]
theorem scalarQuadraticAction_stage (a : Rˣ) (A : C.Stage)
    (x : degreeOne T A.val.val) :
    (scalarQuadraticAction T C S a).stageEquiv A x = (a : R) • x := by
  obtain ⟨x, rfl⟩ := (degreeOneEquiv T A.val.val).surjective x
  change ((degreeOneDiagramEquiv T C S).symm _).stageEquiv A _ = _
  rw [degreeOneDiagramEquiv_symm_stage]
  simp

/-- The one actual common target carries the same scalar as every stage. -/
@[simp]
theorem scalarQuadraticAction_target (a : Rˣ)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (scalarQuadraticAction T C S a).targetEquiv x = (a : R) • x := by
  obtain ⟨x, rfl⟩ := (targetDegreeOneEquiv T).surjective x
  change ((degreeOneDiagramEquiv T C S).symm _).targetEquiv _ = _
  rw [degreeOneDiagramEquiv_symm_target]
  simp

/-- The actual Galois family fixes the one common degree-one target identically. -/
@[simp]
theorem galoisQuadraticAction_target (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (galoisQuadraticAction T C S σ).targetEquiv x = x := by
  obtain ⟨x, rfl⟩ := (targetDegreeOneEquiv T).surjective x
  change ((degreeOneDiagramEquiv T C S).symm _).targetEquiv _ = _
  rw [degreeOneDiagramEquiv_symm_target]
  simp

/-- On actual canonical logarithmic generators, Galois transport uses the covariant label.
-/
theorem galoisQuadraticAction_stage_generator (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) :
    (galoisQuadraticAction T C S σ).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    degreeOneEquiv T A.val.val (Finsupp.single (galoisLabelEquiv A.val σ H) 1) := by
  change ((degreeOneDiagramEquiv T C S).symm _).stageEquiv A _ = _
  rw [degreeOneDiagramEquiv_symm_stage]
  simp only [HyperplaneGT.galoisQuadraticAction_apply,
    galoisQuadraticAut_stageEquiv_single]

/-- The actual full scalar action multiplies every vector of ordinary degree q by a^q. -/
theorem scalarGradedAction_stage_degree (a : Rˣ) (A : C.Stage) (q : ℕ)
    (x : diagonalDegree T (D.complement A.val.val) q) :
    (scalarGradedAction T C S a).stageEquiv A (x : diagonal T _) =
      (a : R)^q • (x : diagonal T _) := by
  have hx : (x : diagonal T _) ∈ (OSAlgebra.degree R A.val.val q).map
      (T.diagonalEquiv A.val.val).toLinearMap :=
    (map_diagonalEquiv_degree T A.val.val q).symm ▸ x.property
  obtain ⟨y, hy, hxy⟩ := hx
  change T.diagonalEquiv A.val.val y = (x : diagonal T _) at hxy
  rw [← hxy]
  change ((gradedDiagramEquiv T C S).symm _).stageEquiv A _ = _
  rw [gradedDiagramEquiv_symm_stage]
  simp only [HyperplaneGT.scalarGradedAction_apply,
    scalarGradedAut_stage_apply_of_mem_degree R C S a A q y hy, map_smul]

/-- The same degree power acts on the whole actual common-target summand. -/
theorem scalarGradedAction_target_degree (a : Rˣ) (q : ℕ)
    (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (scalarGradedAction T C S a).targetEquiv (x : diagonal T _) =
      (a : R)^q • (x : diagonal T _) := by
  have hx : (x : diagonal T _) ∈ (OSAlgebra.degree R (twoPunctureArrangement k) q).map
      (T.diagonalEquiv (twoPunctureArrangement k)).toLinearMap :=
    (map_diagonalEquiv_degree T (twoPunctureArrangement k) q).symm ▸ x.property
  obtain ⟨y, hy, hxy⟩ := hx
  change T.diagonalEquiv (twoPunctureArrangement k) y = (x : diagonal T _) at hxy
  rw [← hxy]
  change ((gradedDiagramEquiv T C S).symm _).targetEquiv _ = _
  rw [gradedDiagramEquiv_symm_target]
  simp only [HyperplaneGT.scalarGradedAction_apply,
    scalarGradedAut_target_apply_of_mem_degree R C S a q y hy, map_smul]

/-- On every whole stage algebra, the actual Galois action is presentation transport. -/
theorem galoisGradedAction_stage (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (x : OSAlgebra R A.val.val) :
    (galoisGradedAction T C S σ).stageEquiv A (T.diagonalEquiv A.val.val x) =
      T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) := by
  change ((gradedDiagramEquiv T C S).symm _).stageEquiv A _ = _
  rw [gradedDiagramEquiv_symm_stage]
  rfl

/-- The actual full Galois family fixes the entire common target algebra. -/
@[simp]
theorem galoisGradedAction_target (σ : k ≃ₐ[k₀] k) (x : diagonal T (schemeMarkingTarget D)) :
    (galoisGradedAction T C S σ).targetEquiv x = x := by
  obtain ⟨x, rfl⟩ := (T.diagonalEquiv (twoPunctureArrangement k)).surjective x
  change ((gradedDiagramEquiv T C S).symm _).targetEquiv _ = _
  rw [gradedDiagramEquiv_symm_target]
  simp

/-- Actual degree-one restriction carries the full scalar family to its quadratic family.
-/
@[simp]
theorem toQuadratic_scalarGradedAction (a : Rˣ) :
    GradedDiagramAut.toQuadratic T C S (scalarGradedAction T C S a) =
      scalarQuadraticAction T C S a := by
  apply (degreeOneDiagramEquiv T C S).injective
  rw [GradedDiagramAut.toQuadratic_comparison, gradedDiagramEquiv_scalarGradedAction,
    degreeOneDiagramEquiv_scalarQuadraticAction]
  exact HyperplaneGT.toQuadratic_scalarGradedAut R C S a

/-- Actual degree-one restriction carries the full Galois family to its quadratic family. -/
@[simp]
theorem toQuadratic_galoisGradedAction (σ : k ≃ₐ[k₀] k) :
    GradedDiagramAut.toQuadratic T C S (galoisGradedAction T C S σ) =
      galoisQuadraticAction T C S σ := by
  apply (degreeOneDiagramEquiv T C S).injective
  rw [GradedDiagramAut.toQuadratic_comparison, gradedDiagramEquiv_galoisGradedAction,
    degreeOneDiagramEquiv_galoisQuadraticAction]
  rfl

end OrlikSolomon.HyperplaneGT.Cohomology
