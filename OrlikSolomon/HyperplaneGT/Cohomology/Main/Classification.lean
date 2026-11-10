/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Actions
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain

/-!
# Reconstruction of the actual marked cohomology diagrams

The proved pure classifications transport through A04 to the actual ordinary diagonal
and degree-one/cup-kernel diagram groups. The same coefficient unit acts on every stage
and on the common target; the Galois factor uses the covariant hyperplane label. Quotients
are by the literal central scalar ranges. All theory content comes from the existing
C1–C5 ordinary theory, without additional generation or comparison hypotheses.

Forward expansion equations are plain rewrite rules, preserving ordinary two-sided
equivalence cancellation under `simp`.

Blueprint: E01 (`thm:e01`).
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

/-- A04 identifies the quotient by the actual scalar range with the pure quotient, over
every commutative ring. -/
def DiagramAut.scalarQuotientComparison :
    (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) ≃*
      (HyperplaneGT.DiagramAut R C S ⧸ HyperplaneGT.DiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.congr _ _ (degreeOneDiagramEquiv T C S)
    (degreeOneDiagramEquiv_map_scalarSubgroup T C S)

/-- The quotient comparison retains the actual diagram representative. -/
@[simp]
theorem DiagramAut.scalarQuotientComparison_map (g : DiagramAut T C S) :
    scalarQuotientComparison T C S (scalarQuotientMap T C S g) =
      HyperplaneGT.DiagramAut.scalarQuotientMap R C S (degreeOneDiagramEquiv T C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

/-- A04 identifies the quotient by the actual scalar range with the pure quotient, over
every commutative ring. -/
def GradedDiagramAut.scalarQuotientComparison :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃*
      (HyperplaneGT.GradedDiagramAut R C S ⧸ HyperplaneGT.GradedDiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.congr _ _ (gradedDiagramEquiv T C S) (gradedDiagramEquiv_map_scalarSubgroup T C S)

/-- The quotient comparison retains the actual diagram representative. -/
@[simp]
theorem GradedDiagramAut.scalarQuotientComparison_map (g : GradedDiagramAut T C S) :
    scalarQuotientComparison T C S (scalarQuotientMap T C S g) =
      HyperplaneGT.GradedDiagramAut.scalarQuotientMap R C S (gradedDiagramEquiv T C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

section Local

variable [IsLocalRing R]

/-- The actual degree-one and entire cup-kernel
diagram is classified by one unit and one base-field automorphism.
Blueprint: E01 (`thm:e01`). -/
def localQuadraticReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut T C S :=
  (quadraticAutEquiv R C S hS hgen hn).trans (degreeOneDiagramEquiv T C S).symm

/-- The classification is literally scalar action followed by coefficient-linear Galois
presentation transport. -/
theorem localQuadraticReconstruction_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    localQuadraticReconstruction T C S hS hgen hn (a, σ) =
      scalarQuadraticAction T C S a * galoisQuadraticAction T C S σ := by
  change (degreeOneDiagramEquiv T C S).symm (quadraticAutEquiv R C S hS hgen hn (a, σ)) = _
  rw [quadraticAutEquiv_apply, map_mul]
  rfl

/-- The actual inverse reads the same scalar and Galois coordinates after A04. -/
theorem localQuadraticReconstruction_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    (localQuadraticReconstruction T C S hS hgen hn).symm g =
      (quadraticAutEquiv R C S hS hgen hn).symm (degreeOneDiagramEquiv T C S g) := rfl

/-- Reconstruction followed by coordinate extraction recovers both parameters. -/
theorem localQuadraticReconstruction_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (localQuadraticReconstruction T C S hS hgen hn).symm
      (localQuadraticReconstruction T C S hS hgen hn p) = p :=
  (localQuadraticReconstruction T C S hS hgen hn).symm_apply_apply p

/-- Extracting and reconstructing recovers the entire actual diagram and common target. -/
theorem localQuadraticReconstruction_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    localQuadraticReconstruction T C S hS hgen hn
      ((localQuadraticReconstruction T C S hS hgen hn).symm g) = g :=
  (localQuadraticReconstruction T C S hS hgen hn).apply_symm_apply g

/-- In canonical coordinates the actual reconstruction is the existing pure classification.
-/
@[simp]
theorem degreeOneDiagramEquiv_localQuadraticReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (localQuadraticReconstruction T C S hS hgen hn p) =
      quadraticAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The actual quadratic diagram modulo its literal scalar range
is canonically the Galois group. Blueprint: E01 (`thm:e01`). -/
def DiagramAut.localScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) ≃* (k ≃ₐ[k₀] k) :=
  (DiagramAut.scalarQuotientComparison T C S).trans
    (HyperplaneGT.DiagramAut.scalarQuotientEquiv R C S hS hgen hn)

/-- The actual quotient map extracts exactly the Galois coordinate of reconstruction. -/
@[simp]
theorem DiagramAut.localScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((localQuadraticReconstruction T C S hS hgen hn).symm g).2 := by
  change HyperplaneGT.DiagramAut.scalarQuotientEquiv R C S hS hgen hn
    (scalarQuotientComparison T C S (scalarQuotientMap T C S g)) = _
  rw [scalarQuotientComparison_map, HyperplaneGT.DiagramAut.scalarQuotientEquiv_map]
  rfl

/-- The actual full ordinary diagonal
diagram is classified by one unit and one base-field automorphism.
Blueprint: E01 (`thm:e01`). -/
def localGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut T C S :=
  (gradedClassificationEquiv R C S hS hgen hn).trans (gradedDiagramEquiv T C S).symm

/-- The classification is literally scalar action followed by coefficient-linear Galois
presentation transport. -/
theorem localGradedReconstruction_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    localGradedReconstruction T C S hS hgen hn (a, σ) =
      scalarGradedAction T C S a * galoisGradedAction T C S σ := by
  change (gradedDiagramEquiv T C S).symm (gradedClassificationEquiv R C S hS hgen hn (a, σ)) = _
  rw [gradedClassificationEquiv_apply, map_mul]
  rfl

/-- The actual inverse reads the same scalar and Galois coordinates after A04. -/
theorem localGradedReconstruction_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (localGradedReconstruction T C S hS hgen hn).symm g =
      (gradedClassificationEquiv R C S hS hgen hn).symm (gradedDiagramEquiv T C S g) := rfl

/-- Reconstruction followed by coordinate extraction recovers both parameters. -/
theorem localGradedReconstruction_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (localGradedReconstruction T C S hS hgen hn).symm
      (localGradedReconstruction T C S hS hgen hn p) = p :=
  (localGradedReconstruction T C S hS hgen hn).symm_apply_apply p

/-- Extracting and reconstructing recovers the entire actual diagram and common target. -/
theorem localGradedReconstruction_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localGradedReconstruction T C S hS hgen hn
      ((localGradedReconstruction T C S hS hgen hn).symm g) = g :=
  (localGradedReconstruction T C S hS hgen hn).apply_symm_apply g

/-- In canonical coordinates the actual reconstruction is the existing pure classification.
-/
@[simp]
theorem gradedDiagramEquiv_localGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (localGradedReconstruction T C S hS hgen hn p) =
      gradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The actual full graded diagram modulo its literal scalar range
is canonically the Galois group. Blueprint: E01 (`thm:e01`). -/
def GradedDiagramAut.localScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃* (k ≃ₐ[k₀] k) :=
  (GradedDiagramAut.scalarQuotientComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn)

/-- The actual quotient map extracts exactly the Galois coordinate of reconstruction. -/
@[simp]
theorem GradedDiagramAut.localScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((localGradedReconstruction T C S hS hgen hn).symm g).2 := by
  change HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
    (scalarQuotientComparison T C S (scalarQuotientMap T C S g)) = _
  rw [scalarQuotientComparison_map, HyperplaneGT.GradedDiagramAut.scalarQuotientEquiv_map]
  rfl

/-- Degree-one restriction is an equivalence of the actual full and quadratic groups after
reconstruction. Its forward map is the literal A04 restriction. Blueprint: E01 (`thm:e01`). -/
def localRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃* DiagramAut T C S :=
  (gradedDiagramEquiv T C S).trans
    ((gradedAutEquiv R C S hS hgen hn).trans (degreeOneDiagramEquiv T C S).symm)

/-- The actual restriction equivalence applies the existing degree-one restriction. -/
theorem localRestrictionEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    localRestrictionEquiv T C S hS hgen hn g = GradedDiagramAut.toQuadratic T C S g := by
  apply (degreeOneDiagramEquiv T C S).injective
  rw [GradedDiagramAut.toQuadratic_comparison]
  exact (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- Both reconstructions restrict to the same scalar and Galois family. -/
@[simp]
theorem toQuadratic_localGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (localGradedReconstruction T C S hS hgen hn p) =
      localQuadraticReconstruction T C S hS hgen hn p := by
  rcases p with ⟨a, σ⟩
  rw [localGradedReconstruction_apply, map_mul, toQuadratic_scalarGradedAction,
    toQuadratic_galoisGradedAction, localQuadraticReconstruction_apply]

/-- The actual stage logarithmic generator uses the same primal scalar and covariant label.
-/
theorem localQuadraticReconstruction_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) := by
  rw [localQuadraticReconstruction_apply, DiagramAut.stageEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAction_stage_generator, scalarQuadraticAction_stage]

/-- The same unit acts on every vector of the actual common degree-one target. -/
@[simp]
theorem localQuadraticReconstruction_target (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticReconstruction T C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x := by
  rw [localQuadraticReconstruction_apply, DiagramAut.targetEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAction_target, scalarQuadraticAction_target]

/-- The whole actual tagged marking square uses that same target scalar. -/
theorem localQuadraticReconstruction_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (localQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) := by
  have he := LinearMap.congr_fun
    ((localQuadraticReconstruction T C S hS hgen hn (a, σ)).marking_naturality A w hw) x
  change (localQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
    (componentPull T (w.schemeMap D hw) 1 x) = componentPull T (w.schemeMap D hw) 1
      ((localQuadraticReconstruction T C S hS hgen hn (a, σ)).targetEquiv x) at he
  simpa only [localQuadraticReconstruction_target] using he

/-- On a whole ordinary stage component, the scalar is the degree power and the Galois
part is the coefficient-linear OS transport. -/
theorem localGradedReconstruction_stage_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (localGradedReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) := by
  rw [localGradedReconstruction_apply, GradedDiagramAut.stageEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAction_stage]
  have hz : T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) ∈
      diagonalDegree T (D.complement A.val.val) q := by
    rw [← map_diagonalEquiv_degree T A.val.val q]
    exact ⟨_, galoisOSAlgebraEquiv_mem_degree R A.val σ hx, rfl⟩
  exact scalarGradedAction_stage_degree T C S a A q ⟨_, hz⟩

/-- The common actual target has the same degree-power scalar and no Galois contribution.
-/
theorem localGradedReconstruction_target_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (localGradedReconstruction T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) := by
  rw [localGradedReconstruction_apply, GradedDiagramAut.targetEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAction_target]
  exact scalarGradedAction_target_degree T C S a q x

/-- The full actual logarithmic-generator action has the same degree-one formula. -/
theorem localGradedReconstruction_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (localGradedReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) := by
  rw [localGradedReconstruction_stage_degree T C S hS hgen hn a σ A 1 _
    (OSAlgebra.generator_mem_degree R A.val.val H), pow_one,
    galoisOSAlgebraEquiv_generator]


/-- The direct actual Galois class is a section of the canonical quotient equivalence. -/
@[simp]
theorem DiagramAut.localScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientSection T C S σ) = σ := by
  have he : localQuadraticReconstruction T C S hS hgen hn (1, σ) =
      galoisQuadraticAction T C S σ := by
    rw [localQuadraticReconstruction_apply, map_one, one_mul]
  change localScalarQuotientEquiv T C S hS hgen hn
    (scalarQuotientMap T C S (galoisQuadraticAction T C S σ)) = σ
  rw [localScalarQuotientEquiv_map, ← he, MulEquiv.symm_apply_apply]

/-- The explicit quotient inverse is the class of the existing actual Galois family. -/
theorem DiagramAut.localScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientEquiv T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ := by
  apply (localScalarQuotientEquiv T C S hS hgen hn).injective
  simp

/-- The Galois class section followed by its quotient projection recovers every class. -/
theorem DiagramAut.scalarQuotientSection_localScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientSection T C S (localScalarQuotientEquiv T C S hS hgen hn q) = q := by
  rw [← localScalarQuotientEquiv_symm_apply]
  exact (localScalarQuotientEquiv T C S hS hgen hn).symm_apply_apply q

/-- The direct actual Galois class is a section of the canonical quotient equivalence. -/
@[simp]
theorem GradedDiagramAut.localScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    localScalarQuotientEquiv T C S hS hgen hn (scalarQuotientSection T C S σ) = σ := by
  have he : localGradedReconstruction T C S hS hgen hn (1, σ) =
      galoisGradedAction T C S σ := by
    rw [localGradedReconstruction_apply, map_one, one_mul]
  change localScalarQuotientEquiv T C S hS hgen hn
    (scalarQuotientMap T C S (galoisGradedAction T C S σ)) = σ
  rw [localScalarQuotientEquiv_map, ← he, MulEquiv.symm_apply_apply]

/-- The explicit quotient inverse is the class of the existing actual Galois family. -/
theorem GradedDiagramAut.localScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (localScalarQuotientEquiv T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ := by
  apply (localScalarQuotientEquiv T C S hS hgen hn).injective
  simp

/-- The Galois class section followed by its quotient projection recovers every class. -/
theorem GradedDiagramAut.scalarQuotientSection_localScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientSection T C S (localScalarQuotientEquiv T C S hS hgen hn q) = q := by
  rw [← localScalarQuotientEquiv_symm_apply]
  exact (localScalarQuotientEquiv T C S hS hgen hn).symm_apply_apply q

end Local

section Domain

variable [IsDomain R]

/-- The actual degree-one and entire cup-kernel
diagram is classified by one unit and one base-field automorphism.
Blueprint: E01 (`thm:e01`). -/
def domainQuadraticReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut T C S :=
  (coefficientDomainAutEquiv R C S hS hgen hn).trans (degreeOneDiagramEquiv T C S).symm

/-- The classification is literally scalar action followed by coefficient-linear Galois
presentation transport. -/
theorem domainQuadraticReconstruction_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    domainQuadraticReconstruction T C S hS hgen hn (a, σ) =
      scalarQuadraticAction T C S a * galoisQuadraticAction T C S σ := by
  change (degreeOneDiagramEquiv T C S).symm (coefficientDomainAutEquiv R C S hS hgen hn (a, σ)) = _
  rw [coefficientDomainAutEquiv_apply, map_mul]
  rfl

/-- The actual inverse reads the same scalar and Galois coordinates after A04. -/
theorem domainQuadraticReconstruction_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    (domainQuadraticReconstruction T C S hS hgen hn).symm g =
      (coefficientDomainAutEquiv R C S hS hgen hn).symm (degreeOneDiagramEquiv T C S g) := rfl

/-- Reconstruction followed by coordinate extraction recovers both parameters. -/
theorem domainQuadraticReconstruction_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (domainQuadraticReconstruction T C S hS hgen hn).symm
      (domainQuadraticReconstruction T C S hS hgen hn p) = p :=
  (domainQuadraticReconstruction T C S hS hgen hn).symm_apply_apply p

/-- Extracting and reconstructing recovers the entire actual diagram and common target. -/
theorem domainQuadraticReconstruction_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainQuadraticReconstruction T C S hS hgen hn
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g) = g :=
  (domainQuadraticReconstruction T C S hS hgen hn).apply_symm_apply g

/-- In canonical coordinates the actual reconstruction is the existing pure classification.
-/
@[simp]
theorem degreeOneDiagramEquiv_domainQuadraticReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    degreeOneDiagramEquiv T C S (domainQuadraticReconstruction T C S hS hgen hn p) =
      coefficientDomainAutEquiv R C S hS hgen hn p :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The actual quadratic diagram modulo its literal scalar range
is canonically the Galois group. Blueprint: E01 (`thm:e01`). -/
def DiagramAut.domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut T C S ⧸ DiagramAut.scalarSubgroup T C S) ≃* (k ≃ₐ[k₀] k) :=
  (DiagramAut.scalarQuotientComparison T C S).trans
    (HyperplaneGT.DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn)

/-- The actual quotient map extracts exactly the Galois coordinate of reconstruction. -/
@[simp]
theorem DiagramAut.domainScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut T C S) :
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((domainQuadraticReconstruction T C S hS hgen hn).symm g).2 := by
  change HyperplaneGT.DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
    (scalarQuotientComparison T C S (scalarQuotientMap T C S g)) = _
  rw [scalarQuotientComparison_map, HyperplaneGT.DiagramAut.domainScalarQuotientEquiv_map]
  rfl

/-- The actual full ordinary diagonal
diagram is classified by one unit and one base-field automorphism.
Blueprint: E01 (`thm:e01`). -/
def domainGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut T C S :=
  (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).trans
    (gradedDiagramEquiv T C S).symm

/-- The classification is literally scalar action followed by coefficient-linear Galois
presentation transport. -/
theorem domainGradedReconstruction_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    domainGradedReconstruction T C S hS hgen hn (a, σ) =
      scalarGradedAction T C S a * galoisGradedAction T C S σ := by
  change (gradedDiagramEquiv T C S).symm
    (coefficientDomainGradedClassificationEquiv R C S hS hgen hn (a, σ)) =
      _
  rw [coefficientDomainGradedClassificationEquiv_apply, map_mul]
  rfl

/-- The actual inverse reads the same scalar and Galois coordinates after A04. -/
theorem domainGradedReconstruction_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    (domainGradedReconstruction T C S hS hgen hn).symm g =
      (coefficientDomainGradedClassificationEquiv R C S hS hgen hn).symm
        (gradedDiagramEquiv T C S g) := rfl

/-- Reconstruction followed by coordinate extraction recovers both parameters. -/
theorem domainGradedReconstruction_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    (domainGradedReconstruction T C S hS hgen hn).symm
      (domainGradedReconstruction T C S hS hgen hn p) = p :=
  (domainGradedReconstruction T C S hS hgen hn).symm_apply_apply p

/-- Extracting and reconstructing recovers the entire actual diagram and common target. -/
theorem domainGradedReconstruction_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainGradedReconstruction T C S hS hgen hn
      ((domainGradedReconstruction T C S hS hgen hn).symm g) = g :=
  (domainGradedReconstruction T C S hS hgen hn).apply_symm_apply g

/-- In canonical coordinates the actual reconstruction is the existing pure classification.
-/
@[simp]
theorem gradedDiagramEquiv_domainGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    gradedDiagramEquiv T C S (domainGradedReconstruction T C S hS hgen hn p) =
      coefficientDomainGradedClassificationEquiv R C S hS hgen hn p :=
  (gradedDiagramEquiv T C S).apply_symm_apply _

/-- The actual full graded diagram modulo its literal scalar range
is canonically the Galois group. Blueprint: E01 (`thm:e01`). -/
def GradedDiagramAut.domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut T C S ⧸ GradedDiagramAut.scalarSubgroup T C S) ≃* (k ≃ₐ[k₀] k) :=
  (GradedDiagramAut.scalarQuotientComparison T C S).trans
    (HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn)

/-- The actual quotient map extracts exactly the Galois coordinate of reconstruction. -/
@[simp]
theorem GradedDiagramAut.domainScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientMap T C S g) =
      ((domainGradedReconstruction T C S hS hgen hn).symm g).2 := by
  change HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
    (scalarQuotientComparison T C S (scalarQuotientMap T C S g)) = _
  rw [scalarQuotientComparison_map, HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv_map]
  rfl

/-- Degree-one restriction is an equivalence of the actual full and quadratic groups after
reconstruction. Its forward map is the literal A04 restriction. Blueprint: E01 (`thm:e01`). -/
def domainRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut T C S ≃* DiagramAut T C S :=
  (gradedDiagramEquiv T C S).trans
    ((coefficientDomainGradedAutEquiv R C S hS hgen hn).trans (degreeOneDiagramEquiv T C S).symm)

/-- The actual restriction equivalence applies the existing degree-one restriction. -/
theorem domainRestrictionEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut T C S) :
    domainRestrictionEquiv T C S hS hgen hn g = GradedDiagramAut.toQuadratic T C S g := by
  apply (degreeOneDiagramEquiv T C S).injective
  rw [GradedDiagramAut.toQuadratic_comparison]
  exact (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- Both reconstructions restrict to the same scalar and Galois family. -/
@[simp]
theorem toQuadratic_domainGradedReconstruction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (p : Rˣ × (k ≃ₐ[k₀] k)) :
    GradedDiagramAut.toQuadratic T C S (domainGradedReconstruction T C S hS hgen hn p) =
      domainQuadraticReconstruction T C S hS hgen hn p := by
  rcases p with ⟨a, σ⟩
  rw [domainGradedReconstruction_apply, map_mul, toQuadratic_scalarGradedAction,
    toQuadratic_galoisGradedAction, domainQuadraticReconstruction_apply]

/-- The actual stage logarithmic generator uses the same primal scalar and covariant label.
-/
theorem domainQuadraticReconstruction_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv T A.val.val (Finsupp.single H 1)) =
    (a : R) • degreeOneEquiv T A.val.val
      (Finsupp.single (galoisLabelEquiv A.val σ H) 1) := by
  rw [domainQuadraticReconstruction_apply, DiagramAut.stageEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAction_stage_generator, scalarQuadraticAction_stage]

/-- The same unit acts on every vector of the actual common degree-one target. -/
@[simp]
theorem domainQuadraticReconstruction_target (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticReconstruction T C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x := by
  rw [domainQuadraticReconstruction_apply, DiagramAut.targetEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAction_target, scalarQuadraticAction_target]

/-- The whole actual tagged marking square uses that same target scalar. -/
theorem domainQuadraticReconstruction_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne T (twoPunctureArrangement k)) :
    (domainQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull T (w.schemeMap D hw) 1 x) =
    componentPull T (w.schemeMap D hw) 1 ((a : R) • x) := by
  have he := LinearMap.congr_fun
    ((domainQuadraticReconstruction T C S hS hgen hn (a, σ)).marking_naturality A w hw) x
  change (domainQuadraticReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
    (componentPull T (w.schemeMap D hw) 1 x) = componentPull T (w.schemeMap D hw) 1
      ((domainQuadraticReconstruction T C S hS hgen hn (a, σ)).targetEquiv x) at he
  simpa only [domainQuadraticReconstruction_target] using he

/-- On a whole ordinary stage component, the scalar is the degree power and the Galois
part is the coefficient-linear OS transport. -/
theorem domainGradedReconstruction_stage_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (q : ℕ) (x : OSAlgebra R A.val.val)
    (hx : x ∈ OSAlgebra.degree R A.val.val q) :
    (domainGradedReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val x) =
    (a : R)^q • T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) := by
  rw [domainGradedReconstruction_apply, GradedDiagramAut.stageEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAction_stage]
  have hz : T.diagonalEquiv A.val.val (galoisOSAlgebraEquiv R A.val σ x) ∈
      diagonalDegree T (D.complement A.val.val) q := by
    rw [← map_diagonalEquiv_degree T A.val.val q]
    exact ⟨_, galoisOSAlgebraEquiv_mem_degree R A.val σ hx, rfl⟩
  exact scalarGradedAction_stage_degree T C S a A q ⟨_, hz⟩

/-- The common actual target has the same degree-power scalar and no Galois contribution.
-/
theorem domainGradedReconstruction_target_degree (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q) :
    (domainGradedReconstruction T C S hS hgen hn (a, σ)).targetEquiv
      (x : diagonal T _) = (a : R)^q • (x : diagonal T _) := by
  rw [domainGradedReconstruction_apply, GradedDiagramAut.targetEquiv_mul, AlgEquiv.mul_apply,
    galoisGradedAction_target]
  exact scalarGradedAction_target_degree T C S a q x

/-- The full actual logarithmic-generator action has the same degree-one formula. -/
theorem domainGradedReconstruction_stage_generator (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (domainGradedReconstruction T C S hS hgen hn (a, σ)).stageEquiv A
      (T.diagonalEquiv A.val.val (OSAlgebra.generator R A.val.val H)) =
    (a : R) • T.diagonalEquiv A.val.val
      (OSAlgebra.generator R A.val.val (galoisLabelEquiv A.val σ H)) := by
  rw [domainGradedReconstruction_stage_degree T C S hS hgen hn a σ A 1 _
    (OSAlgebra.generator_mem_degree R A.val.val H), pow_one,
    galoisOSAlgebraEquiv_generator]


/-- The direct actual Galois class is a section of the canonical quotient equivalence. -/
@[simp]
theorem DiagramAut.domainScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientSection T C S σ) = σ := by
  have he : domainQuadraticReconstruction T C S hS hgen hn (1, σ) =
      galoisQuadraticAction T C S σ := by
    rw [domainQuadraticReconstruction_apply, map_one, one_mul]
  change domainScalarQuotientEquiv T C S hS hgen hn
    (scalarQuotientMap T C S (galoisQuadraticAction T C S σ)) = σ
  rw [domainScalarQuotientEquiv_map, ← he, MulEquiv.symm_apply_apply]

/-- The explicit quotient inverse is the class of the existing actual Galois family. -/
theorem DiagramAut.domainScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientEquiv T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ := by
  apply (domainScalarQuotientEquiv T C S hS hgen hn).injective
  simp

/-- The Galois class section followed by its quotient projection recovers every class. -/
theorem DiagramAut.scalarQuotientSection_domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientSection T C S (domainScalarQuotientEquiv T C S hS hgen hn q) = q := by
  rw [← domainScalarQuotientEquiv_symm_apply]
  exact (domainScalarQuotientEquiv T C S hS hgen hn).symm_apply_apply q

/-- The direct actual Galois class is a section of the canonical quotient equivalence. -/
@[simp]
theorem GradedDiagramAut.domainScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainScalarQuotientEquiv T C S hS hgen hn (scalarQuotientSection T C S σ) = σ := by
  have he : domainGradedReconstruction T C S hS hgen hn (1, σ) =
      galoisGradedAction T C S σ := by
    rw [domainGradedReconstruction_apply, map_one, one_mul]
  change domainScalarQuotientEquiv T C S hS hgen hn
    (scalarQuotientMap T C S (galoisGradedAction T C S σ)) = σ
  rw [domainScalarQuotientEquiv_map, ← he, MulEquiv.symm_apply_apply]

/-- The explicit quotient inverse is the class of the existing actual Galois family. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientEquiv T C S hS hgen hn).symm σ =
      scalarQuotientSection T C S σ := by
  apply (domainScalarQuotientEquiv T C S hS hgen hn).injective
  simp

/-- The Galois class section followed by its quotient projection recovers every class. -/
theorem GradedDiagramAut.scalarQuotientSection_domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut T C S ⧸ scalarSubgroup T C S) :
    scalarQuotientSection T C S (domainScalarQuotientEquiv T C S hS hgen hn q) = q := by
  rw [← domainScalarQuotientEquiv_symm_apply]
  exact (domainScalarQuotientEquiv T C S hS hgen hn).symm_apply_apply q

end Domain

/-- The actual domain and local constructions agree on their common coefficient scope. -/
theorem domainQuadraticReconstruction_eq_localQuadraticReconstruction [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainQuadraticReconstruction T C S hS hgen hn =
      localQuadraticReconstruction T C S hS hgen hn := by
  unfold domainQuadraticReconstruction localQuadraticReconstruction
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv]

/-- The actual domain and local constructions agree on their common coefficient scope. -/
theorem domainGradedReconstruction_eq_localGradedReconstruction [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainGradedReconstruction T C S hS hgen hn = localGradedReconstruction T C S hS hgen hn := by
  unfold domainGradedReconstruction localGradedReconstruction
  rw [coefficientDomainGradedClassificationEquiv_eq_gradedClassificationEquiv]

/-- The actual domain and local constructions agree on their common coefficient scope. -/
theorem domainRestrictionEquiv_eq_localRestrictionEquiv [IsDomain R] [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainRestrictionEquiv T C S hS hgen hn = localRestrictionEquiv T C S hS hgen hn := by
  unfold domainRestrictionEquiv localRestrictionEquiv
  rw [coefficientDomainGradedAutEquiv_eq_gradedAutEquiv]

/-- The literal actual scalar quotients agree on the local/domain overlap. -/
theorem DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientEquiv T C S hS hgen hn = localScalarQuotientEquiv T C S hS hgen hn := by
  unfold domainScalarQuotientEquiv localScalarQuotientEquiv
  rw [HyperplaneGT.DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv]

/-- The literal actual scalar quotients agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv
    [IsDomain R] [IsLocalRing R] (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientEquiv T C S hS hgen hn = localScalarQuotientEquiv T C S hS hgen hn := by
  unfold domainScalarQuotientEquiv localScalarQuotientEquiv
  rw [HyperplaneGT.GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv]

end OrlikSolomon.HyperplaneGT.Cohomology
