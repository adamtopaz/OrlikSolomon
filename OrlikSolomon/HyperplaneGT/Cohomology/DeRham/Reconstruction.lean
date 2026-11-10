/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Diagram
public import OrlikSolomon.HyperplaneGT.Cohomology.Main.Classification
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits

/-!
# Unconditional reconstruction from ordinary de Rham cohomology

The actual ordinary de Rham H¹/cup-kernel and full graded diagram groups are canonically
the product of `kˣ` with the base-field automorphism group. The final statements contain
no supplied cohomology theory. They use the existing constructed characteristic-zero
instance internally and remove Laurent weights only on its diagonal `E^(q,q)`.

The action is `k`-linear, has covariant label action `H ↦ σH`, and scales a degree `q`
class by the primal unit's `q`th power. It is not identified with semilinear transport of
differential forms or pullback along a nonexistent `k`-morphism induced by `σ`.

Supplied cofinal systems need no algebraicity or perfectness hypothesis. The canonical
full-family wrappers use algebraicity solely to construct that system. Every marking uses
one actual two-puncture target, with the same scalar as every stage.

Blueprint: E03 (`cor:e03`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "HdRdegree" => Geometric.DeRham.Cohomology.degree

/-- The canonical scalar family on the actual ordinary quadratic diagram. -/
def scalarQuadraticAction : kˣ →* DiagramAut C S :=
  (quadraticTwistEquiv C S).symm.toMonoidHom.comp (Cohomology.scalarQuadraticAction Tdr C S)

/-- The canonical scalar family on the actual ordinary full graded diagram. -/
def scalarGradedAction : kˣ →* GradedDiagramAut C S :=
  (gradedTwistEquiv C S).symm.toMonoidHom.comp (Cohomology.scalarGradedAction Tdr C S)

/-- The coefficient-linear Galois family on actual ordinary H¹, with covariant labels. -/
def galoisQuadraticAction : (k ≃ₐ[k₀] k) →* DiagramAut C S :=
  (quadraticTwistEquiv C S).symm.toMonoidHom.comp (Cohomology.galoisQuadraticAction Tdr C S)

/-- The coefficient-linear Galois family on the full actual ordinary algebra. -/
def galoisGradedAction : (k ≃ₐ[k₀] k) →* GradedDiagramAut C S :=
  (gradedTwistEquiv C S).symm.toMonoidHom.comp (Cohomology.galoisGradedAction Tdr C S)

variable (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)

/-- **Unconditional ordinary de Rham quadratic reconstruction.** One primal unit and one
base-field automorphism classify the actual H¹/cup-kernel marked diagram.
Blueprint: E03 (`cor:e03`). -/
def quadraticReconstruction : (kˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut C S :=
  (Cohomology.localQuadraticReconstruction Tdr C S hS hgen hn).trans
    (quadraticTwistEquiv C S).symm

/-- **Unconditional ordinary de Rham graded reconstruction.** The same parameters classify
the actual ordinary total cohomology marked diagram. Blueprint: E03 (`cor:e03`). -/
def gradedReconstruction : (kˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut C S :=
  (Cohomology.localGradedReconstruction Tdr C S hS hgen hn).trans
    (gradedTwistEquiv C S).symm

/-- Ordinary degree-one restriction is an equivalence, with the literal restriction as
forward map. Blueprint: E03 (`cor:e03`). -/
def restrictionEquiv : GradedDiagramAut C S ≃* DiagramAut C S :=
  (gradedTwistEquiv C S).trans
    ((Cohomology.localRestrictionEquiv Tdr C S hS hgen hn).trans
      (quadraticTwistEquiv C S).symm)

/-- Reconstruction agrees exactly with E01 under actual quadratic untwisting. -/
@[simp]
theorem quadraticTwistEquiv_quadraticReconstruction (p : kˣ × (k ≃ₐ[k₀] k)) :
    quadraticTwistEquiv C S (quadraticReconstruction C S hS hgen hn p) =
      Cohomology.localQuadraticReconstruction Tdr C S hS hgen hn p :=
  (quadraticTwistEquiv C S).apply_symm_apply _

/-- Reconstruction agrees exactly with E01 under actual full diagonal untwisting. -/
@[simp]
theorem gradedTwistEquiv_gradedReconstruction (p : kˣ × (k ≃ₐ[k₀] k)) :
    gradedTwistEquiv C S (gradedReconstruction C S hS hgen hn p) =
      Cohomology.localGradedReconstruction Tdr C S hS hgen hn p :=
  (gradedTwistEquiv C S).apply_symm_apply _

/-- The quadratic action is precisely scalar followed by coefficient-linear Galois action. -/
theorem quadraticReconstruction_apply (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    quadraticReconstruction C S hS hgen hn (a, σ) =
      scalarQuadraticAction C S a * galoisQuadraticAction C S σ :=
  (congrArg (quadraticTwistEquiv C S).symm
    (Cohomology.localQuadraticReconstruction_apply Tdr C S hS hgen hn a σ)).trans
      ((quadraticTwistEquiv C S).symm.map_mul _ _)

/-- The full action is precisely scalar followed by coefficient-linear Galois action. -/
theorem gradedReconstruction_apply (a : kˣ) (σ : k ≃ₐ[k₀] k) :
    gradedReconstruction C S hS hgen hn (a, σ) =
      scalarGradedAction C S a * galoisGradedAction C S σ := by
  change (gradedTwistEquiv C S).symm
    (Cohomology.localGradedReconstruction Tdr C S hS hgen hn (a, σ)) = _
  rw [Cohomology.localGradedReconstruction_apply Tdr C S hS hgen hn a σ, map_mul]
  rfl

/-- The explicit quadratic inverse reads E01 coordinates after actual untwisting. -/
theorem quadraticReconstruction_symm_apply (g : DiagramAut C S) :
    (quadraticReconstruction C S hS hgen hn).symm g =
      (Cohomology.localQuadraticReconstruction Tdr C S hS hgen hn).symm
        (quadraticTwistEquiv C S g) := rfl

/-- The explicit graded inverse reads E01 coordinates after actual diagonal untwisting. -/
theorem gradedReconstruction_symm_apply (g : GradedDiagramAut C S) :
    (gradedReconstruction C S hS hgen hn).symm g =
      (Cohomology.localGradedReconstruction Tdr C S hS hgen hn).symm
        (gradedTwistEquiv C S g) := rfl

/-- Reconstruction and extraction recover both quadratic parameters. -/
theorem quadraticReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (quadraticReconstruction C S hS hgen hn).symm
      (quadraticReconstruction C S hS hgen hn p) = p :=
  (quadraticReconstruction C S hS hgen hn).symm_apply_apply p

/-- Extraction and reconstruction recover the entire ordinary quadratic diagram. -/
theorem quadraticReconstruction_right_inv (g : DiagramAut C S) :
    quadraticReconstruction C S hS hgen hn
      ((quadraticReconstruction C S hS hgen hn).symm g) = g :=
  (quadraticReconstruction C S hS hgen hn).apply_symm_apply g

/-- Reconstruction and extraction recover both graded parameters. -/
theorem gradedReconstruction_left_inv (p : kˣ × (k ≃ₐ[k₀] k)) :
    (gradedReconstruction C S hS hgen hn).symm
      (gradedReconstruction C S hS hgen hn p) = p :=
  (gradedReconstruction C S hS hgen hn).symm_apply_apply p

/-- Extraction and reconstruction recover the entire ordinary graded diagram. -/
theorem gradedReconstruction_right_inv (g : GradedDiagramAut C S) :
    gradedReconstruction C S hS hgen hn
      ((gradedReconstruction C S hS hgen hn).symm g) = g :=
  (gradedReconstruction C S hS hgen hn).apply_symm_apply g

/-- The restriction equivalence applies the existing literal ordinary H¹ restriction. -/
theorem restrictionEquiv_apply (g : GradedDiagramAut C S) :
    restrictionEquiv C S hS hgen hn g = GradedDiagramAut.toQuadratic C S g :=
  congrArg (quadraticTwistEquiv C S).symm
    (Cohomology.localRestrictionEquiv_apply Tdr C S hS hgen hn (gradedTwistEquiv C S g))

/-- Both ordinary reconstructions have the same unit and field coordinates under literal
degree-one restriction. -/
theorem restrictionEquiv_gradedReconstruction (p : kˣ × (k ≃ₐ[k₀] k)) :
    restrictionEquiv C S hS hgen hn (gradedReconstruction C S hS hgen hn p) =
      quadraticReconstruction C S hS hgen hn p :=
  congrArg (quadraticTwistEquiv C S).symm
    ((congrArg (Cohomology.localRestrictionEquiv Tdr C S hS hgen hn)
      (gradedTwistEquiv_gradedReconstruction C S hS hgen hn p)).trans
        ((Cohomology.localRestrictionEquiv_apply Tdr C S hS hgen hn _).trans
          (Cohomology.toQuadratic_localGradedReconstruction Tdr C S hS hgen hn p)))

/-- Every ordinary H¹ hyperplane generator has the primal scalar and covariant label. -/
theorem quadraticReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (quadraticReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (degreeOneEquiv A.val.val (Finsupp.single H 1)) =
      (a : k) • degreeOneEquiv A.val.val
        (Finsupp.single (galoisLabelEquiv A.val σ H) 1) := by
  exact (congrArg ((quadraticReconstruction C S hS hgen hn (a, σ)).stageEquiv A)
    (degreeOneUntwist_degreeOneEquiv A.val.val _).symm).trans
      ((quadraticTwistEquiv_symm_stage C S _ A _).trans
        ((congrArg (degreeOneUntwist A.val.val)
          (Cohomology.localQuadraticReconstruction_stage_generator
            Tdr C S hS hgen hn a σ A H)).trans
            ((map_smul (degreeOneUntwist A.val.val) (a : k) _).trans
              (congrArg ((a : k) • ·) (degreeOneUntwist_degreeOneEquiv A.val.val _)))))

/-- The same primal unit scales all ordinary H¹ classes of the one common target. -/
theorem quadraticReconstruction_target (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticReconstruction C S hS hgen hn (a, σ)).targetEquiv x = (a : k) • x := by
  obtain ⟨x, rfl⟩ := (degreeOneUntwist (twoPunctureArrangement k)).surjective x
  exact (quadraticTwistEquiv_symm_target C S _ x).trans
    ((congrArg (degreeOneUntwist (twoPunctureArrangement k))
      (Cohomology.localQuadraticReconstruction_target Tdr C S hS hgen hn a σ x)).trans
        (map_smul (degreeOneUntwist (twoPunctureArrangement k)) (a : k) x))

-- The proof traverses the nested actual-diagram and full OS quotient comparisons.
set_option maxRecDepth 2000 in
/-- On each whole stage degree, the primal scalar is its degree power and the field part
is the coefficient-linear transport of the actual full OS quotient. -/
theorem gradedReconstruction_stage_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (q : ℕ) (x : OSAlgebra k A.val.val) (hx : x ∈ OSAlgebra.degree k A.val.val q) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val x) =
      (a : k)^q • Geometric.DeRham.affineEquiv A.val.val
        (galoisOSAlgebraEquiv k A.val σ x) :=
  (gradedTwistEquiv_symm_stage C S _ A ((Tdr).diagonalEquiv A.val.val x)).trans
    ((congrArg (diagonalUntwist ((Daff).complement A.val.val))
      (Cohomology.localGradedReconstruction_stage_degree Tdr C S hS hgen hn a σ A q x hx)).trans
        (map_smul (diagonalUntwist ((Daff).complement A.val.val)) ((a : k)^q) _))

-- The common target has the same nested comparison types as the stage formula.
set_option maxRecDepth 2000 in
/-- The same primal unit scales a whole common-target degree by its degree power. -/
theorem gradedReconstruction_target_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedReconstruction C S hS hgen hn (a, σ)).targetEquiv (x : HdR _) =
      (a : k)^q • (x : HdR _) := by
  have hx : (x : HdR (Cohomology.schemeMarkingTarget Daff)) ∈
      (Cohomology.diagonalDegree Tdr (Cohomology.schemeMarkingTarget Daff) q).map
        (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)).toLinearMap :=
    (diagonalUntwist_degree (Cohomology.schemeMarkingTarget Daff) q).symm ▸ x.property
  obtain ⟨y, hy, he⟩ := hx
  rw [← he]
  exact (gradedTwistEquiv_symm_target C S _ y).trans
    ((congrArg (diagonalUntwist (Cohomology.schemeMarkingTarget Daff))
      (Cohomology.localGradedReconstruction_target_degree Tdr C S hS hgen hn a σ q ⟨y, hy⟩)).trans
        (map_smul (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)) ((a : k)^q) y))

/-- The actual ordinary logarithmic generator formula for the full graded action. -/
theorem gradedReconstruction_stage_generator (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.affineEquiv A.val.val (OSAlgebra.generator k A.val.val H)) =
      (a : k) • Geometric.DeRham.affineEquiv A.val.val
        (OSAlgebra.generator k A.val.val (galoisLabelEquiv A.val σ H)) := by
  rw [gradedReconstruction_stage_degree C S hS hgen hn a σ A 1 _
    (OSAlgebra.generator_mem_degree k A.val.val H), pow_one,
    galoisOSAlgebraEquiv_generator]

/-- **The actual dlog action.** Any equations of `H` and `σH` give this same formula.
The coefficient is unchanged by `σ`: this is a `k`-linear classified action.
Blueprint: E03 (`cor:e03`). -/
theorem gradedReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val)
    {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) := by
  rw [← Geometric.DeRham.affineEquiv_generator_of_isEquation H hf,
    gradedReconstruction_stage_generator C S hS hgen hn a σ A H,
    Geometric.DeRham.affineEquiv_generator_of_isEquation _ hf']

/-- The quadratic action has the same actual dlog formula, with its source explicitly
regarded as an ordinary degree-one class. -/
theorem quadraticReconstruction_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (H : A.val.val) {f f' : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H) (hf' : IsEquation f' (galoisLabelEquiv A.val σ H)) :
    ((quadraticReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      ⟨OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :
          HdR ((Daff).complement A.val.val)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f'
          (hf'.covers (galoisLabelEquiv A.val σ H).property)) := by
  have hs : degreeOneEquiv A.val.val (Finsupp.single H 1) =
      ⟨OrlikSolomon.DeRham.dlogClass k
        (Geometric.complementUnit A.val.val f (hf.covers H.property)),
        OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :=
    Subtype.ext (degreeOneEquiv_single_of_isEquation A.val.val H hf)
  rw [← hs, quadraticReconstruction_stage_generator C S hS hgen hn a σ A H,
    Submodule.coe_smul, degreeOneEquiv_single_of_isEquation A.val.val _ hf']

/-- The canonical transformed equation is one permissible equation in the dlog formula.
No `k`-scheme map induced by the semilinear field action is asserted. -/
theorem gradedReconstruction_dlog_fieldAffineForm (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val f (hf.covers H.property))) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A.val.val).obj)
        (Geometric.complementUnit A.val.val (fieldAffineForm σ.toRingEquiv f)
          (((galoisLabelEquiv_val A.val σ H).symm ▸
            (isEquation_fieldAffineForm σ.toRingEquiv hf)).covers
              (galoisLabelEquiv A.val σ H).property)) :=
  gradedReconstruction_dlog C S hS hgen hn a σ A H hf
    ((galoisLabelEquiv_val A.val σ H).symm ▸ isEquation_fieldAffineForm σ.toRingEquiv hf)

/-- Every ordinary H¹ marking square uses the same target scalar, on every target vector. -/
theorem quadraticReconstruction_marking (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val)
    (x : degreeOne (twoPunctureArrangement k)) :
    (quadraticReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (componentPull (w.schemeMap Daff hw) 1 x) =
      componentPull (w.schemeMap Daff hw) 1 ((a : k) • x) := by
  have h := DFunLike.congr_fun
    ((quadraticReconstruction C S hS hgen hn (a, σ)).marking_naturality A w hw) x
  exact h.trans (congrArg (componentPull (w.schemeMap Daff hw) 1)
    (quadraticReconstruction_target C S hS hgen hn a σ x))

/-- On every ordinary degree of the common target, actual marking pullback intertwines
the classified action with the same degree-power scalar. -/
theorem gradedReconstruction_marking_degree (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) (q : ℕ)
    (x : HdRdegree (Cohomology.schemeMarkingTarget Daff) q) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) x) =
      Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw) ((a : k)^q • (x : HdR _)) := by
  have h := DFunLike.congr_fun
    ((gradedReconstruction C S hS hgen hn (a, σ)).marking_naturality A w hw) (x : HdR _)
  exact h.trans (congrArg (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw))
    (gradedReconstruction_target_degree C S hS hgen hn a σ q x))

/-- The full classified action fixes scalar coefficients. It is `k`-linear, even when
the field-automorphism parameter acts nontrivially on `k`. -/
theorem gradedReconstruction_smul (a : kˣ) (σ : k ≃ₐ[k₀] k) (A : C.Stage)
    (c : k) (x : HdR ((Daff).complement A.val.val)) :
    (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A (c • x) =
      c • (gradedReconstruction C S hS hgen hn (a, σ)).stageEquiv A x :=
  map_smul _ c x

/-- The one common-target action also fixes scalar coefficients. -/
theorem gradedReconstruction_target_smul (a : kˣ) (σ : k ≃ₐ[k₀] k)
    (c : k) (x : HdR (Cohomology.schemeMarkingTarget Daff)) :
    (gradedReconstruction C S hS hgen hn (a, σ)).targetEquiv (c • x) =
      c • (gradedReconstruction C S hS hgen hn (a, σ)).targetEquiv x :=
  map_smul _ c x

/-- Each of the two ordered actual target dlogs is individually scaled by the same unit. -/
theorem gradedReconstruction_target_dlog (a : kˣ) (σ : k ≃ₐ[k₀] k) (i : Fin 2) :
    (gradedReconstruction C S hS hgen hn (a, σ)).targetEquiv
      (OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i)) =
      (a : k) • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff i) := by
  simpa only [pow_one] using gradedReconstruction_target_degree C S hS hgen hn a σ 1
    ⟨_, OrlikSolomon.DeRham.dlogClass_mem_degree _⟩

/-- Unconditional ordinary H¹ reconstruction on the canonical full stable family.
Algebraicity is used only to construct that family. Blueprint: E03 (`cor:e03`). -/
def fullQuadraticReconstruction [Algebra.IsAlgebraic k₀ k] (S : Set k₀)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (kˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut (fullCofinalSystem k₀ k n) S :=
  quadraticReconstruction (fullCofinalSystem k₀ k n) S hS hgen hn

/-- Unconditional ordinary graded reconstruction on the canonical full stable family.
The algebraic-closure setting specializes this algebraic-family result.
Blueprint: E03 (`cor:e03`). -/
def fullGradedReconstruction [Algebra.IsAlgebraic k₀ k] (S : Set k₀)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (kˣ × (k ≃ₐ[k₀] k)) ≃* GradedDiagramAut (fullCofinalSystem k₀ k n) S :=
  gradedReconstruction (fullCofinalSystem k₀ k n) S hS hgen hn

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
