/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Untwist
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Automorphisms of the actual ordinary de Rham diagram

The quadratic group acts on actual ordinary H¹, preserves its entire exterior cup kernel,
and commutes with actual inclusion and tagged marking pullbacks. The graded group acts on
actual ordinary total de Rham cohomology, preserves every ordinary degree, and commutes
with the same scheme maps. Both retain one actual two-puncture target.

The groups are comaps of A04's actual subgroups under natural diagonal untwisting. The
membership theorems identify them with precisely the ordinary predicates. No new theory
or generic diagram structure is introduced. The four named product/subgroup type synonyms
are `@[reducible] def`s under the approved A03/A04 exception: inherited product and subgroup
instances require their literal type heads. They add no data or transported instances.

Blueprint: the actual ordinary marked diagram in E03 (`cor:e03`).
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

/-- The actual ordinary H¹ stage and common-target equivalences. Transparency inherits
the existing product instances, as in A03/A04, without transported instances. -/
@[reducible]
def QuadraticAutFamily :=
  (∀ A : C.Stage, degreeOne A.val.val ≃ₗ[k] degreeOne A.val.val) ×
    (degreeOne (twoPunctureArrangement k) ≃ₗ[k] degreeOne (twoPunctureArrangement k))

/-- Conjugation from actual ordinary H¹ families to A04's actual weighted H¹ families. -/
def quadraticFamilyEquiv : QuadraticAutFamily C ≃* Cohomology.QuadraticAutFamily Tdr C :=
  MulEquiv.prodCongr
    (MulEquiv.piCongrRight fun A ↦
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k _).symm.trans
        (LinearMap.GeneralLinearGroup.congrLinearEquiv (degreeOneUntwist A.val.val).symm)).trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv k _))
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv k _).symm.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv
        (degreeOneUntwist (twoPunctureArrangement k)).symm)).trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv k _))

/-- The actual ordinary cup-kernel and marked-arrow subgroup, obtained by natural
conjugation from A04. Its exact ordinary predicate is `quadraticFamilyEquiv_mem_iff`. -/
def quadraticDiagramAutSubgroup : Subgroup (QuadraticAutFamily C) :=
  (Cohomology.quadraticDiagramAutSubgroup Tdr C S).comap
    (quadraticFamilyEquiv C).toMonoidHom

/-- Membership means whole ordinary cup-kernel image equality and actual inclusion and
marking squares, with no reconstruction conclusion stored in the data. -/
theorem quadraticFamilyEquiv_mem_iff (g : QuadraticAutFamily C) :
    g ∈ quadraticDiagramAutSubgroup C S ↔
      (∀ A : C.Stage, (LinearMap.ker (cupMap A.val.val)).map
        (exteriorPower.map 2 (g.1 A).toLinearMap) = LinearMap.ker (cupMap A.val.val)) ∧
      (∀ (A B : C.Stage) (h : A ≤ B),
        (g.1 B).toLinearMap.comp (componentPull ((Daff).complementInclusion h) 1) =
          (componentPull ((Daff).complementInclusion h) 1).comp (g.1 A).toLinearMap) ∧
      ∀ (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val),
        (g.1 A).toLinearMap.comp (componentPull (w.schemeMap Daff hw) 1) =
          (componentPull (w.schemeMap Daff hw) 1).comp g.2.toLinearMap := by
  refine and_congr (forall_congr' fun A ↦ ?_)
    (and_congr (forall_congr' fun A ↦ forall_congr' fun B ↦ forall_congr' fun h ↦ ?_)
      (forall_congr' fun A ↦ forall_congr' fun w ↦ forall_congr' fun hw ↦ ?_))
  · exact (Cohomology.exterior_conjugate_iff (degreeOneUntwist A.val.val) _ _
      (map_cupKernel_untwist A.val.val) (g.1 A)).symm
  · exact (Cohomology.linear_conjugate_arrow_iff
      (degreeOneUntwist A.val.val) (degreeOneUntwist B.val.val)
      (Cohomology.componentPull Tdr ((Daff).complementInclusion h) 1)
      (componentPull ((Daff).complementInclusion h) 1)
      (degreeOneUntwist_naturality B.val.val A.val.val
        ((Daff).complementInclusion h)).symm (g.1 A) (g.1 B)).symm
  · exact (Cohomology.linear_conjugate_arrow_iff
      (degreeOneUntwist (twoPunctureArrangement k)) (degreeOneUntwist A.val.val)
      (Cohomology.componentPull Tdr (w.schemeMap Daff hw) 1)
      (componentPull (w.schemeMap Daff hw) 1)
      (degreeOneUntwist_naturality A.val.val (twoPunctureArrangement k)
        (w.schemeMap Daff hw)).symm g.2 (g.1 A)).symm

/-- Automorphisms of actual ordinary H¹ and cup kernels with one actual common target.
This transparent subgroup synonym inherits existing instances; it adds no data or instances.
Blueprint: E03 (`cor:e03`). -/
@[reducible]
def DiagramAut := ↥(quadraticDiagramAutSubgroup C S)

namespace DiagramAut

variable {C S}

/-- The actual ordinary H¹ equivalence at a stage. -/
def stageEquiv (g : DiagramAut C S) (A : C.Stage) :
    degreeOne A.val.val ≃ₗ[k] degreeOne A.val.val := g.val.1 A

/-- The actual ordinary H¹ equivalence at the single common target. -/
def targetEquiv (g : DiagramAut C S) :
    degreeOne (twoPunctureArrangement k) ≃ₗ[k] degreeOne (twoPunctureArrangement k) := g.val.2

/-- Every stage preserves the complete actual ordinary cup kernel. -/
theorem map_cupKernel (g : DiagramAut C S) (A : C.Stage) :
    (LinearMap.ker (cupMap A.val.val)).map (exteriorPower.map 2 (g.stageEquiv A).toLinearMap) =
      LinearMap.ker (cupMap A.val.val) :=
  ((quadraticFamilyEquiv_mem_iff C S g.val).mp g.property).1 A

/-- Actual ordinary H¹ inclusion pullback commutes with the stage maps. -/
theorem inclusion_naturality (g : DiagramAut C S) {A B : C.Stage} (h : A ≤ B) :
    (g.stageEquiv B).toLinearMap.comp (componentPull ((Daff).complementInclusion h) 1) =
      (componentPull ((Daff).complementInclusion h) 1).comp (g.stageEquiv A).toLinearMap :=
  ((quadraticFamilyEquiv_mem_iff C S g.val).mp g.property).2.1 A B h

/-- All actual ordinary marking squares retain the same target equivalence. -/
theorem marking_naturality (g : DiagramAut C S) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) :
    (g.stageEquiv A).toLinearMap.comp (componentPull (w.schemeMap Daff hw) 1) =
      (componentPull (w.schemeMap Daff hw) 1).comp g.targetEquiv.toLinearMap :=
  ((quadraticFamilyEquiv_mem_iff C S g.val).mp g.property).2.2 A w hw

/-- Construct an ordinary quadratic diagram action from exactly the ordinary cup-kernel
and actual arrow conditions. -/
def ofEquivs (g : ∀ A : C.Stage, degreeOne A.val.val ≃ₗ[k] degreeOne A.val.val)
    (gT : degreeOne (twoPunctureArrangement k) ≃ₗ[k] degreeOne (twoPunctureArrangement k))
    (hQ : ∀ A : C.Stage, (LinearMap.ker (cupMap A.val.val)).map
      (exteriorPower.map 2 (g A).toLinearMap) = LinearMap.ker (cupMap A.val.val))
    (hi : ∀ (A B : C.Stage) (h : A ≤ B),
      (g B).toLinearMap.comp (componentPull ((Daff).complementInclusion h) 1) =
        (componentPull ((Daff).complementInclusion h) 1).comp (g A).toLinearMap)
    (hm : ∀ (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val),
      (g A).toLinearMap.comp (componentPull (w.schemeMap Daff hw) 1) =
        (componentPull (w.schemeMap Daff hw) 1).comp gT.toLinearMap) : DiagramAut C S :=
  ⟨(g, gT), (quadraticFamilyEquiv_mem_iff C S _).mpr ⟨hQ, hi, hm⟩⟩

@[simp]
theorem stageEquiv_ofEquivs (g gT hQ hi hm) (A : C.Stage) :
    (ofEquivs (C := C) (S := S) g gT hQ hi hm).stageEquiv A = g A := rfl

@[simp]
theorem targetEquiv_ofEquivs (g gT hQ hi hm) :
    (ofEquivs (C := C) (S := S) g gT hQ hi hm).targetEquiv = gT := rfl

/-- Stages and the retained common target determine an ordinary quadratic automorphism. -/
@[ext]
theorem ext {g h : DiagramAut C S} (hs : ∀ A, g.stageEquiv A = h.stageEquiv A)
    (ht : g.targetEquiv = h.targetEquiv) : g = h :=
  Subtype.ext (Prod.ext (funext hs) ht)

@[simp] theorem stageEquiv_one (A : C.Stage) :
    (1 : DiagramAut C S).stageEquiv A = LinearEquiv.refl k _ := rfl
@[simp] theorem targetEquiv_one :
    (1 : DiagramAut C S).targetEquiv = LinearEquiv.refl k _ := rfl
@[simp] theorem stageEquiv_mul (g h : DiagramAut C S) (A : C.Stage) :
    (g * h).stageEquiv A = g.stageEquiv A * h.stageEquiv A := rfl
@[simp] theorem targetEquiv_mul (g h : DiagramAut C S) :
    (g * h).targetEquiv = g.targetEquiv * h.targetEquiv := rfl
@[simp] theorem stageEquiv_inv (g : DiagramAut C S) (A : C.Stage) :
    g⁻¹.stageEquiv A = (g.stageEquiv A).symm := rfl
@[simp] theorem targetEquiv_inv (g : DiagramAut C S) :
    g⁻¹.targetEquiv = g.targetEquiv.symm := rfl

end DiagramAut

/-- The ordinary and weighted actual quadratic diagrams are canonically equivalent in
both directions. Blueprint: E03 (`cor:e03`). -/
def quadraticTwistEquiv : DiagramAut C S ≃* Cohomology.DiagramAut Tdr C S where
  __ := (quadraticFamilyEquiv C).toEquiv.subtypeEquiv
    (p := fun g ↦ g ∈ quadraticDiagramAutSubgroup C S)
    (q := fun g ↦ g ∈ Cohomology.quadraticDiagramAutSubgroup Tdr C S)
    (fun _ ↦ Iff.rfl)
  map_mul' g h := Subtype.ext ((quadraticFamilyEquiv C).map_mul g.val h.val)

/-- The quadratic comparison intertwines actual stage actions with ordinary untwisting. -/
theorem quadraticTwistEquiv_stage (g : DiagramAut C S) (A : C.Stage)
    (x : Cohomology.degreeOne Tdr A.val.val) :
    degreeOneUntwist A.val.val ((quadraticTwistEquiv C S g).stageEquiv A x) =
      g.stageEquiv A (degreeOneUntwist A.val.val x) := by
  change degreeOneUntwist A.val.val ((degreeOneUntwist A.val.val).symm _) = _
  exact (degreeOneUntwist A.val.val).apply_symm_apply _

/-- The quadratic comparison intertwines the one actual target action. -/
theorem quadraticTwistEquiv_target (g : DiagramAut C S)
    (x : Cohomology.degreeOne Tdr (twoPunctureArrangement k)) :
    degreeOneUntwist (twoPunctureArrangement k) ((quadraticTwistEquiv C S g).targetEquiv x) =
      g.targetEquiv (degreeOneUntwist (twoPunctureArrangement k) x) := by
  change degreeOneUntwist (twoPunctureArrangement k)
    ((degreeOneUntwist (twoPunctureArrangement k)).symm _) = _
  exact (degreeOneUntwist (twoPunctureArrangement k)).apply_symm_apply _

/-- The inverse quadratic comparison recovers each ordinary stage action. -/
theorem quadraticTwistEquiv_symm_stage (g : Cohomology.DiagramAut Tdr C S) (A : C.Stage)
    (x : Cohomology.degreeOne Tdr A.val.val) :
    ((quadraticTwistEquiv C S).symm g).stageEquiv A (degreeOneUntwist A.val.val x) =
      degreeOneUntwist A.val.val (g.stageEquiv A x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (quadraticTwistEquiv_stage C S ((quadraticTwistEquiv C S).symm g) A x).symm

/-- The inverse quadratic comparison recovers the ordinary common-target action. -/
theorem quadraticTwistEquiv_symm_target (g : Cohomology.DiagramAut Tdr C S)
    (x : Cohomology.degreeOne Tdr (twoPunctureArrangement k)) :
    ((quadraticTwistEquiv C S).symm g).targetEquiv
        (degreeOneUntwist (twoPunctureArrangement k) x) =
      degreeOneUntwist (twoPunctureArrangement k) (g.targetEquiv x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (quadraticTwistEquiv_target C S ((quadraticTwistEquiv C S).symm g) x).symm

/-- The actual ordinary total-cohomology stage and target algebra equivalences.
Transparency inherits the existing product instances, with no transported instances. -/
@[reducible]
def GradedAutFamily :=
  (∀ A : C.Stage, HdR ((Daff).complement A.val.val) ≃ₐ[k]
    HdR ((Daff).complement A.val.val)) ×
  (HdR (Cohomology.schemeMarkingTarget Daff) ≃ₐ[k]
    HdR (Cohomology.schemeMarkingTarget Daff))

/-- Conjugation from actual ordinary total families to the actual diagonal families. -/
def gradedFamilyEquiv : GradedAutFamily C ≃* Cohomology.GradedAutFamily Tdr C :=
  MulEquiv.prodCongr
    (MulEquiv.piCongrRight fun A ↦ AlgEquiv.autCongr
      (diagonalUntwist ((Daff).complement A.val.val)).symm)
    (AlgEquiv.autCongr (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)).symm)

/-- The actual ordinary full graded subgroup, obtained by the natural diagonal comparison.
Its exact ordinary degrees and actual arrow predicate is `gradedFamilyEquiv_mem_iff`. -/
def gradedDiagramAutSubgroup : Subgroup (GradedAutFamily C) :=
  (Cohomology.gradedDiagramAutSubgroup Tdr C S).comap (gradedFamilyEquiv C).toMonoidHom

/-- Membership means preservation of every actual ordinary degree at stages and target,
and naturality with actual inclusion and tagged marking pullbacks. -/
theorem gradedFamilyEquiv_mem_iff (g : GradedAutFamily C) :
    g ∈ gradedDiagramAutSubgroup C S ↔
      (∀ (A : C.Stage) (q : ℕ),
        (HdRdegree ((Daff).complement A.val.val) q).map (g.1 A).toLinearMap =
          HdRdegree ((Daff).complement A.val.val) q) ∧
      (∀ q : ℕ, (HdRdegree (Cohomology.schemeMarkingTarget Daff) q).map g.2.toLinearMap =
        HdRdegree (Cohomology.schemeMarkingTarget Daff) q) ∧
      (∀ (A B : C.Stage) (h : A ≤ B),
        (g.1 B).toAlgHom.comp (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)) =
          (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)).comp
            (g.1 A).toAlgHom) ∧
      ∀ (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val),
        (g.1 A).toAlgHom.comp (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)) =
          (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)).comp g.2.toAlgHom := by
  refine and_congr (forall_congr' fun A ↦ forall_congr' fun q ↦ ?_)
    (and_congr (forall_congr' fun q ↦ ?_)
      (and_congr
        (forall_congr' fun A ↦ forall_congr' fun B ↦ forall_congr' fun h ↦ ?_)
        (forall_congr' fun A ↦ forall_congr' fun w ↦ forall_congr' fun hw ↦ ?_)))
  · exact Cohomology.map_conjugate_eq_iff
      (diagonalUntwist ((Daff).complement A.val.val)).toLinearEquiv _ _
      (diagonalUntwist_degree _ q) (g.1 A).toLinearEquiv
  · exact Cohomology.map_conjugate_eq_iff
      (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)).toLinearEquiv _ _
      (diagonalUntwist_degree _ q) g.2.toLinearEquiv
  · exact (Cohomology.algebra_conjugate_arrow_iff
      (diagonalUntwist ((Daff).complement A.val.val))
      (diagonalUntwist ((Daff).complement B.val.val))
      (Cohomology.diagonalPull Tdr ((Daff).complementInclusion h))
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h))
      (diagonalUntwist_naturality _).symm (g.1 A) (g.1 B)).symm
  · exact (Cohomology.algebra_conjugate_arrow_iff
      (diagonalUntwist (Cohomology.schemeMarkingTarget Daff))
      (diagonalUntwist ((Daff).complement A.val.val))
      (Cohomology.diagonalPull Tdr (w.schemeMap Daff hw))
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw))
      (diagonalUntwist_naturality _).symm g.2 (g.1 A)).symm

/-- Automorphisms of the actual ordinary graded marked de Rham diagram. Transparency
inherits the existing subgroup instances, with no new data or transported instances.
Blueprint: E03 (`cor:e03`). -/
@[reducible]
def GradedDiagramAut := ↥(gradedDiagramAutSubgroup C S)

namespace GradedDiagramAut

variable {C S}

/-- The actual ordinary total algebra equivalence at a stage. -/
def stageEquiv (g : GradedDiagramAut C S) (A : C.Stage) :
    HdR ((Daff).complement A.val.val) ≃ₐ[k] HdR ((Daff).complement A.val.val) := g.val.1 A

/-- The actual ordinary total algebra equivalence at the one common target. -/
def targetEquiv (g : GradedDiagramAut C S) :
    HdR (Cohomology.schemeMarkingTarget Daff) ≃ₐ[k]
      HdR (Cohomology.schemeMarkingTarget Daff) := g.val.2

/-- Every whole ordinary homogeneous degree is preserved at every stage. -/
theorem map_degree (g : GradedDiagramAut C S) (A : C.Stage) (q : ℕ) :
    (HdRdegree ((Daff).complement A.val.val) q).map (g.stageEquiv A).toLinearMap =
      HdRdegree ((Daff).complement A.val.val) q :=
  ((gradedFamilyEquiv_mem_iff C S g.val).mp g.property).1 A q

/-- Every whole ordinary homogeneous degree is preserved at the one target. -/
theorem map_target_degree (g : GradedDiagramAut C S) (q : ℕ) :
    (HdRdegree (Cohomology.schemeMarkingTarget Daff) q).map g.targetEquiv.toLinearMap =
      HdRdegree (Cohomology.schemeMarkingTarget Daff) q :=
  ((gradedFamilyEquiv_mem_iff C S g.val).mp g.property).2.1 q

/-- Ordinary total stage actions commute with actual inclusion pullback. -/
theorem inclusion_naturality (g : GradedDiagramAut C S) {A B : C.Stage} (h : A ≤ B) :
    (g.stageEquiv B).toAlgHom.comp
        (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)) =
      (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)).comp
        (g.stageEquiv A).toAlgHom :=
  ((gradedFamilyEquiv_mem_iff C S g.val).mp g.property).2.2.1 A B h

/-- Every whole ordinary marking algebra square uses the same target action. -/
theorem marking_naturality (g : GradedDiagramAut C S) (A : C.Stage)
    (w : Marking S n) (hw : w.Available A.val.val) :
    (g.stageEquiv A).toAlgHom.comp (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)) =
      (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)).comp g.targetEquiv.toAlgHom :=
  ((gradedFamilyEquiv_mem_iff C S g.val).mp g.property).2.2.2 A w hw

/-- Construct a full ordinary diagram action from precisely ordinary degree preservation
and the actual inclusion/marking equations. -/
def ofEquivs (g : ∀ A : C.Stage, HdR ((Daff).complement A.val.val) ≃ₐ[k]
      HdR ((Daff).complement A.val.val))
    (gT : HdR (Cohomology.schemeMarkingTarget Daff) ≃ₐ[k]
      HdR (Cohomology.schemeMarkingTarget Daff))
    (hd : ∀ (A : C.Stage) (q : ℕ),
      (HdRdegree ((Daff).complement A.val.val) q).map (g A).toLinearMap =
        HdRdegree ((Daff).complement A.val.val) q)
    (ht : ∀ q : ℕ, (HdRdegree (Cohomology.schemeMarkingTarget Daff) q).map gT.toLinearMap =
      HdRdegree (Cohomology.schemeMarkingTarget Daff) q)
    (hi : ∀ (A B : C.Stage) (h : A ≤ B),
      (g B).toAlgHom.comp (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)) =
        (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion h)).comp (g A).toAlgHom)
    (hm : ∀ (A : C.Stage) (w : Marking S n) (hw : w.Available A.val.val),
      (g A).toAlgHom.comp (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)) =
        (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)).comp gT.toAlgHom) :
    GradedDiagramAut C S :=
  ⟨(g, gT), (gradedFamilyEquiv_mem_iff C S _).mpr ⟨hd, ht, hi, hm⟩⟩

@[simp] theorem stageEquiv_ofEquivs (g gT hd ht hi hm) (A : C.Stage) :
    (ofEquivs (C := C) (S := S) g gT hd ht hi hm).stageEquiv A = g A := rfl
@[simp] theorem targetEquiv_ofEquivs (g gT hd ht hi hm) :
    (ofEquivs (C := C) (S := S) g gT hd ht hi hm).targetEquiv = gT := rfl

/-- Stage and retained common-target algebra actions determine an ordinary graded action. -/
@[ext]
theorem ext {g h : GradedDiagramAut C S} (hs : ∀ A, g.stageEquiv A = h.stageEquiv A)
    (ht : g.targetEquiv = h.targetEquiv) : g = h :=
  Subtype.ext (Prod.ext (funext hs) ht)

@[simp] theorem stageEquiv_one (A : C.Stage) :
    (1 : GradedDiagramAut C S).stageEquiv A = AlgEquiv.refl := rfl
@[simp] theorem targetEquiv_one :
    (1 : GradedDiagramAut C S).targetEquiv = AlgEquiv.refl := rfl
@[simp] theorem stageEquiv_mul (g h : GradedDiagramAut C S) (A : C.Stage) :
    (g * h).stageEquiv A = g.stageEquiv A * h.stageEquiv A := rfl
@[simp] theorem targetEquiv_mul (g h : GradedDiagramAut C S) :
    (g * h).targetEquiv = g.targetEquiv * h.targetEquiv := rfl
@[simp] theorem stageEquiv_inv (g : GradedDiagramAut C S) (A : C.Stage) :
    g⁻¹.stageEquiv A = (g.stageEquiv A).symm := rfl
@[simp] theorem targetEquiv_inv (g : GradedDiagramAut C S) :
    g⁻¹.targetEquiv = g.targetEquiv.symm := rfl

end GradedDiagramAut

/-- The actual ordinary and weighted full graded diagrams are canonically equivalent in
both directions. Blueprint: E03 (`cor:e03`). -/
def gradedTwistEquiv : GradedDiagramAut C S ≃* Cohomology.GradedDiagramAut Tdr C S where
  __ := (gradedFamilyEquiv C).toEquiv.subtypeEquiv
    (p := fun g ↦ g ∈ gradedDiagramAutSubgroup C S)
    (q := fun g ↦ g ∈ Cohomology.gradedDiagramAutSubgroup Tdr C S)
    (fun _ ↦ Iff.rfl)
  map_mul' g h := Subtype.ext ((gradedFamilyEquiv C).map_mul g.val h.val)

/-- The full comparison intertwines actual stage actions with diagonal untwisting. -/
theorem gradedTwistEquiv_stage (g : GradedDiagramAut C S) (A : C.Stage)
    (x : Cohomology.diagonal Tdr ((Daff).complement A.val.val)) :
    diagonalUntwist ((Daff).complement A.val.val) ((gradedTwistEquiv C S g).stageEquiv A x) =
      g.stageEquiv A (diagonalUntwist ((Daff).complement A.val.val) x) := by
  change diagonalUntwist _ ((diagonalUntwist _).symm _) = _
  exact (diagonalUntwist _).apply_symm_apply _

/-- The full comparison intertwines the one actual target action. -/
theorem gradedTwistEquiv_target (g : GradedDiagramAut C S)
    (x : Cohomology.diagonal Tdr (Cohomology.schemeMarkingTarget Daff)) :
    diagonalUntwist (Cohomology.schemeMarkingTarget Daff)
        ((gradedTwistEquiv C S g).targetEquiv x) =
      g.targetEquiv (diagonalUntwist (Cohomology.schemeMarkingTarget Daff) x) := by
  change diagonalUntwist _ ((diagonalUntwist _).symm _) = _
  exact (diagonalUntwist _).apply_symm_apply _

/-- The inverse full comparison recovers each actual ordinary stage action. -/
theorem gradedTwistEquiv_symm_stage (g : Cohomology.GradedDiagramAut Tdr C S) (A : C.Stage)
    (x : Cohomology.diagonal Tdr ((Daff).complement A.val.val)) :
    ((gradedTwistEquiv C S).symm g).stageEquiv A
        (diagonalUntwist ((Daff).complement A.val.val) x) =
      diagonalUntwist ((Daff).complement A.val.val) (g.stageEquiv A x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (gradedTwistEquiv_stage C S ((gradedTwistEquiv C S).symm g) A x).symm

/-- The inverse full comparison recovers the one actual ordinary target action. -/
theorem gradedTwistEquiv_symm_target (g : Cohomology.GradedDiagramAut Tdr C S)
    (x : Cohomology.diagonal Tdr (Cohomology.schemeMarkingTarget Daff)) :
    ((gradedTwistEquiv C S).symm g).targetEquiv
        (diagonalUntwist (Cohomology.schemeMarkingTarget Daff) x) =
      diagonalUntwist (Cohomology.schemeMarkingTarget Daff) (g.targetEquiv x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (gradedTwistEquiv_target C S ((gradedTwistEquiv C S).symm g) x).symm

namespace GradedDiagramAut

/-- Restriction to the actual ordinary H¹ diagram. The stage and target equations below
identify this map with literal restriction of the ordinary total algebra actions. -/
def toQuadratic : GradedDiagramAut C S →* DiagramAut C S :=
  (quadraticTwistEquiv C S).symm.toMonoidHom.comp
    ((Cohomology.GradedDiagramAut.toQuadratic Tdr C S).comp
      (gradedTwistEquiv C S).toMonoidHom)

/-- Ordinary restriction commutes exactly with both weighted diagram comparisons. -/
theorem toQuadratic_comparison (g : GradedDiagramAut C S) :
    quadraticTwistEquiv C S (toQuadratic C S g) =
      Cohomology.GradedDiagramAut.toQuadratic Tdr C S (gradedTwistEquiv C S g) :=
  (quadraticTwistEquiv C S).apply_symm_apply _

-- These terms traverse both nested subgroup comparisons and the actual scheme grading.
set_option maxRecDepth 2000 in
/-- Ordinary restriction is literal action on every actual stage H¹ class. -/
theorem toQuadratic_stage (g : GradedDiagramAut C S) (A : C.Stage)
    (x : degreeOne A.val.val) :
    g.stageEquiv A (x : HdR ((Daff).complement A.val.val)) =
      ((toQuadratic C S g).stageEquiv A x : HdR ((Daff).complement A.val.val)) := by
  obtain ⟨x, rfl⟩ := (degreeOneUntwist A.val.val).surjective x
  calc
    _ = g.stageEquiv A (diagonalUntwist ((Daff).complement A.val.val)
        (Cohomology.degreeOneι Tdr A.val.val x)) :=
      congrArg (g.stageEquiv A) (diagonalUntwist_degreeOneι A.val.val x).symm
    _ = diagonalUntwist ((Daff).complement A.val.val)
        ((gradedTwistEquiv C S g).stageEquiv A (Cohomology.degreeOneι Tdr A.val.val x)) :=
      (gradedTwistEquiv_stage C S g A _).symm
    _ = diagonalUntwist ((Daff).complement A.val.val)
        (Cohomology.degreeOneι Tdr A.val.val
          ((Cohomology.GradedDiagramAut.toQuadratic Tdr C S
            (gradedTwistEquiv C S g)).stageEquiv A x)) :=
      congrArg (diagonalUntwist ((Daff).complement A.val.val))
        (DFunLike.congr_fun (Cohomology.GradedDiagramAut.toQuadratic_stage Tdr C S
          (gradedTwistEquiv C S g) A) x)
    _ = _ := (diagonalUntwist_degreeOneι A.val.val _).trans
      (congrArg Subtype.val (quadraticTwistEquiv_symm_stage C S _ A x)).symm

-- The actual target uses the same nested comparisons as the stage restriction.
set_option maxRecDepth 2000 in
/-- Ordinary restriction is literal action on H¹ of the one retained target. -/
theorem toQuadratic_target (g : GradedDiagramAut C S)
    (x : degreeOne (twoPunctureArrangement k)) :
    g.targetEquiv (x : HdR (Cohomology.schemeMarkingTarget Daff)) =
      ((toQuadratic C S g).targetEquiv x : HdR (Cohomology.schemeMarkingTarget Daff)) := by
  obtain ⟨x, rfl⟩ := (degreeOneUntwist (twoPunctureArrangement k)).surjective x
  calc
    _ = g.targetEquiv (diagonalUntwist (Cohomology.schemeMarkingTarget Daff)
        (Cohomology.degreeOneι Tdr (twoPunctureArrangement k) x)) :=
      congrArg g.targetEquiv (diagonalUntwist_degreeOneι (twoPunctureArrangement k) x).symm
    _ = diagonalUntwist (Cohomology.schemeMarkingTarget Daff)
        ((gradedTwistEquiv C S g).targetEquiv
          (Cohomology.degreeOneι Tdr (twoPunctureArrangement k) x)) :=
      (gradedTwistEquiv_target C S g _).symm
    _ = diagonalUntwist (Cohomology.schemeMarkingTarget Daff)
        (Cohomology.degreeOneι Tdr (twoPunctureArrangement k)
          ((Cohomology.GradedDiagramAut.toQuadratic Tdr C S
            (gradedTwistEquiv C S g)).targetEquiv x)) :=
      congrArg (diagonalUntwist (Cohomology.schemeMarkingTarget Daff))
        (DFunLike.congr_fun (Cohomology.GradedDiagramAut.toQuadratic_target Tdr C S
          (gradedTwistEquiv C S g)) x)
    _ = _ := (diagonalUntwist_degreeOneι (twoPunctureArrangement k) _).trans
      (congrArg Subtype.val (quadraticTwistEquiv_symm_target C S _ x)).symm

/-- Literal degree-one restriction is faithful on the full ordinary marked diagram. -/
theorem toQuadratic_injective : Function.Injective (toQuadratic C S) :=
  (quadraticTwistEquiv C S).symm.injective.comp
    ((Cohomology.GradedDiagramAut.toQuadratic_injective Tdr C S).comp
      (gradedTwistEquiv C S).injective)

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
