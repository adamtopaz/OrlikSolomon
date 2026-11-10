/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import OrlikSolomon.HyperplaneGT.Cohomology.Topology.Adapter.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# The actual diagram adapters are topological group isomorphisms

The exact existing actual-to-presentation comparisons preserve each complete stage and
the single common target by conjugation. Their simultaneous identity kernels therefore
agree. The directly defined neighborhood bases make each old comparison inducing, and
its old inverse is continuous. No classification or field-extension hypothesis is used.

## Main results

* `degreeOneDiagramEquiv_preimage_stageKernel` and its graded counterpart identify
  actual stage-and-target kernels with the preimages of the presentation kernels.
* `degreeOneDiagramContinuousEquiv` and `gradedDiagramContinuousEquiv` adjoin continuity
  to the old comparisons, with exact underlying-map and forward/inverse component API.

Blueprint: the group comparison clauses of T14 (`thm:t14`).
-/

@[expose] public section

noncomputable section

universe u v r b h

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Filter Topology
open scoped FiniteStageTopology

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Canonical coordinates preserve equality of entire actual stage automorphisms. -/
theorem degreeOneDiagramEquiv_stage_eq_iff (g h : DiagramAut T C S) (A : C.Stage) :
    (degreeOneDiagramEquiv T C S g).stageEquiv A = (degreeOneDiagramEquiv T C S h).stageEquiv A ↔
      g.stageEquiv A = h.stageEquiv A := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (degreeOneEquiv T A.val.val).surjective x
    rw [← degreeOneDiagramEquiv_stage, ← degreeOneDiagramEquiv_stage, heq]
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (degreeOneEquiv T A.val.val).injective
    rw [degreeOneDiagramEquiv_stage, degreeOneDiagramEquiv_stage, heq]

/-- Canonical coordinates preserve equality of the one entire actual target automorphism. -/
theorem degreeOneDiagramEquiv_target_eq_iff (g h : DiagramAut T C S) :
    (degreeOneDiagramEquiv T C S g).targetEquiv = (degreeOneDiagramEquiv T C S h).targetEquiv ↔
      g.targetEquiv = h.targetEquiv := by
  constructor
  · intro heq
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (targetDegreeOneEquiv T).surjective x
    rw [← degreeOneDiagramEquiv_target, ← degreeOneDiagramEquiv_target, heq]
  · intro heq
    apply LinearEquiv.ext
    intro x
    apply (targetDegreeOneEquiv T).injective
    rw [degreeOneDiagramEquiv_target, degreeOneDiagramEquiv_target, heq]

/-- The old adapter pulls each presentation stage-and-target kernel back to the actual one.
Both complete components are retained, also in dimension zero and with zero coefficients. -/
theorem degreeOneDiagramEquiv_preimage_stageKernel (A : C.Stage) :
    (degreeOneDiagramEquiv T C S) ⁻¹'
        (HyperplaneGT.DiagramAut.stageKernel R C S A : Set _) =
      (DiagramAut.stageKernel T C S A : Set _) := by
  ext g
  change degreeOneDiagramEquiv T C S g ∈ HyperplaneGT.DiagramAut.stageKernel R C S A ↔
    g ∈ DiagramAut.stageKernel T C S A
  rw [HyperplaneGT.DiagramAut.mem_stageKernel, DiagramAut.mem_stageKernel]
  simpa only [map_one, DiagramAut.stageEquiv_one, DiagramAut.targetEquiv_one,
    HyperplaneGT.DiagramAut.stageEquiv_one, HyperplaneGT.DiagramAut.targetEquiv_one,
    LinearEquiv.one_eq_refl] using
    and_congr (degreeOneDiagramEquiv_stage_eq_iff T C S g 1 A)
      (degreeOneDiagramEquiv_target_eq_iff T C S g 1)

/-- The direct actual topology is induced by the old adapter as a consequence of the
complete-stage-and-target neighborhood bases, rather than by definition. -/
theorem isInducing_degreeOneDiagramEquiv : IsInducing (degreeOneDiagramEquiv T C S) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply (DiagramAut.nhds_one_stageBasis T C S).eq_of_same_basis
  simpa only [degreeOneDiagramEquiv_preimage_stageKernel] using
    (HyperplaneGT.DiagramAut.nhds_one_stageBasis R C S).comap (degreeOneDiagramEquiv T C S)

/-- Equality between the direct actual topology and the topology induced by the old adapter.
This theorem does not change the original product/subgroup definition. -/
theorem DiagramAut.stageTopology_eq_induced_degreeOneDiagramEquiv :
    DiagramAut.stageTopology T C S =
      TopologicalSpace.induced (degreeOneDiagramEquiv T C S)
        (HyperplaneGT.DiagramAut.stageTopology R C S) :=
  (isInducing_degreeOneDiagramEquiv T C S).eq_induced

/-- The exact old actual-to-presentation adapter, now a topological group isomorphism.
Blueprint: the group comparison clause of T14 (`thm:t14`). -/
def degreeOneDiagramContinuousEquiv : DiagramAut T C S ≃ₜ* HyperplaneGT.DiagramAut R C S where
  __ := degreeOneDiagramEquiv T C S
  continuous_toFun := (isInducing_degreeOneDiagramEquiv T C S).continuous
  continuous_invFun := ((degreeOneDiagramEquiv T C S).toEquiv.toHomeomorphOfIsInducing
    (isInducing_degreeOneDiagramEquiv T C S)).continuous_invFun

/-- The topological upgrade has exactly the old underlying multiplicative equivalence. -/
theorem degreeOneDiagramContinuousEquiv_toMulEquiv :
    (degreeOneDiagramContinuousEquiv T C S).toMulEquiv = degreeOneDiagramEquiv T C S := rfl

/-- The topological upgrade has exactly the old forward function. -/
theorem coe_degreeOneDiagramContinuousEquiv :
    ⇑(degreeOneDiagramContinuousEquiv T C S) = degreeOneDiagramEquiv T C S := rfl

/-- The upgrade evaluates by the old actual-to-presentation adapter. -/
theorem degreeOneDiagramContinuousEquiv_apply (g : DiagramAut T C S) :
    degreeOneDiagramContinuousEquiv T C S g = degreeOneDiagramEquiv T C S g := rfl

/-- The inverse upgrade evaluates by the old presentation-to-actual adapter. -/
theorem degreeOneDiagramContinuousEquiv_symm_apply (g : HyperplaneGT.DiagramAut R C S) :
    (degreeOneDiagramContinuousEquiv T C S).symm g = (degreeOneDiagramEquiv T C S).symm g := rfl

/-- Canonical coordinates preserve equality of entire actual stage automorphisms. -/
theorem gradedDiagramEquiv_stage_eq_iff (g h : GradedDiagramAut T C S) (A : C.Stage) :
    (gradedDiagramEquiv T C S g).stageEquiv A = (gradedDiagramEquiv T C S h).stageEquiv A ↔
      g.stageEquiv A = h.stageEquiv A := by
  constructor
  · intro heq
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (T.diagonalEquiv A.val.val).surjective x
    rw [← gradedDiagramEquiv_stage, ← gradedDiagramEquiv_stage, heq]
  · intro heq
    apply AlgEquiv.ext
    intro x
    apply (T.diagonalEquiv A.val.val).injective
    rw [gradedDiagramEquiv_stage, gradedDiagramEquiv_stage, heq]

/-- Canonical coordinates preserve equality of the one entire actual target automorphism. -/
theorem gradedDiagramEquiv_target_eq_iff (g h : GradedDiagramAut T C S) :
    (gradedDiagramEquiv T C S g).targetEquiv = (gradedDiagramEquiv T C S h).targetEquiv ↔
      g.targetEquiv = h.targetEquiv := by
  constructor
  · intro heq
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (T.diagonalEquiv (twoPunctureArrangement k)).surjective x
    rw [← gradedDiagramEquiv_target, ← gradedDiagramEquiv_target, heq]
  · intro heq
    apply AlgEquiv.ext
    intro x
    apply (T.diagonalEquiv (twoPunctureArrangement k)).injective
    rw [gradedDiagramEquiv_target, gradedDiagramEquiv_target, heq]

/-- The old adapter pulls each presentation stage-and-target kernel back to the actual one.
Both complete components are retained, also in dimension zero and with zero coefficients. -/
theorem gradedDiagramEquiv_preimage_stageKernel (A : C.Stage) :
    (gradedDiagramEquiv T C S) ⁻¹'
        (HyperplaneGT.GradedDiagramAut.stageKernel R C S A : Set _) =
      (GradedDiagramAut.stageKernel T C S A : Set _) := by
  ext g
  change gradedDiagramEquiv T C S g ∈ HyperplaneGT.GradedDiagramAut.stageKernel R C S A ↔
    g ∈ GradedDiagramAut.stageKernel T C S A
  rw [HyperplaneGT.GradedDiagramAut.mem_stageKernel, GradedDiagramAut.mem_stageKernel]
  simpa only [map_one, GradedDiagramAut.stageEquiv_one, GradedDiagramAut.targetEquiv_one,
    HyperplaneGT.GradedDiagramAut.stageEquiv_one,
    HyperplaneGT.GradedDiagramAut.targetEquiv_one, AlgEquiv.aut_one] using
    and_congr (gradedDiagramEquiv_stage_eq_iff T C S g 1 A)
      (gradedDiagramEquiv_target_eq_iff T C S g 1)

/-- The direct actual topology is induced by the old adapter as a consequence of the
complete-stage-and-target neighborhood bases, rather than by definition. -/
theorem isInducing_gradedDiagramEquiv : IsInducing (gradedDiagramEquiv T C S) := by
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  apply (GradedDiagramAut.nhds_one_stageBasis T C S).eq_of_same_basis
  simpa only [gradedDiagramEquiv_preimage_stageKernel] using
    (HyperplaneGT.GradedDiagramAut.nhds_one_stageBasis R C S).comap (gradedDiagramEquiv T C S)

/-- Equality between the direct actual topology and the topology induced by the old adapter.
This theorem does not change the original product/subgroup definition. -/
theorem GradedDiagramAut.stageTopology_eq_induced_gradedDiagramEquiv :
    GradedDiagramAut.stageTopology T C S =
      TopologicalSpace.induced (gradedDiagramEquiv T C S)
        (HyperplaneGT.GradedDiagramAut.stageTopology R C S) :=
  (isInducing_gradedDiagramEquiv T C S).eq_induced

/-- The exact old actual-to-presentation adapter, now a topological group isomorphism.
Blueprint: the group comparison clause of T14 (`thm:t14`). -/
def gradedDiagramContinuousEquiv :
    GradedDiagramAut T C S ≃ₜ* HyperplaneGT.GradedDiagramAut R C S where
  __ := gradedDiagramEquiv T C S
  continuous_toFun := (isInducing_gradedDiagramEquiv T C S).continuous
  continuous_invFun := ((gradedDiagramEquiv T C S).toEquiv.toHomeomorphOfIsInducing
    (isInducing_gradedDiagramEquiv T C S)).continuous_invFun

/-- The topological upgrade has exactly the old underlying multiplicative equivalence. -/
theorem gradedDiagramContinuousEquiv_toMulEquiv :
    (gradedDiagramContinuousEquiv T C S).toMulEquiv = gradedDiagramEquiv T C S := rfl

/-- The topological upgrade has exactly the old forward function. -/
theorem coe_gradedDiagramContinuousEquiv :
    ⇑(gradedDiagramContinuousEquiv T C S) = gradedDiagramEquiv T C S := rfl

/-- The upgrade evaluates by the old actual-to-presentation adapter. -/
theorem gradedDiagramContinuousEquiv_apply (g : GradedDiagramAut T C S) :
    gradedDiagramContinuousEquiv T C S g = gradedDiagramEquiv T C S g := rfl

/-- The inverse upgrade evaluates by the old presentation-to-actual adapter. -/
theorem gradedDiagramContinuousEquiv_symm_apply (g : HyperplaneGT.GradedDiagramAut R C S) :
    (gradedDiagramContinuousEquiv T C S).symm g = (gradedDiagramEquiv T C S).symm g := rfl

/-- The inverse topological adapter keeps the old inverse function. -/
theorem coe_degreeOneDiagramContinuousEquiv_symm :
    ⇑(degreeOneDiagramContinuousEquiv T C S).symm = (degreeOneDiagramEquiv T C S).symm := rfl

/-- The topological adapter intertwines the entire actual stage action with coordinates. -/
theorem degreeOneDiagramContinuousEquiv_stage (g : DiagramAut T C S) (A : C.Stage)
    (x : A.val.val →₀ R) :
    degreeOneEquiv T A.val.val ((degreeOneDiagramContinuousEquiv T C S g).stageEquiv A x) =
      g.stageEquiv A (degreeOneEquiv T A.val.val x) :=
  degreeOneDiagramEquiv_stage T C S g A x

/-- The topological adapter intertwines the one complete actual common target action. -/
theorem degreeOneDiagramContinuousEquiv_target (g : DiagramAut T C S) (x : Fin 2 →₀ R) :
    targetDegreeOneEquiv T ((degreeOneDiagramContinuousEquiv T C S g).targetEquiv x) =
      g.targetEquiv (targetDegreeOneEquiv T x) :=
  degreeOneDiagramEquiv_target T C S g x

/-- The inverse topological adapter recovers the actual action on the whole stage. -/
theorem degreeOneDiagramContinuousEquiv_symm_stage (g : HyperplaneGT.DiagramAut R C S)
    (A : C.Stage) (x : A.val.val →₀ R) :
    ((degreeOneDiagramContinuousEquiv T C S).symm g).stageEquiv A (degreeOneEquiv T A.val.val x) =
      degreeOneEquiv T A.val.val (g.stageEquiv A x) :=
  degreeOneDiagramEquiv_symm_stage T C S g A x

/-- The inverse topological adapter recovers the entire actual common target action. -/
theorem degreeOneDiagramContinuousEquiv_symm_target (g : HyperplaneGT.DiagramAut R C S)
    (x : Fin 2 →₀ R) :
    ((degreeOneDiagramContinuousEquiv T C S).symm g).targetEquiv (targetDegreeOneEquiv T x) =
      targetDegreeOneEquiv T (g.targetEquiv x) :=
  degreeOneDiagramEquiv_symm_target T C S g x

/-- The inverse topological adapter keeps the old inverse function. -/
theorem coe_gradedDiagramContinuousEquiv_symm :
    ⇑(gradedDiagramContinuousEquiv T C S).symm = (gradedDiagramEquiv T C S).symm := rfl

/-- The topological adapter intertwines the entire actual stage action with coordinates. -/
theorem gradedDiagramContinuousEquiv_stage (g : GradedDiagramAut T C S) (A : C.Stage)
    (x : OSAlgebra R A.val.val) :
    T.diagonalEquiv A.val.val ((gradedDiagramContinuousEquiv T C S g).stageEquiv A x) =
      g.stageEquiv A (T.diagonalEquiv A.val.val x) :=
  gradedDiagramEquiv_stage T C S g A x

/-- The topological adapter intertwines the one complete actual common target action. -/
theorem gradedDiagramContinuousEquiv_target (g : GradedDiagramAut T C S)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    T.diagonalEquiv (twoPunctureArrangement k)
        ((gradedDiagramContinuousEquiv T C S g).targetEquiv x) =
      g.targetEquiv (T.diagonalEquiv (twoPunctureArrangement k) x) :=
  gradedDiagramEquiv_target T C S g x

/-- The inverse topological adapter recovers the actual action on the whole stage. -/
theorem gradedDiagramContinuousEquiv_symm_stage (g : HyperplaneGT.GradedDiagramAut R C S)
    (A : C.Stage) (x : OSAlgebra R A.val.val) :
    ((gradedDiagramContinuousEquiv T C S).symm g).stageEquiv A (T.diagonalEquiv A.val.val x) =
      T.diagonalEquiv A.val.val (g.stageEquiv A x) :=
  gradedDiagramEquiv_symm_stage T C S g A x

/-- The inverse topological adapter recovers the entire actual common target action. -/
theorem gradedDiagramContinuousEquiv_symm_target (g : HyperplaneGT.GradedDiagramAut R C S)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    ((gradedDiagramContinuousEquiv T C S).symm g).targetEquiv
        (T.diagonalEquiv (twoPunctureArrangement k) x) =
      T.diagonalEquiv (twoPunctureArrangement k) (g.targetEquiv x) :=
  gradedDiagramEquiv_symm_target T C S g x

end OrlikSolomon.HyperplaneGT.Cohomology
