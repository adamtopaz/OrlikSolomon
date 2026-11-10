/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Basic.Components

/-!
# Complete-stage neighborhood bases

Simultaneous identity at one selected stage and at the single common target defines a
normal clopen subgroup of either marked diagram group. These subgroups form a neighborhood
basis at the identity. Only cofinal enlargement is required: a selected family need not be
closed under arrangement unions.

For quadratic diagrams, agreement descends along an injective free-module inclusion. For
full graded diagrams the same argument on degree one and algebra generation suffice;
no injectivity assertion about the full Orlik–Solomon inclusion is used.

Blueprint: the pure diagram portion of T02 (`lem:t02`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Filter Topology
open scoped FiniteStageTopology

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {n : ℕ} {R : Type r} [CommRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

namespace DiagramAut

/-- Equality of quadratic components descends from a larger stage along the free inclusion.
This holds also for zero coefficients and empty stages. -/
theorem stageEquiv_eq_of_le {𝒜 ℬ : C.Stage} (h𝒜ℬ : 𝒜 ≤ ℬ)
    {g h : DiagramAut R C S} (hℬ : g.stageEquiv ℬ = h.stageEquiv ℬ) :
    g.stageEquiv 𝒜 = h.stageEquiv 𝒜 := by
  apply LinearEquiv.ext
  intro x
  apply Finsupp.mapDomain_injective (Arrangement.inclusion_injective h𝒜ℬ)
  calc
    Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜ℬ) (g.stageEquiv 𝒜 x) =
        g.stageEquiv ℬ (Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜ℬ) x) :=
      (DFunLike.congr_fun (g.inclusion_naturality h𝒜ℬ) x).symm
    _ = h.stageEquiv ℬ (Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜ℬ) x) := by rw [hℬ]
    _ = Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜ℬ) (h.stageEquiv 𝒜 x) :=
      DFunLike.congr_fun (h.inclusion_naturality h𝒜ℬ) x

variable (R C S)

/-- The kernel of agreement with identity at one complete stage and the one common target.
Blueprint: T02 (`lem:t02`). -/
def stageKernel (𝒜 : C.Stage) : Subgroup (DiagramAut R C S) :=
  DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup R C S) 𝒜

@[simp]
theorem mem_stageKernel (𝒜 : C.Stage) (g : DiagramAut R C S) :
    g ∈ stageKernel R C S 𝒜 ↔ g.stageEquiv 𝒜 = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (quadraticDiagramAutSubgroup R C S) 𝒜 g

instance stageKernel_normal (𝒜 : C.Stage) : (stageKernel R C S 𝒜).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (quadraticDiagramAutSubgroup R C S) 𝒜).Normal

/-- Enlarging the stage makes its simultaneous stage-and-target kernel smaller. -/
theorem stageKernel_antitone : Antitone (stageKernel R C S) := by
  intro 𝒜 ℬ h𝒜ℬ g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel R C S ℬ g).mp hg
  exact (mem_stageKernel R C S 𝒜 g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) h𝒜ℬ hstage, htarget⟩

/-- Every complete-stage-and-target kernel is clopen. Blueprint: T02 (`lem:t02`). -/
theorem isClopen_stageKernel (𝒜 : C.Stage) :
    IsClopen (stageKernel R C S 𝒜 : Set (DiagramAut R C S)) :=
  DiscreteFamily.isClopen_stageKernel (quadraticDiagramAutSubgroup R C S) 𝒜

/-- Every left coset of a simultaneous stage-and-target kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (𝒜 : C.Stage) (g : DiagramAut R C S) :
    IsClopen {h : DiagramAut R C S | g⁻¹ * h ∈ stageKernel R C S 𝒜} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (quadraticDiagramAutSubgroup R C S) 𝒜 g

/-- One selected complete stage and the original common target give a neighborhood basis.
No union closure, classification, algebraicity or nonzero-coefficient assumption is required.
Blueprint: T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : DiagramAut R C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun 𝒜 ↦ (stageKernel R C S 𝒜 : Set (DiagramAut R C S))) := by
  classical
  refine (DiscreteFamily.nhds_one_finiteBasis (quadraticDiagramAutSubgroup R C S)).to_hasBasis
    ?_ ?_
  · intro I hI
    obtain ⟨ℬ, hℬ⟩ := C.exists_ge_finset hI.toFinset
    refine ⟨ℬ, trivial, ?_⟩
    intro g hg
    obtain ⟨hstage, htarget⟩ := (mem_stageKernel R C S ℬ g).mp hg
    exact ⟨fun 𝒜 h𝒜 ↦ stageEquiv_eq_of_le (h := 1)
      (hℬ 𝒜 (hI.mem_toFinset.mpr h𝒜)) hstage, htarget⟩
  · intro 𝒜 _
    refine ⟨{𝒜}, Set.finite_singleton 𝒜, ?_⟩
    intro g hg
    exact (mem_stageKernel R C S 𝒜 g).mpr ⟨hg.1 𝒜 rfl, hg.2⟩

end DiagramAut

namespace GradedDiagramAut

/-- Equality of full graded components descends along an inclusion, by the injective
free-module map on degree one followed by algebra generation. -/
theorem stageEquiv_eq_of_le {𝒜 ℬ : C.Stage} (h𝒜ℬ : 𝒜 ≤ ℬ)
    {g h : GradedDiagramAut R C S} (hℬ : g.stageEquiv ℬ = h.stageEquiv ℬ) :
    g.stageEquiv 𝒜 = h.stageEquiv 𝒜 := by
  have hlinear : (toQuadratic R C S g).stageEquiv ℬ =
      (toQuadratic R C S h).stageEquiv ℬ := by
    apply LinearEquiv.ext
    intro x
    apply (osDegreeOneEquiv R ℬ.val.val).injective
    apply Subtype.ext
    change (osDegreeOneEquiv R ℬ.val.val (g.stageLinearEquiv ℬ x) : OSAlgebra R ℬ.val.val) =
      osDegreeOneEquiv R ℬ.val.val (h.stageLinearEquiv ℬ x)
    rw [stageLinearEquiv_apply, stageLinearEquiv_apply, hℬ]
  have h𝒜 := DiagramAut.stageEquiv_eq_of_le h𝒜ℬ hlinear
  change g.stageLinearEquiv 𝒜 = h.stageLinearEquiv 𝒜 at h𝒜
  apply AlgEquiv.coe_toAlgHom_injective
  apply OSAlgebra.algHom_ext
  intro H
  have hgen := congrArg (fun f : (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) ↦
    (osDegreeOneEquiv R 𝒜.val.val (f (Finsupp.single H 1)) : OSAlgebra R 𝒜.val.val)) h𝒜
  rw [stageLinearEquiv_apply, stageLinearEquiv_apply] at hgen
  simpa using hgen

variable (R C S)

/-- Identity at a complete graded stage together with identity at the original common target.
Blueprint: T02 (`lem:t02`). -/
def stageKernel (𝒜 : C.Stage) : Subgroup (GradedDiagramAut R C S) :=
  DiscreteFamily.stageKernel (gradedDiagramAutSubgroup R C S) 𝒜

@[simp]
theorem mem_stageKernel (𝒜 : C.Stage) (g : GradedDiagramAut R C S) :
    g ∈ stageKernel R C S 𝒜 ↔ g.stageEquiv 𝒜 = 1 ∧ g.targetEquiv = 1 :=
  DiscreteFamily.mem_stageKernel (gradedDiagramAutSubgroup R C S) 𝒜 g

instance stageKernel_normal (𝒜 : C.Stage) : (stageKernel R C S 𝒜).Normal :=
  inferInstanceAs (DiscreteFamily.stageKernel (gradedDiagramAutSubgroup R C S) 𝒜).Normal

/-- Enlarging the selected stage makes its complete graded stage-and-target kernel smaller. -/
theorem stageKernel_antitone : Antitone (stageKernel R C S) := by
  intro 𝒜 ℬ h𝒜ℬ g hg
  obtain ⟨hstage, htarget⟩ := (mem_stageKernel R C S ℬ g).mp hg
  exact (mem_stageKernel R C S 𝒜 g).mpr
    ⟨stageEquiv_eq_of_le (h := 1) h𝒜ℬ hstage, htarget⟩

/-- Complete graded stage-and-target kernels are clopen. Blueprint: T02 (`lem:t02`). -/
theorem isClopen_stageKernel (𝒜 : C.Stage) :
    IsClopen (stageKernel R C S 𝒜 : Set (GradedDiagramAut R C S)) :=
  DiscreteFamily.isClopen_stageKernel (gradedDiagramAutSubgroup R C S) 𝒜

/-- The left cosets of every complete graded stage-and-target kernel are clopen. -/
theorem isClopen_stageKernel_leftCoset (𝒜 : C.Stage) (g : GradedDiagramAut R C S) :
    IsClopen {h : GradedDiagramAut R C S | g⁻¹ * h ∈ stageKernel R C S 𝒜} :=
  DiscreteFamily.isClopen_stageKernel_leftCoset (gradedDiagramAutSubgroup R C S) 𝒜 g

/-- One complete graded stage and the original target give an identity-neighborhood basis.
This uses degree-one faithfulness, not injectivity of the full OS inclusion.
Blueprint: T02 (`lem:t02`). -/
theorem nhds_one_stageBasis :
    (𝓝 (1 : GradedDiagramAut R C S)).HasBasis (fun _ : C.Stage ↦ True)
      (fun 𝒜 ↦ (stageKernel R C S 𝒜 : Set (GradedDiagramAut R C S))) := by
  classical
  refine (DiscreteFamily.nhds_one_finiteBasis (gradedDiagramAutSubgroup R C S)).to_hasBasis
    ?_ ?_
  · intro I hI
    obtain ⟨ℬ, hℬ⟩ := C.exists_ge_finset hI.toFinset
    refine ⟨ℬ, trivial, ?_⟩
    intro g hg
    obtain ⟨hstage, htarget⟩ := (mem_stageKernel R C S ℬ g).mp hg
    exact ⟨fun 𝒜 h𝒜 ↦ stageEquiv_eq_of_le (h := 1)
      (hℬ 𝒜 (hI.mem_toFinset.mpr h𝒜)) hstage, htarget⟩
  · intro 𝒜 _
    refine ⟨{𝒜}, Set.finite_singleton 𝒜, ?_⟩
    intro g hg
    exact (mem_stageKernel R C S 𝒜 g).mpr ⟨hg.1 𝒜 rfl, hg.2⟩

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT
