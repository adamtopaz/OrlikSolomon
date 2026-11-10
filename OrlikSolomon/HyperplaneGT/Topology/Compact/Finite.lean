/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Compact.Closed
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite-coefficient compactness in the original diagram topologies

Finite coefficients make the complete linear stage and target groups finite. For full
algebra automorphisms, only the subgroups preserving every degree are proved finite:
degree-one restriction is faithful because the whole algebra is generated in degree one.

Their product is a compact subset of the original discrete full-automorphism product.
The closed full diagram lies in that compact set. No replacement topology, classification,
coefficient nontriviality or algebraicity assumption is used. Compactness instances are
activated only by `FiniteStageTopology`; the existing separation results give profiniteness.
Blueprint: T03 (`prop:t03`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

variable {k : Type v} [Field k] (R : Type r) [CommRing R]

section Arrangement

variable {V : Type v} [AddCommGroup V] [Module k V] (𝒜 : Arrangement k V)

open scoped Pointwise in
/-- The actual full OS algebra automorphisms preserving every homogeneous degree by image
equality, formed from Mathlib's stabilizers of the existing degree submodules. -/
def osGradedAutSubgroup : Subgroup (OSAlgebra R 𝒜 ≃ₐ[R] OSAlgebra R 𝒜) :=
  ⨅ q : ℕ, MulAction.stabilizer (OSAlgebra R 𝒜 ≃ₐ[R] OSAlgebra R 𝒜)
    (OSAlgebra.degree R 𝒜 q)

/-- Membership retains every whole-degree image equality and hides the stabilizer
implementation. -/
@[simp] theorem mem_osGradedAutSubgroup (g : OSAlgebra R 𝒜 ≃ₐ[R] OSAlgebra R 𝒜) :
    g ∈ osGradedAutSubgroup R 𝒜 ↔
      ∀ q : ℕ, (OSAlgebra.degree R 𝒜 q).map g.toLinearMap = OSAlgebra.degree R 𝒜 q := by
  simp only [osGradedAutSubgroup, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff,
    Submodule.pointwise_smul_def]
  rfl

variable [FiniteDimensional k V]

/-- Full degree-preserving automorphisms are determined by their actual canonical degree-one
restriction, because the OS generators generate the whole algebra. -/
theorem osGradedAutSubgroup_degreeOne_injective :
    Function.Injective (fun g : osGradedAutSubgroup R 𝒜 ↦ osDegreeOneAut R 𝒜 g.val
      ((mem_osGradedAutSubgroup R 𝒜 g.val).mp g.property 1)) := by
  intro g h heq
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply OSAlgebra.algHom_ext
  intro H
  have hgen := congrArg (fun f : (𝒜 →₀ R) ≃ₗ[R] (𝒜 →₀ R) ↦
    (osDegreeOneEquiv R 𝒜 (f (Finsupp.single H 1)) : OSAlgebra R 𝒜)) heq
  rw [osDegreeOneAut_apply, osDegreeOneAut_apply] at hgen
  simpa using hgen

/-- With finite coefficients, the subgroup preserving every degree is finite. No claim
about the unrestricted full algebra-automorphism group is needed. -/
theorem finite_osGradedAutSubgroup [Finite R] : Finite (osGradedAutSubgroup R 𝒜) := by
  classical
  let : Fintype R := Fintype.ofFinite R
  let : Finite ((𝒜 →₀ R) ≃ₗ[R] (𝒜 →₀ R)) := FunLike.finite _
  exact Finite.of_injective _ (osGradedAutSubgroup_degreeOne_injective R 𝒜)

end Arrangement

variable {k₀ : Type u} [Field k₀] [Algebra k₀ k] {n : ℕ}
  (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Finite coefficients make the actual quadratic subgroup compact in the original ambient
product of complete discrete linear groups. Blueprint: T03 (`prop:t03`). -/
theorem DiagramAut.isCompact_subgroup [Finite R] :
    @IsCompact (QuadraticAutFamily R C) (DiagramAut.familyTopology R C)
      (quadraticDiagramAutSubgroup R C S : Set (QuadraticAutFamily R C)) := by
  classical
  let : Fintype R := Fintype.ofFinite R
  let : ∀ 𝒜 : C.Stage, TopologicalSpace
      ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) := fun _ ↦ ⊥
  let : TopologicalSpace ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) := ⊥
  let : ∀ 𝒜 : C.Stage, Finite ((𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R)) :=
    fun _ ↦ FunLike.finite _
  let : Finite ((Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R)) := FunLike.finite _
  exact (DiagramAut.isClosed_subgroup R C S).isCompact

/-- Finite degree-preserving factor subgroups give a compact set in the original full
automorphism product, containing the closed full diagram. Blueprint: T03 (`prop:t03`). -/
theorem GradedDiagramAut.isCompact_subgroup [Finite R] :
    @IsCompact (GradedAutFamily R C) (GradedDiagramAut.familyTopology R C)
      (gradedDiagramAutSubgroup R C S : Set (GradedAutFamily R C)) := by
  let : ∀ 𝒜 : C.Stage, TopologicalSpace
      (OSAlgebra R 𝒜.val.val ≃ₐ[R] OSAlgebra R 𝒜.val.val) := fun _ ↦ ⊥
  let : TopologicalSpace
      (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R] OSAlgebra R (twoPunctureArrangement k)) := ⊥
  have hstage (𝒜 : C.Stage) : IsCompact
      (osGradedAutSubgroup R 𝒜.val.val : Set (OSAlgebra R 𝒜.val.val ≃ₐ[R]
        OSAlgebra R 𝒜.val.val)) := by
    have : Finite (osGradedAutSubgroup R 𝒜.val.val) := finite_osGradedAutSubgroup R _
    exact (Set.toFinite _).isCompact
  have htarget : IsCompact (osGradedAutSubgroup R (twoPunctureArrangement k) :
      Set (OSAlgebra R (twoPunctureArrangement k) ≃ₐ[R]
        OSAlgebra R (twoPunctureArrangement k))) := by
    have : Finite (osGradedAutSubgroup R (twoPunctureArrangement k)) :=
      finite_osGradedAutSubgroup R _
    exact (Set.toFinite _).isCompact
  apply ((isCompact_pi_infinite hstage).prod htarget).of_isClosed_subset
    (GradedDiagramAut.isClosed_subgroup R C S)
  intro g hg
  exact ⟨fun 𝒜 ↦ (mem_osGradedAutSubgroup R _ _).mpr (hg.1 𝒜),
    (mem_osGradedAutSubgroup R _ _).mpr hg.2.1⟩

/-- The existing quadratic diagram topology is compact for every finite coefficient ring,
including the zero ring, without a classification or dimension hypothesis. -/
theorem DiagramAut.compactSpace [Finite R] :
    @CompactSpace (DiagramAut R C S) (DiagramAut.stageTopology R C S) := by
  let : TopologicalSpace (QuadraticAutFamily R C) := DiagramAut.familyTopology R C
  exact isCompact_iff_compactSpace.mp (DiagramAut.isCompact_subgroup R C S)

/-- The exact original full graded diagram topology is compact for finite coefficients,
using only the finite degree-preserving factors. -/
theorem GradedDiagramAut.compactSpace [Finite R] :
    @CompactSpace (GradedDiagramAut R C S) (GradedDiagramAut.stageTopology R C S) := by
  let : TopologicalSpace (GradedAutFamily R C) := GradedDiagramAut.familyTopology R C
  exact isCompact_iff_compactSpace.mp (GradedDiagramAut.isCompact_subgroup R C S)

namespace FiniteStageTopology

open scoped FiniteStageTopology

/-- Finite-coefficient quadratic compactness is activated only in the finite-stage scope. -/
scoped instance diagramCompactSpace [Finite R] : CompactSpace (DiagramAut R C S) :=
  DiagramAut.compactSpace R C S

/-- Finite-coefficient full graded compactness is activated only in the finite-stage scope. -/
scoped instance gradedCompactSpace [Finite R] : CompactSpace (GradedDiagramAut R C S) :=
  GradedDiagramAut.compactSpace R C S

end FiniteStageTopology

end OrlikSolomon.HyperplaneGT
