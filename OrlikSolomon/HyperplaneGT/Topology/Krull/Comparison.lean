/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.KrullTopology
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Hyperplanes

/-!
# The exact pointwise–Krull comparison

The existing global Krull topology agrees with the named pointwise topology precisely when
each scalar fixing subgroup contains the fixer of a finite-dimensional intermediate field.
`KrullFixingCondition` is an ordinary proposition. Algebraicity is sufficient, without
normality or separability. All topology choices remain explicit; importing this module
does not activate the pointwise scope or change a field topology.

Finite collections of hyperplanes have an actual coefficient intermediate field generated
by their normalized affine coefficients. Its fixer is the hyperplane fixer over any field
extension; algebraicity makes that coefficient field finite dimensional. Conversely every
finite intermediate field is fixed by one selected-stage kernel in positive dimension,
using only cofinality.

## Main definitions and results

* `KrullFixingCondition` and `krull_eq_pointwise_iff` give the exact criterion.
* `galoisPointwiseTopology_le_krull` is the unconditional topology inequality.
* `krull_eq_pointwise_of_isAlgebraic` is the algebraic wrapper.
* `hyperplaneCoefficientField`, `fixingHyperplanes_eq_coefficientField` and
  `finiteDimensional_hyperplaneCoefficientField` give the finite-equation field.
* `CofinalSystem.exists_stageKernel_le_fixingSubgroup` gives finite-field containment.
* `CofinalSystem.galoisStagePermutationTopology_eq_krull` and its algebraic wrapper
  compare the actual chosen-stage topology with Krull under the precise hypotheses.

No classification, marking or cohomology hypothesis enters. Blueprint: T06 (`thm:t06`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open Filter Topology

variable (k₀ : Type u) (k : Type v) [Field k₀] [Field k] [Algebra k₀ k]

/-- Every scalar fixer contains the fixer of a finite-dimensional intermediate field.
This is the explicit proposition (K), not a typeclass or a field of a cofinal system.
Blueprint: T06 (`thm:t06`). -/
def KrullFixingCondition : Prop :=
  ∀ a : k, ∃ E : IntermediateField k₀ k, FiniteDimensional k₀ E ∧
    E.fixingSubgroup ≤ fixingSubgroup (k ≃ₐ[k₀] k) ({a} : Set k)

/-- A finite basis of an intermediate field gives a finite scalar test for its entire
fixing subgroup. No invariance of that intermediate field under automorphisms is needed. -/
theorem exists_finset_fixingIntermediateField (E : IntermediateField k₀ k)
    [FiniteDimensional k₀ E] :
    ∃ s : Finset k, (s : Set k) ⊆ (E : Set k) ∧
      fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) = E.fixingSubgroup := by
  classical
  let b := Module.finBasis k₀ E
  let s : Finset k := Finset.univ.image (fun i ↦ ((b i : E) : k))
  have hs : (s : Set k) ⊆ (E : Set k) := by
    rintro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact (b i).property
  refine ⟨s, hs, ?_⟩
  ext σ
  simp only [mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff,
    AlgEquiv.smul_def]
  constructor
  · intro h a ha
    have hf : σ.toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap := by
      apply b.ext
      intro i
      exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    exact LinearMap.congr_fun hf ⟨a, ha⟩
  · intro h a ha
    exact h a (hs ha)

/-- Finite intermediate-field fixing subgroups are clopen for pointwise convergence,
without an algebraicity assumption on the ambient extension. -/
theorem galoisPointwise_isClopen_fixingIntermediateField (E : IntermediateField k₀ k)
    [FiniteDimensional k₀ E] :
    @IsClopen (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k)
      (E.fixingSubgroup : Set (k ≃ₐ[k₀] k)) := by
  obtain ⟨s, -, hs⟩ := exists_finset_fixingIntermediateField k₀ k E
  rw [← hs]
  exact galoisPointwise_isClopen_fixing k₀ k s

/-- Pointwise convergence is always finer than Mathlib's existing Krull topology.
Blueprint: T06 (`thm:t06`). -/
theorem galoisPointwiseTopology_le_krull :
    galoisPointwiseTopology k₀ k ≤ krullTopology k₀ k := by
  have h : @nhds _ (galoisPointwiseTopology k₀ k) (1 : k ≃ₐ[k₀] k) ≤
      @nhds _ (krullTopology k₀ k) 1 := by
    let : TopologicalSpace (k ≃ₐ[k₀] k) := galoisPointwiseTopology k₀ k
    intro U hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff k₀ k U).mp hU
    let : FiniteDimensional k₀ E := hE
    exact Filter.mem_of_superset
      ((galoisPointwise_isClopen_fixingIntermediateField k₀ k E).isOpen.mem_nhds
        E.fixingSubgroup.one_mem) hEU
  apply le_of_nhds_le_nhds
  intro σ
  rw [← @nhds_translation_mul_inv (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) _
    (galoisPointwise_isTopologicalGroup k₀ k) σ,
    ← @nhds_translation_mul_inv (k ≃ₐ[k₀] k) (krullTopology k₀ k) _ inferInstance σ]
  exact Filter.comap_mono h

private theorem fixingFinite_mem_krull (hK : KrullFixingCondition k₀ k) (s : Finset k) :
    (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) ∈
      @nhds _ (krullTopology k₀ k) 1 := by
  have hs : (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) : Set _) =
      ⋂ a ∈ s, (fixingSubgroup (k ≃ₐ[k₀] k) ({a} : Set k) : Set (k ≃ₐ[k₀] k)) := by
    ext σ
    simp [mem_fixingSubgroup_iff]
  rw [hs]
  apply (Filter.biInter_mem s.finite_toSet).mpr
  intro a _
  obtain ⟨E, hE, hEa⟩ := hK a
  exact (krullTopology_mem_nhds_one_iff k₀ k _).mpr ⟨E, hE, hEa⟩

/-- Mathlib's actual global Krull topology equals pointwise convergence exactly under
the finite-intermediate-field fixing condition (K). Blueprint: T06 (`thm:t06`). -/
theorem krull_eq_pointwise_iff :
    krullTopology k₀ k = galoisPointwiseTopology k₀ k ↔ KrullFixingCondition k₀ k := by
  constructor
  · intro h a
    have ha : (fixingSubgroup (k ≃ₐ[k₀] k) ({a} : Set k) : Set _) ∈
        @nhds _ (galoisPointwiseTopology k₀ k) 1 := by
      simpa only [Finset.coe_singleton] using
        (galoisPointwise_nhds_one_basis k₀ k).mem_of_mem (i := {a}) trivial
    rw [← h] at ha
    exact (krullTopology_mem_nhds_one_iff k₀ k _).mp ha
  · intro hK
    have h : @nhds _ (krullTopology k₀ k) (1 : k ≃ₐ[k₀] k) ≤
        @nhds _ (galoisPointwiseTopology k₀ k) 1 := by
      intro U hU
      obtain ⟨s, hs⟩ := (galoisPointwise_mem_nhds_one_iff k₀ k U).mp hU
      exact Filter.mem_of_superset (fixingFinite_mem_krull k₀ k hK s) hs
    exact (inferInstance : IsTopologicalGroup (k ≃ₐ[k₀] k)).ext
      (galoisPointwise_isTopologicalGroup k₀ k)
      (le_antisymm h (nhds_mono (galoisPointwiseTopology_le_krull k₀ k)))

/-- Algebraicity supplies (K) by adjoining one algebraic element. Normality and separability
are not required. Blueprint: T06 (`thm:t06`). -/
theorem krullFixingCondition_of_isAlgebraic [Algebra.IsAlgebraic k₀ k] :
    KrullFixingCondition k₀ k := by
  intro a
  refine ⟨IntermediateField.adjoin k₀ {a},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a), ?_⟩
  intro σ hσ
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hxa : x = a := Set.mem_singleton_iff.mp hx
  subst x
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ a
    (IntermediateField.subset_adjoin k₀ {a} (Set.mem_singleton a))

/-- Over an algebraic field extension, the existing global Krull topology is exactly the
named pointwise topology. Blueprint: T06 (`thm:t06`). -/
theorem krull_eq_pointwise_of_isAlgebraic [Algebra.IsAlgebraic k₀ k] :
    krullTopology k₀ k = galoisPointwiseTopology k₀ k :=
  (krull_eq_pointwise_iff k₀ k).mpr (krullFixingCondition_of_isAlgebraic k₀ k)

variable {k} {n : ℕ}

/-- The actual intermediate field generated by all normalized affine coefficients of a
finite hyperplane collection, including the constants. Blueprint: T06 (`thm:t06`). -/
def hyperplaneCoefficientField (s : Finset (Hyperplane k n)) : IntermediateField k₀ k := by
  classical
  exact IntermediateField.adjoin k₀ (s.biUnion hyperplaneCoefficientTests : Set k)

/-- The empty hyperplane collection generates exactly the base intermediate field. -/
@[simp]
theorem hyperplaneCoefficientField_empty :
    hyperplaneCoefficientField k₀ (∅ : Finset (Hyperplane k n)) = ⊥ := by
  simp [hyperplaneCoefficientField]

/-- Fixing a finite collection of hyperplanes is exactly fixing its coefficient field.
This equality needs no algebraicity of the ambient extension. Blueprint: T06 (`thm:t06`). -/
theorem fixingHyperplanes_eq_coefficientField (s : Finset (Hyperplane k n)) :
    fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n)) =
      (hyperplaneCoefficientField k₀ s).fixingSubgroup := by
  classical
  rw [fixingHyperplanes_eq_fixingCoefficients]
  ext σ
  simp only [mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff,
    AlgEquiv.smul_def]
  exact (IntermediateField.forall_mem_adjoin_smul_eq_self_iff k₀ σ).symm

/-- Under algebraicity, the actual field generated by finitely many normalized affine
coefficients is finite dimensional. Blueprint: T06 (`thm:t06`). -/
theorem finiteDimensional_hyperplaneCoefficientField [Algebra.IsAlgebraic k₀ k]
    (s : Finset (Hyperplane k n)) :
    FiniteDimensional k₀ (hyperplaneCoefficientField k₀ s) := by
  classical
  exact IntermediateField.finiteDimensional_adjoin
    (fun a _ ↦ Algebra.IsIntegral.isIntegral a)

namespace CofinalSystem

variable {k₀} (C : CofinalSystem k₀ k n)

/-- Every finite intermediate-field fixer contains one actual chosen-stage permutation
kernel in positive dimension. Only cofinality and geometric coordinate fibers are used;
the ambient extension need not be algebraic. Blueprint: T06 (`thm:t06`). -/
theorem exists_stageKernel_le_fixingSubgroup (hn : 1 ≤ n) (E : IntermediateField k₀ k)
    [FiniteDimensional k₀ E] :
    ∃ A : C.Stage, C.galoisStageKernel A ≤ E.fixingSubgroup := by
  classical
  obtain ⟨s, -, hs⟩ := exists_finset_fixingIntermediateField k₀ k E
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨A, hA⟩ := C.exists_stage_containing (s.image (coordinateFiber i))
  refine ⟨A, ?_⟩
  rw [← hs]
  intro σ hσ
  rw [mem_fixingSubgroup_iff]
  intro a ha
  change σ a = a
  apply coordinateFiber_injective i
  rw [← galois_smul_coordinateFiber]
  exact (C.mem_galoisStageKernel_iff A σ).mp hσ _
    (hA _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))

/-- Under the exact condition (K), whole selected-stage permutation convergence is the
existing Krull topology. The chosen family need not contain unions. -/
theorem galoisStagePermutationTopology_eq_krull (hn : 1 ≤ n)
    (hK : KrullFixingCondition k₀ k) :
    C.galoisStagePermutationTopology = krullTopology k₀ k := by
  rw [C.galoisStagePermutationTopology_eq_pointwise hn, (krull_eq_pointwise_iff k₀ k).mpr hK]

/-- Algebraicity gives the selected-stage permutation comparison with the existing Krull
topology already in dimension one. -/
theorem galoisStagePermutationTopology_eq_krull_of_isAlgebraic [Algebra.IsAlgebraic k₀ k]
    (hn : 1 ≤ n) : C.galoisStagePermutationTopology = krullTopology k₀ k :=
  C.galoisStagePermutationTopology_eq_krull hn (krullFixingCondition_of_isAlgebraic k₀ k)

end CofinalSystem

end OrlikSolomon.HyperplaneGT
