/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.Krull.Pointwise
public import OrlikSolomon.HyperplaneGT.Diagram.GaloisAction.Stage

/-!
# Finite hyperplane tests for pointwise field automorphisms

Normalizing an affine hyperplane equation by a nonzero normal coefficient gives a finite
scalar test for its stabilizer, including the constant coefficient. Arbitrary geometric
coordinate fibers provide the converse comparison. Cofinality then identifies the same
topology with the kernels of the actual finite-stage label permutations.

## Main definitions and results

* `hyperplaneCoefficientTests` and `hyperplaneStabilizer_eq_fixingCoefficients` give the
  exact finite scalar stabilizer test.
* `coordinateFiber`, `coordinateFiber_injective` and `galois_smul_coordinateFiber` give
  equivariant fibers at arbitrary geometric scalars.
* `galoisPointwise_nhds_one_hyperplaneBasis` gives the finite hyperplane fixing basis.
* `galoisStagePermutation` packages the existing actual finite-stage label action.
* `CofinalSystem.galoisPointwise_nhds_one_stageKernelBasis` and
  `CofinalSystem.galoisStagePermutationTopology_eq_pointwise` give the selected-stage
  kernel basis and the equality of the named topologies.

The pure M8 `Diagram.GaloisAction.Stage` import reuses `galoisLabelEquiv`; no cohomology or
reconstruction theorem enters. Neither algebraicity nor union closure of a cofinal family
is assumed. Blueprint: T05 (`lem:t05`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open Filter Topology
open scoped GaloisPointwise

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}

/-- Divide every affine coefficient, including the constant, by the selected normal pivot. -/
def normalizedAffineCoefficients (f : (Fin n → k) →ᵃ[k] k) (j : Fin n) :
    Fin (n + 1) → k :=
  fun i ↦ affineCoefficients f i / affineCoefficients f j.succ

/-- A nonzero selected normal coefficient becomes one after normalization. -/
theorem normalizedAffineCoefficients_pivot (f : (Fin n → k) →ᵃ[k] k) (j : Fin n)
    (hj : affineCoefficients f j.succ ≠ 0) : normalizedAffineCoefficients f j j.succ = 1 :=
  div_self hj

/-- Fixed-pivot normalization is unchanged by multiplying an equation by any unit. -/
@[simp]
theorem normalizedAffineCoefficients_smul (f : (Fin n → k) →ᵃ[k] k) (j : Fin n)
    (c : kˣ) :
    normalizedAffineCoefficients ((c : k) • f) j = normalizedAffineCoefficients f j := by
  funext i
  simp only [normalizedAffineCoefficients, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ c.ne_zero

/-- Normalizing at a nonzero pivot preserves the entire affine zero locus. -/
theorem zeroLocus_coefficientForm_normalized (f : (Fin n → k) →ᵃ[k] k) (j : Fin n)
    (hj : affineCoefficients f j.succ ≠ 0) :
    zeroLocus (coefficientForm (normalizedAffineCoefficients f j)) = zeroLocus f := by
  have h : normalizedAffineCoefficients f j =
      (affineCoefficients f j.succ)⁻¹ • affineCoefficients f := by
    ext i
    simp [normalizedAffineCoefficients, div_eq_mul_inv, mul_comm]
  rw [h, map_smul, coefficientForm_affineCoefficients, zeroLocus_smul (inv_ne_zero hj)]

/-- Coefficient normalization intertwines the field action at the same pivot. -/
@[simp]
theorem normalizedAffineCoefficients_fieldAffineForm (σ : k ≃ₐ[k₀] k)
    (f : (Fin n → k) →ᵃ[k] k) (j : Fin n) :
    normalizedAffineCoefficients (fieldAffineForm σ.toRingEquiv f) j =
      fun i ↦ σ (normalizedAffineCoefficients f j i) := by
  ext i
  simp only [normalizedAffineCoefficients, affineCoefficients_fieldAffineForm]
  exact (map_div₀ σ _ _).symm

/-- Fixing a hyperplane is equivalent to fixing all coefficients of any normalized equation.
The pivot is normal, so the affine constant coefficient is retained in the test. -/
theorem galois_smul_eq_iff_normalizedCoefficients (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H.val)
    (j : Fin n) (hj : affineCoefficients f j.succ ≠ 0) :
    σ • H = H ↔ ∀ i, σ (normalizedAffineCoefficients f j i) =
      normalizedAffineCoefficients f j i := by
  have hσf := isEquation_fieldAffineForm σ.toRingEquiv hf
  constructor
  · intro h
    have hg : IsEquation (fieldAffineForm σ.toRingEquiv f) H.val := by
      simpa only [← galois_smul_val, h] using hσf
    obtain ⟨c, hc, -⟩ := hf.existsUnique_smul hg
    have hn := normalizedAffineCoefficients_smul f j c
    rw [← hc, normalizedAffineCoefficients_fieldAffineForm] at hn
    exact congrFun hn
  · intro h
    have hn : normalizedAffineCoefficients (fieldAffineForm σ.toRingEquiv f) j =
        normalizedAffineCoefficients f j := by
      rw [normalizedAffineCoefficients_fieldAffineForm]
      exact funext h
    have hjσ : affineCoefficients (fieldAffineForm σ.toRingEquiv f) j.succ ≠ 0 := by
      rw [affineCoefficients_fieldAffineForm]
      exact fun h ↦ hj (σ.toRingEquiv.injective (h.trans (map_zero _).symm))
    apply Subtype.ext
    change fieldAffineSubspace σ.toRingEquiv H.val = H.val
    rw [← hσf.zeroLocus_eq, ← hf.zeroLocus_eq,
      ← zeroLocus_coefficientForm_normalized _ j hjσ,
      ← zeroLocus_coefficientForm_normalized _ j hj, hn]

private def coefficientPivot (H : Hyperplane k n) : Fin n :=
  (exists_normal_coefficient_ne_zero_of_isEquation (isEquation_equation H.property)).choose

private theorem coefficientPivot_ne_zero (H : Hyperplane k n) :
    affineCoefficients (equation H.val) (coefficientPivot H).succ ≠ 0 :=
  (exists_normal_coefficient_ne_zero_of_isEquation (isEquation_equation H.property)).choose_spec

/-- A finite scalar test for a hyperplane stabilizer: all normalized affine coefficients,
including the constant term. Consumers need only the hyperplane, not its chosen equation.
Blueprint: T05 (`lem:t05`). -/
def hyperplaneCoefficientTests (H : Hyperplane k n) : Finset k :=
  by
    classical
    exact Finset.univ.image (normalizedAffineCoefficients (equation H.val)
      (exists_normal_coefficient_ne_zero_of_isEquation
        (isEquation_equation H.property)).choose)

/-- The finite normalized scalar test characterizes the hyperplane stabilizer exactly. -/
theorem galois_smul_eq_iff_fixingCoefficients (σ : k ≃ₐ[k₀] k) (H : Hyperplane k n) :
    σ • H = H ↔ ∀ a ∈ hyperplaneCoefficientTests H, σ a = a := by
  classical
  rw [galois_smul_eq_iff_normalizedCoefficients σ H (isEquation_equation H.property)
    (coefficientPivot H) (coefficientPivot_ne_zero H)]
  simp only [hyperplaneCoefficientTests, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro h a ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h _ ⟨i, rfl⟩

/-- A hyperplane stabilizer is the existing fixing subgroup of its finite scalar test.
Blueprint: T05 (`lem:t05`). -/
theorem hyperplaneStabilizer_eq_fixingCoefficients (H : Hyperplane k n) :
    MulAction.stabilizer (k ≃ₐ[k₀] k) H =
      fixingSubgroup (k ≃ₐ[k₀] k) (hyperplaneCoefficientTests H : Set k) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff, Finset.mem_coe,
    AlgEquiv.smul_def]
  exact galois_smul_eq_iff_fixingCoefficients σ H

/-- The coordinate fiber at an arbitrary geometric scalar, with no base-field restriction.
Supplying an actual coordinate avoids a separate dimension hypothesis. -/
def coordinateFiber (i : Fin n) (a : k) : Hyperplane k n :=
  ⟨zeroLocus ((LinearMap.proj i).toAffineMap - AffineMap.const k _ a),
    isHyperplane_zeroLocus_iff.mpr (by
      intro h
      have hh := congrArg (fun f : (Fin n → k) →ₗ[k] k ↦ f (Pi.single i 1)) h
      simp at hh)⟩

/-- Membership in a geometric coordinate fiber is the literal coordinate equation. -/
@[simp]
theorem mem_coordinateFiber (i : Fin n) (a : k) (x : Fin n → k) :
    x ∈ (coordinateFiber i a).val ↔ x i = a := by
  simp [coordinateFiber, sub_eq_zero]

/-- All geometric scalar values are distinguished by a fixed coordinate's fibers. -/
theorem coordinateFiber_injective (i : Fin n) :
    Function.Injective (coordinateFiber (k := k) i) := by
  intro a b h
  have ha : Pi.single i a ∈ (coordinateFiber i a).val := by simp
  rw [h] at ha
  simpa using ha

/-- Two fibers of the same coordinate agree exactly when their geometric values agree. -/
@[simp]
theorem coordinateFiber_inj (i : Fin n) (a b : k) :
    coordinateFiber i a = coordinateFiber i b ↔ a = b :=
  (coordinateFiber_injective i).eq_iff

/-- Coefficient Galois action sends the geometric fiber at `a` to the fiber at `σ a`.
Blueprint: T05 (`lem:t05`). -/
@[simp]
theorem galois_smul_coordinateFiber (σ : k ≃ₐ[k₀] k) (i : Fin n) (a : k) :
    σ • coordinateFiber i a = coordinateFiber i (σ a) := by
  apply Subtype.ext
  ext x
  simp only [galois_smul_val, mem_fieldAffineSubspace, mem_coordinateFiber,
    fieldCoordinateAddEquiv_symm_apply]
  exact σ.toRingEquiv.symm_apply_eq

open scoped Classical in
/-- Fixing finitely many hyperplanes is exactly one finite scalar fixing test, obtained by
collecting all their normalized affine coefficients. -/
theorem fixingHyperplanes_eq_fixingCoefficients (s : Finset (Hyperplane k n)) :
    fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n)) =
      fixingSubgroup (k ≃ₐ[k₀] k)
        (s.biUnion hyperplaneCoefficientTests : Set k) := by
  classical
  ext σ
  simp only [mem_fixingSubgroup_iff, Finset.mem_coe, AlgEquiv.smul_def,
    Finset.mem_biUnion]
  constructor
  · rintro h a ⟨H, hH, ha⟩
    exact (galois_smul_eq_iff_fixingCoefficients σ H).mp (h H hH) a ha
  · intro h H hH
    exact (galois_smul_eq_iff_fixingCoefficients σ H).mpr
      (fun a ha ↦ h a ⟨H, hH, ha⟩)

open scoped Classical in
/-- Finite scalar fixing tests are realized exactly by geometric coordinate fibers. -/
theorem fixingCoordinateFibers_eq (i : Fin n) (s : Finset k) :
    fixingSubgroup (k ≃ₐ[k₀] k)
      (s.image (coordinateFiber i) : Set (Hyperplane k n)) =
      fixingSubgroup (k ≃ₐ[k₀] k) (s : Set k) := by
  classical
  ext σ
  simp only [mem_fixingSubgroup_iff, Finset.mem_coe, Finset.mem_image,
    AlgEquiv.smul_def]
  constructor
  · intro h a ha
    exact coordinateFiber_injective i (by simpa using h _ ⟨a, ha, rfl⟩)
  · rintro h _ ⟨a, ha, rfl⟩
    simpa using congrArg (coordinateFiber i) (h a ha)

/-- Every finite hyperplane fixing subgroup is clopen, in every dimension. -/
theorem galoisPointwise_isClopen_fixingHyperplanes (s : Finset (Hyperplane k n)) :
    @IsClopen (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k)
      (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n)) : Set _) := by
  classical
  rw [fixingHyperplanes_eq_fixingCoefficients]
  exact galoisPointwise_isClopen_fixing k₀ k _

/-- Finite hyperplane fixing subgroups form the pointwise identity basis as soon as one
coordinate exists. No algebraicity or finite-orbit hypothesis is needed.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_nhds_one_hyperplaneBasis (hn : 1 ≤ n) :
    (@nhds _ (galoisPointwiseTopology k₀ k) 1).HasBasis
      (fun _ : Finset (Hyperplane k n) ↦ True)
      (fun s ↦ (fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n)) : Set _)) := by
  classical
  refine (galoisPointwise_nhds_one_basis k₀ k).to_hasBasis
    (fun s _ ↦ ⟨s.image (coordinateFiber ⟨0, hn⟩), trivial, ?_⟩)
    (fun s _ ↦ ⟨s.biUnion hyperplaneCoefficientTests, trivial, ?_⟩)
  · rw [fixingCoordinateFibers_eq]
  · rw [fixingHyperplanes_eq_fixingCoefficients]

/-- The actual existing permutation of a finite stable arrangement's labels, packaged as
a group homomorphism. Its value is literally `galoisLabelEquiv`, not a new label action. -/
def galoisStagePermutation (A : StableArrangement k₀ k n) :
    (k ≃ₐ[k₀] k) →* Equiv.Perm A.val where
  toFun := galoisLabelEquiv A
  map_one' := by apply Equiv.ext; intro H; exact galoisLabelEquiv_one A H
  map_mul' σ τ := by apply Equiv.ext; intro H; exact galoisLabelEquiv_mul A σ τ H

/-- The stage permutation evaluates to the existing covariant label permutation.
This is a plain rewrite formula so that inverse-cancellation simp lemmas keep the same
equivalence on both sides of an application. -/
theorem galoisStagePermutation_apply (A : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (H : A.val) :
    galoisStagePermutation A σ H = galoisLabelEquiv A σ H := rfl

namespace CofinalSystem

variable (C : CofinalSystem k₀ k n)

/-- The kernel of the actual permutation representation on a selected stage. -/
def galoisStageKernel (A : C.Stage) : Subgroup (k ≃ₐ[k₀] k) :=
  (galoisStagePermutation A.val).ker

/-- A stage kernel fixes every geometric hyperplane occurring in that stage. -/
theorem mem_galoisStageKernel_iff (A : C.Stage) (σ : k ≃ₐ[k₀] k) :
    σ ∈ C.galoisStageKernel A ↔
      ∀ H : Hyperplane k n, H.val ∈ A.val.val → σ • H = H := by
  change galoisStagePermutation A.val σ = 1 ↔ _
  constructor
  · intro h H hH
    apply Subtype.ext
    change fieldAffineSubspace σ.toRingEquiv H.val = H.val
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨H.val, hH⟩)
  · intro h
    apply Equiv.ext
    intro H
    apply Subtype.ext
    change fieldAffineSubspace σ.toRingEquiv H.val = H.val
    exact congrArg (fun K : Hyperplane k n ↦ K.val)
      (h ⟨H.val, A.val.val.isHyperplane H.property⟩ H.property)

/-- Enlarging a stage shrinks its permutation kernel. -/
theorem galoisStageKernel_anti {A B : C.Stage} (h : A ≤ B) :
    C.galoisStageKernel B ≤ C.galoisStageKernel A := by
  intro σ hσ
  rw [C.mem_galoisStageKernel_iff] at hσ ⊢
  exact fun H hH ↦ hσ H (h hH)

private def stageHyperplanes (A : C.Stage) : Finset (Hyperplane k n) := by
  classical
  exact A.val.val.hyperplanes.attach.image
    (fun H ↦ (⟨H.val, A.val.val.isHyperplane H.property⟩ : Hyperplane k n))

private theorem mem_stageHyperplanes (A : C.Stage) (H : Hyperplane k n) :
    H ∈ C.stageHyperplanes A ↔ H.val ∈ A.val.val := by
  classical
  simp only [stageHyperplanes, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨K, rfl⟩
    exact K.property
  · intro hH
    exact ⟨⟨H.val, hH⟩, Subtype.ext rfl⟩

private theorem galoisStageKernel_eq_fixing (A : C.Stage) :
    C.galoisStageKernel A =
      fixingSubgroup (k ≃ₐ[k₀] k) (C.stageHyperplanes A : Set (Hyperplane k n)) := by
  ext σ
  simp only [C.mem_galoisStageKernel_iff, mem_fixingSubgroup_iff, Finset.mem_coe,
    C.mem_stageHyperplanes]

/-- Every actual finite-stage permutation kernel is clopen in the pointwise topology,
without any dimension restriction. -/
theorem galoisPointwise_isClopen_stageKernel (A : C.Stage) :
    @IsClopen (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k)
      (C.galoisStageKernel A : Set _) := by
  rw [C.galoisStageKernel_eq_fixing]
  exact galoisPointwise_isClopen_fixingHyperplanes _

/-- The actual stage permutation kernels form the pointwise identity basis. Cofinality is
the only property of the chosen family used here; union closure and algebraicity are absent.
Blueprint: T05 (`lem:t05`). -/
theorem galoisPointwise_nhds_one_stageKernelBasis (hn : 1 ≤ n) :
    (@nhds _ (galoisPointwiseTopology k₀ k) 1).HasBasis
      (fun _ : C.Stage ↦ True) (fun A ↦ (C.galoisStageKernel A : Set _)) := by
  classical
  refine (galoisPointwise_nhds_one_hyperplaneBasis (k₀ := k₀) (k := k) hn).to_hasBasis
    (fun s _ ↦ ?_) (fun A _ ↦ ⟨C.stageHyperplanes A, trivial, ?_⟩)
  · obtain ⟨A, hA⟩ := C.exists_stage_containing s
    refine ⟨A, trivial, ?_⟩
    intro σ hσ
    change σ ∈ fixingSubgroup (k ≃ₐ[k₀] k) (s : Set (Hyperplane k n))
    rw [mem_fixingSubgroup_iff]
    exact fun H hH ↦ (C.mem_galoisStageKernel_iff A σ).mp hσ H (hA H hH)
  · rw [C.galoisStageKernel_eq_fixing]

/-- A pointwise identity neighborhood contains the kernel of one selected stage. -/
theorem galoisPointwise_mem_nhds_one_iff_stageKernel (hn : 1 ≤ n)
    (U : Set (k ≃ₐ[k₀] k)) :
    U ∈ @nhds _ (galoisPointwiseTopology k₀ k) 1 ↔
      ∃ A : C.Stage, (C.galoisStageKernel A : Set _) ⊆ U := by
  simpa only [true_and] using (C.galoisPointwise_nhds_one_stageKernelBasis hn).mem_iff

/-- The topology induced by the tuple of actual complete stage permutations, each given
the discrete topology. No topology instance is installed on any permutation group. -/
@[instance_reducible]
def galoisStagePermutationTopology : TopologicalSpace (k ≃ₐ[k₀] k) :=
  TopologicalSpace.induced (fun (σ : k ≃ₐ[k₀] k) (A : C.Stage) ↦ galoisStagePermutation A.val σ)
    (@Pi.topologicalSpace C.Stage (fun A ↦ Equiv.Perm A.val.val) (fun _ ↦ ⊥))

/-- The defining tuple for the selected-stage topology consists of whole permutations. -/
theorem galoisStagePermutationTopology_eq_induced :
    C.galoisStagePermutationTopology =
      TopologicalSpace.induced (fun (σ : k ≃ₐ[k₀] k) (A : C.Stage) ↦ galoisStagePermutation A.val σ)
        (@Pi.topologicalSpace C.Stage (fun A ↦ Equiv.Perm A.val.val) (fun _ ↦ ⊥)) := rfl

/-- The named selected-stage topology is a group topology, also in dimension zero. -/
theorem galoisStagePermutationTopology_isTopologicalGroup :
    @IsTopologicalGroup (k ≃ₐ[k₀] k) C.galoisStagePermutationTopology _ := by
  let : (A : C.Stage) → TopologicalSpace (Equiv.Perm A.val.val) := fun _ ↦ ⊥
  let : (A : C.Stage) → DiscreteTopology (Equiv.Perm A.val.val) :=
    fun _ ↦ discreteTopology_bot _
  exact isTopologicalGroup_induced (MonoidHom.pi fun A : C.Stage ↦
    galoisStagePermutation A.val)

/-- Cofinality reduces finite intersections of permutation kernels to single larger-stage
kernels. This basis theorem does not require a positive dimension. -/
theorem galoisStagePermutationTopology_nhds_one_basis :
    (@nhds _ C.galoisStagePermutationTopology 1).HasBasis
      (fun _ : C.Stage ↦ True) (fun A ↦ (C.galoisStageKernel A : Set _)) := by
  classical
  let : (A : C.Stage) → TopologicalSpace (Equiv.Perm A.val.val) := fun _ ↦ ⊥
  let : (A : C.Stage) → DiscreteTopology (Equiv.Perm A.val.val) :=
    fun _ ↦ discreteTopology_bot _
  let := C.galoisStagePermutationTopology
  have hi : IsInducing (fun (σ : k ≃ₐ[k₀] k) (A : C.Stage) ↦
      galoisStagePermutation A.val σ) := ⟨rfl⟩
  have hs : (𝓝 (1 : k ≃ₐ[k₀] k)).HasBasis Set.Finite
      (fun s : Set C.Stage ↦ {σ | ∀ A ∈ s, σ ∈ C.galoisStageKernel A}) := by
    rw [hi.nhds_eq_comap, nhds_pi]
    simp_rw [map_one, nhds_discrete]
    exact (hasBasis_pi_pure (fun A : C.Stage ↦ (1 : Equiv.Perm A.val.val))).comap
      (fun (σ : k ≃ₐ[k₀] k) (A : C.Stage) ↦ galoisStagePermutation A.val σ)
  refine hs.to_hasBasis (fun s hs ↦ ?_) (fun A _ ↦ ⟨{A}, Set.finite_singleton A, ?_⟩)
  · obtain ⟨B, hB⟩ := C.exists_ge_finset hs.toFinset
    refine ⟨B, trivial, ?_⟩
    intro σ hσ A hA
    exact C.galoisStageKernel_anti (hB A (hs.mem_toFinset.mpr hA)) hσ
  · intro σ hσ
    exact hσ A (Set.mem_singleton A)

/-- The actual selected-stage permutation topology is precisely pointwise convergence when
one geometric coordinate exists. No algebraicity of the extension is assumed.
Blueprint: T05 (`lem:t05`). -/
theorem galoisStagePermutationTopology_eq_pointwise (hn : 1 ≤ n) :
    C.galoisStagePermutationTopology = galoisPointwiseTopology k₀ k := by
  apply C.galoisStagePermutationTopology_isTopologicalGroup.ext
    (galoisPointwise_isTopologicalGroup k₀ k)
  exact C.galoisStagePermutationTopology_nhds_one_basis.eq_of_same_basis
    (C.galoisPointwise_nhds_one_stageKernelBasis hn)

end CofinalSystem

end OrlikSolomon.HyperplaneGT
