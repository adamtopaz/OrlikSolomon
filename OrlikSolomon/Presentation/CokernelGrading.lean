/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Grading.LinearImage
public import OrlikSolomon.Presentation.Cokernel

/-!
# The bigrading of the deletion cokernel

The module cokernel of deletion inherits the image pieces of the Orlik–Solomon bigrading.
The homogeneous deletion map makes its range homogeneous, so these pieces have an internal
decomposition. The linear restriction lift has shift `(1,1)`, as is seen on coefficient
weighted generator words. Blueprint: `def:lift-map`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.OSAlgebra

universe u

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (𝒜 : Arrangement k V) (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ]
  (H : AffineSubspace k V)

/-- The image of deletion is closed under taking bigraded components. -/
theorem deletionRange_isHomogeneous :
    ((deletionRange B 𝒜 H).restrictScalars R).IsHomogeneous (bigrading 𝒜 ℬ) := by
  exact IsHomogeneousOfShift.isHomogeneous_range
    (f := (deletionMap B 𝒜 H).toLinearMap.restrictScalars R)
    (deletionMap_isHomogeneous 𝒜 ℬ H)

/-- The bigraded pieces of the module cokernel are the images of the pieces of the original
presentation. Blueprint: `def:lift-map`. -/
def cokernelGrading : ℤ × ℤ → Submodule R (DeletionCokernel B 𝒜 H) :=
  linearImageGrading (bigrading 𝒜 ℬ) ((cokernelMk B 𝒜 H).restrictScalars R)

/-- The cokernel pieces form an internal decomposition because the old image is homogeneous. -/
instance cokernelGradingDecomposition : DirectSum.Decomposition (cokernelGrading 𝒜 ℬ H) := by
  apply linearImageDecomposition (bigrading 𝒜 ℬ) ((cokernelMk B 𝒜 H).restrictScalars R)
    (cokernelMk_surjective B 𝒜 H)
  intro i x hx
  apply (cokernelMk_eq_zero_iff B 𝒜 H).2
  exact deletionRange_isHomogeneous 𝒜 ℬ H i
    ((cokernelMk_eq_zero_iff B 𝒜 H).1 hx)

omit [GradedAlgebra ℬ] in
/-- A cokernel component is represented by an element in the same bigraded piece. -/
theorem mem_cokernelGrading {i : ℤ × ℤ} {y : DeletionCokernel B 𝒜 H} :
    y ∈ cokernelGrading 𝒜 ℬ H i ↔
      ∃ x ∈ bigrading 𝒜 ℬ i, cokernelMk B 𝒜 H x = y :=
  mem_linearImageGrading

omit [GradedAlgebra ℬ] in
/-- The quotient map preserves bidegree. -/
theorem cokernelMk_mem_cokernelGrading {i : ℤ × ℤ} {x : OSAlgebra B 𝒜}
    (hx : x ∈ bigrading 𝒜 ℬ i) : cokernelMk B 𝒜 H x ∈ cokernelGrading 𝒜 ℬ H i :=
  map_mem_linearImageGrading hx

omit [GradedAlgebra ℬ] in
/-- The quotient map to the deletion cokernel is homogeneous of shift zero. -/
theorem cokernelMk_isHomogeneous :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) (cokernelGrading 𝒜 ℬ H) 0
      (cokernelMk B 𝒜 H) :=
  isHomogeneousOfShift_linearImageGrading _ _

/-- A bigraded component of a cokernel class is the class of that component of a representative. -/
@[simp]
theorem decompose_cokernelMk (x : OSAlgebra B 𝒜) (i : ℤ × ℤ) :
    (DirectSum.decompose (cokernelGrading 𝒜 ℬ H) (cokernelMk B 𝒜 H x) i :
        DeletionCokernel B 𝒜 H) =
      cokernelMk B 𝒜 H (DirectSum.decompose (bigrading 𝒜 ℬ) x i) := by
  let : DirectSum.Decomposition (linearImageGrading (bigrading 𝒜 ℬ)
      ((cokernelMk B 𝒜 H).restrictScalars R)) := cokernelGradingDecomposition 𝒜 ℬ H
  exact decompose_linearImageGrading _ _ x i

variable [FiniteDimensional k V] (H : 𝒜)

/-- Any representative choice gives a linear restriction map of bidegree `(1,1)`.
Blueprint: `def:lift-map`. -/
theorem restrictionToCokernelOfRepresentatives_isHomogeneous
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart (H : AffineSubspace k V)) = L) :
    IsHomogeneousOfShift (bigrading (𝒜.restriction H) ℬ) (cokernelGrading 𝒜 ℬ H) (1, 1)
      (restrictionToCokernelOfRepresentatives B 𝒜 H r hr) := by
  rintro ⟨p, w⟩ x hx
  by_cases hp : p < 0
  · have hx0 : x = 0 := by
      simpa only [bigrading_eq_bot_of_fst_neg (𝒜.restriction H) ℬ hp, Submodule.mem_bot] using hx
    subst x
    simp
  · lift p to ℕ using le_of_not_gt hp
    rw [bigrading_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, I, hI, rfl⟩ := hx
      rw [map_smul, restrictionToCokernelOfRepresentatives_word, ← map_smul]
      apply cokernelMk_mem_cokernelGrading 𝒜 ℬ H
      have hword : b • word (representativeGenerator B 𝒜 r) I ∈ bigrading 𝒜 ℬ (p, w) := by
        change b • word (fun L ↦ generator B 𝒜
          (Arrangement.inclusion (𝒜.deletion_le H) (r L))) I ∈ _
        have h := smul_coefficientMap_mem_bigrading 𝒜 ℬ hb
          (word_mem_degree R 𝒜 (I.map (Arrangement.inclusion (𝒜.deletion_le H) ∘ r)))
        rw [coefficientMap_word] at h
        simpa only [word_map, List.length_map, hI,
          sub_add_cancel, Function.comp_apply] using h
      simpa only [mul_smul_comm] using
        (isHomogeneousOfShift_mul_left (generator_mem_bigrading 𝒜 ℬ H)) hword
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      change ((restrictionToCokernelOfRepresentatives B 𝒜 H r hr).restrictScalars R) (a • x) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

/-- The canonical linear restriction lift has bidegree `(1,1)`.
Blueprint: `def:lift-map`. -/
theorem restrictionToCokernel_isHomogeneous :
    IsHomogeneousOfShift (bigrading (𝒜.restriction H) ℬ) (cokernelGrading 𝒜 ℬ H) (1, 1)
      (restrictionToCokernel B 𝒜 H) :=
  restrictionToCokernelOfRepresentatives_isHomogeneous 𝒜 ℬ H
    Arrangement.representative Arrangement.comap_representative

end OrlikSolomon.OSAlgebra
