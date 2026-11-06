/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Parallel
public import OrlikSolomon.Examples.Sanity
public import OrlikSolomon.Presentation.CokernelGrading

/-!
# Consumer regressions for the linear deletion cokernel

For a singleton arrangement the class of its generator is nonzero over any nonzero coefficient
ring. A map to the trivial square-zero extension detects it, independently of a basis theorem.
The unit, in contrast, has zero class. This distinguishes the module quotient from an ideal
quotient, which would vanish. Further calculations exercise empty old traces and degenerate
coefficient rings.

Blueprint: `lem:representatives`, `def:lift-map`, and the regression examples.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.PresentationExamples

variable {k : Type u} [Field k]

/-- The singleton arrangement consisting of the origin in the affine line. -/
def singlePoint (k : Type u) [Field k] : Arrangement k k := by
  classical
  exact Arrangement.ofFinset {pointHyperplane (0 : k)}

@[simp]
theorem mem_singlePoint (H : AffineSubspace k k) :
    H ∈ singlePoint k ↔ H = pointHyperplane 0 := by
  classical
  simp only [singlePoint, Arrangement.mem_ofFinset, Finset.mem_singleton,
    and_iff_left_iff_imp]
  rintro rfl
  exact isHyperplane_pointHyperplane _

/-- The unique generator label of the singleton arrangement. -/
def singlePointLabel (k : Type u) [Field k] : singlePoint k :=
  ⟨pointHyperplane 0, (mem_singlePoint _).2 rfl⟩

instance : Subsingleton (singlePoint k) :=
  ⟨fun H K ↦ Subtype.ext (((mem_singlePoint _).1 H.2).trans ((mem_singlePoint _).1 K.2).symm)⟩

instance : IsEmpty ((singlePoint k).deletion (singlePointLabel k)) :=
  ⟨fun K ↦ (Arrangement.mem_deletion.1 K.2).1
    (((mem_singlePoint _).1 (Arrangement.mem_deletion.1 K.2).2))⟩

private theorem isFamily_singlePointDetector (B : Type v) [CommRing B] :
    OSAlgebra.IsFamily (singlePoint k) (fun _ ↦ (TrivSqZeroExt.inr 1 : TrivSqZeroExt B B)) where
  mul_self _ := by simp
  mul_add_mul_swap_of_ne _ := by simp
  word_eq_zero I _ hI := by
    cases I with
    | nil => simp at hI
    | cons H I =>
      cases I with
      | nil => exact ((singlePoint k).isHyperplane H.2).ne_bot (by simpa using hI) |>.elim
      | cons K I => simp [word_cons, ← mul_assoc]
  wordBoundary_eq_zero I hI hdep := by
    cases I with
    | nil => exact (Arrangement.isDependent_nil _ hdep).elim
    | cons H I =>
      cases I with
      | nil =>
        have h := hdep.2
        simp [Arrangement.inter_cons, ((singlePoint k).isHyperplane H.2).codim_eq_one] at h
      | cons K I =>
        exact ((List.nodup_cons.1 hI).1 (by simp [Subsingleton.elim H K])).elim

private def singlePointDetector (B : Type v) [CommRing B] :
    OSAlgebra B (singlePoint k) →ₐ[B] TrivSqZeroExt B B :=
  OSAlgebra.lift _ (isFamily_singlePointDetector B)

private def singlePointCoefficient (B : Type v) [CommRing B] :
    OSAlgebra B (singlePoint k) →ₗ[B] B :=
  (TrivSqZeroExt.sndHom B B).comp (singlePointDetector B).toLinearMap

private theorem singlePointCoefficient_deletionMap (B : Type v) [CommRing B]
    (x : OSAlgebra B ((singlePoint k).deletion (singlePointLabel k))) :
    singlePointCoefficient B (OSAlgebra.deletionMap B (singlePoint k) (singlePointLabel k) x) =
      0 := by
  have h : (singlePointCoefficient B).comp
      (OSAlgebra.deletionMap B (singlePoint k) (singlePointLabel k)).toLinearMap = 0 := by
    apply OSAlgebra.linearMap_ext
    intro I
    cases I with
    | nil => simp [singlePointCoefficient, singlePointDetector]
    | cons K I => exact isEmptyElim K
  exact LinearMap.congr_fun h x

/-- The class of the deleted generator is nonzero in the module cokernel of a singleton
arrangement. It would vanish in the ideal quotient because the old image contains the unit. -/
theorem singlePoint_cokernel_generator_ne_zero (B : Type v) [CommRing B] [Nontrivial B] :
    OSAlgebra.cokernelMk B (singlePoint k) (singlePointLabel k)
      (OSAlgebra.generator B (singlePoint k) (singlePointLabel k)) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := (OSAlgebra.cokernelMk_eq_zero_iff B (singlePoint k) (singlePointLabel k)).1 h
  have h' := congrArg (singlePointCoefficient B) hx
  change singlePointCoefficient B
      (OSAlgebra.deletionMap B (singlePoint k) (singlePointLabel k) x) = _ at h'
  rw [singlePointCoefficient_deletionMap] at h'
  simp [singlePointCoefficient, singlePointDetector, OSAlgebra.lift_generator] at h'

/-- The actual restriction map takes the empty word to the surviving deleted-generator class. -/
theorem singlePoint_restriction_one (B : Type v) [CommRing B] :
    OSAlgebra.restrictionToCokernel B (singlePoint k) (singlePointLabel k) 1 =
      OSAlgebra.cokernelMk B (singlePoint k) (singlePointLabel k)
        (OSAlgebra.generator B (singlePoint k) (singlePointLabel k)) := by
  simpa only [word_nil, mul_one] using
    OSAlgebra.restrictionToCokernel_word B (singlePoint k) (singlePointLabel k) []

/-- The linear restriction lift is nonzero for the singleton arrangement over any nonzero ring. -/
theorem singlePoint_restriction_one_ne_zero (B : Type v) [CommRing B] [Nontrivial B] :
    OSAlgebra.restrictionToCokernel B (singlePoint k) (singlePointLabel k) 1 ≠ 0 := by
  rw [singlePoint_restriction_one]
  exact singlePoint_cokernel_generator_ne_zero B

/-- The surviving cokernel class remains nonzero in characteristic two, even over the finite
base field with two elements. -/
theorem singlePoint_restriction_one_zmod_two :
    OSAlgebra.restrictionToCokernel (ZMod 2) (singlePoint (ZMod 2))
      (singlePointLabel (ZMod 2)) 1 ≠ 0 :=
  singlePoint_restriction_one_ne_zero (ZMod 2)

/-- Zero coefficients give the zero cokernel map, with no nontriviality assumption on the API. -/
theorem singlePoint_restriction_one_zmod_one :
    OSAlgebra.restrictionToCokernel (ZMod 1) (singlePoint k) (singlePointLabel k) 1 = 0 :=
  (Module.subsingleton (ZMod 1) _).elim _ _

/-- The other point has empty trace on the deleted point, over every field. -/
theorem twoPoints_other_trace_eq_bot :
    (onePoint k : AffineSubspace k k).comap (chart (zeroPoint k : AffineSubspace k k)) = ⊥ :=
  (comap_chart_eq_bot_iff ((twoPoints k).isHyperplane (zeroPoint k).2).ne_bot).2
    (pointHyperplane_inf_eq_bot zero_ne_one)

/-- Deleting either point leaves no retained hyperplane on that point. The old hyperplane is
discarded because its trace is empty. -/
theorem twoPoints_restriction_eq_empty : (twoPoints k).restriction (zeroPoint k) = ∅ := by
  apply Arrangement.ext
  intro L
  constructor
  · intro hL
    obtain ⟨K, hK, hmeet, _⟩ :=
      (Arrangement.mem_restriction ((twoPoints k).isHyperplane (zeroPoint k).2)).1 hL
    have hdel := Arrangement.mem_deletion.1 hK
    rcases (mem_twoPoints K).1 hdel.2 with hzero | hone
    · exact (hdel.1 hzero).elim
    · exact (hmeet (by rw [hone]; exact pointHyperplane_inf_eq_bot zero_ne_one)).elim
  · intro hL
    exact (Arrangement.notMem_empty L hL).elim

/-- The product involving the discarded old trace is already zero before taking its cokernel
class. This is the empty-trace branch used in the linear restriction lift. -/
theorem twoPoints_empty_trace_cokernel (B : Type v) [CommRing B] :
    OSAlgebra.cokernelMk B (twoPoints k) (zeroPoint k)
      (OSAlgebra.generator B (twoPoints k) (zeroPoint k) *
        OSAlgebra.generator B (twoPoints k) (onePoint k)) = 0 := by
  let K : (twoPoints k).deletion (zeroPoint k) :=
    ⟨onePoint k, Arrangement.mem_deletion.2
      ⟨fun h ↦ zeroPoint_ne_onePoint (Subtype.ext h.symm), (onePoint k).2⟩⟩
  have hK : Arrangement.inclusion ((twoPoints k).deletion_le (zeroPoint k)) K =
      onePoint k := Subtype.ext rfl
  simpa only [List.nil_append, word_cons, word_nil, mul_one, OSAlgebra.oldGenerator, hK] using
    OSAlgebra.cokernelMk_generator_word_eq_zero_of_empty_trace B (twoPoints k)
      (zeroPoint k) [] [] K twoPoints_other_trace_eq_bot

/-- The horizontal coordinate line in the affine plane. -/
def horizontalZero (k : Type u) [Field k] : AffineSubspace k (k × k) :=
  zeroLocus (LinearMap.snd k k k).toAffineMap

@[simp]
theorem mem_horizontalZero (p : k × k) : p ∈ horizontalZero k ↔ p.2 = 0 := by
  simp [horizontalZero]

private theorem isHyperplane_horizontalZero : IsHyperplane (horizontalZero k) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have := congrArg (fun f : (k × k) →ₗ[k] k ↦ f (0, 1)) h
  simp at this

/-- The diagonal line in the affine plane, also in characteristic two. -/
def diagonalZero (k : Type u) [Field k] : AffineSubspace k (k × k) :=
  zeroLocus ((LinearMap.fst k k k - LinearMap.snd k k k).toAffineMap)

@[simp]
theorem mem_diagonalZero (p : k × k) : p ∈ diagonalZero k ↔ p.1 = p.2 := by
  simp [diagonalZero, sub_eq_zero]

private theorem isHyperplane_diagonalZero : IsHyperplane (diagonalZero k) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have := congrArg (fun f : (k × k) →ₗ[k] k ↦ f (1, 0)) h
  simp at this

/-- Three distinct concurrent lines, whose two old lines give the same trace on `x = 0`. -/
def threeConcurrent (k : Type u) [Field k] : Arrangement k (k × k) := by
  classical
  exact Arrangement.ofFinset {verticalLine (0 : k), horizontalZero k, diagonalZero k}

@[simp]
theorem mem_threeConcurrent (L : AffineSubspace k (k × k)) :
    L ∈ threeConcurrent k ↔
      L = verticalLine 0 ∨ L = horizontalZero k ∨ L = diagonalZero k := by
  classical
  simp only [threeConcurrent, Arrangement.mem_ofFinset, Finset.mem_insert,
    Finset.mem_singleton, and_iff_left_iff_imp]
  rintro (rfl | rfl | rfl)
  · exact isHyperplane_verticalLine _
  · exact isHyperplane_horizontalZero
  · exact isHyperplane_diagonalZero

/-- The deleted vertical line of the concurrent arrangement. -/
def concurrentBase (k : Type u) [Field k] : threeConcurrent k :=
  ⟨verticalLine 0, (mem_threeConcurrent _).2 (Or.inl rfl)⟩

/-- The horizontal old representative. -/
def concurrentHorizontal (k : Type u) [Field k] :
    (threeConcurrent k).deletion (concurrentBase k) := by
  refine ⟨horizontalZero k, Arrangement.mem_deletion.2 ⟨?_, ?_⟩⟩
  · intro h
    have h' := congrArg (fun L : AffineSubspace k (k × k) ↦ (1, 0) ∈ L) h
    simp [concurrentBase] at h'
  · exact (mem_threeConcurrent _).2 (Or.inr (Or.inl rfl))

/-- The diagonal old representative, distinct from the horizontal line. -/
def concurrentDiagonal (k : Type u) [Field k] :
    (threeConcurrent k).deletion (concurrentBase k) := by
  refine ⟨diagonalZero k, Arrangement.mem_deletion.2 ⟨?_, ?_⟩⟩
  · intro h
    have h' := congrArg (fun L : AffineSubspace k (k × k) ↦ (1, 1) ∈ L) h
    simp [concurrentBase] at h'
  · exact (mem_threeConcurrent _).2 (Or.inr (Or.inr rfl))

/-- The horizontal and diagonal lines are genuinely different old representatives. -/
theorem concurrentHorizontal_ne_concurrentDiagonal :
    concurrentHorizontal k ≠ concurrentDiagonal k := by
  intro h
  have h' := congrArg
    (fun K : (threeConcurrent k).deletion (concurrentBase k) ↦
      ((1 : k), (0 : k)) ∈ (K : AffineSubspace k (k × k))) h
  simp [concurrentHorizontal, concurrentDiagonal] at h'

private theorem concurrent_trace_eq :
    (concurrentHorizontal k : AffineSubspace k (k × k)).comap
        (chart (concurrentBase k : AffineSubspace k (k × k))) =
      (concurrentDiagonal k : AffineSubspace k (k × k)).comap
        (chart (concurrentBase k : AffineSubspace k (k × k))) := by
  apply (comap_chart_eq_comap_chart_iff
    ((threeConcurrent k).isHyperplane (concurrentBase k).2).ne_bot).2
  ext p
  simp only [concurrentBase, concurrentHorizontal, concurrentDiagonal,
    AffineSubspace.mem_inf_iff, mem_verticalLine, mem_horizontalZero, mem_diagonalZero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.trans h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.symm.trans h1⟩

/-- The common old trace contains the origin and is retained by restriction. -/
theorem concurrent_trace_ne_bot :
    (concurrentHorizontal k : AffineSubspace k (k × k)).comap
      (chart (concurrentBase k : AffineSubspace k (k × k))) ≠ ⊥ := by
  apply (comap_chart_eq_bot_iff
    ((threeConcurrent k).isHyperplane (concurrentBase k).2).ne_bot).not.mpr
  apply (AffineSubspace.nonempty_iff_ne_bot _).1
  exact ⟨(0, 0), by simp [concurrentBase, concurrentHorizontal]⟩

/-- The common retained trace of the horizontal and diagonal old lines. -/
def concurrentTrace (k : Type u) [Field k] :
    (threeConcurrent k).restriction (concurrentBase k) :=
  ⟨(concurrentHorizontal k : AffineSubspace k (k × k)).comap
      (chart (concurrentBase k : AffineSubspace k (k × k))),
    Arrangement.comap_chart_mem_restriction
      ((threeConcurrent k).isHyperplane (concurrentBase k).2) (concurrentHorizontal k).2
      ((comap_chart_eq_bot_iff
        ((threeConcurrent k).isHyperplane (concurrentBase k).2).ne_bot).not.mp
          concurrent_trace_ne_bot)⟩

private theorem concurrent_restriction_label_eq
    (L : (threeConcurrent k).restriction (concurrentBase k)) : L = concurrentTrace k := by
  apply Subtype.ext
  obtain ⟨K, hK, _, hKL⟩ := (Arrangement.mem_restriction
    ((threeConcurrent k).isHyperplane (concurrentBase k).2)).1 L.2
  rw [← hKL]
  have hdel := Arrangement.mem_deletion.1 hK
  rcases (mem_threeConcurrent K).1 hdel.2 with hbase | hhorizontal | hdiagonal
  · exact (hdel.1 hbase).elim
  · rw [hhorizontal]
    rfl
  · rw [hdiagonal]
    exact concurrent_trace_eq.symm

/-- Choose the horizontal line for the unique retained trace. -/
def concurrentHorizontalRepresentatives (k : Type u) [Field k] :
    (threeConcurrent k).restriction (concurrentBase k) →
      (threeConcurrent k).deletion (concurrentBase k) := fun _ ↦ concurrentHorizontal k

/-- Choose the diagonal line for the same retained trace. -/
def concurrentDiagonalRepresentatives (k : Type u) [Field k] :
    (threeConcurrent k).restriction (concurrentBase k) →
      (threeConcurrent k).deletion (concurrentBase k) := fun _ ↦ concurrentDiagonal k

/-- The horizontal choice has the prescribed trace for every retained label. -/
theorem comap_concurrentHorizontalRepresentatives
    (L : (threeConcurrent k).restriction (concurrentBase k)) :
    (concurrentHorizontalRepresentatives k L : AffineSubspace k (k × k)).comap
      (chart (concurrentBase k : AffineSubspace k (k × k))) = L := by
  rw [concurrent_restriction_label_eq L]
  rfl

/-- The diagonal choice has the same prescribed trace for every retained label. -/
theorem comap_concurrentDiagonalRepresentatives
    (L : (threeConcurrent k).restriction (concurrentBase k)) :
    (concurrentDiagonalRepresentatives k L : AffineSubspace k (k × k)).comap
      (chart (concurrentBase k : AffineSubspace k (k × k))) = L := by
  rw [concurrent_restriction_label_eq L]
  exact concurrent_trace_eq.symm

/-- The full linear maps agree for the two distinct choices in the concurrent arrangement. -/
theorem concurrent_restriction_maps_eq (B : Type v) [CommRing B] :
    OSAlgebra.restrictionToCokernelOfRepresentatives B (threeConcurrent k) (concurrentBase k)
        (concurrentHorizontalRepresentatives k) comap_concurrentHorizontalRepresentatives =
      OSAlgebra.restrictionToCokernelOfRepresentatives B (threeConcurrent k) (concurrentBase k)
        (concurrentDiagonalRepresentatives k) comap_concurrentDiagonalRepresentatives :=
  OSAlgebra.restrictionToCokernelOfRepresentatives_eq B (threeConcurrent k) (concurrentBase k)
    _ _ comap_concurrentHorizontalRepresentatives comap_concurrentDiagonalRepresentatives

/-- The actual linear lifts on the common trace agree for two distinct old representative
choices. Duplicate traces do not create duplicate generators in the restriction. -/
theorem concurrent_representative_independence (B : Type v) [CommRing B] :
    OSAlgebra.restrictionToCokernelOfRepresentatives B (threeConcurrent k) (concurrentBase k)
        (concurrentHorizontalRepresentatives k) comap_concurrentHorizontalRepresentatives
        (OSAlgebra.generator B _ (concurrentTrace k)) =
      OSAlgebra.restrictionToCokernelOfRepresentatives B (threeConcurrent k) (concurrentBase k)
        (concurrentDiagonalRepresentatives k) comap_concurrentDiagonalRepresentatives
        (OSAlgebra.generator B _ (concurrentTrace k)) := by
  have h1 := OSAlgebra.restrictionToCokernelOfRepresentatives_word B (threeConcurrent k)
    (concurrentBase k) (concurrentHorizontalRepresentatives k)
    comap_concurrentHorizontalRepresentatives [concurrentTrace k]
  have h2 := OSAlgebra.restrictionToCokernelOfRepresentatives_word B (threeConcurrent k)
    (concurrentBase k) (concurrentDiagonalRepresentatives k)
    comap_concurrentDiagonalRepresentatives [concurrentTrace k]
  simp only [word_singleton] at h1 h2
  rw [h1, h2]
  apply (OSAlgebra.cokernelMk_eq_iff B (threeConcurrent k) (concurrentBase k)).2
  rw [OSAlgebra.representativeGenerator, OSAlgebra.representativeGenerator,
    concurrentHorizontalRepresentatives, concurrentDiagonalRepresentatives,
    OSAlgebra.generator_mul_sub_generator_mul_of_same_trace B (threeConcurrent k)
      (concurrentBase k) (concurrentHorizontal k) (concurrentDiagonal k)
      concurrent_trace_eq concurrent_trace_ne_bot]
  exact (OSAlgebra.deletionRange B (threeConcurrent k) (concurrentBase k)).neg_mem
    (OSAlgebra.mul_mem_deletionRange B (threeConcurrent k) (concurrentBase k)
      (OSAlgebra.generator_mem_deletionRange B (threeConcurrent k) (concurrentHorizontal k))
      (OSAlgebra.generator_mem_deletionRange B (threeConcurrent k) (concurrentDiagonal k)))

/-- The shifted `(0,0) → (1,1)` component of the singleton lift with characteristic-two
Laurent coefficients. Both source and target retain the actual quotient's scalar structures. -/
def singlePointComponentZModTwo :
    OSAlgebra.bigrading ((singlePoint (ZMod 2)).restriction (singlePointLabel (ZMod 2)))
        (Sanity.laurentWeight (ZMod 2)) (0, 0) →ₗ[ZMod 2]
      OSAlgebra.cokernelGrading (singlePoint (ZMod 2)) (Sanity.laurentWeight (ZMod 2))
        (singlePointLabel (ZMod 2)) (1, 1) :=
  (OSAlgebra.restrictionToCokernel_isHomogeneous (singlePoint (ZMod 2))
    (Sanity.laurentWeight (ZMod 2)) (singlePointLabel (ZMod 2))).component rfl

/-- The characteristic-two component map is genuinely nonzero: it sends the homogeneous unit
to the nonzero class of the deleted generator. -/
theorem singlePointComponentZModTwo_ne_zero : singlePointComponentZModTwo ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h
    ⟨1, SetLike.one_mem_graded (OSAlgebra.bigrading
      ((singlePoint (ZMod 2)).restriction (singlePointLabel (ZMod 2)))
      (Sanity.laurentWeight (ZMod 2)))⟩
  have hv := congrArg Subtype.val h'
  change OSAlgebra.restrictionToCokernel (LaurentPolynomial (ZMod 2))
    (singlePoint (ZMod 2)) (singlePointLabel (ZMod 2)) 1 = 0 at hv
  exact singlePoint_restriction_one_ne_zero (LaurentPolynomial (ZMod 2)) hv

/-- The same component API elaborates when both scalar rings are the zero ring in the same
universe; every shifted component is zero. -/
theorem singlePoint_component_zero (i : ℤ × ℤ) :
    (OSAlgebra.restrictionToCokernel_isHomogeneous (singlePoint k)
      Sanity.zeroWeight.{0, 0} (singlePointLabel k)).component
        (i := i) (j := i + (1, 1)) rfl = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (Module.subsingleton PUnit _).elim _ _

end OrlikSolomon.PresentationExamples
