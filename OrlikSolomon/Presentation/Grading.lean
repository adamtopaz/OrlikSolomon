/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Grading.Basic
public import OrlikSolomon.Grading.TensorProduct
public import OrlikSolomon.Presentation.BaseChange

/-!
# The weighted internal bigrading of the affine presentation

For a weight-graded coefficient algebra `B` over `R`, `OSAlgebra.bigrading` is an internal
grading by `ℤ × ℤ` whose pieces are `R`-submodules. A coefficient of weight `w` has bidegree
`(0, w)` and a hyperplane generator has bidegree `(1, 1)`.

The construction transports the weighted tensor grading along the canonical coefficient
base-change equivalence. `bigradingComponentEquiv` identifies the `(n, w)` piece with the
tensor product of exterior degree `n` over `R` and coefficient weight `w - n`.
Inclusion and deletion maps preserve the bigrading.

Blueprint: the weighted grading and components in `lem:os-basic`.
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (𝒜 : Arrangement k V) (ℬ : ℤ → Submodule R B)

/-- The affine presentation's internal bigrading over `R`, with exterior generators in bidegree
`(1, 1)` and coefficient weight `w` in bidegree `(0, w)`.

Blueprint: `lem:os-basic`. -/
def bigrading : ℤ × ℤ → Submodule R (OSAlgebra B 𝒜) :=
  transportGrading (weightedTensorGrading ℬ (degree R 𝒜))
    ((baseChangeEquiv R B 𝒜).restrictScalars R).toLinearEquiv

/-- Membership in the bigrading can be checked before coefficient base change. -/
theorem mem_bigrading_iff {i : ℤ × ℤ} {x : OSAlgebra B 𝒜} :
    x ∈ bigrading 𝒜 ℬ i ↔
      (baseChangeEquiv R B 𝒜).symm x ∈ weightedTensorGrading ℬ (degree R 𝒜) i :=
  mem_transportGrading_iff _ _

@[simp]
theorem baseChangeEquiv_mem_bigrading_iff {i : ℤ × ℤ} {x : B ⊗[R] OSAlgebra R 𝒜} :
    baseChangeEquiv R B 𝒜 x ∈ bigrading 𝒜 ℬ i ↔
      x ∈ weightedTensorGrading ℬ (degree R 𝒜) i :=
  apply_mem_transportGrading_iff _ _

variable [GradedAlgebra ℬ]

instance bigradingGradedAlgebra : GradedAlgebra (bigrading 𝒜 ℬ) :=
  inferInstanceAs (GradedAlgebra (transportGrading (weightedTensorGrading ℬ (degree R 𝒜))
    ((baseChangeEquiv R B 𝒜).restrictScalars R).toLinearEquiv))

omit [GradedAlgebra ℬ] in
/-- Coefficients of weight `w` have bidegree `(0, w)`. -/
theorem algebraMap_mem_bigrading {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (OSAlgebra B 𝒜) b ∈ bigrading 𝒜 ℬ (0, w) := by
  have h := (baseChangeEquiv_mem_bigrading_iff 𝒜 ℬ).2
    (tmul_one_mem_weightedTensorGrading ℬ (degree R 𝒜) hb)
  simpa only [baseChangeEquiv_tmul, map_one, Algebra.algebraMap_eq_smul_one] using h

/-- Coefficient extension sends exterior degree `n` over `R` to bidegree `(n, n)`. -/
theorem coefficientMap_mem_bigrading {n : ℕ} {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 n) :
    coefficientMap R B 𝒜 x ∈ bigrading 𝒜 ℬ (n, n) := by
  have h := (baseChangeEquiv_mem_bigrading_iff 𝒜 ℬ).2
    (one_tmul_mem_weightedTensorGrading ℬ (degree R 𝒜) hx)
  simpa only [baseChangeEquiv_tmul, one_smul] using h

/-- Each hyperplane generator has bidegree `(1, 1)`. -/
theorem generator_mem_bigrading (H : 𝒜) : generator B 𝒜 H ∈ bigrading 𝒜 ℬ (1, 1) := by
  simpa only [coefficientMap_generator, Nat.cast_one] using
    coefficientMap_mem_bigrading 𝒜 ℬ (generator_mem_degree R 𝒜 H)

/-- A generator word has diagonal bidegree given by its length. -/
theorem word_mem_bigrading (I : List 𝒜) :
    word (generator B 𝒜) I ∈ bigrading 𝒜 ℬ (I.length, I.length) := by
  simpa only [coefficientMap_word] using
    coefficientMap_mem_bigrading 𝒜 ℬ (word_mem_degree R 𝒜 I)

/-- A signed boundary has diagonal bidegree one less than its word. -/
theorem wordBoundary_mem_bigrading (I : List 𝒜) :
    wordBoundary (generator B 𝒜) I ∈ bigrading 𝒜 ℬ
      (((I.length - 1 : ℕ) : ℤ), ((I.length - 1 : ℕ) : ℤ)) := by
  simpa only [map_wordBoundary, coefficientMap_generator] using
    coefficientMap_mem_bigrading 𝒜 ℬ (wordBoundary_mem_degree R 𝒜 I)

omit [GradedAlgebra ℬ] in
/-- Multiplication by a coefficient of weight `w` shifts the weight of a degree `n` element
to `w + n`. -/
theorem smul_coefficientMap_mem_bigrading {w : ℤ} {n : ℕ} {b : B} {x : OSAlgebra R 𝒜}
    (hb : b ∈ ℬ w) (hx : x ∈ degree R 𝒜 n) :
    b • coefficientMap R B 𝒜 x ∈ bigrading 𝒜 ℬ (n, w + n) := by
  exact (baseChangeEquiv_mem_bigrading_iff 𝒜 ℬ).2
    (tmul_mem_weightedTensorGrading ℬ (degree R 𝒜) hb hx)

omit [GradedAlgebra ℬ] in
/-- A bigraded piece is spanned over `R` by words of the prescribed length with coefficients
of the complementary weight. This gives an induction principle for homogeneous linear maps.

Blueprint: the component description in `lem:os-basic`. -/
theorem bigrading_eq_span (n : ℕ) (w : ℤ) :
    bigrading 𝒜 ℬ (n, w) = Submodule.span R
      {y | ∃ b ∈ ℬ (w - n), ∃ I : List 𝒜, I.length = n ∧
        y = b • word (generator B 𝒜) I} := by
  let N := Submodule.span R
    {y | ∃ b ∈ ℬ (w - n), ∃ I : List 𝒜, I.length = n ∧
      y = b • word (generator B 𝒜) I}
  have hword (b : B) (hb : b ∈ ℬ (w - n)) :
      degree R 𝒜 n ≤ N.comap (b • (coefficientMap R B 𝒜).toLinearMap) := by
    rw [← span_word_length, Submodule.span_le]
    rintro _ ⟨I, hI, rfl⟩
    change b • coefficientMap R B 𝒜 (word (generator R 𝒜) I) ∈ N
    rw [coefficientMap_word]
    exact Submodule.subset_span ⟨b, hb, I, hI, rfl⟩
  change (weightedTensorGrading ℬ (degree R 𝒜) (n, w)).map _ = N
  rw [weightedTensorGrading_apply', tensorProductGrading_eq_span, Submodule.map_span]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨b, hb, a, ha, rfl⟩, rfl⟩
    change baseChangeEquiv R B 𝒜 (b ⊗ₜ[R] a) ∈ N
    rw [baseChangeEquiv_tmul]
    exact hword b hb ha
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, I, rfl, rfl⟩
    apply Submodule.subset_span
    refine ⟨b ⊗ₜ[R] word (generator R 𝒜) I, ?_, ?_⟩
    · refine ⟨b, hb, word (generator R 𝒜) I, word_mem_degree R 𝒜 I, rfl⟩
    · exact (baseChangeEquiv_tmul R B 𝒜 b _).trans
        (congrArg (b • ·) (coefficientMap_word R B 𝒜 I))

omit [GradedAlgebra ℬ] in
/-- There is no negative cohomological degree in the affine presentation. -/
theorem bigrading_eq_bot_of_fst_neg {p w : ℤ} (hp : p < 0) :
    bigrading 𝒜 ℬ (p, w) = ⊥ := by
  change (weightedTensorGrading ℬ (degree R 𝒜) (p, w)).map _ = ⊥
  rw [weightedTensorGrading_eq_bot_of_fst_neg ℬ (degree R 𝒜) hp, Submodule.map_bot]

omit [GradedAlgebra ℬ] in
/-- Forgetting the coefficient weight leaves the ordinary exterior degree. -/
theorem mem_degree_of_mem_bigrading {n : ℕ} {w : ℤ} {x : OSAlgebra B 𝒜}
    (hx : x ∈ bigrading 𝒜 ℬ (n, w)) : x ∈ degree B 𝒜 n := by
  rw [mem_bigrading_iff] at hx
  have h : weightedTensorGrading ℬ (degree R 𝒜) (n, w) ≤
      ((degree B 𝒜 n).restrictScalars R).comap
        ((baseChangeEquiv R B 𝒜).restrictScalars R).toLinearMap := by
    rw [weightedTensorGrading_apply', tensorProductGrading_eq_span, Submodule.span_le]
    rintro _ ⟨b, _, a, ha, rfl⟩
    change baseChangeEquiv R B 𝒜 (b ⊗ₜ[R] a) ∈ degree B 𝒜 n
    rw [baseChangeEquiv_tmul]
    exact Submodule.smul_mem _ b (coefficientMap_mem_degree R B 𝒜 ha)
  have h' := h hx
  change baseChangeEquiv R B 𝒜 ((baseChangeEquiv R B 𝒜).symm x) ∈ degree B 𝒜 n at h'
  simpa only [AlgEquiv.apply_symm_apply] using h'

omit [GradedAlgebra ℬ] in
/-- The weighted affine presentation is graded commutative, with sign determined only by
cohomological degree. No invertibility assumption on two is used. -/
theorem isGradedCommutative_bigrading : IsGradedCommutative (bigrading 𝒜 ℬ) Prod.fst := by
  rintro ⟨p, w⟩ ⟨q, v⟩ x y hx hy
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · lift p to ℕ using hp
      lift q to ℕ using hq
      exact mul_comm_of_mem_degree B 𝒜
        (mem_degree_of_mem_bigrading 𝒜 ℬ hx) (mem_degree_of_mem_bigrading 𝒜 ℬ hy)
    · have hy0 : y = 0 := by
        simpa only [bigrading_eq_bot_of_fst_neg 𝒜 ℬ (lt_of_not_ge hq), Submodule.mem_bot] using hy
      simp [hy0]
  · have hx0 : x = 0 := by
      simpa only [bigrading_eq_bot_of_fst_neg 𝒜 ℬ (lt_of_not_ge hp), Submodule.mem_bot] using hx
    simp [hx0]

/-- The component of bidegree `(n, w)` is exterior degree `n` over `R`, tensored with coefficient
weight `w - n`. This statement includes the zero coefficient ring and needs no flatness.

Blueprint: the component formula in `lem:os-basic`. -/
def bigradingComponentEquiv (n : ℕ) (w : ℤ) :
    (degree R 𝒜 n) ⊗[R] (ℬ (w - n)) ≃ₗ[R] bigrading 𝒜 ℬ (n, w) :=
  TensorProduct.comm R _ _ ≪≫ₗ
    weightedTensorComponentEquiv ℬ (degree R 𝒜) n w ≪≫ₗ
    transportGradingEquiv (weightedTensorGrading ℬ (degree R 𝒜))
      ((baseChangeEquiv R B 𝒜).restrictScalars R).toLinearEquiv (n, w)

@[simp]
theorem coe_bigradingComponentEquiv_tmul (n : ℕ) (w : ℤ)
    (x : degree R 𝒜 n) (b : ℬ (w - n)) :
    (bigradingComponentEquiv 𝒜 ℬ n w (x ⊗ₜ[R] b) : OSAlgebra B 𝒜) =
      (b : B) • coefficientMap R B 𝒜 x := by
  change baseChangeEquiv R B 𝒜
    (weightedTensorComponentEquiv ℬ (degree R 𝒜) n w
      (TensorProduct.comm R _ _ (x ⊗ₜ[R] b))) = _
  rw [TensorProduct.comm_tmul, coe_weightedTensorComponentEquiv, TensorProduct.map_tmul]
  exact baseChangeEquiv_tmul R B 𝒜 b x

omit [GradedAlgebra ℬ] in
/-- Inclusions of arrangements preserve the weighted bigrading. -/
theorem map_mem_bigrading {𝒟 : Arrangement k V} (h : 𝒜 ≤ 𝒟) {i : ℤ × ℤ}
    {x : OSAlgebra B 𝒜} (hx : x ∈ bigrading 𝒜 ℬ i) :
    map B h x ∈ bigrading 𝒟 ℬ i := by
  rw [mem_bigrading_iff] at hx
  have ht := map_mem_weightedTensorGrading ℬ (degree R 𝒜) ℬ (degree R 𝒟)
    (LinearMap.id : B →ₗ[R] B) (map R h).toLinearMap
    (fun _ _ hb ↦ hb) (fun _ _ ha ↦ map_mem_degree R 𝒜 h ha) hx
  have he := map_baseChangeEquiv R B 𝒜 h ((baseChangeEquiv R B 𝒜).symm x)
  rw [AlgEquiv.apply_symm_apply] at he
  rw [he]
  exact (baseChangeEquiv_mem_bigrading_iff 𝒟 ℬ).2 ht

omit [GradedAlgebra ℬ] in
/-- The inclusion algebra map is homogeneous of shift zero. -/
theorem map_isHomogeneous {𝒟 : Arrangement k V} (h : 𝒜 ≤ 𝒟) :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) (bigrading 𝒟 ℬ) 0 (map B h) := by
  intro i x hx
  simpa only [add_zero] using map_mem_bigrading 𝒜 ℬ h hx

omit [GradedAlgebra ℬ] in
/-- Deletion preserves the weighted bigrading. -/
theorem deletionMap_isHomogeneous (H : AffineSubspace k V) :
    IsHomogeneousOfShift (bigrading (𝒜.deletion H) ℬ) (bigrading 𝒜 ℬ) 0
      (deletionMap B 𝒜 H) :=
  map_isHomogeneous (𝒜.deletion H) ℬ (Arrangement.deletion_le 𝒜 H)

end OrlikSolomon.OSAlgebra
