/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Grading

/-!
# The boundary of a central Orlik–Solomon algebra

For a central arrangement the exterior word boundary preserves the full two-sided relation
submodule, and therefore descends to a linear operator on the Orlik–Solomon algebra. It is a
square-zero graded antiderivation, lowering both cohomological degree and weight by one.
Centrality is essential: the affine empty-intersection relations are generally not preserved.

Blueprint: `lem:central-boundary`.
-/

@[expose] public section
noncomputable section

universe u
namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (B : Type*) [CommRing B] {𝒜 : Arrangement k V}

/-- For a central arrangement, contraction kills every context of a relation after passing to the
quotient. This checks the full two-sided relation submodule required for linear descent. -/
theorem boundary_relations (h𝒜 : 𝒜.IsCentral) :
    relationSubmodule B (osRelations B 𝒜) ≤
      LinearMap.ker ((quotient B 𝒜).toLinearMap ∘ₗ exteriorBoundary B) := by
  refine relationSubmodule_le_of_span_eq_top (OrlikSolomon.span_range_word B)
    (OrlikSolomon.span_range_word B) ?_
  rintro _ ⟨l, rfl⟩ r ⟨I, _, ⟨hempty, _⟩ | ⟨hdep, rfl⟩⟩ _ ⟨m, rfl⟩
  · exact ((h𝒜.inter_ne_bot I) hempty).elim
  · have hr : quotient B 𝒜 (wordBoundary (exteriorGen B) I) = 0 := by
      rw [quotient_wordBoundary]
      exact wordBoundary_eq_zero_of_isDependent B 𝒜 hdep
    have hdr : exteriorBoundary B (wordBoundary (exteriorGen B) I) = 0 := by
      rw [← exteriorBoundary_word, exteriorBoundary_exteriorBoundary]
    change quotient B 𝒜
      (exteriorBoundary B (word (exteriorGen B) l * wordBoundary (exteriorGen B) I *
        word (exteriorGen B) m)) = 0
    rw [mul_assoc, exteriorBoundary_word_mul,
      exteriorBoundary_mul_of_mem_exteriorPower B (wordBoundary_mem_exteriorPower B I)]
    simp [hr, hdr]

/-- The square-zero signed boundary on a central Orlik–Solomon algebra, sending each generator
to `1`. It is linear over all coefficients. Blueprint: `lem:central-boundary`. -/
def boundary (h𝒜 : 𝒜.IsCentral) : OSAlgebra B 𝒜 →ₗ[B] OSAlgebra B 𝒜 :=
  RelationQuotient.liftLinear ((quotient B 𝒜).toLinearMap ∘ₗ exteriorBoundary B)
    (boundary_relations B h𝒜)

@[simp]
theorem boundary_quotient (h𝒜 : 𝒜.IsCentral) (x : ExteriorAlgebra B (𝒜 →₀ B)) :
    boundary B h𝒜 (quotient B 𝒜 x) = quotient B 𝒜 (exteriorBoundary B x) := rfl

@[simp]
theorem boundary_one (h𝒜 : 𝒜.IsCentral) : boundary B h𝒜 1 = 0 := by
  simpa only [map_one, exteriorBoundary_one, map_zero] using
    boundary_quotient B h𝒜 1

@[simp]
theorem boundary_algebraMap (h𝒜 : 𝒜.IsCentral) (b : B) :
    boundary B h𝒜 (algebraMap B (OSAlgebra B 𝒜) b) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, boundary_one, smul_zero]

/-- The boundary of a product with a generator is the contracting-homotopy identity. -/
@[simp]
theorem boundary_generator_mul (h𝒜 : 𝒜.IsCentral) (H : 𝒜) (x : OSAlgebra B 𝒜) :
    boundary B h𝒜 (generator B 𝒜 H * x) = x - generator B 𝒜 H * boundary B h𝒜 x := by
  obtain ⟨x, rfl⟩ := quotient_surjective B 𝒜 x
  rw [← quotient_exteriorGen, ← map_mul, boundary_quotient,
    exteriorBoundary_exteriorGen_mul]
  simp

@[simp]
theorem boundary_generator (h𝒜 : 𝒜.IsCentral) (H : 𝒜) :
    boundary B h𝒜 (generator B 𝒜 H) = 1 := by
  simpa using boundary_generator_mul B h𝒜 H 1

/-- The descended boundary squares to zero. -/
@[simp]
theorem boundary_boundary (h𝒜 : 𝒜.IsCentral) (x : OSAlgebra B 𝒜) :
    boundary B h𝒜 (boundary B h𝒜 x) = 0 := by
  obtain ⟨x, rfl⟩ := quotient_surjective B 𝒜 x
  simp

/-- The descended operator computes the signed word boundary. -/
@[simp]
theorem boundary_word (h𝒜 : 𝒜.IsCentral) (I : List 𝒜) :
    boundary B h𝒜 (word (generator B 𝒜) I) = wordBoundary (generator B 𝒜) I := by
  rw [← quotient_word, boundary_quotient, exteriorBoundary_word, quotient_wordBoundary]

/-- The signed Leibniz rule with a word on the left and an arbitrary right factor. -/
theorem boundary_word_mul (h𝒜 : 𝒜.IsCentral) (I : List 𝒜) (x : OSAlgebra B 𝒜) :
    boundary B h𝒜 (word (generator B 𝒜) I * x) =
      wordBoundary (generator B 𝒜) I * x +
        (I.length : ℤ).negOnePow • (word (generator B 𝒜) I * boundary B h𝒜 x) := by
  obtain ⟨x, rfl⟩ := quotient_surjective B 𝒜 x
  rw [← quotient_word, ← map_mul, boundary_quotient, exteriorBoundary_word_mul]
  simp

/-- The signed Leibniz rule for a homogeneous left factor and an arbitrary right factor.
Blueprint: `lem:central-boundary`. -/
theorem boundary_mul_of_mem_degree (h𝒜 : 𝒜.IsCentral) {n : ℕ}
    {x : OSAlgebra B 𝒜} (hx : x ∈ degree B 𝒜 n) (y : OSAlgebra B 𝒜) :
    boundary B h𝒜 (x * y) = boundary B h𝒜 x * y +
      (n : ℤ).negOnePow • (x * boundary B h𝒜 y) := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    simpa only [hI, boundary_word] using boundary_word_mul B h𝒜 I y
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [add_mul, map_add, hx, hz, smul_add]
    abel
  | smul b x _ hx =>
    simp only [smul_mul_assoc, map_smul, hx, smul_add]
    rw [smul_comm]

/-- The boundary lowers a positive exterior degree by one. -/
theorem boundary_mem_degree (h𝒜 : 𝒜.IsCentral) {n : ℕ} {x : OSAlgebra B 𝒜}
    (hx : x ∈ degree B 𝒜 (n + 1)) : boundary B h𝒜 x ∈ degree B 𝒜 n := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    simpa only [boundary_word, hI, Nat.add_sub_cancel] using wordBoundary_mem_degree B 𝒜 I
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul b x _ hx => simpa only [map_smul] using Submodule.smul_mem _ b hx

/-- The boundary vanishes in exterior degree zero. -/
theorem boundary_eq_zero_of_mem_degree_zero (h𝒜 : 𝒜.IsCentral) {x : OSAlgebra B 𝒜}
    (hx : x ∈ degree B 𝒜 0) : boundary B h𝒜 x = 0 := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    have : I = [] := List.length_eq_zero_iff.1 hI
    simp [this]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul b x _ hx => simp only [map_smul, hx, smul_zero]

/-- Extending coefficients commutes with the central boundary. -/
@[simp]
theorem boundary_coefficientMap {S : Type*} [CommRing S] [Algebra B S]
    (h𝒜 : 𝒜.IsCentral) (x : OSAlgebra B 𝒜) :
    boundary S h𝒜 (coefficientMap B S 𝒜 x) = coefficientMap B S 𝒜 (boundary B h𝒜 x) := by
  have h := LinearMap.ext_on_range (span_range_word B 𝒜)
    (f := (boundary S h𝒜).restrictScalars B ∘ₗ (coefficientMap B S 𝒜).toLinearMap)
    (g := (coefficientMap B S 𝒜).toLinearMap ∘ₗ boundary B h𝒜)
    fun I ↦ by simp [map_wordBoundary]
  exact DFunLike.congr_fun h x

end OrlikSolomon.OSAlgebra
