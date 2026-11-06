/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.ProjectiveAlgebra

/-!
# Ordinary degree and coefficient maps of the projective algebra

The boundary kernel inherits the ordinary exterior degree, as well as the weighted bigrading.
Extending coefficients preserves this kernel because coefficient extension commutes with the
central boundary. These constructions are the algebraic input to the diagonal form of the
projective structure theorem.

* `projectiveDegree` is the inherited natural-number grading.
* `projectiveCoefficientMap` extends coefficients inside the boundary kernel.

Blueprint: the diagonal in `thm:projective`.
-/

@[expose] public section

noncomputable section

open DirectSum

universe u

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (R : Type*) [CommRing R] {𝒜 : Arrangement k V}

/-- The contracting projection to the boundary kernel preserves ordinary exterior degree. -/
theorem projectiveProjection_mem_degree (h𝒜 : 𝒜.IsCentral) (H₀ : 𝒜) {n : ℕ}
    {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 n) :
    (projectiveProjection R h𝒜 H₀ x : OSAlgebra R 𝒜) ∈ degree R 𝒜 n := by
  rw [coe_projectiveProjection]
  refine Submodule.sub_mem _ hx ?_
  cases n with
  | zero =>
    rw [boundary_eq_zero_of_mem_degree_zero R h𝒜 hx, mul_zero]
    exact Submodule.zero_mem _
  | succ n =>
    simpa only [Nat.add_comm] using SetLike.mul_mem_graded
      (generator_mem_degree R 𝒜 H₀) (boundary_mem_degree R h𝒜 hx)

/-- The ambient endomorphism underlying the projective projection has degree zero. -/
theorem isHomogeneousOfShift_projectiveProjection_degree (h𝒜 : 𝒜.IsCentral) (H₀ : 𝒜) :
    IsHomogeneousOfShift (degree R 𝒜) (degree R 𝒜) 0
      (fun x ↦ (projectiveProjection R h𝒜 H₀ x : OSAlgebra R 𝒜)) := by
  intro n x hx
  simpa only [add_zero] using projectiveProjection_mem_degree R h𝒜 H₀ hx

/-- Every ordinary homogeneous component of a boundary-closed element is boundary-closed. -/
theorem projectiveAlgebra_isHomogeneous_degree (h𝒜 : 𝒜.IsCentral) (H₀ : 𝒜) :
    DirectSum.SetLike.IsHomogeneous (degree R 𝒜) (projectiveAlgebra R h𝒜) := by
  intro n x hx
  have hpx : (projectiveProjection R h𝒜 H₀ x : OSAlgebra R 𝒜) = x := by
    rw [coe_projectiveProjection, (mem_projectiveAlgebra_iff R h𝒜).1 hx, mul_zero, sub_zero]
  have h := (isHomogeneousOfShift_projectiveProjection_degree R h𝒜 H₀).decompose_map
    (add_zero n) x
  change (decompose (degree R 𝒜) (projectiveProjection R h𝒜 H₀ x : OSAlgebra R 𝒜) n :
      OSAlgebra R 𝒜) =
    (projectiveProjection R h𝒜 H₀ (decompose (degree R 𝒜) x n) : OSAlgebra R 𝒜) at h
  rw [hpx] at h
  rw [h]
  exact (projectiveProjection R h𝒜 H₀ (decompose (degree R 𝒜) x n)).property

/-- The ordinary exterior degree on the projective boundary kernel.
Blueprint: the diagonal in `thm:projective`. -/
def projectiveDegree (h𝒜 : 𝒜.IsCentral) (n : ℕ) : Submodule R (projectiveAlgebra R h𝒜) :=
  (degree R 𝒜 n).comap (projectiveAlgebra R h𝒜).val.toLinearMap

/-- Projective degree is the degree of the underlying element of the cone algebra. -/
@[simp]
theorem mem_projectiveDegree_iff (h𝒜 : 𝒜.IsCentral) {n : ℕ} {x : projectiveAlgebra R h𝒜} :
    x ∈ projectiveDegree R h𝒜 n ↔ (x : OSAlgebra R 𝒜) ∈ degree R 𝒜 n := Iff.rfl

/-- A difference of two generators, regarded as an element of the projective algebra. -/
def projectiveDifference (h𝒜 : 𝒜.IsCentral) (H K : 𝒜) : projectiveAlgebra R h𝒜 :=
  ⟨generator R 𝒜 H - generator R 𝒜 K,
    generator_sub_generator_mem_projectiveAlgebra R h𝒜 H K⟩

/-- A projective difference is the difference of the underlying generators. -/
@[simp]
theorem coe_projectiveDifference (h𝒜 : 𝒜.IsCentral) (H K : 𝒜) :
    (projectiveDifference R h𝒜 H K : OSAlgebra R 𝒜) = generator R 𝒜 H - generator R 𝒜 K := rfl

/-- A projective difference has ordinary degree one. -/
theorem projectiveDifference_mem_degree (h𝒜 : 𝒜.IsCentral) (H K : 𝒜) :
    projectiveDifference R h𝒜 H K ∈ projectiveDegree R h𝒜 1 :=
  Submodule.sub_mem _ (generator_mem_degree R 𝒜 H) (generator_mem_degree R 𝒜 K)

/-- For a nonempty central arrangement, the boundary kernel is an internally graded algebra. -/
instance projectiveDegreeGradedAlgebra [Nonempty 𝒜] (h𝒜 : 𝒜.IsCentral) :
    GradedAlgebra (projectiveDegree R h𝒜) :=
  homogeneousSubalgebraGradedAlgebra (degree R 𝒜) (projectiveAlgebra R h𝒜)
    (projectiveAlgebra_isHomogeneous_degree R h𝒜 (Classical.choice inferInstance))

/-- Decomposition in the projective algebra agrees with ordinary decomposition in the full
algebra. -/
@[simp]
theorem coe_decompose_projectiveDegree [Nonempty 𝒜] (h𝒜 : 𝒜.IsCentral)
    (x : projectiveAlgebra R h𝒜) (n : ℕ) :
    ((decompose (projectiveDegree R h𝒜) x n : projectiveAlgebra R h𝒜) : OSAlgebra R 𝒜) =
      (decompose (degree R 𝒜) (x : OSAlgebra R 𝒜) n : OSAlgebra R 𝒜) := by
  have h : IsHomogeneousOfShift (projectiveDegree R h𝒜) (degree R 𝒜) 0
      (projectiveAlgebra R h𝒜).val := by
    intro i y hy
    change (y : OSAlgebra R 𝒜) ∈ degree R 𝒜 (i + 0)
    simpa only [add_zero] using (mem_projectiveDegree_iff R h𝒜).1 hy
  exact (h.decompose_map (add_zero n) x).symm

section Coefficients

variable (B : Type*) [CommRing B] [Algebra R B]

/-- Extending coefficients preserves the projective boundary kernel.
Blueprint: the diagonal in `thm:projective`. -/
def projectiveCoefficientMap (h𝒜 : 𝒜.IsCentral) :
    projectiveAlgebra R h𝒜 →ₐ[R] projectiveAlgebra B h𝒜 :=
  ((coefficientMap R B 𝒜).comp (projectiveAlgebra R h𝒜).val).codRestrict
    ((projectiveAlgebra B h𝒜).restrictScalars R) fun x ↦ by
      change boundary B h𝒜 (coefficientMap R B 𝒜 x) = 0
      rw [boundary_coefficientMap, x.property, map_zero]

/-- The coefficient map of projective algebras is the ordinary coefficient map underneath. -/
@[simp]
theorem coe_projectiveCoefficientMap (h𝒜 : 𝒜.IsCentral) (x : projectiveAlgebra R h𝒜) :
    (projectiveCoefficientMap R B h𝒜 x : OSAlgebra B 𝒜) = coefficientMap R B 𝒜 x := rfl

/-- Extending coefficients preserves projective differences. -/
@[simp]
theorem projectiveCoefficientMap_difference (h𝒜 : 𝒜.IsCentral) (H K : 𝒜) :
    projectiveCoefficientMap R B h𝒜 (projectiveDifference R h𝒜 H K) =
      projectiveDifference B h𝒜 H K := by
  apply Subtype.ext
  simp only [coe_projectiveCoefficientMap, coe_projectiveDifference, map_sub,
    coefficientMap_generator]

/-- Projective coefficient extension preserves ordinary exterior degree. -/
theorem projectiveCoefficientMap_mem_degree (h𝒜 : 𝒜.IsCentral) {n : ℕ}
    {x : projectiveAlgebra R h𝒜} (hx : x ∈ projectiveDegree R h𝒜 n) :
    projectiveCoefficientMap R B h𝒜 x ∈ projectiveDegree B h𝒜 n :=
  coefficientMap_mem_degree R B 𝒜 hx

/-- Projective coefficient extension sends ordinary degree to the diagonal bidegree. -/
theorem projectiveCoefficientMap_mem_bigrading (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ]
    (h𝒜 : 𝒜.IsCentral) {n : ℕ} {x : projectiveAlgebra R h𝒜}
    (hx : x ∈ projectiveDegree R h𝒜 n) :
    projectiveCoefficientMap R B h𝒜 x ∈ projectiveBigrading B ℬ h𝒜 (n, n) :=
  coefficientMap_mem_bigrading 𝒜 ℬ hx

end Coefficients

end OrlikSolomon.OSAlgebra
