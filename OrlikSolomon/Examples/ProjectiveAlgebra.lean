/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.CoordinatePolynomials
public import OrlikSolomon.Examples.Presentation
public import OrlikSolomon.Grading.Laurent
public import OrlikSolomon.Interface.OSAlgebra
public import OrlikSolomon.Presentation.ProjectiveAlgebra

/-!
# Central boundary regressions

The empty and singleton arrangements test the extreme cases of the central boundary. The
noncentral two-point arrangement proves that its generator identity cannot descend in general:
the product of the two generators is zero, while its prospective boundary is nonzero, including
with characteristic-two coefficients. Zero coefficient rings remain allowed.

Blueprint: focused regressions for `lem:central-boundary` and `lem:projective-algebra`.
-/

@[expose] public section
noncomputable section

universe u
namespace OrlikSolomon.ProjectiveAlgebraExamples

open OSAlgebra PresentationExamples

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (B : Type*) [CommRing B]

/-- With no hyperplanes the central boundary is zero on the coefficient ring. -/
theorem boundary_empty (x : OSAlgebra B (∅ : Arrangement k V)) :
    boundary B Arrangement.isCentral_empty x = 0 := by
  have hx : x = algebraMap B _ (emptyEquiv B (k := k) (V := V) x) := by
    apply (emptyEquiv B).injective
    simp
  rw [hx, boundary_algebraMap]

/-- For the empty arrangement every element belongs to the projective kernel. -/
theorem projectiveAlgebra_empty :
    projectiveAlgebra B (Arrangement.isCentral_empty (k := k) (V := V)) = ⊤ := by
  ext x
  simp only [mem_projectiveAlgebra_iff, Algebra.mem_top, iff_true]
  exact boundary_empty B x

/-- A zero-dimensional arrangement has zero boundary, over every coefficient ring. -/
theorem boundary_dimension_zero [Subsingleton V] (𝒜 : Arrangement k V) (h𝒜 : 𝒜.IsCentral)
    (x : OSAlgebra B 𝒜) : boundary B h𝒜 x = 0 := by
  obtain rfl := Arrangement.eq_empty_of_subsingleton 𝒜
  exact boundary_empty B x

/-- A singleton affine arrangement is central, even when its hyperplane does not pass through the
chosen origin. In the line this is the point `a`. -/
def singletonPoint (a : k) : Arrangement k k := by
  classical
  exact Arrangement.ofFinset {pointHyperplane a}

@[simp]
theorem mem_onePoint (a : k) (H : AffineSubspace k k) :
    H ∈ singletonPoint a ↔ H = pointHyperplane a := by
  classical
  simp only [singletonPoint, Arrangement.mem_ofFinset, Finset.mem_singleton]
  exact ⟨And.left, fun h ↦ ⟨h, h ▸ isHyperplane_pointHyperplane a⟩⟩

/-- The unique generator label in the singleton arrangement. -/
def pointLabel (a : k) : singletonPoint a := ⟨pointHyperplane a, (mem_onePoint _ _).2 rfl⟩

/-- The singleton arrangement has its defining point in every hyperplane. -/
theorem onePoint_isCentral (a : k) : (singletonPoint a).IsCentral := by
  refine ⟨a, fun H hH ↦ ?_⟩
  rw [(mem_onePoint _ _).1 hH]
  simp

/-- The generator of a translated singleton arrangement has boundary one. -/
theorem boundary_onePoint_generator (a : k) :
    boundary B (onePoint_isCentral a) (generator B (singletonPoint a) (pointLabel a)) = 1 :=
  boundary_generator B _ _

/-- For one hyperplane the projective kernel consists exactly of the coefficient subalgebra,
over arbitrary coefficients, including the zero ring. -/
theorem projectiveAlgebra_onePoint (a : k) :
    projectiveAlgebra B (onePoint_isCentral a) = ⊥ := by
  rw [projectiveAlgebra_eq_adjoin B _ (pointLabel a)]
  have hrange : (Set.range fun H : singletonPoint a ↦ generator B (singletonPoint a) H -
      generator B (singletonPoint a) (pointLabel a)) = {0} := by
    ext x
    constructor
    · rintro ⟨H, rfl⟩
      have hH : H = pointLabel a := Subtype.ext ((mem_onePoint _ _).1 H.2)
      simp only [hH, sub_self, Set.mem_singleton_iff]
    · rintro rfl
      exact ⟨pointLabel a, sub_self _⟩
  rw [hrange, Algebra.adjoin_singleton_zero]

-- The two-summand decomposition needs no assumption that the coefficients are nonzero.
example (a : k) :
    (projectiveAlgebra (ZMod 1) (onePoint_isCentral a) ×
      projectiveAlgebra (ZMod 1) (onePoint_isCentral a)) ≃ₗ[ZMod 1]
        OSAlgebra (ZMod 1) (singletonPoint a) :=
  projectiveDecomposition _ _ (pointLabel a)

/-- A word-boundary operator with the generator Leibniz identity cannot exist on the noncentral
two-point algebra over nonzero coefficients. The obstruction is `e₁ - e₀`, rather than twice it. -/
theorem no_boundary_twoPoints [Nontrivial B] :
    ¬ ∃ d : OSAlgebra B (twoPoints k) →ₗ[B] OSAlgebra B (twoPoints k),
      (∀ H, d (generator B (twoPoints k) H) = 1) ∧
        ∀ H x, d (generator B (twoPoints k) H * x) =
          x - generator B (twoPoints k) H * d x := by
  rintro ⟨d, hd, hmul⟩
  have h := hmul (zeroPoint k) (generator B (twoPoints k) (onePoint k))
  rw [twoPoints_product, map_zero, hd, mul_one] at h
  exact twoPoints_difference B h.symm

/-- The two coordinate axes give a central arrangement with two distinct generators. -/
theorem coordinatePlane_isCentral : (Examples.coordinateArrangement k (Fin 2)).IsCentral := by
  classical
  refine ⟨0, fun H hH ↦ ?_⟩
  rw [← Arrangement.mem_hyperplanes, Examples.hyperplanes_coordinateArrangement] at hH
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hH
  simp

/-- A coordinate hyperplane label in the two-dimensional coordinate arrangement. -/
def coordinateLabel (i : Fin 2) : Examples.coordinateArrangement k (Fin 2) := by
  classical
  refine ⟨Examples.coordinateHyperplane k i, ?_⟩
  rw [← Arrangement.mem_hyperplanes, Examples.hyperplanes_coordinateArrangement]
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩

/-- The boundary of the product of two coordinate generators is nonzero. This detects the
signed two-term boundary without any division by two. -/
theorem coordinatePair_boundary_ne_zero [Nontrivial B] :
    boundary B (coordinatePlane_isCentral (k := k))
      (generator B _ (coordinateLabel (k := k) 0) * generator B _ (coordinateLabel 1)) ≠ 0 := by
  rw [boundary_generator_mul, boundary_generator, mul_one, sub_ne_zero]
  apply (linearIndependent_generator B _).injective.ne
  intro h
  have hi := Examples.coordinateHyperplane_injective k (congrArg Subtype.val h)
  exact Fin.zero_ne_one hi.symm

-- In characteristic two the two terms do not cancel each other.
example : boundary (ZMod 2) (coordinatePlane_isCentral (k := ZMod 2))
    (generator (ZMod 2) _ (coordinateLabel (k := ZMod 2) 0) * generator (ZMod 2) _
      (coordinateLabel 1)) ≠ 0 := coordinatePair_boundary_ne_zero _

-- The second projective summand is inserted on the left by its degree-one generator.
example : projectiveDecomposition (ZMod 2) (coordinatePlane_isCentral (k := ZMod 2))
    (coordinateLabel 0) (0, 1) = generator (ZMod 2) _ (coordinateLabel 0) := by simp

-- The two-point obstruction remains valid in characteristic two.
example : ¬ ∃ d : OSAlgebra (ZMod 2) (twoPoints (ZMod 2)) →ₗ[ZMod 2]
    OSAlgebra (ZMod 2) (twoPoints (ZMod 2)),
    (∀ H, d (generator _ _ H) = 1) ∧
      ∀ H x, d (generator _ _ H * x) = x - generator _ _ H * d x :=
  no_boundary_twoPoints _

-- The singleton generator still squares to zero with characteristic-two coefficients.
example : generator (ZMod 2) (singletonPoint (1 : ZMod 2)) (pointLabel 1) ^ 2 = 0 :=
  generator_sq _ _ _

-- The boundary and kernel construction must allow degenerate coefficient rings.
example (𝒜 : Arrangement k V) (h𝒜 : 𝒜.IsCentral) (x : OSAlgebra (ZMod 1) 𝒜) :
    boundary (ZMod 1) h𝒜 x = 0 := Subsingleton.elim _ _

section Interface

variable {𝒜 : Arrangement k V} (h𝒜 : 𝒜.IsCentral) (ι : Type*) [Nonempty ι]
  (Dep : List ι → Prop) (σ : ι ≃ 𝒜)
  (hDep : ∀ S : List ι, S.Nodup → (Dep S ↔ Arrangement.IsDependent (S.map σ)))

/-- The projective comparison computes on differences with characteristic-two coefficients. -/
example (i j : ι) :
    (Interface.projectiveAlgebraEquiv (ZMod 2) ι Dep σ hDep h𝒜
        (Interface.projectiveGenerator (ZMod 2) ι Dep i j) : OSAlgebra (ZMod 2) 𝒜) =
      generator (ZMod 2) 𝒜 (σ i) - generator (ZMod 2) 𝒜 (σ j) := by
  simp

/-- The generic interface equivalence is available over the zero coefficient ring. -/
example : Interface.projectiveOrlikSolomonAlgebra PUnit ι Dep ≃ₐ[PUnit]
    projectiveAlgebra PUnit h𝒜 := Interface.projectiveAlgebraEquiv PUnit ι Dep σ hDep h𝒜

/-- The main theorem's set-image formula elaborates over the canonical Laurent model over ℤ. -/
example (i : ℤ × ℤ) :
    Interface.projectiveAlgebraEquiv (LaurentPolynomial ℤ) ι Dep σ hDep h𝒜 ''
        (Interface.projectiveOrlikSolomonGrading (LaurentPolynomial ℤ) ι Dep
          (laurentGrading ℤ) i : Set _) =
      (projectiveBigrading (LaurentPolynomial ℤ) (laurentGrading ℤ) h𝒜 i : Set _) :=
  Interface.image_projectiveOrlikSolomonGrading _ _ _ _ _ _ _ _

end Interface

end OrlikSolomon.ProjectiveAlgebraExamples
