/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Projective
public import OrlikSolomon.Presentation.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The main theorem's projective space, hyperplanes, complement and ratios

TODO docstring
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Module HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace OrlikSolomon.Interface

open ProjectiveArrangement CoordinateRing

variable {k : Type u} [Field k]

/-! ### Projective space -/

variable (k) in
/-- The grading of `k[x₀, …, xₙ]` by total degree. A copy of the main theorem's `degreeGrading`,
with the same body. -/
abbrev degreeGrading (n : ℕ) : ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

variable (k) in
/-- Projective space `ℙⁿ_k = Proj k[x₀, …, xₙ]`, as a scheme over `Spec k` through the degree-zero
part `k` of `k[x₀, …, xₙ]`. A copy of the main theorem's `projectiveSpace`, with the same body. -/
def projectiveSpace (n : ℕ) : Over (Spec (.of k)) :=
  Over.mk (Proj.toSpecZero (degreeGrading k n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (degreeGrading k n 0))))

variable {n : ℕ}

/-! ### Linear forms and dual vectors -/

section Dual

variable {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}

/-- The dual vector `ℓ^∨` of a polynomial `ℓ`: the linear form `v ↦ ∑ᵢ cᵢ vᵢ` on `k^{n+1}` given by
the coefficients `cᵢ` of the variables `xᵢ` in `ℓ`. On linear forms it is injective
(`toDual_injOn`), and `ℓ ↦ ℓ^∨` identifies the linear forms with the dual of `k^{n+1}`. -/
def toDual : MvPolynomial (Fin (n + 1)) k →ₗ[k] Dual k (Fin (n + 1) → k) where
  toFun ℓ := ∑ i, ℓ.coeff (Finsupp.single i 1) • LinearMap.proj i
  map_add' ℓ ℓ' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c ℓ := by simp [Finset.smul_sum, smul_smul]

theorem toDual_apply (ℓ : MvPolynomial (Fin (n + 1)) k) (v : Fin (n + 1) → k) :
    toDual ℓ v = ∑ i, ℓ.coeff (Finsupp.single i 1) * v i := by
  simp [toDual]

@[simp]
theorem toDual_X (i : Fin (n + 1)) : toDual (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) =
    LinearMap.proj i := by
  ext v
  simp [toDual_apply, MvPolynomial.coeff_X', Finsupp.single_left_inj one_ne_zero, Pi.single_apply]

/-- The value of `ℓ^∨` on the `i`-th basis vector is the coefficient of `xᵢ` in `ℓ`. -/
@[simp]
theorem toDual_apply_single (ℓ : MvPolynomial (Fin (n + 1)) k) (i : Fin (n + 1)) :
    toDual ℓ (Pi.single i 1) = ℓ.coeff (Finsupp.single i 1) := by
  simp [toDual_apply, Pi.single_apply]

/-- A linear form is the sum of its coefficients times the variables. -/
theorem sum_coeff_smul_X (hℓ : ℓ.IsHomogeneous 1) :
    ∑ i, ℓ.coeff (Finsupp.single i 1) • MvPolynomial.X i = ℓ := by
  have hℓ' : ℓ ∈ Submodule.span k (Set.range (MvPolynomial.X : Fin (n + 1) → _)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hℓ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun k |>.1 hℓ'
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_X', Finsupp.single_left_inj one_ne_zero]

/-- Linear forms with the same dual vector are equal. -/
theorem toDual_injOn : Set.InjOn toDual {ℓ : MvPolynomial (Fin (n + 1)) k | ℓ.IsHomogeneous 1} :=
  fun ℓ hℓ ℓ' hℓ' h ↦ by
    rw [← sum_coeff_smul_X hℓ, ← sum_coeff_smul_X hℓ']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← toDual_apply_single, ← toDual_apply_single, h]

theorem toDual_inj (hℓ : ℓ.IsHomogeneous 1) (hℓ' : ℓ'.IsHomogeneous 1) :
    toDual ℓ = toDual ℓ' ↔ ℓ = ℓ' :=
  toDual_injOn.eq_iff hℓ hℓ'

theorem toDual_eq_zero_iff (hℓ : ℓ.IsHomogeneous 1) : toDual ℓ = 0 ↔ ℓ = 0 := by
  rw [← toDual_inj hℓ (MvPolynomial.isHomogeneous_zero _ _ 1), map_zero]

theorem toDual_ne_zero (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) : toDual ℓ ≠ 0 :=
  (toDual_eq_zero_iff hℓ).not.2 hℓ0

/-- A family of linear forms is linearly independent if and only if their dual vectors are. -/
theorem linearIndependent_toDual_comp_iff {ι : Type*} {ℓ : ι → MvPolynomial (Fin (n + 1)) k}
    (hℓ : ∀ i, (ℓ i).IsHomogeneous 1) :
    LinearIndependent k (toDual ∘ ℓ) ↔ LinearIndependent k ℓ :=
  toDual.linearIndependent_iff_of_injOn <| toDual_injOn.mono <|
    (Submodule.span_le (p := degreeGrading k n 1)).2 (Set.range_subset_iff.2 hℓ)

end Dual

/-! ### The comparison of projective spaces -/

section Iso

variable (k n) in
/-- The basis of `(k^{n+1})*` of the coordinate functions `v ↦ vᵢ`, dual to the standard basis. -/
abbrev coordinateBasis : Basis (Fin (n + 1)) k (Dual k (Fin (n + 1) → k)) :=
  (Pi.basisFun k (Fin (n + 1))).dualBasis

@[simp]
theorem coordinateBasis_apply (i : Fin (n + 1)) : coordinateBasis k n i = LinearMap.proj i := by
  ext v
  simp [Basis.dualBasis_apply]

/-- The identification of `Sym((k^{n+1})*)` with `k[x₀, …, xₙ]` sends the element given by the dual
vector `ℓ^∨` of a linear form `ℓ` back to `ℓ`. -/
theorem symmetricGradingToMvPolynomial_coord_toDual {ℓ : MvPolynomial (Fin (n + 1)) k}
    (hℓ : ℓ.IsHomogeneous 1) :
    symmetricGradingToMvPolynomial (coordinateBasis k n) (coord (toDual ℓ).toAffineMap) = ℓ := by
  have : toDual ℓ = ∑ i, ℓ.coeff (Finsupp.single i 1) • coordinateBasis k n i := by
    simp [toDual]
  rw [symmetricGradingToMvPolynomial_apply, coord_toAffineMap, this, map_sum, map_sum]
  simp_rw [map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  exact sum_coeff_smul_X hℓ

variable (k n) in
/-- The main theorem's projective space `Proj k[x₀, …, xₙ]` is the library's projective space
`ℙ(k^{n+1}) = Proj Sym((k^{n+1})*)`, over `Spec k`. The isomorphism is `Proj` of the identification
of `Sym((k^{n+1})*)` with `k[x₀, …, xₙ]` given by the coordinate functions. -/
def projectiveSpaceIso : projectiveSpace k n ≅ Geometric.projectiveSpace k (Fin (n + 1) → k) :=
  Over.isoMk
    (projIsoOfGraded (symmetricGradingToMvPolynomial (coordinateBasis k n))
      (mvPolynomialToSymmetricGrading (coordinateBasis k n))
      (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial _).apply_symm_apply x)
      (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial _).symm_apply_apply x))
    (proj_map_toSpecZero_algebraMap _ _ fun c ↦ (SymmetricAlgebra.equivMvPolynomial _).commutes c)

variable (k n) in
theorem projectiveSpaceIso_hom_left :
    (projectiveSpaceIso k n).hom.left =
      Proj.map (symmetricGradingToMvPolynomial (coordinateBasis k n))
        (irrelevant_le_map_of_comp_eq_id _ (mvPolynomialToSymmetricGrading (coordinateBasis k n))
          (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial _).apply_symm_apply x)) :=
  rfl

/-- A point of `Proj k[x₀, …, xₙ]`, a homogeneous prime of `k[x₀, …, xₙ]`, goes to its preimage in
`Sym((k^{n+1})*)`. -/
theorem asHomogeneousIdeal_projectiveSpaceIso_hom (x : (projectiveSpace k n).left) :
    ProjectiveSpectrum.asHomogeneousIdeal ((projectiveSpaceIso k n).hom.left x) =
      (ProjectiveSpectrum.asHomogeneousIdeal x).comap
        (symmetricGradingToMvPolynomial (coordinateBasis k n)) :=
  rfl

variable {ℓ : MvPolynomial (Fin (n + 1)) k}

/-- The isomorphism matches the zero locus `V₊(ℓ)` of a linear form with the zero locus of its dual
vector `ℓ^∨`. -/
theorem preimage_zeroLocus_coord_toDual (hℓ : ℓ.IsHomogeneous 1) :
    (projectiveSpaceIso k n).hom.left ⁻¹'
        ProjectiveSpectrum.zeroLocus (symmetricGrading k (Dual k (Fin (n + 1) → k)))
          {coord (toDual ℓ).toAffineMap} =
      ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ} := by
  ext x
  simp only [Set.mem_preimage, ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    SetLike.mem_coe]
  change _ ∈ (ProjectiveSpectrum.asHomogeneousIdeal x).comap _ ↔ _
  rw [HomogeneousIdeal.mem_comap, symmetricGradingToMvPolynomial_coord_toDual hℓ]

/-- The isomorphism matches the chart `D₊(ℓ)` of a linear form with the chart of its dual vector. -/
theorem preimage_basicOpen_coord_toDual (hℓ : ℓ.IsHomogeneous 1) :
    (projectiveSpaceIso k n).hom.left ⁻¹ᵁ
        Proj.basicOpen (symmetricGrading k (Dual k (Fin (n + 1) → k)))
          (coord (toDual ℓ).toAffineMap) =
      Proj.basicOpen (degreeGrading k n) ℓ := by
  rw [projectiveSpaceIso_hom_left, Proj.map_preimage_basicOpen,
    symmetricGradingToMvPolynomial_coord_toDual hℓ]

end Iso

end OrlikSolomon.Interface
