/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Geometry.Schemes.Projective
public import OrlikSolomon.Presentation.Basic
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# The main theorem's projective space and hyperplanes

This bridge uses the exact Mathlib presentations of the approved main-theorem interface. Its
`degreeGrading`, `projectiveSpace`, `IsEquation`, `Hyperplane`, `HyperplaneArrangement` and
`IsDependent` have the same bodies as their interface counterparts. The coordinate coefficient map
`toDual` identifies linear polynomials with dual vectors; `projectiveSpaceIso` identifies the two
projective spaces over the base. Equations of a scheme hyperplane differ by a unique nonzero scalar,
and `toProjectiveArrangement`, `projectiveHyperplaneEquiv` and `coneHyperplaneEquiv` translate
scheme hyperplanes to the library's linear and central arrangements.

These comparisons use scheme points, and work in projective dimension zero and over finite fields.
The companion `Interface/ProjectiveComplement` supplies complements and ratio functions. This is
the geometry bridge for milestone M7 (#141); it does not change any blueprint statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Module

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
@[implicit_reducible]
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
  simp [toDual_apply, MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero, Pi.single_apply]

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
  simp [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]

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
  simp

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

/-- The coordinate graded maps are inverse. -/
theorem coordinateGraded_comp :
    (symmetricGradingToMvPolynomial (coordinateBasis k n)).comp
      (mvPolynomialToSymmetricGrading (coordinateBasis k n)) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := by
  apply GradedRingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial (coordinateBasis k n)).apply_symm_apply x

/-- The coordinate graded maps are inverse. -/
theorem coordinateGraded_comp_symm :
    (mvPolynomialToSymmetricGrading (coordinateBasis k n)).comp
      (symmetricGradingToMvPolynomial (coordinateBasis k n)) =
        GradedRingHom.id (symmetricGrading k (Dual k (Fin (n + 1) → k))) := by
  apply GradedRingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial (coordinateBasis k n)).symm_apply_apply x

variable (k n) in
/-- The main theorem's projective space `Proj k[x₀, …, xₙ]` is the library's projective space
`ℙ(k^{n+1}) = Proj Sym((k^{n+1})*)`, over `Spec k`. The isomorphism is `Proj` of the identification
of `Sym((k^{n+1})*)` with `k[x₀, …, xₙ]` given by the coordinate functions. -/
def projectiveSpaceIso : projectiveSpace k n ≅ Geometric.projectiveSpace k (Fin (n + 1) → k) :=
  Over.isoMk
    (projIsoOfGraded (symmetricGradingToMvPolynomial (coordinateBasis k n))
      (mvPolynomialToSymmetricGrading (coordinateBasis k n))
      coordinateGraded_comp
      coordinateGraded_comp_symm)
    (proj_map_toSpecZero_algebraMap _ _ fun c ↦ (SymmetricAlgebra.equivMvPolynomial _).commutes c)

variable (k n) in
theorem projectiveSpaceIso_hom_left :
    (projectiveSpaceIso k n).hom.left =
      Proj.map (symmetricGradingToMvPolynomial (coordinateBasis k n))
        (irrelevant_le_map_of_comp_eq_id _ (mvPolynomialToSymmetricGrading (coordinateBasis k n))
          coordinateGraded_comp) :=
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
  change (ProjectiveSpectrum.comap (symmetricGradingToMvPolynomial (coordinateBasis k n))
      (irrelevant_le_map_of_comp_eq_id _ (mvPolynomialToSymmetricGrading (coordinateBasis k n))
        coordinateGraded_comp)) ⁻¹' _ = _
  ext x
  simp only [Set.mem_preimage, ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change coord (toDual ℓ).toAffineMap ∈
      (ProjectiveSpectrum.asHomogeneousIdeal x).comap
        (symmetricGradingToMvPolynomial (coordinateBasis k n)) ↔
      ℓ ∈ ProjectiveSpectrum.asHomogeneousIdeal x
  change (symmetricGradingToMvPolynomial (coordinateBasis k n))
      (coord (toDual ℓ).toAffineMap) ∈ x.asHomogeneousIdeal ↔ ℓ ∈ x.asHomogeneousIdeal
  rw [symmetricGradingToMvPolynomial_coord_toDual hℓ]

/-- The isomorphism matches the chart `D₊(ℓ)` of a linear form with the chart of its dual vector. -/
theorem preimage_basicOpen_coord_toDual (hℓ : ℓ.IsHomogeneous 1) :
    (projectiveSpaceIso k n).hom.left ⁻¹ᵁ
        Proj.basicOpen (symmetricGrading k (Dual k (Fin (n + 1) → k)))
          (coord (toDual ℓ).toAffineMap) =
      Proj.basicOpen (degreeGrading k n) ℓ := by
  rw [projectiveSpaceIso_hom_left, Proj.map_preimage_basicOpen,
    symmetricGradingToMvPolynomial_coord_toDual hℓ]

end Iso

/-- `ℓ` is an **equation** of the set `H` of points of `ℙⁿ`: a nonzero linear form whose zero locus
`V₊(ℓ)` is `H`. An equation of `H` is unique up to a nonzero scalar. -/
structure IsEquation (H : Set (projectiveSpace k n).left) (ℓ : MvPolynomial (Fin (n + 1)) k) :
    Prop where
  /-- `ℓ` is a linear form. -/
  isHomogeneous : ℓ.IsHomogeneous 1
  /-- `ℓ` is not zero. -/
  ne_zero : ℓ ≠ 0
  /-- `H` is the zero locus of `ℓ`, the points whose homogeneous prime contains `ℓ`. -/
  zeroLocus_eq : ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ} = H

variable (k n) in
/-- A **hyperplane** of `ℙⁿ`: a set of points of `ℙⁿ` that has an equation. -/
abbrev Hyperplane : Type u := {H : Set (projectiveSpace k n).left // ∃ ℓ, IsEquation H ℓ}

variable (k n) in
/-- A **projective hyperplane arrangement**: a finite set of hyperplanes of `ℙⁿ`. -/
abbrev HyperplaneArrangement : Type u := Finset (Hyperplane k n)

/-- A list of hyperplanes of `𝒜` is **dependent** if some choice of equations of its members is
linearly dependent over `k`. Since equations are unique up to nonzero scalars, every choice is then
dependent. For a list without repetitions, this says that the intersection has codimension less
than the length of the list. -/
def IsDependent {𝒜 : HyperplaneArrangement k n} (S : List 𝒜) : Prop :=
  ∃ ℓ : Fin S.length → MvPolynomial (Fin (n + 1)) k,
    (∀ j, IsEquation ((S[j] : 𝒜) : Hyperplane k n) (ℓ j)) ∧ ¬ LinearIndependent k ℓ

/-! ### Equations determine their linear kernels -/

private def vectorPoint {ι : Type*} {v : ι → k} (hv : v ≠ 0) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k) where
  asHomogeneousIdeal := (RingHom.ker (MvPolynomial.eval v)).homogeneousCore _
  isPrime := Ideal.IsPrime.homogeneousCore (RingHom.ker_isPrime (MvPolynomial.eval v))
  not_irrelevant_le h := by
    apply hv
    funext i
    have hXi : MvPolynomial.X i ∈
        HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one (MvPolynomial.isHomogeneous_X k i)
    have hX := Ideal.toIdeal_homogeneousCore_le _ _ (h hXi)
    simpa using hX

private theorem mem_vectorPoint {ι : Type*} {v : ι → k} {ℓ : MvPolynomial ι k}
    (hℓ : ℓ.IsHomogeneous 1) (hv : v ≠ 0) :
    ℓ ∈ (vectorPoint hv).asHomogeneousIdeal ↔ MvPolynomial.eval v ℓ = 0 := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (MvPolynomial.homogeneousSubmodule ι k)
      (RingHom.ker (MvPolynomial.eval v)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (𝒜 := MvPolynomial.homogeneousSubmodule ι k) ⟨1, hℓ⟩ h

/-- Evaluating a linear polynomial is applying its coefficient linear form. -/
theorem eval_eq_toDual {ℓ : MvPolynomial (Fin (n + 1)) k} (hℓ : ℓ.IsHomogeneous 1)
    (v : Fin (n + 1) → k) : MvPolynomial.eval v ℓ = toDual ℓ v := by
  conv_lhs => rw [← sum_coeff_smul_X hℓ]
  simp [toDual_apply]

/-- Equality of projective zero loci forces equality of the linear kernels. This uses scheme
points, and remains true over finite fields and in projective dimension zero. -/
theorem ker_toDual_eq_of_zeroLocus_eq {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
    (hℓ : ℓ.IsHomogeneous 1) (hℓ' : ℓ'.IsHomogeneous 1)
    (h : ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ} =
      ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ'}) :
    LinearMap.ker (toDual ℓ) = LinearMap.ker (toDual ℓ') := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have hv' := congrArg (fun Z ↦ vectorPoint hv ∈ Z) h
  have hx : ℓ ∈ (vectorPoint hv).asHomogeneousIdeal ↔
      ℓ' ∈ (vectorPoint hv).asHomogeneousIdeal := by
    simpa only [ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
      SetLike.mem_coe] using Iff.of_eq hv'
  rw [mem_vectorPoint hℓ hv, mem_vectorPoint hℓ' hv,
    eval_eq_toDual hℓ, eval_eq_toDual hℓ'] at hx
  exact hx

/-- Two equations of the same projective hyperplane differ by a unique nonzero scalar. -/
theorem IsEquation.existsUnique_smul {H : Set (projectiveSpace k n).left}
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation H ℓ) (hℓ' : IsEquation H ℓ') :
    ∃! c : kˣ, ℓ' = (c : k) • ℓ := by
  have hker := ker_toDual_eq_of_zeroLocus_eq hℓ'.isHomogeneous hℓ.isHomogeneous
    (hℓ'.zeroLocus_eq.trans hℓ.zeroLocus_eq.symm)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_ker_eq hker
    (toDual_ne_zero hℓ.isHomogeneous hℓ.ne_zero)
  have heq : ℓ' = (c : k) • ℓ := by
    apply toDual_injOn hℓ'.isHomogeneous ((degreeGrading k n 1).smul_mem _ hℓ.isHomogeneous)
    simpa only [map_smul] using hc
  refine ⟨c, heq, fun d hd ↦ Units.ext ?_⟩
  exact smul_left_injective k hℓ.ne_zero (hd.symm.trans heq)

/-- Chosen equation of a hyperplane. Comparisons below remove this choice from the public maps. -/
def hyperplaneForm (H : Hyperplane k n) : MvPolynomial (Fin (n + 1)) k := H.2.choose

/-- The chosen equation is an equation of its hyperplane. -/
theorem isEquation_hyperplaneForm (H : Hyperplane k n) : IsEquation H (hyperplaneForm H) :=
  H.2.choose_spec

/-- The linear hyperplane in `k^{n+1}` whose projectivization is the given scheme hyperplane. -/
def hyperplaneSubmodule (H : Hyperplane k n) : Submodule k (Fin (n + 1) → k) :=
  LinearMap.ker (toDual (hyperplaneForm H))

/-- The linear hyperplane is the kernel of every equation. -/
theorem hyperplaneSubmodule_eq_ker {H : Hyperplane k n}
    {ℓ : MvPolynomial (Fin (n + 1)) k}
    (hℓ : IsEquation H ℓ) : hyperplaneSubmodule H = LinearMap.ker (toDual ℓ) :=
  ker_toDual_eq_of_zeroLocus_eq
    (isEquation_hyperplaneForm H).isHomogeneous hℓ.isHomogeneous
    ((isEquation_hyperplaneForm H).zeroLocus_eq.trans hℓ.zeroLocus_eq.symm)

/-- The linear hyperplane is a subspace of codimension one. -/
theorem isCoatom_hyperplaneSubmodule (H : Hyperplane k n) : IsCoatom (hyperplaneSubmodule H) :=
  isCoatom_ker (toDual_ne_zero (isEquation_hyperplaneForm H).isHomogeneous
    (isEquation_hyperplaneForm H).ne_zero)

/-- Projective hyperplanes are determined by their linear kernels. -/
theorem hyperplaneSubmodule_injective :
    Function.Injective (hyperplaneSubmodule (k := k) (n := n)) := by
  intro H K h
  obtain ⟨c, hc⟩ := exists_eq_smul_of_ker_eq h
    (toDual_ne_zero (isEquation_hyperplaneForm K).isHomogeneous
      (isEquation_hyperplaneForm K).ne_zero)
  have heq : hyperplaneForm H = (c : k) • hyperplaneForm K := by
    apply toDual_injOn (isEquation_hyperplaneForm H).isHomogeneous
      ((degreeGrading k n 1).smul_mem _ (isEquation_hyperplaneForm K).isHomogeneous)
    simpa only [map_smul] using hc
  apply Subtype.ext
  rw [← (isEquation_hyperplaneForm H).zeroLocus_eq,
    ← (isEquation_hyperplaneForm K).zeroLocus_eq, heq]
  ext x
  simp only [ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  exact (x.asHomogeneousIdeal.toIdeal.restrictScalars k).smul_mem_iff (Units.ne_zero c)

/-! ### Arrangements and their cones -/

/-- The linear projective arrangement associated to a finite family of scheme hyperplanes. -/
def toProjectiveArrangement (𝒜 : HyperplaneArrangement k n) :
    ProjectiveArrangement k (Fin (n + 1) → k) := by
  classical
  exact
    { hyperplanes := 𝒜.image hyperplaneSubmodule
      isCoatom_of_mem' := fun L hL ↦ by
        obtain ⟨H, _, rfl⟩ := Finset.mem_image.1 hL
        exact isCoatom_hyperplaneSubmodule H }

/-- Membership in the linear arrangement is witnessed by a scheme hyperplane. -/
@[simp]
theorem mem_toProjectiveArrangement {𝒜 : HyperplaneArrangement k n}
    {L : Submodule k (Fin (n + 1) → k)} :
    L ∈ toProjectiveArrangement 𝒜 ↔ ∃ H ∈ 𝒜, hyperplaneSubmodule H = L := by
  classical
  exact Finset.mem_image

/-- Every equation of a member supplies a hyperplane of the linear arrangement. -/
theorem ker_toDual_mem_toProjectiveArrangement {𝒜 : HyperplaneArrangement k n}
    {H : Hyperplane k n} (hH : H ∈ 𝒜) {ℓ : MvPolynomial (Fin (n + 1)) k}
    (hℓ : IsEquation H ℓ) : LinearMap.ker (toDual ℓ) ∈ toProjectiveArrangement 𝒜 :=
  mem_toProjectiveArrangement.2 ⟨H, hH, hyperplaneSubmodule_eq_ker hℓ⟩

/-- Scheme hyperplanes biject with the hyperplanes of their linear arrangement. -/
def projectiveHyperplaneEquiv (𝒜 : HyperplaneArrangement k n) : 𝒜 ≃ toProjectiveArrangement 𝒜 :=
  .ofBijective
    (fun H ↦ ⟨hyperplaneSubmodule H, mem_toProjectiveArrangement.2 ⟨H, H.2, rfl⟩⟩)
    ⟨fun H K h ↦ Subtype.ext (hyperplaneSubmodule_injective (congrArg Subtype.val h)),
      fun L ↦ by
        obtain ⟨H, hH, hL⟩ := mem_toProjectiveArrangement.1 L.2
        exact ⟨⟨H, hH⟩, Subtype.ext hL⟩⟩

/-- The bijection sends a scheme hyperplane to its linear kernel. -/
@[simp]
theorem coe_projectiveHyperplaneEquiv {𝒜 : HyperplaneArrangement k n} (H : 𝒜) :
    (projectiveHyperplaneEquiv 𝒜 H : Submodule k (Fin (n + 1) → k)) = hyperplaneSubmodule H :=
  rfl

/-- A nonempty scheme arrangement has a nonempty linear arrangement. -/
instance nonempty_toProjectiveArrangement (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜] :
    Nonempty (toProjectiveArrangement 𝒜) :=
  (projectiveHyperplaneEquiv 𝒜).symm.nonempty

/-- The linear arrangement is nonempty precisely when the scheme arrangement is. -/
theorem nonempty_toProjectiveArrangement_iff (𝒜 : HyperplaneArrangement k n) :
    Nonempty (toProjectiveArrangement 𝒜) ↔ Nonempty 𝒜 :=
  (projectiveHyperplaneEquiv 𝒜).nonempty_congr.symm

/-- Scheme hyperplanes biject with the affine hyperplanes of the central cone. -/
def coneHyperplaneEquiv (𝒜 : HyperplaneArrangement k n) : 𝒜 ≃ (toProjectiveArrangement 𝒜).cone :=
  (projectiveHyperplaneEquiv 𝒜).trans (ProjectiveArrangement.coneHyperplaneEquiv _)

/-- The cone hyperplane is the affine subspace underlying the linear kernel. -/
@[simp]
theorem coe_coneHyperplaneEquiv {𝒜 : HyperplaneArrangement k n} (H : 𝒜) :
    (coneHyperplaneEquiv 𝒜 H : AffineSubspace k (Fin (n + 1) → k)) =
      (hyperplaneSubmodule H).toAffineSubspace :=
  rfl

/-- Each polynomial equation gives an equation of its cone hyperplane. -/
theorem isEquation_coneHyperplaneEquiv {𝒜 : HyperplaneArrangement k n} (H : 𝒜)
    {ℓ : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation (H : Hyperplane k n) ℓ) :
    OrlikSolomon.IsEquation (toDual ℓ).toAffineMap
      (coneHyperplaneEquiv 𝒜 H : AffineSubspace k (Fin (n + 1) → k)) := by
  rw [coe_coneHyperplaneEquiv, hyperplaneSubmodule_eq_ker hℓ]
  exact isEquation_toAffineMap (toDual_ne_zero hℓ.isHomogeneous hℓ.ne_zero)

/-! ### Dependence of equations -/

/-- Dependence of scheme hyperplanes can be tested using any equations of the list. -/
theorem isDependent_iff_not_linearIndependent {𝒜 : HyperplaneArrangement k n} (S : List 𝒜)
    (ℓ : Fin S.length → MvPolynomial (Fin (n + 1)) k)
    (hℓ : ∀ j, IsEquation (S.get j : Hyperplane k n) (ℓ j)) :
    IsDependent S ↔ ¬ LinearIndependent k ℓ := by
  classical
  constructor
  · rintro ⟨ℓ', hℓ', hdep⟩ hli
    choose c hc using fun j ↦ ((hℓ j).existsUnique_smul (hℓ' j)).exists
    apply hdep
    convert hli.units_smul c using 1
    funext j
    exact hc j
  · exact fun h ↦ ⟨ℓ, hℓ, h⟩

/-- The interface's dependence predicate is exactly dependence in the library's central cone.
The statement allows repeated hyperplanes and the empty list. -/
theorem isDependent_iff_cone {𝒜 : HyperplaneArrangement k n} (S : List 𝒜) :
    IsDependent S ↔ Arrangement.IsDependent (S.map (coneHyperplaneEquiv 𝒜)) := by
  let e := coneHyperplaneEquiv 𝒜
  let ℓ : Fin S.length → MvPolynomial (Fin (n + 1)) k :=
    fun j ↦ hyperplaneForm (S.get j)
  let ℓ' : Fin (S.map e).length → MvPolynomial (Fin (n + 1)) k :=
    fun j ↦ hyperplaneForm (e.symm ((S.map e).get j))
  let ef : Fin S.length ≃ Fin (S.map e).length := finCongr (List.length_map (as := S) e).symm
  have hℓ : ∀ j, IsEquation (S.get j : Hyperplane k n) (ℓ j) :=
    fun j ↦ isEquation_hyperplaneForm _
  have hcomp : ℓ' ∘ ef = ℓ := by
    funext j
    simp [ℓ, ℓ', ef, List.get_eq_getElem]
  have hℓ' : ∀ j, OrlikSolomon.IsEquation (toDual (ℓ' j)).toAffineMap
      ((S.map e).get j : AffineSubspace k (Fin (n + 1) → k)) := by
    intro j
    have ht := isEquation_coneHyperplaneEquiv (e.symm ((S.map e).get j))
      (isEquation_hyperplaneForm _)
    change OrlikSolomon.IsEquation (toDual (ℓ' j)).toAffineMap
      (e (e.symm ((S.map e).get j)) : AffineSubspace k (Fin (n + 1) → k)) at ht
    simpa only [e.apply_symm_apply] using ht
  rw [isDependent_iff_not_linearIndependent S ℓ hℓ,
    Arrangement.isDependent_iff_not_linearIndependent
      (fun j ↦ (toDual (ℓ' j)).toAffineMap) hℓ'
      ((toProjectiveArrangement 𝒜).cone_isCentral.inter_ne_bot _)]
  apply not_congr
  exact (linearIndependent_toDual_comp_iff (fun j ↦ (hℓ j).isHomogeneous)).symm.trans
    (linearIndependent_equiv' ef (congrArg (fun f ↦ toDual ∘ f) hcomp))

end OrlikSolomon.Interface
