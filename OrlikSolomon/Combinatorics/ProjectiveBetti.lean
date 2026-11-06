/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Combinatorics.Betti
public import OrlikSolomon.Geometry.ProjectiveArrangement

/-!
# Projective subset polynomials

The cone/decone identities for intersection weights, characteristic polynomials and Poincaré
polynomials are purely combinatorial. The projective Poincaré polynomial is the polynomial of any
decone, independent of the hyperplane and equation used, and its first coefficient is the number
of projective hyperplanes minus one.

* `ProjectiveArrangement.intersectionSum_cone_eq` gives the pairing for arbitrary intersection
  weights and additive maps, without a finite-dimensionality assumption.
* `ProjectiveArrangement.characteristicPolynomial_cone_eq_mul_decone` and
  `ProjectiveArrangement.poincarePolynomial_cone_eq_mul_decone` are its polynomial instances.
* `ProjectiveArrangement.poincarePolynomial_eq_decone` proves independence of the decone.
* `ProjectiveArrangement.bettiNumber_one` computes the first natural coefficient.

Blueprint: the polynomial identities in `cor:projective-betti`.
-/

@[expose] public section

noncomputable section

open Module Polynomial

universe u

namespace OrlikSolomon

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace Arrangement

variable {ℓ₀ : Dual k W}

/-- Taking a trace on a slice pairs the two central-intersection weights with and without the
hyperplane at infinity. Intersections contained in that hyperplane cancel. -/
theorem poincareWeight_sub_inf_ker [FiniteDimensional k W] (hℓ₀ : ℓ₀ ≠ 0)
    (M : Submodule k W) :
    Arrangement.poincareWeight M.toAffineSubspace -
        Arrangement.poincareWeight ((LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace) =
      (1 + Polynomial.X) *
        Arrangement.poincareWeight (M.toAffineSubspace.comap (chart (slice ℓ₀))) := by
  have hM : M.toAffineSubspace ≠ ⊥ := AffineSubspace.toAffineSubspace_ne_bot M
  have hH : IsHyperplane (LinearMap.ker ℓ₀).toAffineSubspace :=
    isHyperplane_toAffineSubspace_iff.2 (isCoatom_ker hℓ₀)
  by_cases hle : M ≤ LinearMap.ker ℓ₀
  · have hle' : M.toAffineSubspace ≤ (LinearMap.ker ℓ₀).toAffineSubspace := hle
    have hbot : M.toAffineSubspace.comap (chart (slice ℓ₀)) = ⊥ := by
      rw [comap_chart_eq_bot_iff (slice_ne_bot hℓ₀)]
      exact not_ne_iff.1 fun h ↦
        (ProjectiveArrangement.slice_inf_toAffineSubspace_ne_bot_iff.1 h) hle
    rw [inf_of_le_right hle', sub_self, hbot, Arrangement.poincareWeight_bot, mul_zero]
  · have hzero : (0 : W) ∈
        (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace :=
      ⟨(LinearMap.ker ℓ₀).zero_mem, M.zero_mem⟩
    have hne : (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨0, hzero⟩
    have hcodim := hH.codim_inf hne (show ¬M.toAffineSubspace ≤
        (LinearMap.ker ℓ₀).toAffineSubspace from hle)
    have hslice : slice ℓ₀ ⊓ M.toAffineSubspace ≠ ⊥ :=
      ProjectiveArrangement.slice_inf_toAffineSubspace_ne_bot_iff.2 hle
    have htrace : M.toAffineSubspace.comap (chart (slice ℓ₀)) ≠ ⊥ :=
      (comap_chart_eq_bot_iff (slice_ne_bot hℓ₀)).not.mpr hslice
    have hcodimSlice := (isHyperplane_slice hℓ₀).codim_inf hslice
      (show ¬M.toAffineSubspace ≤ slice ℓ₀ from fun h ↦ by
        have := h M.zero_mem
        simp at this)
    have hcodimTrace : codim (M.toAffineSubspace.comap (chart (slice ℓ₀))) =
        codim M.toAffineSubspace := by
      have h := codim_inf_eq_codim_comap_chart_add (slice_ne_bot hℓ₀) M.toAffineSubspace
      rw [(isHyperplane_slice hℓ₀).codim_eq_one, hcodimSlice] at h
      omega
    rw [Arrangement.poincareWeight_of_ne_bot hM, Arrangement.poincareWeight_of_ne_bot hne,
      Arrangement.poincareWeight_of_ne_bot htrace, hcodim, hcodimTrace, pow_succ]
    ring

/-- The characteristic weight has the same pairing, with factor `X - 1`. -/
theorem characteristicWeight_sub_inf_ker [FiniteDimensional k W] (hℓ₀ : ℓ₀ ≠ 0)
    (M : Submodule k W) :
    Arrangement.characteristicWeight M.toAffineSubspace -
        Arrangement.characteristicWeight
          ((LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace) =
      (X - 1) *
        Arrangement.characteristicWeight (M.toAffineSubspace.comap (chart (slice ℓ₀))) := by
  have hM : M.toAffineSubspace ≠ ⊥ := AffineSubspace.toAffineSubspace_ne_bot M
  have hH : IsHyperplane (LinearMap.ker ℓ₀).toAffineSubspace :=
    isHyperplane_toAffineSubspace_iff.2 (isCoatom_ker hℓ₀)
  by_cases hle : M ≤ LinearMap.ker ℓ₀
  · have hle' : M.toAffineSubspace ≤ (LinearMap.ker ℓ₀).toAffineSubspace := hle
    have hbot : M.toAffineSubspace.comap (chart (slice ℓ₀)) = ⊥ := by
      rw [comap_chart_eq_bot_iff (slice_ne_bot hℓ₀)]
      exact not_ne_iff.1 fun h ↦
        (ProjectiveArrangement.slice_inf_toAffineSubspace_ne_bot_iff.1 h) hle
    rw [inf_of_le_right hle', sub_self, hbot, Arrangement.characteristicWeight_bot, mul_zero]
  · have hzero : (0 : W) ∈
        (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace :=
      ⟨(LinearMap.ker ℓ₀).zero_mem, M.zero_mem⟩
    have hne : (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨0, hzero⟩
    have hcodim := hH.codim_inf hne (show ¬M.toAffineSubspace ≤
        (LinearMap.ker ℓ₀).toAffineSubspace from hle)
    have hslice : slice ℓ₀ ⊓ M.toAffineSubspace ≠ ⊥ :=
      ProjectiveArrangement.slice_inf_toAffineSubspace_ne_bot_iff.2 hle
    have htrace : M.toAffineSubspace.comap (chart (slice ℓ₀)) ≠ ⊥ :=
      (comap_chart_eq_bot_iff (slice_ne_bot hℓ₀)).not.mpr hslice
    have hcodimSlice := (isHyperplane_slice hℓ₀).codim_inf hslice
      (show ¬M.toAffineSubspace ≤ slice ℓ₀ from fun h ↦ by
        have := h M.zero_mem
        simp at this)
    have hcodimTrace : codim (M.toAffineSubspace.comap (chart (slice ℓ₀))) =
        codim M.toAffineSubspace := by
      have h := codim_inf_eq_codim_comap_chart_add (slice_ne_bot hℓ₀) M.toAffineSubspace
      rw [(isHyperplane_slice hℓ₀).codim_eq_one, hcodimSlice] at h
      omega
    have hdimS := finrank_direction_slice_add_one hℓ₀
    have d1 := codim_add_finrank_direction M.toAffineSubspace
    have d2 := codim_add_finrank_direction
      ((LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace)
    have d3 := codim_add_finrank_direction (M.toAffineSubspace.comap (chart (slice ℓ₀)))
    have e1 : finrank k M.toAffineSubspace.direction =
        finrank k (M.toAffineSubspace.comap (chart (slice ℓ₀))).direction + 1 := by omega
    have e2 : finrank k ((LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace).direction =
        finrank k (M.toAffineSubspace.comap (chart (slice ℓ₀))).direction := by omega
    rw [Arrangement.characteristicWeight_of_ne_bot hM,
      Arrangement.characteristicWeight_of_ne_bot hne,
      Arrangement.characteristicWeight_of_ne_bot htrace, e1, e2, pow_succ]
    ring

end Arrangement

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {ℓ₀ : Dual k W}

/-- Removing the hyperplane at infinity before restricting to its complementary slice has no
effect: that hyperplane has empty trace. -/
theorem restriction_deletion_ker_eq_decone (hℓ₀ : ℓ₀ ≠ 0) :
    (P.cone.deletion (LinearMap.ker ℓ₀).toAffineSubspace).restriction (slice ℓ₀) =
      P.decone ℓ₀ := by
  ext L
  rw [decone, Arrangement.mem_restriction', Arrangement.mem_restriction']
  constructor
  · rintro ⟨hL, K, hK, hKL⟩
    exact ⟨hL, K, (Arrangement.mem_deletion.1 hK).2, hKL⟩
  · rintro ⟨hL, K, hK, hKL⟩
    refine ⟨hL, K, Arrangement.mem_deletion.2 ⟨?_, hK⟩, hKL⟩
    rintro rfl
    exact hL.ne_bot (hKL.symm.trans (comap_ker_chart_slice hℓ₀))

/-- The cone intersection sum is obtained from the decone sum whenever the two central weights
pair through an additive map. This applies to any additive target and requires no finite
dimensionality. -/
theorem intersectionSum_cone_eq {M : Type*} [AddCommGroup M] (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (φ : M →+ M) (w : AffineSubspace k W → M) (v : AffineSubspace k (slice ℓ₀).direction → M)
    (hv : v ⊥ = 0)
    (hw : ∀ N : Submodule k W, w N.toAffineSubspace -
        w ((LinearMap.ker ℓ₀).toAffineSubspace ⊓ N.toAffineSubspace) =
      φ (v (N.toAffineSubspace.comap (chart (slice ℓ₀))))) :
    P.cone.intersectionSum w = φ ((P.decone ℓ₀).intersectionSum v) := by
  classical
  let H := (LinearMap.ker ℓ₀).toAffineSubspace
  let 𝒜 := P.cone.deletion H
  have hne := ProjectiveArrangement.ne_zero_of_ker_mem hℓ₀
  have hzero (K : AffineSubspace k W) (hK : K ∈ 𝒜) : (0 : W) ∈ K := by
    obtain ⟨M, _, rfl⟩ := ProjectiveArrangement.mem_cone.1 ((Arrangement.mem_deletion.1 hK).2)
    exact M.zero_mem
  have hslice : slice ℓ₀ ∉ 𝒜 := fun h ↦ by
    have := hzero _ h
    simp at this
  have hdel : 𝒜.deletion (slice ℓ₀) = 𝒜 := by
    ext K
    rw [Arrangement.mem_deletion]
    exact ⟨And.right, fun h ↦ ⟨fun hK ↦ hslice (hK ▸ h), h⟩⟩
  have hsum :
      (∑ S ∈ 𝒜.hyperplanes.powerset, ((-1 : ℤ) ^ S.card) •
        v ((sInf (S : Set (AffineSubspace k W))).comap (chart (slice ℓ₀)))) =
        (P.decone ℓ₀).intersectionSum v := by
    have h := Arrangement.intersectionSum_trace 𝒜 (isHyperplane_slice hne)
      (fun Y : AffineSubspace k W ↦ v (Y.comap (chart (slice ℓ₀)))) (by simpa using hv)
    rw [hdel] at h
    simp only [AffineSubspace.comap_inf, comap_chart_self (slice_ne_bot hne), top_inf_eq,
      comap_chart_map_chart] at h
    simpa only [𝒜, H, ProjectiveArrangement.restriction_deletion_ker_eq_decone hne] using h
  rw [Arrangement.intersectionSum_deletion P.cone
    (ProjectiveArrangement.toAffineSubspace_mem_cone.2 hℓ₀)]
  change 𝒜.intersectionSum w -
    (∑ S ∈ 𝒜.hyperplanes.powerset, ((-1 : ℤ) ^ S.card) • w (H ⊓ sInf (S : Set _))) = _
  rw [Arrangement.intersectionSum, ← Finset.sum_sub_distrib, ← hsum, map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have h0 : (0 : W) ∈ sInf (S : Set (AffineSubspace k W)) :=
    (AffineSubspace.mem_sInf_iff _ _).2 fun K hK ↦
      hzero K (Finset.mem_powerset.1 hS hK)
  rw [← smul_sub, map_zsmul, ← AffineSubspace.direction_eq_self_iff_zero_mem.2 h0]
  exact congrArg _ (hw _)

/-- The Poincaré polynomial of the central cone is `1 + X` times the polynomial of any decone.
This is a subset-sum identity, independent of any coefficient ring or cohomology theory.
Blueprint: `cor:projective-betti`. -/
theorem poincarePolynomial_cone_eq_mul_decone [FiniteDimensional k W]
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.poincarePolynomial = (1 + Polynomial.X) * (P.decone ℓ₀).poincarePolynomial := by
  have h := intersectionSum_cone_eq hℓ₀ (AddMonoidHom.mulLeft (1 + Polynomial.X : ℤ[X]))
    Arrangement.poincareWeight Arrangement.poincareWeight Arrangement.poincareWeight_bot
    (Arrangement.poincareWeight_sub_inf_ker (ne_zero_of_ker_mem hℓ₀))
  simpa only [Arrangement.poincarePolynomial, AddMonoidHom.coe_mulLeft] using h

/-- The characteristic polynomial of the cone is `X - 1` times the polynomial of any decone.
This is the characteristic-weight instance of `intersectionSum_cone_eq`. -/
theorem characteristicPolynomial_cone_eq_mul_decone [FiniteDimensional k W]
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.characteristicPolynomial = (X - 1) * (P.decone ℓ₀).characteristicPolynomial := by
  have h := intersectionSum_cone_eq hℓ₀ (AddMonoidHom.mulLeft (X - 1 : ℤ[X]))
    Arrangement.characteristicWeight Arrangement.characteristicWeight
    Arrangement.characteristicWeight_bot
    (Arrangement.characteristicWeight_sub_inf_ker (ProjectiveArrangement.ne_zero_of_ker_mem hℓ₀))
  simpa only [Arrangement.characteristicPolynomial, AddMonoidHom.coe_mulLeft] using h

/-- Every decone has the same Poincaré polynomial, independently of the chosen hyperplane and
its linear equation. -/
theorem poincarePolynomial_decone_eq [FiniteDimensional k W]
    {ℓ₁ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hℓ₁ : LinearMap.ker ℓ₁ ∈ P) :
    (P.decone ℓ₀).poincarePolynomial = (P.decone ℓ₁).poincarePolynomial := by
  have hne : (1 + Polynomial.X : ℤ[X]) ≠ 0 := by
    simpa [add_comm] using Polynomial.X_add_C_ne_zero (1 : ℤ)
  apply mul_left_cancel₀ hne
  rw [← poincarePolynomial_cone_eq_mul_decone hℓ₀,
    ← poincarePolynomial_cone_eq_mul_decone hℓ₁]

/-- The projective Poincaré polynomial is the polynomial of any decone. Its value is independent
of the equation and hyperplane used in this definition, by `poincarePolynomial_eq_decone`.
The empty projective arrangement is excluded. Blueprint: `cor:projective-betti`. -/
def poincarePolynomial (P : ProjectiveArrangement k W) [Nonempty P] : ℤ[X] :=
  (P.decone P.exists_ker_mem.choose).poincarePolynomial

/-- The projective Poincaré polynomial agrees with the polynomial of every decone.
Blueprint: `cor:projective-betti`. -/
theorem poincarePolynomial_eq_decone [FiniteDimensional k W] [Nonempty P]
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) : P.poincarePolynomial = (P.decone ℓ₀).poincarePolynomial :=
  poincarePolynomial_decone_eq P.exists_ker_mem.choose_spec hℓ₀

/-- The cone polynomial has the factor `1 + X`, with quotient the projective polynomial.
Blueprint: `cor:projective-betti`. -/
theorem poincarePolynomial_cone [FiniteDimensional k W] (P : ProjectiveArrangement k W)
    [Nonempty P] :
    P.cone.poincarePolynomial = (1 + Polynomial.X) * P.poincarePolynomial :=
  poincarePolynomial_cone_eq_mul_decone P.exists_ker_mem.choose_spec

/-- The degree-`q` coefficient of the projective Poincaré polynomial, as a natural number.
Nonnegativity is proved before identifying this with the original integer coefficient.
Blueprint: `cor:projective-betti`. -/
def bettiNumber (P : ProjectiveArrangement k W) [Nonempty P] (q : ℕ) : ℕ :=
  (P.poincarePolynomial.coeff q).toNat

/-- Projective Betti numbers are the natural Betti numbers of any decone. -/
theorem bettiNumber_eq_decone [FiniteDimensional k W] [Nonempty P]
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (q : ℕ) : P.bettiNumber q = (P.decone ℓ₀).bettiNumber q := by
  rw [bettiNumber, poincarePolynomial_eq_decone hℓ₀, Arrangement.bettiNumber]

/-- Every coefficient of the projective polynomial is nonnegative, before any passage to natural
Betti numbers. -/
theorem poincarePolynomial_coeff_nonneg [FiniteDimensional k W] (P : ProjectiveArrangement k W)
    [Nonempty P] (q : ℕ) : 0 ≤ P.poincarePolynomial.coeff q := by
  rw [poincarePolynomial_eq_decone P.exists_ker_mem.choose_spec]
  exact Arrangement.poincarePolynomial_coeff_nonneg _ q

/-- Casting a projective Betti number to `ℤ` recovers the original polynomial coefficient. -/
@[simp]
theorem natCast_bettiNumber [FiniteDimensional k W] (P : ProjectiveArrangement k W) [Nonempty P]
    (q : ℕ) : (P.bettiNumber q : ℤ) = P.poincarePolynomial.coeff q :=
  Int.toNat_of_nonneg (P.poincarePolynomial_coeff_nonneg q)

/-- The projective polynomial has constant coefficient one. -/
@[simp]
theorem poincarePolynomial_coeff_zero [FiniteDimensional k W] (P : ProjectiveArrangement k W)
    [Nonempty P] : P.poincarePolynomial.coeff 0 = 1 := by
  rw [poincarePolynomial_eq_decone P.exists_ker_mem.choose_spec]
  exact Arrangement.poincarePolynomial_coeff_zero _

/-- Every nonempty projective arrangement has zeroth Betti number one. -/
@[simp]
theorem bettiNumber_zero [FiniteDimensional k W] (P : ProjectiveArrangement k W) [Nonempty P] :
    P.bettiNumber 0 = 1 := by
  simp only [bettiNumber, poincarePolynomial_coeff_zero]
  rfl

/-- Coefficients of the cone polynomial are the sum of the projective coefficient and its
degree-shifted predecessor. -/
theorem poincarePolynomial_cone_coeff_succ [FiniteDimensional k W]
    (P : ProjectiveArrangement k W) [Nonempty P] (q : ℕ) :
    P.cone.poincarePolynomial.coeff (q + 1) =
      P.poincarePolynomial.coeff (q + 1) + P.poincarePolynomial.coeff q := by
  rw [poincarePolynomial_cone, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul]

/-- The cone Betti numbers are the sum of the projective Betti numbers in two consecutive
degrees, as a natural-number identity.
Blueprint: `cor:projective-betti`. -/
theorem bettiNumber_cone_succ [FiniteDimensional k W] (P : ProjectiveArrangement k W)
    [Nonempty P] (q : ℕ) :
    P.cone.bettiNumber (q + 1) = P.bettiNumber (q + 1) + P.bettiNumber q := by
  apply Int.ofNat_injective
  change (P.cone.bettiNumber (q + 1) : ℤ) =
    ((P.bettiNumber (q + 1) + P.bettiNumber q : ℕ) : ℤ)
  rw [Nat.cast_add, Arrangement.natCast_bettiNumber, natCast_bettiNumber,
    natCast_bettiNumber, poincarePolynomial_cone_coeff_succ]

/-- The first projective Betti coefficient is the number of hyperplanes minus one, including
when there is only one hyperplane. This is an integer coefficient identity.
Blueprint: `cor:projective-betti`. -/
theorem poincarePolynomial_coeff_one [FiniteDimensional k W] (P : ProjectiveArrangement k W)
    [Nonempty P] : P.poincarePolynomial.coeff 1 = (P.card : ℤ) - 1 := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  rw [poincarePolynomial_eq_decone hℓ, Arrangement.poincarePolynomial_coeff_one]
  have h := card_decone_add_one hℓ
  omega

/-- The first projective Betti number is the number of hyperplanes minus one.
Blueprint: `cor:projective-betti`. -/
@[simp]
theorem bettiNumber_one [FiniteDimensional k W] (P : ProjectiveArrangement k W) [Nonempty P] :
    P.bettiNumber 1 = P.card - 1 := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  rw [bettiNumber_eq_decone hℓ, Arrangement.bettiNumber_one]
  have h := card_decone_add_one hℓ
  omega

end ProjectiveArrangement

end OrlikSolomon
