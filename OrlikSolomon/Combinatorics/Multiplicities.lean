/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Combinatorics.Betti
public import OrlikSolomon.Geometry.Projective
public import OrlikSolomon.Presentation.Ordinary

/-!
# Projective Poincaré polynomials and multiplicities

For a nonempty projective arrangement, the Poincaré polynomial is the polynomial of any decone.
The cone polynomial is its product with `1 + X`, so this definition is independent of the
hyperplane and equation chosen for deconing. Its degree-one coefficient is the number of
projective hyperplanes minus one.

## Main definitions and results

* `ProjectiveArrangement.poincarePolynomial` and `ProjectiveArrangement.bettiNumber` are the
  projective polynomial and its natural coefficients, with no chosen hyperplane in their API.
* `ProjectiveArrangement.poincarePolynomial_eq_decone` proves decone independence, and
  `ProjectiveArrangement.poincarePolynomial_cone` gives the factor `1 + X`.
* `ProjectiveArrangement.bettiNumber_one` is the formula `b₁ = |P| - 1`.
* `OrdinaryTheory.projectiveDeconeComponentEquiv` identifies the actual cohomological pieces
  with those of any decone.
* `OrdinaryTheory.nonempty_projective_grading_linearEquiv_bettiNumber` and
  `OrdinaryTheory.nonempty_basis_projective_grading_bettiNumber` give the corresponding module
  multiplicities and diagonal bases, including over the zero ring.

Blueprint: `cor:projective-betti`.
-/

@[expose] public section

noncomputable section

open Module Polynomial

universe u v w z

namespace OrlikSolomon

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace Arrangement

/-- The degree-one coefficient counts the distinct hyperplanes, over the integers. -/
theorem poincarePolynomial_coeff_one [FiniteDimensional k W] (𝒜 : Arrangement k W) :
    𝒜.poincarePolynomial.coeff 1 = 𝒜.card := by
  refine Arrangement.induction
    (motive := fun _ _ _ _ ℬ => ℬ.poincarePolynomial.coeff 1 = (ℬ.card : ℤ)) ?_ ?_ W 𝒜
  · intro V _ _ _
    rw [poincarePolynomial_empty, Polynomial.coeff_one]
    norm_num
  · intro V _ _ _ ℬ H hH hdel _
    rw [poincarePolynomial_coeff_succ_deletion_restriction ℬ hH 0, hdel,
      poincarePolynomial_coeff_zero]
    exact_mod_cast card_deletion_add_one hH

/-- The first natural Betti coefficient counts the distinct affine hyperplanes. -/
@[simp]
theorem bettiNumber_one [FiniteDimensional k W] (𝒜 : Arrangement k W) :
    𝒜.bettiNumber 1 = 𝒜.card := by
  simp only [bettiNumber, poincarePolynomial_coeff_one, Int.toNat_natCast]

end Arrangement

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {ℓ₀ : Dual k W}

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
      exact not_ne_iff.1 (fun h ↦ (slice_inf_toAffineSubspace_ne_bot_iff.1 h) hle)
    rw [inf_of_le_right hle', sub_self, hbot, Arrangement.poincareWeight_bot, mul_zero]
  · have hzero : (0 : W) ∈
        (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace :=
      ⟨(LinearMap.ker ℓ₀).zero_mem, M.zero_mem⟩
    have hne : (LinearMap.ker ℓ₀).toAffineSubspace ⊓ M.toAffineSubspace ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨0, hzero⟩
    have hcodim := hH.codim_inf hne (show ¬M.toAffineSubspace ≤
        (LinearMap.ker ℓ₀).toAffineSubspace from hle)
    have hslice : slice ℓ₀ ⊓ M.toAffineSubspace ≠ ⊥ :=
      slice_inf_toAffineSubspace_ne_bot_iff.2 hle
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

/-- The Poincaré polynomial of the central cone is `1 + X` times the polynomial of any decone.
This is a subset-sum identity, independent of any coefficient ring or cohomology theory.
Blueprint: `cor:projective-betti`. -/
theorem poincarePolynomial_cone_eq_mul_decone [FiniteDimensional k W]
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.poincarePolynomial = (1 + Polynomial.X) * (P.decone ℓ₀).poincarePolynomial := by
  classical
  let H := (LinearMap.ker ℓ₀).toAffineSubspace
  let 𝒜 := P.cone.deletion H
  have hne := ne_zero_of_ker_mem hℓ₀
  have hzero (K : AffineSubspace k W) (hK : K ∈ 𝒜) : (0 : W) ∈ K := by
    obtain ⟨M, _, rfl⟩ := mem_cone.1 ((Arrangement.mem_deletion.1 hK).2)
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
        Arrangement.poincareWeight
          ((sInf (S : Set (AffineSubspace k W))).comap (chart (slice ℓ₀)))) =
        (P.decone ℓ₀).poincarePolynomial := by
    have h := Arrangement.intersectionSum_trace 𝒜 (isHyperplane_slice hne)
      (fun Y : AffineSubspace k W ↦
        Arrangement.poincareWeight (Y.comap (chart (slice ℓ₀)))) (by simp)
    rw [hdel] at h
    simp only [AffineSubspace.comap_inf, comap_chart_self (slice_ne_bot hne), top_inf_eq,
      comap_chart_map_chart] at h
    simpa only [𝒜, H, restriction_deletion_ker_eq_decone hne,
      Arrangement.poincarePolynomial] using h
  rw [Arrangement.poincarePolynomial, Arrangement.intersectionSum_deletion P.cone
    (toAffineSubspace_mem_cone.2 hℓ₀)]
  change 𝒜.intersectionSum Arrangement.poincareWeight -
    (∑ S ∈ 𝒜.hyperplanes.powerset, ((-1 : ℤ) ^ S.card) •
      Arrangement.poincareWeight (H ⊓ sInf (S : Set _))) = _
  rw [Arrangement.intersectionSum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ S ∈ 𝒜.hyperplanes.powerset, ((-1 : ℤ) ^ S.card) •
        ((1 + Polynomial.X) * Arrangement.poincareWeight
          ((sInf (S : Set (AffineSubspace k W))).comap (chart (slice ℓ₀)))) := by
      apply Finset.sum_congr rfl
      intro S hS
      have h0 : (0 : W) ∈ sInf (S : Set (AffineSubspace k W)) :=
        (AffineSubspace.mem_sInf_iff _ _).2 fun K hK ↦
          hzero K (Finset.mem_powerset.1 hS hK)
      rw [← smul_sub, ← AffineSubspace.direction_eq_self_iff_zero_mem.2 h0]
      exact congrArg _ (poincareWeight_sub_inf_ker hne _)
    _ = (1 + Polynomial.X) * (P.decone ℓ₀).poincarePolynomial := by
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [mul_smul_comm]

/-- Every decone has the same Poincaré polynomial, independently of the chosen hyperplane and
its linear equation. -/
theorem poincarePolynomial_decone_eq [FiniteDimensional k W]
    {ℓ₁ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hℓ₁ : LinearMap.ker ℓ₁ ∈ P) :
    (P.decone ℓ₀).poincarePolynomial = (P.decone ℓ₁).poincarePolynomial := by
  have hne : (1 + Polynomial.X : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : ℤ[X] ↦ f.coeff 0) h
    norm_num at h0
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

/-- The natural projective Betti coefficients are independent of all choices. -/
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
degrees. This is a natural-number identity even over zero coefficient rings.
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

namespace OrdinaryTheory

open CategoryTheory SmoothAlg

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {P : ProjectiveArrangement k W} [FiniteDimensional k W] [Nonempty P]
  {ℓ₀ : Dual k W}

/-- Pullback along the decone isomorphism identifies projective cohomology with the cohomology
of any affine decone, over the full coefficient ring. -/
def projectiveDeconeEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    T.C.obj (projectiveComplement P) ≃ₐ[B] T.C.obj (complement (P.decone ℓ₀)) :=
  (T.C.mapIso (deconeIso hℓ₀)).toAlgEquiv

/-- The cohomological decone equivalence is pullback along the geometric decone isomorphism. -/
@[simp]
theorem projectiveDeconeEquiv_apply (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (x : T.C.obj (projectiveComplement P)) :
    T.projectiveDeconeEquiv hℓ₀ x = T.C.map (deconeIso hℓ₀).hom x := rfl

/-- Deconing preserves every cohomological bidegree, as an equivalence of the actual
`R`-submodule pieces. -/
def projectiveDeconeComponentEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (i : ℤ × ℤ) :
    T.grading (projectiveComplement P) i ≃ₗ[R] T.grading (complement (P.decone ℓ₀)) i :=
  (T.isHomogeneousOfShift_map (deconeIso hℓ₀).hom).componentEquiv
    (e := (T.projectiveDeconeEquiv hℓ₀).toLinearEquiv) (add_zero i)

/-- The component equivalence is the decone pullback on underlying classes. -/
@[simp]
theorem coe_projectiveDeconeComponentEquiv_apply (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (i : ℤ × ℤ)
    (x : T.grading (projectiveComplement P) i) :
    (T.projectiveDeconeComponentEquiv hℓ₀ i x : T.C.obj (complement (P.decone ℓ₀))) =
      T.C.map (deconeIso hℓ₀).hom x := rfl

/-- Every projective piece `H^{p,w}` is a direct sum of the projective Betti number of copies of
the coefficient piece `B_{w-p}`. This is an explicit module-equivalence statement, so it also
holds for the zero ring without trying to recover multiplicities from ranks.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_projective_grading_linearEquiv_bettiNumber (P : ProjectiveArrangement k W)
    [Nonempty P] (p : ℕ) (w : ℤ) :
    Nonempty (T.grading (projectiveComplement P) ((p : ℤ), w) ≃ₗ[R]
      (Fin (P.bettiNumber p) → ℬ (w - p))) := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  obtain ⟨e⟩ := T.nonempty_grading_linearEquiv_bettiNumber (P.decone ℓ) p w
  rw [← ProjectiveArrangement.bettiNumber_eq_decone hℓ] at e
  exact ⟨T.projectiveDeconeComponentEquiv hℓ _ ≪≫ₗ e⟩

/-- The projective diagonal piece has a basis indexed by the certified combinatorial Betti
number. This statement requires no nontriviality hypothesis on the coefficient ring.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_basis_projective_grading_bettiNumber (P : ProjectiveArrangement k W)
    [Nonempty P] (q : ℕ) :
    Nonempty (Basis (Fin (P.bettiNumber q)) R
      (T.grading (projectiveComplement P) ((q : ℤ), (q : ℤ)))) := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  obtain ⟨b⟩ := T.nonempty_basis_grading_bettiNumber (P.decone ℓ) q
  rw [← ProjectiveArrangement.bettiNumber_eq_decone hℓ] at b
  exact ⟨b.map (T.projectiveDeconeComponentEquiv hℓ _).symm⟩

/-- The first projective diagonal piece has a basis of cardinality `|P|-1`.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_basis_projective_grading_one (P : ProjectiveArrangement k W) [Nonempty P] :
    Nonempty (Basis (Fin (P.card - 1)) R (T.grading (projectiveComplement P) (1, 1))) := by
  simpa using T.nonempty_basis_projective_grading_bettiNumber P 1

end OrdinaryTheory

end OrlikSolomon
