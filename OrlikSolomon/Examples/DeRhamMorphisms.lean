/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.DeRhamMaps
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Unit changes, non-flat morphisms and ramification

These are the three concrete morphisms of `prop:dr-morphism-examples`. The unit change
`z ↦ xy` is flat and has logarithmic residue one. The map with the additional variable
`v ↦ 0` is not flat, but residue and Gysin naturality still apply. The ramified map
`z ↦ x²` is not a morphism of the fixed divisor pairs over a nonzero coefficient ring;
its pulled-back logarithmic form has residue two.

## Main results

* `unitChangeHom`, `flat_unitChangeHom_ambient` and `unitChange_logResidue_theta` give the
  one-variable unit change, its flatness and its residue.
* `nonFlatHom_gysin_map` and `nonFlatHom_residue_map` apply naturality to the existing
  genuinely non-flat morphism `nonFlatHom`.
* `ramifiedAmbient_not_associated` and `ramifiedAmbient_not_pairHom` exclude the ramified
  map from the fixed-pair interface.
* `ramified_logResidue_theta` computes its form residue over every coefficient ring.

Only the cohomological residue statements use the integration hypothesis. Formulas for
forms also apply in positive characteristic and over the zero ring.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.DeRham.Examples

open CategoryTheory SmoothAlg DivisorPair
open scoped Polynomial LaurentPolynomial

variable (k : Type*) [CommRing k]

/-- The fixed-pair morphism `k[z] → k[y,y⁻¹][x]`, `z ↦ yx`, with `y` an ambient unit.

Blueprint: `prop:dr-morphism-examples`. -/
def unitChangeHom : standardPair (point k) ⟶ standardPair (laurent (point k)) :=
  standardMap (fromPoint _) (laurentT (point k))

/-- The unit-change morphism sends the source equation to `y` times the target equation. -/
theorem unitChangeHom_ambient_polynomialX :
    (unitChangeHom k).ambient (polynomialX (point k)) =
      polynomialC _ (laurentT (point k) : laurent (point k)) * polynomialX _ :=
  polynomialLift_polynomialX _ _

private def polynomialLaurentSwap :
    (LaurentPolynomial k)[X] ≃ₐ[k] LaurentPolynomial k[X] :=
  AddMonoidAlgebra.commAlgEquiv k

private theorem polynomialLaurentSwap_map (p : k[X]) :
    polynomialLaurentSwap k (Polynomial.map (LaurentPolynomial.C : k →+* LaurentPolynomial k) p) =
      LaurentPolynomial.C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.map_monomial]
    change AddMonoidAlgebra.commAlgEquiv k
      (AddMonoidAlgebra.single n (AddMonoidAlgebra.single (0 : ℤ) c)) =
      AddMonoidAlgebra.single (0 : ℤ) (AddMonoidAlgebra.single n c)
    exact AddMonoidAlgebra.commAlgEquiv_single_single _ _ _

private theorem flat_polynomial_laurent_map :
    (Polynomial.mapRingHom (LaurentPolynomial.C : k →+* LaurentPolynomial k)).Flat := by
  have h : (LaurentPolynomial.C : k[X] →+* LaurentPolynomial k[X]).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have he := RingHom.Flat.of_bijective
    (f := (polynomialLaurentSwap k).symm.toRingHom) (polynomialLaurentSwap k).symm.bijective
  convert h.comp he using 1
  apply RingHom.ext
  intro p
  apply (polynomialLaurentSwap k).injective
  exact (polynomialLaurentSwap_map k p).trans
    ((polynomialLaurentSwap k).apply_symm_apply (LaurentPolynomial.C p)).symm

/-- The actual map `z ↦ yx` is flat: coefficient extension is a Laurent extension, and
scaling the polynomial coordinate by the unit `y` is an automorphism.

Blueprint: `prop:dr-morphism-examples`. -/
theorem flat_unitChangeHom_ambient : (algHom (unitChangeHom k).ambient).toRingHom.Flat := by
  let e := Polynomial.algEquivCMulXAddC (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial k) 0
  have he := RingHom.Flat.of_bijective (f := e.toRingHom) e.bijective
  have h := (flat_polynomial_laurent_map k).comp he
  let ψ : k[X] →+* (LaurentPolynomial k)[X] := (algHom (unitChangeHom k).ambient).toRingHom
  change ψ.Flat
  have hψ : ψ = e.toRingHom.comp (Polynomial.mapRingHom LaurentPolynomial.C) := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply]
      change ψ (Polynomial.C c) = e ((Polynomial.map LaurentPolynomial.C) (Polynomial.C c))
      rw [Polynomial.map_C]
      simp only [e, Polynomial.algEquivCMulXAddC_apply, Polynomial.aeval_C]
      have hc := (algHom (unitChangeHom k).ambient).commutes c
      change ψ (algebraMap k k[X] c) = algebraMap k (LaurentPolynomial k)[X] c at hc
      simpa only [Polynomial.algebraMap_apply, LaurentPolynomial.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] using hc
    · rw [RingHom.comp_apply]
      change ψ Polynomial.X = e ((Polynomial.map LaurentPolynomial.C) Polynomial.X)
      rw [Polynomial.map_X]
      rw [Polynomial.algEquivCMulXAddC_apply, Polynomial.aeval_X, Polynomial.C_0, add_zero]
      exact unitChangeHom_ambient_polynomialX k
  rw [hψ]
  exact h

/-- Pulling back `dz/z` gives `dx/x + dy/y`, with the second term regular in the ambient
algebra. -/
theorem unitChange_map_theta :
    Forms.map (algHom (unitChangeHom k).compl)
        (theta k (standardPair (point k)).eqn (standardPair (point k)).compl) =
      theta k (standardPair (laurent (point k))).eqn
        (standardPair (laurent (point k))).compl +
        Forms.map (IsScalarTower.toAlgHom k (standardPair (laurent (point k))).ambient
          (standardPair (laurent (point k))).compl)
          (dlog k (show (standardPair (laurent (point k))).ambientˣ from
            mapUnits (polynomialC (laurent (point k))) (laurentT (point k)))) :=
  (unitChangeHom k).isPairHom.map_theta
    (u := mapUnits (polynomialC (laurent (point k))) (laurentT (point k)))
    (unitChangeHom_ambient_polynomialX k)

/-- The pulled-back form `d(xy)/(xy)` has residue one, over every commutative coefficient ring.

Blueprint: `prop:dr-morphism-examples`. -/
theorem unitChange_logResidue_theta :
    logResidue (standardPair (laurent (point k))).compl
      (standardPair (laurent (point k))).isSmoothPrincipalPair
      (logMap (unitChangeHom k).isPairHom
        ⟨theta k (standardPair (point k)).eqn (standardPair (point k)).compl,
          theta_mem_logForms _ _ _⟩) = 1 := by
  exact (logResidue_logMap (unitChangeHom k).isPairHom
    (standardPair (point k)).isSmoothPrincipalPair
    (standardPair (laurent (point k))).isSmoothPrincipalPair _).trans
      ((congrArg (Forms.map (algHom (unitChangeHom k).closed))
        (logResidue_theta (standardPair (point k)).isSmoothPrincipalPair)).trans (map_one _))

/-- Cohomological residue of the same pulled-back logarithmic form is one, under the
integration hypothesis. -/
theorem unitChange_residue_theta (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    residue (standardPair (laurent (point k))).compl hUnits
      (standardPair (laurent (point k))).isSmoothPrincipalPair
      (Cohomology.map (algHom (unitChangeHom k).compl)
        (Cohomology.mk (theta k (standardPair (point k)).eqn (standardPair (point k)).compl)
          (d_theta _ _ _))) = 1 := by
  rw [residue_map hUnits (unitChangeHom k).isPairHom
    (standardPair (point k)).isSmoothPrincipalPair
    (standardPair (laurent (point k))).isSmoothPrincipalPair,
    residue_mk_theta_localization _ hUnits (standardPair (point k)).isSmoothPrincipalPair,
    map_one]

/-- Gysin naturality holds for the actual non-flat map `z ↦ xy`, `v ↦ 0` from
`not_flat_nonFlatAmbient`. -/
theorem nonFlatHom_gysin_map (c : Cohomology k (polynomial (point k))) :
    gysin (standardPair (laurent (point k))).compl
      (standardPair (laurent (point k))).isSmoothPrincipalPair
        (Cohomology.map (algHom (nonFlatHom k).closed) c) =
      Cohomology.map (algHom (nonFlatHom k).ambient)
        (gysin (standardPair (polynomial (point k))).compl
          (standardPair (polynomial (point k))).isSmoothPrincipalPair
          c) :=
  gysin_map (nonFlatHom k).isPairHom _ _ c

/-- Residue naturality holds for the actual non-flat map, with no flatness assumption. -/
theorem nonFlatHom_residue_map (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (c : Cohomology k (standardPair (polynomial (point k))).compl) :
    residue (standardPair (laurent (point k))).compl hUnits
      (standardPair (laurent (point k))).isSmoothPrincipalPair
        (Cohomology.map (algHom (nonFlatHom k).compl) c) =
      Cohomology.map (algHom (nonFlatHom k).closed)
        (residue (standardPair (polynomial (point k))).compl hUnits
          (standardPair (polynomial (point k))).isSmoothPrincipalPair c) :=
  residue_map hUnits (nonFlatHom k).isPairHom _ _ c

/-- Naturality of the form residue for the genuinely non-flat morphism holds over every
coefficient ring, without the integration hypothesis. -/
theorem nonFlatHom_logResidue_map
    (x : logForms k (standardPair (polynomial (point k))).eqn
      (standardPair (polynomial (point k))).compl) :
    logResidue (standardPair (laurent (point k))).compl
        (standardPair (laurent (point k))).isSmoothPrincipalPair
        (logMap (nonFlatHom k).isPairHom x) =
      Forms.map (algHom (nonFlatHom k).closed)
        (logResidue (standardPair (polynomial (point k))).compl
          (standardPair (polynomial (point k))).isSmoothPrincipalPair x) :=
  logResidue_logMap (nonFlatHom k).isPairHom _ _ x

/-- The ambient algebra map `k[z] → k[x]`, `z ↦ x²`. -/
def ramifiedAmbient : polynomial (point k) ⟶ polynomial (point k) :=
  polynomialLift (polynomialC (point k)) (polynomialX (point k) ^ 2)

/-- The localization map `k[z,z⁻¹] → k[x,x⁻¹]`, `z ↦ x²`. -/
def ramifiedComplement : (standardPair (point k)).compl ⟶ (standardPair (point k)).compl :=
  laurentLift (fromPoint (standardPair (point k)).compl)
    ((standardPair (point k)).eqnUnit ^ 2)

/-- The ramified ambient map sends the source coordinate to the square of the target coordinate. -/
@[simp]
theorem ramifiedAmbient_polynomialX :
    ramifiedAmbient k (polynomialX (point k)) = polynomialX (point k) ^ 2 :=
  polynomialLift_polynomialX _ _

/-- The ramified localization map sends the invertible coordinate to its square. -/
theorem ramifiedComplement_laurentT :
    mapUnits (ramifiedComplement k) (laurentT (point k)) =
      (standardPair (point k)).eqnUnit ^ 2 :=
  mapUnits_laurentLift_laurentT _ _

/-- The ambient and localization maps for squaring commute with restriction to the complement. -/
theorem ramifiedAmbient_comp_j :
    ramifiedAmbient k ≫ (standardPair (point k)).j =
      (standardPair (point k)).j ≫ ramifiedComplement k := by
  apply polynomial_hom_ext
  · apply ConcreteCategory.ext
    apply DFunLike.ext
    intro c
    change (standardPair (point k)).j (ramifiedAmbient k (polynomialC (point k) c)) =
      ramifiedComplement k ((standardPair (point k)).j (polynomialC (point k) c))
    have hC : ramifiedAmbient k (polynomialC (point k) c) = polynomialC (point k) c :=
      polynomialLift_polynomialC _ _ c
    rw [hC]
    have hJ : (standardPair (point k)).j (polynomialC (point k) c) =
        laurentC (point k) c := polynomialToLaurent_polynomialC _ _
    rw [hJ]
    exact (laurentLift_laurentC _ _ c).symm
  · change polynomialToLaurent (point k) (ramifiedAmbient k (polynomialX (point k))) =
      ramifiedComplement k (polynomialToLaurent (point k) (polynomialX (point k)))
    rw [ramifiedAmbient_polynomialX, map_pow, polynomialToLaurent_polynomialX]
    have h := (ramifiedComplement_laurentT k).trans
      (congrArg (fun u : (standardPair (point k)).complˣ => u ^ 2)
        (standardPair_eqnUnit (point k)))
    exact (congrArg Units.val h).symm

/-- Squaring the equation is not a unit change over a nonzero coefficient ring.

Blueprint: `prop:dr-morphism-examples`. -/
theorem ramifiedAmbient_not_associated [Nontrivial k] :
    ¬ Associated (ramifiedAmbient k (polynomialX (point k))) (polynomialX (point k)) := by
  rw [ramifiedAmbient_polynomialX]
  change ¬ Associated (Polynomial.X ^ 2 : k[X]) Polynomial.X
  rintro ⟨u, hu⟩
  have h := congrArg (fun p : k[X] => p.coeff 1) hu
  have hzero : (Polynomial.X ^ 2 * (u : k[X])).coeff 1 = 0 :=
    by simpa using Polynomial.coeff_X_pow_mul' (u : k[X]) 2 1
  exact zero_ne_one (hzero.symm.trans (h.trans Polynomial.coeff_X_one))

/-- No morphism of the fixed pairs has ambient map `z ↦ x²`: the associated-equation field fails.

Blueprint: `prop:dr-morphism-examples`. -/
theorem ramifiedAmbient_not_pairHom [Nontrivial k] :
    ¬ ∃ F : standardPair (point k) ⟶ standardPair (point k), F.ambient = ramifiedAmbient k := by
  rintro ⟨F, hF⟩
  exact ramifiedAmbient_not_associated k (hF ▸ F.associated_eqn)

/-- The actual pullback along `z ↦ x²` of `dz/z` is `2 dx/x`, including in characteristic two
and over the zero ring. -/
theorem ramified_map_theta :
    Forms.map (algHom (ramifiedComplement k))
        (theta k (standardPair (point k)).eqn (standardPair (point k)).compl) =
      2 • theta k (standardPair (point k)).eqn (standardPair (point k)).compl := by
  rw [DivisorPair.theta_eq_dlog_eqnUnit, Forms.map_dlog]
  have h : Units.map (algHom (ramifiedComplement k) : _ →* _)
      (standardPair (point k)).eqnUnit = (standardPair (point k)).eqnUnit ^ 2 :=
    (congrArg (mapUnits (ramifiedComplement k))
      (standardPair_eqnUnit (point k))).trans (ramifiedComplement_laurentT k)
  rw [h, pow_two, dlog_mul]
  exact (two_smul ℕ _).symm

/-- The ramified pullback is logarithmic even though it does not define a fixed-pair morphism. -/
theorem ramified_map_theta_mem_logForms :
    Forms.map (algHom (ramifiedComplement k))
        (theta k (standardPair (point k)).eqn (standardPair (point k)).compl) ∈
      logForms k (standardPair (point k)).eqn (standardPair (point k)).compl := by
  rw [ramified_map_theta]
  exact Subalgebra.nsmul_mem _ (theta_mem_logForms _ _ _) _

/-- The form residue of the ramified pullback is two, over every coefficient ring.

Blueprint: `prop:dr-morphism-examples`. -/
theorem ramified_logResidue_theta :
    logResidue (standardPair (point k)).compl (standardPair (point k)).isSmoothPrincipalPair
      ⟨Forms.map (algHom (ramifiedComplement k))
        (theta k (standardPair (point k)).eqn (standardPair (point k)).compl),
        ramified_map_theta_mem_logForms k⟩ = 2 := by
  have h : (⟨Forms.map (algHom (ramifiedComplement k))
      (theta k (standardPair (point k)).eqn (standardPair (point k)).compl),
      ramified_map_theta_mem_logForms k⟩ :
      logForms k (standardPair (point k)).eqn (standardPair (point k)).compl) =
      2 • ⟨theta k _ _, theta_mem_logForms _ _ _⟩ :=
    Subtype.ext (ramified_map_theta k)
  rw [h, map_nsmul, logResidue_theta, two_smul, one_add_one_eq_two]

/-- For nonzero coefficients, the ramified form residue is not one. Characteristic zero is
unnecessary for distinguishing two from one. -/
theorem ramified_logResidue_theta_ne_one [Nontrivial k] :
    logResidue (standardPair (point k)).compl (standardPair (point k)).isSmoothPrincipalPair
      ⟨Forms.map (algHom (ramifiedComplement k))
        (theta k (standardPair (point k)).eqn (standardPair (point k)).compl),
        ramified_map_theta_mem_logForms k⟩ ≠ 1 := by
  rw [ramified_logResidue_theta]
  intro h
  have : (1 : Forms k (standardPair (point k)).closed) = 0 :=
    add_left_cancel (a := 1) (by simpa only [one_add_one_eq_two, add_zero] using h)
  have : Nontrivial (standardPair (point k)).closed := inferInstanceAs (Nontrivial k)
  exact one_ne_zero ‹(1 : Forms k (standardPair (point k)).closed) = 0›

/-- Under the integration hypothesis, the actual pulled-back cohomology class also has residue
two. The corresponding form statement needs no integration hypothesis. -/
theorem ramified_residue_theta (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    residue (standardPair (point k)).compl hUnits (standardPair (point k)).isSmoothPrincipalPair
      (Cohomology.map (algHom (ramifiedComplement k))
        (Cohomology.mk (theta k (standardPair (point k)).eqn (standardPair (point k)).compl)
          (d_theta _ _ _))) = 2 := by
  rw [Cohomology.map_mk,
    residue_mk_of_mem_logForms hUnits (standardPair (point k)).isSmoothPrincipalPair
      (ramified_map_theta_mem_logForms k)]
  exact (Cohomology.mk_congr (ramified_logResidue_theta k) _).trans (by
    simpa only [map_ofNat] using
      Cohomology.mk_algebraMap (k := k) (A := (standardPair (point k)).closed) (2 : k) (by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, d_one, smul_zero]))

end OrlikSolomon.DeRham.Examples
