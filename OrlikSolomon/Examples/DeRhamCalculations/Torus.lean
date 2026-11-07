/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Instance
public import OrlikSolomon.Cohomology.Logarithms
public import OrlikSolomon.Examples.DeRhamMaps

/-!
# Punctured-line and two-torus calculations

The actual de Rham ordinary theory supplies the Laurent product splitting; forgetting its
coefficient variable gives the untwisted calculations without a Künneth assumption.

## Main definitions and results

* `gmCohomologyEquiv` and its degree criteria: the punctured-line basis `1, [dx/x]`.
* `gm_residue_theta` and `gm_normalized_tau`: the residue and Laurent-twisted normalization.
* `torusCohomologyEquiv`, `torusCohomologyEquiv_apply` and its degree criterion: the ordered
  basis `1, θx, θy, θxθy` of the two-torus, in degrees `0, 1, 1, 2`.
* `torusX_mul_self`, `torusY_mul_self` and `torus_anticommute`: its exterior multiplication.
* `torusResidueX_top` and `torus_residue_inner_mul_outer`: the opposite residue signs on
  the same ordered top class, using the actual coordinate interchange for the first map.

Blueprint: `prop:dr-gm-example`, `prop:dr-torus-example`.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace OrlikSolomon.DeRham.Examples
open SmoothAlg DivisorPair
private def unitClass {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (u : Aˣ) : Cohomology k A := Cohomology.mk (dlog k u) (d_dlog k u)

private theorem map_unitClass {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (u : Aˣ) :
    Cohomology.map f (unitClass u) = unitClass (Units.map (f : A →* B) u) :=
  (Cohomology.map_mk f _ _).trans (Cohomology.mk_congr (Forms.map_dlog f u) _)

variable (k : Type*) [Field k] [CharZero k]

/-- The class of the logarithmic coordinate form on `A[y,y⁻¹]`. -/
def laurentThetaClass (A : SmoothAlg k) : Cohomology k (laurent A) :=
  Cohomology.mk (dlog k (laurentT A)) (d_dlog k _)

omit [CharZero k] in
private theorem laurentThetaClass_mem_degree (A : SmoothAlg k) :
    laurentThetaClass k A ∈ Cohomology.degree k (laurent A) 1 :=
  Cohomology.mk_mem_degree (dlog_mem_exteriorPower_one k _) _

private def forgetTwist (A : SmoothAlg k) :
    (ordinaryTheory k).C.obj A →ₐ[k] Cohomology k A := TwistedCohomology.evalOne k A

private theorem forgetTwist_map {A D : SmoothAlg k} (f : A ⟶ D)
    (x : (ordinaryTheory k).C.obj A) :
    forgetTwist k D ((ordinaryTheory k).C.map f x) =
      Cohomology.map (algHom f) (forgetTwist k A x) :=
  TwistedCohomology.evalOne_map (algHom f) x

private theorem forgetTwist_twistedClass (A : SmoothAlg k) (w : ℤ) (c : Cohomology k A) :
    forgetTwist k A (twistedClass w c) = c := evalOne_twistedClass w c

/-- The punctured-line generator `[dx/x]` has actual untwisted residue one. -/
theorem gm_residue_theta : residue (standardPair (point k)).compl (isUnit_natCast_add_one k)
    (standardPair (point k)).isSmoothPrincipalPair (laurentThetaClass k (point k)) = 1 := by
  have hθ : theta k (standardPair (point k)).eqn (standardPair (point k)).compl =
      dlog k (laurentT (point k)) :=
    (standardPair (point k)).theta_eq_dlog_eqnUnit.trans
      (congrArg (dlog k) (standardPair_eqnUnit _))
  exact (congrArg (residue (standardPair (point k)).compl (isUnit_natCast_add_one k)
    (standardPair (point k)).isSmoothPrincipalPair)
    (Cohomology.mk_congr hθ _)).symm.trans (residue_mk_theta_localization _ _ _)

private theorem tau_eq_twistedClass :
    (ordinaryTheory k).tau = twistedClass 1 (laurentThetaClass k (point k)) := by
  symm
  apply (ordinaryTheory k).eq_tau_of_mem_grading
  · exact twistedClass_mem_grading_natCast_iff.2 (laurentThetaClass_mem_degree k _)
  · rw [stdResidue_twistedClass, gm_residue_theta]
    exact twistedClass_zero_one

/-- The normalized twisted punctured-line class is exactly `[dx/x]T`. -/
theorem gm_normalized_tau :
    (ordinaryTheory k).tau = twistedClass 1 (laurentThetaClass k (point k)) :=
  tau_eq_twistedClass k

private theorem logClass_laurentT_eq_twistedClass (A : SmoothAlg k) :
    (ordinaryTheory k).logClass (laurentT A) = twistedClass 1 (laurentThetaClass k A) := by
  rw [OrdinaryTheory.logClass, tau_eq_twistedClass, map_twistedClass]
  apply congrArg (twistedClass 1)
  change Cohomology.map (algHom (gmHom (laurentT A)))
    (Cohomology.mk (dlog k (laurentT (point k))) _) =
    Cohomology.mk (dlog k (laurentT A)) _
  rw [Cohomology.map_mk]
  exact Cohomology.mk_congr ((Forms.map_dlog _ _).trans
    (congrArg (dlog k) (mapUnits_gmHom_laurentT _))) _

/-- The untwisted map `(b,c) ↦ b + [dy/y]c` on a Laurent extension. -/
def laurentCohomologyMap (A : SmoothAlg k) :
    (Cohomology k A × Cohomology k A) →ₗ[k] Cohomology k (laurent A) :=
  ((Cohomology.map (algHom (laurentC A))).toLinearMap.comp (LinearMap.fst k _ _)) +
    (LinearMap.mulLeft k (laurentThetaClass k A)).comp
      ((Cohomology.map (algHom (laurentC A))).toLinearMap.comp (LinearMap.snd k _ _))

private theorem laurentCohomologyMap_twistedClass (A : SmoothAlg k) (b c : Cohomology k A) :
    (ordinaryTheory k).gmProductEquiv A (twistedClass 0 b, twistedClass (-1) c) =
      twistedClass 0 (laurentCohomologyMap k A (b, c)) := by
  simp only [OrdinaryTheory.gmProductEquiv_apply, logClass_laurentT_eq_twistedClass,
    map_twistedClass, twistedClass_mul_twistedClass, Int.reduceAdd]
  exact ((twistedClass 0).map_add _ _).symm

private theorem forgetTwist_gmProductEquiv (A : SmoothAlg k)
    (b c : (ordinaryTheory k).C.obj A) :
    forgetTwist k (laurent A) ((ordinaryTheory k).gmProductEquiv A (b, c)) =
      laurentCohomologyMap k A (forgetTwist k A b, forgetTwist k A c) := by
  simp only [OrdinaryTheory.gmProductEquiv_apply, map_add, map_mul, forgetTwist_map,
    logClass_laurentT_eq_twistedClass, forgetTwist_twistedClass]
  rfl

/-- The actual cohomology of a Laurent extension splits into the regular and logarithmic terms.
This is derived from the proved product equivalence of the de Rham ordinary theory. -/
def laurentCohomologyEquiv (A : SmoothAlg k) :
    (Cohomology k A × Cohomology k A) ≃ₗ[k] Cohomology k (laurent A) :=
  LinearEquiv.ofBijective (laurentCohomologyMap k A) (by
    constructor
    · apply (injective_iff_map_eq_zero _).2
      rintro ⟨b, c⟩ h
      have ht := laurentCohomologyMap_twistedClass k A b c
      rw [h, map_zero] at ht
      have hz := (ordinaryTheory k).gmProductEquiv A |>.injective
        (ht.trans ((ordinaryTheory k).gmProductEquiv A).map_zero.symm)
      exact Prod.ext (twistedClass_eq_zero.1 (congrArg Prod.fst hz))
        (twistedClass_eq_zero.1 (congrArg Prod.snd hz))
    · intro z
      obtain ⟨⟨b, c⟩, h⟩ := ((ordinaryTheory k).gmProductEquiv A).surjective (twistedClass 0 z)
      refine ⟨(forgetTwist k A b, forgetTwist k A c), ?_⟩
      exact (forgetTwist_gmProductEquiv k A b c).symm.trans
        ((congrArg (forgetTwist k (laurent A)) h).trans (forgetTwist_twistedClass k _ _ _)))

/-- The regular summand keeps its degree and the logarithmic summand increases it by one. -/
theorem laurentCohomologyEquiv_mem_grading_iff (A : SmoothAlg k) (p : ℤ)
    (b c : Cohomology k A) :
    laurentCohomologyEquiv k A (b, c) ∈ Cohomology.grading k (laurent A) p ↔
      b ∈ Cohomology.grading k A p ∧ c ∈ Cohomology.grading k A (p - 1) := by
  rw [← twistedClass_mem_grading_iff (w := 0)]
  change twistedClass 0 (laurentCohomologyMap k A (b, c)) ∈ _ ↔ _
  rw [← laurentCohomologyMap_twistedClass]
  exact ((ordinaryTheory k).gmProductEquiv_mem_grading_iff
    (i := (p, 0)) (j := (p - 1, -1)) (by ext <;> simp)).trans
      (and_congr twistedClass_mem_grading_iff twistedClass_mem_grading_iff)

/-- The residue reads off the logarithmic summand of the untwisted Laurent splitting. -/
theorem residue_laurentCohomologyEquiv (A : SmoothAlg k) (b c : Cohomology k A) :
    residue (standardPair A).compl (isUnit_natCast_add_one k) (standardPair A).isSmoothPrincipalPair
      (laurentCohomologyEquiv k A (b, c)) = c := by
  have h := congrArg ((ordinaryTheory k).stdResidue A)
    (laurentCohomologyMap_twistedClass k A b c)
  simp only [OrdinaryTheory.stdResidue_gmProductEquiv, stdResidue_twistedClass,
    Int.reduceSub] at h
  exact (twistedClass_inj.1 h).symm

/-- Point cohomology is the coefficient field. -/
def pointCohomologyEquiv : k ≃ₐ[k] Cohomology k (point k) :=
  AlgEquiv.ofBijective (Algebra.ofId k _) (Cohomology.bijective_algebraMap_point k)

/-- The punctured line has the basis `1, [dx/x]`. -/
def gmCohomologyEquiv : (k × k) ≃ₗ[k] Cohomology k (gm k) :=
  (LinearEquiv.prodCongr (pointCohomologyEquiv k).toLinearEquiv
    (pointCohomologyEquiv k).toLinearEquiv).trans (laurentCohomologyEquiv k (point k))

/-- The punctured-line coefficients multiply the unit and the actual logarithmic class. -/
@[simp] theorem gmCohomologyEquiv_apply (a b : k) :
    gmCohomologyEquiv k (a, b) = algebraMap k _ a +
      laurentThetaClass k (point k) * algebraMap k _ b := by
  change Cohomology.map (algHom (laurentC (point k))) (algebraMap k _ a) +
    laurentThetaClass k (point k) *
      Cohomology.map (algHom (laurentC (point k))) (algebraMap k _ b) = _
  rw [AlgHom.commutes, AlgHom.commutes]

omit [CharZero k] in
private theorem point_algebraMap_mem_grading_iff (p : ℤ) (a : k) :
    algebraMap k (Cohomology k (point k)) a ∈ Cohomology.grading k (point k) p ↔
      p = 0 ∨ a = 0 := by
  by_cases hp : p = 0
  · subst p
    exact iff_of_true (by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem (A := Cohomology.grading k _)))
      (Or.inl rfl)
  · refine ⟨fun h => Or.inr ?_, fun h => ?_⟩
    · exact (Cohomology.bijective_algebraMap_point k).injective
        ((Cohomology.eq_zero_of_mem_grading_point hp h).trans (map_zero _).symm)
    · rcases h with h | rfl
      · exact (hp h).elim
      · simp

/-- The two coefficients of the punctured line have degrees zero and one. -/
theorem gmCohomologyEquiv_mem_grading_iff (p : ℤ) (a b : k) :
    gmCohomologyEquiv k (a, b) ∈ Cohomology.grading k (gm k) p ↔
      (p = 0 ∨ a = 0) ∧ (p = 1 ∨ b = 0) := by
  change laurentCohomologyEquiv k (point k) (algebraMap k _ a, algebraMap k _ b) ∈ _ ↔ _
  rw [laurentCohomologyEquiv_mem_grading_iff, point_algebraMap_mem_grading_iff,
    point_algebraMap_mem_grading_iff]
  simp only [sub_eq_zero]

/-- `H⁰(k[x,x⁻¹])` is the first coefficient field. -/
theorem gmCohomologyEquiv_mem_degree_zero_iff (a b : k) :
    gmCohomologyEquiv k (a, b) ∈ Cohomology.degree k (gm k) 0 ↔ b = 0 := by
  rw [← Cohomology.grading_natCast, gmCohomologyEquiv_mem_grading_iff]
  simp

/-- `H¹(k[x,x⁻¹])` is the coefficient of `[dx/x]`. -/
theorem gmCohomologyEquiv_mem_degree_one_iff (a b : k) :
    gmCohomologyEquiv k (a, b) ∈ Cohomology.degree k (gm k) 1 ↔ a = 0 := by
  rw [← Cohomology.grading_natCast, gmCohomologyEquiv_mem_grading_iff]
  simp

/-- The punctured line has no cohomology above degree one. -/
theorem gm_eq_zero_of_mem_degree_succ_succ (n : ℕ) {c : Cohomology k (gm k)}
    (hc : c ∈ Cohomology.degree k (gm k) (n + 2)) : c = 0 := by
  apply (twistedClass_eq_zero (w := 0)).1
  exact (ordinaryTheory k).eq_zero_of_mem_grading_gm (by omega) (by omega)
    (twistedClass_mem_grading_natCast_iff.2 hc)

/-- The outer and inner logarithmic coordinate classes of the two-torus. -/
def torusX : Cohomology k (laurent (gm k)) :=
  Cohomology.map (algHom (laurentC (gm k))) (laurentThetaClass k (point k))

/-- The logarithmic class of the outer Laurent coordinate. -/
def torusY : Cohomology k (laurent (gm k)) := laurentThetaClass k (gm k)

omit [CharZero k] in
private theorem laurentThetaClass_mul_self (A : SmoothAlg k) :
    laurentThetaClass k A * laurentThetaClass k A = 0 := by
  exact (Cohomology.mk_mul _ _ _ _).trans
    ((Cohomology.mk_congr (dlog_mul_self k _) _).trans (Cohomology.mk_zero _))

omit [CharZero k] in
/-- The two coordinate generators square to zero, as actual exterior classes. -/
theorem torusX_mul_self : torusX k * torusX k = 0 := by
  change Cohomology.map (algHom (laurentC (gm k))) (laurentThetaClass k (point k)) *
    Cohomology.map (algHom (laurentC (gm k))) (laurentThetaClass k (point k)) = 0
  rw [← map_mul, laurentThetaClass_mul_self, map_zero]

omit [CharZero k] in
/-- The second coordinate generator also squares to zero. -/
theorem torusY_mul_self : torusY k * torusY k = 0 := laurentThetaClass_mul_self k _

omit [CharZero k] in
/-- The two logarithmic coordinate generators anticommute. -/
theorem torus_anticommute : torusY k * torusX k = -(torusX k * torusY k) := by
  have h := Cohomology.isGradedCommutative_degree k (laurent (gm k))
    (laurentThetaClass_mem_degree k (gm k))
    (Cohomology.map_mem_degree (algHom (laurentC (gm k)))
      (laurentThetaClass_mem_degree k (point k)))
  simpa [torusX, torusY] using h

/-- The ordered exterior basis `1, θx, θy, θxθy` of the two-torus. -/
def torusCohomologyEquiv : ((k × k) × (k × k)) ≃ₗ[k] Cohomology k (laurent (gm k)) :=
  (LinearEquiv.prodCongr (gmCohomologyEquiv k)
    ((LinearEquiv.prodCongr (LinearEquiv.refl k k) (LinearEquiv.neg k)).trans
      (gmCohomologyEquiv k))).trans (laurentCohomologyEquiv k (gm k))

/-- The ordered exterior-basis formula for the two-torus. -/
theorem torusCohomologyEquiv_apply (a b c e : k) :
    torusCohomologyEquiv k ((a, b), (c, e)) = algebraMap k _ a +
      b • torusX k + c • torusY k + e • (torusX k * torusY k) := by
  change Cohomology.map (algHom (laurentC (gm k))) (gmCohomologyEquiv k (a, b)) +
    torusY k * Cohomology.map (algHom (laurentC (gm k))) (gmCohomologyEquiv k (c, -e)) = _
  simp only [gmCohomologyEquiv_apply, map_add, map_mul, AlgHom.commutes]
  change algebraMap k _ a + torusX k * algebraMap k _ b +
    torusY k * (algebraMap k _ c + torusX k * algebraMap k _ (-e)) = _
  simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, mul_add,
    ← mul_assoc, torus_anticommute, neg_smul, neg_mul_neg, add_assoc]

/-- The logarithmic-first residue formula on the two-torus. With the outer coordinate named
`x` and the coefficient coordinate named `y`, it is `r_x(θx θy) = θy`. -/
theorem torus_residue_outer_mul_inner :
    residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
      (standardPair (gm k)).isSmoothPrincipalPair (torusY k * torusX k) =
      laurentThetaClass k (point k) := by
  have h := residue_laurentCohomologyEquiv k (gm k) 0 (laurentThetaClass k (point k))
  have he : laurentCohomologyEquiv k (gm k) (0, laurentThetaClass k (point k)) =
      torusY k * torusX k := by
    simp only [laurentCohomologyEquiv, LinearEquiv.ofBijective_apply,
      laurentCohomologyMap, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, zero_add, LinearMap.mulLeft_apply]
    rfl
  exact (congrArg (residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
    (standardPair (gm k)).isSmoothPrincipalPair) he.symm).trans h

/-- With the outer coordinate named `y`, residue of the ordered `θx θy` is `-θx`. -/
theorem torus_residue_inner_mul_outer :
    residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
      (standardPair (gm k)).isSmoothPrincipalPair (torusX k * torusY k) =
      -laurentThetaClass k (point k) := by
  have h : torusX k * torusY k = -(torusY k * torusX k) := by
    rw [torus_anticommute, neg_neg]
  exact (congrArg (residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
    (standardPair (gm k)).isSmoothPrincipalPair) h).trans
      ((map_neg _ _).trans (congrArg Neg.neg (torus_residue_outer_mul_inner k)))

/-- Interchanging the two Laurent coordinates is an actual algebra automorphism. -/
def torusSwap : laurent (gm k) ⟶ laurent (gm k) :=
  ofHom (AddMonoidAlgebra.commAlgEquiv k).toAlgHom

omit [CharZero k] in
private theorem torusSwap_outer : mapUnits (torusSwap k) (laurentT (gm k)) =
    mapUnits (laurentC (gm k)) (laurentT (point k)) := by
  apply Units.ext
  change AddMonoidAlgebra.commAlgEquiv k
    (AddMonoidAlgebra.single (1 : ℤ) (1 : LaurentPolynomial k)) =
    AddMonoidAlgebra.single (0 : ℤ) (AddMonoidAlgebra.single (1 : ℤ) (1 : k))
  exact AddMonoidAlgebra.commAlgEquiv_single_zero _

omit [CharZero k] in
private theorem torusSwap_inner :
    mapUnits (torusSwap k) (mapUnits (laurentC (gm k)) (laurentT (point k))) =
      laurentT (gm k) := by
  apply Units.ext
  change AddMonoidAlgebra.commAlgEquiv k
    (AddMonoidAlgebra.single (0 : ℤ) (AddMonoidAlgebra.single (1 : ℤ) (1 : k))) =
      AddMonoidAlgebra.single (1 : ℤ) (1 : LaurentPolynomial k)
  exact AddMonoidAlgebra.commAlgEquiv_single_zero_single _

omit [CharZero k] in
private theorem torusX_eq_unitClass : torusX k =
    unitClass (mapUnits (laurentC (gm k)) (laurentT (point k))) :=
  map_unitClass (algHom (laurentC (gm k))) (laurentT (point k))

omit [CharZero k] in
/-- Coordinate interchange exchanges the actual logarithmic classes. -/
theorem torusSwap_map_X :
    Cohomology.map (algHom (torusSwap k)) (torusX k) = torusY k := by
  calc
    _ = Cohomology.map (algHom (torusSwap k))
        (unitClass (mapUnits (laurentC (gm k)) (laurentT (point k)))) :=
      congrArg (Cohomology.map (algHom (torusSwap k))) (torusX_eq_unitClass k)
    _ = unitClass
        (mapUnits (torusSwap k) (mapUnits (laurentC (gm k)) (laurentT (point k)))) :=
      map_unitClass _ _
    _ = unitClass (laurentT (gm k)) := congrArg unitClass (torusSwap_inner k)
    _ = _ := rfl

omit [CharZero k] in
/-- The other generator is exchanged too. -/
theorem torusSwap_map_Y :
    Cohomology.map (algHom (torusSwap k)) (torusY k) = torusX k := by
  calc
    _ = unitClass (mapUnits (torusSwap k) (laurentT (gm k))) :=
      map_unitClass _ _
    _ = unitClass (mapUnits (laurentC (gm k)) (laurentT (point k))) :=
      congrArg unitClass (torusSwap_outer k)
    _ = _ := (torusX_eq_unitClass k).symm

/-- Residue along the coefficient coordinate `x`, transported by the explicit coordinate swap.
The ordinary standard-pair residue on this model is residue along `y`. -/
def torusResidueX : Cohomology k (laurent (gm k)) →ₗ[k] Cohomology k (gm k) :=
  (residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
    (standardPair (gm k)).isSmoothPrincipalPair).comp
      (Cohomology.map (algHom (torusSwap k))).toLinearMap

/-- On the same ordered top class, residue along `x` is `θy`, with positive sign. -/
theorem torusResidueX_top : torusResidueX k (torusX k * torusY k) =
    laurentThetaClass k (point k) := by
  change residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
    (standardPair (gm k)).isSmoothPrincipalPair
      (Cohomology.map (algHom (torusSwap k)) (torusX k * torusY k)) = _
  have h : Cohomology.map (algHom (torusSwap k)) (torusX k * torusY k) =
      torusY k * torusX k := by rw [map_mul, torusSwap_map_X, torusSwap_map_Y]
  exact (congrArg (residue (standardPair (gm k)).compl (isUnit_natCast_add_one k)
    (standardPair (gm k)).isSmoothPrincipalPair) h).trans (torus_residue_outer_mul_inner k)

/-- The top exterior class on the two-torus is nonzero. -/
theorem torus_top_ne_zero : torusX k * torusY k ≠ 0 := by
  intro h
  have he : torusCohomologyEquiv k ((0, 0), (0, 1)) = 0 := by
    simpa only [torusCohomologyEquiv_apply, map_zero, zero_smul, one_smul,
      zero_add] using h
  have hz := (torusCohomologyEquiv k).injective (he.trans (map_zero _).symm)
  exact one_ne_zero (congrArg (fun p : ((k × k) × (k × k)) => p.2.2) hz)

/-- The basis coordinates of the torus have degrees `0,1,1,2`. -/
theorem torusCohomologyEquiv_mem_grading_iff (p : ℤ) (a b c e : k) :
    torusCohomologyEquiv k ((a, b), (c, e)) ∈ Cohomology.grading k (laurent (gm k)) p ↔
      (p = 0 ∨ a = 0) ∧ (p = 1 ∨ b = 0) ∧ (p = 1 ∨ c = 0) ∧ (p = 2 ∨ e = 0) := by
  change laurentCohomologyEquiv k (gm k)
    (gmCohomologyEquiv k (a, b), gmCohomologyEquiv k (c, -e)) ∈ _ ↔ _
  rw [laurentCohomologyEquiv_mem_grading_iff, gmCohomologyEquiv_mem_grading_iff,
    gmCohomologyEquiv_mem_grading_iff]
  simp only [neg_eq_zero]
  have h0 : p - 1 = 0 ↔ p = 1 := sub_eq_zero
  have h1 : p - 1 = 1 ↔ p = 2 := by omega
  tauto

/-- The two-torus has no cohomology above degree two. -/
theorem torus_eq_zero_of_mem_degree_succ_succ_succ (n : ℕ)
    {c : Cohomology k (laurent (gm k))}
    (hc : c ∈ Cohomology.degree k (laurent (gm k)) (n + 3)) : c = 0 := by
  obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ := (torusCohomologyEquiv k).surjective c
  rw [← Cohomology.grading_natCast, torusCohomologyEquiv_mem_grading_iff] at hc
  have ha := hc.1.resolve_left (by omega)
  have hb := hc.2.1.resolve_left (by omega)
  have hc0 := hc.2.2.1.resolve_left (by omega)
  have he : e = 0 := hc.2.2.2.resolve_left (by omega)
  subst a; subst b; subst c
  subst e
  exact (torusCohomologyEquiv k).map_zero

end OrlikSolomon.DeRham.Examples
