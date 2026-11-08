/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module
public import OrlikSolomon.Examples.DeRhamCrossing
public import OrlikSolomon.Examples.Geometric.Morphisms
public import Mathlib.Algebra.Ring.Fin
public import OrlikSolomon.DeRham.Schemes.Forms.Associated
public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Duality
/-!
# Why regularity, smoothness, and multiplicity hypotheses are essential

The component equation `(1,0)` on the actual spectrum of `k × k` has the correct smooth
closed and open components but is not regular. The cohomology comparison makes actual
restriction the first projection `k × k → k`. A nonzero degree-zero kernel class proves that
no homogeneous Gysin map with shift `+2` can make this pair exact: its necessary lift would
have degree `−2`.

The crossing equation `xy` is regular on the actual smooth affine plane, but its actual
closed spectrum is singular. The sheaf-image logarithmic construction still exists; its two
global normal presentations `dy ∧ dx` and `theta ∧ (y dx)` agree, while `(y dx)|D` is nonzero.
Consequently no residue morphism of those actual sheaves can kill regular forms and have the
usual normal-form formula. The same restricted form has a nonzero germ in the actual
structure-sheaf module of one-forms at the origin. This is proved by localization, since both
coordinates annihilate it and every scalar acts by its origin value.

## Main results

* `Nonregular.equation_not_regular`, `Nonregular.restriction_coordinate`, and
  `Nonregular.no_shifted_gysin_exact`: the full ordinary-localization shift obstruction on
  actual scheme cohomology.
* `Crossing.equation_regular`, `Crossing.divisor_not_smooth`: the geometric crossing is
  excluded by smoothness, although its equation is regular.
* `Crossing.actual_theta_wedge_eta`, `Crossing.no_sheaf_residue`, and
  `Crossing.actualForms_stalk_ne_zero`: actual sheaf sections, the sheaf-image obstruction,
  and its survival at the origin stalk.

The ramification exclusion is re-exported from `Morphisms`: unequal actual divisor ideals
with equal closed support, failure of a Cartesian square, and actual residue two.

Blueprint: `prop:geo-exclusions`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.Examples
namespace Nonregular
variable (k : Type u) [CommRing k]

private def twoPointEquiv : (Fin 2 → k) ≃ₐ[k] k × k where
  __ := RingEquiv.piFinTwo (fun _ : Fin 2 => k)
  commutes' _ := rfl

/-- The algebra of two disjoint points is formally smooth over the base ring. -/
instance twoPoint_formallySmooth : Algebra.FormallySmooth k (k × k) :=
  .of_equiv (twoPointEquiv k)

/-- The actual algebra of two points is smooth over a Noetherian base. -/
instance twoPoint_smooth [IsNoetherianRing k] : Algebra.Smooth k (k × k) where
  finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- The actual spectrum of the two-point algebra `k × k`. -/
def ambient : Over (Spec (CommRingCat.of k)) := spec (.of k (k × k))
/-- The actual first point, the invertibility open of `(1,0)`. -/
def openPart : Over (Spec (CommRingCat.of k)) := spec (.of k k)
/-- The first-component inclusion, realized as an actual morphism of schemes over the base. -/
def openMap : openPart k ⟶ ambient k := specMap (CommAlgCat.ofHom (AlgHom.fst k k k))
/-- The second-component inclusion, the actual zero scheme of `(1,0)`. -/
def closedMap : openPart k ⟶ ambient k := specMap (CommAlgCat.ofHom (AlgHom.snd k k k))

private lemma fst_localization :
    letI := (AlgHom.fst k k k).toRingHom.toAlgebra
    IsLocalization.Away ((1, 0) : k × k) k := by
  let := (AlgHom.fst k k k).toRingHom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact isUnit_one
  · intro a
    exact ⟨0, (a, 0), by simp [RingHom.algebraMap_toAlgebra]⟩
  · intro a b hab
    exact ⟨1, Prod.ext (by simpa [RingHom.algebraMap_toAlgebra] using hab) (by simp)⟩

/-- The first-component map is an actual open immersion. -/
instance openMap_isOpenImmersion : IsOpenImmersion (openMap k).left :=
  isOpenImmersion_specMap_of_isLocalization
    (CommRingCat.ofHom (AlgHom.fst k k k).toRingHom) ((1, 0) : k × k) (fst_localization k)

/-- The first component is exactly the basic open of the component equation. -/
lemma openMap_opensRange : (openMap k).left.opensRange =
    (ambient k).left.basicOpen ((Scheme.ΓSpecIso (.of (k × k))).inv ((1, 0) : k × k)) :=
  opensRange_specMap_of_isLocalization
    (CommRingCat.ofHom (AlgHom.fst k k k).toRingHom) ((1, 0) : k × k) (fst_localization k)

/-- The second-component map is an actual closed immersion. -/
instance closedMap_isClosedImmersion : IsClosedImmersion (closedMap k).left :=
  IsClosedImmersion.spec_of_surjective _ (fun a => ⟨(0, a), rfl⟩)

private lemma snd_ker :
    RingHom.ker (AlgHom.snd k k k).toRingHom = Ideal.span {((1, 0) : k × k)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro ha
    exact ⟨(a.1, 0), Prod.ext (by simp) (by simpa using ha)⟩
  · rintro ⟨a, rfl⟩
    simp

/-- The second component is cut out scheme-theoretically by `(1,0)`. -/
lemma closedMap_ker : (closedMap k).left.ker =
    principalIdealSheaf ((Scheme.ΓSpecIso (.of (k × k))).inv ((1, 0) : k × k)) :=
  ker_specMap_of_ker_eq (CommRingCat.ofHom (AlgHom.snd k k k).toRingHom) (snd_ker k)

/-- The actual global section `(1,0)` is not regular for nonzero coefficients. -/
theorem equation_not_regular [Nontrivial k] :
    ¬ IsRegularSection ((Scheme.ΓSpecIso (.of (k × k))).inv ((1, 0) : k × k)) := by
  rw [isRegularSection_ΓSpecIso_inv_iff]
  intro h
  have hz := (mem_nonZeroDivisors_iff.mp h).1 ((0, 1) : k × k) (by simp)
  exact zero_ne_one (congrArg Prod.snd hz).symm

/-- Actual de Rham cohomology of the two-point spectrum is `k × k` over every base ring. -/
def cohomologyEquiv : Cohomology k (globalSections (ambient k)) ≃ₐ[k] k × k :=
  (specCohomologyEquiv k (.of k (k × k))).trans
    ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k)).trans
      (AlgEquiv.prodCongr (Cohomology.equivOfSurjective
        (Function.surjective_id : Function.Surjective (algebraMap k k)))
        (Cohomology.equivOfSurjective
          (Function.surjective_id : Function.Surjective (algebraMap k k)))))

/-- Actual de Rham cohomology of the open point is `k`. -/
def openCohomologyEquiv : Cohomology k (globalSections (openPart k)) ≃ₐ[k] k :=
  (specCohomologyEquiv k (.of k k)).trans
    (Cohomology.equivOfSurjective
      (Function.surjective_id : Function.Surjective (algebraMap k k)))

/-- Actual restriction to the open component is the first coordinate of `k × k`. -/
lemma restriction_coordinate (c : Cohomology k (globalSections (ambient k))) :
    openCohomologyEquiv k (Cohomology.map (globalSectionsMap (openMap k)).hom c) =
      (cohomologyEquiv k c).1 := by
  have h := specCohomologyEquiv_pull k (CommAlgCat.ofHom (AlgHom.fst k k k)) c
  have h := congrArg (Cohomology.equivOfSurjective
    (Function.surjective_id : Function.Surjective (algebraMap k k))) h
  exact h.trans (congrArg (Cohomology.equivOfSurjective
    (Function.surjective_id : Function.Surjective (algebraMap k k)))
      (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_fst
        (AlgHom.id k k) (specCohomologyEquiv k (.of k (k × k)) c)).symm)

/-- The actual restriction kernel is exactly the second coordinate copy of `k`. -/
lemma restriction_eq_zero_iff (c : Cohomology k (globalSections (ambient k))) :
    Cohomology.map (globalSectionsMap (openMap k)).hom c = 0 ↔
      (cohomologyEquiv k c).1 = 0 := by
  constructor
  · intro h
    exact (restriction_coordinate k c).symm.trans
      ((congrArg (openCohomologyEquiv k) h).trans (openCohomologyEquiv k).map_zero)
  · intro h
    exact (openCohomologyEquiv k).injective
      (((restriction_coordinate k c).trans h).trans (openCohomologyEquiv k).map_zero.symm)

private lemma point_mem_degree_zero (c : Cohomology k k) :
    c ∈ Cohomology.degree k k 0 := by
  induction c using Cohomology.induction with
  | mk a ha =>
      apply Cohomology.mk_mem_degree _ ha
      rw [← Cohomology.algebraMap_algebraMapInv_of_surjective Function.surjective_id a]
      exact algebraMap_mem_exteriorPower_zero _ _

/-- Every actual class on the two-point spectrum has degree zero. Together with the coordinate
comparison, this identifies both `H⁰` and its restriction kernel over every coefficient ring. -/
lemma mem_degree_zero (c : Cohomology k (globalSections (ambient k))) :
    c ∈ Cohomology.degree k (globalSections (ambient k)) 0 := by
  apply (specCohomologyEquiv_mem_degree_iff k (.of k (k × k)) 0 c).1
  apply (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_mem_degree
    (AlgHom.id k k) 0 _).2
  exact ⟨point_mem_degree_zero k _, point_mem_degree_zero k _⟩

/-- The actual degree-zero class supported on the second connected component. -/
def kernelClass : Cohomology k (globalSections (ambient k)) :=
  (specCohomologyEquiv k (.of k (k × k))).symm
    ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k)).symm
      (0, 1))

/-- The actual class on the closed component is nonzero for nonzero coefficients. -/
lemma kernelClass_ne_zero [Nontrivial k] : kernelClass k ≠ 0 := by
  intro h
  have h := congrArg (fun c =>
    OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k)
      (specCohomologyEquiv k (.of k (k × k)) c)) h
  change (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k))
      ((specCohomologyEquiv k (.of k (k × k)))
        ((specCohomologyEquiv k (.of k (k × k))).symm
          ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
            (AlgHom.id k k)).symm (0, 1)))) = _ at h
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at h
  have hz := congrArg
    (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k))
    (specCohomologyEquiv k (.of k (k × k))).map_zero
  have hz := hz.trans
    (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation (AlgHom.id k k)).map_zero
  exact one_ne_zero (congrArg Prod.snd (h.trans hz))

/-- The component-supported kernel class has cohomological degree zero. -/
lemma kernelClass_mem_degree_zero :
    kernelClass k ∈ Cohomology.degree k (globalSections (ambient k)) 0 := by
  apply (specCohomologyEquiv_mem_degree_iff k (.of k (k × k)) 0 _).1
  have hc := (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_mem_degree
    (AlgHom.id k k) 0
      ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
        (AlgHom.id k k)).symm (0, 1))).2
  have hc := hc (by rw [AlgEquiv.apply_symm_apply]; exact ⟨zero_mem _, SetLike.one_mem_graded _⟩)
  exact (congrArg (fun c => c ∈ Cohomology.degree k (k × k) 0)
    ((specCohomologyEquiv k (.of k (k × k))).apply_symm_apply _)).symm ▸ hc

/-- The component-supported class is killed by actual restriction to the open component. -/
lemma pull_kernelClass :
    Cohomology.map (globalSectionsMap (openMap k)).hom (kernelClass k) = 0 := by
  apply (specCohomologyEquiv k (.of k k)).injective
  have hp := specCohomologyEquiv_pull k (CommAlgCat.ofHom (AlgHom.fst k k k)) (kernelClass k)
  have he := (specCohomologyEquiv k (.of k (k × k))).apply_symm_apply
    ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
      (AlgHom.id k k)).symm (0, 1))
  have hp := hp.trans (congrArg (Cohomology.map (AlgHom.fst k k k)) he)
  have hc := congrArg Prod.fst
    ((OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
      (AlgHom.id k k)).apply_symm_apply (0, 1))
  rw [OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_fst] at hc
  exact hp.trans (hc.trans (specCohomologyEquiv k (.of k k)).map_zero.symm)

/-- No map of cohomological shift `+2` can make the actual component restriction exact. -/
lemma no_shifted_gysin_exact [Nontrivial k]
    (G : Cohomology k (globalSections (openPart k)) →ₗ[k]
      Cohomology k (globalSections (ambient k)))
    (hG : IsHomogeneousOfShift (Cohomology.grading k (globalSections (openPart k)))
      (Cohomology.grading k (globalSections (ambient k))) (2 : ℤ) G) :
    ¬ Function.Exact G (Cohomology.map (globalSectionsMap (openMap k)).hom) := by
  intro hex
  have hc : kernelClass k ∈ Cohomology.grading k (globalSections (ambient k)) 0 := by
    simpa only [← Cohomology.grading_natCast (k := k) (A := globalSections (ambient k)) 0,
      Nat.cast_zero] using
      kernelClass_mem_degree_zero k
  obtain ⟨c, hc, he⟩ := hG.exists_mem_preimage_of_exact hex
    (show (-2 : ℤ) + 2 = 0 by decide) hc (pull_kernelClass k)
  have hz := Cohomology.eq_zero_of_mem_grading_of_neg (by decide : (-2 : ℤ) < 0) hc
  exact kernelClass_ne_zero k (he.symm.trans (hz ▸ G.map_zero))

end Nonregular

namespace Crossing
section Algebraic
variable (k : Type u) [CommRing k]
local notation "A" => OrlikSolomon.DeRham.Examples.CrossingPlane k
local notation "Q" => OrlikSolomon.DeRham.Examples.CrossingDivisor k
local notation "x" => OrlikSolomon.DeRham.Examples.crossingX k
local notation "y" => OrlikSolomon.DeRham.Examples.crossingY k
local notation "equation" => OrlikSolomon.DeRham.Examples.crossingEquation k
local notation "π" => OrlikSolomon.DeRham.Examples.crossingQuotient k

/-- The actual affine plane over the base ring. -/
@[implicit_reducible] def plane : Over (Spec (CommRingCat.of k)) := spec (.of k A)
/-- The actual singular crossing spectrum `Spec k[x,y]/(xy)`. -/
@[implicit_reducible] def divisor : Over (Spec (CommRingCat.of k)) := spec (.of k Q)
/-- The actual principal-open spectrum where `xy` is invertible. -/
@[implicit_reducible] def complement : Over (Spec (CommRingCat.of k)) :=
  spec (.of k (Localization.Away equation))
/-- The actual closed immersion of the crossing divisor into the plane. -/
def closedMap : divisor k ⟶ plane k := specMap (CommAlgCat.ofHom π)
/-- The actual open immersion of the principal complement of `xy`. -/
def openMap : complement k ⟶ plane k :=
  specMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (Localization.Away equation)))

/-- The actual ambient affine plane is smooth over every commutative base ring. -/
theorem plane_smooth : Smooth (plane k).hom :=
  (smooth_spec_hom_iff (.of k A)).2 inferInstance

/-- The crossing quotient defines an actual closed immersion. -/
instance closedMap_isClosedImmersion : IsClosedImmersion (closedMap k).left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The actual crossing divisor has the principal ideal sheaf generated by `xy`. -/
lemma closedMap_ker : (closedMap k).left.ker =
    principalIdealSheaf ((Scheme.ΓSpecIso (.of A)).inv equation) :=
  ker_specMap_of_ker_eq (CommRingCat.ofHom (π).toRingHom) (f := equation) Ideal.mk_ker

/-- The crossing localization defines an actual open immersion. -/
instance openMap_isOpenImmersion : IsOpenImmersion (openMap k).left :=
  isOpenImmersion_specMap_of_isLocalization
    (CommRingCat.ofHom (algebraMap A (Localization.Away equation))) equation
      (isLocalizationAway_toAlgebra rfl)

/-- The actual localization has precisely the invertibility open of the crossing equation. -/
lemma openMap_opensRange : (openMap k).left.opensRange =
    (plane k).left.basicOpen ((Scheme.ΓSpecIso (.of A)).inv equation) :=
  opensRange_specMap_of_isLocalization
    (CommRingCat.ofHom (algebraMap A (Localization.Away equation))) equation
      (isLocalizationAway_toAlgebra rfl)

/-- The crossing equation is a regular global section on the actual affine plane. -/
theorem equation_regular :
    IsRegularSection ((Scheme.ΓSpecIso (.of A)).inv equation) :=
  (isRegularSection_ΓSpecIso_inv_iff _).2
    (OrlikSolomon.DeRham.Examples.crossingEquation_mem_nonZeroDivisors k)

/-- The actual crossing divisor is not smooth for nonzero coefficients. -/
theorem divisor_not_smooth [Nontrivial k] : ¬ Smooth (divisor k).hom := by
  intro h
  have h : Algebra.Smooth k Q := (smooth_spec_hom_iff (.of k Q)).1 h
  exact OrlikSolomon.DeRham.Examples.crossingDivisor_not_formallySmooth k h.formallySmooth

/-- The ambient algebraic one-form `y dx`. -/
def eta : ⋀[A]^1 Ω[A⁄k] :=
  ⟨y • diff k x, Submodule.smul_mem _ _ (diff_mem_exteriorPower_one k _)⟩

/-- The ambient regular algebraic two-form `dy ∧ dx`. -/
def omega : ⋀[A]^2 Ω[A⁄k] :=
  ⟨diff k y * diff k x,
    SetLike.mul_mem_graded (diff_mem_exteriorPower_one k _) (diff_mem_exteriorPower_one k _)⟩

/-- The restriction of `y dx` to the crossing quotient, in exterior degree one. -/
def quotientEta : ⋀[Q]^1 Ω[Q⁄k] := Forms.mapPower π 1 (eta k)

/-- The restricted crossing form is nonzero, without a characteristic-zero hypothesis. -/
theorem quotientEta_ne_zero [Nontrivial k] : quotientEta k ≠ 0 := by
  intro h
  apply OrlikSolomon.DeRham.Examples.crossing_restriction_ne_zero k
  exact congrArg Subtype.val h

/-- The crossing form on the quotient is represented by `y dx` in its total exterior algebra. -/
lemma quotientEta_coe :
    (quotientEta k).val = π y • diff k (π x) := by
  simp only [quotientEta, Forms.coe_mapPower, eta, Forms.map_smul, Forms.map_diff]

/-- The two coordinate functions multiply to zero in the crossing quotient. -/
lemma quotient_xy : π x * π y = 0 := by
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))

/-- The first coordinate annihilates the restricted crossing form. -/
lemma x_smul_quotientEta : π x • quotientEta k = 0 := by
  apply Subtype.ext
  change π x • (quotientEta k).val = 0
  rw [quotientEta_coe, smul_smul, quotient_xy, zero_smul]

/-- The second coordinate also annihilates the restricted crossing form. -/
lemma y_smul_quotientEta : π y • quotientEta k = 0 := by
  apply Subtype.ext
  change π y • (quotientEta k).val = 0
  rw [quotientEta_coe]
  have h := congrArg (fun a : Forms k Q => π y • a)
    ((diff k : Derivation k Q (Forms k Q)).leibniz (π x) (π y))
  rw [quotient_xy, map_zero, smul_zero, smul_add, smul_smul,
    mul_comm (π y) (π x), quotient_xy, zero_smul, zero_add] at h
  exact h.symm

/-- Evaluation of functions on the actual crossing divisor at its origin. -/
def originEvaluation : Q →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _ : Fin 2 => (0 : k))) (by
    change Ideal.span {equation} ≤ RingHom.ker _
    rw [Ideal.span_le]
    intro a ha
    rcases ha with rfl
    simp [OrlikSolomon.DeRham.Examples.crossingEquation,
      OrlikSolomon.DeRham.Examples.crossingX, OrlikSolomon.DeRham.Examples.crossingY])

/-- Each coordinate annihilates the restricted one-form. -/
lemma variable_smul_quotientEta (i : Fin 2) : π (MvPolynomial.X i) • quotientEta k = 0 := by
  fin_cases i
  · exact x_smul_quotientEta k
  · exact y_smul_quotientEta k

/-- A polynomial acts on the crossing form by its constant coefficient. -/
lemma polynomial_smul_quotientEta (a : A) :
    π a • quotientEta k = (MvPolynomial.eval (fun _ : Fin 2 => (0 : k)) a) • quotientEta k := by
  induction a using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.eval_C]
      change π (algebraMap k A c) • quotientEta k = c • quotientEta k
      rw [AlgHom.commutes, IsScalarTower.algebraMap_smul]
  | add a b ha hb => simp only [map_add, add_smul, ha, hb]
  | mul_X a i _ =>
      rw [map_mul, mul_smul, variable_smul_quotientEta, smul_zero]
      simp only [map_mul, MvPolynomial.eval_X, mul_zero, zero_smul]

/-- Every function on the crossing divisor acts on the form by its value at the origin. -/
lemma scalar_smul_quotientEta (a : Q) :
    a • quotientEta k = originEvaluation k a • quotientEta k := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact polynomial_smul_quotientEta k a

/-- The nonzero restricted form as an actual global section of the one-form sheaf on the
divisor. -/
def actualEta : (DeRham.formsSheaf k (divisor k) 1).obj.obj (op ⊤) :=
  specFormSection k (.of k Q) 1 (quotientEta k)

/-- The actual regular global two-form `dy ∧ dx` on the ambient plane. -/
def actualOmega : (DeRham.formsSheaf k (plane k) 2).obj.obj (op ⊤) :=
  specFormSection k (.of k A) 2 (omega k)

/-- The actual ambient global one-form `y dx`. -/
def actualAmbientEta : (DeRham.formsSheaf k (plane k) 1).obj.obj (op ⊤) :=
  specFormSection k (.of k A) 1 (eta k)

/-- The actual global one-form `d(xy)/(xy)` on the principal complement. -/
def actualTheta : (DeRham.formsSheaf k (complement k) 1).obj.obj (op ⊤) :=
  specFormSection k (.of k (Localization.Away equation)) 1
    ⟨theta k equation (Localization.Away equation),
      theta_mem_exteriorPower_one k equation (Localization.Away equation)⟩

/-- The restricted actual global one-form is nonzero. -/
theorem actualEta_ne_zero [Nontrivial k] : actualEta k ≠ 0 := by
  intro h
  apply quotientEta_ne_zero k
  exact specFormSection_injective k (.of k Q) 1 (h.trans (map_zero _).symm)

/-- On actual global sheaf forms, `theta ∧ (y dx)` is the restriction of the regular form `dy ∧
dx`. -/
theorem actual_theta_wedge_eta :
    DeRham.formsSheafWedge k (complement k) 1 1 (op ⊤) (actualTheta k)
        (DeRham.formsSheafPullbackTop (openMap k) 1 (actualAmbientEta k)) =
      DeRham.formsSheafPullbackTop (openMap k) 2 (actualOmega k) := by
  change DeRham.formsSheafWedge k (spec (.of k (Localization.Away equation))) 1 1 (op ⊤)
      (specFormSection k (.of k (Localization.Away equation)) 1 _)
      (DeRham.formsSheafPullbackTop (specMap _) 1 (specFormSection k (.of k A) 1 _)) =
    DeRham.formsSheafPullbackTop (specMap _) 2 (specFormSection k (.of k A) 2 _)
  rw [specFormSection_pull, specFormSection_pull, specFormSection_wedge]
  exact congrArg (specFormSection k (.of k (Localization.Away equation)) 2)
    (Subtype.ext (OrlikSolomon.DeRham.Examples.crossing_theta_mul k (Localization.Away equation)))

private lemma specFormSection_unit (R : CommAlgCat.{u} k) (n : ℕ) (a : ⋀[R]^n Ω[R⁄k]) :
    specFormSection k R n a = (DeRham.formsSheafUnit k (spec R) n).app (op ⊤)
      (Forms.mapPower (DeRham.specSectionMap ⊤) n a) := by
  change DeRham.globalFormsEquiv (spec R) n _ = _
  rw [DeRham.globalFormsEquiv_apply, DeRham.affineFormsComparison_apply]
  congr 1
  apply Subtype.ext
  simp only [Forms.coe_mapPower, Forms.map_map]
  rfl

/-- The crossing equation as an actual invertible global function on its complement. -/
def complementUnit : (DeRham.sectionAlgebra k (complement k) ⊤)ˣ :=
  Units.map (DeRham.specSectionMap (k := k) ⊤).toMonoidHom
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away equation) equation).unit

private lemma thetaWedge_actualEta :
    (DeRham.thetaWedgeSheaf (complement k) (complementUnit k) 1).hom.app (op ⊤)
      (DeRham.formsSheafPullbackTop (openMap k) 1 (actualAmbientEta k)) =
        DeRham.formsSheafPullbackTop (openMap k) 2 (actualOmega k) := by
  let R : CommAlgCat.{u} k := .of k (Localization.Away equation)
  let a := Forms.mapPower (IsScalarTower.toAlgHom k A (Localization.Away equation)) 1 (eta k)
  let b := Forms.mapPower (IsScalarTower.toAlgHom k A (Localization.Away equation)) 2 (omega k)
  have ha := specFormSection_pull k
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (Localization.Away equation))) 1 (eta k)
  have hb := specFormSection_pull k
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (Localization.Away equation))) 2 (omega k)
  have hu := specFormSection_unit k R 1 a
  have hv := specFormSection_unit k R 2 b
  have ht := DeRham.thetaWedgeSheaf_unit (complement k) (complementUnit k) 1 (op ⊤)
    (Forms.mapPower (DeRham.specSectionMap ⊤) 1 a)
  refine (congrArg ((DeRham.thetaWedgeSheaf (complement k) (complementUnit k) 1).hom.app
    (op ⊤)) ha).trans ?_
  refine (congrArg ((DeRham.thetaWedgeSheaf (complement k) (complementUnit k) 1).hom.app
    (op ⊤)) hu).trans (ht.trans ?_)
  refine Eq.trans ?_ (hv.symm.trans hb.symm)
  congr 1
  apply Subtype.ext
  change dlog k (Units.map (DeRham.sectionRestriction k (complement k)
      (⊤ : (complement k).left.Opens).leTop).toMonoidHom (complementUnit k)) *
    Forms.map (DeRham.specSectionMap ⊤)
      (Forms.map (IsScalarTower.toAlgHom k A (Localization.Away equation)) (eta k).val) = _
  have hu : Units.map (DeRham.sectionRestriction k (complement k)
      (⊤ : (complement k).left.Opens).leTop).toMonoidHom (complementUnit k) =
      complementUnit k := by apply Units.ext; rfl
  rw [hu]
  change dlog k (Units.map (DeRham.specSectionMap (k := k) ⊤).toMonoidHom
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away equation) equation).unit) * _ = _
  have hd := Forms.map_dlog (DeRham.specSectionMap (k := k)  ⊤)
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away equation) equation).unit
  refine (congrArg (fun c => c * Forms.map (DeRham.specSectionMap ⊤)
    (Forms.map (IsScalarTower.toAlgHom k A (Localization.Away equation))
      (eta k).val)) hd.symm).trans ?_
  exact (map_mul (Forms.map (DeRham.specSectionMap ⊤)) _ _).symm.trans
    (congrArg (Forms.map (DeRham.specSectionMap ⊤))
      (OrlikSolomon.DeRham.Examples.crossing_theta_mul k (Localization.Away equation)))

/-- The actual regular-plus-left-theta map of sheaves in exterior degree two. -/
def normalMap : DeRham.formsSheaf k (plane k) 2 ⊞ DeRham.formsSheaf k (plane k) 1 ⟶
    (TopCat.Sheaf.pushforward (ModuleCat k) (openMap k).left.base).obj
      (DeRham.formsSheaf k (complement k) 2) :=
  biprod.desc (DeRham.formsSheafPullback (openMap k) 2)
    (DeRham.formsSheafPullback (openMap k) 1 ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) (openMap k).left.base).map
        (DeRham.thetaWedgeSheaf (complement k) (complementUnit k) 1))

/-- The actual image sheaf of regular and left-theta forms for the singular crossing. -/
@[implicit_reducible] def logarithmicSheaf : TopCat.Sheaf (ModuleCat k) (plane k).left :=
  image (normalMap k)

/-- The regular summand of the normal-form map into the actual logarithmic image sheaf. -/
def regularToLog : DeRham.formsSheaf k (plane k) 2 ⟶ logarithmicSheaf k :=
  biprod.inl ≫ factorThruImage (normalMap k)

/-- The left-theta summand into the actual logarithmic image sheaf. -/
def thetaToLog : DeRham.formsSheaf k (plane k) 1 ⟶ logarithmicSheaf k :=
  biprod.inr ≫ factorThruImage (normalMap k)

private lemma regularToLog_image : regularToLog k ≫ image.ι (normalMap k) =
    DeRham.formsSheafPullback (openMap k) 2 := by
  rw [regularToLog, Category.assoc, image.fac]
  exact biprod.inl_desc _ _

private lemma thetaToLog_image : thetaToLog k ≫ image.ι (normalMap k) =
    DeRham.formsSheafPullback (openMap k) 1 ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) (openMap k).left.base).map
        (DeRham.thetaWedgeSheaf (complement k) (complementUnit k) 1) := by
  rw [thetaToLog, Category.assoc, image.fac]
  exact biprod.inr_desc _ _

/-- The regular and left-theta presentations are equal inside the actual sheaf image. -/
lemma logarithmic_presentations_eq :
    (regularToLog k).hom.app (op ⊤) (actualOmega k) =
      (thetaToLog k).hom.app (op ⊤) (actualAmbientEta k) := by
  have hmono : Mono (((sheafToPresheaf _ _).map (image.ι (normalMap k))).app (op ⊤)) :=
    inferInstance
  apply (ModuleCat.mono_iff_injective _).1 hmono
  have hr := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t => t.hom) (regularToLog_image k)) (op ⊤)) (actualOmega k)
  have ht := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t => t.hom) (thetaToLog_image k)) (op ⊤))
      (actualAmbientEta k)
  exact hr.trans ((thetaWedge_actualEta k).symm.trans ht.symm)

/-- There is no actual sheaf residue killing regular forms and restricting the coefficient of
left theta. -/
lemma no_sheaf_residue [Nontrivial k] :
    ¬ ∃ ρ : logarithmicSheaf k ⟶
        (TopCat.Sheaf.pushforward (ModuleCat k) (closedMap k).left.base).obj
          (DeRham.formsSheaf k (divisor k) 1),
      regularToLog k ≫ ρ = 0 ∧ thetaToLog k ≫ ρ = DeRham.formsSheafPullback (closedMap k) 1 := by
  rintro ⟨ρ, hreg, htheta⟩
  have he := congrArg (ρ.hom.app (op ⊤)) (logarithmic_presentations_eq k)
  have hr := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t => t.hom) hreg) (op ⊤)) (actualOmega k)
  have ht := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t => t.hom) htheta) (op ⊤)) (actualAmbientEta k)
  have he := hr.symm.trans (he.trans ht)
  have hp := specFormSection_pull k (CommAlgCat.ofHom π) 1 (eta k)
  exact actualEta_ne_zero k (hp.symm.trans he.symm)

end Algebraic

section Field
variable (K : Type u) [Field K]

/-- The actual origin point of the crossing spectrum over a field. -/
def origin : PrimeSpectrum (OrlikSolomon.DeRham.Examples.CrossingDivisor K) :=
  PrimeSpectrum.comap (originEvaluation K).toRingHom ⟨⊥, inferInstance⟩

/-- A function lies in the origin prime ideal exactly when its origin value vanishes. -/
lemma origin_mem_iff (a : OrlikSolomon.DeRham.Examples.CrossingDivisor K) :
    a ∈ (origin K).asIdeal ↔ originEvaluation K a = 0 := Iff.rfl

private lemma tilde_toStalk_eq_zero_iff {R : CommRingCat.{u}} (M : ModuleCat R)
    (pt : PrimeSpectrum.Top R) (m : M) :
    tilde.toStalk M pt m = 0 ↔ ∃ s : pt.asIdeal.primeCompl, s • m = 0 :=
  IsLocalizedModule.eq_zero_iff pt.asIdeal.primeCompl (tilde.toStalk M pt).hom

/-- The restricted one-form survives in the associated one-form sheaf stalk at the origin. -/
lemma quotientEta_stalk_ne_zero :
    tilde.toStalk (ModuleCat.of (CommRingCat.of (OrlikSolomon.DeRham.Examples.CrossingDivisor K))
      (⋀[OrlikSolomon.DeRham.Examples.CrossingDivisor K]^1
        Ω[OrlikSolomon.DeRham.Examples.CrossingDivisor K⁄K]))
      (origin K) (quotientEta K) ≠ 0 := by
  intro h
  obtain ⟨s, hs⟩ := (tilde_toStalk_eq_zero_iff
    (ModuleCat.of (CommRingCat.of (OrlikSolomon.DeRham.Examples.CrossingDivisor K))
      (⋀[OrlikSolomon.DeRham.Examples.CrossingDivisor K]^1
        Ω[OrlikSolomon.DeRham.Examples.CrossingDivisor K⁄K])) (origin K) (quotientEta K)).1 h
  have hs : (s : OrlikSolomon.DeRham.Examples.CrossingDivisor K) • quotientEta K = 0 := hs
  rw [scalar_smul_quotientEta] at hs
  have hne : originEvaluation K s ≠ 0 := fun hz => s.property ((origin_mem_iff K s).2 hz)
  exact quotientEta_ne_zero K ((smul_eq_zero.mp hs).resolve_left hne)

/-- The germ of the represented crossing form is nonzero in the actual one-form module sheaf. -/
lemma actualForms_stalk_ne_zero :
    (DeRham.formsModuleSheaf K (divisor K) 1).presheaf.germ ⊤ (origin K) (by trivial)
      (DeRham.specFormsModuleSection (k := K) 1 ⊤ (quotientEta K)) ≠ 0 := by
  intro h
  let e := DeRham.specFormsModuleSheafAssociatedIso
    (k := K) (A := OrlikSolomon.DeRham.Examples.CrossingDivisor K) 1
  have he := DeRham.specFormsModuleSheafAssociatedIso_toOpen
    (k := K) (A := OrlikSolomon.DeRham.Examples.CrossingDivisor K) 1 ⊤ (quotientEta K)
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ (origin K) (by trivial)
    e.hom.mapPresheaf (DeRham.specFormsModuleSection (k := K) 1 ⊤ (quotientEta K))
  have hm := congrArg
    ((TopCat.Presheaf.stalkFunctor Ab.{u} (origin K)).map e.hom.mapPresheaf) h
  have he' := congrArg
    ((tilde (ModuleCat.of (CommRingCat.of (OrlikSolomon.DeRham.Examples.CrossingDivisor K))
      (⋀[OrlikSolomon.DeRham.Examples.CrossingDivisor K]^1
        Ω[OrlikSolomon.DeRham.Examples.CrossingDivisor K⁄K]))).presheaf.germ
          ⊤ (origin K) (by trivial)) he
  apply quotientEta_stalk_ne_zero K
  exact (hg.trans he').symm.trans (hm.trans (map_zero _))

end Field
end Crossing
end OrlikSolomon.Geometric.Examples
