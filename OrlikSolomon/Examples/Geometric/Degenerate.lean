/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.DeRhamCalculations.Basic
public import OrlikSolomon.DeRham.Schemes.Instance
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Unit, empty, and disconnected geometric pairs

The unit pair and the spectrum of the zero ring are actual smooth scheme objects, including
when the base ring is zero. The disconnected pair is the spectrum of `k × k[z]` with equation
`(1,z)`; its divisor is the second component's origin and its complement is
`Spec k ⨿ Spec k[z,z⁻¹]`. No global derivation normalizes this equation to one.

The affine de Rham comparisons identify the actual ambient cohomology with `k × k` and the
complement cohomology with two constants and one logarithmic class. The degree criterion records
all degrees, and the third generator has residue one. Quotient and localization computations are
the existing algebraic regressions transported through the public affine duality.

## Main results

* `zeroScheme_cohomology_eq_zero`, `unitPairOpenIso`, `unitPair_gysin_eq_zero`, and
  `unitPair_residue_eq_zero`: the empty and unit edge cases.
* `disconnectedDivisorDomainIso`, `disconnectedAmbientCoproductIso`, and
  `disconnectedComplementCoproductIso`: the actual geometric identifications.
* `disconnectedAmbientCohomologyEquiv`, `disconnectedCohomologyEquiv_mem_degree_iff`, and
  `disconnected_residue_generator`: the cohomology and normalized residue calculation.
* `disconnected_no_global_normal_section`: the failure of global normalization on actual
  global functions.

The example-only `specCohomologyEquiv` and `specFormSection` retain the concrete algebraic
representatives for the other geometric regression modules.

Blueprint: `prop:geo-degenerate`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Polynomial LaurentPolynomial

universe u v w

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u) [CommRing k] (D : SmoothDomain k)

/-- The empty smooth affine scheme, the actual spectrum of the zero algebra. -/
@[implicit_reducible] def zeroScheme : D.Obj := D.spec (SmoothAlg.zero k)

/-- The spectrum of the zero algebra has no scheme points. -/
instance zeroScheme_isEmpty : IsEmpty (zeroScheme k D).obj.left :=
  inferInstanceAs (IsEmpty (Spec (CommRingCat.of PUnit)))

/-- The spectrum of the unit-equation algebraic pair; its closed part is empty. -/
def unitPair (A : SmoothAlg k) : DivisorPair D :=
  DivisorPair.spec D (OrlikSolomon.DivisorPair.emptyDivisor A (SmoothAlg.zero k))

/-- The equation of the unit pair is the constant global section one. -/
theorem unitPair_eqn (A : SmoothAlg k) : (unitPair k D A).eqn = 1 := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv 1 = 1
  exact map_one _

/-- The divisor of the unit pair is empty over every commutative base ring. -/
instance unitPair_closed_isEmpty (A : SmoothAlg k) : IsEmpty (unitPair k D A).closed.obj.left :=
  (unitPair k D A).isEmpty_closed_of_isUnit ((unitPair_eqn k D A).symm ▸ isUnit_one)

/-- The complement inclusion of the unit pair is an actual scheme isomorphism. -/
def unitPairOpenIso (A : SmoothAlg k) :
    (unitPair k D A).compl.obj.left ≅ (unitPair k D A).ambient.obj.left := by
  have := (unitPair k D A).isIso_j_of_isUnit ((unitPair_eqn k D A).symm ▸ isUnit_one)
  exact asIso (unitPair k D A).j.hom.left

/-- De Rham cohomology of an actual spectrum, compared with its coordinate algebra. -/
def specCohomologyEquiv (A : CommAlgCat.{u} k) :
    OrlikSolomon.DeRham.Cohomology k (globalSections (spec A)) ≃ₐ[k]
      OrlikSolomon.DeRham.Cohomology k A :=
  OrlikSolomon.DeRham.Cohomology.mapEquiv (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A))

/-- The spectrum cohomology comparison preserves and reflects each natural degree. -/
theorem specCohomologyEquiv_mem_degree_iff (A : CommAlgCat.{u} k) (n : ℕ)
    (c : OrlikSolomon.DeRham.Cohomology k (globalSections (spec A))) :
    specCohomologyEquiv k A c ∈ OrlikSolomon.DeRham.Cohomology.degree k A n ↔
      c ∈ OrlikSolomon.DeRham.Cohomology.degree k (globalSections (spec A)) n := by
  constructor
  · intro h
    have hm := OrlikSolomon.DeRham.Cohomology.map_mem_degree
      (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).symm.toAlgHom h
    simpa only [specCohomologyEquiv, ← OrlikSolomon.DeRham.Cohomology.mapEquiv_symm_apply,
      AlgEquiv.symm_apply_apply] using hm
  · exact OrlikSolomon.DeRham.Cohomology.map_mem_degree _

/-- Every de Rham class on the actual empty scheme vanishes, including in degree zero. -/
theorem zeroScheme_cohomology_eq_zero
    (c : DeRham.Cohomology (zeroScheme k (SmoothDomain.aff k))) : c = 0 := by
  exact (specCohomologyEquiv k (SmoothAlg.zero k).obj).injective (Subsingleton.elim _ _)

/-- The spectrum cohomology comparison intertwines actual scheme pullback with the ring map. -/
lemma specCohomologyEquiv_pull {A B : CommAlgCat.{u} k} (φ : A ⟶ B)
    (c : OrlikSolomon.DeRham.Cohomology k (globalSections (spec A))) :
    specCohomologyEquiv k B
        (OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap (specMap φ)).hom c) =
      OrlikSolomon.DeRham.Cohomology.map φ.hom (specCohomologyEquiv k A c) := by
  change OrlikSolomon.DeRham.Cohomology.map
      (CommAlgCat.algEquivOfIso (globalSectionsSpecIso B)).toAlgHom
      (OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap (specMap φ)).hom c) =
    OrlikSolomon.DeRham.Cohomology.map φ.hom
      (OrlikSolomon.DeRham.Cohomology.map
        (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).toAlgHom c)
  rw [OrlikSolomon.DeRham.Cohomology.map_map, OrlikSolomon.DeRham.Cohomology.map_map]
  exact congrArg (fun f => OrlikSolomon.DeRham.Cohomology.map f c)
    (congrArg CommAlgCat.Hom.hom (globalSectionsSpecIso_naturality φ))

/-- An algebraic exterior form as an actual global section of the forms sheaf on its spectrum. -/
def specFormSection (A : CommAlgCat.{u} k) (n : ℕ) :
    (⋀[A]^n Ω[A⁄k]) →ₗ[k] (DeRham.formsSheaf k (spec A) n).obj.obj (op ⊤) :=
  (DeRham.globalFormsEquiv (spec A) n).toLinearMap.comp
    (OrlikSolomon.DeRham.Forms.mapPower
      (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).symm.toAlgHom n)

/-- Actual pullback of a represented global form is represented by the algebraic pullback. -/
lemma specFormSection_pull {A B : CommAlgCat.{u} k} (φ : A ⟶ B) (n : ℕ)
    (x : ⋀[A]^n Ω[A⁄k]) :
    DeRham.formsSheafPullbackTop (specMap φ) n (specFormSection k A n x) =
      specFormSection k B n (OrlikSolomon.DeRham.Forms.mapPower φ.hom n x) := by
  change DeRham.formsSheafPullbackTop (specMap φ) n
      (DeRham.globalFormsEquiv (spec A) n _) = DeRham.globalFormsEquiv (spec B) n _
  rw [DeRham.globalFormsEquiv_pull]
  congr 1
  have hφ : (globalSectionsMap (specMap φ)).hom.comp
      (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).symm.toAlgHom =
      (CommAlgCat.algEquivOfIso (globalSectionsSpecIso B)).symm.toAlgHom.comp φ.hom :=
    congrArg CommAlgCat.Hom.hom (globalSectionsSpecIso_inv_naturality φ).symm
  rw [← LinearMap.comp_apply, ← OrlikSolomon.DeRham.Forms.mapPower_comp, hφ,
    OrlikSolomon.DeRham.Forms.mapPower_comp, LinearMap.comp_apply]

/-- The algebraic representative of a global form on a spectrum is unique. -/
lemma specFormSection_injective (A : CommAlgCat.{u} k) (n : ℕ) :
    Function.Injective (specFormSection k A n) := by
  intro a b h
  apply Subtype.ext
  apply (OrlikSolomon.DeRham.Forms.mapEquiv
    (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).symm).injective
  exact congrArg Subtype.val ((DeRham.globalFormsEquiv (spec A) n).injective h)

/-- The spectrum comparison preserves wedge products of represented global forms. -/
lemma specFormSection_wedge (A : CommAlgCat.{u} k) (p q : ℕ)
    (a : ⋀[A]^p Ω[A⁄k]) (b : ⋀[A]^q Ω[A⁄k]) :
    DeRham.formsSheafWedge k (spec A) p q (op ⊤)
      (specFormSection k A p a) (specFormSection k A q b) =
        specFormSection k A (p + q) ⟨a.val * b.val, SetLike.mul_mem_graded a.2 b.2⟩ := by
  change DeRham.formsSheafWedge k (spec A) p q (op ⊤)
    (DeRham.globalFormsEquiv (spec A) p _) (DeRham.globalFormsEquiv (spec A) q _) =
      DeRham.globalFormsEquiv (spec A) (p + q) _
  rw [DeRham.globalFormsEquiv_wedge]
  congr 1
  exact Subtype.ext (map_mul (OrlikSolomon.DeRham.Forms.map
    (CommAlgCat.algEquivOfIso (globalSectionsSpecIso A)).symm.toAlgHom) a.val b.val).symm

section UnitMaps
variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory D ℬ)

/-- The Gysin map of the unit pair vanishes in every supplied geometric ordinary theory. -/
lemma unitPair_gysin_eq_zero (A : SmoothAlg k) : T.gysin (unitPair k D A) = 0 :=
  T.gysin_eq_zero_of_isUnit _ ((unitPair_eqn k D A).symm ▸ isUnit_one)

/-- The residue of the unit pair vanishes in every supplied geometric ordinary theory. -/
lemma unitPair_residue_eq_zero (A : SmoothAlg k) : T.residue (unitPair k D A) = 0 :=
  T.residue_eq_zero_of_isUnit _ ((unitPair_eqn k D A).symm ▸ isUnit_one)

end UnitMaps

section Product

variable [IsNoetherianRing k]

/-- The disconnected polynomial algebra is smooth over a Noetherian base. -/
instance productPolynomial_smooth : Algebra.Smooth k (k × k[X]) where
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

/-- The divisor quotient of the disconnected polynomial algebra is smooth. -/
instance productPolynomialQuotient_smooth :
    Algebra.Smooth k ((k × k[X]) ⧸ Ideal.span {Sanity.productPolynomialEquation k}) where
  finitePresentation := Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

/-- The principal-open algebra of the disconnected pair is smooth. -/
instance productPolynomialLocalization_smooth :
    Algebra.Smooth k (Localization.Away (Sanity.productPolynomialEquation k)) := by
  have : Algebra.Smooth (k × k[X]) (Localization.Away (Sanity.productPolynomialEquation k)) :=
    .of_isLocalization_Away (Sanity.productPolynomialEquation k)
  exact .comp k (k × k[X]) _

/-- The certified algebraic fixture `(k × k[z], (1,z))`, with its quotient and localization. -/
@[implicit_reducible] def disconnectedAlgebraicPair : OrlikSolomon.DivisorPair k where
  ambient := SmoothAlg.of k (k × k[X])
  closed := SmoothAlg.of k ((k × k[X]) ⧸ Ideal.span {Sanity.productPolynomialEquation k})
  compl := SmoothAlg.of k (Localization.Away (Sanity.productPolynomialEquation k))
  i := SmoothAlg.ofHom (Ideal.Quotient.mkₐ k (Ideal.span {Sanity.productPolynomialEquation k}))
  j := SmoothAlg.ofHom (IsScalarTower.toAlgHom k (k × k[X])
    (Localization.Away (Sanity.productPolynomialEquation k)))
  eqn := Sanity.productPolynomialEquation k
  surjective_i := Ideal.Quotient.mk_surjective
  ker_i := Ideal.mk_ker
  isLocalization_j := isLocalizationAway_toAlgebra rfl
  eqn_mem_nonZeroDivisors := Sanity.productPolynomialEquation_regular k

/-- The actual geometric principal pair with disconnected ambient spectrum and equation `(1,z)`. -/
@[implicit_reducible] def disconnectedPair : DivisorPair D :=
  DivisorPair.spec D (disconnectedAlgebraicPair k)

/-- The divisor is the point in the given geometric domain; this is an isomorphism over the
base. -/
def disconnectedDivisorDomainIso : (disconnectedPair k D).closed ≅ D.point :=
  ((D.specFunctor.mapIso (SmoothAlg.isoOfAlgEquiv
      (A := (disconnectedAlgebraicPair k).closed) (B := SmoothAlg.point k)
      (Sanity.productPolynomialQuotientEquiv k))).unop).symm ≪≫ D.specPointIso

/-- The ambient scheme is the disjoint union of the point and affine line. -/
def disconnectedAmbientCoproductIso :
    (disconnectedPair k D).ambient.obj.left ≅
      Spec (CommRingCat.of k) ⨿ Spec (CommRingCat.of k[X]) :=
  (asIso (coprodSpec k k[X])).symm

/-- The actual principal open is the spectrum of `k × k[z,z⁻¹]`. -/
def disconnectedComplementIso :
    (disconnectedPair k D).compl.obj.left ≅ Spec (CommRingCat.of (k × k[T;T⁻¹])) :=
  Scheme.Spec.mapIso
    ((OrlikSolomon.DeRham.Examples.productLocalizationEquiv k).toRingEquiv.toCommRingCatIso).symm.op

/-- The complement is the disjoint union of the point and multiplicative group. -/
def disconnectedComplementCoproductIso :
    (disconnectedPair k D).compl.obj.left ≅
      Spec (CommRingCat.of k) ⨿ Spec (CommRingCat.of k[T;T⁻¹]) :=
  disconnectedComplementIso k D ≪≫ (asIso (coprodSpec k k[T;T⁻¹])).symm

/-- The actual divisor scheme is the spectrum of the base ring. -/
def disconnectedDivisorIso :
    (disconnectedPair k D).closed.obj.left ≅ Spec (CommRingCat.of k) :=
  Scheme.Spec.mapIso
    ((Sanity.productPolynomialQuotientEquiv k).toRingEquiv.toCommRingCatIso).symm.op

/-- No derivation of the actual global function algebra takes the disconnected equation to one. -/
theorem disconnected_no_global_normal_section [Nontrivial k]
    (v : Derivation k (globalSections (spec (disconnectedAlgebraicPair k).ambient.obj))
      (globalSections (spec (disconnectedAlgebraicPair k).ambient.obj))) :
    v (disconnectedPair k D).eqn ≠ 1 := by
  let e : globalSections (spec (disconnectedAlgebraicPair k).ambient.obj) ≃ₐ[k] (k × k[X]) :=
    CommAlgCat.algEquivOfIso (globalSectionsSpecIso (disconnectedAlgebraicPair k).ambient.obj)
  let w : Derivation k (k × k[X]) (k × k[X]) :=
    { toLinearMap := e.toLinearMap.comp (v.toLinearMap.comp e.symm.toLinearMap)
      map_one_eq_zero' := by simp
      leibniz' a b := by
        change e (v (e.symm (a * b))) = a * e (v (e.symm b)) + b * e (v (e.symm a))
        rw [map_mul, v.leibniz]
        simp only [Algebra.smul_def, map_add, map_mul, AlgEquiv.apply_symm_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  intro h
  apply Sanity.productPolynomial_no_global_normal k w
  exact (congrArg e h).trans e.map_one


/-- The actual ambient de Rham cohomology is the algebra of two independent constants. -/
def disconnectedAmbientCohomologyEquiv (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    DeRham.Cohomology (disconnectedPair k (SmoothDomain.aff k)).ambient ≃ₐ[k] k × k :=
  ((specCohomologyEquiv k (SmoothAlg.of k (k × k[X])).obj).trans
    (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
      (Polynomial.aeval (0 : k)))).trans
    (AlgEquiv.prodCongr (OrlikSolomon.DeRham.Cohomology.equivOfSurjective
      (Function.surjective_id : Function.Surjective (algebraMap k k)))
      ((OrlikSolomon.DeRham.polynomialCohomologyEquiv k k hUnits).symm.trans
        (OrlikSolomon.DeRham.Cohomology.equivOfSurjective
          (Function.surjective_id : Function.Surjective (algebraMap k k)))))

omit [IsNoetherianRing k] in
private lemma point_mem_degree_zero (c : OrlikSolomon.DeRham.Cohomology k k) :
    c ∈ OrlikSolomon.DeRham.Cohomology.degree k k 0 := by
  induction c using OrlikSolomon.DeRham.Cohomology.induction with
  | mk a ha =>
      apply OrlikSolomon.DeRham.Cohomology.mk_mem_degree _ ha
      rw [← OrlikSolomon.DeRham.Cohomology.algebraMap_algebraMapInv_of_surjective
        Function.surjective_id a]
      exact OrlikSolomon.DeRham.algebraMap_mem_exteriorPower_zero _ _

/-- Every ambient class in the disconnected calculation has degree zero. -/
lemma disconnectedAmbient_mem_degree_zero (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (c : DeRham.Cohomology (disconnectedPair k (SmoothDomain.aff k)).ambient) :
    c ∈ DeRham.Cohomology.degree (disconnectedPair k (SmoothDomain.aff k)).ambient 0 := by
  apply (specCohomologyEquiv_mem_degree_iff k (disconnectedAlgebraicPair k).ambient.obj 0 c).1
  apply (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_mem_degree
    (Polynomial.aeval (0 : k)) 0 _).2
  refine ⟨point_mem_degree_zero k _, ?_⟩
  let e := OrlikSolomon.DeRham.polynomialCohomologyEquiv k k hUnits
  let z := (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
    (Polynomial.aeval (0 : k))
      (specCohomologyEquiv k (disconnectedAlgebraicPair k).ambient.obj c)).2
  change z ∈ OrlikSolomon.DeRham.Cohomology.degree k k[X] 0
  have h := (OrlikSolomon.DeRham.polynomialCohomologyEquiv_mem_degree_iff k k hUnits
    0 (e.symm z)).2 (point_mem_degree_zero k (e.symm z))
  change e (e.symm z) ∈ OrlikSolomon.DeRham.Cohomology.degree k k[X] 0 at h
  exact (e.apply_symm_apply z) ▸ h

/-- The actual complement cohomology agrees with the proved product-Laurent calculation. -/
def disconnectedComplementCohomologyComparison :
    DeRham.Cohomology (disconnectedPair k (SmoothDomain.aff k)).compl ≃ₐ[k]
      OrlikSolomon.DeRham.Cohomology k (k × k[T;T⁻¹]) :=
  (specCohomologyEquiv k
    (disconnectedAlgebraicPair k).compl.obj).trans
    (OrlikSolomon.DeRham.Cohomology.mapEquiv
      (OrlikSolomon.DeRham.Examples.productLocalizationEquiv k))

/-- The disconnected ambient scheme has no positive-degree de Rham cohomology. -/
lemma disconnectedAmbient_cohomology_eq_zero_of_mem_degree (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    {n : ℕ} (hn : n ≠ 0)
    {c : DeRham.Cohomology (disconnectedPair k (SmoothDomain.aff k)).ambient}
    (hc : c ∈ DeRham.Cohomology.degree (disconnectedPair k (SmoothDomain.aff k)).ambient n) :
    c = 0 := by
  let e := specCohomologyEquiv k (SmoothAlg.of k (k × k[X])).obj
  have he : e c ∈ OrlikSolomon.DeRham.Cohomology.degree k (k × k[X]) n :=
    (specCohomologyEquiv_mem_degree_iff k (SmoothAlg.of k (k × k[X])).obj n c).2 hc
  let eP := OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation
    (Polynomial.aeval (0 : k))
  obtain ⟨h₁, h₂⟩ :=
    (OrlikSolomon.DeRham.Examples.productCohomologyEquivOfAugmentation_mem_degree
      (Polynomial.aeval (0 : k)) n (e c)).1 he
  have h₁ := OrlikSolomon.DeRham.Cohomology.eq_zero_of_mem_degree_point hn h₁
  have h₂' := OrlikSolomon.DeRham.Cohomology.map_mem_degree
    (OrlikSolomon.DeRham.polynomialEvaluationAtZero k k) h₂
  have h₂' := OrlikSolomon.DeRham.Cohomology.eq_zero_of_mem_degree_point hn h₂'
  have h₂ : (eP (e c)).2 = 0 := by
    apply (OrlikSolomon.DeRham.polynomialCohomologyEquiv k k hUnits).symm.injective
    simpa only [eP, OrlikSolomon.DeRham.polynomialCohomologyEquiv_symm_apply, map_zero] using h₂'
  apply e.injective
  apply eP.injective
  have hz : eP (e c) = (0 : OrlikSolomon.DeRham.Cohomology k k ×
      OrlikSolomon.DeRham.Cohomology k k[X]) := Prod.ext h₁ h₂
  exact hz.trans ((congrArg eP e.map_zero).trans eP.map_zero).symm

end Product

section CharacteristicZero

variable (K : Type u) [Field K] [CharZero K]

/-- Two constants and one logarithmic coefficient parametrize the actual complement cohomology. -/
def disconnectedCohomologyEquiv : (K × (K × K)) ≃ₗ[K]
    DeRham.Cohomology (disconnectedPair K (SmoothDomain.aff K)).compl :=
  (OrlikSolomon.DeRham.Examples.productCohomologyEquiv K).trans
    (disconnectedComplementCohomologyComparison K).toLinearEquiv.symm

omit [CharZero K] in
/-- The product-Laurent comparison preserves and reflects degree. -/
lemma disconnectedComplementCohomologyComparison_mem_degree_iff (n : ℕ)
    (c : DeRham.Cohomology (disconnectedPair K (SmoothDomain.aff K)).compl) :
    disconnectedComplementCohomologyComparison K c ∈
        OrlikSolomon.DeRham.Cohomology.degree K (K × K[T;T⁻¹]) n ↔
      c ∈ DeRham.Cohomology.degree (disconnectedPair K (SmoothDomain.aff K)).compl n := by
  constructor
  · intro hc
    have hm := OrlikSolomon.DeRham.Cohomology.map_mem_degree
      (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K).symm.toAlgHom hc
    have hm : specCohomologyEquiv K
        (disconnectedAlgebraicPair K).compl.obj c ∈
        OrlikSolomon.DeRham.Cohomology.degree K
          (Localization.Away (Sanity.productPolynomialEquation K)) n := by
      change (OrlikSolomon.DeRham.Cohomology.mapEquiv
          (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K)).symm
        ((OrlikSolomon.DeRham.Cohomology.mapEquiv
          (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K))
          (specCohomologyEquiv K
            (disconnectedAlgebraicPair K).compl.obj c)) ∈ _ at hm
      simpa only [AlgEquiv.symm_apply_apply] using hm
    exact (specCohomologyEquiv_mem_degree_iff K
      (disconnectedAlgebraicPair K).compl.obj n c).1 hm
  · intro hc
    exact OrlikSolomon.DeRham.Cohomology.map_mem_degree _
      ((specCohomologyEquiv_mem_degree_iff K
        (disconnectedAlgebraicPair K).compl.obj n c).2 hc)

/-- The first two coefficients have degree zero and the last coefficient has degree one. -/
lemma disconnectedCohomologyEquiv_mem_degree_iff (n : ℕ) (a b c : K) :
    disconnectedCohomologyEquiv K (a, (b, c)) ∈
        DeRham.Cohomology.degree (disconnectedPair K (SmoothDomain.aff K)).compl n ↔
      (n = 0 ∨ a = 0) ∧ (n = 0 ∨ b = 0) ∧ (n = 1 ∨ c = 0) := by
  rw [← disconnectedComplementCohomologyComparison_mem_degree_iff]
  change disconnectedComplementCohomologyComparison K
      ((disconnectedComplementCohomologyComparison K).symm
        (OrlikSolomon.DeRham.Examples.productCohomologyEquiv K (a, (b, c)))) ∈ _ ↔ _
  rw [AlgEquiv.apply_symm_apply]
  exact OrlikSolomon.DeRham.Examples.productCohomologyEquiv_mem_degree_iff K n a b c

/-- The spectrum comparison identifies the actual geometric de Rham residue with the algebraic
residue. -/
lemma specCohomologyEquiv_residue (P : OrlikSolomon.DivisorPair K)
    (c : DeRham.Cohomology (DivisorPair.spec (SmoothDomain.aff K) P).compl) :
    specCohomologyEquiv K P.closed.obj
        (DeRham.residue (DivisorPair.spec (SmoothDomain.aff K) P) c) =
      OrlikSolomon.DeRham.residue P.compl (OrlikSolomon.DeRham.isUnit_natCast_add_one K)
        P.isSmoothPrincipalPair (specCohomologyEquiv K P.compl.obj c) := by
  exact (OrlikSolomon.DeRham.residue_map (OrlikSolomon.DeRham.isUnit_natCast_add_one K)
    (DivisorPair.unitIso P).inv.isPairHom _ _ c).symm

/-- The actual complement class represented by the disconnected logarithmic form `(0,dz/z)`. -/
def disconnectedLogClass : DeRham.Cohomology (disconnectedPair K (SmoothDomain.aff K)).compl :=
  (specCohomologyEquiv K (disconnectedAlgebraicPair K).compl.obj).symm
    (OrlikSolomon.DeRham.Cohomology.mk
      (OrlikSolomon.DeRham.theta K (disconnectedAlgebraicPair K).eqn
        (disconnectedAlgebraicPair K).compl) (OrlikSolomon.DeRham.d_theta _ _ _))

/-- The transported logarithmic class is exactly the third coefficient of the geometric
calculation. -/
lemma disconnectedLogClass_eq_generator :
    disconnectedLogClass K = disconnectedCohomologyEquiv K (0, (0, 1)) := by
  apply (disconnectedComplementCohomologyComparison K).injective
  refine (congrArg (OrlikSolomon.DeRham.Cohomology.mapEquiv
      (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K))
      ((specCohomologyEquiv K (disconnectedAlgebraicPair K).compl.obj).apply_symm_apply
        (OrlikSolomon.DeRham.Cohomology.mk
          (OrlikSolomon.DeRham.theta K (disconnectedAlgebraicPair K).eqn
            (disconnectedAlgebraicPair K).compl) (OrlikSolomon.DeRham.d_theta _ _ _)))).trans ?_
  refine Eq.trans ?_ ((disconnectedComplementCohomologyComparison K).apply_symm_apply _).symm
  refine Eq.trans ?_ (OrlikSolomon.DeRham.Examples.productCohomologyEquiv_generator K).symm
  change OrlikSolomon.DeRham.Cohomology.map
      (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K).toAlgHom
        (OrlikSolomon.DeRham.Cohomology.mk _ _) = _
  rw [OrlikSolomon.DeRham.Cohomology.map_mk]
  apply OrlikSolomon.DeRham.Cohomology.mk_congr
  rw [OrlikSolomon.DeRham.theta, OrlikSolomon.DeRham.Forms.map_dlog]
  exact (OrlikSolomon.DeRham.theta_eq_dlog K _ _
    (by
      change (OrlikSolomon.DeRham.Examples.productLocalizationEquiv K)
        ((IsLocalization.Away.algebraMap_isUnit
          (S := Localization.Away (Sanity.productPolynomialEquation K))
          (Sanity.productPolynomialEquation K)).unit :
            Localization.Away (Sanity.productPolynomialEquation K)) = _
      rw [IsUnit.unit_spec]
      exact (IsLocalization.algEquiv (.powers (Sanity.productPolynomialEquation K))
        (Localization.Away (Sanity.productPolynomialEquation K)) (K × K[T;T⁻¹])).commutes _)).symm

/-- The actual residue of the disconnected logarithmic class is one. -/
lemma disconnectedLogClass_residue :
    DeRham.residue (disconnectedPair K (SmoothDomain.aff K)) (disconnectedLogClass K) = 1 := by
  apply (specCohomologyEquiv K (disconnectedAlgebraicPair K).closed.obj).injective
  have h := specCohomologyEquiv_residue K (disconnectedAlgebraicPair K) (disconnectedLogClass K)
  rw [disconnectedLogClass, AlgEquiv.apply_symm_apply] at h
  exact h.trans ((OrlikSolomon.DeRham.Examples.residue_mk_theta_localization _
    (OrlikSolomon.DeRham.isUnit_natCast_add_one K)
    (disconnectedAlgebraicPair K).isSmoothPrincipalPair).trans
      (specCohomologyEquiv K (disconnectedAlgebraicPair K).closed.obj).map_one.symm)

/-- The disconnected complement has no de Rham cohomology above degree one. -/
lemma disconnected_cohomology_eq_zero_of_mem_degree_succ_succ (n : ℕ)
    {c : DeRham.Cohomology (disconnectedPair K (SmoothDomain.aff K)).compl}
    (hc : c ∈ DeRham.Cohomology.degree (disconnectedPair K (SmoothDomain.aff K)).compl (n + 2)) :
    c = 0 := by
  apply (disconnectedComplementCohomologyComparison K).injective
  exact (OrlikSolomon.DeRham.Examples.product_eq_zero_of_mem_degree_succ_succ K n
    ((disconnectedComplementCohomologyComparison_mem_degree_iff K (n + 2) c).2 hc)).trans
      (disconnectedComplementCohomologyComparison K).map_zero.symm

/-- Residue of the degree-one generator in the actual complement calculation is one. -/
lemma disconnected_residue_generator :
    DeRham.residue (disconnectedPair K (SmoothDomain.aff K))
      (disconnectedCohomologyEquiv K (0, (0, 1))) = 1 := by
  exact (congrArg (DeRham.residue (disconnectedPair K (SmoothDomain.aff K)))
    (disconnectedLogClass_eq_generator K)).symm.trans (disconnectedLogClass_residue K)

end CharacteristicZero

end OrlikSolomon.Geometric.Examples
