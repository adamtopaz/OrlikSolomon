/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.DeRhamMorphisms
public import OrlikSolomon.Examples.Geometric.Degenerate
public import OrlikSolomon.Cohomology.Geometric.Logarithms
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Non-flat transverse pullback and excluded ramification

The actual scheme morphism `z ↦ xy, v ↦ 0` is a morphism of geometric principal pairs over
every commutative base ring. For nonzero coefficients its ambient scheme map is not flat,
but Gysin and residue naturality hold in every supplied geometric ordinary theory. The simpler
unit-change map to the affine line is flat. Both pullbacks carry `dz/z` to `dx/x + dy/y`,
and the actual affine de Rham residue is one.

Squaring the coordinate gives an actual scheme map and a map of the open complements, but not
a morphism of the fixed reduced divisor pairs. Its principal ideals and divisor ideal sheaves
differ, its supports agree, and no Cartesian divisor square exists. Pullback on actual global
sheaf forms sends `dz/z` to `2 dx/x`, including in characteristic two and over the zero ring.
The characteristic-zero realization has actual residue two.

## Main results

* `nonFlatTransverseMap`, `nonFlatTransverseMap_not_flat`, and the two naturality theorems:
  the permitted non-flat regression.
* `unitChangeMap_flat`, `nonFlatTransverseMap_thetaSection`, and
  `nonFlatTransverseMap_deRham_residue_theta`: flatness, actual form representatives, and residue.
* `ramifiedMap_not_cartesian`, `ramifiedMap_pullback_ideal_ne`,
  `ramifiedMap_principal_ideals_ne`, and `ramifiedMap_same_support`: the scheme-theoretic
  distinction between the doubled and reduced point.
* `ramifiedMap_thetaSection` and `ramifiedMap_residue_theta`: the multiplicity-two calculation.

Blueprint: `prop:geo-nonflat` and the ramification clause of `prop:geo-exclusions`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u) [CommRing k] (D : SmoothDomain k)

/-- The actual flat pair map from the Laurent-polynomial surface to the affine line, `z ↦ xy`. -/
def unitChangeMap :
    DivisorPair.spec D
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))) ⟶
      DivisorPair.spec D (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)) :=
  DivisorPair.specMap D (OrlikSolomon.DeRham.Examples.unitChangeHom k)

/-- The actual non-flat transverse pair map `z ↦ xy, v ↦ 0`; no ambient flatness is required. -/
def nonFlatTransverseMap :
    DivisorPair.spec D
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))) ⟶
      DivisorPair.spec D
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point k))) :=
  DivisorPair.specMap D (OrlikSolomon.DeRham.Examples.nonFlatHom k)

/-- The simpler unit-change ambient scheme map is flat over every commutative base ring. -/
theorem unitChangeMap_flat : Flat (unitChangeMap k D).ambient.hom.left := by
  change Flat (Spec.map (CommRingCat.ofHom
    (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.unitChangeHom k).ambient).toRingHom))
  rw [Flat.SpecMap_iff]
  exact OrlikSolomon.DeRham.Examples.flat_unitChangeHom_ambient k

/-- The genuine two-coordinate ambient scheme map is not flat for nonzero coefficients. -/
theorem nonFlatTransverseMap_not_flat [Nontrivial k] :
    ¬ Flat (nonFlatTransverseMap k D).ambient.hom.left := by
  change ¬ Flat (Spec.map (CommRingCat.ofHom
    (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.nonFlatAmbient k)).toRingHom))
  rw [Flat.SpecMap_iff]
  exact OrlikSolomon.DeRham.Examples.not_flat_nonFlatAmbient k

/-- The actual affine-line pair with its reduced origin and multiplicative-group complement. -/
def standardSpecPair : DivisorPair D :=
  DivisorPair.spec D (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k))

/-- The actual affine-line scheme map whose coordinate pullback is squaring. -/
def ramifiedMap : (standardSpecPair k D).ambient ⟶ (standardSpecPair k D).ambient :=
  (D.specFunctor.map (OrlikSolomon.DeRham.Examples.ramifiedAmbient k)).unop

/-- The pulled-back global equation is not a unit multiple of the fixed reduced equation. -/
theorem ramifiedMap_not_associated [Nontrivial k] :
    ¬ Associated ((ramifiedMap k D).hom.left.appTop (standardSpecPair k D).eqn)
      (standardSpecPair k D).eqn := by
  intro h
  change Associated ((Geometric.specMap
      (OrlikSolomon.DeRham.Examples.ramifiedAmbient k).hom).left.appTop
        ((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).inv
          (SmoothAlg.polynomialX (SmoothAlg.point k))))
      ((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).inv
        (SmoothAlg.polynomialX (SmoothAlg.point k))) at h
  rw [specMap_left_appTop_ΓSpecIso_inv] at h
  have hm := h.map (Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).hom.hom
  apply OrlikSolomon.DeRham.Examples.ramifiedAmbient_not_associated k
  change Associated
    (((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).inv ≫
        (Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).hom)
      (OrlikSolomon.DeRham.Examples.ramifiedAmbient k (SmoothAlg.polynomialX (SmoothAlg.point k))))
    (((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).inv ≫
        (Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.point k)))).hom)
      (SmoothAlg.polynomialX (SmoothAlg.point k))) at hm
  simpa only [Iso.inv_hom_id, ConcreteCategory.id_apply] using hm

/-- No morphism of the fixed geometric pairs has the squaring ambient map. -/
theorem ramifiedMap_not_pairHom [Nontrivial k] :
    ¬ ∃ F : standardSpecPair k D ⟶ standardSpecPair k D, F.ambient = ramifiedMap k D := by
  rintro ⟨F, hF⟩
  exact ramifiedMap_not_associated k D (hF ▸ F.associated_eqn)

/-- The actual pulled-back doubled divisor and the fixed reduced divisor have different ideal
sheaves. -/
theorem ramifiedMap_pullback_ideal_ne [Nontrivial k] :
    (Limits.pullback.fst (ramifiedMap k D).hom.left (standardSpecPair k D).i.hom.left).ker ≠
      (standardSpecPair k D).i.hom.left.ker :=
  fun h => ramifiedMap_not_associated k D
    (((standardSpecPair k D).associated_iff_ker_pullback_fst
      (ramifiedMap k D)).2 h)

/-- There is no divisor map making the squaring square Cartesian for the fixed reduced pairs. -/
theorem ramifiedMap_not_cartesian [Nontrivial k] :
    ¬ ∃ gD : (standardSpecPair k D).closed.obj.left ⟶ (standardSpecPair k D).closed.obj.left,
      IsPullback (standardSpecPair k D).i.hom.left gD
        (ramifiedMap k D).hom.left (standardSpecPair k D).i.hom.left :=
  fun h => ramifiedMap_not_associated k D
    (((standardSpecPair k D).associated_iff_isPullback
      (ramifiedMap k D)).2 h)

/-- Squaring also gives an actual morphism of the open complements. -/
def ramifiedOpenMap : (standardSpecPair k D).compl ⟶ (standardSpecPair k D).compl :=
  (D.specFunctor.map (OrlikSolomon.DeRham.Examples.ramifiedComplement k)).unop

/-- The algebraic `df/f` as an actual global section of the one-form sheaf on the open spectrum. -/
def spectrumThetaSection (P : OrlikSolomon.DivisorPair k) :
    (DeRham.formsSheaf k (spec P.compl.obj) 1).obj.obj (op ⊤) :=
  specFormSection k P.compl.obj 1
    ⟨OrlikSolomon.DeRham.theta k P.eqn P.compl,
      OrlikSolomon.DeRham.theta_mem_exteriorPower_one k P.eqn P.compl⟩

/-- Actual pullback of global sheaf forms under squaring sends `dz/z` to `2 dx/x` over every
base ring. -/
lemma ramifiedMap_thetaSection :
    DeRham.formsSheafPullbackTop (ramifiedOpenMap k D).hom 1
        (spectrumThetaSection k (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k))) =
      2 • spectrumThetaSection k (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)) := by
  have h := specFormSection_pull k (OrlikSolomon.DeRham.Examples.ramifiedComplement k).hom 1
    ⟨OrlikSolomon.DeRham.theta k
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).eqn
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl,
      OrlikSolomon.DeRham.theta_mem_exteriorPower_one k _ _⟩
  refine h.trans ?_
  have he : OrlikSolomon.DeRham.Forms.mapPower
      (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.ramifiedComplement k)) 1
      ⟨OrlikSolomon.DeRham.theta k
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).eqn
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl,
        OrlikSolomon.DeRham.theta_mem_exteriorPower_one k _ _⟩ =
      2 • (⟨OrlikSolomon.DeRham.theta k
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).eqn
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl,
        OrlikSolomon.DeRham.theta_mem_exteriorPower_one k _ _⟩ :
          ⋀[(OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl]^1
            Ω[(OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl⁄k]) :=
    Subtype.ext (OrlikSolomon.DeRham.Examples.ramified_map_theta k)
  exact (congrArg (specFormSection k
    (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl.obj 1) he).trans
      (map_nsmul (specFormSection k
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)).compl.obj 1) _ _)

/-- The doubled and reduced points have the same underlying closed support in the actual
spectrum. -/
lemma ramifiedMap_same_support :
    PrimeSpectrum.zeroLocus ({(SmoothAlg.polynomialX (SmoothAlg.point k)) ^ 2} :
      Set (SmoothAlg.polynomial (SmoothAlg.point k))) =
        PrimeSpectrum.zeroLocus {SmoothAlg.polynomialX (SmoothAlg.point k)} :=
  PrimeSpectrum.zeroLocus_singleton_pow _ 2 (by decide)

/-- On actual scheme points, the inverse image of the reduced divisor has exactly the same
closed support. The doubled and reduced ideal sheaves still differ. -/
lemma ramifiedMap_preimage_divisor_support :
    (ramifiedMap k D).hom.left ⁻¹' Set.range (standardSpecPair k D).i.hom.left =
      Set.range (standardSpecPair k D).i.hom.left := by
  let P := OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)
  let φ : P.ambient →+* P.ambient :=
    (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.ramifiedAmbient k)).toRingHom
  have hr : Set.range (PrimeSpectrum.comap (SmoothAlg.algHom P.i).toRingHom) =
      PrimeSpectrum.zeroLocus {P.eqn} :=
    (range_comap_of_surjective _ _ P.surjective_i).trans
      ((congrArg (fun I : Ideal P.ambient => PrimeSpectrum.zeroLocus (I : Set P.ambient))
        P.ker_i).trans (PrimeSpectrum.zeroLocus_span _))
  change PrimeSpectrum.comap φ ⁻¹' Set.range (PrimeSpectrum.comap
      (SmoothAlg.algHom P.i).toRingHom) =
    Set.range (PrimeSpectrum.comap (SmoothAlg.algHom P.i).toRingHom)
  refine (congrArg (fun Z : Set (PrimeSpectrum P.ambient) =>
    PrimeSpectrum.comap φ ⁻¹' Z) hr).trans ?_
  refine Eq.trans ?_ hr.symm
  rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]
  have hφ : φ P.eqn = P.eqn ^ 2 :=
    OrlikSolomon.DeRham.Examples.ramifiedAmbient_polynomialX k
  exact (congrArg (fun a : P.ambient => PrimeSpectrum.zeroLocus {a}) hφ).trans
    (PrimeSpectrum.zeroLocus_singleton_pow _ 2 (by decide))


/-- The ideals `(x²)` and `(x)` differ even though their closed supports agree. -/
lemma ramifiedMap_principal_ideals_ne [Nontrivial k] :
    Ideal.span ({(Polynomial.X : Polynomial k) ^ 2} : Set (Polynomial k)) ≠
      Ideal.span {(Polynomial.X : Polynomial k)} := by
  intro h
  have hx : (Polynomial.X : Polynomial k) ∈ Ideal.span {(Polynomial.X : Polynomial k) ^ 2} :=
    h.symm ▸ Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.1 hx
  have hc := congrArg (fun q : Polynomial k => q.coeff 1) hp
  have hz : ((Polynomial.X : Polynomial k) ^ 2 * p).coeff 1 = 0 :=
    by simpa using Polynomial.coeff_X_pow_mul' p 2 1
  exact zero_ne_one (hz.symm.trans (hc.symm.trans Polynomial.coeff_X_one))

/-- The actual pullback on global functions sends the divisor coordinate `z` to `xy`. -/
lemma nonFlatTransverseMap_pull_coordinate :
    (nonFlatTransverseMap k D).ambient.hom.left.appTop
      ((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.polynomial (SmoothAlg.point k))))).inv
        (SmoothAlg.polynomialX (SmoothAlg.polynomial (SmoothAlg.point k)))) =
      (Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.laurent (SmoothAlg.point k))))).inv
        (SmoothAlg.polynomialC (SmoothAlg.laurent (SmoothAlg.point k))
          (SmoothAlg.laurentT (SmoothAlg.point k)) *
            SmoothAlg.polynomialX (SmoothAlg.laurent (SmoothAlg.point k))) := by
  change (specMap (OrlikSolomon.DeRham.Examples.nonFlatAmbient k).hom).left.appTop _ = _
  rw [specMap_left_appTop_ΓSpecIso_inv]
  exact congrArg (Scheme.ΓSpecIso
    (.of (SmoothAlg.polynomial (SmoothAlg.laurent (SmoothAlg.point k))))).inv
      (OrlikSolomon.DeRham.Examples.nonFlatAmbient_polynomialX k)

/-- The actual pullback on global functions kills the second plane coordinate `v`. -/
lemma nonFlatTransverseMap_pull_killed_coordinate :
    (nonFlatTransverseMap k D).ambient.hom.left.appTop
      ((Scheme.ΓSpecIso (.of (SmoothAlg.polynomial (SmoothAlg.polynomial (SmoothAlg.point k))))).inv
        (SmoothAlg.polynomialC (SmoothAlg.polynomial (SmoothAlg.point k))
          (SmoothAlg.polynomialX (SmoothAlg.point k)))) = 0 := by
  change (specMap (OrlikSolomon.DeRham.Examples.nonFlatAmbient k).hom).left.appTop _ = _
  rw [specMap_left_appTop_ΓSpecIso_inv]
  exact (congrArg (Scheme.ΓSpecIso
    (.of (SmoothAlg.polynomial (SmoothAlg.laurent (SmoothAlg.point k))))).inv
      (OrlikSolomon.DeRham.Examples.nonFlatAmbient_polynomialC_polynomialX k)).trans (map_zero _)

private lemma spectrumThetaSection_pull (P Q : OrlikSolomon.DivisorPair k) (F : P ⟶ Q)
    (u : Q.ambientˣ) (hu : F.ambient P.eqn = u * Q.eqn) :
    DeRham.formsSheafPullbackTop (specMap F.compl.hom) 1 (spectrumThetaSection k P) =
      spectrumThetaSection k Q +
        DeRham.formsSheafPullbackTop (specMap Q.j.hom) 1
          (specFormSection k Q.ambient.obj 1
            ⟨OrlikSolomon.DeRham.dlog k u,
              OrlikSolomon.DeRham.dlog_mem_exteriorPower_one k u⟩) := by
  have h := specFormSection_pull k F.compl.hom 1
    ⟨OrlikSolomon.DeRham.theta k P.eqn P.compl,
      OrlikSolomon.DeRham.theta_mem_exteriorPower_one k P.eqn P.compl⟩
  have hj := specFormSection_pull k Q.j.hom 1
    ⟨OrlikSolomon.DeRham.dlog k u, OrlikSolomon.DeRham.dlog_mem_exteriorPower_one k u⟩
  refine h.trans ?_
  have hn : OrlikSolomon.DeRham.Forms.mapPower F.compl.hom.hom 1
      ⟨OrlikSolomon.DeRham.theta k P.eqn P.compl,
        OrlikSolomon.DeRham.theta_mem_exteriorPower_one k P.eqn P.compl⟩ =
      (⟨OrlikSolomon.DeRham.theta k Q.eqn Q.compl,
        OrlikSolomon.DeRham.theta_mem_exteriorPower_one k Q.eqn Q.compl⟩ :
          ⋀[Q.compl]^1 Ω[Q.compl⁄k]) +
      OrlikSolomon.DeRham.Forms.mapPower Q.j.hom.hom 1
        ⟨OrlikSolomon.DeRham.dlog k u, OrlikSolomon.DeRham.dlog_mem_exteriorPower_one k u⟩ :=
    Subtype.ext (F.isPairHom.map_theta hu)
  exact (congrArg (specFormSection k Q.compl.obj 1) hn).trans
    ((map_add (specFormSection k Q.compl.obj 1) _ _).trans (congrArg
      (fun a => spectrumThetaSection k Q + a) hj.symm))

/-- The actual regular global one-form `dy/y` on the Laurent-polynomial ambient surface. -/
def laurentUnitCorrection :
    (DeRham.formsSheaf k
      (spec (OrlikSolomon.DivisorPair.standardPair
        (SmoothAlg.laurent (SmoothAlg.point k))).ambient.obj) 1).obj.obj (op ⊤) :=
  specFormSection k
    (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))).ambient.obj 1
    ⟨OrlikSolomon.DeRham.dlog k (SmoothAlg.mapUnits
      (SmoothAlg.polynomialC (SmoothAlg.laurent (SmoothAlg.point k)))
      (SmoothAlg.laurentT (SmoothAlg.point k))), OrlikSolomon.DeRham.dlog_mem_exteriorPower_one k _⟩

/-- The flat unit-change map pulls `dz/z` back to `dx/x` plus the regular form `dy/y`. -/
lemma unitChangeMap_thetaSection :
    DeRham.formsSheafPullbackTop (unitChangeMap k D).compl.hom 1
        (spectrumThetaSection k (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k))) =
      spectrumThetaSection k
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))) +
        DeRham.formsSheafPullbackTop
          (specMap (OrlikSolomon.DivisorPair.standardPair
            (SmoothAlg.laurent (SmoothAlg.point k))).j.hom) 1 (laurentUnitCorrection k) :=
  spectrumThetaSection_pull k _ _ (OrlikSolomon.DeRham.Examples.unitChangeHom k) _
    (OrlikSolomon.DeRham.Examples.unitChangeHom_ambient_polynomialX k)

/-- The non-flat map has the same actual sheaf-form pullback `dz/z = dx/x + dy/y`. -/
lemma nonFlatTransverseMap_thetaSection :
    DeRham.formsSheafPullbackTop (nonFlatTransverseMap k D).compl.hom 1
        (spectrumThetaSection k (OrlikSolomon.DivisorPair.standardPair
          (SmoothAlg.polynomial (SmoothAlg.point k)))) =
      spectrumThetaSection k
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))) +
        DeRham.formsSheafPullbackTop
          (specMap (OrlikSolomon.DivisorPair.standardPair
            (SmoothAlg.laurent (SmoothAlg.point k))).j.hom) 1 (laurentUnitCorrection k) :=
  spectrumThetaSection_pull k _ _ (OrlikSolomon.DeRham.Examples.nonFlatHom k) _
    (OrlikSolomon.DeRham.Examples.nonFlatAmbient_polynomialX k)

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory D ℬ)

/-- Gysin naturality holds on the actual non-flat geometric pair map in every ordinary theory. -/
theorem nonFlatTransverseMap_gysin_naturality
    (c : T.obj (DivisorPair.spec D
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point k)))).closed) :
    T.gysin (DivisorPair.spec D
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))))
        (T.pull (nonFlatTransverseMap k D).closed c) =
      T.pull (nonFlatTransverseMap k D).ambient
        (T.gysin (DivisorPair.spec D
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point k)))) c) :=
  T.gysin_pull (nonFlatTransverseMap k D) c

/-- Residue naturality holds on the actual non-flat geometric pair map in every ordinary theory. -/
theorem nonFlatTransverseMap_residue_naturality
    (c : T.obj (DivisorPair.spec D
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point k)))).compl) :
    T.residue (DivisorPair.spec D
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))))
        (T.pull (nonFlatTransverseMap k D).compl c) =
      T.pull (nonFlatTransverseMap k D).closed
        (T.residue (DivisorPair.spec D
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point k)))) c) :=
  T.residue_pull (nonFlatTransverseMap k D) c

/-- The pulled-back geometric logarithm has normalized residue one despite ambient non-flatness. -/
lemma nonFlatTransverseMap_residue_logarithm :
    T.residue (DivisorPair.spec D
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point k))))
      (T.pull (nonFlatTransverseMap k D).compl
        (T.logClass (DivisorPair.spec D
          (OrlikSolomon.DivisorPair.standardPair
            (SmoothAlg.polynomial (SmoothAlg.point k)))).eqnUnit)) = 1 := by
  exact (T.residue_pull (nonFlatTransverseMap k D) _).trans
    ((congrArg (T.pull (nonFlatTransverseMap k D).closed)
      (T.residue_logClass_eqnUnit _)).trans (map_one _))

section CharacteristicZero
variable (K : Type u) [Field K] [CharZero K]

/-- The actual affine de Rham class of `dz/z` on the source of the ramified pullback. -/
def ramifiedSourceLogClass : DeRham.Cohomology (standardSpecPair K (SmoothDomain.aff K)).compl :=
  (specCohomologyEquiv K
    (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point K)).compl.obj).symm
    (OrlikSolomon.DeRham.Cohomology.mk
      (OrlikSolomon.DeRham.theta K
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point K)).eqn
        (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point K)).compl)
      (OrlikSolomon.DeRham.d_theta _ _ _))

/-- The actual affine de Rham residue after squaring is two, reflecting the doubled divisor. -/
lemma ramifiedMap_residue_theta :
    DeRham.residue (standardSpecPair K (SmoothDomain.aff K))
      (DeRham.Cohomology.pull (ramifiedOpenMap K (SmoothDomain.aff K)) (ramifiedSourceLogClass K)) =
        2 := by
  let P := OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point K)
  let e := specCohomologyEquiv K P.compl.obj
  let c := OrlikSolomon.DeRham.Cohomology.mk
    (OrlikSolomon.DeRham.theta K P.eqn P.compl) (OrlikSolomon.DeRham.d_theta _ _ _)
  apply (specCohomologyEquiv K P.closed.obj).injective
  have hp := specCohomologyEquiv_pull K
    (OrlikSolomon.DeRham.Examples.ramifiedComplement K).hom (e.symm c)
  have hp := hp.trans (congrArg
    (OrlikSolomon.DeRham.Cohomology.map
      (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.ramifiedComplement K)))
        (e.apply_symm_apply c))
  have hr := specCohomologyEquiv_residue K P
    (DeRham.Cohomology.pull (ramifiedOpenMap K (SmoothDomain.aff K)) (ramifiedSourceLogClass K))
  exact hr.trans ((congrArg
    (OrlikSolomon.DeRham.residue P.compl (OrlikSolomon.DeRham.isUnit_natCast_add_one K)
      P.isSmoothPrincipalPair) hp).trans
        ((OrlikSolomon.DeRham.Examples.ramified_residue_theta K
          (OrlikSolomon.DeRham.isUnit_natCast_add_one K)).trans
            (map_ofNat (specCohomologyEquiv K P.closed.obj) 2).symm))

/-- The actual affine de Rham class of `dz/z` on the plane complement. -/
def nonFlatSourceLogClass : DeRham.Cohomology
    (DivisorPair.spec (SmoothDomain.aff K) (OrlikSolomon.DivisorPair.standardPair
      (SmoothAlg.polynomial (SmoothAlg.point K)))).compl :=
  (specCohomologyEquiv K (OrlikSolomon.DivisorPair.standardPair
    (SmoothAlg.polynomial (SmoothAlg.point K))).compl.obj).symm
      (OrlikSolomon.DeRham.Cohomology.mk
        (OrlikSolomon.DeRham.theta K
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point K))).eqn
          (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point K))).compl)
        (OrlikSolomon.DeRham.d_theta _ _ _))

/-- The actual affine de Rham residue of the non-flat pullback of `dz/z` is one. -/
lemma nonFlatTransverseMap_deRham_residue_theta :
    DeRham.residue (DivisorPair.spec (SmoothDomain.aff K)
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point K))))
      (DeRham.Cohomology.pull (nonFlatTransverseMap K (SmoothDomain.aff K)).compl
        (nonFlatSourceLogClass K)) = 1 := by
  let P := OrlikSolomon.DivisorPair.standardPair (SmoothAlg.polynomial (SmoothAlg.point K))
  let Q := OrlikSolomon.DivisorPair.standardPair (SmoothAlg.laurent (SmoothAlg.point K))
  let e := specCohomologyEquiv K P.compl.obj
  let c := OrlikSolomon.DeRham.Cohomology.mk
    (OrlikSolomon.DeRham.theta K P.eqn P.compl) (OrlikSolomon.DeRham.d_theta _ _ _)
  apply (specCohomologyEquiv K Q.closed.obj).injective
  have hp := specCohomologyEquiv_pull K
    (OrlikSolomon.DeRham.Examples.nonFlatHom K).compl.hom (e.symm c)
  have hp := hp.trans (congrArg
    (OrlikSolomon.DeRham.Cohomology.map
      (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.nonFlatHom K).compl))
        (e.apply_symm_apply c))
  have hr := specCohomologyEquiv_residue K Q
    (DeRham.Cohomology.pull (nonFlatTransverseMap K (SmoothDomain.aff K)).compl
      (nonFlatSourceLogClass K))
  have ho := OrlikSolomon.DeRham.Examples.nonFlatHom_residue_map K
    (OrlikSolomon.DeRham.isUnit_natCast_add_one K) c
  have ho := ho.trans ((congrArg
    (OrlikSolomon.DeRham.Cohomology.map
      (SmoothAlg.algHom (OrlikSolomon.DeRham.Examples.nonFlatHom K).closed))
      (OrlikSolomon.DeRham.Examples.residue_mk_theta_localization _
        (OrlikSolomon.DeRham.isUnit_natCast_add_one K) P.isSmoothPrincipalPair)).trans (map_one _))
  exact hr.trans ((congrArg
    (OrlikSolomon.DeRham.residue Q.compl (OrlikSolomon.DeRham.isUnit_natCast_add_one K)
      Q.isSmoothPrincipalPair) hp).trans
        (ho.trans (specCohomologyEquiv K Q.closed.obj).map_one.symm))

end CharacteristicZero

end OrlikSolomon.Geometric.Examples
