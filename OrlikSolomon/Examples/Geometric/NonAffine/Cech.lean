/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import OrlikSolomon.Examples.DeRhamCalculations.Torus
public import OrlikSolomon.Examples.Geometric.NonAffine.Fiber
public import OrlikSolomon.Examples.Geometric.NonAffine.MatchingForms

/-!
# The two-chart Čech–de Rham complex of the projective line

The charts have rings `k[X]` and `k[Y]`, with overlap `k[T;T⁻¹]` and coordinates `X = T`,
`Y = T⁻¹`. The total complex is the homotopy fiber of the difference of restrictions, with
total differential `δ + (-1)^a d` in Čech degree `a`.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.DeRham
open scoped Polynomial LaurentPolynomial

universe u

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u)

section Ring
variable [CommRing k]

/-- The first chart coordinate is the Laurent coordinate. -/
def projectiveLineFirstRestriction : k[X] →ₐ[k] k[T;T⁻¹] := Polynomial.toLaurentAlg

/-- The second chart coordinate is the inverse Laurent coordinate. -/
def projectiveLineSecondRestriction : k[X] →ₐ[k] k[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

/-- The modules of regular forms on the two charts, taken together. -/
@[implicit_reducible]
def projectiveLineChartTerm (n : ℕ) : ModuleCat k :=
  ModuleCat.of k ((complex k k[X]).X n × (complex k k[X]).X n)

/-- The componentwise de Rham differential on the charts. -/
def projectiveLineChartDifferential (n : ℕ) :
    projectiveLineChartTerm k n →ₗ[k] projectiveLineChartTerm k (n + 1) :=
  ((complex k k[X]).d n (n + 1)).hom.prodMap ((complex k k[X]).d n (n + 1)).hom

/-- The sum of the two affine-chart de Rham complexes. -/
def projectiveLineChartComplex : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (projectiveLineChartTerm k)
    (fun n => ModuleCat.ofHom (projectiveLineChartDifferential k n)) (fun n => by
      ext x
      apply Prod.ext <;>
        change ((complex k k[X]).d n (n + 1) ≫
          (complex k k[X]).d (n + 1) (n + 2)) _ = 0 <;>
        rw [HomologicalComplex.d_comp_d] <;> rfl)

@[simp]
lemma projectiveLineChartComplex_d (n : ℕ) :
    (projectiveLineChartComplex k).d n (n + 1) =
      ModuleCat.ofHom (projectiveLineChartDifferential k n) := by
  simp only [projectiveLineChartComplex, CochainComplex.of_d]

/-- The Čech difference `β| - α|` from the two charts to their intersection. -/
def projectiveLineRestrictionDifference : projectiveLineChartComplex k ⟶ complex k k[T;T⁻¹] :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    (((complexMap (projectiveLineSecondRestriction k)).f n).hom.comp (LinearMap.snd k _ _) -
      ((complexMap (projectiveLineFirstRestriction k)).f n).hom.comp (LinearMap.fst k _ _)))
    (fun n => by
      rw [projectiveLineChartComplex_d]
      ext x
      change (complex k k[T;T⁻¹]).d n (n + 1)
        ((complexMap (projectiveLineSecondRestriction k)).f n x.2 -
          (complexMap (projectiveLineFirstRestriction k)).f n x.1) =
        (complexMap (projectiveLineSecondRestriction k)).f (n + 1)
          ((complex k k[X]).d n (n + 1) x.2) -
        (complexMap (projectiveLineFirstRestriction k)).f (n + 1)
          ((complex k k[X]).d n (n + 1) x.1)
      rw [map_sub]
      exact congrArg₂ (· - ·)
        congr($((complexMap (projectiveLineSecondRestriction k)).comm n (n + 1)) x.2)
        congr($((complexMap (projectiveLineFirstRestriction k)).comm n (n + 1)) x.1))

/-- The actual two-chart total complex, built from the existing algebraic de Rham complexes. -/
def projectiveLineCechComplex : CochainComplex (ModuleCat k) ℕ :=
  twoChartFiber (projectiveLineRestrictionDifference k)

end Ring

section CharacteristicZero

variable [Field k] [CharZero k]

/-- A polynomial chart has no positive-degree de Rham homology. -/
theorem polynomialComplex_isZero_homology_succ (n : ℕ) :
    Limits.IsZero ((complex k k[X]).homology (n + 1)) := by
  apply Limits.IsZero.of_iso ?_ (homologyIso k k[X] (n + 1))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (c : OrlikSolomon.DeRham.Cohomology.degree k k[X] (n + 1)) :
      (c : OrlikSolomon.DeRham.Cohomology k k[X]) = 0 := by
    apply (polynomialCohomologyEquiv k k (isUnit_natCast_add_one k)).symm.injective
    rw [map_zero, polynomialCohomologyEquiv_symm_apply]
    exact OrlikSolomon.DeRham.Cohomology.eq_zero_of_mem_degree_point (Nat.succ_ne_zero n)
      (OrlikSolomon.DeRham.Cohomology.map_mem_degree _ c.2)
  exact ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩

/-- Both polynomial charts are exact in every positive degree. -/
theorem projectiveLineChartComplex_exactAt_succ (n : ℕ) :
    (projectiveLineChartComplex k).ExactAt (n + 1) := by
  have h := ((complex k k[X]).exactAt_iff_isZero_homology (n + 1)).mpr
    (polynomialComplex_isZero_homology_succ k n)
  have hprev := (ComplexShape.up ℕ).prev_eq'
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
  have hnext := CochainComplex.next ℕ (n + 1)
  rw [(complex k k[X]).exactAt_iff' n (n + 1) (n + 2) hprev hnext] at h
  rw [(projectiveLineChartComplex k).exactAt_iff' n (n + 1) (n + 2) hprev hnext]
  rw [ShortComplex.moduleCat_exact_iff] at h ⊢
  intro x hx
  change (projectiveLineChartComplex k).d (n + 1) (n + 2) x = 0 at hx
  rw [projectiveLineChartComplex_d] at hx
  have hx₁ : (complex k k[X]).d (n + 1) (n + 2) x.1 = 0 := congrArg Prod.fst hx
  have hx₂ : (complex k k[X]).d (n + 1) (n + 2) x.2 = 0 := congrArg Prod.snd hx
  obtain ⟨a, ha⟩ := h x.1 hx₁
  obtain ⟨b, hb⟩ := h x.2 hx₂
  refine ⟨(a, b), ?_⟩
  change (projectiveLineChartComplex k).d n (n + 1) (a, b) = x
  rw [projectiveLineChartComplex_d]
  exact Prod.ext ha hb

/-- Positive-degree homology of the pair of charts vanishes. -/
theorem projectiveLineChartComplex_isZero_homology_succ (n : ℕ) :
    Limits.IsZero ((projectiveLineChartComplex k).homology (n + 1)) :=
  (projectiveLineChartComplex_exactAt_succ k n).isZero_homology

/-- Inclusion of the ordered logarithmic generator identifies `k` with the overlap's `H¹`. -/
def overlapDegreeOneMap : k →ₗ[k]
    OrlikSolomon.DeRham.Cohomology.degree k k[T;T⁻¹] 1 :=
  (((OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).toLinearMap).comp
    (LinearMap.inr k k k)).codRestrict _ (fun a =>
      (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_one_iff k 0 a).mpr rfl)

/-- The degree-one cohomology of the overlap is generated freely by `[dx/x]`. -/
def overlapDegreeOneEquiv : k ≃ₗ[k]
    OrlikSolomon.DeRham.Cohomology.degree k k[T;T⁻¹] 1 :=
  LinearEquiv.ofBijective (overlapDegreeOneMap k) (by
    constructor
    · intro a b h
      have hh := congrArg Subtype.val h
      change OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k (0, a) =
        OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k (0, b) at hh
      exact congrArg Prod.snd ((OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).injective hh)
    · intro c
      obtain ⟨⟨a, b⟩, hab⟩ := (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).surjective
        (c : OrlikSolomon.DeRham.Cohomology k k[T;T⁻¹])
      have ha := (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_one_iff k a b).mp
        (hab ▸ c.2)
      subst a
      exact ⟨b, Subtype.ext hab⟩)

/-- The overlap coefficient one is the existing class `[dT/T]`, with its degree witness. -/
lemma overlapDegreeOneEquiv_one_val :
    (overlapDegreeOneEquiv k 1).val =
      OrlikSolomon.DeRham.Examples.laurentThetaClass k (SmoothAlg.point k) := by
  change OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k (0, 1) = _
  simp only [OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_apply, map_zero, map_one,
    mul_one, zero_add]

/-- Inclusion of the shifted overlap identifies its second homology with the Čech homology. -/
def projectiveLineCechOverlapHomologyTwoIso :
    (twoChartOverlap (complex k k[T;T⁻¹])).homology 2 ≅
      (projectiveLineCechComplex k).homology 2 := by
  let S := twoChartFiberSequence (projectiveLineRestrictionDifference k)
  have hS : S.ShortExact := twoChartFiberSequence_shortExact _
  let i := HomologicalComplex.homologyMap S.f 2
  have hmono : Mono i := (hS.homology_exact₁ 1 2 rfl).mono_g
    ((projectiveLineChartComplex_isZero_homology_succ k 0).eq_of_src _ _)
  have hepi : Epi i := (hS.homology_exact₂ 2).epi_f
    ((projectiveLineChartComplex_isZero_homology_succ k 1).eq_of_tgt _ _)
  letI : IsIso i := isIso_of_mono_of_epi i
  exact @asIso _ _ _ _ i (isIso_of_mono_of_epi i)

/-- The two-chart Čech complex has `H² = k`, although global forms on `ℙ¹` do not. -/
def projectiveLineCechHomologyTwoEquiv :
    (projectiveLineCechComplex k).homology 2 ≃ₗ[k] k :=
  ((projectiveLineCechOverlapHomologyTwoIso k).symm ≪≫
    twoChartOverlapHomologySuccIso (B := complex k k[T;T⁻¹]) 0 ≪≫
    homologyIso k k[T;T⁻¹] 1 ≪≫ (overlapDegreeOneEquiv k).toModuleIso.symm).toLinearEquiv

/-- The overlap logarithmic generator enters degree two through the inclusion of the
shifted overlap complex. Thus this is the Čech class `[dT/T]`. -/
def projectiveLineCechLogClass : (projectiveLineCechComplex k).homology 2 :=
  (projectiveLineCechOverlapHomologyTwoIso k).hom
      ((twoChartOverlapHomologySuccIso (B := complex k k[T;T⁻¹]) 0 ≪≫
        homologyIso k k[T;T⁻¹] 1).inv (overlapDegreeOneEquiv k 1))

/-- The degree-two comparison sends the overlap logarithmic class to one. -/
@[simp]
lemma projectiveLineCechHomologyTwoEquiv_logClass :
    projectiveLineCechHomologyTwoEquiv k (projectiveLineCechLogClass k) = 1 := by
  change (overlapDegreeOneEquiv k).symm
    ((homologyIso k k[T;T⁻¹] 1).hom
      ((twoChartOverlapHomologySuccIso (B := complex k k[T;T⁻¹]) 0).hom
        ((projectiveLineCechOverlapHomologyTwoIso k).inv
          (projectiveLineCechLogClass k)))) = 1
  dsimp only [projectiveLineCechLogClass, Iso.trans_inv, ModuleCat.comp_apply]
  rw [Iso.hom_inv_id_apply, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply, LinearEquiv.symm_apply_apply]

/-- The degree-two Čech class detected by the overlap logarithmic coefficient is nonzero. -/
theorem projectiveLineCechHomologyTwo_generator_ne_zero :
    (projectiveLineCechHomologyTwoEquiv k).symm 1 ≠ 0 := by
  intro h
  have hh := congrArg (projectiveLineCechHomologyTwoEquiv k) h
  rw [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact one_ne_zero hh

/-- The Laurent overlap has no homology above degree one. -/
theorem overlapComplex_isZero_homology_succ_succ (n : ℕ) :
    Limits.IsZero ((complex k k[T;T⁻¹]).homology (n + 2)) := by
  apply Limits.IsZero.of_iso ?_ (homologyIso k k[T;T⁻¹] (n + 2))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => Subtype.ext ?_⟩
  exact (OrlikSolomon.DeRham.Examples.gm_eq_zero_of_mem_degree_succ_succ k n x.2).trans
    (OrlikSolomon.DeRham.Examples.gm_eq_zero_of_mem_degree_succ_succ k n y.2).symm

/-- The two-chart total complex has no homology above degree two. -/
theorem projectiveLineCechComplex_isZero_homology_succ_succ_succ (n : ℕ) :
    Limits.IsZero ((projectiveLineCechComplex k).homology (n + 3)) := by
  have hB : Limits.IsZero ((twoChartOverlap (complex k k[T;T⁻¹])).homology (n + 3)) :=
    Limits.IsZero.of_iso (overlapComplex_isZero_homology_succ_succ k n)
      (twoChartOverlapHomologySuccIso (B := complex k k[T;T⁻¹]) (n + 1))
  have hS := twoChartFiberSequence_shortExact (projectiveLineRestrictionDifference k)
  exact (hS.homology_exact₂ (n + 3)).isZero_of_both_isZero hB
    (projectiveLineChartComplex_isZero_homology_succ k (n + 2))

/-- The two-chart total complex is exact in degree one. The difference of constants already
surjects onto the closed overlap functions. -/
theorem projectiveLineCechComplex_exactAt_one : (projectiveLineCechComplex k).ExactAt 1 := by
  apply twoChartFiber_exactAt_one (projectiveLineRestrictionDifference k)
    (projectiveLineChartComplex_exactAt_succ k 0)
  intro b hb
  change (⋀[k[T;T⁻¹]]^0 Ω[k[T;T⁻¹]⁄k]) at b
  rw [complex_d] at hb
  have hb' := congrArg Subtype.val hb
  change d k (b : Forms k k[T;T⁻¹]) = 0 at hb'
  obtain ⟨c, hc⟩ := NonAffine.closedLaurentZero_eq_constant b hb'
  refine ⟨(0, NonAffine.polynomialConstantForm c), ?_, ?_⟩
  · rw [projectiveLineChartComplex_d]
    apply Prod.ext
    · change (complex k k[X]).d 0 1 0 = 0
      exact map_zero _
    · change powerD k k[X] 0 (NonAffine.polynomialConstantForm c) = 0
      apply Subtype.ext
      change d k (algebraMap k (Forms k k[X]) c) = 0
      rw [IsScalarTower.algebraMap_apply k k[X] (Forms k k[X]), d_algebraMap,
        Derivation.map_algebraMap]
  · change Forms.mapPower (projectiveLineSecondRestriction k) 0
      (NonAffine.polynomialConstantForm c) -
        Forms.mapPower (projectiveLineFirstRestriction k) 0 0 = b
    rw [map_zero, sub_zero]
    apply Subtype.ext
    change Forms.map (projectiveLineSecondRestriction k) (algebraMap k (Forms k k[X]) c) = b.val
    rw [AlgHom.commutes, hc]

/-- The two-chart Čech–de Rham complex has zero first cohomology. -/
theorem projectiveLineCechComplex_isZero_homology_one :
    Limits.IsZero ((projectiveLineCechComplex k).homology 1) :=
  (projectiveLineCechComplex_exactAt_one k).isZero_homology

end CharacteristicZero

end OrlikSolomon.Geometric.Examples
