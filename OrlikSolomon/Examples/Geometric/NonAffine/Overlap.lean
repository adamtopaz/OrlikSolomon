/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Charts

/-!
# The Laurent overlap of the projective-line charts

The intersection of the two standard charts has ring `k[T,T⁻¹]`. The two restriction maps
from `k[X]` send the coordinate respectively to `T` and `T⁻¹`. The construction uses the
existing homogeneous projective-complement rings and their actual open immersions.

Blueprint: the two-chart calculation of `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module Polynomial HomogeneousLocalization
open scoped LaurentPolynomial

namespace OrlikSolomon.Geometric.Examples

open ProjectiveArrangement ProjectiveArrangement.ComplementRing CoordinateRing

section Inclusion

universe u
variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]
variable (P Q : ProjectiveArrangement k W) [Nonempty P] [Nonempty Q]
variable (h : P.cone.equationSubmonoid ≤ Q.cone.equationSubmonoid)

private def incRing : P.ComplementRing →+* Q.ComplementRing :=
  mapId (symmetricGrading k (Dual k W)) h
omit [Nonempty P] [Nonempty Q] in
private lemma mapId_comp_awayEquiv :
    (incRing P Q h).comp
        (awayEquiv (P := P) form ker_form).toRingHom =
      mapId (symmetricGrading k (Dual k W))
        ((powers_prod_coord_le (P := P) form ker_form).trans h) := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rfl

private lemma complementInclusion_square :
    Spec.map (CommRingCat.ofHom (R := P.ComplementRing) (S := Q.ComplementRing)
      (incRing P Q h)) ≫
      complementι P = complementι Q := by
  rw [complementι_eq_awayι, complementι_eq_awayι, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, mapId_comp_awayEquiv]
  have hP := ((powers_prod_coord_le (P := P) form ker_form).trans h)
  have hQ := powers_prod_coord_le (P := Q) form ker_form
  have hPQ : Submonoid.powers (formProduct P * formProduct Q) ≤ Q.cone.equationSubmonoid :=
    Submonoid.powers_le.mpr (mul_mem (hP (Submonoid.mem_powers _)) (hQ (Submonoid.mem_powers _)))
  change Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hP)) ≫
      Proj.awayι _ (formProduct P) (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P) =
    Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hQ)) ≫
      Proj.awayι _ (formProduct Q) (formProduct_mem_symmetricGrading Q) (card_pos_of_nonempty Q)
  have step {f g : CoordinateRing k W} {d e : ℕ}
      (hf : f ∈ symmetricGrading k (Dual k W) d) (hd : 0 < d)
      (hg : g ∈ symmetricGrading k (Dual k W) e)
      (hfM : Submonoid.powers f ≤ Q.cone.equationSubmonoid)
      (hfgM : Submonoid.powers (f * g) ≤ Q.cone.equationSubmonoid) :
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hfM)) ≫
        Proj.awayι _ f hf hd =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hfgM)) ≫
        Proj.awayι _ (f * g) (SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) := by
    rw [← Proj.SpecMap_awayMap_awayι (symmetricGrading k (Dual k W)) hf hd hg rfl,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      mapId_comp_awayMap _ hf hg hfM hfgM]
  rw [step (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P)
    (formProduct_mem_symmetricGrading Q) hP hPQ]
  have hQP : Submonoid.powers (formProduct Q * formProduct P) ≤ Q.cone.equationSubmonoid :=
    Submonoid.powers_le.mpr (mul_mem (hQ (Submonoid.mem_powers _)) (hP (Submonoid.mem_powers _)))
  rw [step (formProduct_mem_symmetricGrading Q) (card_pos_of_nonempty Q)
    (formProduct_mem_symmetricGrading P) hQ hQP]
  have congr {a b : CoordinateRing k W} (hab : a = b) {d e : ℕ} (hde : d = e)
      (ha : a ∈ symmetricGrading k (Dual k W) d)
      (hb : b ∈ symmetricGrading k (Dual k W) e) (hd : 0 < d) (he : 0 < e)
      (hMa : Submonoid.powers a ≤ Q.cone.equationSubmonoid)
      (hMb : Submonoid.powers b ≤ Q.cone.equationSubmonoid) :
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hMa)) ≫
        Proj.awayι _ a ha hd =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hMb)) ≫
        Proj.awayι _ b hb he := by
    subst b; subst e; rfl
  exact congr (mul_comm _ _) (Nat.add_comm _ _) _ _ _ _ _ _

end Inclusion

universe u
variable (k : Type u) [Field k]

private abbrev l (i : Fin 2) := projectiveLineCoordinate k i

private lemma lne (i : Fin 2) : l k i ≠ 0 := projectiveLineCoordinate_ne_zero k i

/-- The two coordinate points omitted by the chart overlap. -/
@[no_expose] def projectiveLineOverlapArrangement : ProjectiveArrangement k (Fin 2 → k) := by
  classical
  exact ofForms {l k 0, l k 1} (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro m (rfl | rfl) <;> exact lne k _)

/-- Both coordinate hyperplanes belong to the overlap arrangement. -/
lemma projectiveLineCoordinate_ker_mem_overlap (i : Fin 2) :
    LinearMap.ker (projectiveLineCoordinate k i) ∈ projectiveLineOverlapArrangement k := by
  classical
  apply ker_mem_ofForms
  fin_cases i <;> simp

/-- The coordinate-point arrangement is nonempty. -/
instance projectiveLineOverlapArrangement_nonempty :
    Nonempty (projectiveLineOverlapArrangement k) :=
  nonempty_of_ker_mem (projectiveLineCoordinate_ker_mem_overlap k 0)

private def subLinear : Dual k (Fin 2 → k) →ₗ[k] LaurentPolynomial k where
  toFun m := LaurentPolynomial.C (m (Pi.single 0 1)) +
    LaurentPolynomial.C (m (Pi.single 1 1)) * LaurentPolynomial.T 1
  map_add' m n := by simp [add_mul, add_add_add_comm]
  map_smul' a m := by simp [Algebra.smul_def, mul_add, mul_assoc]

private def subst : CoordinateRing k (Fin 2 → k) →ₐ[k] LaurentPolynomial k :=
  SymmetricAlgebra.lift (subLinear k)

private lemma subst_coord (m : Dual k (Fin 2 → k)) :
    subst k (coord m.toAffineMap) = LaurentPolynomial.C (m (Pi.single 0 1)) +
      LaurentPolynomial.C (m (Pi.single 1 1)) * LaurentPolynomial.T 1 := by
  rw [coord_toAffineMap, subst, SymmetricAlgebra.lift_ι_apply]
  rfl

private lemma subst_zero : subst k (coord (l k 0).toAffineMap) = 1 := by
  rw [subst_coord]
  simp [l, projectiveLineCoordinate]

private lemma subst_one : subst k (coord (l k 1).toAffineMap) = LaurentPolynomial.T 1 := by
  rw [subst_coord]
  simp [l, projectiveLineCoordinate]

private def coneEval :
    (projectiveLineOverlapArrangement k).cone.ComplementRing →ₐ[k] LaurentPolynomial k :=
  Arrangement.ComplementRing.lift _ (subst k) fun K hK ↦ by
    classical
    obtain ⟨M, hM, rfl⟩ := mem_cone.mp hK
    obtain ⟨m, hm, rfl⟩ := mem_ofForms.mp hM
    rcases Finset.mem_insert.mp hm with hm | hm
    · subst m
      exact ⟨(l k 0).toAffineMap, isEquation_toAffineMap (lne k 0), by
        rw [subst_zero]; exact isUnit_one⟩
    · have hm' : m = l k 1 := Finset.mem_singleton.mp hm
      subst m
      exact ⟨(l k 1).toAffineMap, isEquation_toAffineMap (lne k 1), by
        rw [subst_one]; exact LaurentPolynomial.isUnit_T 1⟩

private lemma coneEval_coord (m : Dual k (Fin 2 → k)) :
    coneEval k (algebraMap _ _ (coord m.toAffineMap)) = LaurentPolynomial.C (m (Pi.single 0 1)) +
      LaurentPolynomial.C (m (Pi.single 1 1)) * LaurentPolynomial.T 1 := by
  rw [coneEval, Arrangement.ComplementRing.lift_algebraMap, subst_coord]

private def overlapEval :
    (projectiveLineOverlapArrangement k).ComplementRing →ₐ[k] LaurentPolynomial k :=
  (coneEval k).comp (toCone _)

private lemma overlapEval_ratio (m : Dual k (Fin 2 → k)) :
    overlapEval k (ratio m (projectiveLineCoordinate_ker_mem_overlap k 0)) =
      LaurentPolynomial.C (m (Pi.single 0 1)) +
      LaurentPolynomial.C (m (Pi.single 1 1)) * LaurentPolynomial.T 1 := by
  have h := congrArg (coneEval k)
    (toCone_ratio_mul m (projectiveLineCoordinate_ker_mem_overlap k 0))
  rw [map_mul, coneEval, Arrangement.ComplementRing.lift_algebraMap,
    subst_zero, mul_one, Arrangement.ComplementRing.lift_algebraMap, subst_coord] at h
  exact h

private def overlapInverse :
    LaurentPolynomial k →ₐ[k] (projectiveLineOverlapArrangement k).ComplementRing :=
  laurentPolynomialLift (Algebra.ofId k _)
    (ratioUnit (projectiveLineCoordinate_ker_mem_overlap k 1)
      (projectiveLineCoordinate_ker_mem_overlap k 0))

private lemma linear_decomp (m : Dual k (Fin 2 → k)) :
    m = m (Pi.single 0 1) • l k 0 + m (Pi.single 1 1) • l k 1 := by
  have hv (v : Fin 2 → k) : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext j; fin_cases j <;> simp
  apply LinearMap.ext
  intro v
  conv_lhs => rw [hv v, map_add, map_smul, map_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, projectiveLineCoordinate_apply, l,
    smul_eq_mul]
  ring

private lemma fixed_ratio (m : Dual k (Fin 2 → k)) :
    overlapInverse k (overlapEval k (ratio m (projectiveLineCoordinate_ker_mem_overlap k 0))) =
      ratio m (projectiveLineCoordinate_ker_mem_overlap k 0) := by
  rw [overlapEval_ratio]
  conv_rhs => rw [linear_decomp k m, ratio_add, ratio_smul, ratio_smul, ratio_self]
  simp [overlapInverse, laurentPolynomialLift_T, Algebra.smul_def]

/-- The ring of the overlap is the Laurent polynomial ring, with `T = X₁/X₀`. -/
@[no_expose] def projectiveLineOverlapRingEquiv :
    (projectiveLineOverlapArrangement k).ComplementRing ≃ₐ[k] LaurentPolynomial k :=
  AlgEquiv.ofAlgHom (overlapEval k) (overlapInverse k) (by
    apply laurentPolynomial_algHom_ext
    · intro a; simp [overlapInverse, laurentPolynomialLift_C]
    · rw [AlgHom.comp_apply, overlapInverse, laurentPolynomialLift_T, coe_ratioUnit,
        overlapEval_ratio]
      simp [projectiveLineCoordinate]) (by
    apply ProjectiveArrangement.ComplementRing.algHom_ext
    intro m n hn
    apply (ratioUnit hn (projectiveLineCoordinate_ker_mem_overlap k 0)).isUnit.mul_right_cancel
    change overlapInverse k (overlapEval k (ratio m hn)) *
      ratio n (projectiveLineCoordinate_ker_mem_overlap k 0) =
      ratio m hn * ratio n (projectiveLineCoordinate_ker_mem_overlap k 0)
    calc
      _ = overlapInverse k (overlapEval k (ratio m hn)) *
          overlapInverse k (overlapEval k
            (ratio n (projectiveLineCoordinate_ker_mem_overlap k 0))) := by
        rw [fixed_ratio]
      _ = overlapInverse k (overlapEval k
          (ratio m (projectiveLineCoordinate_ker_mem_overlap k 0))) := by
        rw [← map_mul, ← map_mul, ratio_mul_ratio]
      _ = _ := by rw [fixed_ratio, ratio_mul_ratio])

/-- The overlap removes every hyperplane removed by either individual chart. -/
lemma projectiveLineChart_cone_le_overlap (i : Fin 2) :
    (projectiveLineChartArrangement k i).cone ≤ (projectiveLineOverlapArrangement k).cone := by
  intro K hK
  obtain ⟨M, hM, rfl⟩ := mem_cone.mp hK
  obtain ⟨m, hm, rfl⟩ := mem_ofForms.mp hM
  have hm' : m = l k i := Finset.mem_singleton.mp hm
  subst m
  exact mem_cone.mpr ⟨_, projectiveLineCoordinate_ker_mem_overlap k i, rfl⟩

/-- Restriction from a standard chart to their intersection, as a map of rings. -/
def projectiveLineChartRingRestriction (i : Fin 2) :
    (projectiveLineChartArrangement k i).ComplementRing →ₐ[k]
      (projectiveLineOverlapArrangement k).ComplementRing where
  toRingHom := HomogeneousLocalization.mapId _
    (Arrangement.equationSubmonoid_mono (projectiveLineChart_cone_le_overlap k i))
  commutes' _ := rfl

/-- Restriction keeps a homogeneous-coordinate ratio. -/
lemma projectiveLineChartRingRestriction_ratio (i : Fin 2) (m : Dual k (Fin 2 → k)) :
    projectiveLineChartRingRestriction k i (ratio m (projectiveLineCoordinate_ker_mem k i)) =
      ratio m (projectiveLineCoordinate_ker_mem_overlap k i) := rfl

/-- The first chart coordinate restricts to the Laurent coordinate. -/
lemma projectiveLineOverlapRingEquiv_X :
    projectiveLineOverlapRingEquiv k (ratio (projectiveLineCoordinate k 1)
      (projectiveLineCoordinate_ker_mem_overlap k 0)) = LaurentPolynomial.T 1 := by
  change overlapEval k _ = _
  rw [overlapEval_ratio]
  simp [projectiveLineCoordinate]

/-- The second chart coordinate restricts to the inverse Laurent coordinate. -/
lemma projectiveLineOverlapRingEquiv_Y :
    projectiveLineOverlapRingEquiv k (ratio (projectiveLineCoordinate k 0)
      (projectiveLineCoordinate_ker_mem_overlap k 1)) = LaurentPolynomial.T (-1) := by
  apply (LaurentPolynomial.isUnit_T (R := k) 1).mul_right_cancel
  have h := congrArg (projectiveLineOverlapRingEquiv k)
    (ratio_mul_ratio (l k 0) (projectiveLineCoordinate_ker_mem_overlap k 0)
      (projectiveLineCoordinate_ker_mem_overlap k 1))
  rw [ratio_self, map_mul, projectiveLineOverlapRingEquiv_X, map_one] at h
  rw [h, ← LaurentPolynomial.T_add]
  simp

/-- In coordinates, restriction from the first chart is `X ↦ T`. -/
lemma projectiveLineChartRingRestriction_zero :
    (projectiveLineOverlapRingEquiv k).toAlgHom.comp
        ((projectiveLineChartRingRestriction k 0).comp
          (projectiveLineChartRingEquiv k 0).symm.toAlgHom) = Polynomial.toLaurentAlg := by
  apply Polynomial.algHom_ext
  change projectiveLineOverlapRingEquiv k (projectiveLineChartRingRestriction k 0
    ((projectiveLineChartRingEquiv k 0).symm X)) = Polynomial.toLaurent X
  rw [projectiveLineChartRingEquiv_symm_X, projectiveLineChartRingRestriction_ratio]
  simpa only [l, Fin.reduceRev, Polynomial.toLaurent_X] using projectiveLineOverlapRingEquiv_X k

/-- In coordinates, restriction from the second chart is `Y ↦ T⁻¹`. -/
lemma projectiveLineChartRingRestriction_one :
    (projectiveLineOverlapRingEquiv k).toAlgHom.comp
        ((projectiveLineChartRingRestriction k 1).comp
          (projectiveLineChartRingEquiv k 1).symm.toAlgHom) =
      LaurentPolynomial.invert.toAlgHom.comp (Polynomial.toLaurentAlg : k[X] →ₐ[k] _) := by
  apply Polynomial.algHom_ext
  change projectiveLineOverlapRingEquiv k (projectiveLineChartRingRestriction k 1
    ((projectiveLineChartRingEquiv k 1).symm X)) = LaurentPolynomial.invert (Polynomial.toLaurent X)
  rw [projectiveLineChartRingEquiv_symm_X, projectiveLineChartRingRestriction_ratio,
    Polynomial.toLaurent_X,
    LaurentPolynomial.invert_T]
  exact projectiveLineOverlapRingEquiv_Y k

/-- The actual open overlap of the two standard projective-line charts. -/
@[instance_reducible]
def projectiveLineOverlap : (projectiveLine k).left.Opens :=
  complementOpen (projectiveLineOverlapArrangement k)

/-- The coordinate-point complement is exactly the intersection of the two chart opens. -/
theorem projectiveLineOverlap_eq_inf :
    projectiveLineOverlap k = projectiveLineChart k 0 ⊓ projectiveLineChart k 1 := by
  classical
  rw [projectiveLineChart_eq_basicOpen, projectiveLineChart_eq_basicOpen]
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ complementOpen (projectiveLineOverlapArrangement k) ↔
    coord (projectiveLineCoordinate k 0).toAffineMap ∉ x.asHomogeneousIdeal ∧
      coord (projectiveLineCoordinate k 1).toAffineMap ∉ x.asHomogeneousIdeal
  rw [mem_complementOpen_iff]
  constructor
  · intro h
    exact ⟨h _ (projectiveLineCoordinate_ker_mem_overlap k 0),
      h _ (projectiveLineCoordinate_ker_mem_overlap k 1)⟩
  · rintro ⟨h0, h1⟩ m hm
    obtain ⟨n, hn, hnm⟩ := mem_ofForms.mp hm
    have hn' : n ≠ 0 := by
      rcases Finset.mem_insert.mp hn with hn | hn
      · exact hn ▸ lne k 0
      · exact (Finset.mem_singleton.mp hn) ▸ lne k 1
    have hb := basicOpen_coord_eq_of_ker_eq hnm.symm hn'
    have hx : x ∈ Proj.basicOpen (symmetricGrading k (Dual k (Fin 2 → k)))
        (coord n.toAffineMap) := by
      rcases Finset.mem_insert.mp hn with hn | hn
      · change coord n.toAffineMap ∉ x.asHomogeneousIdeal
        simpa only [hn, l] using h0
      · change coord n.toAffineMap ∉ x.asHomogeneousIdeal
        simpa only [Finset.mem_singleton.mp hn, l] using h1
    exact show x ∈ Proj.basicOpen _ (coord m.toAffineMap) from hb ▸ hx

/-- The overlap as the actual open subscheme with its base structure map. -/
@[instance_reducible]
def projectiveLineOverlapOver : Over (Spec (.of k)) :=
  projectiveComplement (projectiveLineOverlapArrangement k)

/-- The overlap of the standard charts is the spectrum of the Laurent polynomial ring. -/
def projectiveLineOverlapIso :
    projectiveLineOverlapOver k ≅ spec (CommAlgCat.of k (LaurentPolynomial k)) :=
  projectiveComplementIsoSpec (projectiveLineOverlapArrangement k) ≪≫
    ((specFunctor k).mapIso (CommAlgCat.isoMk (projectiveLineOverlapRingEquiv k)).op).symm

/-- The Laurent-spectrum chart map into the actual projective line. -/
def projectiveLineOverlapMap :
    spec (CommAlgCat.of k (LaurentPolynomial k)) ⟶ projectiveLine k :=
  (projectiveLineOverlapIso k).inv ≫ projectiveComplementι (projectiveLineOverlapArrangement k)

/-- The Laurent-spectrum chart map on underlying schemes. -/
theorem projectiveLineOverlapMap_left :
    (projectiveLineOverlapMap k).left =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapRingEquiv k).toRingHom) ≫
        ProjectiveArrangement.complementι (projectiveLineOverlapArrangement k) := rfl

/-- The Laurent-spectrum chart is an open immersion. -/
instance projectiveLineOverlapMap_isOpenImmersion :
    IsOpenImmersion (projectiveLineOverlapMap k).left := by
  change IsOpenImmersion ((projectiveLineOverlapIso k).inv.left ≫
    (projectiveComplementι (projectiveLineOverlapArrangement k)).left)
  infer_instance

/-- The Laurent-spectrum chart has precisely the overlap as its image. -/
theorem projectiveLineOverlapMap_opensRange :
    (projectiveLineOverlapMap k).left.opensRange = projectiveLineOverlap k := by
  change ((projectiveLineOverlapIso k).inv.left ≫
    (projectiveComplementι (projectiveLineOverlapArrangement k)).left).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (opensRange_projectiveComplementι (projectiveLineOverlapArrangement k))

private lemma restriction_complementι (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (projectiveLineChartRingRestriction k i).toRingHom) ≫
      ProjectiveArrangement.complementι (projectiveLineChartArrangement k i) =
        ProjectiveArrangement.complementι (projectiveLineOverlapArrangement k) :=
  complementInclusion_square _ _
    (Arrangement.equationSubmonoid_mono (projectiveLineChart_cone_le_overlap k i))

private lemma restriction_chartMap (i : Fin 2) :
    specMap (CommAlgCat.ofHom ((projectiveLineOverlapRingEquiv k).toAlgHom.comp
        ((projectiveLineChartRingRestriction k i).comp
          (projectiveLineChartRingEquiv k i).symm.toAlgHom))) ≫
      projectiveLineChartMap k i = projectiveLineOverlapMap k := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, projectiveLineChartMap_left, projectiveLineOverlapMap_left]
  change Spec.map (CommRingCat.ofHom _) ≫
      Spec.map (CommRingCat.ofHom (projectiveLineChartRingEquiv k i).toRingHom) ≫ _ = _
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have h : (((projectiveLineOverlapRingEquiv k).toAlgHom.comp
      ((projectiveLineChartRingRestriction k i).comp
        (projectiveLineChartRingEquiv k i).symm.toAlgHom)).toRingHom).comp
        (projectiveLineChartRingEquiv k i).toRingHom =
      (projectiveLineOverlapRingEquiv k).toRingHom.comp
        (projectiveLineChartRingRestriction k i).toRingHom := by
    apply RingHom.ext
    intro a
    exact congrArg (fun b => projectiveLineOverlapRingEquiv k
      (projectiveLineChartRingRestriction k i b))
      ((projectiveLineChartRingEquiv k i).symm_apply_apply a)
  simp only [CommAlgCat.hom_ofHom] at *
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, restriction_complementι]

/-- Restriction from the first affine-line chart to the overlap is the usual Laurent inclusion. -/
@[reassoc]
theorem projectiveLineChartMap_zero_overlap :
    specMap (CommAlgCat.ofHom (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k)) ≫
      projectiveLineChartMap k 0 = projectiveLineOverlapMap k := by
  rw [← projectiveLineChartRingRestriction_zero]
  exact restriction_chartMap k 0

/-- Restriction from the second affine-line chart sends its coordinate to the
inverse Laurent coordinate. -/
@[reassoc]
theorem projectiveLineChartMap_one_overlap :
    specMap (CommAlgCat.ofHom (LaurentPolynomial.invert.toAlgHom.comp
      (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k))) ≫
        projectiveLineChartMap k 1 = projectiveLineOverlapMap k := by
  rw [← projectiveLineChartRingRestriction_one]
  exact restriction_chartMap k 1

end OrlikSolomon.Geometric.Examples
