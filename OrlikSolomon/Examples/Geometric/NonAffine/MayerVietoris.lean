/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import OrlikSolomon.Examples.Geometric.NonAffine.SheafCech

/-!
# The conditional Mayer–Vietoris computation for the projective line

`ProjectiveLineMayerVietorisData` takes a nonnegative graded family and a two-open long
exact sequence with the actual de Rham homology of the standard affine charts and overlap.
The difference map is induced by the actual sheaf restrictions. Over a characteristic-zero
field, the affine computations identify these terms with `k × k` in degree zero on the charts,
and `k` in degrees zero and one on the overlap. Restriction preserves constant classes, so
the degree-zero difference becomes `(a, b) ↦ b - a`.

`normalized` transports the actual sequence to `NormalizedProjectiveLineMayerVietorisData`.
The elementary exactness argument then gives `k` in degrees zero and two and zero otherwise.
The degree-two generator is the boundary of the actual overlap logarithmic class. Neither
chart computations nor a non-affine cohomology conclusion are inputs to the public data.

Blueprint: the universal conditional assertion in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace OrlikSolomon.Geometric.Examples

section Normalized

variable (k : Type u) [CommRing k]

/-- The normalized affine-chart groups: `k × k` in degree zero and zero otherwise. -/
-- Instance search must see the concrete product carrier in mixed-coordinate formulas.
@[instance_reducible]
def projectiveLineMVCharts : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k (k × k)
  | _ + 1 => ModuleCat.of k PUnit.{u + 1}

/-- The normalized Laurent-overlap groups: `k` in degrees zero and one and zero otherwise. -/
-- Keep the scalar and zero carriers visible to the same instance-search convention.
@[instance_reducible]
def projectiveLineMVOverlap : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k k
  | 1 => ModuleCat.of k k
  | _ + 2 => ModuleCat.of k PUnit.{u + 1}

/-- The normalized chart groups vanish in positive degrees. -/
instance projectiveLineMVCharts_subsingleton (n : ℕ) :
    Subsingleton (projectiveLineMVCharts k (n + 1)) := by
  change Subsingleton PUnit
  infer_instance

/-- The normalized overlap groups vanish above degree one. -/
instance projectiveLineMVOverlap_subsingleton (n : ℕ) :
    Subsingleton (projectiveLineMVOverlap k (n + 2)) := by
  change Subsingleton PUnit
  infer_instance

/-- The normalized difference of chart restrictions: `(a, b) ↦ b - a` in degree zero. -/
def projectiveLineMVDifference :
    (n : ℕ) → projectiveLineMVCharts k n →ₗ[k] projectiveLineMVOverlap k n
  | 0 => LinearMap.snd k k k - LinearMap.fst k k k
  | _ + 1 => 0

/-- In degree zero the normalized difference is second minus first. -/
@[simp]
lemma projectiveLineMVDifference_zero_apply (a b : k) :
    projectiveLineMVDifference k 0 (a, b) = b - a := rfl

/-- The normalized difference vanishes in positive degrees. -/
@[simp]
lemma projectiveLineMVDifference_succ (n : ℕ) :
    projectiveLineMVDifference k (n + 1) = 0 := rfl

/-- The normalized nonnegative Mayer–Vietoris long exact sequence for the projective-line cover.
The affine chart and overlap computations fix the intermediate groups and their difference map;
the fields record restriction, connecting maps, and exactness.

Blueprint: the conditional Mayer–Vietoris conclusion of `prop:geo-nonaffine`. -/
structure NormalizedProjectiveLineMayerVietorisData (H : ℕ → ModuleCat.{u} k) where
  /-- Restriction to the normalized pair of affine-chart cohomology groups. -/
  restrict (n : ℕ) : H n →ₗ[k] projectiveLineMVCharts k n
  /-- The connecting map from overlap degree `n` to global degree `n + 1`. -/
  boundary (n : ℕ) : projectiveLineMVOverlap k n →ₗ[k] H (n + 1)
  /-- The first restriction is injective because overlap degree `-1` vanishes. -/
  restrict_zero_injective : Function.Injective (restrict 0)
  /-- Exactness at the sum of the two chart groups. -/
  exact_restrict_difference (n : ℕ) : Function.Exact (restrict n) (projectiveLineMVDifference k n)
  /-- Exactness at the overlap group. -/
  exact_difference_boundary (n : ℕ) : Function.Exact (projectiveLineMVDifference k n) (boundary n)
  /-- Exactness at global degree `n + 1`. -/
  exact_boundary_restrict (n : ℕ) : Function.Exact (boundary n) (restrict (n + 1))

namespace NormalizedProjectiveLineMayerVietorisData

variable {k} {H : ℕ → ModuleCat.{u} k} (M : NormalizedProjectiveLineMayerVietorisData k H)

/-- The two chart coefficients of a global degree-zero class agree. -/
lemma restrict_zero_diag (x : H 0) : (M.restrict 0 x).2 = (M.restrict 0 x).1 := by
  have h := (M.exact_restrict_difference 0).apply_apply_eq_zero x
  exact sub_eq_zero.mp h

/-- The first chart coefficient of a global degree-zero class. -/
def zeroCoefficient : H 0 →ₗ[k] k := (LinearMap.fst k k k).comp (M.restrict 0)

/-- Every diagonal constant comes from a unique global degree-zero class. -/
private lemma zeroCoefficient_bijective : Function.Bijective M.zeroCoefficient := by
  constructor
  · intro x y h
    apply M.restrict_zero_injective
    apply Prod.ext h
    exact (M.restrict_zero_diag x).trans (h.trans (M.restrict_zero_diag y).symm)
  · intro c
    obtain ⟨x, hx⟩ := ((M.exact_restrict_difference 0) (c, c)).mp (sub_self c)
    exact ⟨x, congrArg Prod.fst hx⟩

/-- Every normalized Mayer–Vietoris sequence has degree-zero group `k`. -/
def homologyZeroEquiv : H 0 ≃ₗ[k] k :=
  LinearEquiv.ofBijective M.zeroCoefficient (by exact M.zeroCoefficient_bijective)

/-- The degree-zero equivalence reads the first chart coefficient. -/
@[simp]
lemma homologyZeroEquiv_apply (x : H 0) : M.homologyZeroEquiv x = (M.restrict 0 x).1 := rfl

/-- A scalar corresponds to a global class restricting to that scalar on both charts. -/
@[simp]
lemma restrict_homologyZeroEquiv_symm (c : k) :
    M.restrict 0 (M.homologyZeroEquiv.symm c) = (c, c) := by
  have h := M.homologyZeroEquiv.apply_symm_apply c
  apply Prod.ext h
  exact (M.restrict_zero_diag _).trans h

/-- The connecting map out of overlap degree zero vanishes, since `b - a` is surjective. -/
lemma boundary_zero (c : k) : M.boundary 0 c = 0 := by
  have h := (M.exact_difference_boundary 0).apply_apply_eq_zero (0, c)
  change M.boundary 0 (c - (0 : k)) = 0 at h
  simpa only [sub_zero] using h

include M in
/-- The degree-one global group vanishes in every normalized Mayer–Vietoris sequence. -/
lemma homologyOne_subsingleton : Subsingleton (H 1) := by
  have hz (x : H 1) : x = 0 := by
    obtain ⟨c, hc⟩ := ((M.exact_boundary_restrict 0) x).mp (Subsingleton.elim _ _)
    exact hc.symm.trans (M.boundary_zero c)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The boundary identifies overlap degree one with global degree two. -/
private lemma boundary_one_bijective : Function.Bijective (M.boundary 1) := by
  constructor
  · exact (LinearMap.injective_iff_eq_zero_of_exact (M.exact_difference_boundary 1)).mpr rfl
  · intro x
    exact ((M.exact_boundary_restrict 1) x).mp (Subsingleton.elim _ _)

/-- Every normalized Mayer–Vietoris sequence has degree-two group `k`, via the boundary. -/
def homologyTwoEquiv : H 2 ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (M.boundary 1) (by exact M.boundary_one_bijective)).symm

/-- The degree-two equivalence returns the coefficient of a boundary class. -/
@[simp]
lemma homologyTwoEquiv_boundary (c : k) : M.homologyTwoEquiv (M.boundary 1 c) = c :=
  (LinearEquiv.ofBijective (M.boundary 1) (by exact M.boundary_one_bijective)).symm_apply_apply c

/-- The inverse degree-two equivalence is the connecting map from overlap degree one. -/
@[simp]
lemma homologyTwoEquiv_symm_apply (c : k) : M.homologyTwoEquiv.symm c = M.boundary 1 c := rfl

include M in
/-- The global groups above degree two vanish in every normalized Mayer–Vietoris sequence. -/
lemma homologyHigh_subsingleton (n : ℕ) : Subsingleton (H (n + 3)) := by
  have hz (x : H (n + 3)) : x = 0 := by
    obtain ⟨c, hc⟩ := ((M.exact_boundary_restrict (n + 2)) x).mp (Subsingleton.elim _ _)
    have hc0 : c = 0 := Subsingleton.elim _ _
    rw [hc0, map_zero] at hc
    exact hc.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The degree-two boundary of the chosen overlap generator `[dT/T]`. -/
def boundaryGenerator : H 2 := M.boundary 1 (1 : k)

/-- The boundary of the overlap generator has coefficient one. -/
@[simp]
lemma homologyTwoEquiv_boundaryGenerator : M.homologyTwoEquiv M.boundaryGenerator = 1 :=
  M.homologyTwoEquiv_boundary 1

/-- The boundary generator is nonzero when the coefficient ring is nontrivial. -/
lemma boundaryGenerator_ne_zero [Nontrivial k] : M.boundaryGenerator ≠ 0 := by
  intro h
  have hh := M.homologyTwoEquiv_boundaryGenerator
  rw [h, map_zero] at hh
  exact zero_ne_one hh

end NormalizedProjectiveLineMayerVietorisData

end Normalized

open OrlikSolomon.DeRham
open scoped Polynomial LaurentPolynomial

variable (k : Type u) [Field k] [CharZero k]

private def constantDegreeZero (A : Type u) [CommRing A] [Algebra k A] :
    k →ₗ[k] Cohomology.degree k A 0 :=
  (Algebra.linearMap k (Cohomology k A)).codRestrict _ fun c =>
    by
      change algebraMap k (Cohomology k A) c ∈ _
      simpa only [Algebra.smul_def, mul_one] using
        (Cohomology.degree k A 0).smul_mem c (SetLike.one_mem_graded _)

private def polynomialDegreeZeroEquiv : k ≃ₗ[k] Cohomology.degree k k[X] 0 :=
  LinearEquiv.ofBijective (constantDegreeZero k k[X]) (by
    let e := (OrlikSolomon.DeRham.Examples.pointCohomologyEquiv k).trans
      (polynomialCohomologyEquiv k k (OrlikSolomon.DeRham.isUnit_natCast_add_one k))
    have he (c : k) : (constantDegreeZero k k[X] c).val = e c := (e.commutes c).symm
    constructor
    · intro a b h
      exact e.injective ((he a).symm.trans ((congrArg Subtype.val h).trans (he b)))
    · intro x
      obtain ⟨c, hc⟩ := e.surjective x.val
      exact ⟨c, Subtype.ext ((he c).trans hc)⟩)

private def laurentDegreeZeroEquiv : k ≃ₗ[k] Cohomology.degree k (LaurentPolynomial k) 0 :=
  LinearEquiv.ofBijective (constantDegreeZero k (LaurentPolynomial k)) (by
    have he (c : k) : (constantDegreeZero k (LaurentPolynomial k) c).val =
        OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k (c, 0) := by
      simp only [OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_apply,
        map_zero, mul_zero, add_zero]
      rfl
    constructor
    · intro a b h
      exact congrArg Prod.fst ((OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).injective
        ((he a).symm.trans ((congrArg Subtype.val h).trans (he b))))
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ :=
        (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).surjective x.val
      have hb := (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_degree_zero_iff k a b).1
        (hab.symm ▸ x.property)
      subst b
      exact ⟨a, Subtype.ext ((he a).trans hab)⟩)

omit [CharZero k] in
private lemma homologyIso_map_val {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (n : ℕ)
    (x : (complex k A).homology n) :
    ((homologyIso k B n).hom (HomologicalComplex.homologyMap (complexMap φ) n x)).val =
      Cohomology.map φ ((homologyIso k A n).hom x).val := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex k A).homologyπ n)).1
    inferInstance x
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (complexMap φ) n) z
  simp only [ModuleCat.comp_apply] at h
  rw [h, coe_homologyIso_hom_homologyπ, coe_homologyIso_hom_homologyπ,
    Cohomology.map_mk]
  apply Cohomology.mk_congr
  have hc := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (complexMap φ) n) z
  exact congrArg Subtype.val hc

private def constantHomology (A : Type u) [CommRing A] [Algebra k A] :
    k →ₗ[k] (complex k A).homology 0 :=
  (homologyIso k A 0).inv.hom.comp (constantDegreeZero k A)

omit [CharZero k] in
private lemma constantHomology_map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (c : k) :
    HomologicalComplex.homologyMap (complexMap φ) 0 (constantHomology k A c) =
      constantHomology k B c := by
  apply (homologyIso k B 0).toLinearEquiv.injective
  apply Subtype.ext
  change ((homologyIso k B 0).hom
    (HomologicalComplex.homologyMap (complexMap φ) 0 (constantHomology k A c))).val =
      ((homologyIso k B 0).hom (constantHomology k B c)).val
  rw [homologyIso_map_val]
  change Cohomology.map φ
      ((homologyIso k A 0).hom ((homologyIso k A 0).inv (constantDegreeZero k A c))).val =
    ((homologyIso k B 0).hom ((homologyIso k B 0).inv (constantDegreeZero k B c))).val
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  exact (Cohomology.map φ).commutes c


/-- The actual cohomology of a chart in degree zero is generated by the constant unit. -/
@[no_expose] def projectiveLineChartHomologyZeroEquiv (i : Fin 2) :
    k ≃ₗ[k] (projectiveLineFormsOn k (projectiveLineChart k i)).homology 0 :=
  (polynomialDegreeZeroEquiv k).trans ((homologyIso k k[X] 0).symm.toLinearEquiv.trans
    (HomologicalComplex.homologyMapIso (projectiveLineChartFormsComplexIso k i) 0).toLinearEquiv)

/-- The actual overlap has constant cohomology in degree zero. -/
@[no_expose] def projectiveLineOverlapHomologyZeroEquiv :
    k ≃ₗ[k] (projectiveLineFormsOn k (projectiveLineOverlap k)).homology 0 :=
  (laurentDegreeZeroEquiv k).trans ((homologyIso k (LaurentPolynomial k) 0).symm.toLinearEquiv.trans
    (HomologicalComplex.homologyMapIso (projectiveLineOverlapFormsComplexIso k) 0).toLinearEquiv)

/-- Actual restriction from either standard chart sends the constant class to that same class. -/
lemma projectiveLineHomologyRestriction_constant (i : Fin 2) (c : k) :
    HomologicalComplex.homologyMap (projectiveLineFormsRestriction k i) 0
        (projectiveLineChartHomologyZeroEquiv k i c) =
      projectiveLineOverlapHomologyZeroEquiv k c := by
  have h0 : HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 0) 0
        (projectiveLineChartHomologyZeroEquiv k 0 c) =
      projectiveLineOverlapHomologyZeroEquiv k c := by
    change (HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 0) 0)
      ((HomologicalComplex.homologyMap (projectiveLineChartFormsComplexIso k 0).hom 0)
        (constantHomology k k[X] c)) =
      (HomologicalComplex.homologyMap (projectiveLineOverlapFormsComplexIso k).hom 0)
        (constantHomology k (LaurentPolynomial k) c)
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      projectiveLineChartFormsComplexIso_restrict_zero, HomologicalComplex.homologyMap_comp,
      ModuleCat.comp_apply, constantHomology_map]
  have h1 : HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 1) 0
        (projectiveLineChartHomologyZeroEquiv k 1 c) =
      projectiveLineOverlapHomologyZeroEquiv k c := by
    change (HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 1) 0)
      ((HomologicalComplex.homologyMap (projectiveLineChartFormsComplexIso k 1).hom 0)
        (constantHomology k k[X] c)) =
      (HomologicalComplex.homologyMap (projectiveLineOverlapFormsComplexIso k).hom 0)
        (constantHomology k (LaurentPolynomial k) c)
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      projectiveLineChartFormsComplexIso_restrict_one, HomologicalComplex.homologyMap_comp,
      ModuleCat.comp_apply, constantHomology_map]
  fin_cases i
  · exact h0
  · exact h1

/-- The overlap's actual first homology is generated by the logarithmic class. -/
def projectiveLineOverlapHomologyOneEquiv :
    k ≃ₗ[k] (projectiveLineFormsOn k (projectiveLineOverlap k)).homology 1 :=
  (overlapDegreeOneEquiv k).trans ((homologyIso k (LaurentPolynomial k) 1).symm.toLinearEquiv.trans
    (HomologicalComplex.homologyMapIso (projectiveLineOverlapFormsComplexIso k) 1).toLinearEquiv)

private lemma chartHomology_subsingleton (i : Fin 2) (n : ℕ) :
    Subsingleton ((projectiveLineFormsOn k (projectiveLineChart k i)).homology (n + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1 (Limits.IsZero.of_iso
    (polynomialComplex_isZero_homology_succ k n)
    (HomologicalComplex.homologyMapIso (projectiveLineChartFormsComplexIso k i) (n + 1)).symm)

private lemma overlapHomology_subsingleton (n : ℕ) :
    Subsingleton ((projectiveLineFormsOn k (projectiveLineOverlap k)).homology (n + 2)) :=
  ModuleCat.isZero_iff_subsingleton.1 (Limits.IsZero.of_iso
    (overlapComplex_isZero_homology_succ_succ k n)
    (HomologicalComplex.homologyMapIso (projectiveLineOverlapFormsComplexIso k) (n + 2)).symm)


/-- The actual homology groups on the two standard affine charts. -/
@[instance_reducible] def projectiveLineMVChartHomology (n : ℕ) : ModuleCat.{u} k :=
  ModuleCat.of k ((projectiveLineFormsOn k (projectiveLineChart k 0)).homology n ×
    (projectiveLineFormsOn k (projectiveLineChart k 1)).homology n)

/-- The difference of the maps induced by the actual sheaf restrictions to the intersection. -/
def projectiveLineMVHomologyDifference (n : ℕ) :
    projectiveLineMVChartHomology k n →ₗ[k]
      (projectiveLineFormsOn k (projectiveLineOverlap k)).homology n :=
  (HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 1) n).hom.comp
      (LinearMap.snd k _ _) -
    (HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 0) n).hom.comp
      (LinearMap.fst k _ _)

/-- The affine computations identify the normalized chart groups with the actual groups. -/
@[no_expose] def projectiveLineMVChartsEquiv :
    (n : ℕ) → projectiveLineMVCharts k n ≃ₗ[k] projectiveLineMVChartHomology k n
  | 0 => LinearEquiv.prodCongr (projectiveLineChartHomologyZeroEquiv k 0)
      (projectiveLineChartHomologyZeroEquiv k 1)
  | n + 1 => by
      letI := chartHomology_subsingleton k 0 n
      letI := chartHomology_subsingleton k 1 n
      change projectiveLineMVCharts k (n + 1) ≃ₗ[k]
        ((projectiveLineFormsOn k (projectiveLineChart k 0)).homology (n + 1) ×
          (projectiveLineFormsOn k (projectiveLineChart k 1)).homology (n + 1))
      exact LinearEquiv.ofSubsingleton _ _

/-- The affine Laurent computation identifies normalized and actual overlap groups. -/
@[no_expose] def projectiveLineMVOverlapEquiv :
    (n : ℕ) → projectiveLineMVOverlap k n ≃ₗ[k]
      (projectiveLineFormsOn k (projectiveLineOverlap k)).homology n
  | 0 => projectiveLineOverlapHomologyZeroEquiv k
  | 1 => projectiveLineOverlapHomologyOneEquiv k
  | n + 2 => by
      letI := overlapHomology_subsingleton k n
      exact LinearEquiv.ofSubsingleton _ _

/-- After the affine computations, the actual restriction difference is `b - a` in degree
zero and zero above. The chart-to-overlap identifications are proved, not assumed. -/
lemma projectiveLineMVHomologyDifference_equiv (n : ℕ) (x : projectiveLineMVCharts k n) :
    projectiveLineMVHomologyDifference k n (projectiveLineMVChartsEquiv k n x) =
      projectiveLineMVOverlapEquiv k n (projectiveLineMVDifference k n x) := by
  cases n with
  | zero =>
    change HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 1) 0
        (projectiveLineChartHomologyZeroEquiv k 1 x.2) -
      HomologicalComplex.homologyMap (projectiveLineFormsRestriction k 0) 0
        (projectiveLineChartHomologyZeroEquiv k 0 x.1) =
      projectiveLineOverlapHomologyZeroEquiv k (x.2 - x.1)
    rw [projectiveLineHomologyRestriction_constant, projectiveLineHomologyRestriction_constant,
      map_sub]
  | succ n =>
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, map_zero, map_zero, map_zero, map_zero]

/-- A two-open Mayer–Vietoris sequence whose intermediate terms and restriction difference
are the actual affine de Rham homology of the standard projective-line cover.
Only restriction, connecting maps and exactness are inputs; none of the chart or overlap
cohomology calculations is a field.

Blueprint: the conditional assertion in `prop:geo-nonaffine`. -/
structure ProjectiveLineMayerVietorisData (H : ℕ → ModuleCat.{u} k) where
  /-- Restriction to the actual two affine-chart cohomology groups. -/
  restrict (n : ℕ) : H n →ₗ[k] projectiveLineMVChartHomology k n
  /-- The connecting map from actual overlap homology to the next global group. -/
  boundary (n : ℕ) :
    (projectiveLineFormsOn k (projectiveLineOverlap k)).homology n →ₗ[k] H (n + 1)
  /-- Injectivity at the beginning of the nonnegative sequence. -/
  restrict_zero_injective : Function.Injective (restrict 0)
  /-- Exactness at the actual chart groups. -/
  exact_restrict_difference (n : ℕ) :
    Function.Exact (restrict n) (projectiveLineMVHomologyDifference k n)
  /-- Exactness at actual overlap homology. -/
  exact_difference_boundary (n : ℕ) :
    Function.Exact (projectiveLineMVHomologyDifference k n) (boundary n)
  /-- Exactness at the next global group. -/
  exact_boundary_restrict (n : ℕ) : Function.Exact (boundary n) (restrict (n + 1))

namespace ProjectiveLineMayerVietorisData

variable {k} {H : ℕ → ModuleCat.{u} k} (M : ProjectiveLineMayerVietorisData k H)

/-- The actual affine computations transport the given exact sequence to its scalar model. -/
@[no_expose] def normalized : NormalizedProjectiveLineMayerVietorisData k H where
  restrict n := (projectiveLineMVChartsEquiv k n).symm.toLinearMap.comp (M.restrict n)
  boundary n := (M.boundary n).comp (projectiveLineMVOverlapEquiv k n).toLinearMap
  restrict_zero_injective := (projectiveLineMVChartsEquiv k 0).symm.injective.comp
    M.restrict_zero_injective
  exact_restrict_difference n := by
    intro x
    constructor
    · intro hx
      have hactual : projectiveLineMVHomologyDifference k n (projectiveLineMVChartsEquiv k n x) =
          0 := by rw [projectiveLineMVHomologyDifference_equiv, hx, map_zero]
      obtain ⟨y, hy⟩ := (M.exact_restrict_difference n _).1 hactual
      exact ⟨y, by
        change (projectiveLineMVChartsEquiv k n).symm (M.restrict n y) = x
        rw [hy, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨y, hy⟩
      apply (projectiveLineMVOverlapEquiv k n).injective
      rw [map_zero, ← projectiveLineMVHomologyDifference_equiv]
      have hxy : M.restrict n y = projectiveLineMVChartsEquiv k n x :=
        (projectiveLineMVChartsEquiv k n).symm_apply_eq.1 hy
      rw [← hxy]
      exact (M.exact_restrict_difference n).apply_apply_eq_zero y
  exact_difference_boundary n := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (M.exact_difference_boundary n _).1 hx
      refine ⟨(projectiveLineMVChartsEquiv k n).symm y, ?_⟩
      apply (projectiveLineMVOverlapEquiv k n).injective
      rw [← projectiveLineMVHomologyDifference_equiv, LinearEquiv.apply_symm_apply, hy]
      rfl
    · rintro ⟨y, hy⟩
      change M.boundary n (projectiveLineMVOverlapEquiv k n x) = 0
      rw [← hy, ← projectiveLineMVHomologyDifference_equiv]
      exact (M.exact_difference_boundary n).apply_apply_eq_zero _
  exact_boundary_restrict n := by
    intro x
    constructor
    · intro hx
      have hx' : M.restrict (n + 1) x = 0 :=
        (projectiveLineMVChartsEquiv k (n + 1)).symm.map_eq_zero_iff.1 hx
      obtain ⟨y, hy⟩ := (M.exact_boundary_restrict n x).1 hx'
      exact ⟨(projectiveLineMVOverlapEquiv k n).symm y, by
        change M.boundary n ((projectiveLineMVOverlapEquiv k n)
          ((projectiveLineMVOverlapEquiv k n).symm y)) = x
        rw [LinearEquiv.apply_symm_apply, hy]⟩
    · rintro ⟨y, hy⟩
      change (projectiveLineMVChartsEquiv k (n + 1)).symm (M.restrict (n + 1) x) = 0
      rw [← hy]
      change (projectiveLineMVChartsEquiv k (n + 1)).symm
        (M.restrict (n + 1) (M.boundary n (projectiveLineMVOverlapEquiv k n y))) = 0
      rw [(M.exact_boundary_restrict n).apply_apply_eq_zero, map_zero]

/-- Any extension agreeing with the affine de Rham theory and the two-open sequence has `H⁰ = k`. -/
def homologyZeroEquiv : H 0 ≃ₗ[k] k := M.normalized.homologyZeroEquiv

include M in
/-- The first group of every such extension vanishes. -/
lemma homologyOne_subsingleton : Subsingleton (H 1) := M.normalized.homologyOne_subsingleton

/-- Any such extension has `H² = k`, induced by the boundary of the actual overlap's `H¹`. -/
def homologyTwoEquiv : H 2 ≃ₗ[k] k := M.normalized.homologyTwoEquiv

include M in
/-- All groups above degree two of every such extension vanish. -/
lemma homologyHigh_subsingleton (n : ℕ) : Subsingleton (H (n + 3)) :=
  M.normalized.homologyHigh_subsingleton n

/-- The class obtained by applying the given boundary to the actual overlap logarithmic class. -/
def boundaryGenerator : H 2 := M.boundary 1 (projectiveLineOverlapHomologyOneEquiv k 1)

/-- The actual overlap logarithmic class gives the coefficient-one generator in degree two. -/
@[simp] lemma homologyTwoEquiv_boundaryGenerator : M.homologyTwoEquiv M.boundaryGenerator = 1 :=
  M.normalized.homologyTwoEquiv_boundaryGenerator

end ProjectiveLineMayerVietorisData

end OrlikSolomon.Geometric.Examples
