/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Geometry

/-!
# The standard affine charts of the projective line

The two standard charts are complements of one coordinate hyperplane. Their coordinate rings
are identified with `k[X]` by substituting `(1, X)` or `(X, 1)` into homogeneous coordinates.
All maps use the existing projective-complement localization and its spectrum comparison.

Blueprint: the chart computations in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module Polynomial

namespace OrlikSolomon.Geometric.Examples

open ProjectiveArrangement ProjectiveArrangement.ComplementRing CoordinateRing

universe u
variable (k : Type u) [Field k]

/-- The `i`th homogeneous coordinate on the two-dimensional vector space. -/
def projectiveLineCoordinate (i : Fin 2) : Dual k (Fin 2 → k) := LinearMap.proj i
@[simp] lemma projectiveLineCoordinate_apply (i :
    Fin 2) (v : Fin 2 → k) : projectiveLineCoordinate k i v = v i := rfl

/-- A homogeneous coordinate is a nonzero linear form. -/
lemma projectiveLineCoordinate_ne_zero (i : Fin 2) : projectiveLineCoordinate k i ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h (Pi.single i 1)
  simp [projectiveLineCoordinate] at h'

/-- The single point omitted by the `i`th standard chart. -/
def projectiveLineChartArrangement (i : Fin 2) : ProjectiveArrangement k (Fin 2 → k) :=
  ofForms {projectiveLineCoordinate k i} (by simpa using projectiveLineCoordinate_ne_zero k i)

/-- The coordinate hyperplane is the unique member of the chart arrangement. -/
lemma projectiveLineCoordinate_ker_mem (i : Fin 2) :
     LinearMap.ker (projectiveLineCoordinate k i) ∈ projectiveLineChartArrangement k i :=
  ker_mem_ofForms (Finset.mem_singleton_self _)

/-- Every standard chart omits one coordinate point. -/
instance projectiveLineChartArrangement_nonempty (i : Fin 2) :
    Nonempty (projectiveLineChartArrangement k i) :=
  nonempty_of_ker_mem (projectiveLineCoordinate_ker_mem k i)

private def subLinear (i : Fin 2) : Dual k (Fin 2 → k) →ₗ[k] k[X] where
  toFun l := C (l (Pi.single i 1)) + C (l (Pi.single i.rev 1)) * X
  map_add' l m := by simp [add_mul, add_add_add_comm]
  map_smul' a l := by simp [Algebra.smul_def, mul_add, mul_assoc]

private def subst (i : Fin 2) : CoordinateRing k (Fin 2 → k) →ₐ[k] k[X] :=
  SymmetricAlgebra.lift (subLinear k i)

private lemma subst_coord (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    subst k i (coord l.toAffineMap) =
      C (l (Pi.single i 1)) + C (l (Pi.single i.rev 1)) * X := by
  rw [coord_toAffineMap, subst, SymmetricAlgebra.lift_ι_apply]
  rfl

private lemma subst_self (i : Fin 2) :
     subst k i (coord (projectiveLineCoordinate k i).toAffineMap) = 1 := by
  rw [subst_coord]
  fin_cases i <;> simp [projectiveLineCoordinate]

private lemma subst_other (i : Fin 2) :
     subst k i (coord (projectiveLineCoordinate k i.rev).toAffineMap) = X := by
  rw [subst_coord]
  fin_cases i <;> simp [projectiveLineCoordinate]

private def coneEval (i : Fin 2) :
     (projectiveLineChartArrangement k i).cone.ComplementRing →ₐ[k] k[X] :=
  Arrangement.ComplementRing.lift _ (subst k i) fun K hK ↦ by
    obtain ⟨M, hM, rfl⟩ := mem_cone.mp hK
    obtain ⟨l, hl, rfl⟩ := mem_ofForms.mp hM
    have hl' : l = projectiveLineCoordinate k i := Finset.mem_singleton.mp hl
    subst hl'
    exact ⟨(projectiveLineCoordinate k i).toAffineMap,
      isEquation_toAffineMap (projectiveLineCoordinate_ne_zero k i), by
      rw [subst_self]; exact isUnit_one⟩

private lemma coneEval_coord (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    coneEval k i (algebraMap _ _ (coord l.toAffineMap)) =
      C (l (Pi.single i 1)) + C (l (Pi.single i.rev 1)) * X := by
  rw [coneEval, Arrangement.ComplementRing.lift_algebraMap, subst_coord]

private def chartEval (i : Fin 2) :
     (projectiveLineChartArrangement k i).ComplementRing →ₐ[k] k[X] :=
  (coneEval k i).comp (toCone _)

private lemma chartEval_ratio (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    chartEval k i (ratio l (projectiveLineCoordinate_ker_mem k i)) =
      C (l (Pi.single i 1)) + C (l (Pi.single i.rev 1)) * X := by
  have h := congrArg (coneEval k i) (toCone_ratio_mul l (projectiveLineCoordinate_ker_mem k i))
  rw [map_mul, coneEval, Arrangement.ComplementRing.lift_algebraMap,
    subst_self, mul_one, Arrangement.ComplementRing.lift_algebraMap, subst_coord] at h
  exact h

private lemma linear_decomp (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    l = l (Pi.single i 1) • projectiveLineCoordinate k i +
      l (Pi.single i.rev 1) • projectiveLineCoordinate k i.rev := by
  have hv (v : Fin 2 → k) :
      v = v i • Pi.single i 1 + v i.rev • Pi.single i.rev 1 := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp
  apply LinearMap.ext
  intro v
  conv_lhs => rw [hv v, map_add, map_smul, map_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, projectiveLineCoordinate_apply, smul_eq_mul]
  ring

private def chartInverse (i : Fin 2) :
     k[X] →ₐ[k] (projectiveLineChartArrangement k i).ComplementRing :=
  aeval (ratio (projectiveLineCoordinate k i.rev) (projectiveLineCoordinate_ker_mem k i))

private lemma fixed_ratio (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    chartInverse k i (chartEval k i (ratio l (projectiveLineCoordinate_ker_mem k i))) =
      ratio l (projectiveLineCoordinate_ker_mem k i) := by
  rw [chartEval_ratio]
  conv_rhs => rw [linear_decomp k i l, ratio_add, ratio_smul, ratio_smul, ratio_self]
  simp [chartInverse, Algebra.smul_def]

/-- The coordinate ring of the `i`th standard chart is `k[X]`, with `X` the ratio
of the other homogeneous coordinate to the `i`th coordinate. -/
@[no_expose] def projectiveLineChartRingEquiv (i : Fin 2) :
     (projectiveLineChartArrangement k i).ComplementRing ≃ₐ[k] k[X] :=
  AlgEquiv.ofAlgHom (chartEval k i) (chartInverse k i) (by
    ext
    rw [AlgHom.comp_apply, chartInverse, aeval_X, chartEval_ratio]
    fin_cases i <;> simp [projectiveLineCoordinate]) (by
    apply ProjectiveArrangement.ComplementRing.algHom_ext
    intro l m hm
    apply (ratioUnit hm (projectiveLineCoordinate_ker_mem k i)).isUnit.mul_right_cancel
    change chartInverse k i (chartEval k i (ratio l hm)) *
      ratio m (projectiveLineCoordinate_ker_mem k i) =
      ratio l hm * ratio m (projectiveLineCoordinate_ker_mem k i)
    calc
      _ = chartInverse k i (chartEval k i (ratio l hm)) *
          chartInverse k i (chartEval k i (ratio m (projectiveLineCoordinate_ker_mem k i))) := by
        rw [fixed_ratio]
      _ = chartInverse k i (chartEval k i (ratio l (projectiveLineCoordinate_ker_mem k i))) := by
        rw [← map_mul, ← map_mul, ratio_mul_ratio]
      _ = _ := by rw [fixed_ratio, ratio_mul_ratio])

/-- The chart-ring comparison sends a homogeneous-coordinate ratio to its usual polynomial. -/
theorem projectiveLineChartRingEquiv_ratio (i : Fin 2) (l : Dual k (Fin 2 → k)) :
    projectiveLineChartRingEquiv k i (ratio l (projectiveLineCoordinate_ker_mem k i)) =
      C (l (Pi.single i 1)) + C (l (Pi.single i.rev 1)) * X :=
  chartEval_ratio k i l

/-- The inverse chart-ring comparison sends `X` to the ratio of the two coordinates. -/
@[simp]
theorem projectiveLineChartRingEquiv_symm_X (i : Fin 2) :
    (projectiveLineChartRingEquiv k i).symm X =
      ratio (projectiveLineCoordinate k i.rev) (projectiveLineCoordinate_ker_mem k i) :=
  aeval_X _

/-- The `i`th standard open subset of the actual projective line. -/
@[instance_reducible]
def projectiveLineChart (i : Fin 2) : (projectiveLine k).left.Opens :=
  complementOpen (projectiveLineChartArrangement k i)

/-- The standard chart is the basic open of the corresponding homogeneous coordinate. -/
theorem projectiveLineChart_eq_basicOpen (i : Fin 2) :
    projectiveLineChart k i = Proj.basicOpen (symmetricGrading k (Dual k (Fin 2 → k)))
      (coord (projectiveLineCoordinate k i).toAffineMap) :=
  complementOpen_ofForms_singleton (projectiveLineCoordinate_ne_zero k i)

/-- Each standard chart is an affine open subset. -/
theorem isAffineOpen_projectiveLineChart (i : Fin 2) :
    IsAffineOpen (projectiveLineChart k i) := by
  rw [projectiveLineChart_eq_basicOpen]
  exact Proj.isAffineOpen_basicOpen _ _ (coord_toAffineMap_mem _) (by decide : 0 < 1)

/-- A standard chart, with its actual open-immersion structure map to `Spec k`. -/
@[instance_reducible]
def projectiveLineChartOver (i : Fin 2) : Over (Spec (.of k)) :=
  projectiveComplement (projectiveLineChartArrangement k i)

/-- The standard chart is the affine line as a scheme over `Spec k`. -/
def projectiveLineChartIso (i : Fin 2) :
    projectiveLineChartOver k i ≅ spec (CommAlgCat.of k k[X]) :=
  projectiveComplementIsoSpec (projectiveLineChartArrangement k i) ≪≫
    ((specFunctor k).mapIso (CommAlgCat.isoMk (projectiveLineChartRingEquiv k i)).op).symm

/-- The chart map from the actual spectrum of `k[X]` to the projective line. -/
def projectiveLineChartMap (i : Fin 2) :
    spec (CommAlgCat.of k k[X]) ⟶ projectiveLine k :=
  (projectiveLineChartIso k i).inv ≫ projectiveComplementι (projectiveLineChartArrangement k i)

/-- On underlying schemes, the chart is the complement chart followed by its
coordinate isomorphism. -/
theorem projectiveLineChartMap_left (i : Fin 2) :
    (projectiveLineChartMap k i).left =
      Spec.map (CommRingCat.ofHom (projectiveLineChartRingEquiv k i).toRingHom) ≫
        ProjectiveArrangement.complementι (projectiveLineChartArrangement k i) := rfl

/-- The standard affine-line chart maps are open immersions. -/
instance projectiveLineChartMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (projectiveLineChartMap k i).left := by
  change IsOpenImmersion ((projectiveLineChartIso k i).inv.left ≫
    (projectiveComplementι (projectiveLineChartArrangement k i)).left)
  infer_instance

/-- The image of the chart map is the specified standard open subset. -/
theorem projectiveLineChartMap_opensRange (i : Fin 2) :
    (projectiveLineChartMap k i).left.opensRange = projectiveLineChart k i := by
  change ((projectiveLineChartIso k i).inv.left ≫
    (projectiveComplementι (projectiveLineChartArrangement k i)).left).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (opensRange_projectiveComplementι (projectiveLineChartArrangement k i))

/-- The two standard charts cover the actual projective line. -/
theorem projectiveLineChart_sup : projectiveLineChart k 0 ⊔ projectiveLineChart k 1 = ⊤ := by
  rw [projectiveLineChart_eq_basicOpen, projectiveLineChart_eq_basicOpen]
  apply top_le_iff.mp
  intro x _
  by_contra h
  have h0 : coord (projectiveLineCoordinate k 0).toAffineMap ∈ x.asHomogeneousIdeal := by
    by_contra h0
    exact h (Or.inl h0)
  have h1 : coord (projectiveLineCoordinate k 1).toAffineMap ∈ x.asHomogeneousIdeal := by
    by_contra h1
    exact h (Or.inr h1)
  have hall (l : Dual k (Fin 2 → k)) : coord l.toAffineMap ∈ x.asHomogeneousIdeal := by
    rw [linear_decomp k 0 l, coord_toAffineMap, map_add, map_smul, map_smul]
    simp only [Fin.reduceRev, Algebra.smul_def]
    change _ ∈ x.asHomogeneousIdeal.toIdeal
    exact x.asHomogeneousIdeal.toIdeal.add_mem
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left _ (by
        change SymmetricAlgebra.ι k _ (projectiveLineCoordinate k 0) ∈ x.asHomogeneousIdeal
        simpa only [coord_toAffineMap] using h0))
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left _ (by
        change SymmetricAlgebra.ι k _ (projectiveLineCoordinate k 1) ∈ x.asHomogeneousIdeal
        simpa only [coord_toAffineMap] using h1))
  have hx : x ∈ ⨆ l : {l : Dual k (Fin 2 → k) // l ≠ 0},
      Proj.basicOpen (symmetricGrading k (Dual k (Fin 2 → k))) (coord l.1.toAffineMap) := by
    rw [iSup_basicOpen_coord_eq_top]
    trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact hl (hall l.1)

end OrlikSolomon.Geometric.Examples
