/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Cech
public import OrlikSolomon.Examples.Geometric.NonAffine.MatchingForms

/-!
# Degree-zero Čech cohomology of the projective line

The two-chart Čech–de Rham complex has cohomology `k` in degree zero over an arbitrary
commutative ring. A cocycle is a pair of closed chart functions agreeing on the Laurent overlap.
The matching-functions calculation identifies this pair with a unique diagonal constant.
There are no incoming boundaries in degree zero.

`projectiveLineCechHomologyZeroEquiv` is the resulting linear equivalence. Its inverse is the
class of `projectiveLineCechZeroCycle`, whose formulas on both charts identify the coefficient.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.DeRham
open OrlikSolomon.Geometric.Examples.NonAffine
open scoped Polynomial LaurentPolynomial

universe u

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u) [CommRing k]

/-- Diagonal scalar constants, viewed as degree-zero Čech cocycles in the concrete kernel. -/
def projectiveLineCechZeroConstants : k →ₗ[k]
    LinearMap.ker ((projectiveLineCechComplex k).d 0 1).hom where
  toFun c := ⟨(matchingFormsZeroEquiv k c).val, by
      apply LinearMap.mem_ker.mpr
      change (twoChartFiber (projectiveLineRestrictionDifference k)).d 0 1 _ = 0
      rw [twoChartFiber_d]
      apply Prod.ext
      · change (projectiveLineChartComplex k).d 0 1 _ = 0
        rw [projectiveLineChartComplex_d]
        apply Prod.ext <;> apply Subtype.ext
        · change d k ((matchingFormsZeroEquiv k c).val.1 : Forms k k[X]) = 0
          rw [matchingFormsZeroEquiv_apply, Algebra.algebraMap_eq_smul_one, map_smul,
            d_one, smul_zero]
        · change d k ((matchingFormsZeroEquiv k c).val.2 : Forms k k[X]) = 0
          rw [matchingFormsZeroEquiv_apply_snd, Algebra.algebraMap_eq_smul_one, map_smul,
            d_one, smul_zero]
      · change Forms.mapPower (projectiveLineSecondRestriction k) 0
            (matchingFormsZeroEquiv k c).val.2 -
          Forms.mapPower (projectiveLineFirstRestriction k) 0
            (matchingFormsZeroEquiv k c).val.1 = 0
        exact sub_eq_zero.mpr ((mem_matchingForms _ _).mp
          (matchingFormsZeroEquiv k c).property).symm⟩
  map_add' c d := Subtype.ext (congrArg (fun x : matchingForms k 0 => x.val)
    ((matchingFormsZeroEquiv k).map_add c d))
  map_smul' r c := Subtype.ext (congrArg (fun x : matchingForms k 0 => x.val)
    ((matchingFormsZeroEquiv k).map_smul r c))

private lemma projectiveLineCechZeroConstants_bijective :
    Function.Bijective (projectiveLineCechZeroConstants k) := by
  constructor
  · intro c d h
    apply (matchingFormsZeroEquiv k).injective
    exact Subtype.ext (congrArg
      (fun x : LinearMap.ker ((projectiveLineCechComplex k).d 0 1).hom => x.val) h)
  · intro x
    have hx := x.property
    change (twoChartFiber (projectiveLineRestrictionDifference k)).d 0 1 x.val = 0 at hx
    rw [twoChartFiber_d] at hx
    have hm : x.val ∈ matchingForms k 0 := by
      apply (mem_matchingForms _ _).mpr
      have hh := congrArg Prod.snd hx
      change Forms.mapPower (projectiveLineSecondRestriction k) 0 x.val.2 -
        Forms.mapPower (projectiveLineFirstRestriction k) 0 x.val.1 = 0 at hh
      exact (sub_eq_zero.mp hh).symm
    obtain ⟨c, hc⟩ := (matchingFormsZeroEquiv k).surjective ⟨x.val, hm⟩
    exact ⟨c, Subtype.ext (congrArg (fun x : matchingForms k 0 => x.val) hc)⟩

/-- The concrete kernel of the degree-zero Čech differential is the coefficient ring. -/
def projectiveLineCechZeroKernelEquiv :
    LinearMap.ker ((projectiveLineCechComplex k).d 0 1).hom ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (projectiveLineCechZeroConstants k)
    (by exact projectiveLineCechZeroConstants_bijective k)).symm

/-- The two-chart Čech–de Rham complex of the projective line has degree-zero cohomology `k`.
This holds over every commutative ring, including the zero ring.

Blueprint: `prop:geo-nonaffine`. -/
def projectiveLineCechHomologyZeroEquiv : (projectiveLineCechComplex k).homology 0 ≃ₗ[k] k := by
  let K := projectiveLineCechComplex k
  let S := K.sc' 0 0 1
  have hf : S.f = 0 := by
    change K.d 0 0 = 0
    exact K.shape _ _ (by decide)
  exact ((K.homologyIsoSc' 0 0 1 (by simp) (CochainComplex.next ℕ 0)) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.moduleCatCyclesIso).toLinearEquiv.trans
      (projectiveLineCechZeroKernelEquiv k)

/-- The canonical identification of degree-zero cycles with the concrete kernel of the
differential. -/
def projectiveLineCechZeroCycleKernelIso : (projectiveLineCechComplex k).cycles 0 ≅
    ModuleCat.of k (LinearMap.ker ((projectiveLineCechComplex k).d 0 1).hom) :=
  (projectiveLineCechComplex k).cyclesIsoSc' 0 0 1 (by simp) (CochainComplex.next ℕ 0) ≪≫
    ((projectiveLineCechComplex k).sc' 0 0 1).moduleCatCyclesIso

/-- The degree-zero cycle with the same scalar constant on both affine charts. -/
def projectiveLineCechZeroCycle (c : k) : (projectiveLineCechComplex k).cycles 0 :=
  (projectiveLineCechZeroCycleKernelIso k).inv (projectiveLineCechZeroConstants k c)

/-- The constant cycle has the corresponding diagonal matching forms as its underlying
chart pair. -/
@[simp]
lemma projectiveLineCechZeroCycle_iCycles (c : k) :
    (projectiveLineCechComplex k).iCycles 0 (projectiveLineCechZeroCycle k c) =
      (matchingFormsZeroEquiv k c).val := by
  have h : (projectiveLineCechZeroCycleKernelIso k).inv ≫ (projectiveLineCechComplex k).iCycles 0 =
      ModuleCat.ofHom (LinearMap.ker ((projectiveLineCechComplex k).d 0 1).hom).subtype := by
    simp only [projectiveLineCechZeroCycleKernelIso, Iso.trans_inv, Category.assoc,
      HomologicalComplex.cyclesIsoSc'_inv_iCycles, ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  exact congr($(h) (projectiveLineCechZeroConstants k c))

/-- The class of the diagonal constant cycle has the given scalar as its coefficient. -/
@[simp]
lemma projectiveLineCechHomologyZeroEquiv_class (c : k) :
    projectiveLineCechHomologyZeroEquiv k
      ((projectiveLineCechComplex k).homologyπ 0 (projectiveLineCechZeroCycle k c)) = c := by
  let K := projectiveLineCechComplex k
  let S := K.sc' 0 0 1
  have hf : S.f = 0 := K.shape _ _ (by decide)
  have h : K.homologyπ 0 ≫
      (K.homologyIsoSc' 0 0 1 (by simp) (CochainComplex.next ℕ 0)).hom ≫
      (S.asIsoHomologyπ hf).inv ≫ S.moduleCatCyclesIso.hom =
      (projectiveLineCechZeroCycleKernelIso k).hom := by
    rw [K.π_homologyIsoSc'_hom_assoc]
    change (K.cyclesIsoSc' 0 0 1 (by simp) (CochainComplex.next ℕ 0)).hom ≫
      S.homologyπ ≫ (S.asIsoHomologyπ hf).inv ≫ S.moduleCatCyclesIso.hom = _
    rw [ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc]
    rfl
  change projectiveLineCechZeroKernelEquiv k
    ((K.homologyπ 0 ≫
      (K.homologyIsoSc' 0 0 1 (by simp) (CochainComplex.next ℕ 0)).hom ≫
      (S.asIsoHomologyπ hf).inv ≫ S.moduleCatCyclesIso.hom) (projectiveLineCechZeroCycle k c)) = c
  rw [h, projectiveLineCechZeroCycle, Iso.inv_hom_id_apply]
  exact (LinearEquiv.ofBijective (projectiveLineCechZeroConstants k)
    (by exact projectiveLineCechZeroConstants_bijective k)).symm_apply_apply c

/-- The scalar `c` corresponds to the class of the diagonal constant cycle. -/
@[simp]
lemma projectiveLineCechHomologyZeroEquiv_symm (c : k) :
    (projectiveLineCechHomologyZeroEquiv k).symm c =
      (projectiveLineCechComplex k).homologyπ 0 (projectiveLineCechZeroCycle k c) := by
  apply (projectiveLineCechHomologyZeroEquiv k).injective
  rw [LinearEquiv.apply_symm_apply, projectiveLineCechHomologyZeroEquiv_class]

end OrlikSolomon.Geometric.Examples
