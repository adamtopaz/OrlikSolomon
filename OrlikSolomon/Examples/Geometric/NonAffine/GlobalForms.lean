/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.ChartForms
public import OrlikSolomon.Examples.Geometric.NonAffine.MatchingForms
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Global differential forms on the projective line

Sheaf gluing for the actual two-chart cover identifies global forms with matching polynomial
forms. Consequently global functions are constants and every global form of positive degree
vanishes. The global-sections de Rham complex is thus concentrated in degree zero.

Blueprint: `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Module Polynomial TopologicalSpace
open CategoryTheory.Limits
open scoped LaurentPolynomial

namespace OrlikSolomon.Geometric.Examples

open Geometric.DeRham OrlikSolomon.DeRham

universe u

section Gluing

variable {k : Type u} [CommRing k] {X : TopCat.{u}}

private def matchingSections (F : TopCat.Sheaf (ModuleCat.{u} k) X) (U V W : Opens X)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Submodule k (F.obj.obj (op U) × F.obj.obj (op V)) where
  carrier := {p | F.obj.map (homOfLE hWU : W ⟶ U).op p.1 =
    F.obj.map (homOfLE hWV : W ⟶ V).op p.2}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change _ = _ at hp hq
    change F.obj.map _ (p.1 + q.1) = F.obj.map _ (p.2 + q.2)
    simp only [map_add, hp, hq]
  smul_mem' a p hp := by
    change _ = _ at hp
    change F.obj.map _ (a • p.1) = F.obj.map _ (a • p.2)
    simp only [map_smul, hp]

private def globalToMatching (F : TopCat.Sheaf (ModuleCat.{u} k) X) (U V W : Opens X)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    F.obj.obj (op ⊤) →ₗ[k] matchingSections F U V W hWU hWV where
  toFun s := ⟨(F.obj.map (homOfLE le_top : U ⟶ ⊤).op s,
    F.obj.map (homOfLE le_top : V ⟶ ⊤).op s), by
      change F.obj.map _ (F.obj.map _ s) = F.obj.map _ (F.obj.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
      rfl⟩
  map_add' a b := by apply Subtype.ext; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' a b := by apply Subtype.ext; exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

private lemma globalToMatching_bijective (F : TopCat.Sheaf (ModuleCat.{u} k) X)
    (U V W : Opens X) (hWU : W ≤ U) (hWV : W ≤ V) (hW : W = U ⊓ V)
    (hUV : U ⊔ V = ⊤) : Function.Bijective (globalToMatching F U V W hWU hWV) := by
  let cover : Bool → Opens X := fun b => if b then U else V
  have hcover : (⊤ : Opens X) ≤ ⨆ b, cover b := by
    rw [← hUV]
    exact sup_le (le_iSup_of_le true (by simp [cover])) (le_iSup_of_le false (by simp [cover]))
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' cover ⊤ (fun _ => homOfLE le_top) hcover
    intro b
    cases b
    · exact congrArg (fun p => p.val.2) h
    · exact congrArg (fun p => p.val.1) h
  · intro p
    let sf : ∀ b, F.obj.obj (op (cover b)) := fun b => by
      cases b
      · exact p.val.2
      · exact p.val.1
    have hc : TopCat.Presheaf.IsCompatible F.obj cover sf := by
      intro a b
      cases a <;> cases b
      · rfl
      · have h := congrArg (F.obj.map (eqToHom ((inf_comm V U).trans hW.symm)).op) p.property
        simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp] at h
        exact h.symm
      · have h := congrArg (F.obj.map (eqToHom hW.symm).op) p.property
        simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp] at h
        exact h
      · rfl
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' cover ⊤ (fun _ => homOfLE le_top) hcover sf hc
    refine ⟨s, Subtype.ext (Prod.ext (hs true) (hs false))⟩

end Gluing

variable (k : Type u) [Field k]

private abbrev chartMatchingSections (n : ℕ) :=
  matchingSections (formsSheaf k (projectiveLine k) n)
    (projectiveLineChart k 0) (projectiveLineChart k 1) (projectiveLineOverlap k)
    (projectiveLineOverlap_le_chart k 0) (projectiveLineOverlap_le_chart k 1)

private def matchingSectionsEquiv (n : ℕ) :
    chartMatchingSections k n ≃ₗ[k] NonAffine.matchingForms k n where
  toFun p := ⟨((projectiveLineChartFormsEquiv k 0 n).symm p.val.1,
    (projectiveLineChartFormsEquiv k 1 n).symm p.val.2), by
      apply (NonAffine.mem_matchingForms _ _).2
      apply (projectiveLineOverlapFormsEquiv k n).injective
      exact (projectiveLineChartFormsEquiv_restrict_zero k n
        ((projectiveLineChartFormsEquiv k 0 n).symm p.val.1)).symm.trans
        ((congrArg ((formsSheaf k (projectiveLine k) n).obj.map
          (homOfLE (projectiveLineOverlap_le_chart k 0)).op)
          ((projectiveLineChartFormsEquiv k 0 n).apply_symm_apply p.val.1)).trans
          (p.property.trans ((congrArg ((formsSheaf k (projectiveLine k) n).obj.map
            (homOfLE (projectiveLineOverlap_le_chart k 1)).op)
            ((projectiveLineChartFormsEquiv k 1 n).apply_symm_apply p.val.2)).symm.trans
              (projectiveLineChartFormsEquiv_restrict_one k n
                ((projectiveLineChartFormsEquiv k 1 n).symm p.val.2)))))⟩
  invFun p := ⟨(projectiveLineChartFormsEquiv k 0 n p.val.1,
    projectiveLineChartFormsEquiv k 1 n p.val.2), by
    exact (projectiveLineChartFormsEquiv_restrict_zero k n p.val.1).trans
      ((congrArg (projectiveLineOverlapFormsEquiv k n)
        ((NonAffine.mem_matchingForms _ _).1 p.property)).trans
        (projectiveLineChartFormsEquiv_restrict_one k n p.val.2).symm)⟩
  left_inv p := Subtype.ext (Prod.ext
    ((projectiveLineChartFormsEquiv k 0 n).apply_symm_apply p.val.1)
    ((projectiveLineChartFormsEquiv k 1 n).apply_symm_apply p.val.2))
  right_inv p := Subtype.ext (Prod.ext
    ((projectiveLineChartFormsEquiv k 0 n).symm_apply_apply p.val.1)
    ((projectiveLineChartFormsEquiv k 1 n).symm_apply_apply p.val.2))
  map_add' p q := Subtype.ext (Prod.ext (map_add _ _ _) (map_add _ _ _))
  map_smul' a p := Subtype.ext (Prod.ext (map_smul _ _ _) (map_smul _ _ _))

/-- Global forms on the projective line are matching polynomial forms on its two charts. -/
@[no_expose] def projectiveLineGlobalFormsMatchingEquiv (n : ℕ) :
    (formsSheaf k (projectiveLine k) n).obj.obj (op ⊤) ≃ₗ[k] NonAffine.matchingForms k n :=
  (LinearEquiv.ofBijective
    (globalToMatching (formsSheaf k (projectiveLine k) n)
      (projectiveLineChart k 0) (projectiveLineChart k 1) (projectiveLineOverlap k)
      (projectiveLineOverlap_le_chart k 0) (projectiveLineOverlap_le_chart k 1))
    (globalToMatching_bijective _ _ _ _ _ _ (projectiveLineOverlap_eq_inf k)
      (projectiveLineChart_sup k))).trans (matchingSectionsEquiv k n)

/-- Every positive-degree global differential form on the projective line vanishes. -/
instance projectiveLineGlobalFormsPositive_subsingleton (n : ℕ) :
    Subsingleton ((formsSheaf k (projectiveLine k) (n + 1)).obj.obj (op ⊤)) :=
  (projectiveLineGlobalFormsMatchingEquiv k (n + 1)).injective.subsingleton

/-- Global differential forms of degree zero on the projective line are constants. -/
@[no_expose] def projectiveLineGlobalFormsZeroEquiv :
    (formsSheaf k (projectiveLine k) 0).obj.obj (op ⊤) ≃ₗ[k] k :=
  (projectiveLineGlobalFormsMatchingEquiv k 0).trans (NonAffine.matchingFormsZeroEquiv k).symm

private def globalFunctionCoefficient : sectionAlgebra k (projectiveLine k) ⊤ →ₐ[k] k :=
  (Polynomial.aeval (0 : k)).comp ((projectiveLineChartSectionsEquiv k 0).toAlgHom.comp
    (sectionRestriction k (projectiveLine k) (homOfLE le_top)))

private lemma globalFunction_eq_constant (a : sectionAlgebra k (projectiveLine k) ⊤) :
    a = algebraMap k (sectionAlgebra k (projectiveLine k) ⊤) (globalFunctionCoefficient k a) := by
  let p : k[X] := projectiveLineChartSectionsEquiv k 0
    (sectionRestriction k (projectiveLine k) (homOfLE le_top) a)
  let q : k[X] := projectiveLineChartSectionsEquiv k 1
    (sectionRestriction k (projectiveLine k) (homOfLE le_top) a)
  have hm : p.toLaurent = LaurentPolynomial.invert q.toLaurent := by
    have h0 := AlgHom.congr_fun (projectiveLineChartSectionsEquiv_restrict_zero k)
      (sectionRestriction k (projectiveLine k) (homOfLE le_top) a)
    have h1 := AlgHom.congr_fun (projectiveLineChartSectionsEquiv_restrict_one k)
      (sectionRestriction k (projectiveLine k) (homOfLE le_top) a)
    have hr : sectionRestriction k (projectiveLine k)
        (homOfLE (projectiveLineOverlap_le_chart k 0))
        (sectionRestriction k (projectiveLine k)
          (homOfLE (show projectiveLineChart k 0 ≤ ⊤ from le_top)) a) =
      sectionRestriction k (projectiveLine k)
        (homOfLE (projectiveLineOverlap_le_chart k 1))
        (sectionRestriction k (projectiveLine k)
          (homOfLE (show projectiveLineChart k 1 ≤ ⊤ from le_top)) a) := by
      rw [← AlgHom.comp_apply, ← sectionRestriction_comp,
        ← AlgHom.comp_apply, ← sectionRestriction_comp]
      rfl
    exact h0.symm.trans ((congrArg (projectiveLineOverlapSectionsEquiv k) hr).trans h1)
  obtain ⟨hp, hq⟩ := NonAffine.matchingPolynomials_eq_constants p q hm
  have hcoeff : globalFunctionCoefficient k a = p.coeff 0 := by
    exact (Polynomial.coeff_zero_eq_aeval_zero p).symm
  let cover : Bool → (projectiveLine k).left.Opens :=
    fun b => if b then projectiveLineChart k 0 else projectiveLineChart k 1
  have hcover : (⊤ : (projectiveLine k).left.Opens) ≤ ⨆ b, cover b := by
    rw [← projectiveLineChart_sup k]
    exact sup_le (le_iSup_of_le true (by simp [cover]))
      (le_iSup_of_le false (by simp [cover]))
  apply (functionsSheaf k (projectiveLine k)).eq_of_locally_eq'
    cover ⊤ (fun _ => homOfLE le_top) hcover
  intro b
  cases b
  · change sectionRestriction k (projectiveLine k)
        (homOfLE (show projectiveLineChart k 1 ≤ ⊤ from le_top)) a = _
    apply (projectiveLineChartSectionsEquiv k 1).injective
    change q = projectiveLineChartSectionsEquiv k 1
      (sectionRestriction k (projectiveLine k)
        (homOfLE (show projectiveLineChart k 1 ≤ ⊤ from le_top))
        (algebraMap k (sectionAlgebra k (projectiveLine k) ⊤) (globalFunctionCoefficient k a)))
    rw [AlgHom.commutes, AlgEquiv.commutes, hcoeff]
    exact hq
  · change sectionRestriction k (projectiveLine k)
        (homOfLE (show projectiveLineChart k 0 ≤ ⊤ from le_top)) a = _
    apply (projectiveLineChartSectionsEquiv k 0).injective
    change p = projectiveLineChartSectionsEquiv k 0
      (sectionRestriction k (projectiveLine k)
        (homOfLE (show projectiveLineChart k 0 ≤ ⊤ from le_top))
        (algebraMap k (sectionAlgebra k (projectiveLine k) ⊤) (globalFunctionCoefficient k a)))
    rw [AlgHom.commutes, AlgEquiv.commutes, hcoeff]
    exact hp

/-- All global regular functions on the projective line are constants, as a `k`-algebra. -/
@[no_expose] def projectiveLineSectionsEquiv :
    sectionAlgebra k (projectiveLine k) ⊤ ≃ₐ[k] k :=
  AlgEquiv.ofAlgHom (globalFunctionCoefficient k) (Algebra.ofId k _) (by
    apply AlgHom.ext; intro c; exact (globalFunctionCoefficient k).commutes c)
      (by apply AlgHom.ext; intro a; exact (globalFunction_eq_constant k a).symm)

/-- The coordinate algebra of global functions of the projective line is the base field. -/
def projectiveLineGlobalSectionsEquiv : globalSections (projectiveLine k) ≃ₐ[k] k :=
  (globalSectionsAlgEquiv (projectiveLine k)).trans (projectiveLineSectionsEquiv k)

/-- The inverse of the global-functions comparison is the canonical scalar map. -/
@[simp] lemma projectiveLineGlobalSectionsEquiv_symm_apply (c : k) :
    (projectiveLineGlobalSectionsEquiv k).symm c =
      algebraMap k (globalSections (projectiveLine k)) c := by
  simpa only [Algebra.algebraMap_self_apply] using
    (projectiveLineGlobalSectionsEquiv k).symm.commutes c

/-- Every global function on the projective line is its constant coefficient. -/
lemma projectiveLineGlobalSections_eq_algebraMap (a : globalSections (projectiveLine k)) :
    a = algebraMap k (globalSections (projectiveLine k))
      (projectiveLineGlobalSectionsEquiv k a) := by
  exact ((projectiveLineGlobalSectionsEquiv k).symm_apply_apply a).symm.trans
    (projectiveLineGlobalSectionsEquiv_symm_apply k _)

private def globalTermIso (n : ℕ) :
    (globalFormsComplex k (projectiveLine k)).X n ≅
      ((CochainComplex.single₀ (ModuleCat k)).obj (ModuleCat.of k k)).X n := by
  cases n with
  | zero => exact (projectiveLineGlobalFormsZeroEquiv k).toModuleIso
  | succ n =>
    have hz : IsZero ((globalFormsComplex k (projectiveLine k)).X (n + 1)) := by
      change IsZero ((formsSheaf k (projectiveLine k) (n + 1)).obj.obj (op ⊤))
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (ModuleCat.of k k) (n + 1) (by omega))

/-- The actual global-sections de Rham complex of the projective line is `k` in degree zero.
Blueprint: `prop:geo-nonaffine`. -/
@[no_expose] def projectiveLineGlobalFormsComplexIso :
    globalFormsComplex k (projectiveLine k) ≅
      (CochainComplex.single₀ (ModuleCat k)).obj (ModuleCat.of k k) :=
  HomologicalComplex.Hom.isoOfComponents (globalTermIso k) (by
    rintro n _ rfl
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      (ModuleCat.of k k) (n + 1) (by omega)).eq_of_tgt)

/-- Degree-zero cohomology of the actual global-forms complex of the projective line is `k`. -/
def projectiveLineGlobalFormsHomologyZeroEquiv :
    (globalFormsComplex k (projectiveLine k)).homology 0 ≃ₗ[k] k :=
  (HomologicalComplex.homologyMapIso (projectiveLineGlobalFormsComplexIso k) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      (ModuleCat.of k k)).toLinearEquiv

/-- Every positive cohomology group of the actual global-forms complex vanishes. -/
lemma projectiveLineGlobalFormsHomologyPositive_isZero (n : ℕ) :
    IsZero ((globalFormsComplex k (projectiveLine k)).homology (n + 1)) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0
    (ModuleCat.of k k) (n + 1) (by omega)).of_iso
      (HomologicalComplex.homologyMapIso (projectiveLineGlobalFormsComplexIso k) (n + 1))

end OrlikSolomon.Geometric.Examples
