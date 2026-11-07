/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Instance
public import OrlikSolomon.Examples.DeRhamCalculations.Torus
public import OrlikSolomon.Examples.DeRhamCharacteristic

/-!
# Affine de Rham regressions on actual schemes

The canonical affine comparison transports the punctured-line and two-torus computations
and the positive-characteristic obstructions to global sheaf forms and their classes.
The characteristic-zero computations have no supplied ordinary theory. The two coordinate
residues are the maps of actual geometric divisor pairs, with opposite signs.

The main calculations are `gmCohomologyEquiv`, `torusCohomologyEquiv`,
`gmClass_residue`, `torusXResidue_top`, and `torusYResidue_top`. In positive characteristic,
`affineLinePowerForm_closed`, `affineLinePower_ne_constant`,
`affineLineCharacteristicForm_not_exact`, and `affineLine_pull_not_surjective` give the
closed-function and integration obstructions on actual global sheaf forms.

Blueprint: `prop:geo-affine-regressions`.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
open scoped Polynomial LaurentPolynomial

universe u
namespace OrlikSolomon.Geometric.Examples
namespace AffineDeRham

section Base
variable {k : Type u} [CommRing k]

/-- The canonical algebra identification `A ≃ Γ(Spec A, 𝒪)` over the base ring. -/
def specSectionsEquiv (A : SmoothAlg k) :
    A ≃ₐ[k] globalSections ((SmoothDomain.aff k).spec A).obj :=
  CommAlgCat.algEquivOfIso (globalSectionsSpecIso A.obj).symm

/-- The cohomology of the actual affine scheme `Spec A`, with its global-form specification. -/
def specCohomologyEquiv (A : SmoothAlg k) :
    OrlikSolomon.DeRham.Cohomology k A ≃ₐ[k]
      Geometric.DeRham.Cohomology ((SmoothDomain.aff k).spec A) :=
  OrlikSolomon.DeRham.Cohomology.mapEquiv (specSectionsEquiv A)

/-- An algebraic differential word as a global sheaf form on `Spec A`. -/
def specGlobalForm (A : SmoothAlg k) (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    (Geometric.DeRham.formsSheaf k ((SmoothDomain.aff k).spec A).obj n).obj.obj (op ⊤) :=
  Geometric.DeRham.globalFormsEquiv _ n (Forms.mapPower (specSectionsEquiv A).toAlgHom n ω)

/-- The affine forms comparison takes a closed differential word to a closed global form. -/
lemma specGlobalForm_closed (A : SmoothAlg k) (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k])
    (hω : d k (ω : Forms k A) = 0) :
    (Geometric.DeRham.formsSheafD k ((SmoothDomain.aff k).spec A).obj n).hom.app (op ⊤)
      (specGlobalForm A n ω) = 0 := by
  apply Geometric.DeRham.formsSheafD_globalFormsEquiv_eq_zero_iff.2
  change d k (Forms.map (specSectionsEquiv A).toAlgHom (ω : Forms k A)) = 0
  rw [← Forms.map_d, hω, map_zero]

/-- Transport to scheme cohomology is the class of the actual global sheaf form. -/
lemma specCohomologyEquiv_mk (A : SmoothAlg k) (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k])
    (hω : d k (ω : Forms k A) = 0) :
    specCohomologyEquiv A (OrlikSolomon.DeRham.Cohomology.mk (ω : Forms k A) hω) =
      Geometric.DeRham.globalClass _ n (specGlobalForm A n ω) (specGlobalForm_closed A n ω hω) := by
  refine (OrlikSolomon.DeRham.Cohomology.map_mk (specSectionsEquiv A).toAlgHom _ _).trans ?_
  exact (Geometric.DeRham.globalClass_globalFormsEquiv
    (Forms.mapPower (specSectionsEquiv A).toAlgHom n ω) _).symm

/-- A polynomial function viewed as a differential word is its actual degree-zero sheaf form. -/
lemma specGlobalForm_zero (A : SmoothAlg k) (a : A) :
    specGlobalForm A 0 ⟨algebraMap A (Forms k A) a, algebraMap_mem_exteriorPower_zero k a⟩ =
      (Geometric.DeRham.formsSheafZeroIso k ((SmoothDomain.aff k).spec A).obj).hom.hom.app (op ⊤)
        (Geometric.DeRham.globalSectionsAlgEquiv _ (specSectionsEquiv A a)) := by
  rw [Geometric.DeRham.formsSheafZeroIso_hom]
  change (Geometric.DeRham.formsSheafUnit k ((SmoothDomain.aff k).spec A).obj 0).app (op ⊤)
    (Forms.mapPower (Geometric.DeRham.globalSectionsAlgEquiv _).toAlgHom 0
      (Forms.mapPower (specSectionsEquiv A).toAlgHom 0 _)) =
    (Geometric.DeRham.formsSheafUnit k ((SmoothDomain.aff k).spec A).obj 0).app (op ⊤) _
  congr 1
  apply Subtype.ext
  simp only [Forms.coe_mapPower, Forms.map_algebraMap]
  rfl

/-- The affine comparison preserves each cohomological degree in both directions. -/
lemma specCohomologyEquiv_mem_degree_iff (A : SmoothAlg k) (n : ℕ)
    (c : OrlikSolomon.DeRham.Cohomology k A) :
    specCohomologyEquiv A c ∈ Geometric.DeRham.Cohomology.degree ((SmoothDomain.aff k).spec A) n ↔
      c ∈ OrlikSolomon.DeRham.Cohomology.degree k A n := by
  constructor
  · intro h
    have hi := OrlikSolomon.DeRham.Cohomology.map_mem_degree
      (specSectionsEquiv A).symm.toAlgHom h
    change (specCohomologyEquiv A).symm (specCohomologyEquiv A c) ∈ _ at hi
    simpa only [AlgEquiv.symm_apply_apply] using hi
  · exact OrlikSolomon.DeRham.Cohomology.map_mem_degree (specSectionsEquiv A).toAlgHom

/-- Scheme pullback and algebraic pullback agree under the canonical spectrum comparisons. -/
lemma specCohomologyEquiv_pull {A B : SmoothAlg k} (f : A ⟶ B)
    (c : OrlikSolomon.DeRham.Cohomology k A) :
    Geometric.DeRham.Cohomology.pull ((SmoothDomain.aff k).specFunctor.map f).unop
      (specCohomologyEquiv A c) =
        specCohomologyEquiv B (OrlikSolomon.DeRham.Cohomology.map (SmoothAlg.algHom f) c) := by
  change OrlikSolomon.DeRham.Cohomology.map (globalSectionsMap (specMap f.hom)).hom
    (OrlikSolomon.DeRham.Cohomology.map (specSectionsEquiv A).toAlgHom c) =
      OrlikSolomon.DeRham.Cohomology.map (specSectionsEquiv B).toAlgHom
        (OrlikSolomon.DeRham.Cohomology.map (SmoothAlg.algHom f) c)
  rw [OrlikSolomon.DeRham.Cohomology.map_map, OrlikSolomon.DeRham.Cohomology.map_map]
  exact congrArg (fun g => OrlikSolomon.DeRham.Cohomology.map g c)
    (congrArg (fun g => g.hom) (globalSectionsSpecIso_inv_naturality f.hom)).symm

section NamedSchemes
variable (k)

/-- The actual punctured affine line `Spec k[x,x⁻¹]`. -/
abbrev gmScheme : (SmoothDomain.aff k).Obj := (SmoothDomain.aff k).spec (SmoothAlg.gm k)

/-- The actual two-torus `Spec k[x,x⁻¹,y,y⁻¹]`. -/
abbrev torusScheme : (SmoothDomain.aff k).Obj :=
  (SmoothDomain.aff k).spec (SmoothAlg.laurent (SmoothAlg.gm k))

/-- The logarithmic coordinate form `dx/x` as a global sheaf one-form on the punctured line. -/
def gmForm := specGlobalForm (SmoothAlg.gm k) 1
  ⟨dlog k (SmoothAlg.laurentT (SmoothAlg.point k)), dlog_mem_exteriorPower_one k _⟩

/-- The geometric punctured-line class is represented by its actual global form `dx/x`. -/
def gmClass : Geometric.DeRham.Cohomology (gmScheme k) :=
  Geometric.DeRham.globalClass _ 1 (gmForm k)
    (specGlobalForm_closed _ _ _ (d_dlog k _))

/-- The form `dx/x` on the two-torus, where `x` is the inner Laurent coordinate. -/
def torusXForm := specGlobalForm (SmoothAlg.laurent (SmoothAlg.gm k)) 1
  ⟨dlog k (SmoothAlg.mapUnits (SmoothAlg.laurentC (SmoothAlg.gm k))
    (SmoothAlg.laurentT (SmoothAlg.point k))), dlog_mem_exteriorPower_one k _⟩

/-- The form `dy/y` on the two-torus, where `y` is the outer Laurent coordinate. -/
def torusYForm := specGlobalForm (SmoothAlg.laurent (SmoothAlg.gm k)) 1
  ⟨dlog k (SmoothAlg.laurentT (SmoothAlg.gm k)), dlog_mem_exteriorPower_one k _⟩

/-- The inner-coordinate class represented by the actual global one-form `dx/x`. -/
def torusX : Geometric.DeRham.Cohomology (torusScheme k) :=
  Geometric.DeRham.globalClass _ 1 (torusXForm k)
    (specGlobalForm_closed _ _ _ (d_dlog k _))

/-- The outer-coordinate class represented by the actual global one-form `dy/y`. -/
def torusY : Geometric.DeRham.Cohomology (torusScheme k) :=
  Geometric.DeRham.globalClass _ 1 (torusYForm k)
    (specGlobalForm_closed _ _ _ (d_dlog k _))

/-- This spectrum model is the library's actual multiplicative group scheme. -/
lemma gmScheme_eq : gmScheme k = (SmoothDomain.aff k).gm := rfl

/-- The spectrum model of the two-torus is the actual product of two multiplicative groups. -/
def torusIsoProdGm : torusScheme k ≅ (SmoothDomain.aff k).prodGm (SmoothDomain.aff k).gm :=
  (SmoothDomain.aff k).specLaurentIso (SmoothAlg.gm k)

end NamedSchemes

end Base

section CharacteristicZero
variable {k : Type u} [Field k] [CharZero k]

/-- Residue is preserved by the canonical scheme/algebra comparison of a certified pair. -/
lemma specCohomologyEquiv_residue (P : OrlikSolomon.DivisorPair k)
    (c : OrlikSolomon.DeRham.Cohomology k P.compl) :
    Geometric.DeRham.residue (Geometric.DivisorPair.spec (SmoothDomain.aff k) P)
      (specCohomologyEquiv P.compl c) =
        specCohomologyEquiv P.closed
          (OrlikSolomon.DeRham.residue P.compl (isUnit_natCast_add_one k)
            P.isSmoothPrincipalPair c) := by
  exact OrlikSolomon.DeRham.residue_map (isUnit_natCast_add_one k)
    (Geometric.DivisorPair.unitIso P).hom.isPairHom P.isSmoothPrincipalPair
    (Geometric.DivisorPair.globalSections
      (Geometric.DivisorPair.spec (SmoothDomain.aff k) P)).isSmoothPrincipalPair c

variable (k)

omit [CharZero k] in
private lemma gmClass_eq : gmClass k = specCohomologyEquiv (SmoothAlg.gm k)
    (OrlikSolomon.DeRham.Examples.laurentThetaClass k (SmoothAlg.point k)) :=
  (specCohomologyEquiv_mk _ 1 _ (d_dlog k _)).symm

/-- The punctured-line cohomology has the ordered basis `1, [dx/x]`. -/
def gmCohomologyEquiv : (k × k) ≃ₗ[k] Geometric.DeRham.Cohomology (gmScheme k) :=
  (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k).trans
    (specCohomologyEquiv (SmoothAlg.gm k)).toLinearEquiv

/-- The two coordinates multiply the unit and the logarithmic global-form class. -/
@[simp] theorem gmCohomologyEquiv_apply (a b : k) :
    gmCohomologyEquiv k (a, b) = algebraMap k _ a + gmClass k * algebraMap k _ b := by
  change specCohomologyEquiv _ (OrlikSolomon.DeRham.Examples.gmCohomologyEquiv k (a, b)) = _
  rw [OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_apply, map_add, map_mul,
    AlgEquiv.commutes, AlgEquiv.commutes, ← gmClass_eq]

omit [CharZero k] in
/-- The logarithmic class on the punctured line squares to zero. -/
theorem gmClass_mul_self : gmClass k * gmClass k = 0 := by
  have h : OrlikSolomon.DeRham.Examples.laurentThetaClass k (SmoothAlg.point k) *
      OrlikSolomon.DeRham.Examples.laurentThetaClass k (SmoothAlg.point k) = 0 :=
    (OrlikSolomon.DeRham.Cohomology.mk_mul _ _ _ _).trans
      ((OrlikSolomon.DeRham.Cohomology.mk_congr (dlog_mul_self k _) _).trans
        (OrlikSolomon.DeRham.Cohomology.mk_zero _))
  rw [gmClass_eq, ← map_mul, h, map_zero]


omit [CharZero k] in
/-- The punctured-line generator has cohomological degree one. -/
theorem gmClass_mem_degree : gmClass k ∈ Geometric.DeRham.Cohomology.degree (gmScheme k) 1 := by
  rw [gmClass_eq, specCohomologyEquiv_mem_degree_iff]
  exact dlogClass_mem_degree _

/-- The punctured-line basis has degrees zero and one. -/
theorem gmCohomologyEquiv_mem_degree_iff (n : ℕ) (a b : k) :
    gmCohomologyEquiv k (a, b) ∈ Geometric.DeRham.Cohomology.degree (gmScheme k) n ↔
      ((n : ℤ) = 0 ∨ a = 0) ∧ ((n : ℤ) = 1 ∨ b = 0) := by
  rw [gmCohomologyEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    specCohomologyEquiv_mem_degree_iff, ← OrlikSolomon.DeRham.Cohomology.grading_natCast]
  exact OrlikSolomon.DeRham.Examples.gmCohomologyEquiv_mem_grading_iff k n a b

/-- The punctured line has no cohomology above degree one. -/
theorem gm_eq_zero_of_mem_degree_succ_succ (n : ℕ)
    {c : Geometric.DeRham.Cohomology (gmScheme k)}
    (hc : c ∈ Geometric.DeRham.Cohomology.degree (gmScheme k) (n + 2)) : c = 0 := by
  obtain ⟨x, rfl⟩ := (specCohomologyEquiv (SmoothAlg.gm k)).surjective c
  rw [specCohomologyEquiv_mem_degree_iff] at hc
  rw [OrlikSolomon.DeRham.Examples.gm_eq_zero_of_mem_degree_succ_succ k n hc, map_zero]

/-- The actual geometric pair `(𝔸¹, {0}, 𝔾ₘ)`, obtained by affine duality. -/
abbrev gmPair : Geometric.DivisorPair (SmoothDomain.aff k) :=
  Geometric.DivisorPair.spec _ (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k))

/-- The residue of the actual global-form generator on the punctured line is one. -/
theorem gmClass_residue : Geometric.DeRham.residue (gmPair k) (gmClass k) = 1 := by
  refine (congrArg (Geometric.DeRham.residue (gmPair k)) (gmClass_eq k)).trans
    ((specCohomologyEquiv_residue _ _).trans ?_)
  rw [OrlikSolomon.DeRham.Examples.gm_residue_theta, map_one]

omit [CharZero k] in
private lemma torusX_eq : torusX k = specCohomologyEquiv _
    (OrlikSolomon.DeRham.Examples.torusX k) := by
  change Geometric.DeRham.globalClass _ 1 (specGlobalForm _ 1 _) _ = _
  rw [← specCohomologyEquiv_mk _ 1 _ (d_dlog k _)]
  exact congrArg (specCohomologyEquiv _) (map_dlogClass _ _).symm

omit [CharZero k] in
private lemma torusY_eq : torusY k = specCohomologyEquiv _
    (OrlikSolomon.DeRham.Examples.torusY k) :=
  (specCohomologyEquiv_mk _ 1 _ (d_dlog k _)).symm

/-- The ordered exterior basis `1, [dx/x], [dy/y], [dx/x][dy/y]` of the actual two-torus. -/
def torusCohomologyEquiv : ((k × k) × (k × k)) ≃ₗ[k]
    Geometric.DeRham.Cohomology (torusScheme k) :=
  (OrlikSolomon.DeRham.Examples.torusCohomologyEquiv k).trans
    (specCohomologyEquiv (SmoothAlg.laurent (SmoothAlg.gm k))).toLinearEquiv

/-- The two-torus coefficients are the coefficients of its ordered exterior basis. -/
theorem torusCohomologyEquiv_apply (a b c e : k) :
    torusCohomologyEquiv k ((a, b), (c, e)) = algebraMap k _ a + b • torusX k +
      c • torusY k + e • (torusX k * torusY k) := by
  change specCohomologyEquiv _
    (OrlikSolomon.DeRham.Examples.torusCohomologyEquiv k ((a, b), (c, e))) = _
  rw [OrlikSolomon.DeRham.Examples.torusCohomologyEquiv_apply]
  simp only [map_add, map_smul, map_mul, AlgEquiv.commutes, ← torusX_eq, ← torusY_eq]

omit [CharZero k] in
/-- The first logarithmic coordinate generator squares to zero. -/
theorem torusX_mul_self : torusX k * torusX k = 0 := by
  rw [torusX_eq, ← map_mul, OrlikSolomon.DeRham.Examples.torusX_mul_self, map_zero]

omit [CharZero k] in
/-- The second logarithmic coordinate generator squares to zero. -/
theorem torusY_mul_self : torusY k * torusY k = 0 := by
  rw [torusY_eq, ← map_mul, OrlikSolomon.DeRham.Examples.torusY_mul_self, map_zero]

omit [CharZero k] in
/-- The logarithmic coordinate generators anticommute. -/
theorem torus_anticommute : torusY k * torusX k = -(torusX k * torusY k) := by
  rw [torusX_eq, torusY_eq, ← map_mul, OrlikSolomon.DeRham.Examples.torus_anticommute,
    map_neg, map_mul]

/-- The ordered top exterior class of the two-torus is nonzero. -/
theorem torus_top_ne_zero : torusX k * torusY k ≠ 0 := by
  rw [torusX_eq, torusY_eq, ← map_mul]
  intro h
  exact OrlikSolomon.DeRham.Examples.torus_top_ne_zero k
    ((specCohomologyEquiv _).injective (h.trans (map_zero _).symm))

/-- The exterior basis of the two-torus has degrees `0, 1, 1, 2`. -/
theorem torusCohomologyEquiv_mem_degree_iff (n : ℕ) (a b c e : k) :
    torusCohomologyEquiv k ((a, b), (c, e)) ∈
        Geometric.DeRham.Cohomology.degree (torusScheme k) n ↔
      ((n : ℤ) = 0 ∨ a = 0) ∧ ((n : ℤ) = 1 ∨ b = 0) ∧
        ((n : ℤ) = 1 ∨ c = 0) ∧ ((n : ℤ) = 2 ∨ e = 0) := by
  rw [torusCohomologyEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    specCohomologyEquiv_mem_degree_iff, ← OrlikSolomon.DeRham.Cohomology.grading_natCast]
  exact OrlikSolomon.DeRham.Examples.torusCohomologyEquiv_mem_grading_iff k n a b c e

/-- The two-torus has no cohomology above degree two. -/
theorem torus_eq_zero_of_mem_degree_succ_succ_succ (n : ℕ)
    {c : Geometric.DeRham.Cohomology (torusScheme k)}
    (hc : c ∈ Geometric.DeRham.Cohomology.degree (torusScheme k) (n + 3)) : c = 0 := by
  obtain ⟨x, rfl⟩ :=
    (specCohomologyEquiv (SmoothAlg.laurent (SmoothAlg.gm k))).surjective c
  rw [specCohomologyEquiv_mem_degree_iff] at hc
  rw [OrlikSolomon.DeRham.Examples.torus_eq_zero_of_mem_degree_succ_succ_succ k n hc, map_zero]

/-- The pair with ambient `𝔾ₘ_x × 𝔸¹_y`, closed divisor `y = 0`, and the fixed ordered torus. -/
abbrev torusYPair : Geometric.DivisorPair (SmoothDomain.aff k) :=
  Geometric.DivisorPair.spec _ (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.gm k))

/-- The pair with ambient `𝔸¹_x × 𝔾ₘ_y` and divisor `x = 0`, using the same ordered torus. -/
abbrev torusXPair : Geometric.DivisorPair (SmoothDomain.aff k) :=
  Geometric.DivisorPair.spec _ (OrlikSolomon.DeRham.Examples.torusXPair k)

/-- The ambient of the `y`-pair is the actual product `𝔾ₘ_x × 𝔸¹_y`. -/
def torusYPairAmbientIso : (torusYPair k).ambient ≅
    (SmoothDomain.aff k).prodAffineLine (SmoothDomain.aff k).gm :=
  (SmoothDomain.aff k).specPolynomialIso (SmoothAlg.gm k)

/-- The ambient of the `x`-pair is the actual product `𝔸¹_x × 𝔾ₘ_y`. -/
def torusXPairAmbientIso : (torusXPair k).ambient ≅
    (SmoothDomain.aff k).prodGm (SmoothDomain.aff k).affineLine :=
  ObjectProperty.isoMk _ (Geometric.specPolynomialIso (SmoothAlg.gm k).obj ≪≫
    BraidedCategory.braiding _ _)

/-- Along `x = 0`, the residue of the ordered class `[dx/x][dy/y]` is `[dy/y]`. -/
theorem torusXPair_residue_top :
    Geometric.DeRham.residue (torusXPair k) (torusX k * torusY k) = gmClass k := by
  have ht : torusX k * torusY k = specCohomologyEquiv _
      (OrlikSolomon.DeRham.Examples.torusX k * OrlikSolomon.DeRham.Examples.torusY k) := by
    rw [torusX_eq, torusY_eq, map_mul]
  refine (congrArg (Geometric.DeRham.residue (torusXPair k)) ht).trans
    ((specCohomologyEquiv_residue _ _).trans ?_)
  rw [OrlikSolomon.DeRham.Examples.torusXPair_residue_top]
  change specCohomologyEquiv (SmoothAlg.gm k) _ = gmClass k
  exact (gmClass_eq k).symm

/-- Along `y = 0`, the residue of the same ordered class is `-[dx/x]`. -/
theorem torusYPair_residue_top :
    Geometric.DeRham.residue (torusYPair k) (torusX k * torusY k) = -gmClass k := by
  have ht : torusX k * torusY k = specCohomologyEquiv _
      (OrlikSolomon.DeRham.Examples.torusX k * OrlikSolomon.DeRham.Examples.torusY k) := by
    rw [torusX_eq, torusY_eq, map_mul]
  refine (congrArg (Geometric.DeRham.residue (torusYPair k)) ht).trans
    ((specCohomologyEquiv_residue _ _).trans ?_)
  rw [OrlikSolomon.DeRham.Examples.torus_residue_inner_mul_outer]
  change specCohomologyEquiv (SmoothAlg.gm k)
    (-OrlikSolomon.DeRham.Examples.laurentThetaClass k (SmoothAlg.point k)) = -gmClass k
  rw [map_neg, ← gmClass_eq]

/-- Actual residue along `x = 0`, typed on the fixed torus and punctured-line cohomology. -/
def torusXResidue : Geometric.DeRham.Cohomology (torusScheme k) →ₗ[k]
    Geometric.DeRham.Cohomology (gmScheme k) := Geometric.DeRham.residue (torusXPair k)

/-- Actual residue along `y = 0`, typed on the same displayed cohomology carriers. -/
def torusYResidue : Geometric.DeRham.Cohomology (torusScheme k) →ₗ[k]
    Geometric.DeRham.Cohomology (gmScheme k) := Geometric.DeRham.residue (torusYPair k)

/-- The typed `x`-residue is the map of the actual geometric divisor pair. -/
lemma torusXResidue_apply (c : Geometric.DeRham.Cohomology (torusScheme k)) :
    torusXResidue k c = Geometric.DeRham.residue (torusXPair k) c := rfl

/-- The typed `y`-residue is the map of the actual geometric divisor pair. -/
lemma torusYResidue_apply (c : Geometric.DeRham.Cohomology (torusScheme k)) :
    torusYResidue k c = Geometric.DeRham.residue (torusYPair k) c := rfl

/-- Residue of the ordered top exterior class along `x = 0` has positive sign. -/
@[simp] theorem torusXResidue_top : torusXResidue k (torusX k * torusY k) = gmClass k :=
  torusXPair_residue_top k

/-- Residue of the same ordered top exterior class along `y = 0` has negative sign. -/
@[simp] theorem torusYResidue_top : torusYResidue k (torusX k * torusY k) = -gmClass k :=
  torusYPair_residue_top k

end CharacteristicZero

section PositiveCharacteristic
variable (k : Type u) [CommRing k]

/-- The actual affine line, presented as the spectrum of its polynomial algebra. -/
abbrev affineLineScheme : (SmoothDomain.aff k).Obj :=
  (SmoothDomain.aff k).spec (SmoothAlg.polynomial (SmoothAlg.point k))

/-- This spectrum model is the library's actual affine line. -/
lemma affineLineScheme_eq : affineLineScheme k = (SmoothDomain.aff k).affineLine := rfl

/-- The global polynomial function `x^p` on the actual affine line. -/
def affineLinePower (p : ℕ) : globalSections (affineLineScheme k).obj :=
  specSectionsEquiv (SmoothAlg.polynomial (SmoothAlg.point k)) (Polynomial.X ^ p)

/-- The global degree-zero sheaf form of the polynomial function `x^p`. -/
def affineLinePowerForm (p : ℕ) :=
  specGlobalForm (SmoothAlg.polynomial (SmoothAlg.point k)) 0
    ⟨algebraMap k[X] (Forms k k[X]) (Polynomial.X ^ p), algebraMap_mem_exteriorPower_zero k _⟩

/-- The closed degree-zero form is the actual structure-sheaf function `x^p`. -/
lemma affineLinePowerForm_eq (p : ℕ) :
    affineLinePowerForm k p =
      (Geometric.DeRham.formsSheafZeroIso k (affineLineScheme k).obj).hom.hom.app (op ⊤)
        (Geometric.DeRham.globalSectionsAlgEquiv _ (affineLinePower k p)) :=
  specGlobalForm_zero _ _

/-- In characteristic `p`, the actual global function form `x^p` is closed. -/
theorem affineLinePowerForm_closed (p : ℕ) [CharP k p] :
    (Geometric.DeRham.formsSheafD k (affineLineScheme k).obj 0).hom.app (op ⊤)
      (affineLinePowerForm k p) = 0 :=
  specGlobalForm_closed _ _ _ (OrlikSolomon.DeRham.Examples.d_algebraMap_X_pow_charP k p)

/-- The closed global function `x^p` is not constant when `p` is positive and `k` is nonzero. -/
theorem affineLinePower_ne_constant [Nontrivial k] {p : ℕ} (hp : 0 < p) (a : k) :
    affineLinePower k p ≠ algebraMap k (globalSections (affineLineScheme k).obj) a := by
  intro h
  apply OrlikSolomon.DeRham.Examples.X_pow_ne_C k hp a
  apply (specSectionsEquiv (SmoothAlg.polynomial (SmoothAlg.point k))).injective
  exact h.trans ((specSectionsEquiv (SmoothAlg.polynomial (SmoothAlg.point k))).commutes a).symm

/-- The actual closed global one-form `x^(p-1)dx` on the affine line. -/
def affineLineCharacteristicForm (p : ℕ) :=
  specGlobalForm (SmoothAlg.polynomial (SmoothAlg.point k)) 1
    ⟨OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm k p,
      OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm_mem_exteriorPower_one k p⟩

/-- The polynomial characteristic obstruction is closed as an actual global sheaf form. -/
theorem affineLineCharacteristicForm_closed (p : ℕ) :
    (Geometric.DeRham.formsSheafD k (affineLineScheme k).obj 1).hom.app (op ⊤)
      (affineLineCharacteristicForm k p) = 0 :=
  specGlobalForm_closed _ _ _ (OrlikSolomon.DeRham.Examples.d_polynomialCharacteristicForm k p)

/-- The actual sheaf one-form obstruction gives a nonzero class in positive characteristic. -/
theorem affineLineCharacteristicForm_class_ne_zero [Nontrivial k]
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    Geometric.DeRham.globalClass (affineLineScheme k).obj 1
      (affineLineCharacteristicForm k p) (affineLineCharacteristicForm_closed k p) ≠ 0 := by
  intro h
  have hh := (specCohomologyEquiv_mk (SmoothAlg.polynomial (SmoothAlg.point k)) 1
    ⟨OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm k p,
      OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm_mem_exteriorPower_one k p⟩
    (OrlikSolomon.DeRham.Examples.d_polynomialCharacteristicForm k p)).trans h
  exact OrlikSolomon.DeRham.Examples.polynomialCharacteristicForm_class_ne_zero k p hp
    ((specCohomologyEquiv (SmoothAlg.polynomial (SmoothAlg.point k))).injective
      (hh.trans (map_zero _).symm))

/-- No global sheaf function has differential `x^(p-1)dx` in positive characteristic. -/
theorem affineLineCharacteristicForm_not_exact [Nontrivial k]
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ¬ ∃ η : (Geometric.DeRham.formsSheaf k (affineLineScheme k).obj 0).obj.obj (op ⊤),
      (Geometric.DeRham.formsSheafD k (affineLineScheme k).obj 0).hom.app (op ⊤) η =
        affineLineCharacteristicForm k p := by
  intro h
  exact affineLineCharacteristicForm_class_ne_zero k p hp
    ((Geometric.DeRham.globalClass_eq_zero_iff (affineLineCharacteristicForm_closed k p)).2 h)

/-- Actual pullback along `𝔸¹ → Spec k`, with its scheme cohomology carriers explicit. -/
def affineLinePull : Geometric.DeRham.Cohomology ((SmoothDomain.aff k).spec (SmoothAlg.point k))
    →ₐ[k] Geometric.DeRham.Cohomology (affineLineScheme k) :=
  Geometric.DeRham.Cohomology.pull
    ((SmoothDomain.aff k).specFunctor.map (SmoothAlg.polynomialC (SmoothAlg.point k))).unop

/-- The structure map `𝔸¹ → Spec k` fails affine-line invariance on actual de Rham cohomology
in positive characteristic. Its pullback misses the closed class of `x^p`. -/
theorem affineLine_pull_not_surjective [Nontrivial k] (p : ℕ) [CharP k p] (hp : 0 < p) :
    ¬ Function.Surjective (affineLinePull k) := by
  intro h
  apply OrlikSolomon.DeRham.Examples.not_surjective_map_C_of_charP k p hp
  intro c
  obtain ⟨b, hb⟩ := h (specCohomologyEquiv (SmoothAlg.polynomial (SmoothAlg.point k)) c)
  refine ⟨(specCohomologyEquiv (SmoothAlg.point k)).symm b, ?_⟩
  apply (specCohomologyEquiv (SmoothAlg.polynomial (SmoothAlg.point k))).injective
  have hh := specCohomologyEquiv_pull (SmoothAlg.polynomialC (SmoothAlg.point k))
    ((specCohomologyEquiv (SmoothAlg.point k)).symm b)
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm.trans hb

end PositiveCharacteristic

end AffineDeRham
end OrlikSolomon.Geometric.Examples
