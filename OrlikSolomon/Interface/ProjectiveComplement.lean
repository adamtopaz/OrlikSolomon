/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Interface.ProjectiveSpace

/-!
# Comparing projective complements and ratios

This module compares the Mathlib-only open complement and equation ratios of the main theorem
with the library's projective complement and its ratio units. The definitions repeat the approved
skeleton's bodies. The comparison is over `Spec k` and uses no rational point.

## Main definitions and results

* `complementOpens`, `complement`, `ratio`: the main theorem's open complement and fractions.
* `complementIso`: the comparison with the library's actual open subscheme.
* `complement_isAffine_smooth`: affineness and smoothness for a nonempty arrangement.
* `complementIso_hom_appTop_projectiveRatio`, `isUnit_ratio`: agreement with the library's ratio
  units, and invertibility of the ratio of any two equations.

Blueprint: `def:geo-projective`, `thm:geo-projective-geometry`; milestone M7, issue #141.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace OrlikSolomon.Interface
open ProjectiveArrangement CoordinateRing
variable {k : Type u} [Field k] {n : ℕ} (𝒜 : HyperplaneArrangement k n)
/-- The complement `ℙⁿ ∖ ⋃_{H ∈ 𝒜} H`, an open subset of `ℙⁿ`. -/
def complementOpens : (projectiveSpace k n).left.Opens where
  carrier := (⋃ H ∈ 𝒜, (H : Set (projectiveSpace k n).left))ᶜ
  is_open' := by
    rw [isOpen_compl_iff]
    refine 𝒜.finite_toSet.isClosed_biUnion fun H _ ↦ ?_
    obtain ⟨ℓ, hℓ⟩ := H.2
    rw [← hℓ.zeroLocus_eq]
    exact ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The **complement** `U = ℙⁿ ∖ ⋃_{H ∈ 𝒜} H`, the open subscheme of `ℙⁿ` on `complementOpens 𝒜`,
as a scheme over `Spec k`. -/
@[implicit_reducible]
def complement : Over (Spec (.of k)) :=
  Over.mk ((complementOpens 𝒜).ι ≫ (projectiveSpace k n).hom)

/-- The function `ℓ / ℓ'` on the complement, for a linear form `ℓ` and an equation `ℓ'` of a
hyperplane of `𝒜`. It is the degree-zero fraction `ℓ / ℓ'`, a function on the chart `D₊(ℓ')` of
`ℙⁿ` where `ℓ'` does not vanish, restricted to the complement, which lies in that chart. If `ℓ` is
an equation of a hyperplane of `𝒜` too, it is a unit. -/
def ratio {𝒜 : HyperplaneArrangement k n} {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : ℓ.IsHomogeneous 1) (hℓ' : IsEquation K ℓ') :
    Γ((complement 𝒜).left, ⊤) :=
  (complementOpens 𝒜).ι.appLE (Proj.basicOpen (degreeGrading k n) ℓ') ⊤ (fun x _ h ↦ by
    have hx : x.1 ∉ ⋃ H ∈ 𝒜, (H : Set (projectiveSpace k n).left) := x.2
    have hℓx : x.1 ∈ ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ'} :=
      (ProjectiveSpectrum.mem_zeroLocus _ _ _).2 (Set.singleton_subset_iff.2 h)
    exact hx (Set.mem_biUnion hK (hℓ'.zeroLocus_eq ▸ hℓx)))
    (Proj.awayToSection (degreeGrading k n) ℓ'
      (HomogeneousLocalization.Away.mk (degreeGrading k n) hℓ'.isHomogeneous 1 ℓ
        (by simpa using hℓ)))


/-- The projective-space comparison identifies the two open complements, independently of
equations and including the empty arrangement. -/
theorem preimage_complementOpen :
    (projectiveSpaceIso k n).hom.left ⁻¹ᵁ complementOpen (toProjectiveArrangement 𝒜) =
      complementOpens 𝒜 := by
  ext x
  change (projectiveSpaceIso k n).hom.left x ∈ complementOpen (toProjectiveArrangement 𝒜) ↔
    x ∉ ⋃ H ∈ 𝒜, (H : Set (projectiveSpace k n).left)
  rw [mem_complementOpen_iff]
  constructor
  · intro hx hmem
    obtain ⟨H, hH, hxH⟩ := Set.mem_iUnion₂.1 hmem
    have hℓ := isEquation_hyperplaneForm H
    have hz : x ∈ ProjectiveSpectrum.zeroLocus (degreeGrading k n) {hyperplaneForm H} :=
      hℓ.zeroLocus_eq.symm ▸ hxH
    have hz' : (projectiveSpaceIso k n).hom.left x ∈
        ProjectiveSpectrum.zeroLocus (symmetricGrading k (Module.Dual k (Fin (n + 1) → k)))
          {coord (toDual (hyperplaneForm H)).toAffineMap} := by
      change x ∈ (projectiveSpaceIso k n).hom.left ⁻¹'
        ProjectiveSpectrum.zeroLocus _ _
      rw [preimage_zeroLocus_coord_toDual hℓ.isHomogeneous]
      exact hz
    exact hx _ (ker_toDual_mem_toProjectiveArrangement hH hℓ)
      ((ProjectiveSpectrum.mem_zeroLocus _ _ _).1 hz' (Set.mem_singleton _))
  · intro hx ℓ hℓ
    obtain ⟨H, hH, hker⟩ := mem_toProjectiveArrangement.1 hℓ
    have hHℓ := isEquation_hyperplaneForm H
    have hxH : x ∉ (H : Set (projectiveSpace k n).left) :=
      fun h ↦ hx (Set.mem_iUnion₂.2 ⟨H, hH, h⟩)
    have hxℓ : x ∈ Proj.basicOpen (degreeGrading k n) (hyperplaneForm H) := by
      change hyperplaneForm H ∉ x.asHomogeneousIdeal
      intro h
      exact hxH (hHℓ.zeroLocus_eq ▸
        (ProjectiveSpectrum.mem_zeroLocus _ _ _).2 (Set.singleton_subset_iff.2 h))
    change x ∈ (projectiveSpaceIso k n).hom.left ⁻¹ᵁ
      Proj.basicOpen (symmetricGrading k (Module.Dual k (Fin (n + 1) → k)))
        (coord ℓ.toAffineMap)
    rw [basicOpen_coord_eq_of_ker_eq
      (hker.symm.trans (hyperplaneSubmodule_eq_ker hHℓ))
      (toDual_ne_zero hHℓ.isHomogeneous hHℓ.ne_zero),
      preimage_basicOpen_coord_toDual hHℓ.isHomogeneous]
    exact hxℓ

/-- The comparison of the actual open complements as schemes. -/
def complementSchemeIso :
    (complement 𝒜).left ≅ (Geometric.projectiveComplement (toProjectiveArrangement 𝒜)).left :=
  ((projectiveSpace k n).left.isoOfEq (preimage_complementOpen 𝒜).symm) ≪≫
    (projectiveSpaceIso k n).hom.left.preimageIso (complementOpen (toProjectiveArrangement 𝒜))

/-- The restricted comparison commutes with the two open immersions. -/
@[reassoc]
theorem complementSchemeIso_hom_ι :
    (complementSchemeIso 𝒜).hom ≫ (complementOpen (toProjectiveArrangement 𝒜)).ι =
      (complementOpens 𝒜).ι ≫ (projectiveSpaceIso k n).hom.left := by
  change (((projectiveSpace k n).left.isoOfEq (preimage_complementOpen 𝒜).symm).hom ≫
    ((projectiveSpaceIso k n).hom.left.preimageIso _).hom) ≫ _ = _
  rw [Category.assoc, Scheme.Hom.preimageIso_hom_ι, ← Category.assoc,
    Scheme.isoOfEq_hom_ι]

/-- The Mathlib-only open complement is the library's projective complement, over `Spec k`. -/
def complementIso : complement 𝒜 ≅ Geometric.projectiveComplement (toProjectiveArrangement 𝒜) :=
  Over.isoMk (complementSchemeIso 𝒜) (by
    change ((complementSchemeIso 𝒜).hom ≫
      (complementOpen (toProjectiveArrangement 𝒜)).ι) ≫
        (Geometric.projectiveSpace k (Fin (n + 1) → k)).hom =
      (complementOpens 𝒜).ι ≫ (projectiveSpace k n).hom
    exact (congrArg (fun g ↦ g ≫ (Geometric.projectiveSpace k (Fin (n + 1) → k)).hom)
      (complementSchemeIso_hom_ι 𝒜)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun g ↦ (complementOpens 𝒜).ι ≫ g) (Over.w (projectiveSpaceIso k n).hom))))

/-- The underlying map is the comparison of open subschemes. -/
@[simp]
theorem complementIso_hom_left : (complementIso 𝒜).hom.left = (complementSchemeIso 𝒜).hom := rfl

/-- The complement of a nonempty arrangement is affine and smooth over `k`. -/
theorem complement_isAffine_smooth (h𝒜 : 𝒜.Nonempty) :
    IsAffine (complement 𝒜).left ∧ Smooth (complement 𝒜).hom := by
  obtain ⟨H, hH⟩ := h𝒜
  let : Nonempty 𝒜 := ⟨⟨H, hH⟩⟩
  refine ⟨.of_isIso (complementIso 𝒜).hom.left, ?_⟩
  rw [← Over.w (complementIso 𝒜).hom]
  infer_instance

/-- The complement lies in the chart of every equation of a member. -/
theorem complementOpens_le_basicOpen {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ' : IsEquation K ℓ') :
    complementOpens 𝒜 ≤ Proj.basicOpen (degreeGrading k n) ℓ' := by
  intro x hx h
  exact hx (Set.mem_biUnion hK (hℓ'.zeroLocus_eq ▸
    (ProjectiveSpectrum.mem_zeroLocus _ _ _).2 (Set.singleton_subset_iff.2 h)))

private theorem top_le_complementOpens_ι_preimage_basicOpen {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ' : IsEquation K ℓ') :
    ⊤ ≤ (complementOpens 𝒜).ι ⁻¹ᵁ Proj.basicOpen (degreeGrading k n) ℓ' :=
  (Scheme.Opens.ι_preimage_self _).ge.trans
    (Scheme.Hom.preimage_mono _ (complementOpens_le_basicOpen 𝒜 hK hℓ'))

private theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {U : Y.Opens} {V : X.Opens} (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

private theorem restricted_chart_pullback {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ' : IsEquation K ℓ') :
    let s := coord (toDual ℓ').toAffineMap
    let F := symmetricGradingToMvPolynomial (coordinateBasis k n)
    let U := Proj.basicOpen (symmetricGrading k (Module.Dual k (Fin (n + 1) → k))) s
    let V := Proj.basicOpen (degreeGrading k n) (F s)
    ∃ (hV : ⊤ ≤ (complementOpen (toProjectiveArrangement 𝒜)).ι ⁻¹ᵁ U)
      (hE : V ≤ (projectiveSpaceIso k n).hom.left ⁻¹ᵁ U)
      (hU : ⊤ ≤ (complementOpens 𝒜).ι ⁻¹ᵁ V),
      (complementOpen (toProjectiveArrangement 𝒜)).ι.appLE U ⊤ hV ≫
          (complementSchemeIso 𝒜).hom.appTop =
        (projectiveSpaceIso k n).hom.left.appLE U V hE ≫
          (complementOpens 𝒜).ι.appLE V ⊤ hU := by
  dsimp only
  have hV := top_le_complementOpen_ι_preimage_basicOpen (toProjectiveArrangement 𝒜)
    (ker_toDual_mem_toProjectiveArrangement hK hℓ')
  have hE : Proj.basicOpen (degreeGrading k n)
      (symmetricGradingToMvPolynomial (coordinateBasis k n) (coord (toDual ℓ').toAffineMap)) ≤
      (projectiveSpaceIso k n).hom.left ⁻¹ᵁ
        Proj.basicOpen (symmetricGrading k (Module.Dual k (Fin (n + 1) → k)))
          (coord (toDual ℓ').toAffineMap) := by
    rw [projectiveSpaceIso_hom_left, Proj.map_preimage_basicOpen]
  have hU : ⊤ ≤ (complementOpens 𝒜).ι ⁻¹ᵁ Proj.basicOpen (degreeGrading k n)
      (symmetricGradingToMvPolynomial (coordinateBasis k n) (coord (toDual ℓ').toAffineMap)) := by
    rw [symmetricGradingToMvPolynomial_coord_toDual hℓ'.isHomogeneous]
    exact top_le_complementOpens_ι_preimage_basicOpen 𝒜 hK hℓ'
  refine ⟨hV, hE, hU, ?_⟩
  have h₁ := Scheme.Hom.appLE_comp_appLE (complementSchemeIso 𝒜).hom
    (complementOpen (toProjectiveArrangement 𝒜)).ι _ ⊤ ⊤ hV
    (Scheme.Hom.preimage_top _).ge
  rw [appLE_top_eq_appTop] at h₁
  exact h₁.trans ((appLE_congr_hom (complementSchemeIso_hom_ι 𝒜) _ _).trans
    (Scheme.Hom.appLE_comp_appLE (complementOpens 𝒜).ι
      (projectiveSpaceIso k n).hom.left _ _ ⊤ hE hU).symm)

variable [Nonempty 𝒜]

private theorem restricted_linearFraction_congr {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒢 : ℕ → σ} [GradedRing 𝒢] {X : Scheme.{u}} (g : X ⟶ Proj 𝒢)
    {s t : A} (hst : s = t) (hs : s ∈ 𝒢 1) (ht : t ∈ 𝒢 1)
    (hgs : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen 𝒢 s) (hgt : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen 𝒢 t)
    (a : A) (ha : a ∈ 𝒢 1) :
    g.appLE (Proj.basicOpen 𝒢 s) ⊤ hgs
        (Proj.awayToSection 𝒢 s (Away.mk 𝒢 hs 1 a (by simpa using ha))) =
      g.appLE (Proj.basicOpen 𝒢 t) ⊤ hgt
        (Proj.awayToSection 𝒢 t (Away.mk 𝒢 ht 1 a (by simpa using ha))) := by
  subst t
  rfl

/-- Pulling the library's fraction section back to the Mathlib complement gives the fraction
in the approved main-theorem definition. The numerator may be any homogeneous linear form. -/
theorem complementSchemeIso_hom_appTop_ratio {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : ℓ.IsHomogeneous 1) (hℓ' : IsEquation K ℓ') :
    (complementSchemeIso 𝒜).hom.appTop
      ((complementOpenIso (toProjectiveArrangement 𝒜)).hom.appTop
        ((Scheme.ΓSpecIso (.of (toProjectiveArrangement 𝒜).ComplementRing)).inv
          (ComplementRing.ratio (toDual ℓ) (ker_toDual_mem_toProjectiveArrangement hK hℓ')))) =
      ratio hK hℓ hℓ' := by
  rw [complementOpenIso_hom_appTop_ratio]
  obtain ⟨hV, hE, hU, hcomp⟩ := restricted_chart_pullback 𝒜 hK hℓ'
  let F := symmetricGradingToMvPolynomial (coordinateBasis k n)
  let s := coord (toDual ℓ').toAffineMap
  have hnat := Proj.awayToSection_comp_appLE F
    (irrelevant_le_map_of_comp_eq_id F
      (mvPolynomialToSymmetricGrading (coordinateBasis k n)) coordinateGraded_comp)
    (coord_toAffineMap_mem (toDual ℓ'))
  have hnat' : Proj.awayToSection _ s ≫
      (projectiveSpaceIso k n).hom.left.appLE _ _ hE =
      CommRingCat.ofHom (Away.map F s : Away _ s →+* Away _ (F s)) ≫
        Proj.awayToSection _ (F s) := hnat
  have hfull : Proj.awayToSection _ s ≫
      ((complementOpen (toProjectiveArrangement 𝒜)).ι.appLE _ ⊤ hV ≫
        (complementSchemeIso 𝒜).hom.appTop) =
      CommRingCat.ofHom (Away.map F s : Away _ s →+* Away _ (F s)) ≫
        (Proj.awayToSection _ (F s) ≫ (complementOpens 𝒜).ι.appLE _ ⊤ hU) := by
    exact (congrArg (fun φ ↦ Proj.awayToSection _ s ≫ φ) hcomp).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun φ ↦ φ ≫ (complementOpens 𝒜).ι.appLE _ ⊤ hU) hnat').trans
          (Category.assoc _ _ _)))
  have hval := congrArg (fun φ ↦ φ (Away.mk _ (coord_toAffineMap_mem (toDual ℓ')) 1
      (coord (toDual ℓ).toAffineMap) (by simpa using coord_toAffineMap_mem (toDual ℓ)))) hfull
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Away.map_mk, F, s,
    symmetricGradingToMvPolynomial_coord_toDual hℓ] at hval
  exact hval.trans (restricted_linearFraction_congr (complementOpens 𝒜).ι
    (symmetricGradingToMvPolynomial_coord_toDual hℓ'.isHomogeneous) _ _ _ _ ℓ hℓ)

/-- The complement comparison identifies the library's ratio unit with the main theorem's
fraction, for any equations of the two hyperplanes. -/
theorem complementIso_hom_appTop_projectiveRatio {H K : Hyperplane k n} (hH : H ∈ 𝒜)
    (hK : K ∈ 𝒜) {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
    (hℓ : IsEquation H ℓ) (hℓ' : IsEquation K ℓ') :
    (complementIso 𝒜).hom.left.appTop
      (Geometric.projectiveRatio (ker_toDual_mem_toProjectiveArrangement hH hℓ)
        (ker_toDual_mem_toProjectiveArrangement hK hℓ') :
          Γ((Geometric.projectiveComplement (toProjectiveArrangement 𝒜)).left, ⊤)) =
      ratio hK hℓ.isHomogeneous hℓ' := by
  change (complementSchemeIso 𝒜).hom.appTop
    ((complementOpenIso (toProjectiveArrangement 𝒜)).hom.appTop
      ((Scheme.ΓSpecIso (.of (toProjectiveArrangement 𝒜).ComplementRing)).inv
        (ComplementRing.ratio (toDual ℓ) (ker_toDual_mem_toProjectiveArrangement hK hℓ')))) = _
  exact complementSchemeIso_hom_appTop_ratio 𝒜 hK hℓ.isHomogeneous hℓ'

/-- The ratio of equations of two members is a global unit on the actual open complement. -/
theorem isUnit_ratio {H K : Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation H ℓ) (hℓ' : IsEquation K ℓ') :
    IsUnit (ratio hK hℓ.isHomogeneous hℓ') := by
  rw [← complementIso_hom_appTop_projectiveRatio 𝒜 hH hK hℓ hℓ']
  exact ((Geometric.projectiveRatio (ker_toDual_mem_toProjectiveArrangement hH hℓ)
    (ker_toDual_mem_toProjectiveArrangement hK hℓ')).isUnit).map _

end OrlikSolomon.Interface
