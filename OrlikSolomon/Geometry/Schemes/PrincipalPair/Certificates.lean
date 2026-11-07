/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.AffinePairs

/-!
# The certificates of a principal pair

A geometric divisor pair (`def:geo-divisor-pair`) certifies its closed map `i : D ⟶ X` by
`IsClosedImmersion i ∧ i.ker = principalIdealSheaf f`, its open map `j : U ⟶ X` by
`IsOpenImmersion j ∧ j.opensRange = X.basicOpen f`, and its equation by `IsRegularSection f`. This
file proves what these certificates mean on every scheme, affine or not, and translates them
into the certificates of an algebraic `OrlikSolomon.DivisorPair` on affine schemes.

## Main results

* `exists_comp_eq_iff_of_ker_eq`, `range_subset_range_iff_of_opensRange_eq`: universal properties.
  A morphism `g` factors through `i` exactly when `g^* f = 0`, and through `j` exactly when `g^* f`
  is a unit.
* `ker_pullback_fst_of_ker_eq`, `opensRange_pullback_fst_of_opensRange_eq`: base change along any
  `g : Y ⟶ X` cuts out the zero scheme and the basic open of `g^* f`.
* `isClosedImmersion_and_ker_eq_of_mono`, `isOpenImmersion_of_mono`, `opensRange_eq_of_mono`: a
  monomorphism with the universal property of the zero scheme, or of the basic open, carries the
  certificate.
* `associated_iff_principalIdealSheaf_eq`: for a regular `b`, `a 𝒪_X = b 𝒪_X` exactly when `a` is
  a unit multiple of `b`. This is the gluing argument of `thm:geo-cartesian`.
* `IsRegularSection.of_isOpenImmersion_cover`: regularity is local.
* `isLocalization_appTop_of_opensRange_eq`: on an affine `X`, an open immersion onto `X.basicOpen f`
  makes `Γ(U, 𝒪)` the localization of `Γ(X, 𝒪)` away from `f`.
* `ker_specMap_of_ker_eq`, `opensRange_specMap_of_isLocalization`,
  `isRegularSection_ΓSpecIso_inv_iff`: the certificates of `Spec` of an algebraic pair.

Units and the empty scheme are allowed throughout.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace OrlikSolomon.Geometric

/-! ### Closed immersions cut out by one function -/

section Closed

variable {X Y T D : Scheme.{u}} {f : Γ(X, ⊤)}

/-- The ideal sheaf `f 𝒪_X` lies in the kernel of `g` exactly when `g^* f = 0`. -/
lemma principalIdealSheaf_le_ker_iff {g : T ⟶ X} :
    principalIdealSheaf f ≤ g.ker ↔ g.appTop f = 0 := by
  refine ⟨fun h ↦ ?_, principalIdealSheaf_le_ker⟩
  have e := IsClosedImmersion.lift_fac (zeroSchemeι f) g ((ker_zeroSchemeι f).trans_le h)
  rw [← e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSchemeι_appTop, map_zero]

/-- A morphism `g` factors through a closed immersion `i` exactly when the kernel of `i` is
contained in that of `g`. -/
lemma exists_comp_eq_iff_ker_le (i : D ⟶ X) [IsClosedImmersion i] (g : T ⟶ X) :
    (∃ h : T ⟶ D, h ≫ i = g) ↔ i.ker ≤ g.ker := by
  refine ⟨?_, fun H ↦ ⟨IsClosedImmersion.lift i g H, IsClosedImmersion.lift_fac i g H⟩⟩
  rintro ⟨h, rfl⟩
  exact Scheme.Hom.le_ker_comp h i

variable (f) in
/-- The function `f` vanishes on any `D ⟶ X` with kernel `f 𝒪_X`. -/
lemma appTop_eq_zero_of_ker_eq {i : D ⟶ X} (hi : i.ker = principalIdealSheaf f) :
    i.appTop f = 0 :=
  principalIdealSheaf_le_ker_iff.1 hi.ge

/-- The universal property of a closed immersion `i` with kernel `f 𝒪_X`: a morphism `g` factors
through `i` exactly when `g^* f = 0`. -/
lemma exists_comp_eq_iff_of_ker_eq {i : D ⟶ X} [IsClosedImmersion i]
    (hi : i.ker = principalIdealSheaf f) (g : T ⟶ X) :
    (∃ h : T ⟶ D, h ≫ i = g) ↔ g.appTop f = 0 := by
  rw [exists_comp_eq_iff_ker_le, hi, principalIdealSheaf_le_ker_iff]

/-- Base change of a closed immersion with kernel `f 𝒪_X` along any `g : Y ⟶ X` has kernel
`(g^* f) 𝒪_Y`: the scheme-theoretic preimage of the zero scheme of `f` is the zero scheme of
`g^* f`. No flatness is needed. -/
theorem ker_pullback_fst_of_ker_eq {i : D ⟶ X} [IsClosedImmersion i]
    (hi : i.ker = principalIdealSheaf f) (g : Y ⟶ X) :
    (pullback.fst g i).ker = principalIdealSheaf (g.appTop f) := by
  apply le_antisymm
  · rw [← ker_zeroSchemeι (g.appTop f), ← exists_comp_eq_iff_ker_le]
    have h0 : (zeroSchemeι (g.appTop f) ≫ g).appTop f = 0 := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSchemeι_appTop]
    obtain ⟨h, hh⟩ := (exists_comp_eq_iff_of_ker_eq hi _).2 h0
    exact ⟨pullback.lift _ h hh.symm, pullback.lift_fst _ _ _⟩
  · apply principalIdealSheaf_le_ker
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_eq_zero_of_ker_eq f hi, map_zero]

/-- A monomorphism `i : D ⟶ X` with `i^* f = 0` through which the zero scheme of `f` factors is a
closed immersion with kernel `f 𝒪_X`: it is isomorphic to `Z_X(f)` over `X`. -/
theorem isClosedImmersion_and_ker_eq_of_mono {i : D ⟶ X} [Mono i] (hi : i.appTop f = 0)
    {a : zeroScheme f ⟶ D} (ha : a ≫ i = zeroSchemeι f) :
    IsClosedImmersion i ∧ i.ker = principalIdealSheaf f := by
  have hb : zeroSchemeLift i hi ≫ zeroSchemeι f = i := zeroSchemeLift_ι i hi
  have : IsIso (zeroSchemeLift i hi) :=
    ⟨a, by rw [← cancel_mono i, Category.assoc, ha, hb, Category.id_comp],
      by rw [← cancel_mono (zeroSchemeι f), Category.assoc, hb, ha, Category.id_comp]⟩
  rw [← hb]
  exact ⟨inferInstance, (Scheme.Hom.ker_comp_of_isIso _ _).trans (ker_zeroSchemeι f)⟩

end Closed

/-! ### Open immersions onto a basic open -/

section Open

variable {X Y T U : Scheme.{u}} {f : Γ(X, ⊤)}

/-- A global function is a unit exactly when its basic open is everything. -/
lemma basicOpen_eq_top_iff (f : Γ(X, ⊤)) : X.basicOpen f = ⊤ ↔ IsUnit f := by
  refine ⟨fun h ↦ X.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ ↦ ?_,
    fun h ↦ X.basicOpen_of_isUnit h⟩
  have hx : x ∈ X.basicOpen f := by
    rw [h]
    trivial
  exact (X.mem_basicOpen_top f x).1 hx

/-- A morphism lands in `X.basicOpen f` exactly when it pulls `f` back to a unit. -/
lemma range_subset_basicOpen_iff (g : T ⟶ X) :
    Set.range g ⊆ (X.basicOpen f : Set X) ↔ IsUnit (g.appTop f) := by
  rw [← basicOpen_eq_top_iff, ← Scheme.preimage_basicOpen_top, eq_top_iff]
  constructor
  · intro h x _
    exact h ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h (Set.mem_univ x)

/-- The universal property of an open immersion `j` onto `X.basicOpen f`: a morphism `g` factors
through `j` exactly when `g^* f` is a unit. -/
lemma range_subset_range_iff_of_opensRange_eq {j : U ⟶ X} [IsOpenImmersion j]
    (hj : j.opensRange = X.basicOpen f) (g : T ⟶ X) :
    Set.range g ⊆ Set.range j ↔ IsUnit (g.appTop f) := by
  rw [← range_subset_basicOpen_iff, ← hj, Scheme.Hom.coe_opensRange]

variable (f) in
/-- The function `f` is a unit on any open immersion onto `X.basicOpen f`. -/
lemma isUnit_appTop_of_opensRange_eq {j : U ⟶ X} [IsOpenImmersion j]
    (hj : j.opensRange = X.basicOpen f) : IsUnit (j.appTop f) :=
  (range_subset_range_iff_of_opensRange_eq hj j).1 subset_rfl

/-- Base change of an open immersion onto `X.basicOpen f` along any `g : Y ⟶ X` is an open
immersion onto `Y.basicOpen (g^* f)`. -/
theorem opensRange_pullback_fst_of_opensRange_eq {j : U ⟶ X} [IsOpenImmersion j]
    (hj : j.opensRange = X.basicOpen f) (g : Y ⟶ X) :
    (pullback.fst g j).opensRange = Y.basicOpen (g.appTop f) := by
  rw [Scheme.Hom.opensRange_pullbackFst, hj, Scheme.preimage_basicOpen_top]

/-- A monomorphism `j : U ⟶ X` with `j^* f` a unit through which `X.basicOpen f` factors is
isomorphic to `X.basicOpen f` over `X`. -/
theorem exists_iso_basicOpen_of_mono {j : U ⟶ X} [Mono j] (hj : IsUnit (j.appTop f))
    {a : (X.basicOpen f).toScheme ⟶ U} (ha : a ≫ j = (X.basicOpen f).ι) :
    ∃ e : U ≅ (X.basicOpen f).toScheme, e.hom ≫ (X.basicOpen f).ι = j := by
  have hr : Set.range j ⊆ Set.range (X.basicOpen f).ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_subset_basicOpen_iff j).2 hj
  have hb : IsOpenImmersion.lift _ j hr ≫ (X.basicOpen f).ι = j := IsOpenImmersion.lift_fac _ _ _
  exact ⟨⟨IsOpenImmersion.lift _ j hr, a,
    by rw [← cancel_mono j, Category.assoc, ha, hb, Category.id_comp],
    by rw [← cancel_mono (X.basicOpen f).ι, Category.assoc, hb, ha, Category.id_comp]⟩, hb⟩

/-- A monomorphism `j : U ⟶ X` with `j^* f` a unit through which `X.basicOpen f` factors is an open
immersion. -/
theorem isOpenImmersion_of_mono {j : U ⟶ X} [Mono j] (hj : IsUnit (j.appTop f))
    {a : (X.basicOpen f).toScheme ⟶ U} (ha : a ≫ j = (X.basicOpen f).ι) : IsOpenImmersion j := by
  obtain ⟨e, rfl⟩ := exists_iso_basicOpen_of_mono hj ha
  infer_instance

/-- A monomorphism `j : U ⟶ X` with `j^* f` a unit through which `X.basicOpen f` factors is an open
immersion onto `X.basicOpen f`. -/
theorem opensRange_eq_of_mono {j : U ⟶ X} [Mono j] [IsOpenImmersion j] (hj : IsUnit (j.appTop f))
    {a : (X.basicOpen f).toScheme ⟶ U} (ha : a ≫ j = (X.basicOpen f).ι) :
    j.opensRange = X.basicOpen f := by
  obtain ⟨e, rfl⟩ := exists_iso_basicOpen_of_mono hj ha
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Opens.opensRange_ι _)

end Open

/-! ### Unit multiples and regularity -/

section Regular

variable {X W : Scheme.{u}}

/-- Restricting twice is restricting once. -/
lemma presheaf_map_presheaf_map {U V V' : X.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Unit multiples generate the same ideal sheaf. -/
lemma principalIdealSheaf_eq_of_associated {a b : Γ(X, ⊤)} (h : Associated a b) :
    principalIdealSheaf a = principalIdealSheaf b := by
  obtain ⟨u, rfl⟩ := h
  ext U : 2
  rw [principalIdealSheaf_ideal, principalIdealSheaf_ideal, map_mul]
  exact (Ideal.span_singleton_mul_right_unit (u.isUnit.map _) _).symm

/-- Unit multiples have the same basic open. -/
lemma basicOpen_eq_of_associated {a b : Γ(X, ⊤)} (h : Associated a b) :
    X.basicOpen a = X.basicOpen b := by
  obtain ⟨u, rfl⟩ := h
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit u.isUnit, inf_top_eq]

/-- A unit multiple of a regular section is regular. -/
lemma IsRegularSection.of_associated {a b : Γ(X, ⊤)} (h : Associated a b)
    (hb : IsRegularSection b) : IsRegularSection a := by
  obtain ⟨u, rfl⟩ := h.symm
  intro U
  rw [map_mul]
  exact mul_mem_nonZeroDivisors.2 ⟨hb U, (u.isUnit.map _).mem_nonZeroDivisors⟩

/-- If `b` is regular and `a 𝒪_X = b 𝒪_X`, then `a` is a unit multiple of `b`. On each affine open
`a = c b` and `b = d a` for local functions `c` and `d`, so `(1 - d c) b = 0`, and regularity of
`b` gives `d c = 1`. The local ratios `c` are unique for the same reason, so they glue to a global
unit. The global statement needs this gluing on a non-affine `X`.

Blueprint: `thm:geo-cartesian`. -/
theorem associated_of_principalIdealSheaf_eq {a b : Γ(X, ⊤)} (hb : IsRegularSection b)
    (h : principalIdealSheaf a = principalIdealSheaf b) : Associated a b := by
  let res : ∀ U : X.Opens, Γ(X, ⊤) →+* Γ(X, U) := fun U ↦ (X.presheaf.map (homOfLE le_top).op).hom
  have hab (U : X.affineOpens) : res U a ∈ Ideal.span {res U b} := by
    rw [← principalIdealSheaf_ideal, ← h, principalIdealSheaf_ideal]
    exact Ideal.subset_span rfl
  have hba (U : X.affineOpens) : res U b ∈ Ideal.span {res U a} := by
    rw [← principalIdealSheaf_ideal, h, principalIdealSheaf_ideal]
    exact Ideal.subset_span rfl
  choose c hc using fun U : X.affineOpens ↦ Ideal.mem_span_singleton'.1 (hab U)
  -- the ratio `c U` is the unique function with `c U * b = a` on `U`
  have huniq (V : X.Opens) (t x y : Γ(X, V)) (hx : x * res V b = t)
      (hy : y * res V b = t) : x = y := by
    rw [← sub_eq_zero]
    apply mem_nonZeroDivisors_iff_right.1 (hb V)
    rw [sub_mul, hx, hy, sub_self]
  have hres (V V' : X.Opens) (hle : V' ≤ V) (s : Γ(X, ⊤)) :
      X.presheaf.map (homOfLE hle).op (res V s) = res V' s :=
    presheaf_map_presheaf_map _ _ s
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun U : X.affineOpens ↦ U.1) c := by
    intro U V
    change X.presheaf.map (homOfLE inf_le_left).op (c U) =
      X.presheaf.map (homOfLE inf_le_right).op (c V)
    apply huniq (U.1 ⊓ V.1) (res _ a)
    · rw [← hres U.1 _ inf_le_left, ← hres U.1 _ inf_le_left a, ← map_mul, hc]
    · rw [← hres V.1 _ inf_le_right, ← hres V.1 _ inf_le_right a, ← map_mul, hc]
  obtain ⟨α₀, hα, -⟩ := X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.1) ⊤
    (fun U ↦ homOfLE le_top) (iSup_affineOpens_eq_top X).ge c hcompat
  let α : Γ(X, ⊤) := α₀
  have hαU (U : X.affineOpens) : res U α = c U := hα U
  have hcunit (U : X.affineOpens) : IsUnit (c U) := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (hba U)
    refine IsUnit.of_mul_eq_one d ?_
    apply huniq U.1 (res U b) _ _ _ (one_mul _)
    rw [mul_comm (c U), mul_assoc, hc, hd]
  have hαunit : IsUnit α := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ α fun x _ ↦ ?_
    obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.1 :=
      Opens.mem_iSup.1 ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    have := (hcunit U).map (X.presheaf.germ U.1 x hxU).hom
    rwa [← hαU, X.presheaf.germ_res_apply] at this
  have hmul : α * b = a := by
    apply X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens ↦ U.1) ⊤
      (fun U ↦ homOfLE le_top) (iSup_affineOpens_eq_top X).ge
    intro U
    change res U (α * b) = res U a
    rw [map_mul, hαU, hc]
  obtain ⟨u, hu⟩ := hαunit
  refine ⟨u⁻¹, ?_⟩
  rw [← hmul, ← hu, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- For a regular `b`, the ideal sheaves `a 𝒪_X` and `b 𝒪_X` agree exactly when `a` is a unit
multiple of `b`. Equality of the underlying closed sets would not suffice.

Blueprint: `thm:geo-cartesian`. -/
theorem associated_iff_principalIdealSheaf_eq {a b : Γ(X, ⊤)} (hb : IsRegularSection b) :
    Associated a b ↔ principalIdealSheaf a = principalIdealSheaf b :=
  ⟨principalIdealSheaf_eq_of_associated, associated_of_principalIdealSheaf_eq hb⟩

/-- Regularity is local: a global function is regular if every point lies in the image of an open
immersion along which it pulls back to a regular function. -/
theorem IsRegularSection.of_isOpenImmersion_cover {f : Γ(X, ⊤)}
    (h : ∀ x : X, ∃ (W : Scheme.{u}) (e : W ⟶ X) (_ : IsOpenImmersion e),
      x ∈ Set.range e ∧ IsRegularSection (e.appTop f)) :
    IsRegularSection f := by
  intro U
  rw [mem_nonZeroDivisors_iff_right]
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf U s 0
  intro x hx
  obtain ⟨W, e, _, ⟨w, rfl⟩, hreg⟩ := h x
  change X.presheaf.germ U (e w) hx s = X.presheaf.germ U (e w) hx 0
  apply (ConcreteCategory.bijective_of_isIso (e.stalkMap w)).1
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, map_zero, map_zero]
  have hnat : e.app U (X.presheaf.map (homOfLE le_top).op f) =
      W.presheaf.map (homOfLE le_top).op (e.appTop f) :=
    (ConcreteCategory.congr_hom (e.naturality (homOfLE (le_top : U ≤ ⊤)).op) f).trans rfl
  have : e.app U s = 0 := by
    apply mem_nonZeroDivisors_iff_right.1 (hreg (e ⁻¹ᵁ U))
    rw [← hnat, ← map_mul, hs, map_zero]
  rw [this, map_zero]

/-- Regularity can be checked after pulling back along an isomorphism. -/
lemma IsRegularSection.of_isIso {f : Γ(X, ⊤)} (e : W ⟶ X) [IsIso e]
    (h : IsRegularSection (e.appTop f)) : IsRegularSection f :=
  .of_isOpenImmersion_cover fun x ↦ ⟨W, e, inferInstance, e.surjective x, h⟩

end Regular

/-! ### Affine schemes: from geometric to algebraic certificates -/

section ToAffine

variable {X U : Scheme.{u}} [IsAffine X] {f : Γ(X, ⊤)}

/-- An open immersion onto `X.basicOpen f` has the same image as the inclusion of that open. -/
lemma range_eq_range_ι_of_opensRange_eq {X U : Scheme.{u}} {f : Γ(X, ⊤)} {j : U ⟶ X}
    [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen f) :
    Set.range j = Set.range (X.basicOpen f).ι := by
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, hj]

/-- An open immersion onto a basic open of an affine scheme has affine source. -/
lemma isAffine_of_opensRange_eq {j : U ⟶ X} [IsOpenImmersion j]
    (hj : j.opensRange = X.basicOpen f) : IsAffine U := by
  have : IsAffine (X.basicOpen f).toScheme := (isAffineOpen_top X).basicOpen f
  exact .of_isIso (IsOpenImmersion.isoOfRangeEq j (X.basicOpen f).ι
    (range_eq_range_ι_of_opensRange_eq hj)).hom

/-- On an affine `X`, an open immersion `j : U ⟶ X` onto `X.basicOpen f` makes `Γ(U, 𝒪)`, through
`j^*`, the localization of `Γ(X, 𝒪)` away from `f`. This translates the open certificate of a
geometric pair into the localization certificate of an algebraic pair. -/
theorem isLocalization_appTop_of_opensRange_eq {j : U ⟶ X} [IsOpenImmersion j]
    (hj : j.opensRange = X.basicOpen f) :
    letI := j.appTop.hom.toAlgebra
    IsLocalization.Away f Γ(U, ⊤) := by
  let e := IsOpenImmersion.isoOfRangeEq j (X.basicOpen f).ι
    (range_eq_range_ι_of_opensRange_eq hj)
  let r : Γ((X.basicOpen f).toScheme, ⊤) ≃+* Γ(U, ⊤) :=
    (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  have key : r.toRingHom.comp (algebraMap Γ(X, ⊤) Γ((X.basicOpen f).toScheme, ⊤)) =
      j.appTop.hom := by
    rw [← IsOpenImmersion.isoOfRangeEq_hom_fac j (X.basicOpen f).ι
      (range_eq_range_ι_of_opensRange_eq hj), Scheme.Hom.comp_appTop]
    rfl
  rw [← key]
  exact (IsLocalization.isLocalization_iff_of_ringEquiv _ r).1 inferInstance

end ToAffine

/-! ### Spectra: from algebraic to geometric certificates -/

section Spec

variable {R S : CommRingCat.{u}}

/-- A ring isomorphism preserves and reflects non-zero-divisors. -/
lemma ringEquiv_mem_nonZeroDivisors_iff {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {x : A} : e x ∈ nonZeroDivisors B ↔ x ∈ nonZeroDivisors A := by
  rw [← MulEquivClass.map_nonZeroDivisors e, Submonoid.mem_map]
  exact ⟨fun ⟨y, hy, hyx⟩ ↦ e.injective hyx ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩

/-- `Spec` of a ring map `φ : R ⟶ S` with kernel `(f)` has kernel the ideal sheaf of `f`. -/
theorem ker_specMap_of_ker_eq (φ : R ⟶ S) {f : R} (h : RingHom.ker φ.hom = Ideal.span {f}) :
    (Spec.map φ).ker = principalIdealSheaf ((Scheme.ΓSpecIso R).inv f) := by
  rw [ker_eq_principalIdealSheaf_iff]
  ext x
  have hx : (Spec.map φ).appTop x = (Scheme.ΓSpecIso S).inv (φ ((Scheme.ΓSpecIso R).hom x)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Category.assoc,
      ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinv (y : S) : (Scheme.ΓSpecIso S).inv y = 0 ↔ y = 0 :=
    ⟨fun hy ↦ by simpa using congrArg (Scheme.ΓSpecIso S).hom hy, fun hy ↦ by rw [hy, map_zero]⟩
  rw [RingHom.mem_ker, hx, hinv, ← RingHom.mem_ker, h, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · intro hd
    have := map_dvd (Scheme.ΓSpecIso R).inv.hom hd
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
  · intro hd
    have := map_dvd (Scheme.ΓSpecIso R).hom.hom hd
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at this

/-- `Spec` of a localization `R → S` away from `f` is an open immersion. -/
theorem isOpenImmersion_specMap_of_isLocalization (φ : R ⟶ S) (f : R)
    (h : letI := φ.hom.toAlgebra; IsLocalization.Away f S) : IsOpenImmersion (Spec.map φ) := by
  let := φ.hom.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := R) (S := S) f

/-- `Spec` of a localization `R → S` away from `f` is an open immersion onto the basic open of
`f`. -/
theorem opensRange_specMap_of_isLocalization (φ : R ⟶ S) (f : R)
    (h : letI := φ.hom.toAlgebra; IsLocalization.Away f S) :
    letI := isOpenImmersion_specMap_of_isLocalization φ f h
    (Spec.map φ).opensRange = (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) := by
  let := φ.hom.toAlgebra
  rw [basicOpen_eq_of_affine]
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range S f)

/-- A function on `Spec R` is regular exactly when it is a non-zero-divisor of `R`. -/
theorem isRegularSection_ΓSpecIso_inv_iff (f : R) :
    IsRegularSection ((Scheme.ΓSpecIso R).inv f) ↔ f ∈ nonZeroDivisors R := by
  rw [isRegularSection_iff]
  exact ringEquiv_mem_nonZeroDivisors_iff (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm

end Spec

end OrlikSolomon.Geometric
