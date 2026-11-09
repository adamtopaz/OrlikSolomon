/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import OrlikSolomon.Geometry.Projective

/-!
# The projective complement as an open subscheme of `Proj`

This file identifies the ring `O(U_P)` of `OrlikSolomon/Geometry/Projective.lean` with the actual
complement of the hyperplanes of `P` in the projective space `Proj Sym(W*)`, using Mathlib's scheme
`Proj`.

## Main definitions

* `ProjectiveArrangement.complementOpen P`: the open subscheme of `Proj Sym(W*)` of the points on no
  hyperplane of `P`, by `mem_complementOpen_iff`.
* `ProjectiveArrangement.complementOpenIso P`: for nonempty `P`, this open subscheme is the spectrum
  of `O(U_P)`.
* `ProjectiveArrangement.complementι P`: the open immersion `Spec O(U_P) → Proj Sym(W*)`, with image
  `complementOpen P`, by `opensRange_complementι`.
* `ProjectiveArrangement.ComplementRing.awayEquiv`: for any equations `F H` of the hyperplanes of
  `P`, the ring `O(U_P)` is Mathlib's homogeneous localization `Away 𝒜 (∏ H, F H)`, the ring of
  degree-zero fractions with denominators a power of the product.
* `OrlikSolomon.projIsoMvPolynomial`: in a basis of `W*`, the scheme `Proj Sym(W*)` is
  `Proj k[x_i]`.

## Main results

* `OrlikSolomon.mapId_bijective_of_forall_exists_mul_mem`: a homogeneous localization does not
  change when the denominators are enlarged to elements that homogeneously divide the old
  denominators.
* `ProjectiveArrangement.complementOpen_eq_iInf`, `complementOpen_eq_iInf_basicOpen`: the
  complement is the intersection of the charts `D₊(ℓ)` of the equations, which depend only on the
  hyperplanes (`basicOpen_coord_eq_of_ker_eq`). It is `⊤` for empty `P` (`complementOpen_eq_top`).
* `ProjectiveArrangement.complementι_eq_awayι_of_ker_eq`: the open immersion of the complement,
  and so `complementOpenIso`, do not depend on the equations chosen to define them.

## Implementation notes

The proof of the structure theorem does not use schemes, and none of its modules may import this
file. It is what makes the statement of the theorem recognizable. The scheme layer of the geometric
refactor builds on it: `OrlikSolomon/Geometry/Schemes/Projective.lean` makes the complement a scheme
over `Spec k`. Mathlib has no projective
space as a named scheme, so `Proj Sym(W*)` is the definition of the projectivization of `W`, and
`projIsoMvPolynomial` relates it to the polynomial ring in a basis.

## Blueprint

The identification of the object of `def:projective` with the complement in `P^n` that the blueprint
means. The blueprint itself does not spell it out, as it works only with the decone. The first
sentence of the proof of `lem:decone` is `complementOpen_le_basicOpen`. The lemmas on the
intersection of charts and their independence of equations are part of `def:geo-projective` of the
geometric refactor blueprint.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization

universe u

namespace OrlikSolomon

open CoordinateRing

section MapId

variable {ι A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι]
variable [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {S T : Submonoid A}

/-- A homogeneous localization does not change when its denominators `S` are enlarged to a submonoid
`T` of non-zero-divisors, as long as each `t ∈ T` multiplies into `S` by a homogeneous element. -/
theorem mapId_bijective_of_forall_exists_mul_mem (h : S ≤ T) (hT : T ≤ nonZeroDivisors A)
    (hdvd : ∀ t ∈ T, ∃ (i : ι) (c : A), c ∈ 𝒜 i ∧ t * c ∈ S) :
    Function.Bijective (mapId 𝒜 h) := by
  have key (c : NumDenSameDeg 𝒜 S) : (mapId 𝒜 h (HomogeneousLocalization.mk c)).val =
      Localization.mk (c.num : A) ⟨c.den, h c.den_mem⟩ := rfl
  constructor
  · intro x y hxy
    obtain ⟨⟨m, a, b, hb⟩, rfl⟩ := mk_surjective x
    obtain ⟨⟨n, c, d, hd⟩, rfl⟩ := mk_surjective y
    have hval := congrArg val hxy
    rw [key, key, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
    obtain ⟨t, ht⟩ := hval
    have ht' := (mul_cancel_left_mem_nonZeroDivisors (hT t.2)).1 ht
    refine val_injective _ ?_
    simp only [val_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, congrArg _ ht'⟩
  · intro z
    obtain ⟨⟨n, a, b, hb⟩, rfl⟩ := mk_surjective z
    obtain ⟨i, c, hc, hbc⟩ := hdvd _ hb
    refine ⟨mk ⟨n + i, ⟨a * c, SetLike.mul_mem_graded a.2 hc⟩,
      ⟨b * c, SetLike.mul_mem_graded b.2 hc⟩, hbc⟩, val_injective _ ?_⟩
    rw [key, val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [mul_comm, mul_left_comm]⟩

/-- Mapping `A_{(f)}` to `A_{(fg)}`, sending `a / f ^ n` to `a g ^ n / (f g) ^ n`, and then to the
homogeneous localization at `T`, is the inclusion of `A_{(f)}`. -/
theorem mapId_comp_awayMap {f g : A} {d e : ι} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfT : Submonoid.powers f ≤ T) (hT : Submonoid.powers (f * g) ≤ T) :
    (mapId 𝒜 hT).comp (awayMap 𝒜 hg rfl) = mapId 𝒜 hfT := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hf z
  rw [RingHom.comp_apply, awayMap_mk]
  have h₁ : (mapId 𝒜 hT (Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (a * g ^ n)
      (by rw [smul_add]; exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg)))).val =
      Localization.mk (a * g ^ n) ⟨(f * g) ^ n, hT ⟨n, rfl⟩⟩ := rfl
  have h₂ : (mapId 𝒜 hfT (Away.mk 𝒜 hf n a ha)).val = Localization.mk a ⟨f ^ n, hfT ⟨n, rfl⟩⟩ :=
    rfl
  rw [h₁, h₂, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, mul_pow]; ring⟩

/-- `mapId_comp_awayMap` for a product `x = f * g` that is only propositionally equal to `f * g`,
such as a product over a finite set from which `f` is split off. -/
theorem mapId_comp_awayMap_of_eq {f g x : A} {d e : ι} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hx : x = f * g) (hfT : Submonoid.powers f ≤ T) (hT : Submonoid.powers x ≤ T) :
    (mapId 𝒜 hT).comp (awayMap 𝒜 hg hx) = mapId 𝒜 hfT := by
  subst hx
  exact mapId_comp_awayMap 𝒜 hf hg hfT hT

end MapId

section GradedIso

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded map with a graded section carries the irrelevant ideal onto the irrelevant ideal. -/
theorem irrelevant_le_map_of_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (h : f.comp g = .id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := fun b hb ↦ by
  have hg : g b ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      ← map_directSumDecompose ℬ 𝒜 g]
    have hb' : (DirectSum.decompose ℬ b 0 : B) = 0 := by
      simpa [GradedRing.proj_apply] using hb
    rw [hb', map_zero]
  have hfg : f (g b) = b := GradedRingHom.congr_fun h b
  rw [← hfg]
  exact Ideal.mem_map_of_mem _ hg

/-- A graded endomorphism equal to the identity induces the identity of `Proj`. -/
theorem proj_map_eq_id {f : 𝒜 →+*ᵍ 𝒜} (h : f = .id 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- An isomorphism of graded rings induces an isomorphism of their `Proj`. -/
def projIsoOfGraded (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : f.comp g = .id ℬ)
    (hgf : g.comp f = .id 𝒜) : Proj ℬ ≅ Proj 𝒜 where
  hom := Proj.map f (irrelevant_le_map_of_comp_eq_id f g hfg)
  inv := Proj.map g (irrelevant_le_map_of_comp_eq_id g f hgf)
  hom_inv_id := by
    rw [← Proj.map_comp, proj_map_eq_id hfg]
  inv_hom_id := by
    rw [← Proj.map_comp, proj_map_eq_id hgf]

end GradedIso

section StructureMap

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

set_option backward.isDefEq.respectTransparency false in
/-- A graded map of graded `R`-algebras that is the identity on `R` induces a map of `Proj` over
`Spec R`: the structure maps `Proj → Spec R`, through the degree-zero parts, are compatible. -/
theorem proj_map_toSpecZero_algebraMap (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))) =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ℬ 0))) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change (HomogeneousLocalization.mk _).val = (HomogeneousLocalization.mk _).val
  simp only [HomogeneousLocalization.val_mk]
  change Localization.mk (f (algebraMap R A r)) _ = Localization.mk (algebraMap R B r) _
  simp [hfR]

end StructureMap

section Charts

/-- Restricting a global function along `g` from the open `⊤` to `⊤` is pulling it back. -/
theorem appLE_top_eq_appTop {X Y : Scheme.{u}} (g : X ⟶ Y) (e : ⊤ ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ e = g.appTop :=
  g.appLE_eq_app (U := ⊤)

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
variable [GradedRing 𝒜] {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

/-- The chart `Spec (A_f)₀ → Proj A` lands in `D₊(f)`. -/
theorem top_le_awayι_preimage_basicOpen :
    ⊤ ≤ Proj.awayι 𝒜 f f_deg hm ⁻¹ᵁ Proj.basicOpen 𝒜 f := by
  rw [← Proj.opensRange_awayι 𝒜 f f_deg hm, Scheme.Hom.preimage_opensRange]

set_option backward.isDefEq.respectTransparency false in
private theorem awayToSection_appLE_of_eq {g : Spec (.of (Away 𝒜 f)) ⟶ Proj 𝒜}
    (hg : (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι = g)
    (h : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    Proj.awayToSection 𝒜 f ≫ g.appLE (Proj.basicOpen 𝒜 f) ⊤ h = (Scheme.ΓSpecIso _).inv := by
  subst hg
  have h₁ := Proj.basicOpenToSpec_app_top 𝒜 f
  rw [← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm] at h₁
  have h' : Proj.awayToSection 𝒜 f = (Scheme.ΓSpecIso _).inv ≫
      (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop ≫ (Proj.basicOpen 𝒜 f).topIso.hom := by
    rw [Scheme.Hom.appTop, h₁]
    simp
  rw [h']
  simp only [Category.assoc, Scheme.Hom.comp_appLE]
  have h₂ : (Proj.basicOpen 𝒜 f).topIso.hom ≫ (Proj.basicOpen 𝒜 f).ι.app (Proj.basicOpen 𝒜 f) =
      (Proj.basicOpen 𝒜 f).toScheme.presheaf.map (homOfLE le_top).op := by
    simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_app, ← Functor.map_comp]
    rfl
  rw [reassoc_of% h₂, Scheme.Hom.map_appLE, appLE_top_eq_appTop, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id]

/-- The chart `Spec (A_f)₀ → Proj A` pulls the section of `D₊(f)` given by a fraction `a / f ^ n`
back to the same fraction, as a function on `Spec (A_f)₀`. -/
theorem awayToSection_awayι_appLE :
    Proj.awayToSection 𝒜 f ≫ (Proj.awayι 𝒜 f f_deg hm).appLE (Proj.basicOpen 𝒜 f) ⊤
      (top_le_awayι_preimage_basicOpen f_deg hm) = (Scheme.ΓSpecIso _).inv :=
  awayToSection_appLE_of_eq f_deg hm rfl _

/-- If `g : Y → Proj A` factors through the chart `Spec (A_f)₀ → Proj A` as `β`, then `g` pulls
the section of `D₊(f)` given by a fraction back to the pullback along `β` of the same fraction. -/
theorem awayToSection_appLE_of_comp_eq {Y : Scheme.{u}} {g : Y ⟶ Proj 𝒜}
    {β : Y ⟶ Spec (.of (Away 𝒜 f))} (hβ : β ≫ Proj.awayι 𝒜 f f_deg hm = g)
    (h : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    Proj.awayToSection 𝒜 f ≫ g.appLE (Proj.basicOpen 𝒜 f) ⊤ h =
      (Scheme.ΓSpecIso _).inv ≫ β.appTop := by
  subst hβ
  have e := Scheme.Hom.appLE_comp_appLE β (Proj.awayι 𝒜 f f_deg hm) (Proj.basicOpen 𝒜 f) ⊤ ⊤
    (top_le_awayι_preimage_basicOpen f_deg hm) (Scheme.Hom.preimage_top β).ge
  rw [← e, reassoc_of% awayToSection_awayι_appLE, appLE_top_eq_appTop]

end Charts

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {ℓ : Dual k W}

/-- A linear form chosen for each hyperplane of `P`, whose kernel is that hyperplane. Everything
below is stated for all such forms, or does not depend on them. -/
def form (H : P) : Dual k W :=
  (exists_ker_eq H.2).choose

@[simp]
theorem ker_form (H : P) : LinearMap.ker (form H) = H :=
  (exists_ker_eq H.2).choose_spec

section Product

variable (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)

/-- A product of equations, one for each hyperplane of `P`, is homogeneous of degree the number of
hyperplanes. -/
theorem prod_coord_mem_symmetricGrading :
    ∏ H : P, coord (F H).toAffineMap ∈ symmetricGrading k (Dual k W) P.card := by
  have := SetLike.prod_mem_graded (A := symmetricGrading k (Dual k W)) (F := Finset.univ)
    (g := fun H : P ↦ coord (F H).toAffineMap) (i := fun _ ↦ 1)
    fun H _ ↦ coord_toAffineMap_mem (F H)
  simpa using this

include hF in
theorem prod_coord_mem_equationSubmonoid_cone :
    ∏ H : P, coord (F H).toAffineMap ∈ P.cone.equationSubmonoid :=
  Submonoid.prod_mem _ fun H _ ↦ coord_mem_equationSubmonoid_cone (by simp [hF])

include hF in
/-- The powers of a product of equations are products of equations. -/
theorem powers_prod_coord_le :
    Submonoid.powers (∏ H : P, coord (F H).toAffineMap) ≤ P.cone.equationSubmonoid :=
  Submonoid.powers_le.2 (prod_coord_mem_equationSubmonoid_cone F hF)

include hF in
/-- Every product of equations of hyperplanes of `P` multiplies by a homogeneous element into a
power of `∏ H, F H`. -/
theorem exists_mul_mem_powers_prod_coord {t : CoordinateRing k W}
    (ht : t ∈ P.cone.equationSubmonoid) :
    ∃ (i : ℕ) (c : CoordinateRing k W), c ∈ symmetricGrading k (Dual k W) i ∧
      t * c ∈ Submonoid.powers (∏ H : P, coord (F H).toAffineMap) := by
  classical
  refine forall_mem_equationSubmonoid_cone
    (p := fun t ↦ ∃ (i : ℕ) (c : CoordinateRing k W), c ∈ symmetricGrading k (Dual k W) i ∧
      t * c ∈ Submonoid.powers (∏ H : P, coord (F H).toAffineMap))
    ⟨0, 1, SetLike.GradedOne.one_mem, by simp⟩
    (fun x y ⟨i, c, hc, hxc⟩ ⟨j, d, hd, hyd⟩ ↦ ⟨i + j, c * d, SetLike.GradedMul.mul_mem hc hd, by
      rw [mul_mul_mul_comm]
      exact mul_mem hxc hyd⟩)
    (fun ℓ hℓ ↦ ?_) ht
  obtain ⟨u, hu⟩ := exists_eq_smul_of_ker_eq (hF ⟨_, hℓ⟩) (ne_zero_of_ker_mem hℓ)
  have hprod := SetLike.prod_mem_graded (symmetricGrading k (Dual k W))
    (F := Finset.univ.erase (⟨_, hℓ⟩ : P)) (fun _ ↦ 1) (fun H : P ↦ coord (F H).toAffineMap)
    fun H _ ↦ coord_toAffineMap_mem (F H)
  refine ⟨_, _, (symmetricGrading k (Dual k W) _).smul_mem (u : k) hprod, ⟨1, ?_⟩⟩
  beta_reduce
  rw [pow_one, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨_, hℓ⟩ : P)), hu,
    coord_toAffineMap, coord_toAffineMap, map_smul, smul_mul_assoc, mul_smul_comm]

end Product

/-- The powers of an equation of a hyperplane of `P` are products of equations. -/
theorem powers_coord_le (hℓ : LinearMap.ker ℓ ∈ P) :
    Submonoid.powers (coord ℓ.toAffineMap) ≤ P.cone.equationSubmonoid :=
  Submonoid.powers_le.2 (coord_mem_equationSubmonoid_cone hℓ)

/-! ### The comparison with `Away` -/

namespace ComplementRing

section Away

variable (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)

/-- For any equations `F H` of the hyperplanes of `P`, the ring `O(U_P)` is Mathlib's homogeneous
localization `Away` of their product, which is the ring of the chart `D₊(∏ H, F H)` of `Proj`.
Allowing denominators in all equations rather than in powers of one product is what makes the
definition of `O(U_P)` free of choices.

Blueprint: `def:projective`. -/
def awayEquiv :
    Away (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap) ≃+* P.ComplementRing :=
  RingEquiv.ofBijective (mapId (symmetricGrading k (Dual k W)) (powers_prod_coord_le F hF))
    (mapId_bijective_of_forall_exists_mul_mem _ _
      (Arrangement.equationSubmonoid_le_nonZeroDivisors)
      fun _ ht ↦ exists_mul_mem_powers_prod_coord F hF ht)

/-- The comparison with `Away` sends the fraction `a / f ^ n` to the fraction `a / f ^ n`. -/
theorem awayEquiv_mk {n : ℕ} {a : CoordinateRing k W}
    (ha : a ∈ symmetricGrading k (Dual k W) (n • P.card)) :
    awayEquiv F hF (Away.mk _ (prod_coord_mem_symmetricGrading F) n a ha) =
      mk ha (SetLike.pow_mem_graded n (prod_coord_mem_symmetricGrading F))
        (pow_mem (prod_coord_mem_equationSubmonoid_cone F hF) n) :=
  rfl

end Away

/-- The inclusion into `O(U_P)` of the ring `(Sym(W*)_ℓ)₀` of the chart `D₊(ℓ)`, for an equation `ℓ`
of a hyperplane of `P`: a fraction whose denominator is a power of `ℓ` is a fraction whose
denominator is a product of equations. -/
def fromAway (hℓ : LinearMap.ker ℓ ∈ P) :
    Away (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) →+* P.ComplementRing :=
  mapId (symmetricGrading k (Dual k W)) (powers_coord_le hℓ)

/-- The ratio `ξ / ℓ` is the image of the fraction `ξ / ℓ` of the chart `D₊(ℓ)`. -/
theorem ratio_eq_fromAway (ξ : Dual k W) (hℓ : LinearMap.ker ℓ ∈ P) :
    ratio ξ hℓ = fromAway hℓ (Away.mk _ (coord_toAffineMap_mem ℓ) 1 (coord ξ.toAffineMap)
      (by simpa using coord_toAffineMap_mem ξ)) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mk _).val = (HomogeneousLocalization.mk _).val
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  ext
  simp

end ComplementRing

/-! ### The complement in `Proj` -/

section Proj

variable (P)

/-- The product of the chosen equations of the hyperplanes of `P`. It unfolds at implicit
transparency, so that `Away 𝒜 (formProduct P)`, the ring of the chart `complementOpen P`, is the
ring `Away 𝒜 (∏ H, form H)` of `ComplementRing.awayEquiv` when Lean checks the types of
composites. -/
@[implicit_reducible]
def formProduct : CoordinateRing k W :=
  ∏ H : P, coord (form H).toAffineMap

/-- The product of the chosen equations is homogeneous of degree the number of hyperplanes. -/
theorem formProduct_mem_symmetricGrading :
    formProduct P ∈ symmetricGrading k (Dual k W) P.card :=
  prod_coord_mem_symmetricGrading form

/-- The complement of the hyperplanes of `P` in the projective space `Proj Sym(W*)`, as an open
subscheme. It is the set of points that are on no hyperplane of `P`, by `mem_complementOpen_iff`,
which does not depend on a choice of equations.

Blueprint: `def:projective`. -/
def complementOpen : (Proj (symmetricGrading k (Dual k W))).Opens :=
  Proj.basicOpen (symmetricGrading k (Dual k W)) (formProduct P)

variable {P}

/-- A point of `Proj Sym(W*)` is off the zero locus of a product of equations of the hyperplanes of
`P` exactly when it is off the zero locus of each equation of each hyperplane. -/
theorem prod_coord_notMem_iff (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)
    (x : Proj (symmetricGrading k (Dual k W))) :
    ∏ H : P, coord (F H).toAffineMap ∉ x.asHomogeneousIdeal ↔
      ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal := by
  have hprime : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  change ∏ H : P, coord (F H).toAffineMap ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal.toIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  constructor
  · intro h ℓ hℓ hmem
    obtain ⟨u, hu⟩ := exists_eq_smul_of_ker_eq (hF ⟨_, hℓ⟩) (ne_zero_of_ker_mem hℓ)
    refine h ⟨⟨_, hℓ⟩, Finset.mem_univ _, ?_⟩
    rw [hu, coord_toAffineMap, map_smul, Algebra.smul_def, ← coord_toAffineMap]
    exact Ideal.mul_mem_left _ _ hmem
  · rintro h ⟨H, -, hH⟩
    exact h (F H) (by simp [hF]) hH

/-- A point of `Proj Sym(W*)` is in the complement exactly when no equation of a hyperplane of `P`
vanishes at it. -/
theorem mem_complementOpen_iff (x : Proj (symmetricGrading k (Dual k W))) :
    x ∈ complementOpen P ↔
      ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal :=
  prod_coord_notMem_iff form ker_form x

/-- The complement is also the chart of the product of any other equations. -/
theorem complementOpen_eq_basicOpen (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementOpen P = Proj.basicOpen (symmetricGrading k (Dual k W))
      (∏ H : P, coord (F H).toAffineMap) :=
  TopologicalSpace.Opens.ext <| Set.ext fun x ↦ by
    change x ∈ complementOpen P ↔ x ∈ Proj.basicOpen _ _
    rw [mem_complementOpen_iff, Proj.mem_basicOpen, prod_coord_notMem_iff F hF]

/-- Every point of the complement lies in the standard chart `ℓ₀ ≠ 0`, for an equation `ℓ₀` of any
hyperplane of `P`.

Blueprint: `lem:decone`. -/
theorem complementOpen_le_basicOpen {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    complementOpen P ≤
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ₀.toAffineMap) :=
  fun x hx ↦ (mem_complementOpen_iff x).1 hx ℓ₀ hℓ₀

/-- The chart `D₊(ℓ)` of a linear form depends only on its kernel. In particular, multiplying an
equation by a nonzero scalar does not change its chart.

Blueprint: `def:geo-projective`. -/
theorem basicOpen_coord_eq_of_ker_eq {ℓ ℓ' : Dual k W} (h : LinearMap.ker ℓ = LinearMap.ker ℓ')
    (hℓ' : ℓ' ≠ 0) :
    Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) =
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ'.toAffineMap) := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_ker_eq h hℓ'
  refine TopologicalSpace.Opens.ext <| Set.ext fun x ↦ ?_
  change x ∈ Proj.basicOpen _ _ ↔ x ∈ Proj.basicOpen _ _
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen, coord_toAffineMap, coord_toAffineMap, map_smul,
    Algebra.smul_def]
  exact not_congr (Ideal.unit_mul_mem_iff_mem x.asHomogeneousIdeal.toIdeal
    ((IsUnit.mk0 _ c.ne_zero).map _))

/-- The complement is the intersection of the charts `D₊(ℓ)` of all equations `ℓ` of all hyperplanes
of `P`. It is `⊤` for empty `P`, by `complementOpen_eq_top`.

Blueprint: `def:geo-projective`. -/
theorem complementOpen_eq_iInf :
    complementOpen P = ⨅ (ℓ : Dual k W) (_ : LinearMap.ker ℓ ∈ P),
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) :=
  le_antisymm (le_iInf₂ fun _ hℓ ↦ complementOpen_le_basicOpen hℓ) fun x hx ↦
    (mem_complementOpen_iff x).2 fun ℓ hℓ ↦ iInf₂_le (κ := fun ℓ : Dual k W ↦ LinearMap.ker ℓ ∈ P)
      (f := fun ℓ _ ↦ Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap)) ℓ hℓ hx

/-- The complement is the intersection of the charts of any choice of equations, one for each
hyperplane of `P`.

Blueprint: `def:geo-projective`. -/
theorem complementOpen_eq_iInf_basicOpen (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementOpen P =
      ⨅ H : P, Proj.basicOpen (symmetricGrading k (Dual k W)) (coord (F H).toAffineMap) := by
  rw [complementOpen_eq_iInf]
  refine le_antisymm (le_iInf fun H ↦ iInf₂_le (F H) (by rw [hF]; exact H.2))
    (le_iInf₂ fun ℓ hℓ ↦ ?_)
  rw [basicOpen_coord_eq_of_ker_eq (hF ⟨_, hℓ⟩).symm (ne_zero_of_ker_mem (by rwa [hF]))]
  exact iInf_le _ _

/-- The complement of the empty arrangement is all of `Proj Sym(W*)`.

Blueprint: `def:geo-projective`. -/
@[simp]
theorem complementOpen_eq_top [IsEmpty P] : complementOpen P = ⊤ := by
  rw [complementOpen_eq_iInf_basicOpen form ker_form, iInf_of_empty]

variable (P) [Nonempty P]

/-- For nonempty `P`, the complement of the hyperplanes of `P` in `Proj Sym(W*)` is the spectrum of
`O(U_P)`. In particular it is an affine scheme.

Blueprint: `def:projective`. -/
def complementOpenIso : (complementOpen P).toScheme ≅ Spec (.of P.ComplementRing) :=
  Proj.basicOpenIsoSpec (symmetricGrading k (Dual k W)) (formProduct P)
      (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P) ≪≫
    Scheme.Spec.mapIso (ComplementRing.awayEquiv (P := P) form ker_form).symm.toCommRingCatIso.op

/-- The ring `O(U_P)` is the ring of global functions on the complement in `Proj`. -/
def complementRingIso :
    .of P.ComplementRing ≅ Γ(Proj (symmetricGrading k (Dual k W)), complementOpen P) :=
  (ComplementRing.awayEquiv (P := P) form ker_form).symm.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway (symmetricGrading k (Dual k W)) (formProduct P)
      (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P)

/-- The open immersion `Spec O(U_P) → Proj Sym(W*)` of the complement. -/
def complementι : Spec (.of P.ComplementRing) ⟶ Proj (symmetricGrading k (Dual k W)) :=
  (complementOpenIso P).inv ≫ (complementOpen P).ι

instance : IsOpenImmersion (complementι P) :=
  IsOpenImmersion.comp _ _

/-- The open immersion of the complement is Mathlib's `Proj.awayι` for the chart `D₊(f)` of the
product `f` of equations, through the comparison of `O(U_P)` with `Away 𝒜 f`. -/
theorem complementι_eq_awayι :
    complementι P =
      Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv (P := P) form ker_form).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (formProduct P)
          (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P) :=
  rfl

variable {P} in
/-- For equations `F` and `G` of the hyperplanes of `P`, the chart of `∏ H, F H`, composed with the
comparison of `O(U_P)` with its ring, factors through the chart of `(∏ H, F H) * (∏ H, G H)`. -/
theorem specMap_awayEquiv_comp_awayι (F G : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)
    (hG : ∀ H : P, LinearMap.ker (G H) = H) :
    Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv F hF).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
          (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) (Submonoid.powers_le.2
          (mul_mem (prod_coord_mem_equationSubmonoid_cone F hF)
            (prod_coord_mem_equationSubmonoid_cone G hG))))) ≫
        Proj.awayι (symmetricGrading k (Dual k W))
          ((∏ H : P, coord (F H).toAffineMap) * ∏ H : P, coord (G H).toAffineMap)
          (SetLike.mul_mem_graded (prod_coord_mem_symmetricGrading F)
            (prod_coord_mem_symmetricGrading G))
          (Nat.add_pos_left (card_pos_of_nonempty P) _) := by
  rw [← Proj.SpecMap_awayMap_awayι (symmetricGrading k (Dual k W))
    (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P)
    (prod_coord_mem_symmetricGrading G) rfl, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    mapId_comp_awayMap _ (prod_coord_mem_symmetricGrading F) (prod_coord_mem_symmetricGrading G)
      (powers_prod_coord_le F hF)]
  rfl

omit [Nonempty P] in
/-- The chart of a product of equations, composed with an inclusion of degree-zero fractions, only
depends on the product through the open subscheme it cuts out. -/
private theorem specMap_mapId_comp_awayι_congr {x y : CoordinateRing k W} (hxy : x = y) {m : ℕ}
    (hx : x ∈ symmetricGrading k (Dual k W) m) (hy : y ∈ symmetricGrading k (Dual k W) m)
    (hm : 0 < m) (hSx : Submonoid.powers x ≤ P.cone.equationSubmonoid)
    (hSy : Submonoid.powers y ≤ P.cone.equationSubmonoid) :
    Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hSx)) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) x hx hm =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hSy)) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) y hy hm := by
  subst hxy
  rfl

/-- The open immersion of the complement does not depend on a choice of equations: for any
equations `F` of the hyperplanes of `P`, it is the chart `Proj.awayι` of `∏ H, F H`, through the
comparison of `O(U_P)` with its ring. So neither does `complementOpenIso`, since the open immersion
of `complementOpen P` is a monomorphism. -/
theorem complementι_eq_awayι_of_ker_eq (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementι P =
      Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv F hF).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
          (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) := by
  exact (specMap_awayEquiv_comp_awayι form F ker_form hF).trans
    ((specMap_mapId_comp_awayι_congr P (mul_comm _ _) _ _ _ _ _).trans
      (specMap_awayEquiv_comp_awayι F form hF ker_form).symm)

/-- The image of the open immersion `Spec O(U_P) → Proj Sym(W*)` is the complement of the
hyperplanes of `P`. -/
theorem opensRange_complementι : (complementι P).opensRange = complementOpen P :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (complementOpen P).opensRange_ι

/-- The open immersion of the complement factors through the chart `D₊(ℓ)` of any equation `ℓ` of a
hyperplane of `P`, by `Spec` of the inclusion `ComplementRing.fromAway` of the ring of the chart. -/
theorem complementι_eq_specMap_comp_awayι (hℓ : LinearMap.ker ℓ ∈ P) :
    complementι P =
      Spec.map (CommRingCat.ofHom (ComplementRing.fromAway (P := P) hℓ)) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap)
          (coord_toAffineMap_mem ℓ) one_pos := by
  classical
  let K : P := ⟨_, hℓ⟩
  let F : P → Dual k W := Function.update form K ℓ
  have hF : ∀ H : P, LinearMap.ker (F H) = H := fun H ↦ by
    by_cases hH : H = K
    · subst hH
      simp [F, K]
    · simp [F, hH]
  have hg := SetLike.prod_mem_graded (symmetricGrading k (Dual k W))
    (F := Finset.univ.erase K) (fun _ ↦ 1) (fun H : P ↦ coord (F H).toAffineMap)
    fun H _ ↦ coord_toAffineMap_mem (F H)
  have hx : ∏ H : P, coord (F H).toAffineMap =
      coord ℓ.toAffineMap * ∏ H ∈ Finset.univ.erase K, coord (F H).toAffineMap := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ K)]
    simp [F]
  -- The chart of the product does not depend on the degree in which it is taken.
  have e : Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
      (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) =
      Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
        (hx ▸ SetLike.mul_mem_graded (coord_toAffineMap_mem ℓ) hg)
        (one_pos.trans_le (Nat.le_add_right 1 _)) := rfl
  rw [complementι_eq_awayι_of_ker_eq P F hF, e, ← Proj.SpecMap_awayMap_awayι _
    (coord_toAffineMap_mem ℓ) one_pos hg hx, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ) ≫ _)
    (mapId_comp_awayMap_of_eq _ (coord_toAffineMap_mem ℓ) hg hx (powers_coord_le hℓ)
      (powers_prod_coord_le F hF))

omit [Nonempty P] in
/-- The complement lies in the chart `D₊(ℓ)` of every equation `ℓ` of a hyperplane of `P`. -/
theorem top_le_complementOpen_ι_preimage_basicOpen (hℓ : LinearMap.ker ℓ ∈ P) :
    ⊤ ≤ (complementOpen P).ι ⁻¹ᵁ
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) :=
  (Scheme.Opens.ι_preimage_self _).ge.trans
    (Scheme.Hom.preimage_mono _ (complementOpen_le_basicOpen hℓ))

/-- The function `ξ / ℓ` on the complement, pulled back along `complementOpenIso` from the element
`ComplementRing.ratio ξ hℓ` of `O(U_P)`, is the restriction to the complement of the section
`ξ / ℓ` of the chart `D₊(ℓ)` of `Proj Sym(W*)`. -/
theorem complementOpenIso_hom_appTop_ratio (ξ : Dual k W) (hℓ : LinearMap.ker ℓ ∈ P) :
    (complementOpenIso P).hom.appTop ((Scheme.ΓSpecIso (.of P.ComplementRing)).inv
        (ComplementRing.ratio ξ hℓ)) =
      (complementOpen P).ι.appLE
        (Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap)) ⊤
        (top_le_complementOpen_ι_preimage_basicOpen P hℓ)
        (Proj.awayToSection _ _ (Away.mk _ (coord_toAffineMap_mem ℓ) 1 (coord ξ.toAffineMap)
          (by simpa using coord_toAffineMap_mem ξ))) := by
  have hβ : ((complementOpenIso P).hom ≫ Spec.map (CommRingCat.ofHom
      (ComplementRing.fromAway (P := P) hℓ))) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap)
          (coord_toAffineMap_mem ℓ) one_pos = (complementOpen P).ι := by
    rw [Category.assoc, ← complementι_eq_specMap_comp_awayι P hℓ, complementι,
      Iso.hom_inv_id_assoc]
  symm
  rw [← CommRingCat.comp_apply, awayToSection_appLE_of_comp_eq _ one_pos hβ,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, ComplementRing.ratio_eq_fromAway]
  rfl

end Proj

end ProjectiveArrangement

/-! ### In a basis -/

section Basis

attribute [local instance] MvPolynomial.gradedAlgebra

variable {κ : Type*} (b : Basis κ k (Dual k W))

/-- A basis of `W*` identifies `Sym(W*)` with the polynomial ring, as graded rings. -/
def symmetricGradingToMvPolynomial :
    symmetricGrading k (Dual k W) →+*ᵍ MvPolynomial.homogeneousSubmodule κ k where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b : _ →+* MvPolynomial κ k)
  map_mem {n x} hx := by
    rw [← map_equivMvPolynomial_symmetricGrading b n]
    exact Submodule.mem_map_of_mem hx

/-- A basis of `W*` identifies the polynomial ring with `Sym(W*)`, as graded rings. -/
def mvPolynomialToSymmetricGrading :
    MvPolynomial.homogeneousSubmodule κ k →+*ᵍ symmetricGrading k (Dual k W) where
  toRingHom := ((SymmetricAlgebra.equivMvPolynomial b).symm : _ →+* SymmetricAlgebra k (Dual k W))
  map_mem {n x} hx := by
    rw [← map_equivMvPolynomial_symmetricGrading b n] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy

@[simp]
theorem symmetricGradingToMvPolynomial_apply (x : SymmetricAlgebra k (Dual k W)) :
    symmetricGradingToMvPolynomial b x = SymmetricAlgebra.equivMvPolynomial b x :=
  rfl

@[simp]
theorem mvPolynomialToSymmetricGrading_apply (x : MvPolynomial κ k) :
    mvPolynomialToSymmetricGrading b x = (SymmetricAlgebra.equivMvPolynomial b).symm x :=
  rfl

/-- `Proj Sym(W*)`, the projectivization of `W`, is the projective space `Proj k[x_i]` of the
polynomial ring in the variables given by a basis of `W*`, with its usual grading by total degree.
So `complementOpen P` is the complement of hyperplanes in projective space in the usual sense.

The index type `κ` lives in the universe of `k`, as `Proj` of a graded map needs both rings in one
universe; the graded maps above have no such restriction. -/
def projIsoMvPolynomial {κ : Type u} (b : Basis κ k (Dual k W)) :
    Proj (symmetricGrading k (Dual k W)) ≅ Proj (MvPolynomial.homogeneousSubmodule κ k) :=
  projIsoOfGraded (mvPolynomialToSymmetricGrading b) (symmetricGradingToMvPolynomial b)
    (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x)
    (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x)

end Basis

end OrlikSolomon
