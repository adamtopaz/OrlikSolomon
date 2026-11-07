/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Complement
public import OrlikSolomon.Geometry.Schemes.Complement.AffineSpace

/-!
# Arrangement complements as open subschemes

This file realizes `def:geo-complement` and `thm:geo-complement-spec` of the geometric refactor
blueprint. The complement `U_𝒜` of an arrangement is the open subscheme of `𝔸_V` on the
intersection of the complements of the supports of the hyperplane schemes `𝐇`, `H ∈ 𝒜`, with the
restricted structure sheaf. It is not a set of `k`-points, of which it may have none. It is
canonically isomorphic over `𝔸_V` to `Spec` of the existing ring `𝒜.ComplementRing`, by `s_𝒜`,
and this comparison is compatible with every map of complements of the existing theory.

## Main definitions

* `Geometric.hyperplaneComplement H`: the open complement of the support of `𝐇` in `𝔸_V`.
* `Geometric.complementOpens 𝒜`, `Geometric.complement 𝒜`, `Geometric.complementι 𝒜`: the open set
  of `U_𝒜`, the `S`-scheme `U_𝒜`, and the open immersion `j_𝒜 : U_𝒜 → 𝔸_V`.
* `Geometric.complementIsoSpec 𝒜`: the comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` over `𝔸_V`.
* `Geometric.complementUnit 𝒜 f hf`: the restriction `f̃|_{U_𝒜}` of the function of an affine
  function whose zero locus is covered by `𝒜`, as a global unit on `U_𝒜`.
* `Geometric.complementHom F`: the morphism of complements of a map `F` of the existing coordinate
  rings, `Spec F` under the comparisons.
* `Geometric.complementMap`, `Geometric.complementInclusion`, `Geometric.complementIso`: the maps of
  complements given by an affine map, by a sub-arrangement and by an affine equivalence.
* `SmoothDomain.complement D 𝒜`, `SmoothDomain.complementIsoSpec D 𝒜`: `U_𝒜` as an object of any
  admissible domain, and `s_𝒜` with target `D.spec (SmoothAlg.complement 𝒜)`, where an algebraic
  theory is evaluated; with `SmoothDomain.complementMap`, `SmoothDomain.complementInclusion` and
  `SmoothDomain.complementIso`.

## Main results

* `hyperplaneComplement_eq_basicOpen`, `complementOpens_eq_basicOpen`: the complement of `𝐇` is the
  basic open of `f̃` for every equation `f` of `H`, and `U_𝒜` is the basic open `D(F)` of every
  product `F` of equations, one for each hyperplane.
* `complementOpens_empty`: the complement of the empty arrangement is all of `𝔸_V`.
* `complementIsoSpec_hom_comp`: `s_𝒜` is a morphism over `𝔸_V`; it does not depend on equations,
  since `j_𝒜` is a monomorphism.
* `isLocalizationAway_complementι_appTop`: `Γ(U_𝒜) = Sym(V*)[1/F]` for every such `F`.
* `complementIsoSpec_hom_appTop_coord`: under `s_𝒜`, the image of an affine function in
  `O(U_𝒜)` is the restriction of its function, so each equation unit is the restricted function.
* `complementMap_comp_complementIsoSpec_hom`, `complementInclusion_comp_complementIsoSpec_hom`, and
  their forms in a domain: `s_𝒜` is natural for the existing `complementMap` and
  `complementInclusion`.

## Implementation notes

The maps of complements are `complementHom` of the existing ring maps, so one set of naturality
lemmas for `s` serves all of them, and they are characterized by their composite with `j_𝒜`
(`complementMap_comp_complementι`), which determines them. Lemmas on functions in a domain are
stated as equations of global sections, not of units, because `Γ((D.spec A).obj.left, ⊤)` and
`Γ((spec A.obj).left, ⊤)` agree only at implicit transparency; recover unit equations with
`Units.ext`. Named objects are `@[implicit_reducible] def`s, and equations between objects are not
`simp` lemmas. No `k`-point of any scheme is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace OrlikSolomon.Geometric

open CoordinateRing Arrangement Arrangement.ComplementRing

/-- The basic open of a finite product is the intersection of the basic opens. -/
lemma basicOpen_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, ⊤)) :
    X.basicOpen (∏ i ∈ s, f i) = ⨅ i ∈ s, X.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_of_isUnit]
  | insert a s ha ih => rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert]

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
variable {W : Type u} [AddCommGroup W] [Module k W] {U : Type u} [AddCommGroup U] [Module k U]

/-! ### Hyperplane complements -/

section HyperplaneComplement

variable {H : AffineSubspace k V} {f : V →ᵃ[k] k}

variable (H) in
/-- The open complement `𝔸_V ∖ |𝐇|` of the support of the hyperplane scheme.

Blueprint: `def:geo-complement`. -/
def hyperplaneComplement : (affineSpace k V).left.Opens :=
  ⟨(Set.range (hyperplaneι H).left)ᶜ,
    ((hyperplaneι H).left.isClosedEmbedding.isClosed_range).isOpen_compl⟩

lemma coe_hyperplaneComplement :
    (hyperplaneComplement H : Set (affineSpace k V).left) = (Set.range (hyperplaneι H).left)ᶜ :=
  rfl

/-- The complement of `𝐇` is the basic open of `f̃`, for every equation `f` of `H`.

Blueprint: `def:geo-complement`, `thm:geo-complement-spec`. -/
theorem hyperplaneComplement_eq_basicOpen (hf : IsEquation f H) :
    hyperplaneComplement H = (affineSpace k V).left.basicOpen (affineSpaceCoord f) := by
  apply Opens.ext
  change _ = ((Spec (.of (CoordinateRing k V))).basicOpen
    ((Scheme.ΓSpecIso (.of (CoordinateRing k V))).inv (coord f)) :
      Set (Spec (.of (CoordinateRing k V))))
  rw [coe_hyperplaneComplement, basicOpen_eq_of_affine]
  change (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (hyperplaneIdeal H))))ᶜ = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    hyperplaneIdeal_eq_span hf, PrimeSpectrum.zeroLocus_span]
  exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl _).symm

end HyperplaneComplement

/-! ### The complement -/

section Complement

variable (𝒜 : Arrangement k V) {ℬ : Arrangement k V} {f : V →ᵃ[k] k}

/-- The open set of `U_𝒜` in `𝔸_V`: the intersection of the complements of the supports of the
hyperplane schemes of `𝒜`. It is `⊤` for the empty arrangement.

Blueprint: `def:geo-complement`. -/
def complementOpens : (affineSpace k V).left.Opens :=
  ⨅ H : 𝒜, hyperplaneComplement (H : AffineSubspace k V)

variable {𝒜}

/-- `U_𝒜` is the basic open `D(F)` of `F = ∏_{H ∈ 𝒜} f̃_H`, for any equations `f_H`.

Blueprint: `thm:geo-complement-spec`. -/
theorem complementOpens_eq_basicOpen (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    complementOpens 𝒜 = (affineSpace k V).left.basicOpen (∏ H : 𝒜, affineSpaceCoord (F H)) := by
  rw [basicOpen_prod, complementOpens]
  simp only [Finset.mem_univ, iInf_true]
  exact iInf_congr fun H ↦ hyperplaneComplement_eq_basicOpen (hF H)

/-- The complement of the empty arrangement is all of `𝔸_V`.

Blueprint: `def:geo-complement`. -/
@[simp] theorem complementOpens_empty : complementOpens (∅ : Arrangement k V) = ⊤ :=
  iInf_of_empty _

variable (𝒜)

/-- The complement `U_𝒜` of an arrangement, as a scheme over `S = Spec k`: the open subscheme of
`𝔸_V` on `complementOpens 𝒜`, with the restricted structure sheaf. It is not a set of `k`-points:
over a finite field it can have none.

Blueprint: `def:geo-complement`. -/
@[implicit_reducible]
def complement : Over (Spec (.of k)) := Over.mk ((complementOpens 𝒜).ι ≫ (affineSpace k V).hom)

lemma complement_left : (complement 𝒜).left = (complementOpens 𝒜).toScheme := rfl

lemma complement_hom : (complement 𝒜).hom = (complementOpens 𝒜).ι ≫ (affineSpace k V).hom := rfl

/-- The open immersion `j_𝒜 : U_𝒜 → 𝔸_V`.

Blueprint: `def:geo-complement`. -/
def complementι : complement 𝒜 ⟶ affineSpace k V := Over.homMk (complementOpens 𝒜).ι rfl

@[simp] lemma complementι_left : (complementι 𝒜).left = (complementOpens 𝒜).ι := rfl

instance : IsOpenImmersion (complementι 𝒜).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

instance : Mono (complementι 𝒜) := Over.mono_homMk _

lemma opensRange_complementι : (complementι 𝒜).left.opensRange = complementOpens 𝒜 :=
  Scheme.Opens.opensRange_ι _

variable {𝒜}

/-- The image of `j_𝒜` is the basic open `D(F)` of any product `F` of equations.

Blueprint: `thm:geo-complement-spec`. -/
lemma opensRange_complementι_eq_basicOpen (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    (complementι 𝒜).left.opensRange =
      (affineSpace k V).left.basicOpen (∏ H : 𝒜, affineSpaceCoord (F H)) :=
  (opensRange_complementι 𝒜).trans (complementOpens_eq_basicOpen F hF)

/-- For the empty arrangement, `j_∅ : U_∅ → 𝔸_V` is an isomorphism.

Blueprint: `def:geo-complement`. -/
instance isIso_complementι_empty : IsIso (complementι (∅ : Arrangement k V)) := by
  have : IsIso ((Over.forget _).map (complementι (∅ : Arrangement k V))) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top (complementι (∅ : Arrangement k V)).left
      ((opensRange_complementι _).trans complementOpens_empty)
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- Morphisms into `U_𝒜` are determined by their composite with `j_𝒜`. -/
lemma hom_ext_complement {X : Over (Spec (.of k))} {g₁ g₂ : X ⟶ complement 𝒜}
    (h : g₁ ≫ complementι 𝒜 = g₂ ≫ complementι 𝒜) : g₁ = g₂ :=
  (cancel_mono _).1 h

end Complement

/-! ### The comparison `s_𝒜` -/

section Comparison

variable (𝒜 : Arrangement k V) {f : V →ᵃ[k] k}

/-- `O(U_𝒜)` is the localization of `O(V)` away from the product of the chosen equations, in the
form used by `Spec`. -/
lemma isLocalizationAway_toComplementRing :
    letI := (CommRingCat.ofHom (toComplementRing 𝒜).toRingHom).hom.toAlgebra
    IsLocalization.Away (∏ H : 𝒜, coord (equation (H : AffineSubspace k V))) 𝒜.ComplementRing :=
  have := isLocalizationAway (𝒜 := 𝒜) (fun H ↦ equation H)
    fun H ↦ isEquation_equation (𝒜.isHyperplane H.2)
  isLocalizationAway_toAlgebra rfl

/-- `Spec` of `O(V) → O(U_𝒜)` is an open immersion. -/
instance : IsOpenImmersion (specMap (CommAlgCat.ofHom (toComplementRing 𝒜))).left :=
  isOpenImmersion_specMap_of_isLocalization (CommRingCat.ofHom (toComplementRing 𝒜).toRingHom) _
    (isLocalizationAway_toComplementRing 𝒜)

/-- `U_𝒜` and `Spec O(U_𝒜)` have the same image in `𝔸_V`. -/
lemma range_complementOpens_ι :
    Set.range (complementOpens 𝒜).ι =
      Set.range (specMap (CommAlgCat.ofHom (toComplementRing 𝒜))).left := by
  have := isOpenImmersion_specMap_of_isLocalization
    (CommRingCat.ofHom (toComplementRing 𝒜).toRingHom) _ (isLocalizationAway_toComplementRing 𝒜)
  change _ = Set.range (Spec.map (CommRingCat.ofHom (toComplementRing 𝒜).toRingHom))
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
    opensRange_specMap_of_isLocalization _ _ (isLocalizationAway_toComplementRing 𝒜),
    complementOpens_eq_basicOpen (fun H ↦ equation H)
      fun H ↦ isEquation_equation (𝒜.isHyperplane H.2)]
  simp only [affineSpaceCoord, map_prod]
  rfl

/-- The canonical comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` of `S`-schemes, with the existing ring
`𝒜.ComplementRing`. It is a morphism over `𝔸_V` (`complementIsoSpec_hom_comp`), which determines
it, so it involves no choice of equations.

Blueprint: `thm:geo-complement-spec`. -/
def complementIsoSpec : complement 𝒜 ≅ spec (CommAlgCat.of k 𝒜.ComplementRing) :=
  Over.isoMk (IsOpenImmersion.isoOfRangeEq (complementOpens 𝒜).ι
      (specMap (CommAlgCat.ofHom (toComplementRing 𝒜))).left (range_complementOpens_ι 𝒜)) <| by
    rw [← specMap_w (CommAlgCat.ofHom (toComplementRing 𝒜)), ← specMap_left,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    rfl

/-- `s_𝒜` is a morphism over `𝔸_V`: followed by `Spec O(U_𝒜) → 𝔸_V` it is `j_𝒜`.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementIsoSpec_hom_comp :
    (complementIsoSpec 𝒜).hom ≫ specMap (CommAlgCat.ofHom (toComplementRing 𝒜)) =
      complementι 𝒜 :=
  Over.OverMorphism.ext (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (range_complementOpens_ι 𝒜))

@[reassoc (attr := simp)]
lemma complementIsoSpec_inv_comp_complementι :
    (complementIsoSpec 𝒜).inv ≫ complementι 𝒜 =
      specMap (CommAlgCat.ofHom (toComplementRing 𝒜)) := by
  rw [Iso.inv_comp_eq, complementIsoSpec_hom_comp]

instance : Mono (specMap (CommAlgCat.ofHom (toComplementRing 𝒜))) :=
  Over.mono_of_mono_left _

/-- `s_𝒜` is the only isomorphism `U_𝒜 ≅ Spec O(U_𝒜)` over `𝔸_V`, since `Spec O(U_𝒜) → 𝔸_V` is a
monomorphism. In particular it does not depend on a choice of equations.

Blueprint: `thm:geo-complement-spec`. -/
lemma eq_complementIsoSpec (e : complement 𝒜 ≅ spec (CommAlgCat.of k 𝒜.ComplementRing))
    (he : e.hom ≫ specMap (CommAlgCat.ofHom (toComplementRing 𝒜)) = complementι 𝒜) :
    e = complementIsoSpec 𝒜 :=
  Iso.ext ((cancel_mono _).1 (he.trans (complementIsoSpec_hom_comp 𝒜).symm))

/-- The complement is affine.

Blueprint: `thm:geo-complement-spec`. -/
instance isAffine_complement_left : IsAffine (complement 𝒜).left :=
  .of_isIso (complementIsoSpec 𝒜).hom.left

/-- The complement of an arrangement in a finite-dimensional space is smooth over `S`.

Blueprint: `thm:geo-complement-spec`. -/
instance smooth_complement_hom [FiniteDimensional k V] : Smooth (complement 𝒜).hom :=
  inferInstanceAs (Smooth ((complementOpens 𝒜).ι ≫ (affineSpace k V).hom))

/-- The ring of global functions of `U_𝒜` is the localization of `Sym(V*)` away from any product
`F` of equations, one for each hyperplane, through `j_𝒜^*`.

Blueprint: `thm:geo-complement-spec`. -/
theorem isLocalizationAway_complementι_appTop (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    letI := (complementι 𝒜).left.appTop.hom.toAlgebra
    IsLocalization.Away (∏ H : 𝒜, affineSpaceCoord (F H)) Γ((complement 𝒜).left, ⊤) :=
  isLocalization_appTop_of_opensRange_eq (opensRange_complementι_eq_basicOpen F hF)

variable {𝒜}

/-- Under `s_𝒜`, the image in `O(U_𝒜)` of a function on `𝔸_V` is the restriction of that function
to `U_𝒜`.

Blueprint: `thm:geo-complement-spec`. -/
lemma complementIsoSpec_hom_appTop_algebraMap (x : CoordinateRing k V) :
    (complementIsoSpec 𝒜).hom.left.appTop
        ((Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv (algebraMap _ _ x)) =
      (complementι 𝒜).left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing k V))).inv x) := by
  rw [← complementIsoSpec_hom_comp 𝒜, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, specMap_left_appTop_ΓSpecIso_inv]
  rfl

/-- Pulling back along `s_𝒜⁻¹` the restriction of a function on `𝔸_V` gives its image in `O(U_𝒜)`.

Blueprint: `thm:geo-complement-spec`. -/
lemma complementIsoSpec_inv_appTop_complementι_appTop (x : CoordinateRing k V) :
    (complementIsoSpec 𝒜).inv.left.appTop
        ((complementι 𝒜).left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing k V))).inv x)) =
      (Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv (algebraMap _ _ x) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
    complementIsoSpec_inv_comp_complementι, specMap_left_appTop_ΓSpecIso_inv]
  rfl

/-- Under `s_𝒜`, the image in `O(U_𝒜)` of an affine function is the restriction of its function.

Blueprint: `thm:geo-complement-spec`. -/
lemma complementIsoSpec_hom_appTop_coord (f : V →ᵃ[k] k) :
    (complementIsoSpec 𝒜).hom.left.appTop
        ((Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv (algebraMap _ _ (coord f))) =
      (complementι 𝒜).left.appTop (affineSpaceCoord f) :=
  complementIsoSpec_hom_appTop_algebraMap (coord f)

/-- An affine function whose zero locus is covered by `𝒜`, such as an equation of a hyperplane of
`𝒜`, restricts to a unit on `U_𝒜`. -/
lemma isUnit_complementι_appTop (hf : 𝒜.Covers (zeroLocus f)) :
    IsUnit ((complementι 𝒜).left.appTop (affineSpaceCoord f)) := by
  rw [← complementIsoSpec_hom_appTop_coord]
  exact ((isUnit_coord hf).map (Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv.hom).map
    (complementIsoSpec 𝒜).hom.left.appTop.hom

variable (𝒜) in
/-- The restriction `f̃|_{U_𝒜}` of the function of an affine function whose zero locus is covered by
`𝒜`, as a global unit on `U_𝒜`. Under `s_𝒜` it is the existing unit `SmoothAlg.complementUnit`
(`SmoothDomain.complementIsoSpec_hom_appTop_complementUnit`).

Blueprint: `thm:geo-complement-spec`. -/
def complementUnit (f : V →ᵃ[k] k) (hf : 𝒜.Covers (zeroLocus f)) : Γ((complement 𝒜).left, ⊤)ˣ :=
  (isUnit_complementι_appTop hf).unit

@[simp] lemma coe_complementUnit (hf : 𝒜.Covers (zeroLocus f)) :
    (complementUnit 𝒜 f hf : Γ((complement 𝒜).left, ⊤)) =
      (complementι 𝒜).left.appTop (affineSpaceCoord f) :=
  rfl

/-- Scaling an affine function by a nonzero constant `c` multiplies its unit by `c`. -/
lemma coe_complementUnit_smul (c : kˣ) (hf : 𝒜.Covers (zeroLocus f)) :
    (complementUnit 𝒜 ((c : k) • f) (hf.zeroLocus_smul c) : Γ((complement 𝒜).left, ⊤)) =
      (complementι 𝒜).left.appTop (affineSpaceCoord (AffineMap.const k V (c : k))) *
        complementUnit 𝒜 f hf := by
  rw [coe_complementUnit, coe_complementUnit, affineSpaceCoord_smul, map_mul]

end Comparison

/-! ### Maps of complements -/

section Hom

variable {𝒜 : Arrangement k V} {ℬ : Arrangement k W}

/-- The morphism `U_𝒜 → U_ℬ` of a map `F : O(U_ℬ) → O(U_𝒜)` of the existing coordinate rings:
`Spec F` under the comparisons `s`. Every map of complements below is of this form, and maps that
are not affine, such as the normalized slice of `thm:geo-small-targets`, are built this way from
their ring maps.

Blueprint: `thm:geo-complement-spec`. -/
def complementHom (F : ℬ.ComplementRing →ₐ[k] 𝒜.ComplementRing) : complement 𝒜 ⟶ complement ℬ :=
  (complementIsoSpec 𝒜).hom ≫ specMap (CommAlgCat.ofHom F) ≫ (complementIsoSpec ℬ).inv

variable (F : ℬ.ComplementRing →ₐ[k] 𝒜.ComplementRing)

/-- Under the comparisons, `complementHom F` is `Spec F`. -/
@[reassoc (attr := simp)]
lemma complementHom_comp_complementIsoSpec_hom :
    complementHom F ≫ (complementIsoSpec ℬ).hom =
      (complementIsoSpec 𝒜).hom ≫ specMap (CommAlgCat.ofHom F) := by
  simp [complementHom]

/-- The composite of `complementHom F` with `j_ℬ` is `Spec` of `O(W) → O(U_ℬ) → O(U_𝒜)`. -/
@[reassoc]
lemma complementHom_comp_complementι :
    complementHom F ≫ complementι ℬ =
      (complementIsoSpec 𝒜).hom ≫
        specMap (CommAlgCat.ofHom (F.comp (ComplementRing.toComplementRing ℬ))) := by
  rw [← complementIsoSpec_hom_comp ℬ, complementHom_comp_complementIsoSpec_hom_assoc,
    ← specMap_comp]
  rfl

/-- `complementHom F` pulls back the restriction of a function `x` on `𝔸_W` to the function on
`U_𝒜` of `F x` under `s_𝒜`. -/
lemma complementHom_appTop (x : CoordinateRing k W) :
    (complementHom F).left.appTop
        ((complementι ℬ).left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing k W))).inv x)) =
      (complementIsoSpec 𝒜).hom.left.appTop
        ((Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv (F (algebraMap _ _ x))) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
    complementHom_comp_complementι, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    specMap_left_appTop_ΓSpecIso_inv]
  rfl

end Hom

section Maps

variable {𝒜 : Arrangement k V} {ℬ : Arrangement k W} {𝒞 : Arrangement k U} {f : V →ᵃ[k] k}

/-- The morphism `U_ℬ → U_𝒜` given by an affine map `φ : W → V`, when the preimage under `φ` of
each hyperplane of `𝒜` is covered by `ℬ`. It is `Spec` of the existing `ComplementRing.map` under
the comparisons (`complementMap_comp_complementIsoSpec_hom`), and its composite with `j_𝒜` is
`𝔸_φ ∘ j_ℬ` (`complementMap_comp_complementι`), which determines it. It exists whether or not the
complements have `k`-points.

Blueprint: `thm:geo-complement-spec`. -/
def complementMap (φ : W →ᵃ[k] V) (𝒜 : Arrangement k V) (ℬ : Arrangement k W)
    (h : ∀ K ∈ 𝒜, ℬ.Covers (K.comap φ)) : complement ℬ ⟶ complement 𝒜 :=
  complementHom (ComplementRing.map φ 𝒜 ℬ h)

variable (φ : W →ᵃ[k] V) (h : ∀ K ∈ 𝒜, ℬ.Covers (K.comap φ))

/-- `s` is natural for the maps of complements given by affine maps: under the comparisons, the
morphism `U_ℬ → U_𝒜` is `Spec` of the existing `ComplementRing.map`.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementMap_comp_complementIsoSpec_hom :
    complementMap φ 𝒜 ℬ h ≫ (complementIsoSpec 𝒜).hom =
      (complementIsoSpec ℬ).hom ≫ specMap (CommAlgCat.ofHom (ComplementRing.map φ 𝒜 ℬ h)) :=
  complementHom_comp_complementIsoSpec_hom _

/-- The square of a map of complements into the affine spaces: `j_𝒜 ∘ (U_ℬ → U_𝒜) = 𝔸_φ ∘ j_ℬ`.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementMap_comp_complementι :
    complementMap φ 𝒜 ℬ h ≫ complementι 𝒜 = complementι ℬ ≫ affineSpaceMap k φ := by
  rw [← complementIsoSpec_hom_comp 𝒜, complementMap_comp_complementIsoSpec_hom_assoc,
    ← complementIsoSpec_hom_comp ℬ, Category.assoc, affineSpaceMap, ← specMap_comp, ← specMap_comp]
  congr 2
  exact CommAlgCat.hom_ext (AlgHom.ext fun x ↦ ComplementRing.map_algebraMap φ h x)

/-- A map of complements pulls back the restriction of `g̃` to the restriction of `(g ∘ φ)~`. -/
lemma complementMap_appTop (g : V →ᵃ[k] k) :
    (complementMap φ 𝒜 ℬ h).left.appTop ((complementι 𝒜).left.appTop (affineSpaceCoord g)) =
      (complementι ℬ).left.appTop (affineSpaceCoord (g.comp φ)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
    complementMap_comp_complementι, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineSpaceMap_appTop_affineSpaceCoord]

/-- A map of complements pulls back the unit of `f` to the unit of `f ∘ φ`. -/
lemma complementMap_appTop_complementUnit (hf : 𝒜.Covers (zeroLocus f)) :
    (complementMap φ 𝒜 ℬ h).left.appTop (complementUnit 𝒜 f hf : Γ((complement 𝒜).left, ⊤)) =
      (complementUnit ℬ (f.comp φ) (zeroLocus_comp f φ ▸ hf.comap h) :
        Γ((complement ℬ).left, ⊤)) :=
  complementMap_appTop φ h f

@[simp] lemma complementMap_id (h : ∀ K ∈ 𝒜, 𝒜.Covers (K.comap (AffineMap.id k V))) :
    complementMap (AffineMap.id k V) 𝒜 𝒜 h = 𝟙 (complement 𝒜) :=
  hom_ext_complement (by simp)

/-- Maps of complements compose. -/
@[reassoc (attr := simp)]
lemma complementMap_comp (ψ : U →ᵃ[k] W) (h₂ : ∀ K ∈ ℬ, 𝒞.Covers (K.comap ψ)) :
    complementMap ψ ℬ 𝒞 h₂ ≫ complementMap φ 𝒜 ℬ h =
      complementMap (φ.comp ψ) 𝒜 𝒞 (Covers.comap_comp h h₂) :=
  hom_ext_complement (by simp [affineSpaceMap_comp])

end Maps

section Inclusion

variable {𝒜 ℬ : Arrangement k V} {f : V →ᵃ[k] k}

variable (h : 𝒜 ≤ ℬ)

/-- The open immersion `U_ℬ → U_𝒜` for a sub-arrangement `𝒜 ≤ ℬ`. It is `Spec` of the existing
`ComplementRing.inclusion` under the comparisons (`complementInclusion_comp_complementIsoSpec_hom`),
and it commutes with the immersions into `𝔸_V` (`complementInclusion_comp_complementι`).

Blueprint: `thm:geo-complement-spec`. -/
def complementInclusion : complement ℬ ⟶ complement 𝒜 :=
  complementHom (ComplementRing.inclusion h)

/-- `s` is natural for inclusions of arrangements.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementInclusion_comp_complementIsoSpec_hom :
    complementInclusion h ≫ (complementIsoSpec 𝒜).hom =
      (complementIsoSpec ℬ).hom ≫ specMap (CommAlgCat.ofHom (ComplementRing.inclusion h)) :=
  complementHom_comp_complementIsoSpec_hom _

/-- The inclusion `U_ℬ → U_𝒜` commutes with the open immersions into `𝔸_V`.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementInclusion_comp_complementι :
    complementInclusion h ≫ complementι 𝒜 = complementι ℬ := by
  rw [← complementIsoSpec_hom_comp 𝒜, complementInclusion_comp_complementIsoSpec_hom_assoc,
    ← complementIsoSpec_hom_comp ℬ, ← specMap_comp]
  congr 2
  exact CommAlgCat.hom_ext (AlgHom.ext fun x ↦ ComplementRing.inclusion_algebraMap h x)

/-- The inclusion of a sub-arrangement is the map of complements given by the identity of `V`. -/
lemma complementInclusion_eq_complementMap
    (h' : ∀ K ∈ 𝒜, ℬ.Covers (K.comap (AffineMap.id k V))) :
    complementInclusion h = complementMap (AffineMap.id k V) 𝒜 ℬ h' :=
  hom_ext_complement (by simp)

instance : IsOpenImmersion (complementInclusion h).left := by
  have : IsOpenImmersion ((complementInclusion h).left ≫ (complementι 𝒜).left) := by
    rw [← Over.comp_left, complementInclusion_comp_complementι]
    infer_instance
  exact .of_comp _ (complementι 𝒜).left

/-- The inclusion pulls back the restriction of a function to `U_𝒜` to its restriction to `U_ℬ`. -/
lemma complementInclusion_appTop (x : Γ((affineSpace k V).left, ⊤)) :
    (complementInclusion h).left.appTop ((complementι 𝒜).left.appTop x) =
      (complementι ℬ).left.appTop x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
    complementInclusion_comp_complementι]

/-- The inclusion pulls back the unit of `f` on `U_𝒜` to the unit of `f` on `U_ℬ`. -/
lemma complementInclusion_appTop_complementUnit (hf : 𝒜.Covers (zeroLocus f)) :
    (complementInclusion h).left.appTop (complementUnit 𝒜 f hf : Γ((complement 𝒜).left, ⊤)) =
      (complementUnit ℬ f (hf.mono h) : Γ((complement ℬ).left, ⊤)) :=
  complementInclusion_appTop h _

@[simp] lemma complementInclusion_refl : complementInclusion (le_refl 𝒜) = 𝟙 (complement 𝒜) :=
  hom_ext_complement (by simp)

@[reassoc (attr := simp)]
lemma complementInclusion_comp {𝒞 : Arrangement k V} (h' : ℬ ≤ 𝒞) :
    complementInclusion h' ≫ complementInclusion h = complementInclusion (h.trans h') :=
  hom_ext_complement (by simp)

end Inclusion

section Iso

variable (𝒜 : Arrangement k V) (ℬ : Arrangement k W)

/-- An affine equivalence `e : W ≃ V` that identifies the hyperplanes of `𝒜` with those of `ℬ` by
pullback identifies the complements, by `complementMap`. It covers affine coordinate changes.

Blueprint: `thm:geo-complement-spec`. -/
@[simps hom]
def complementIso (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ ℬ) :
    complement ℬ ≅ complement 𝒜 where
  hom := complementMap (e : W →ᵃ[k] V) 𝒜 ℬ fun K hK ↦ .of_mem ((h K).1 hK)
  inv := complementMap (e.symm : V →ᵃ[k] W) ℬ 𝒜 fun L hL ↦
    .of_mem ((h _).2 (by rwa [comap_symm_comap]))
  hom_inv_id := by
    have hid : (e.symm : V →ᵃ[k] W).comp (e : W →ᵃ[k] V) = AffineMap.id k W := by
      ext x
      simp
    refine hom_ext_complement ?_
    rw [Category.assoc, complementMap_comp_complementι, complementMap_comp_complementι_assoc,
      ← affineSpaceMap_comp, hid, affineSpaceMap_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    have hid : (e : W →ᵃ[k] V).comp (e.symm : V →ᵃ[k] W) = AffineMap.id k V := by
      ext x
      simp
    refine hom_ext_complement ?_
    rw [Category.assoc, complementMap_comp_complementι, complementMap_comp_complementι_assoc,
      ← affineSpaceMap_comp, hid, affineSpaceMap_id, Category.id_comp, Category.comp_id]

end Iso

/-! ### In a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k) [FiniteDimensional k V] [FiniteDimensional k W]
variable (𝒜 : Arrangement k V) {f : V →ᵃ[k] k}

/-- The complement `U_𝒜` of an arrangement in a finite-dimensional space, as an object of any
admissible domain `D`. It is smooth and affine, so its membership is found by instances, with no
hypothesis on `𝒜`.

Blueprint: `def:geo-complement`, `thm:geo-complement-spec`. -/
@[implicit_reducible]
def complement : D.Obj := D.ofAffine (Geometric.complement 𝒜)

lemma complement_obj : (D.complement 𝒜).obj = Geometric.complement 𝒜 := rfl

/-- The comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` in a domain `D`, with target the object
`D.spec (SmoothAlg.complement 𝒜)` at which an algebraic theory is evaluated. A structure theorem
for `U_𝒜` is the existing one for `D.spec (SmoothAlg.complement 𝒜)`, composed with pullback
along `s_𝒜`.

Blueprint: `thm:geo-complement-spec`. -/
def complementIsoSpec : D.complement 𝒜 ≅ D.spec (SmoothAlg.complement 𝒜) :=
  ObjectProperty.isoMk _ (Geometric.complementIsoSpec 𝒜)

lemma complementIsoSpec_hom_hom :
    (D.complementIsoSpec 𝒜).hom.hom = (Geometric.complementIsoSpec 𝒜).hom := rfl

lemma complementIsoSpec_inv_hom :
    (D.complementIsoSpec 𝒜).inv.hom = (Geometric.complementIsoSpec 𝒜).inv := rfl

variable {𝒜} in
/-- Under `s_𝒜`, the existing unit `SmoothAlg.complementUnit 𝒜 f hf` of `O(U_𝒜)`, seen as a
function on `D.spec (SmoothAlg.complement 𝒜)`, is the restriction `f̃|_{U_𝒜}`. This identifies the
generators of the existing structure theorem with those on `U_𝒜`.

Blueprint: `thm:geo-complement-spec`. -/
lemma complementIsoSpec_hom_appTop_complementUnit (hf : 𝒜.Covers (zeroLocus f)) :
    (D.complementIsoSpec 𝒜).hom.hom.left.appTop
        ((Scheme.ΓSpecIso (.of (SmoothAlg.complement 𝒜))).inv
          (SmoothAlg.complementUnit 𝒜 f hf : SmoothAlg.complement 𝒜)) =
      (Geometric.complementUnit 𝒜 f hf : Γ((Geometric.complement 𝒜).left, ⊤)) :=
  complementIsoSpec_hom_appTop_coord f

variable {𝒜} {ℬ : Arrangement k W}

/-- The morphism `U_ℬ → U_𝒜` of an affine map, in a domain `D`.

Blueprint: `thm:geo-complement-spec`. -/
def complementMap (φ : W →ᵃ[k] V) (𝒜 : Arrangement k V) (ℬ : Arrangement k W)
    (h : ∀ K ∈ 𝒜, ℬ.Covers (K.comap φ)) : D.complement ℬ ⟶ D.complement 𝒜 :=
  ObjectProperty.homMk (Geometric.complementMap φ 𝒜 ℬ h)

@[simp] lemma complementMap_hom (φ : W →ᵃ[k] V) (h : ∀ K ∈ 𝒜, ℬ.Covers (K.comap φ)) :
    (D.complementMap φ 𝒜 ℬ h).hom = Geometric.complementMap φ 𝒜 ℬ h := rfl

/-- `s` is natural for the existing `SmoothAlg.complementMap`: under the comparisons, the morphism
`U_ℬ → U_𝒜` of an affine map is `Spec` of the existing map of rings. This is the square along which
a structure theorem on `U_𝒜` commutes with pullback.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementMap_comp_complementIsoSpec_hom (φ : W →ᵃ[k] V)
    (h : ∀ K ∈ 𝒜, ℬ.Covers (K.comap φ)) :
    D.complementMap φ 𝒜 ℬ h ≫ (D.complementIsoSpec 𝒜).hom =
      (D.complementIsoSpec ℬ).hom ≫ (D.specFunctor.map (SmoothAlg.complementMap φ 𝒜 ℬ h)).unop :=
  ObjectProperty.hom_ext _ (Geometric.complementMap_comp_complementIsoSpec_hom φ h)

variable {ℬ : Arrangement k V}

/-- The inclusion `U_ℬ → U_𝒜` of complements for a sub-arrangement `𝒜 ≤ ℬ`, in a domain `D`.

Blueprint: `thm:geo-complement-spec`. -/
def complementInclusion (h : 𝒜 ≤ ℬ) : D.complement ℬ ⟶ D.complement 𝒜 :=
  ObjectProperty.homMk (Geometric.complementInclusion h)

@[simp] lemma complementInclusion_hom (h : 𝒜 ≤ ℬ) :
    (D.complementInclusion h).hom = Geometric.complementInclusion h := rfl

/-- `s` is natural for the existing `SmoothAlg.complementInclusion`.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc (attr := simp)]
lemma complementInclusion_comp_complementIsoSpec_hom (h : 𝒜 ≤ ℬ) :
    D.complementInclusion h ≫ (D.complementIsoSpec 𝒜).hom =
      (D.complementIsoSpec ℬ).hom ≫ (D.specFunctor.map (SmoothAlg.complementInclusion h)).unop :=
  ObjectProperty.hom_ext _ (Geometric.complementInclusion_comp_complementIsoSpec_hom h)

/-- The isomorphism `U_ℬ ≅ U_𝒜` of an affine equivalence identifying the hyperplanes, in a domain
`D`. Under the comparisons it is `Spec` of the existing `SmoothAlg.complementIso`
(`complementIso_hom_comp_complementIsoSpec_hom`).

Blueprint: `thm:geo-complement-spec`. -/
def complementIso (𝒜 : Arrangement k V) (ℬ : Arrangement k W) (e : W ≃ᵃ[k] V)
    (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ ℬ) : D.complement ℬ ≅ D.complement 𝒜 :=
  ObjectProperty.isoMk _ (Geometric.complementIso 𝒜 ℬ e h)

@[simp] lemma complementIso_hom {ℬ : Arrangement k W} (e : W ≃ᵃ[k] V)
    (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ ℬ) :
    (D.complementIso 𝒜 ℬ e h).hom =
      D.complementMap (e : W →ᵃ[k] V) 𝒜 ℬ (fun K hK ↦ .of_mem ((h K).1 hK)) := rfl

/-- `s` is natural for the existing `SmoothAlg.complementIso` of an affine equivalence.

Blueprint: `thm:geo-complement-spec`. -/
@[reassoc]
lemma complementIso_hom_comp_complementIsoSpec_hom {ℬ : Arrangement k W} (e : W ≃ᵃ[k] V)
    (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ ℬ) :
    (D.complementIso 𝒜 ℬ e h).hom ≫ (D.complementIsoSpec 𝒜).hom =
      (D.complementIsoSpec ℬ).hom ≫
        (D.specFunctor.map (SmoothAlg.complementIso 𝒜 ℬ e h).hom).unop :=
  D.complementMap_comp_complementIsoSpec_hom _ _

end SmoothDomain

end OrlikSolomon.Geometric
