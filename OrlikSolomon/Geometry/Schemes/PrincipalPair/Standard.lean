/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Basic
public import OrlikSolomon.Geometry.Schemes.Products

/-!
# The geometric standard pair

For every scheme `X` over `S = Spec k`, affine or not, the zero section `X → X ×_S 𝔸¹`, the open
immersion `X ×_S 𝔾ₘ → X ×_S 𝔸¹` and the coordinate `z` form a principal pair: the zero section is a
closed immersion with kernel `z 𝒪`, the open immersion has image the basic open of `z`, and `z` is
regular. In a domain this is the pair `DivisorPair.standardPair D X`, which `thm:geo-gm-product`
uses for every object of the domain.

## Main results

* `isClosedImmersion_zeroSection_left`, `ker_zeroSection_left`: the closed certificate. The zero
  section is a monomorphism with the universal property of the zero scheme of `z`.
* `isOpenImmersion_whiskerLeft_gmToAffineLine_left`, `opensRange_whiskerLeft_gmToAffineLine_left`:
  the open certificate, by the same argument for the basic open.
* `isRegularSection_prodCoord`: `z` is regular. Regularity is local, an affine open `V` of `X` gives
  the open `V ×_S 𝔸¹` of `X ×_S 𝔸¹`, and on `Spec B ×_S 𝔸¹ ≅ Spec B[z]` the coordinate is the
  variable, a non-zero-divisor of `B[z]` for every ring `B`, including `0`.

## Main definitions

* `DivisorPair.standardPair D X`: the standard pair `(X ×_S 𝔸¹, X, X ×_S 𝔾ₘ, z)` of an object `X` of
  a domain `D`.
* `DivisorPair.standardPairMap`, `DivisorPair.standardPairFunctor`: its naturality in `X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### Certificates on every scheme -/

section Certificates

variable (X : Over (Spec (.of k)))

/-- Pulling back the coordinate along `f ▷ 𝔸¹` gives the coordinate. It is not a `simp` lemma:
`simp` rewrites the object `(X ⊗ 𝔸¹).left` in its type. -/
lemma whiskerRight_appTop_prodCoord {Y : Over (Spec (.of k))} (f : Y ⟶ X) :
    (f ▷ affineLine k).left.appTop (prodCoord X) = prodCoord Y := by
  rw [prodCoord, prodCoord, ← homAffineLineEquiv_comp, whiskerRight_snd]

instance : Mono (zeroSection X).left :=
  have : IsSplitMono (zeroSection X).left :=
    .mk' ⟨(fst X (affineLine k)).left, by rw [← Over.comp_left, zeroSection_fst, Over.id_left]⟩
  inferInstance

/-- The zero scheme of `z` factors through the zero section. -/
lemma exists_comp_zeroSection_left :
    ∃ a, a ≫ (zeroSection X).left = zeroSchemeι (prodCoord X) := by
  let Z : Over (Spec (.of k)) := Over.mk (zeroSchemeι (prodCoord X) ≫ (X ⊗ affineLine k).hom)
  let ι : Z ⟶ X ⊗ affineLine k := Over.homMk (zeroSchemeι (prodCoord X))
  have h : (ι ≫ fst _ _) ≫ zeroSection X = ι := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, zeroSection_fst, Category.comp_id]
    · apply (homAffineLineEquiv _).injective
      rw [homAffineLineEquiv_comp, homAffineLineEquiv_comp]
      change ((ι ≫ fst _ _).left ≫ (zeroSection X).left).appTop (prodCoord X) =
        (zeroSchemeι (prodCoord X)).appTop (prodCoord X)
      rw [zeroSchemeι_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        zeroSection_appTop_prodCoord, map_zero]
  exact ⟨(ι ≫ fst _ _).left, by rw [← Over.comp_left, h]; rfl⟩

/-- The zero section `X → X ×_S 𝔸¹` is a closed immersion, for every `S`-scheme `X`.

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
instance isClosedImmersion_zeroSection_left : IsClosedImmersion (zeroSection X).left :=
  (isClosedImmersion_and_ker_eq_of_mono (zeroSection_appTop_prodCoord X)
    (exists_comp_zeroSection_left X).choose_spec).1

/-- The zero section `X → X ×_S 𝔸¹` has kernel `z 𝒪`, for every `S`-scheme `X`.

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
lemma ker_zeroSection_left :
    (zeroSection X).left.ker = principalIdealSheaf (prodCoord X) :=
  (isClosedImmersion_and_ker_eq_of_mono (zeroSection_appTop_prodCoord X)
    (exists_comp_zeroSection_left X).choose_spec).2

instance : Mono (gmToAffineLine k) :=
  ⟨fun a b e ↦ hom_ext_gm (by
    rw [← gmToAffineLine_appTop_affineLineCoord, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, ← Over.comp_left, e, Over.comp_left, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply])⟩

instance : Mono (X ◁ gmToAffineLine k) := by
  refine ⟨fun a b e ↦ CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
  · have := congrArg (fun φ ↦ φ ≫ fst X (affineLine k)) e
    simpa only [Category.assoc, whiskerLeft_fst] using this
  · rw [← cancel_mono (gmToAffineLine k), Category.assoc, Category.assoc, ← whiskerLeft_snd,
      reassoc_of% e]

/-- The coordinate is a unit on `X ×_S 𝔾ₘ`. -/
lemma isUnit_whiskerLeft_gmToAffineLine_appTop_prodCoord :
    IsUnit ((X ◁ gmToAffineLine k).left.appTop (prodCoord X)) := by
  rw [whiskerLeft_gmToAffineLine_appTop_prodCoord]
  exact (gmCoord k).isUnit.map _

/-- The basic open of the coordinate factors through `X ×_S 𝔾ₘ`. -/
lemma exists_comp_whiskerLeft_gmToAffineLine_left :
    ∃ a, a ≫ (X ◁ gmToAffineLine k).left =
      ((X ⊗ affineLine k).left.basicOpen (prodCoord X)).ι := by
  let V := (X ⊗ affineLine k).left.basicOpen (prodCoord X)
  have hu : IsUnit (V.ι.appTop (prodCoord X)) :=
    (range_subset_basicOpen_iff V.ι).1 (by rw [Scheme.Opens.range_ι])
  let W : Over (Spec (.of k)) := Over.mk (V.ι ≫ (X ⊗ affineLine k).hom)
  let ι : W ⟶ X ⊗ affineLine k := Over.homMk V.ι
  have h : lift (ι ≫ fst _ _) (unitsEquivHomGm W hu.unit) ≫ (X ◁ gmToAffineLine k) = ι := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
    · apply (homAffineLineEquiv _).injective
      rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc, homAffineLineEquiv_comp,
        homAffineLineEquiv_apply, gmToAffineLine_appTop_affineLineCoord,
        unitsEquivHomGm_appTop_gmCoord, IsUnit.unit_spec]
      rfl
  exact ⟨(lift (ι ≫ fst _ _) (unitsEquivHomGm W hu.unit)).left, by
    rw [← Over.comp_left, h]; rfl⟩

/-- The open immersion `X ×_S 𝔾ₘ → X ×_S 𝔸¹` is an open immersion, for every `S`-scheme `X`.

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
instance isOpenImmersion_whiskerLeft_gmToAffineLine_left :
    IsOpenImmersion (X ◁ gmToAffineLine k).left :=
  isOpenImmersion_of_mono (isUnit_whiskerLeft_gmToAffineLine_appTop_prodCoord X)
    (exists_comp_whiskerLeft_gmToAffineLine_left X).choose_spec

/-- The image of `X ×_S 𝔾ₘ → X ×_S 𝔸¹` is the basic open of the coordinate, for every `S`-scheme
`X`.

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
lemma opensRange_whiskerLeft_gmToAffineLine_left :
    (X ◁ gmToAffineLine k).left.opensRange = (X ⊗ affineLine k).left.basicOpen (prodCoord X) :=
  opensRange_eq_of_mono (isUnit_whiskerLeft_gmToAffineLine_appTop_prodCoord X)
    (exists_comp_whiskerLeft_gmToAffineLine_left X).choose_spec

/-- On `Spec B ×_S 𝔸¹ ≅ Spec B[z]` the coordinate is the variable, which is regular for every
`k`-algebra `B`. -/
lemma isRegularSection_prodCoord_spec (B : CommAlgCat.{u} k) :
    IsRegularSection (prodCoord (spec B)) := by
  apply IsRegularSection.of_isIso (specPolynomialIso B).hom.left
  rw [specPolynomialIso_hom_appTop_prodCoord, isRegularSection_ΓSpecIso_inv_iff]
  exact Polynomial.X_mem_nonZeroDivisors

/-- The coordinate of `V ×_S 𝔸¹` is regular for affine `V`. -/
lemma isRegularSection_prodCoord_of_isAffine [IsAffine X.left] :
    IsRegularSection (prodCoord X) := by
  have : IsIso ((specGlobalSectionsIso X).hom ▷ affineLine k).left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map
      ((specGlobalSectionsIso X).hom ▷ affineLine k)))
  apply IsRegularSection.of_isIso ((specGlobalSectionsIso X).hom ▷ affineLine k).left
  rw [whiskerRight_appTop_prodCoord]
  exact isRegularSection_prodCoord_spec _

/-- The coordinate of `X ×_S 𝔸¹` is regular, for every `S`-scheme `X`: regularity is local, and over
an affine open `V` of `X` it is the regularity of the variable of `Γ(V)[z]`.

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
theorem isRegularSection_prodCoord : IsRegularSection (prodCoord X) := by
  refine .of_isOpenImmersion_cover fun y ↦ ?_
  obtain ⟨V, hV⟩ : ∃ V : X.left.affineOpens, (fst X (affineLine k)).left y ∈ V.1 :=
    TopologicalSpace.Opens.mem_iSup.1 ((iSup_affineOpens_eq_top X.left).ge (Set.mem_univ _))
  let V' : Over (Spec (.of k)) := Over.mk (V.1.ι ≫ X.hom)
  have : IsAffine V'.left := V.2
  let ιV : V' ⟶ X := Over.homMk V.1.ι rfl
  have sq : IsPullback (fst V' (affineLine k)).left (ιV ▷ affineLine k).left V.1.ι
      (fst X (affineLine k)).left := by
    refine IsPullback.of_bot ?_ (by rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]; rfl)
      (IsPullback.of_hasPullback X.hom (affineLine k).hom)
    rw [Over.whiskerRight_left_snd]
    exact IsPullback.of_hasPullback V'.hom (affineLine k).hom
  refine ⟨_, pullback.fst (fst X (affineLine k)).left V.1.ι, inferInstance, ?_, ?_⟩
  · rw [IsOpenImmersion.range_pullbackFst]
    change (fst X (affineLine k)).left y ∈ V.1.ι.opensRange
    rwa [Scheme.Opens.opensRange_ι]
  · apply IsRegularSection.of_isIso sq.flip.isoPullback.hom
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sq.flip.isoPullback_hom_fst,
      whiskerRight_appTop_prodCoord]
    exact isRegularSection_prodCoord_of_isAffine V'

end Certificates

/-! ### The standard pair in a domain -/

namespace DivisorPair

variable {D : SmoothDomain k}

variable (D) in
/-- The standard pair `(X ×_S 𝔸¹, X, X ×_S 𝔾ₘ, z)` of an object `X` of a domain `D`: the zero
section, the open immersion of `X ×_S 𝔾ₘ`, and the coordinate `z`. It is a pair for every `X`,
affine or not. For `X = Spec A` it is `Spec` of the algebraic standard pair
`(A[z], A, A[z, z⁻¹], z)` (`specStandardPairIso`).

Blueprint: `lem:geo-products`, `def:geo-divisor-pair`. -/
@[implicit_reducible]
def standardPair (X : D.Obj) : DivisorPair D where
  ambient := D.prodAffineLine X
  closed := X
  compl := D.prodGm X
  i := D.zeroSection X
  j := D.prodGmToProdAffineLine X
  eqn := prodCoord X.obj
  isRegularSection_eqn := isRegularSection_prodCoord X.obj
  isClosedImmersion_i := isClosedImmersion_zeroSection_left X.obj
  ker_i := ker_zeroSection_left X.obj
  isOpenImmersion_j := isOpenImmersion_whiskerLeft_gmToAffineLine_left X.obj
  opensRange_j := opensRange_whiskerLeft_gmToAffineLine_left X.obj

section StandardPair

variable (X : D.Obj)

lemma standardPair_ambient : (standardPair D X).ambient = D.prodAffineLine X := rfl
lemma standardPair_closed : (standardPair D X).closed = X := rfl
lemma standardPair_compl : (standardPair D X).compl = D.prodGm X := rfl
@[simp] lemma standardPair_i : (standardPair D X).i = D.zeroSection X := rfl
@[simp] lemma standardPair_j : (standardPair D X).j = D.prodGmToProdAffineLine X := rfl
@[simp] lemma standardPair_eqn : (standardPair D X).eqn = prodCoord X.obj := rfl

/-- The equation of the standard pair, as a unit on `X ×_S 𝔾ₘ`, is the coordinate of `𝔾ₘ`. -/
lemma coe_standardPair_eqnUnit :
    ((standardPair D X).eqnUnit : Γ((standardPair D X).compl.obj.left, ⊤)) =
      (snd X.obj (gm k)).left.appTop (gmCoord k) :=
  whiskerLeft_gmToAffineLine_appTop_prodCoord X.obj

variable {X} {Y Z : D.Obj}

/-- The morphism of standard pairs `g × 𝔸¹` of a morphism `g : X ⟶ Y`; it pulls the coordinate back
to the coordinate. -/
def standardPairMap (g : X ⟶ Y) : standardPair D X ⟶ standardPair D Y where
  ambient := D.prodAffineLineMap g
  closed := g
  compl := D.prodGmMap g
  i_comp := by
    apply ObjectProperty.hom_ext
    change zeroSection X.obj ≫ g.hom ▷ affineLine k = g.hom ≫ zeroSection Y.obj
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, zeroSection_fst_assoc, Category.assoc,
        zeroSection_fst, Category.comp_id]
    · apply (homAffineLineEquiv _).injective
      rw [Category.assoc, whiskerRight_snd, Category.assoc, homAffineLineEquiv_comp,
        homAffineLineEquiv_comp, homAffineLineEquiv_comp]
      change (zeroSection X.obj).left.appTop (prodCoord X.obj) =
        g.hom.left.appTop ((zeroSection Y.obj).left.appTop (prodCoord Y.obj))
      rw [zeroSection_appTop_prodCoord, zeroSection_appTop_prodCoord, map_zero]
  j_comp := by
    apply ObjectProperty.hom_ext
    change X.obj ◁ gmToAffineLine k ≫ g.hom ▷ affineLine k =
      g.hom ▷ gm k ≫ Y.obj ◁ gmToAffineLine k
    exact whisker_exchange g.hom (gmToAffineLine k)
  associated_eqn := by
    change Associated ((g.hom ▷ affineLine k).left.appTop (prodCoord Y.obj)) (prodCoord X.obj)
    rw [whiskerRight_appTop_prodCoord]

@[simp] lemma standardPairMap_ambient (g : X ⟶ Y) :
    (standardPairMap g).ambient = D.prodAffineLineMap g := rfl
@[simp] lemma standardPairMap_closed (g : X ⟶ Y) : (standardPairMap g).closed = g := rfl
@[simp] lemma standardPairMap_compl (g : X ⟶ Y) : (standardPairMap g).compl = D.prodGmMap g := rfl

variable (D) in
/-- The standard pair is functorial in the object. -/
@[simps obj map]
def standardPairFunctor : D.Obj ⥤ DivisorPair D where
  obj := standardPair D
  map := standardPairMap
  map_id _ := hom_ext (ObjectProperty.hom_ext _ (id_whiskerRight _ _))
  map_comp _ _ := hom_ext (ObjectProperty.hom_ext _ (comp_whiskerRight _ _ _))

end StandardPair

/-! ### The map to the standard pair of the point -/

section ToStandard

variable (P : DivisorPair D)

/-- The map `X → S ×_S 𝔸¹` of the equation `f` of a pair. -/
def toStandardAmbient : P.ambient ⟶ D.prodAffineLine D.point :=
  ObjectProperty.homMk (lift (toUnit P.ambient.obj) ((homAffineLineEquiv _).symm P.eqn))

/-- The map of the equation pulls the coordinate back to the equation. -/
@[simp] lemma toStandardAmbient_appTop_prodCoord :
    (toStandardAmbient P).hom.left.appTop (prodCoord D.point.obj) = P.eqn := by
  change homAffineLineEquiv _ (lift (toUnit P.ambient.obj) ((homAffineLineEquiv _).symm P.eqn) ≫
    snd _ _) = P.eqn
  rw [lift_snd, Equiv.apply_symm_apply]

/-- The morphism from a pair to the standard pair of the point given by its equation, `z ↦ f`,
with multiplier `1`. On ambient schemes it is the map `X → 𝔸¹` of `f` (`toStandard_ambient`), on
divisors the map to the point, and on open parts the map `U → 𝔾ₘ` of the unit `f|_U`
(`toStandard_compl`). It is the geometric form of `OrlikSolomon.DivisorPair.fromStandard`, with
arrows reversed, and is used for `thm:geo-log-laws`. -/
def toStandard : P ⟶ standardPair D D.point :=
  homOfAmbient (toStandardAmbient P) (by
    rw [standardPair_eqn, toStandardAmbient_appTop_prodCoord])

@[simp] lemma toStandard_ambient : (toStandard P).ambient = toStandardAmbient P := rfl

/-- On divisors, `toStandard` is the map to the point. -/
lemma toStandard_closed : (toStandard P).closed = D.isTerminalPoint.from P.closed :=
  D.isTerminalPoint.hom_ext _ _

/-- On open parts, `toStandard` is the map `U → 𝔾ₘ` of the unit `f|_U`. -/
lemma toStandard_compl :
    (toStandard P).compl =
      ObjectProperty.homMk (lift (toUnit P.compl.obj) (unitsEquivHomGm _ P.eqnUnit)) := by
  rw [← cancel_mono (standardPair D D.point).j, ← (toStandard P).j_comp]
  apply ObjectProperty.hom_ext
  change P.j.hom ≫ lift (toUnit P.ambient.obj) ((homAffineLineEquiv _).symm P.eqn) =
    lift (toUnit P.compl.obj) (unitsEquivHomGm _ P.eqnUnit) ≫ (_ ◁ gmToAffineLine k)
  apply CartesianMonoidalCategory.hom_ext
  · exact toUnit_unique _ _
  · apply (homAffineLineEquiv _).injective
    rw [Category.assoc, lift_snd, Category.assoc, whiskerLeft_snd, lift_snd_assoc,
      homAffineLineEquiv_comp, Equiv.apply_symm_apply, homAffineLineEquiv_apply,
      Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      gmToAffineLine_appTop_affineLineCoord, unitsEquivHomGm_appTop_gmCoord, coe_eqnUnit]

end ToStandard

end DivisorPair

end OrlikSolomon.Geometric
