/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Exactness, stalk detection and inverse-image coherence for module sheaves

Mathlib constructs the associated module sheaf with `tilde.functor`, identifies its global
sections with the original module by `tilde.isoTop`, and exhibits its sections on distinguished
opens as localizations. We use these constructions directly. The additional result here is that
the associated-sheaf functor preserves exact sequences. Generic stalk criteria detect
quasi-isomorphisms, and inverse-image identity and composition isomorphisms record their coherence.

## Main results

* `tilde_map_basicOpen_eq_localized`: on a distinguished open, the associated-sheaf map is
  the localization of the original linear map.
* `tilde_preservesMonomorphisms` and `tilde_preservesHomology`: exactness of the tilde functor.
* `tilde_map_exact`: an exact sequence of arbitrary modules remains exact as associated sheaves.
* `sheafComplex_quasiIso_iff_stalk` and `sheafComplex_quasiIso_of_basis`: stalk and basis criteria.
* `sheafPullbackId`, `sheafPullbackComp`: inverse-image identity, composition and coherence.

No finite-generation, reducedness or nonzero-ring assumption is used.

Blueprint: `lem:geo-module-gluing`.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace OrlikSolomon.Geometric
variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- On a distinguished open, the sheaf map is the localized module homomorphism. -/
theorem tilde_map_basicOpen_eq_localized (f : M ⟶ N) (r : R) :
    ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op (PrimeSpectrum.basicOpen r))).hom =
      IsLocalizedModule.map (Submonoid.powers r)
        (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
  rw [IsLocalizedModule.map_comp]
  exact congrArg ModuleCat.Hom.hom (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r))

/-- An injective module map stays injective on each distinguished open. -/
theorem tilde_map_basicOpen_injective (f : M ⟶ N) (hf : Function.Injective f) (r : R) :
    Function.Injective ((modulesSpecToSheaf.map (tilde.map f)).hom.app
      (op (PrimeSpectrum.basicOpen r))) := by
  change Function.Injective (((modulesSpecToSheaf.map (tilde.map f)).hom.app
    (op (PrimeSpectrum.basicOpen r))).hom)
  rw [tilde_map_basicOpen_eq_localized]
  exact IsLocalizedModule.map_injective _ _ _ f.hom hf

/-- The associated-sheaf functor preserves monomorphisms. -/
instance tilde_preservesMonomorphisms (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f := by
    intro hmono
    let φ := modulesSpecToSheaf.map (tilde.map f)
    have : Mono φ := by
      constructor
      intro K g h e
      apply ObjectProperty.hom_ext
      apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
      intro r
      ext x
      apply tilde_map_basicOpen_injective f ((ModuleCat.mono_iff_injective f).1 inferInstance) r
      exact ConcreteCategory.congr_hom (NatTrans.congr_app
        (congrArg (fun t => t.hom) e) (op (PrimeSpectrum.basicOpen r))) x
    change Mono (tilde.map f)
    exact (modulesSpecToSheaf (R := R)).mono_of_mono_map inferInstance

/-- The associated-sheaf functor preserves homology, hence exact sequences. -/
instance tilde_preservesHomology (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (tilde.functor R)

/-- Exact module sequences give exact sequences of associated sheaves.
Blueprint: `lem:geo-module-gluing`. -/
theorem tilde_map_exact (S : ShortComplex (ModuleCat R)) (hS : S.Exact) :
    (S.map (tilde.functor R)).Exact := hS.map _

open CategoryTheory.Limits TopologicalSpace

/-- A morphism of complexes of module sheaves is a quasi-isomorphism if and only if its
ordinary stalk maps are quasi-isomorphisms. This compares homology sheaves, without any
exactness assertion for global sections. -/
theorem sheafComplex_quasiIso_iff_stalk (k : Type u) [Ring k] (X : TopCat.{u})
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (TopCat.Sheaf (ModuleCat.{u} k) X) c} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ x : X,
      QuasiIso (((TopCat.Sheaf.forget (ModuleCat.{u} k) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).mapHomologicalComplex c).map f) := by
  constructor
  · intro hf x
    infer_instance
  · intro hf
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap,
      TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    let F := TopCat.Sheaf.forget (ModuleCat.{u} k) X ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x
    let g := (HomologicalComplex.shortComplexFunctor _ _ n).map f
    have hg : ShortComplex.QuasiIso (F.mapShortComplex.map g) := by
      have h := (quasiIso_iff _).1 (hf x) n
      exact (quasiIsoAt_iff _ n).1 h
    have hmap := ShortComplex.mapHomologyIso_hom_naturality g F
    have : IsIso ((K.sc n).mapHomologyIso F).hom := inferInstance
    have : IsIso (((K.sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap f n)) := by
      change IsIso (((K.sc n).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap g))
      rw [← hmap]
      have := (ShortComplex.quasiIso_iff _).1 hg
      infer_instance
    change IsIso (F.map (HomologicalComplex.homologyMap f n))
    exact IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso F).hom _

section BasisComparison

variable (k : Type u) [Ring k] (X : TopCat.{u})

private theorem presheafStalk_preservesHomology (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).PreservesHomology := by
  have : PreservesFiniteLimits ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ
      (ModuleCat.{u} k)).obj (OpenNhds.inclusion x).op) := by infer_instance
  have : PreservesFiniteColimits ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ
      (ModuleCat.{u} k)).obj (OpenNhds.inclusion x).op) := by infer_instance
  have : PreservesFiniteLimits (colim (J := (OpenNhds x)ᵒᵖ) (C := ModuleCat.{u} k)) :=
    inferInstance
  have : PreservesFiniteColimits (colim (J := (OpenNhds x)ᵒᵖ) (C := ModuleCat.{u} k)) :=
    inferInstance
  have : PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x) :=
    comp_preservesFiniteColimits _ _
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

private theorem presheaf_stalkMap_isIso_of_basis {F G : X.Presheaf (ModuleCat.{u} k)}
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (f : F ⟶ G)
    (hf : ∀ U ∈ B, IsIso (f.app (op U))) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB
    intro U hU
    have := hf U hU
    exact (ConcreteCategory.bijective_of_isIso _).1
  · intro t
    obtain ⟨U, hxU, hU, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G x t
    have := hf U hU
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (f.app (op U))).2 s
    refine ⟨F.germ U x hxU a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha]

/-- A map of complexes of module presheaves induces a quasi-isomorphism at every stalk if
its maps on section complexes are quasi-isomorphisms on a basis. Filtered colimits of modules
preserve homology; no sheaf condition or assertion about global sections is needed. -/
theorem presheafComplex_stalk_quasiIso_of_basis
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (X.Presheaf (ModuleCat.{u} k)) c} (f : K ⟶ L)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso
      ((((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)).mapHomologicalComplex c).map f))
    (x : X) :
    QuasiIso
      (((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).mapHomologicalComplex c).map f) := by
  have := presheafStalk_preservesHomology k X x
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff]
  let S := K.sc n
  let T := L.sc n
  let g := (HomologicalComplex.shortComplexFunctor _ _ n).map f
  have hmap : ∀ U ∈ B, IsIso ((ShortComplex.homologyMap g).app (op U)) := by
    intro U hU
    let E := (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)
    have : E.Additive := by infer_instance
    have : E.PreservesHomology := by infer_instance
    have hg : ShortComplex.QuasiIso (E.mapShortComplex.map g) := by
      exact (quasiIsoAt_iff _ n).1 ((quasiIso_iff _).1 (hf U hU) n)
    have hnat := ShortComplex.mapHomologyIso_hom_naturality g E
    have : IsIso ((S.mapHomologyIso E).hom ≫ E.map (ShortComplex.homologyMap g)) := by
      rw [← hnat]
      have := (ShortComplex.quasiIso_iff _).1 hg
      infer_instance
    change IsIso (E.map (ShortComplex.homologyMap g))
    exact IsIso.of_isIso_comp_left (S.mapHomologyIso E).hom _
  let F := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x
  have : IsIso (F.map (ShortComplex.homologyMap g)) :=
    presheaf_stalkMap_isIso_of_basis k X hB _ hmap x
  have hnat := ShortComplex.mapHomologyIso_hom_naturality g F
  have : IsIso ((S.mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap g)) :=
    inferInstance
  rw [← hnat] at this
  have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map g)) :=
    IsIso.of_isIso_comp_right _ (T.mapHomologyIso F).hom
  exact (ShortComplex.quasiIso_iff _).2 this

/-- A map of complexes of module sheaves is a quasi-isomorphism if its maps on section
complexes are quasi-isomorphisms on a basis. In particular, affine-open section comparisons
suffice for a scheme; this does not assert that global sections preserve sheaf homology. -/
theorem sheafComplex_quasiIso_of_basis
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (TopCat.Sheaf (ModuleCat.{u} k) X) c} (f : K ⟶ L)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso
      ((((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)).mapHomologicalComplex c).map
        (((TopCat.Sheaf.forget (ModuleCat.{u} k) X).mapHomologicalComplex c).map f))) :
    QuasiIso f := by
  apply (sheafComplex_quasiIso_iff_stalk k X f).2
  intro x
  exact presheafComplex_stalk_quasiIso_of_basis k X
    (((TopCat.Sheaf.forget (ModuleCat.{u} k) X).mapHomologicalComplex c).map f) hB hf x

end BasisComparison

/-- The inverse-image functor on module-valued sheaves for the identity map is canonically
isomorphic to the identity functor, by the identity adjunction. -/
def sheafPullbackId (R : Type u) [Ring R] (T : TopCat.{u}) :
    TopCat.Sheaf.pullback (ModuleCat.{u} R) (𝟙 T) ≅ 𝟭 _ :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (𝟙 T)).leftAdjointIdIso
    (Iso.refl _)

/-- Successive inverse images of module-valued sheaves are canonically isomorphic to the
inverse image for the composite map, by composition of the pullback-pushforward adjunctions. -/
def sheafPullbackComp (R : Type u) [Ring R] {T₁ T₂ T₃ : TopCat.{u}}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    TopCat.Sheaf.pullback (ModuleCat.{u} R) g ⋙
      TopCat.Sheaf.pullback (ModuleCat.{u} R) f ≅
        TopCat.Sheaf.pullback (ModuleCat.{u} R) (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (f ≫ g))
    (Iso.refl _)

/-- Composing inverse image with the identity on the source agrees with the right unitor. -/
theorem sheafPullbackComp_id_comp (R : Type u) [Ring R] {T₁ T₂ : TopCat.{u}}
    (f : T₁ ⟶ T₂) :
    sheafPullbackComp R (𝟙 T₁) f =
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} R) f)
        (sheafPullbackId R T₁) ≪≫ Functor.rightUnitor _ := by
  exact Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (by ext; rfl)

/-- Composing inverse image with the identity on the target agrees with the left unitor. -/
theorem sheafPullbackComp_comp_id (R : Type u) [Ring R] {T₁ T₂ : TopCat.{u}}
    (f : T₁ ⟶ T₂) :
    sheafPullbackComp R f (𝟙 T₂) =
      Functor.isoWhiskerRight (sheafPullbackId R T₂)
        (TopCat.Sheaf.pullback (ModuleCat.{u} R) f) ≪≫ Functor.leftUnitor _ := by
  exact Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (by ext; rfl)

/-- The two canonical comparisons for three successive inverse images agree under the
functor associator. -/
theorem sheafPullbackComp_assoc (R : Type u) [Ring R] {T₁ T₂ T₃ T₄ : TopCat.{u}}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) (h : T₃ ⟶ T₄) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} R) h)
        (sheafPullbackComp R f g) ≪≫ sheafPullbackComp R (f ≫ g) h =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sheafPullbackComp R g h)
          (TopCat.Sheaf.pullback (ModuleCat.{u} R) f) ≪≫ sheafPullbackComp R f (g ≫ h) := by
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (by ext; rfl)

end OrlikSolomon.Geometric
