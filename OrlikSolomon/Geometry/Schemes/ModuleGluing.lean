/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Exact
/-!
# Exactness of associated module sheaves

Mathlib constructs the associated module sheaf with `tilde.functor`, identifies its global
sections with the original module by `tilde.isoTop`, and exhibits its sections on distinguished
opens as localizations. We use these constructions directly. The additional result here is that
the associated-sheaf functor preserves exact sequences.

## Main results

* `tilde_map_basicOpen_eq_localized`: on a distinguished open, the associated-sheaf map is
  the localization of the original linear map.
* `tilde_preservesMonomorphisms` and `tilde_preservesHomology`: exactness of the tilde functor.
* `tilde_map_exact`: an exact sequence of arbitrary modules remains exact as associated sheaves.

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

/-- Exact module sequences give exact sequences of associated sheaves. -/
theorem tilde_map_exact (S : ShortComplex (ModuleCat R)) (hS : S.Exact) :
    (S.map (tilde.functor R)).Exact := hS.map _
end OrlikSolomon.Geometric
