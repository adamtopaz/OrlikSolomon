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
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Detecting sheaf-complex comparisons on stalks

The ordinary module stalk functors preserve homology and jointly detect isomorphisms of
sheaves. Consequently they detect quasi-isomorphisms of sheaf complexes of any shape.
This criterion is the sheaf-theoretic step in the logarithmic comparison of
`thm:geo-log-sheaves`; it makes no assertion about applying global sections to a
quasi-isomorphism.

## Main results

* `sheafComplex_quasiIso_iff_stalk`: a map of complexes of module sheaves is a
  quasi-isomorphism exactly when all of its stalk maps are quasi-isomorphisms.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace OrlikSolomon.Geometric.DeRham

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

end OrlikSolomon.Geometric.DeRham
