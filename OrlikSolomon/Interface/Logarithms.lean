/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Geometric.Logarithms

/-!
# Interface: the standard divisor, the fundamental class and maps to `𝔾ₘ`

This file is a bridge between the library and the interface file `OrlikSolomon/MainTheorem.lean`
(#140), which states the main theorem with Mathlib terms only. There, the class `τ` on `𝔾ₘ` is
characterized by its bidegree and its residue at the origin of `𝔸¹_k`, cut out by the coordinate
`X`, and maps `g : U → 𝔾ₘ` are characterized by the function that they pull the coordinate back
to. Here these terms are related to the library's standard pair of the base
`Geometric.DivisorPair.standardPair D D.point`, its class `Geometric.OrdinaryTheory.tau` and its
logarithmic classes `Geometric.OrdinaryTheory.logClass`, for a geometric theory on any admissible
domain `D`.

## Main definitions

* `Interface.standardPair D`: the divisor `{0} ⊆ 𝔸¹_k` with complement `𝔾ₘ` and equation `X`, with
  `i = Spec (X ↦ 0)` and `j = Spec (k[X] → k[T, T⁻¹])`. Its data are those of the interface's
  `standardDivisor`.
* `Interface.standardPairIso D`: its isomorphism with the library's standard pair of the base,
  `S ⊆ S ×_S 𝔸¹` with complement `S ×_S 𝔾ₘ`.

## Main results

* `Interface.residue_standardPair`: the residue of `Interface.standardPair D` is the standard
  residue of the base after pullback along the second projection `S ×_S 𝔾ₘ → 𝔾ₘ`.
* `Interface.mem_grading_and_residue_eq_one_iff`: a class on `𝔾ₘ` of bidegree `(1, 1)` has residue
  `1` at the origin exactly when it is `τ`. So the fundamental class of the interface exists and is
  unique (`Interface.existsUnique_mem_grading_and_residue_eq_one`).
* `Interface.eq_gmHom`, `Interface.pull_tau_eq_logClass`: a map `g : X → 𝔾ₘ` pulling the coordinate
  back to a unit `u` is the map `û` of `u`, so `g^* τ = [u]`.
* `Interface.existsUnique_hom_gm_iff`, `Interface.existsUnique_gmHom_iff`: a global function `f`
  is the pullback of the coordinate along some map to `𝔾ₘ` exactly when it is a unit, and the map
  is then unique.

Blueprint: `def:geo-log` and `thm:geo-units`, in the form used by the interface file.

## Implementation notes

The interface file imports the library privately, so its definitions cannot be library terms.
`Interface.standardPair` therefore repeats the body of the interface's `standardDivisor`: the
assembly of the interface identifies the two by unfolding, not by a lemma. Keep the two bodies
identical. Its equation is `Geometric.affineLineCoord k` (`standardPair_eqn`), and the coordinate
`gmCoordinate k` of `𝔾ₘ` in the interface is `Geometric.gmCoord k`, both by definition.

Inside `namespace OrlikSolomon.Interface`, the names `DivisorPair` and `OrdinaryTheory` resolve to
the algebraic `OrlikSolomon.DivisorPair` and `OrlikSolomon.OrdinaryTheory`, so the geometric ones
are written `Geometric.DivisorPair` and `Geometric.OrdinaryTheory`.

No hypothesis on `k` is needed: it is a field in the interface file, but every statement here
holds over any commutative ring, including the zero ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial

universe u v w z

namespace OrlikSolomon.Interface

open Geometric

variable {k : Type u} [CommRing k]

/-! ### The standard divisor -/

section StandardPair

variable (D : SmoothDomain k)

/-- The **standard divisor** `{0} ⊆ 𝔸¹_k`, in a domain `D`, with complement `𝔾ₘ` and equation the
coordinate `X`: `i : Spec k → 𝔸¹_k` is `Spec` of evaluation at `0`, and `j : 𝔾ₘ → 𝔸¹_k` is `Spec`
of the inclusion `k[X] → k[T, T⁻¹]`, `X ↦ T`. Its data are those of the interface's
`standardDivisor`, and it is isomorphic to the library's standard pair of the base
(`standardPairIso`). -/
@[implicit_reducible]
def standardPair : Geometric.DivisorPair D where
  ambient := D.affineLine
  closed := D.point
  compl := D.gm
  i := ObjectProperty.homMk <| Over.homMk
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) <| by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext c
      simp
  j := ObjectProperty.homMk <| Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap k[X] k[T;T⁻¹]))) <| by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  eqn := (Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X
  isRegularSection_eqn :=
    (isRegularSection_ΓSpecIso_inv_iff _).2 Polynomial.X_mem_nonZeroDivisors
  isClosedImmersion_i := IsClosedImmersion.spec_of_surjective _ fun c ↦ ⟨Polynomial.C c, by simp⟩
  ker_i := ker_specMap_of_ker_eq _ (by
    rw [CommRingCat.hom_ofHom, Polynomial.ker_evalRingHom, map_zero, sub_zero])
  isOpenImmersion_j := IsOpenImmersion.of_isLocalization (Polynomial.X : k[X])
  opensRange_j := opensRange_specMap_of_isLocalization _ _ inferInstance

lemma standardPair_ambient : (standardPair D).ambient = D.affineLine := rfl
lemma standardPair_closed : (standardPair D).closed = D.point := rfl
lemma standardPair_compl : (standardPair D).compl = D.gm := rfl

/-- The closed immersion of the standard divisor is `Spec` of evaluation at `0`. -/
@[simp] lemma standardPair_i_hom_left :
    (standardPair D).i.hom.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) := rfl

/-- The open immersion of the standard divisor is `Spec` of `k[X] → k[T, T⁻¹]`. -/
@[simp] lemma standardPair_j_hom_left :
    (standardPair D).j.hom.left = Spec.map (CommRingCat.ofHom (algebraMap k[X] k[T;T⁻¹])) := rfl

/-- The equation of the standard divisor is the coordinate of `𝔸¹_k`. -/
@[simp] lemma standardPair_eqn : (standardPair D).eqn = affineLineCoord k := rfl

/-- The equation of the standard divisor, as a unit on `𝔾ₘ`, is the coordinate of `𝔾ₘ`. -/
@[simp] lemma standardPair_eqnUnit : (standardPair D).eqnUnit = gmCoord k := by
  ext
  rw [Geometric.DivisorPair.coe_eqnUnit, standardPair_j_hom_left, standardPair_eqn, affineLineCoord,
    coe_gmCoord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, CommRingCat.ofHom_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X]

/-- `𝔸¹_k → 𝔸¹_k` given by the coordinate is the identity. -/
private lemma homAffineLineEquiv_symm_affineLineCoord :
    (homAffineLineEquiv (affineLine k)).symm (affineLineCoord k) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq, homAffineLineEquiv_apply, Over.id_left, Scheme.Hom.id_appTop,
    CommRingCat.id_apply]

/-- The isomorphism of the standard divisor with the library's standard pair of the base
`S = Spec k`: on ambient schemes `𝔸¹ ≅ S ×_S 𝔸¹`, given by the coordinate, on divisors the identity
of `S`, and on complements `𝔾ₘ ≅ S ×_S 𝔾ₘ`, whose inverse is the second projection
(`standardPairIso_inv_compl`). Its forward map is `Geometric.DivisorPair.toStandard`, with
multiplier `1`. -/
def standardPairIso : standardPair D ≅ Geometric.DivisorPair.standardPair D D.point where
  hom := Geometric.DivisorPair.toStandard (standardPair D)
  inv := Geometric.DivisorPair.homOfAmbient
    (ObjectProperty.homMk (snd _ _) : D.prodAffineLine D.point ⟶ D.affineLine) (Associated.refl _)
  hom_inv_id := Geometric.DivisorPair.hom_ext <| ObjectProperty.hom_ext _ <| by
    change lift (toUnit _) ((homAffineLineEquiv _).symm (affineLineCoord k)) ≫ snd _ _ = 𝟙 _
    rw [lift_snd, homAffineLineEquiv_symm_affineLineCoord]
  inv_hom_id := Geometric.DivisorPair.hom_ext <| ObjectProperty.hom_ext _ <| by
    change snd _ _ ≫ lift (toUnit _) ((homAffineLineEquiv _).symm (affineLineCoord k)) = 𝟙 _
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, homAffineLineEquiv_symm_affineLineCoord, Category.comp_id,
        Category.id_comp]

/-- The forward map of `standardPairIso` is `Geometric.DivisorPair.toStandard`. It is not a `simp`
lemma, so that the components below stay in `simp` normal form. -/
lemma standardPairIso_hom :
    (standardPairIso D).hom = Geometric.DivisorPair.toStandard (standardPair D) := rfl

/-- On ambient schemes, `standardPairIso` is the map `𝔸¹ → S ×_S 𝔸¹` of the coordinate. -/
@[simp] lemma standardPairIso_hom_ambient :
    (standardPairIso D).hom.ambient = Geometric.DivisorPair.toStandardAmbient (standardPair D) :=
  rfl

/-- On ambient schemes, the inverse of `standardPairIso` is the second projection
`S ×_S 𝔸¹ → 𝔸¹`. -/
@[simp] lemma standardPairIso_inv_ambient :
    (standardPairIso D).inv.ambient =
      (ObjectProperty.homMk (snd _ _) : D.prodAffineLine D.point ⟶ D.affineLine) := rfl

/-- On divisors, `standardPairIso` is the identity of the base. -/
@[simp] lemma standardPairIso_hom_closed : (standardPairIso D).hom.closed = 𝟙 D.point :=
  D.isTerminalPoint.hom_ext _ _

/-- On divisors, the inverse of `standardPairIso` is the identity of the base. -/
@[simp] lemma standardPairIso_inv_closed : (standardPairIso D).inv.closed = 𝟙 D.point :=
  D.isTerminalPoint.hom_ext _ _

/-- On complements, `𝔾ₘ ≅ S ×_S 𝔾ₘ` is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma standardPairIso_hom_compl_prodGmSnd :
    (standardPairIso D).hom.compl ≫ D.prodGmSnd D.point = 𝟙 D.gm := by
  rw [standardPairIso_hom, Geometric.DivisorPair.toStandard_compl]
  apply ObjectProperty.hom_ext
  change lift (toUnit _) (unitsEquivHomGm _ (standardPair D).eqnUnit) ≫ snd _ _ = 𝟙 _
  rw [lift_snd, standardPair_eqnUnit]
  apply hom_ext_gm
  rw [unitsEquivHomGm_appTop_gmCoord]
  exact (SmoothDomain.appTop_id_apply D.gm _).symm

/-- On complements, the inverse of `standardPairIso` is the second projection `S ×_S 𝔾ₘ → 𝔾ₘ`. -/
@[simp] lemma standardPairIso_inv_compl : (standardPairIso D).inv.compl = D.prodGmSnd D.point := by
  calc (standardPairIso D).inv.compl
      = (standardPairIso D).inv.compl ≫ (standardPairIso D).hom.compl ≫ D.prodGmSnd D.point := by
        rw [standardPairIso_hom_compl_prodGmSnd]
        exact (Category.comp_id _).symm
    _ = D.prodGmSnd D.point := by
        rw [← Category.assoc, ← Geometric.DivisorPair.comp_compl, Iso.inv_hom_id,
          Geometric.DivisorPair.id_compl]
        exact Category.id_comp _

end StandardPair

/-! ### The fundamental class -/

section FundamentalClass

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The residue of the standard divisor is the standard residue of the base, after pullback along
the second projection `S ×_S 𝔾ₘ → 𝔾ₘ`. This is naturality of the residue (C5) along the inverse
of `standardPairIso`. -/
theorem residue_standardPair (x : T.obj D.gm) :
    T.residue (standardPair D) x = T.standardResidue D.point (T.pull (D.prodGmSnd D.point) x) := by
  have h := T.residue_pull (standardPairIso D).inv x
  rw [standardPairIso_inv_compl, standardPairIso_inv_closed] at h
  exact (h.trans (T.pull_id D.point _)).symm

/-- `τ` has residue `1` at the origin. Blueprint: `def:geo-log`. -/
@[simp] theorem residue_standardPair_tau : T.residue (standardPair D) T.tau = 1 := by
  rw [residue_standardPair, Geometric.OrdinaryTheory.standardResidue_pull_prodGmSnd_tau]

/-- A class on `𝔾ₘ` has bidegree `(1, 1)` and residue `1` at the origin exactly when it is `τ`.
So the fundamental class of the interface file is `τ`: it exists and is unique.
Blueprint: `def:geo-log`. -/
theorem mem_grading_and_residue_eq_one_iff {τ : T.obj D.gm} :
    τ ∈ T.grading D.gm (1, 1) ∧ T.residue (standardPair D) τ = 1 ↔ τ = T.tau := by
  refine ⟨fun h ↦ T.eq_tau_of_mem_grading h.1 ?_, ?_⟩
  · rw [← residue_standardPair, h.2]
  · rintro rfl
    exact ⟨T.tau_mem_grading, residue_standardPair_tau T⟩

/-- There is exactly one class on `𝔾ₘ` of bidegree `(1, 1)` with residue `1` at the origin, the
fundamental class of the interface file. Blueprint: `def:geo-log`. -/
theorem existsUnique_mem_grading_and_residue_eq_one :
    ∃! τ : T.obj D.gm, τ ∈ T.grading D.gm (1, 1) ∧ T.residue (standardPair D) τ = 1 :=
  ⟨T.tau, (mem_grading_and_residue_eq_one_iff T).2 rfl,
    fun _ h ↦ (mem_grading_and_residue_eq_one_iff T).1 h⟩

end FundamentalClass

/-! ### Maps to `𝔾ₘ` -/

section Gm

/-- A map `g : X → 𝔾ₘ` of `S`-schemes that pulls the coordinate back to a unit `u` is the map `û`
of `u`. Blueprint: `thm:geo-units`. -/
theorem eq_unitsEquivHomGm {X : Over (Spec (.of k))} {g : X ⟶ gm k} {u : Γ(X.left, ⊤)ˣ}
    (hg : g.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = u) : g = unitsEquivHomGm X u :=
  hom_ext_gm (by rw [hg, unitsEquivHomGm_appTop_gmCoord])

/-- A global function `f` on an `S`-scheme `X` is the pullback of the coordinate of `𝔾ₘ` along some
map `X → 𝔾ₘ` exactly when it is a unit. Blueprint: `thm:geo-units`. -/
theorem exists_hom_gm_iff (X : Over (Spec (.of k))) (f : Γ(X.left, ⊤)) :
    (∃ g : X ⟶ gm k, g.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = f) ↔ IsUnit f := by
  refine ⟨?_, fun hf ↦ ⟨unitsEquivHomGm X hf.unit, by
    rw [unitsEquivHomGm_appTop_gmCoord, IsUnit.unit_spec]⟩⟩
  rintro ⟨g, rfl⟩
  exact (homGmEquiv X g).isUnit

/-- A global function `f` on an `S`-scheme `X` is the pullback of the coordinate of `𝔾ₘ` along
exactly one map `X → 𝔾ₘ` when it is a unit, and along none otherwise. Blueprint: `thm:geo-units`. -/
theorem existsUnique_hom_gm_iff (X : Over (Spec (.of k))) (f : Γ(X.left, ⊤)) :
    (∃! g : X ⟶ gm k, g.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = f) ↔ IsUnit f := by
  refine ⟨fun h ↦ (exists_hom_gm_iff X f).1 h.exists, fun hf ↦ ?_⟩
  obtain ⟨g, hg⟩ := (exists_hom_gm_iff X f).2 hf
  exact ⟨g, hg, fun g' hg' ↦ hom_ext_gm (hg'.trans hg.symm)⟩

variable {D : SmoothDomain k}

/-- A map `g : X → 𝔾ₘ` of a domain that pulls the coordinate back to a unit `u` is the map `û` of
`u`. Blueprint: `thm:geo-units`. -/
theorem eq_gmHom {X : D.Obj} {g : X ⟶ D.gm} {u : Γ(X.obj.left, ⊤)ˣ}
    (hg : g.hom.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = u) : g = D.gmHom u :=
  ObjectProperty.hom_ext _ (eq_unitsEquivHomGm hg)

/-- In a domain, a global function `f` on `X` is the pullback of the coordinate of `𝔾ₘ` along some
map `X → 𝔾ₘ` exactly when it is a unit. Blueprint: `thm:geo-units`. -/
theorem exists_gmHom_iff (X : D.Obj) (f : Γ(X.obj.left, ⊤)) :
    (∃ g : X ⟶ D.gm, g.hom.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = f) ↔ IsUnit f := by
  rw [← exists_hom_gm_iff]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g.hom, hg⟩, fun ⟨g, hg⟩ ↦ ⟨ObjectProperty.homMk g, hg⟩⟩

/-- In a domain, a global function `f` on `X` is the pullback of the coordinate of `𝔾ₘ` along
exactly one map `X → 𝔾ₘ` when it is a unit, and along none otherwise. Blueprint: `thm:geo-units`.
-/
theorem existsUnique_gmHom_iff (X : D.Obj) (f : Γ(X.obj.left, ⊤)) :
    (∃! g : X ⟶ D.gm, g.hom.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = f) ↔ IsUnit f := by
  refine ⟨fun h ↦ (exists_gmHom_iff X f).1 h.exists, fun hf ↦ ?_⟩
  obtain ⟨g, hg⟩ := (exists_gmHom_iff X f).2 hf
  exact ⟨g, hg, fun g' hg' ↦ SmoothDomain.gm_hom_ext (hg'.trans hg.symm)⟩

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : Geometric.OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The pullback of `τ` along a map `g : X → 𝔾ₘ` that pulls the coordinate back to a unit `u` is
the logarithmic class `[u]`. In the interface file, this identifies `g^* τ` with `[u]`.
Blueprint: `def:geo-log`. -/
theorem pull_tau_eq_logClass {X : D.Obj} {g : X ⟶ D.gm} {u : Γ(X.obj.left, ⊤)ˣ}
    (hg : g.hom.left.appTop (gmCoord k : Γ((gm k).left, ⊤)) = u) :
    T.pull g T.tau = T.logClass u := by
  rw [eq_gmHom hg, Geometric.OrdinaryTheory.logClass]

end Gm

end OrlikSolomon.Interface
