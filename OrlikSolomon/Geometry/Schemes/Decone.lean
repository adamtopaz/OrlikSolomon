/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Complement.Basic
public import OrlikSolomon.Geometry.Schemes.Projective

/-!
# The cone and the decone as open subschemes of affine space

This file completes `thm:geo-projective-geometry` of the geometric refactor blueprint on its affine
sides. `Geometry/Schemes/Projective` states the decone and cone isomorphisms with the spectra of the
existing coordinate rings of `decone_{ℓ₀} P` and `cone P`. Composing with the comparisons `s_𝒜` of
`thm:geo-complement-spec` gives them with the actual complements: `U_P ≅ U_{decone_{ℓ₀} P}`, an open
subscheme of the affine space of the slice `ℓ₀ = 1`, and `V_P = U_{cone P} ≅ U_P ×_S 𝔾ₘ`, with `V_P`
an open subscheme of `𝔸_W`.

## Main definitions

* `Geometric.coneComplementProjection P`: the canonical projection `q : V_P → U_P`.
* `Geometric.coneComplementIsoProdGm hℓ₀`: `V_P ≅ U_P ×_S 𝔾ₘ`, for an equation `ℓ₀` of a hyperplane
  of `P`.
* `Geometric.projectiveDeconeComplementIso hℓ₀`: `U_P ≅ U_{decone_{ℓ₀} P}`.
* `SmoothDomain.coneComplementProjection`, `SmoothDomain.coneComplementIsoProdGm`,
  `SmoothDomain.projectiveDeconeComplementIso`: the same in an admissible domain.

## Main results

* `coneComplementIsoProdGm_hom_fst`, `coneComplementIsoProdGm_hom_snd_appTop_gmCoord`: the first
  coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` is `q`, and the second is `ℓ₀`.
* `complementι_appTop_eq_mul_coneComplementProjection_appTop`: `ℓ = ℓ₀ q^*(ℓ / ℓ₀)` on `V_P`.
* `projectiveDeconeComplementIso_hom_appTop`: the decone isomorphism identifies `ℓ / ℓ₀` with the
  restriction of `ℓ` to the slice.
* `SmoothDomain.coneComplementProjection_comp_projectiveComplementIsoSpec_hom`,
  `SmoothDomain.projectiveDeconeComplementIso_hom_comp_complementIsoSpec_hom`: under the
  comparisons, `q` and the decone isomorphism are `Spec` of the existing `projectiveToCone` and
  `deconeIso`.

## Implementation notes

The names `complementι` of `Geometry/Schemes/Complement/Basic` and of
`ProjectiveArrangement.complementι` in `Geometry/ProjectiveScheme` would clash under
`open ProjectiveArrangement`, so this file does not open that namespace.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open Module

universe u

namespace OrlikSolomon.Geometric

open CoordinateRing ProjectiveArrangement.ComplementRing

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]
variable {P : ProjectiveArrangement k W} [Nonempty P] {ℓ ℓ₀ : Dual k W}

/-! ### The cone -/

variable (P) in
/-- The canonical projection `q : V_P → U_P` from the complement `V_P = U_{cone P}` of the cone, the
open subscheme of `𝔸_W`: the comparison `s_{cone P}` followed by `coneProjection`. It involves no
hyperplane at infinity.

Blueprint: `thm:geo-projective-geometry`. -/
def coneComplementProjection : complement P.cone ⟶ projectiveComplement P :=
  (complementIsoSpec P.cone).hom ≫ coneProjection P

/-- The isomorphism `V_P ≅ U_P ×_S 𝔾ₘ` for the complement `V_P = U_{cone P}` of the cone, for an
equation `ℓ₀` of a hyperplane of `P`.

Blueprint: `thm:geo-projective-geometry`. -/
def coneComplementIsoProdGm (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    complement P.cone ≅ projectiveComplement P ⊗ gm k :=
  complementIsoSpec P.cone ≪≫ coneIsoProdGm hℓ₀

/-- The first coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` is the canonical projection `q`.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc (attr := simp)]
lemma coneComplementIsoProdGm_hom_fst (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (coneComplementIsoProdGm hℓ₀).hom ≫ fst _ _ = coneComplementProjection P := by
  rw [coneComplementIsoProdGm, Iso.trans_hom, Category.assoc, coneIsoProdGm_hom_fst,
    coneComplementProjection]

/-- The second coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` pulls back the coordinate of `𝔾ₘ` to the restriction
of `ℓ₀` to `V_P`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma coneComplementIsoProdGm_hom_snd_appTop_gmCoord (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    ((coneComplementIsoProdGm hℓ₀).hom ≫ snd _ _).left.appTop (gmCoord k) =
      (complementι P.cone).left.appTop (affineSpaceCoord ℓ₀.toAffineMap) := by
  rw [coneComplementIsoProdGm, Iso.trans_hom, Category.assoc, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coneIsoProdGm_hom_snd_appTop_gmCoord,
    complementIsoSpec_hom_appTop_coord]

/-- On `V_P = U_{cone P}`, an equation `ℓ` is `ℓ₀ q^*(ℓ / ℓ₀)`, for every equation `ℓ₀` of a
hyperplane of `P`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma complementι_appTop_eq_mul_coneComplementProjection_appTop (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (complementι P.cone).left.appTop (affineSpaceCoord ℓ.toAffineMap) =
      (complementι P.cone).left.appTop (affineSpaceCoord ℓ₀.toAffineMap) *
        (coneComplementProjection P).left.appTop
          (projectiveRatio hℓ hℓ₀ : Γ((projectiveComplement P).left, ⊤)) := by
  have h := congrArg (complementIsoSpec P.cone).hom.left.appTop
    (congrArg Units.val (specUnit_coneUnit hℓ hℓ₀))
  simp only [Units.val_mul, map_mul, coe_coneUnit, Units.coe_map] at h
  rw [← complementIsoSpec_hom_appTop_coord, ← complementIsoSpec_hom_appTop_coord,
    coneComplementProjection, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact h

/-! ### The decone -/

/-- The isomorphism `U_P ≅ U_{decone_{ℓ₀} P}` with the complement of the decone, the open
subscheme of the affine space of the slice `ℓ₀ = 1`: `projectiveDeconeIso` followed by
`s_{decone P}⁻¹`.

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveDeconeComplementIso (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    projectiveComplement P ≅ complement (P.decone ℓ₀) :=
  projectiveDeconeIso hℓ₀ ≪≫ (complementIsoSpec (P.decone ℓ₀)).symm

/-- The decone isomorphism pulls back the restriction of an equation `ℓ` to the slice `ℓ₀ = 1`,
seen on the complement of the decone, to the ratio `ℓ / ℓ₀`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma projectiveDeconeComplementIso_hom_appTop (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) :
    (projectiveDeconeComplementIso hℓ₀).hom.left.appTop ((complementι (P.decone ℓ₀)).left.appTop
        (affineSpaceCoord (ℓ.toAffineMap.comp (chart (slice ℓ₀))))) =
      projectiveRatio hℓ hℓ₀ := by
  rw [projectiveDeconeComplementIso, Iso.trans_hom, Iso.symm_hom, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineSpaceCoord,
    complementIsoSpec_inv_appTop_complementι_appTop, projectiveDeconeIso_hom_appTop]

/-! ### In a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k) [FiniteDimensional k W]

/-- The canonical projection `q : V_P → U_P` from the complement `V_P = U_{cone P}` of the cone, in
a domain `D`: `s_{cone P}` followed by `coneToProjectiveComplement`.

Blueprint: `thm:geo-projective-geometry`. -/
def coneComplementProjection : D.complement P.cone ⟶ D.projectiveComplement P :=
  (D.complementIsoSpec P.cone).hom ≫ D.coneToProjectiveComplement P

lemma coneComplementProjection_hom :
    (D.coneComplementProjection (P := P)).hom = Geometric.coneComplementProjection P :=
  rfl

/-- Under `s_{cone P}` and `s_P`, the projection `q : V_P → U_P` is `Spec` of the existing
`projectiveToCone`. This is the square along which a structure theorem on `U_P` commutes with
pullback to the complement of the cone.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc (attr := simp)]
lemma coneComplementProjection_comp_projectiveComplementIsoSpec_hom :
    D.coneComplementProjection (P := P) ≫ (D.projectiveComplementIsoSpec P).hom =
      (D.complementIsoSpec P.cone).hom ≫
        (D.specFunctor.map (SmoothAlg.projectiveToCone P)).unop := by
  rw [coneComplementProjection, Category.assoc,
    coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom]

/-- The isomorphism `V_P ≅ U_P ×_S 𝔾ₘ` for the complement `V_P = U_{cone P}` of the cone, in a
domain `D`, for an equation `ℓ₀` of a hyperplane of `P`.

Blueprint: `thm:geo-projective-geometry`. -/
def coneComplementIsoProdGm (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    D.complement P.cone ≅ D.prodGm (D.projectiveComplement P) :=
  D.complementIsoSpec P.cone ≪≫ D.coneIsoProdGm hℓ₀

/-- The first coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` is the canonical projection `q`.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc (attr := simp)]
lemma coneComplementIsoProdGm_hom_prodGmFst (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.coneComplementIsoProdGm hℓ₀).hom ≫ D.prodGmFst (D.projectiveComplement P) =
      D.coneComplementProjection :=
  ObjectProperty.hom_ext _ (Geometric.coneComplementIsoProdGm_hom_fst hℓ₀)

/-- The isomorphism `U_P ≅ U_{decone_{ℓ₀} P}` with the complement of the decone, in a domain `D`:
`s_P`, then `Spec` of the existing `SmoothAlg.deconeIso`, then `s_{decone P}⁻¹`.

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveDeconeComplementIso (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    D.projectiveComplement P ≅ D.complement (P.decone ℓ₀) :=
  D.projectiveDeconeIso hℓ₀ ≪≫ (D.complementIsoSpec (P.decone ℓ₀)).symm

/-- Under `s_P` and `s_{decone P}`, the decone isomorphism is `Spec` of the existing
`SmoothAlg.deconeIso`.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc]
lemma projectiveDeconeComplementIso_hom_comp_complementIsoSpec_hom
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.projectiveDeconeComplementIso hℓ₀).hom ≫ (D.complementIsoSpec (P.decone ℓ₀)).hom =
      (D.projectiveComplementIsoSpec P).hom ≫
        (D.specFunctor.map (SmoothAlg.deconeIso hℓ₀).inv).unop := by
  rw [projectiveDeconeComplementIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, projectiveDeconeIso_hom]

end SmoothDomain

end OrlikSolomon.Geometric
