/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.RelationTargets
public import OrlikSolomon.Geometry.Schemes.Complement.Basic

/-!
# The small relation targets as scheme morphisms

This file realizes `thm:geo-small-targets` of the geometric refactor blueprint. The two targets of
`lem:small-targets` are complements `Y` of arrangements, so they are smooth affine schemes by
`Geometry/Schemes/Complement/Basic`, and the existing ring maps `toAffineImageRing` and
`toNormalizedSliceRing` become morphisms `U_𝒜 → Y` through the comparisons `s`.

* If `f₁, …, fₛ` have no common zero, `affineImageMap 𝒜 f hf : U_𝒜 → W ∩ 𝔾ₘˢ` pulls back the
  coordinate `yᵢ` to `fᵢ`, and factors `(f₁, …, fₛ) : U_𝒜 → 𝔸ˢ` through the affine image `W`. Its
  target lives on `W.direction`, of dimension less than `s` by the existing
  `finrank_direction_affineImage_lt`.
* If `f₀, …, fₛ` have a common zero, `normalizedSliceMap 𝒜 f hf hX : U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹` pulls back
  `yᵢ` to `fᵢ / f₀`. Its target lives on `W₁.direction`, of dimension `r - 1` by the existing
  `finrank_direction_normalizedSlice_add_one`.

These are identities of global functions on `U_𝒜`, and no `k`-point is involved.

## Main definitions

* `Geometric.affineImageMap`, `Geometric.normalizedSliceMap`: the two morphisms, and their forms
  `SmoothDomain.affineImageMap`, `SmoothDomain.normalizedSliceMap` in an admissible domain.

## Main results

* `affineImageMap_comp_complementIsoSpec_hom`, `normalizedSliceMap_comp_complementIsoSpec_hom`, and
  the domain forms: under the comparisons, the morphisms are `Spec` of the existing ring maps.
* `affineImageMap_appTop`, `normalizedSliceMap_appTop`: the pullback formulas `yᵢ ↦ fᵢ` and
  `yᵢ ↦ fᵢ / f₀`.
* `affineImageMap_comp_complementι`: the factorization through the affine image.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric

open CoordinateRing Arrangement Arrangement.ComplementRing

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V] {s : ℕ}
variable (𝒜 : Arrangement k V)

/-! ### The affine image -/

section AffineImage

variable (f : Fin s → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))

/-- The morphism `(f₁, …, fₛ) : U_𝒜 → W ∩ 𝔾ₘˢ` to the complement of the torus section of the affine
image `W` of the `fᵢ`: `Spec` of the existing `toAffineImageRing` under the comparisons.

Blueprint: `thm:geo-small-targets`. -/
def affineImageMap : complement 𝒜 ⟶ complement (torusSection (affineImage f)) :=
  complementHom (toAffineImageRing 𝒜 f hf)

/-- Under the comparisons, `affineImageMap` is `Spec` of the existing `toAffineImageRing`.

Blueprint: `thm:geo-small-targets`. -/
@[reassoc (attr := simp)]
lemma affineImageMap_comp_complementIsoSpec_hom :
    affineImageMap 𝒜 f hf ≫ (complementIsoSpec _).hom =
      (complementIsoSpec 𝒜).hom ≫ specMap (CommAlgCat.ofHom (toAffineImageRing 𝒜 f hf)) :=
  complementHom_comp_complementIsoSpec_hom _

/-- The morphism `(f₁, …, fₛ) : U_𝒜 → 𝔸ˢ` factors through `U_𝒜 → W ∩ 𝔾ₘˢ` and the inclusion of the
affine image `W`.

Blueprint: `thm:geo-small-targets`. -/
@[reassoc]
lemma affineImageMap_comp_complementι :
    affineImageMap 𝒜 f hf ≫ complementι _ ≫ affineSpaceMap k (chart (affineImage f)) =
      complementι 𝒜 ≫ affineSpaceMap k (AffineMap.pi f) := by
  rw [affineImageMap, complementHom_comp_complementι_assoc, ← complementIsoSpec_hom_comp 𝒜,
    Category.assoc, affineSpaceMap, affineSpaceMap, ← specMap_comp, ← specMap_comp]
  congr 2
  exact CommAlgCat.hom_ext (AlgHom.ext fun x ↦ toAffineImageRing_algebraMap_pull_chart 𝒜 f hf x)

/-- `U_𝒜 → W ∩ 𝔾ₘˢ` pulls back the coordinate `yᵢ` of the target to the restriction of `fᵢ`.

Blueprint: `thm:geo-small-targets`. -/
lemma affineImageMap_appTop (i : Fin s) :
    (affineImageMap 𝒜 f hf).left.appTop ((complementι _).left.appTop
        (affineSpaceCoord ((yCoord k i).comp (chart (affineImage f))))) =
      (complementι 𝒜).left.appTop (affineSpaceCoord (f i)) := by
  rw [affineImageMap, affineSpaceCoord, complementHom_appTop,
    toAffineImageRing_algebraMap_coord, complementIsoSpec_hom_appTop_coord]

end AffineImage

/-! ### The normalized slice -/

section NormalizedSlice

variable (f : Fin (s + 1) → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))
  (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥)

/-- The morphism `(f₀ / f₀, …, fₛ / f₀) : U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹` to the complement of the torus section
of the normalized slice `W₁`, for functions with a common zero: `Spec` of the existing
`toNormalizedSliceRing` under the comparisons. It is not induced by an affine map.

Blueprint: `thm:geo-small-targets`. -/
def normalizedSliceMap : complement 𝒜 ⟶ complement (torusSection (normalizedSlice f)) :=
  complementHom (toNormalizedSliceRing 𝒜 f hf hX)

/-- Under the comparisons, `normalizedSliceMap` is `Spec` of the existing `toNormalizedSliceRing`.

Blueprint: `thm:geo-small-targets`. -/
@[reassoc (attr := simp)]
lemma normalizedSliceMap_comp_complementIsoSpec_hom :
    normalizedSliceMap 𝒜 f hf hX ≫ (complementIsoSpec _).hom =
      (complementIsoSpec 𝒜).hom ≫ specMap (CommAlgCat.ofHom (toNormalizedSliceRing 𝒜 f hf hX)) :=
  complementHom_comp_complementIsoSpec_hom _

/-- `U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹` pulls back the coordinate `yᵢ` of the target to `fᵢ / f₀` on `U_𝒜`, using
the inverse of the unit `f₀`.

Blueprint: `thm:geo-small-targets`. -/
lemma normalizedSliceMap_appTop (i : Fin (s + 1)) :
    (normalizedSliceMap 𝒜 f hf hX).left.appTop ((complementι _).left.appTop
        (affineSpaceCoord ((yCoord k i).comp (chart (normalizedSlice f))))) =
      (complementι 𝒜).left.appTop (affineSpaceCoord (f i)) *
        ((complementUnit 𝒜 (f 0) (hf 0))⁻¹ : Γ((complement 𝒜).left, ⊤)ˣ) := by
  let φ : 𝒜.ComplementRing →+* Γ((complement 𝒜).left, ⊤) :=
    (complementIsoSpec 𝒜).hom.left.appTop.hom.comp (Scheme.ΓSpecIso (.of 𝒜.ComplementRing)).inv.hom
  have hu : Units.map φ (isUnit_coord (hf 0)).unit = complementUnit 𝒜 (f 0) (hf 0) :=
    Units.ext (complementIsoSpec_hom_appTop_coord (f 0))
  rw [normalizedSliceMap, affineSpaceCoord, complementHom_appTop,
    toNormalizedSliceRing_algebraMap_coord, ← hu, Units.coe_map_inv]
  exact (map_mul φ _ _).trans (congrArg (· * _) (complementIsoSpec_hom_appTop_coord (f i)))

end NormalizedSlice

/-! ### In a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k) [FiniteDimensional k V]

/-- The morphism `U_𝒜 → W ∩ 𝔾ₘˢ` of the first relation target, in a domain `D`.

Blueprint: `thm:geo-small-targets`. -/
def affineImageMap (f : Fin s → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i))) :
    D.complement 𝒜 ⟶ D.complement (torusSection (affineImage f)) :=
  ObjectProperty.homMk (Geometric.affineImageMap 𝒜 f hf)

/-- Under the comparisons, `D.affineImageMap` is `Spec` of the existing `toAffineImage`.

Blueprint: `thm:geo-small-targets`. -/
@[reassoc (attr := simp)]
lemma affineImageMap_comp_complementIsoSpec_hom (f : Fin s → V →ᵃ[k] k)
    (hf : ∀ i, 𝒜.Covers (zeroLocus (f i))) :
    D.affineImageMap 𝒜 f hf ≫ (D.complementIsoSpec _).hom =
      (D.complementIsoSpec 𝒜).hom ≫ (D.specFunctor.map (toAffineImage 𝒜 f hf)).unop :=
  ObjectProperty.hom_ext _ (Geometric.affineImageMap_comp_complementIsoSpec_hom 𝒜 f hf)

/-- The morphism `U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹` of the second relation target, in a domain `D`.

Blueprint: `thm:geo-small-targets`. -/
def normalizedSliceMap (f : Fin (s + 1) → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))
    (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    D.complement 𝒜 ⟶ D.complement (torusSection (normalizedSlice f)) :=
  ObjectProperty.homMk (Geometric.normalizedSliceMap 𝒜 f hf hX)

/-- Under the comparisons, `D.normalizedSliceMap` is `Spec` of the existing `toNormalizedSlice`.

Blueprint: `thm:geo-small-targets`. -/
@[reassoc (attr := simp)]
lemma normalizedSliceMap_comp_complementIsoSpec_hom (f : Fin (s + 1) → V →ᵃ[k] k)
    (hf : ∀ i, 𝒜.Covers (zeroLocus (f i))) (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    D.normalizedSliceMap 𝒜 f hf hX ≫ (D.complementIsoSpec _).hom =
      (D.complementIsoSpec 𝒜).hom ≫ (D.specFunctor.map (toNormalizedSlice 𝒜 f hf hX)).unop :=
  ObjectProperty.hom_ext _ (Geometric.normalizedSliceMap_comp_complementIsoSpec_hom 𝒜 f hf hX)

end SmoothDomain

end OrlikSolomon.Geometric
