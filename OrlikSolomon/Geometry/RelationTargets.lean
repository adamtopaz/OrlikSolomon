/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Complement

/-!
# The two low-dimensional targets of the relations

For affine functions on `V` that are units on `U_𝒜`, this file constructs the two targets through
which these units factor, as used to show that the Orlik-Solomon relations hold in cohomology. Each
is the complement of an arrangement on a space of small dimension, so the dimension bound of
`thm:generation` applies to it, with no comparison between its number of hyperplanes and `|𝒜|`.

* If `f₁, …, fₛ` have no common zero, then their affine image `W ⊆ 𝔸ˢ` avoids `0` and has dimension
  less than `s`, and the `fᵢ` give a map from `U_𝒜` to `W ∩ 𝔾ₘˢ`.
* If `f₀, …, fₛ` have a common zero, of codimension `r`, then their image `W ⊆ 𝔸ˢ⁺¹` is a linear
  space of dimension `r`, and the fractions `fᵢ / f₀` give a map from `U_𝒜` to `W₁ ∩ 𝔾ₘˢ⁺¹`, where
  the slice `W₁ = W ∩ {y₀ = 1}` has dimension `r - 1`.

The blueprint numbers the functions from `1` in both cases, so its condition `r < s` in the second
case is `r < s + 1` here. The first map is affine and the second is not. Neither refers to
`k`-points of `U_𝒜`, of which there may be none: the maps are `k`-algebra maps on coordinate rings,
and the only points that occur are points of `V` and of `𝔸ˢ`, in the linear algebra of `W` and `W₁`.

## Main definitions

* `OrlikSolomon.coordinateArrangement`: the coordinate hyperplanes of `𝔸ˢ`.
* `OrlikSolomon.torusSection X`: the arrangement on `X.direction` whose complement is `X ∩ 𝔾ₘˢ`, for
  an affine subspace `X` of `𝔸ˢ`, with its units `OrlikSolomon.torusUnit` and the maps out of its
  coordinate ring `OrlikSolomon.torusLift`.
* `OrlikSolomon.affineImage f`, `OrlikSolomon.normalizedSlice f`: the subspaces `W` and `W₁`.
* `OrlikSolomon.toAffineImage`, `OrlikSolomon.toNormalizedSlice`: the maps `O(W ∩ 𝔾ₘˢ) ⟶ O(U_𝒜)`
  and `O(W₁ ∩ 𝔾ₘˢ⁺¹) ⟶ O(U_𝒜)`.
* `OrlikSolomon.RelationTarget`: what the relations need to know about a target, namely a list of
  units of `O(U_𝒜)` factoring through a complement of dimension smaller than their number.

## Main results

* `OrlikSolomon.isLocalization_torusSection`: the complement of `torusSection X` is `X ∩ 𝔾ₘˢ`, if no
  coordinate vanishes on all of `X`. `OrlikSolomon.not_affineImage_le_zeroLocus` and
  `OrlikSolomon.not_normalizedSlice_le_zeroLocus` show this for the two targets.
* `OrlikSolomon.zero_notMem_affineImage`, `OrlikSolomon.finrank_direction_affineImage_lt`: the first
  target avoids `0` and has dimension less than `s`.
* `OrlikSolomon.mem_affineImage_iff_mem_direction`, `OrlikSolomon.finrank_direction_affineImage`:
  in the second case the image is a linear space, of dimension the codimension of the common zero
  locus.
* `OrlikSolomon.finrank_direction_normalizedSlice_add_one`: the slice has dimension `r - 1`.
* `OrlikSolomon.mapUnits_toAffineImage_torusUnit`,
  `OrlikSolomon.mapUnits_toNormalizedSlice_torusUnit`: the coordinate `yᵢ` pulls back to the unit
  `fᵢ` and to the unit `fᵢ / f₀`.
* `OrlikSolomon.RelationTarget.ofInterEqBot`, `OrlikSolomon.RelationTarget.ofDependent`: the targets
  for a list of hyperplanes of `𝒜`, in the form that the Orlik-Solomon relations ask for.

## Implementation notes

Both targets are complements of a `torusSection`, so "discarding empty coordinate sections and
duplicates" is built into `Arrangement.comap`, and both maps are `torusLift` of a map out of
`O(𝔸ˢ)`. The maps are built on the ring level, with `ofHom` applied last, as `Geometry/Complement`
explains.

Consumers should use `RelationTarget`. A list `us` of units with such a target `t` has
`word logClass us = 0`: rewrite with `t.map_units` and `word_map`, and apply the pullback along
`t.map` to `word logClass t.units = 0`, which is the dimension bound, by
`RelationTarget.finrank_lt_length_units`. It is a list of units rather than a family because the
relations of `def:os` are stated for words in hyperplanes, and `word_map` passes between
`word x (I.map g)` and `word (fun H ↦ x (g H)) I`.

## Blueprint

`lem:small-targets`, and the maps to affine images and normalized slices of `lem:geometry-adapter`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Module

universe u

namespace OrlikSolomon

open CoordinateRing Arrangement SmoothAlg

open Arrangement.ComplementRing (isUnit_coord toComplementRing)

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V] {s : ℕ}

/-! ### Coordinates on `𝔸ˢ` -/

section Coordinates

variable (k) in
/-- The coordinate function `yᵢ` on `𝔸ˢ`. -/
abbrev yCoord (i : Fin s) : (Fin s → k) →ᵃ[k] k :=
  AffineMap.proj i

theorem yCoord_linear_ne_zero (i : Fin s) : (yCoord k i).linear ≠ 0 := by
  classical
  intro h
  simpa using LinearMap.congr_fun h (Pi.single i 1)

variable (k s) in
/-- The arrangement of the coordinate hyperplanes of `𝔸ˢ`, whose complement is `𝔾ₘˢ`. -/
def coordinateArrangement : Arrangement k (Fin s → k) :=
  open scoped Classical in
  ofFinset (Finset.univ.image fun i ↦ zeroLocus (yCoord k i))

@[simp]
theorem mem_coordinateArrangement {H : AffineSubspace k (Fin s → k)} :
    H ∈ coordinateArrangement k s ↔ ∃ i, zeroLocus (yCoord k i) = H := by
  classical
  simp only [coordinateArrangement, mem_ofFinset, Finset.mem_image, Finset.mem_univ, true_and,
    and_iff_left_iff_imp]
  rintro ⟨i, rfl⟩
  exact isHyperplane_zeroLocus_iff.2 (yCoord_linear_ne_zero i)

theorem zeroLocus_yCoord_mem (i : Fin s) : zeroLocus (yCoord k i) ∈ coordinateArrangement k s :=
  mem_coordinateArrangement.2 ⟨i, rfl⟩

/-- The value of the map `v ↦ G v / u` on a coordinate, when `G = (f₁, …, fₛ)`. -/
theorem fraction_coord_yCoord {B : Type*} [CommRing B] [Algebra k B]
    (φ : CoordinateRing k V →ₐ[k] B) (f : Fin s → V →ᵃ[k] k) (u : Bˣ) (i : Fin s) :
    fraction φ (AffineMap.pi f) u (coord (yCoord k i)) = φ (coord (f i)) * ((u⁻¹ : Bˣ) : B) := by
  have : (LinearMap.proj i : (Fin s → k) →ₗ[k] k).toAffineMap.comp (AffineMap.pi f) = f i := by
    ext v
    simp
  simp [fraction_coord, this]

end Coordinates

/-! ### Sections of `𝔾ₘˢ` by an affine subspace -/

section TorusSection

variable {X : AffineSubspace k (Fin s → k)} {i : Fin s}

/-- The arrangement on `X.direction`, identified with `X` through `chart X`, whose complement is
`X ∩ 𝔾ₘˢ`. It consists of the coordinate sections of `X`, discarding those that are empty or all of
`X`, and discarding duplicates: see `mem_torusSection`.

A coordinate that vanishes on all of `X` makes `X ∩ 𝔾ₘˢ` empty, which this arrangement does not see.
So its complement is `X ∩ 𝔾ₘˢ` only if no coordinate vanishes on all of `X`, in the sense of
`isLocalization_torusSection`. This holds for the two targets, by `not_affineImage_le_zeroLocus` and
`not_normalizedSlice_le_zeroLocus`.

Blueprint: `lem:small-targets`. -/
def torusSection (X : AffineSubspace k (Fin s → k)) : Arrangement k X.direction :=
  (coordinateArrangement k s).restriction X

@[simp]
theorem mem_torusSection {L : AffineSubspace k X.direction} :
    L ∈ torusSection X ↔ IsHyperplane L ∧ ∃ i, zeroLocus ((yCoord k i).comp (chart X)) = L := by
  simp only [torusSection, mem_restriction', mem_coordinateArrangement, exists_exists_eq_and,
    zeroLocus_comp]

theorem ne_bot_of_not_le_zeroLocus (h : ¬X ≤ zeroLocus (yCoord k i)) : X ≠ ⊥ := by
  rintro rfl
  exact h bot_le

/-- A coordinate that does not vanish on all of `X` is a unit on `X ∩ 𝔾ₘˢ`: its section is either
empty, and it is then a nonzero constant, or a hyperplane of `torusSection X`. -/
theorem covers_torusSection (h : ¬X ≤ zeroLocus (yCoord k i)) :
    (torusSection X).Covers (zeroLocus ((yCoord k i).comp (chart X))) := by
  rw [zeroLocus_comp]
  exact covers_comap_comap (zeroLocus_yCoord_mem i)
    (mt (comap_chart_eq_top_iff (ne_bot_of_not_le_zeroLocus h)).1 h)

/-- The coordinate `yᵢ` as a unit of `O(X ∩ 𝔾ₘˢ)`, when it does not vanish on all of `X`. -/
def torusUnit (X : AffineSubspace k (Fin s → k)) (i : Fin s) (h : ¬X ≤ zeroLocus (yCoord k i)) :
    (complement (torusSection X))ˣ :=
  complementUnit _ ((yCoord k i).comp (chart X)) (covers_torusSection h)

@[simp]
theorem coe_torusUnit (h : ¬X ≤ zeroLocus (yCoord k i)) :
    (torusUnit X i h : complement (torusSection X)) =
      toComplement _ (affineCoord ((yCoord k i).comp (chart X))) :=
  rfl

/-- If no coordinate vanishes on all of `X`, then the coordinate ring of the complement of
`torusSection X` is the localization of `O(X)` at the coordinates. For nonempty `X`, this says that
the complement is `X ∩ 𝔾ₘˢ`, whichever coordinate sections were discarded.

Blueprint: `lem:small-targets`. -/
theorem isLocalization_torusSection (h : ∀ i, ¬X ≤ zeroLocus (yCoord k i)) :
    IsLocalization (Submonoid.closure (Set.range fun i ↦ coord ((yCoord k i).comp (chart X))))
      (torusSection X).ComplementRing := by
  refine ComplementRing.isLocalization_of_exists_dvd _ (fun m hm ↦ ?_) fun L hL ↦ ?_
  · induction hm using Submonoid.closure_induction with
    | mem _ hy =>
      obtain ⟨i, rfl⟩ := hy
      exact isUnit_coord (covers_torusSection (h i))
    | one => simp
    | mul _ _ _ _ hx hy => simpa using hx.mul hy
  · obtain ⟨hL', i, rfl⟩ := mem_torusSection.1 hL
    exact ⟨_, isEquation_zeroLocus (isHyperplane_zeroLocus_iff.1 hL'), _,
      Submonoid.subset_closure ⟨i, rfl⟩, dvd_rfl⟩

variable {B : Type*} [CommRing B] [Algebra k B]

/-- A map to `𝔸ˢ` that lands in `X` and in `𝔾ₘˢ` is a map to `X ∩ 𝔾ₘˢ`. On the level of rings, a map
out of `O(𝔸ˢ)` extends to `O(X ∩ 𝔾ₘˢ)` as soon as it kills the affine functions vanishing on `X`,
and makes every coordinate a unit. No `k`-points of the source are involved. -/
def torusLift (hX : X ≠ ⊥) (g : CoordinateRing k (Fin s → k) →ₐ[k] B)
    (hg : ∀ a : (Fin s → k) →ᵃ[k] k, (∀ x ∈ X, a x = 0) → g (coord a) = 0)
    (hu : ∀ i, IsUnit (g (coord (yCoord k i)))) : (torusSection X).ComplementRing →ₐ[k] B :=
  ComplementRing.lift _ (liftChart hX ⟨g, hg⟩) fun L hL ↦ by
    obtain ⟨hL', i, rfl⟩ := mem_torusSection.1 hL
    refine ⟨_, isEquation_zeroLocus (isHyperplane_zeroLocus_iff.1 hL'), ?_⟩
    rw [← pull_coord, liftChart_pull_chart]
    exact hu i

@[simp]
theorem torusLift_algebraMap_pull_chart (hX : X ≠ ⊥) (g : CoordinateRing k (Fin s → k) →ₐ[k] B)
    (hg : ∀ a : (Fin s → k) →ᵃ[k] k, (∀ x ∈ X, a x = 0) → g (coord a) = 0)
    (hu : ∀ i, IsUnit (g (coord (yCoord k i)))) (x : CoordinateRing k (Fin s → k)) :
    torusLift hX g hg hu (algebraMap _ _ (pull (chart X) x)) = g x := by
  rw [torusLift, ComplementRing.lift_algebraMap, liftChart_pull_chart]

/-- The map `torusLift` sends the coordinate `yᵢ` of `X` to the image of `yᵢ`. -/
theorem torusLift_algebraMap_coord (hX : X ≠ ⊥) (g : CoordinateRing k (Fin s → k) →ₐ[k] B)
    (hg : ∀ a : (Fin s → k) →ᵃ[k] k, (∀ x ∈ X, a x = 0) → g (coord a) = 0)
    (hu : ∀ i, IsUnit (g (coord (yCoord k i)))) (i : Fin s) :
    torusLift hX g hg hu (algebraMap _ _ (coord ((yCoord k i).comp (chart X)))) =
      g (coord (yCoord k i)) := by
  rw [← pull_coord, torusLift_algebraMap_pull_chart]

end TorusSection

/-! ### The affine image -/

section AffineImage

variable {f : Fin s → V →ᵃ[k] k} {x : Fin s → k}

/-- The affine image `W ⊆ 𝔸ˢ` of the map `(f₁, …, fₛ) : V → 𝔸ˢ`.

Blueprint: `lem:small-targets`. -/
def affineImage (f : Fin s → V →ᵃ[k] k) : AffineSubspace k (Fin s → k) :=
  (⊤ : AffineSubspace k V).map (AffineMap.pi f)

@[simp]
theorem mem_affineImage : x ∈ affineImage f ↔ ∃ v, AffineMap.pi f v = x := by
  simp [affineImage]

@[simp]
theorem pi_mem_affineImage (f : Fin s → V →ᵃ[k] k) (v : V) : AffineMap.pi f v ∈ affineImage f :=
  mem_affineImage.2 ⟨v, rfl⟩

theorem affineImage_ne_bot (f : Fin s → V →ᵃ[k] k) : affineImage f ≠ ⊥ :=
  (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨_, pi_mem_affineImage f 0⟩

/-- The image contains `0` exactly when the functions have a common zero. -/
theorem zero_mem_affineImage_iff : 0 ∈ affineImage f ↔ (⨅ i, zeroLocus (f i)) ≠ ⊥ := by
  simp only [mem_affineImage, ← AffineSubspace.nonempty_iff_ne_bot, funext_iff, AffineMap.pi_apply,
    Pi.zero_apply]
  exact ⟨fun ⟨v, hv⟩ ↦ ⟨v, mem_iInf_zeroLocus.2 hv⟩, fun ⟨v, hv⟩ ↦ ⟨v, mem_iInf_zeroLocus.1 hv⟩⟩

/-- If the functions have no common zero, then their image avoids `0`.

Blueprint: `lem:small-targets`. -/
theorem zero_notMem_affineImage (h : (⨅ i, zeroLocus (f i)) = ⊥) : 0 ∉ affineImage f :=
  fun h0 ↦ zero_mem_affineImage_iff.1 h0 h

/-- If the functions have no common zero, then their image has dimension less than `s`: otherwise it
would be all of `𝔸ˢ`, which contains `0`.

Blueprint: `lem:small-targets`. -/
theorem finrank_direction_affineImage_lt (h : (⨅ i, zeroLocus (f i)) = ⊥) :
    finrank k (affineImage f).direction < s := by
  have hd : (affineImage f).direction ≠ ⊤ := fun hd ↦ zero_notMem_affineImage h <| by
    rw [(AffineSubspace.direction_eq_top_iff_of_nonempty
      ((AffineSubspace.nonempty_iff_ne_bot _).2 (affineImage_ne_bot f))).1 hd]
    exact AffineSubspace.mem_top _ _ _
  simpa using Submodule.finrank_lt hd

/-- If the functions have a common zero, then their image is a linear subspace of `𝔸ˢ`, namely its
own direction. The blueprint translates a common zero to the origin of `V`, which does not change
the image: it contains `0` because it is the image of that point.

Blueprint: `lem:small-targets`. -/
theorem mem_affineImage_iff_mem_direction (h : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    x ∈ affineImage f ↔ x ∈ (affineImage f).direction := by
  simpa using (AffineSubspace.vsub_right_mem_direction_iff_mem
    (zero_mem_affineImage_iff.2 h) x).symm

/-- If the functions have a common zero, then their image has dimension the codimension `r` of the
common zero locus.

Blueprint: `lem:small-targets`. -/
theorem finrank_direction_affineImage [FiniteDimensional k V] (h : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    finrank k (affineImage f).direction = codim (⨅ i, zeroLocus (f i)) := by
  have hrange : (affineImage f).direction = LinearMap.range (AffineMap.pi f).linear := by
    rw [affineImage, AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  have hker : LinearMap.ker (AffineMap.pi f).linear = (⨅ i, zeroLocus (f i)).direction := by
    rw [direction_iInf_zeroLocus h, AffineMap.pi_linear, LinearMap.ker_pi]
  have h1 := LinearMap.finrank_range_add_finrank_ker (AffineMap.pi f).linear
  have h2 := codim_add_finrank_direction (⨅ i, zeroLocus (f i))
  rw [hker, ← hrange] at h1
  omega

/-- The image of a family does not lie in the hyperplane of a coordinate whose function is not
zero. Hence the section of the image by that coordinate is empty or a hyperplane of it.

Blueprint: `lem:small-targets`. -/
theorem not_affineImage_le_zeroLocus {i : Fin s} (h : f i ≠ 0) :
    ¬affineImage f ≤ zeroLocus (yCoord k i) := fun hle ↦ h <| AffineMap.ext fun v ↦ by
  simpa using hle (pi_mem_affineImage f v)

end AffineImage

/-! ### The normalized slice -/

section NormalizedSlice

variable {f : Fin (s + 1) → V →ᵃ[k] k} {x : Fin (s + 1) → k}

variable (k s) in
/-- The hyperplane `{y₀ = 1}` of `𝔸ˢ⁺¹`. -/
def levelOne : AffineSubspace k (Fin (s + 1) → k) :=
  zeroLocus (yCoord k 0 - AffineMap.const k _ 1)

@[simp]
theorem mem_levelOne : x ∈ levelOne k s ↔ x 0 = 1 := by
  simp [levelOne, sub_eq_zero]

theorem isHyperplane_levelOne : IsHyperplane (levelOne k s) :=
  isHyperplane_zeroLocus_iff.2 <| by simpa using yCoord_linear_ne_zero (k := k) (0 : Fin (s + 1))

/-- The slice `W₁ = W ∩ {y₀ = 1}` of the affine image of `(f₀, …, fₛ)`.

Blueprint: `lem:small-targets`. -/
def normalizedSlice (f : Fin (s + 1) → V →ᵃ[k] k) : AffineSubspace k (Fin (s + 1) → k) :=
  affineImage f ⊓ levelOne k s

@[simp]
theorem mem_normalizedSlice : x ∈ normalizedSlice f ↔ x ∈ affineImage f ∧ x 0 = 1 := by
  simp [normalizedSlice, AffineSubspace.mem_inf_iff]

/-- The first function takes the value `1` on the slice, as soon as it is not constant. -/
theorem normalizedSlice_ne_bot (h₀ : (f 0).linear ≠ 0) : normalizedSlice f ≠ ⊥ := by
  have : (f 0 - AffineMap.const k V 1).linear ≠ 0 := by simpa using h₀
  obtain ⟨v, hv⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 (zeroLocus_ne_bot this)
  refine (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨_, mem_normalizedSlice.2
    ⟨pi_mem_affineImage f v, ?_⟩⟩
  simpa [sub_eq_zero] using hv

/-- A common zero makes the image linear, so it is spanned by the slice: an affine function `g`
vanishing on the slice has a homogenization `g.linear + g 0 • y₀` vanishing on the whole image. -/
theorem linear_add_mul_eq_zero_of_forall_mem_normalizedSlice
    (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) (h₀ : (f 0).linear ≠ 0) {g : (Fin (s + 1) → k) →ᵃ[k] k}
    (hg : ∀ y ∈ normalizedSlice f, g y = 0) (hx : x ∈ affineImage f) :
    g.linear x + g 0 * x 0 = 0 := by
  have hdir {y : Fin (s + 1) → k} := mem_affineImage_iff_mem_direction (x := y) hX
  have hslice {y : Fin (s + 1) → k} (hy : y ∈ normalizedSlice f) : g.linear y + g 0 * y 0 = 0 := by
    obtain ⟨-, hy0⟩ := mem_normalizedSlice.1 hy
    have := hg y hy
    rw [show g y = g.linear y + g 0 from by simpa using congrFun g.decomp y] at this
    simpa [hy0] using this
  obtain h | h := eq_or_ne (x 0) 0
  · obtain ⟨d, hd⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 (normalizedSlice_ne_bot h₀)
    obtain ⟨hdW, hd0⟩ := mem_normalizedSlice.1 hd
    have hxd : x + d ∈ normalizedSlice f := mem_normalizedSlice.2
      ⟨hdir.2 (Submodule.add_mem _ (hdir.1 hx) (hdir.1 hdW)), by simp [h, hd0]⟩
    have h1 := hslice hxd
    have h2 := hslice hd
    simp only [map_add, Pi.add_apply, h, hd0] at h1 h2 ⊢
    linear_combination h1 - h2
  · have hxs : (x 0)⁻¹ • x ∈ normalizedSlice f := mem_normalizedSlice.2
      ⟨hdir.2 (Submodule.smul_mem _ _ (hdir.1 hx)), by simp [h]⟩
    have := hslice hxs
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h, mul_one] at this
    have h2 : (x 0)⁻¹ * (g.linear x + g 0 * x 0) = 0 := by
      rw [← this]
      field_simp
    simpa [h] using h2

/-- A function that is not zero does not vanish on the slice, since the slice spans the image. Hence
the section of the slice by that coordinate is empty or a hyperplane of it.

Blueprint: `lem:small-targets`. -/
theorem not_normalizedSlice_le_zeroLocus (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥)
    (h₀ : (f 0).linear ≠ 0) {i : Fin (s + 1)} (h : f i ≠ 0) :
    ¬normalizedSlice f ≤ zeroLocus (yCoord k i) := fun hle ↦ h <| AffineMap.ext fun v ↦ by
  have := linear_add_mul_eq_zero_of_forall_mem_normalizedSlice hX h₀ (g := yCoord k i)
    (fun y hy ↦ by simpa using hle hy) (pi_mem_affineImage f v)
  simpa using this

/-- If the functions have a common zero locus of codimension `r` and `f₀` is not constant, then the
slice has dimension `r - 1`: the coordinate `y₀` is nonzero on the linear space `W`.

Blueprint: `lem:small-targets`. -/
theorem finrank_direction_normalizedSlice_add_one [FiniteDimensional k V]
    (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) (h₀ : (f 0).linear ≠ 0) :
    finrank k (normalizedSlice f).direction + 1 = codim (⨅ i, zeroLocus (f i)) := by
  have hnotle : ¬affineImage f ≤ levelOne k s := fun hle ↦ by
    simpa using hle (zero_mem_affineImage_iff.2 hX)
  have hcodim := isHyperplane_levelOne.codim_inf (X := affineImage f) (by
    rw [inf_comm]
    exact normalizedSlice_ne_bot h₀) hnotle
  rw [inf_comm] at hcodim
  have h1 := codim_add_finrank_direction (normalizedSlice f)
  have h2 := codim_add_finrank_direction (affineImage f)
  have h3 := finrank_direction_affineImage hX
  rw [normalizedSlice] at h1
  rw [normalizedSlice]
  omega

end NormalizedSlice

/-! ### The regular maps -/

section Maps

variable {𝒜 : Arrangement k V}

/-- A family with a common zero, whose zero loci are covered by an arrangement, consists of
equations: no member is constant. -/
theorem linear_ne_zero_of_iInf_ne_bot {ι : Sort*} {f : ι → V →ᵃ[k] k}
    (hf : ∀ i, 𝒜.Covers (zeroLocus (f i))) (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) (i : ι) :
    (f i).linear ≠ 0 :=
  (hf i).linear_ne_zero (ne_bot_of_le_ne_bot hX (iInf_le _ i))

/-- The chosen equations of a list of hyperplanes of `𝒜` have as common zero locus the intersection
of the list. -/
theorem iInf_zeroLocus_equation_get (I : List 𝒜) :
    (⨅ i : Fin I.length, zeroLocus (equation (I.get i : AffineSubspace k V))) = inter I := by
  rw [inter_eq_iInf_get]
  exact iInf_congr fun i ↦ (isEquation_equation (𝒜.isHyperplane (I.get i).2)).zeroLocus_eq

/-- The zero locus of the chosen equation of a hyperplane of `𝒜` is covered by `𝒜`. -/
theorem covers_zeroLocus_equation (H : 𝒜) :
    𝒜.Covers (zeroLocus (equation (H : AffineSubspace k V))) :=
  (isEquation_equation (𝒜.isHyperplane H.2)).covers H.2

section AffineImage

variable (𝒜) (f : Fin s → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))

/-- The map `O(W ∩ 𝔾ₘˢ) → O(U_𝒜)`, on the level of rings, given by `(f₁, …, fₛ) : U_𝒜 → W ∩ 𝔾ₘˢ`. -/
def toAffineImageRing : (torusSection (affineImage f)).ComplementRing →ₐ[k] 𝒜.ComplementRing :=
  torusLift (affineImage_ne_bot f) ((toComplementRing 𝒜).comp (pull (AffineMap.pi f)))
    (fun a ha ↦ by
      have : a.comp (AffineMap.pi f) = 0 := AffineMap.ext fun v ↦ ha _ (pi_mem_affineImage f v)
      simp [this])
    (fun i ↦ by simpa [AffineMap.proj_pi] using isUnit_coord (hf i))

/-- On functions on `𝔸ˢ`, the ring map to the affine image is the pullback along `(f₁, …, fₛ)`. -/
@[simp]
theorem toAffineImageRing_algebraMap_pull_chart (x : CoordinateRing k (Fin s → k)) :
    toAffineImageRing 𝒜 f hf (algebraMap _ _ (pull (chart (affineImage f)) x)) =
      algebraMap _ _ (pull (AffineMap.pi f) x) :=
  torusLift_algebraMap_pull_chart _ _ _ _ x

/-- The ring map to the affine image sends the coordinate `yᵢ` to `fᵢ`. -/
theorem toAffineImageRing_algebraMap_coord (i : Fin s) :
    toAffineImageRing 𝒜 f hf
        (algebraMap _ _ (coord ((yCoord k i).comp (chart (affineImage f))))) =
      algebraMap _ _ (coord (f i)) := by
  rw [← pull_coord, toAffineImageRing_algebraMap_pull_chart, pull_coord, AffineMap.proj_pi]

/-- The map `O(W ∩ 𝔾ₘˢ) ⟶ O(U_𝒜)` given by `(f₁, …, fₛ) : U_𝒜 → W ∩ 𝔾ₘˢ`, for the affine image `W`
of the `fᵢ`.

Blueprint: `lem:small-targets`, `lem:geometry-adapter`. -/
def toAffineImage [FiniteDimensional k V] :
    complement (torusSection (affineImage f)) ⟶ complement 𝒜 :=
  ofHom (toAffineImageRing 𝒜 f hf)

/-- The map to the affine image sends the coordinate `yᵢ` to the unit `fᵢ`.

Blueprint: `lem:small-targets`. -/
@[simp]
theorem mapUnits_toAffineImage_torusUnit [FiniteDimensional k V] (i : Fin s)
    (h : ¬affineImage f ≤ zeroLocus (yCoord k i)) :
    mapUnits (toAffineImage 𝒜 f hf) (torusUnit (affineImage f) i h) =
      complementUnit 𝒜 (f i) (hf i) :=
  Units.ext (toAffineImageRing_algebraMap_coord 𝒜 f hf i)

end AffineImage

section NormalizedSlice

variable (𝒜) (f : Fin (s + 1) → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))
  (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥)

/-- The map `O(W₁ ∩ 𝔾ₘˢ⁺¹) → O(U_𝒜)`, on the level of rings, given by
`(f₀ / f₀, …, fₛ / f₀) : U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹`. It is not affine: it is defined by `fraction`, and it
exists because `f₀` is a unit on `U_𝒜`, whether or not `U_𝒜` has `k`-points. -/
def toNormalizedSliceRing :
    (torusSection (normalizedSlice f)).ComplementRing →ₐ[k] 𝒜.ComplementRing :=
  torusLift (normalizedSlice_ne_bot (linear_ne_zero_of_iInf_ne_bot hf hX 0))
    (fraction (toComplementRing 𝒜) (AffineMap.pi f) (isUnit_coord (hf 0)).unit)
    (fun g hg ↦ by
      have h := fraction_coord_mul (toComplementRing 𝒜) (AffineMap.pi f) (u₀ := f 0)
        (isUnit_coord (hf 0)).unit (by simp) g
      have hz : g.linear.toAffineMap.comp (AffineMap.pi f) + g 0 • f 0 = 0 :=
        AffineMap.ext fun v ↦ by
          simpa using linear_add_mul_eq_zero_of_forall_mem_normalizedSlice hX
            (linear_ne_zero_of_iInf_ne_bot hf hX 0) hg (pi_mem_affineImage f v)
      rw [hz, map_zero, map_zero] at h
      exact (Units.mul_left_eq_zero _).1 h)
    (fun i ↦ by
      rw [fraction_coord_yCoord]
      exact (isUnit_coord (hf i)).mul (Units.isUnit _))

/-- On functions on `𝔸ˢ⁺¹`, the ring map to the slice is the map `v ↦ (f₀ v, …, fₛ v) / f₀ v`. -/
@[simp]
theorem toNormalizedSliceRing_algebraMap_pull_chart (x : CoordinateRing k (Fin (s + 1) → k)) :
    toNormalizedSliceRing 𝒜 f hf hX (algebraMap _ _ (pull (chart (normalizedSlice f)) x)) =
      fraction (toComplementRing 𝒜) (AffineMap.pi f) (isUnit_coord (hf 0)).unit x :=
  torusLift_algebraMap_pull_chart _ _ _ _ x

/-- The ring map to the slice sends the coordinate `yᵢ` to the fraction `fᵢ / f₀`. -/
theorem toNormalizedSliceRing_algebraMap_coord (i : Fin (s + 1)) :
    toNormalizedSliceRing 𝒜 f hf hX
        (algebraMap _ _ (coord ((yCoord k i).comp (chart (normalizedSlice f))))) =
      algebraMap _ _ (coord (f i)) * (((isUnit_coord (hf 0)).unit⁻¹ : 𝒜.ComplementRingˣ) :
        𝒜.ComplementRing) := by
  rw [← pull_coord, toNormalizedSliceRing_algebraMap_pull_chart, fraction_coord_yCoord]
  rfl

/-- The map `O(W₁ ∩ 𝔾ₘˢ⁺¹) ⟶ O(U_𝒜)` given by `(f₀ / f₀, …, fₛ / f₀) : U_𝒜 → W₁ ∩ 𝔾ₘˢ⁺¹`, for the
normalized slice `W₁` of the affine image of the `fᵢ`, which have a common zero.

Blueprint: `lem:small-targets`, `lem:geometry-adapter`. -/
def toNormalizedSlice [FiniteDimensional k V] :
    complement (torusSection (normalizedSlice f)) ⟶ complement 𝒜 :=
  ofHom (toNormalizedSliceRing 𝒜 f hf hX)

/-- The map to the slice sends the coordinate `yᵢ` to the unit `fᵢ / f₀`.

Blueprint: `lem:small-targets`. -/
@[simp]
theorem mapUnits_toNormalizedSlice_torusUnit [FiniteDimensional k V] (i : Fin (s + 1))
    (h : ¬normalizedSlice f ≤ zeroLocus (yCoord k i)) :
    mapUnits (toNormalizedSlice 𝒜 f hf hX) (torusUnit (normalizedSlice f) i h) =
      complementUnit 𝒜 (f i) (hf i) / complementUnit 𝒜 (f 0) (hf 0) :=
  Units.ext <| (toNormalizedSliceRing_algebraMap_coord 𝒜 f hf hX i).trans <| by
    rw [div_eq_mul_inv]
    rfl

end NormalizedSlice

end Maps

/-! ### The package used by the relations -/

section RelationTarget

variable [FiniteDimensional k V]

/-- A *relation target* for a list `us` of units of `O(U_𝒜)`: the units factor through the
complement of an arrangement on a space of dimension smaller than their number. By the dimension
bound of `thm:generation`, the product of the logarithmic classes of `us` then vanishes: it is
pulled back from a class of degree above the dimension.

This is what `lem:empty-relation` and `lem:dependent-relation` need to know about the two targets of
`lem:small-targets`, which `RelationTarget.ofInterEqBot` and `RelationTarget.ofDependent` provide.
The number of hyperplanes of `arrangement` has no relation to that of `𝒜`.

Blueprint: `lem:small-targets`. -/
structure RelationTarget (𝒜 : Arrangement k V) (us : List (complement 𝒜)ˣ) where
  /-- The ambient space of the target. -/
  space : Type u
  [addCommGroup : AddCommGroup space]
  [module : Module k space]
  [finiteDimensional : FiniteDimensional k space]
  /-- The arrangement whose complement is the target. -/
  arrangement : Arrangement k space
  /-- The target has dimension smaller than the number of units. -/
  finrank_lt : finrank k space < us.length
  /-- The regular map from `U_𝒜` to the target. -/
  map : complement arrangement ⟶ complement 𝒜
  /-- The units on the target. -/
  units : List (complement arrangement)ˣ
  /-- The units on the target pull back to the given units. -/
  map_units : units.map (mapUnits map) = us

attribute [instance] RelationTarget.addCommGroup RelationTarget.module
  RelationTarget.finiteDimensional

namespace RelationTarget

variable {𝒜 : Arrangement k V} {us us' : List (complement 𝒜)ˣ}

/-- The units on the target are as many as the given units, so more than its dimension. -/
theorem finrank_lt_length_units (t : RelationTarget 𝒜 us) :
    finrank k t.space < t.units.length := by
  have h := congrArg List.length t.map_units
  rw [List.length_map] at h
  exact h ▸ t.finrank_lt

/-- Transport along an equality of lists of units. -/
protected def congr (t : RelationTarget 𝒜 us) (h : us = us') : RelationTarget 𝒜 us' where
  space := t.space
  arrangement := t.arrangement
  finrank_lt := h ▸ t.finrank_lt
  map := t.map
  units := t.units
  map_units := t.map_units.trans h

/-- **The first target**, for a family: if `f₁, …, fₛ` have no common zero, then the units `fᵢ`
factor through `W ∩ 𝔾ₘˢ`, where `W` is their affine image, of dimension less than `s`.

Blueprint: `lem:small-targets`. -/
def ofAffineImage (f : Fin s → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))
    (h : (⨅ i, zeroLocus (f i)) = ⊥) :
    RelationTarget 𝒜 (List.ofFn fun i ↦ complementUnit 𝒜 (f i) (hf i)) where
  space := (affineImage f).direction
  arrangement := torusSection (affineImage f)
  finrank_lt := by simpa using finrank_direction_affineImage_lt h
  map := toAffineImage 𝒜 f hf
  units := List.ofFn fun i ↦
    torusUnit (affineImage f) i (not_affineImage_le_zeroLocus (hf i).ne_zero)
  map_units := by simp [List.map_ofFn, Function.comp_def]

/-- **The second target**, for a family: if `f₀, …, fₛ` have a common zero, of codimension `r ≤ s`,
then the units `fᵢ / f₀`, for `i` other than `0`, factor through `W₁ ∩ 𝔾ₘˢ⁺¹`, where `W₁` is the
normalized slice of their affine image, of dimension `r - 1 < s`.

Blueprint: `lem:small-targets`. -/
def ofNormalizedSlice (f : Fin (s + 1) → V →ᵃ[k] k) (hf : ∀ i, 𝒜.Covers (zeroLocus (f i)))
    (hX : (⨅ i, zeroLocus (f i)) ≠ ⊥) (hr : codim (⨅ i, zeroLocus (f i)) < s + 1) :
    RelationTarget 𝒜 (List.ofFn fun i : Fin s ↦
      complementUnit 𝒜 (f i.succ) (hf _) / complementUnit 𝒜 (f 0) (hf 0)) where
  space := (normalizedSlice f).direction
  arrangement := torusSection (normalizedSlice f)
  finrank_lt := by
    have := finrank_direction_normalizedSlice_add_one hX (linear_ne_zero_of_iInf_ne_bot hf hX 0)
    simp only [List.length_ofFn]
    omega
  map := toNormalizedSlice 𝒜 f hf hX
  units := List.ofFn fun i : Fin s ↦ torusUnit (normalizedSlice f) i.succ
    (not_normalizedSlice_le_zeroLocus hX (linear_ne_zero_of_iInf_ne_bot hf hX 0) (hf _).ne_zero)
  map_units := by simp [List.map_ofFn, Function.comp_def]

/-- **The first target**, for a list `I` of hyperplanes of `𝒜` with empty intersection, and their
chosen equations. This is the target of `lem:empty-relation`.

Blueprint: `lem:small-targets`. -/
def ofInterEqBot (I : List 𝒜) (h : inter I = ⊥) : RelationTarget 𝒜 (I.map (equationUnit 𝒜)) :=
  (ofAffineImage (fun i : Fin I.length ↦ equation (I.get i : AffineSubspace k V))
    (fun _ ↦ covers_zeroLocus_equation _) (by rw [iInf_zeroLocus_equation_get, h])).congr
    (List.ofFn_getElem_eq_map I (equationUnit 𝒜))

/-- **The second target**, for a list `H₀ :: J` of hyperplanes of `𝒜` with nonempty intersection of
codimension less than its length, and their chosen equations. This is the target of
`lem:dependent-relation`, whose boundary is the product over `J` of the classes `[f_H / f_{H₀}]`.

Blueprint: `lem:small-targets`. -/
def ofDependent (H₀ : 𝒜) (J : List 𝒜) (h₁ : inter (H₀ :: J) ≠ ⊥)
    (h₂ : codim (inter (H₀ :: J)) < (H₀ :: J).length) :
    RelationTarget 𝒜 (J.map fun H ↦ equationUnit 𝒜 H / equationUnit 𝒜 H₀) :=
  (ofNormalizedSlice (s := J.length)
    (fun i ↦ equation ((H₀ :: J).get i : AffineSubspace k V))
    (fun _ ↦ covers_zeroLocus_equation _)
    ((iInf_zeroLocus_equation_get (H₀ :: J)).trans_ne h₁)
    ((congrArg codim (iInf_zeroLocus_equation_get (H₀ :: J))).trans_lt h₂)).congr
    (List.ofFn_getElem_eq_map J fun H ↦ equationUnit 𝒜 H / equationUnit 𝒜 H₀)

end RelationTarget

end RelationTarget

end OrlikSolomon
