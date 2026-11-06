/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Arrangement

/-!
# Projective arrangements, cones and decones

A split projective arrangement is a finite set of codimension-one linear subspaces of a vector space
`W`, regarded as hyperplanes in the projectivization of `W`. This file contains the incidence side:
the central cone `cP`, an arrangement on `W`, and the decone `d_{H₀}P`, an arrangement on the slice
`ℓ₀ = 1` for an equation `ℓ₀` of `H₀ ∈ P`. It involves linear algebra over `k` only. The coordinate
rings are in `OrlikSolomon/Geometry/ProjectiveRing.lean` and
`OrlikSolomon/Geometry/Projective.lean`.

The blueprint writes `𝒫` for a projective arrangement. Mathlib reserves that symbol for the power
set, so the code writes `P`.

## Main definitions

* `OrlikSolomon.ProjectiveArrangement`: a finite set of hyperplanes of the vector space `W`.
* `ProjectiveArrangement.ofForms`: the arrangement of the kernels of a finite set of nonzero forms.
* `ProjectiveArrangement.cone`: the central cone `cP`.
* `ProjectiveArrangement.coneHyperplaneEquiv`: the hyperplanes of the cone are those of `P`.
* `Arrangement.IsCentral`: an arrangement whose hyperplanes all contain a common point. This does
  not mention the origin, so it makes sense on restrictions, whose base point is not determined.
* `OrlikSolomon.slice`: the slice `ℓ₀ = 1`.
* `ProjectiveArrangement.decone`: the decone `d_{H₀}P`, as an arrangement on the vector space
  `(slice ℓ₀).direction`.
* `ProjectiveArrangement.deconeHyperplaneEquiv`: the hyperplanes of the decone are the hyperplanes
  of `P` other than `H₀`.

## Main results

* `ProjectiveArrangement.mem_cone_zeroLocus`: the equations of the hyperplanes of the cone are the
  linear forms whose kernel belongs to `P`.
* `ProjectiveArrangement.cone_isCentral`: the cone is central.
* `ProjectiveArrangement.isHyperplane_comap_chart_slice`: a hyperplane other than `H₀` has a trace
  on the slice that is a nonempty hyperplane.
* `ProjectiveArrangement.comap_chart_slice_inj`: distinct hyperplanes other than `H₀` have distinct
  traces on the slice.
* `ProjectiveArrangement.mem_decone`: the hyperplanes of the decone are these traces.
* `ProjectiveArrangement.isEquation_comp_chart_slice`: equations restrict to equations.
* `ProjectiveArrangement.card_decone_add_one`: the decone has one hyperplane fewer than `P`.

## Implementation notes

An equation of `H₀` is a linear form `ℓ₀ : Dual k W` with `ker ℓ₀ = H₀`. The membership `ker ℓ ∈ P`
already implies `ℓ ≠ 0`, as `ker 0 = ⊤` is not a hyperplane, so that hypothesis is all a statement
needs. The slice depends on `ℓ₀` and not only on `H₀`, so the decone is indexed by `ℓ₀`.

The empty arrangement is allowed by the definition, because the blueprint's definition allows it,
but it has no decone, and it is excluded wherever a decone or a complement is involved. There is no
fake hyperplane at infinity.

## Blueprint

`def:projective`, and the part of `lem:decone` about distinct restricted hyperplanes.
-/

@[expose] public section

open Module

universe u

namespace OrlikSolomon

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

/-! ### Linear hyperplanes as affine hyperplanes -/

section Linear

variable {H : Submodule k W}

/-- A linear subspace is an affine hyperplane exactly when it has codimension one. -/
theorem isHyperplane_toAffineSubspace_iff : IsHyperplane H.toAffineSubspace ↔ IsCoatom H := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨AffineSubspace.toAffineSubspace_ne_bot H, ?_⟩⟩
  · simpa [Submodule.toAffineSubspace_direction] using h.isCoatom_direction
  · simpa [Submodule.toAffineSubspace_direction] using h

theorem zeroLocus_toAffineMap (ℓ : Dual k W) :
    zeroLocus ℓ.toAffineMap = (LinearMap.ker ℓ).toAffineSubspace := by
  ext x
  simp

/-- A nonzero linear form is an equation of the affine hyperplane given by its kernel. -/
theorem isEquation_toAffineMap {ℓ : Dual k W} (hℓ : ℓ ≠ 0) :
    IsEquation ℓ.toAffineMap (LinearMap.ker ℓ).toAffineSubspace :=
  ⟨by simpa using hℓ, zeroLocus_toAffineMap ℓ⟩

/-- Two linear forms with the same kernel, one of them nonzero, differ by a unit of `k`. This is
`IsEquation.existsUnique_smul`, for the linear forms that are equations of linear hyperplanes. -/
theorem exists_eq_smul_of_ker_eq {ℓ ℓ' : Dual k W} (h : LinearMap.ker ℓ = LinearMap.ker ℓ')
    (hℓ' : ℓ' ≠ 0) : ∃ c : kˣ, ℓ = (c : k) • ℓ' := by
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    exact hℓ' (LinearMap.ker_eq_top.1 (h ▸ LinearMap.ker_zero))
  obtain ⟨c, hc, -⟩ := (isEquation_toAffineMap hℓ').existsUnique_smul
    (h ▸ isEquation_toAffineMap hℓ)
  exact ⟨c, by simpa using congrArg AffineMap.linear hc⟩

/-- The kernel of a nonzero linear form has codimension one. -/
theorem isCoatom_ker {ℓ : Dual k W} (hℓ : ℓ ≠ 0) : IsCoatom (LinearMap.ker ℓ) :=
  LinearMap.isCoatom_ker_of_surjective (LinearMap.surjective hℓ)

/-- A linear subspace of codimension one is the kernel of a linear form. -/
theorem exists_ker_eq_of_isCoatom (hH : IsCoatom H) : ∃ ℓ : Dual k W, LinearMap.ker ℓ = H := by
  obtain ⟨f, hf⟩ := (isHyperplane_toAffineSubspace_iff.2 hH).exists_isEquation
  have h0 : f 0 = 0 := hf.apply_eq_zero_iff.2 (by simp)
  have hf' : f = f.linear.toAffineMap := by
    ext v
    simpa [h0] using congrFun f.decomp v
  refine ⟨f.linear, Submodule.toAffineSubspace_injective ?_⟩
  rw [← zeroLocus_toAffineMap, ← hf', hf.zeroLocus_eq]

end Linear

/-! ### Projective arrangements -/

/-- A split projective arrangement in the projectivization of `W`: a finite set of codimension-one
linear subspaces of `W`.

Blueprint: `def:projective`. -/
structure ProjectiveArrangement (k : Type u) [Field k] (W : Type u) [AddCommGroup W]
    [Module k W] where
  /-- The finite set of hyperplanes of a projective arrangement. -/
  hyperplanes : Finset (Submodule k W)
  /-- All members have codimension one. Use `ProjectiveArrangement.isCoatom` instead. -/
  isCoatom_of_mem' : ∀ H ∈ hyperplanes, IsCoatom H

namespace ProjectiveArrangement

variable {P Q : ProjectiveArrangement k W} {H M : Submodule k W} {ℓ ℓ₀ : Dual k W}

instance : SetLike (ProjectiveArrangement k W) (Submodule k W) where
  coe P := P.hyperplanes
  coe_injective := by
    rintro ⟨s, _⟩ ⟨t, _⟩ h
    congr
    exact Finset.coe_injective h

/-- Projective arrangements are ordered by inclusion. -/
instance : PartialOrder (ProjectiveArrangement k W) := .ofSetLike (ProjectiveArrangement k W)

@[simp]
theorem mem_hyperplanes : H ∈ P.hyperplanes ↔ H ∈ P :=
  Iff.rfl

@[simp]
theorem coe_hyperplanes (P : ProjectiveArrangement k W) :
    (P.hyperplanes : Set (Submodule k W)) = P :=
  rfl

@[ext]
theorem ext (h : ∀ H, H ∈ P ↔ H ∈ Q) : P = Q :=
  SetLike.ext h

/-- Every member of a projective arrangement has codimension one. -/
theorem isCoatom (P : ProjectiveArrangement k W) (hH : H ∈ P) : IsCoatom H :=
  P.isCoatom_of_mem' H hH

instance (P : ProjectiveArrangement k W) : Fintype P :=
  inferInstanceAs (Fintype P.hyperplanes)

/-- The number of hyperplanes of a projective arrangement. -/
def card (P : ProjectiveArrangement k W) : ℕ :=
  P.hyperplanes.card

@[simp]
theorem card_hyperplanes (P : ProjectiveArrangement k W) : P.hyperplanes.card = P.card :=
  rfl

@[simp]
theorem fintypeCard_coe (P : ProjectiveArrangement k W) : Fintype.card P = P.card :=
  Fintype.card_coe P.hyperplanes

theorem card_pos_of_nonempty (P : ProjectiveArrangement k W) [Nonempty P] : 0 < P.card := by
  rw [← fintypeCard_coe]
  exact Fintype.card_pos

/-- The projective arrangement of the kernels of a finite set of nonzero linear forms. -/
noncomputable def ofForms (s : Finset (Dual k W)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ProjectiveArrangement k W :=
  open scoped Classical in
  { hyperplanes := s.image LinearMap.ker
    isCoatom_of_mem' := fun H hH ↦ by
      classical
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hH
      exact isCoatom_ker (hs ℓ hℓ) }

theorem mem_ofForms {s : Finset (Dual k W)} {hs : ∀ ℓ ∈ s, ℓ ≠ 0} :
    H ∈ ofForms s hs ↔ ∃ ℓ ∈ s, LinearMap.ker ℓ = H := by
  classical
  exact Finset.mem_image

theorem ker_mem_ofForms {s : Finset (Dual k W)} {hs : ∀ ℓ ∈ s, ℓ ≠ 0} (hℓ : ℓ ∈ s) :
    LinearMap.ker ℓ ∈ ofForms s hs :=
  mem_ofForms.2 ⟨ℓ, hℓ, rfl⟩

/-- A linear form whose kernel belongs to `P` is nonzero: the kernel of `0` is everything, which has
no codimension one. -/
theorem ne_zero_of_ker_mem (hℓ : LinearMap.ker ℓ ∈ P) : ℓ ≠ 0 := by
  rintro rfl
  exact (P.isCoatom hℓ).ne_top LinearMap.ker_zero

/-- Every hyperplane of a projective arrangement has a linear equation. -/
theorem exists_ker_eq (hH : H ∈ P) : ∃ ℓ : Dual k W, LinearMap.ker ℓ = H :=
  exists_ker_eq_of_isCoatom (P.isCoatom hH)

/-- A nonempty projective arrangement has a hyperplane with an equation, which may serve as the
hyperplane at infinity. -/
theorem exists_ker_mem (P : ProjectiveArrangement k W) [Nonempty P] :
    ∃ ℓ : Dual k W, LinearMap.ker ℓ ∈ P := by
  obtain ⟨H, hH⟩ := ‹Nonempty P›
  obtain ⟨ℓ, rfl⟩ := exists_ker_eq hH
  exact ⟨ℓ, hH⟩

/-- A projective arrangement with an equation of a hyperplane is nonempty. -/
theorem nonempty_of_ker_mem (hℓ : LinearMap.ker ℓ ∈ P) : Nonempty P :=
  ⟨⟨_, hℓ⟩⟩

/-! ### The central cone -/

/-- The central cone `cP`: the same hyperplanes, as an arrangement of affine hyperplanes of `W`.

Blueprint: `def:projective`. -/
noncomputable def cone (P : ProjectiveArrangement k W) : Arrangement k W :=
  open scoped Classical in
  { hyperplanes := P.hyperplanes.image Submodule.toAffineSubspace
    isHyperplane_of_mem' := fun _ hL ↦ by
      classical
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hL
      exact isHyperplane_toAffineSubspace_iff.2 (P.isCoatom hH) }

theorem mem_cone {L : AffineSubspace k W} : L ∈ P.cone ↔ ∃ H ∈ P, H.toAffineSubspace = L := by
  classical
  exact Finset.mem_image

@[simp]
theorem toAffineSubspace_mem_cone : H.toAffineSubspace ∈ P.cone ↔ H ∈ P := by
  simp [mem_cone, Submodule.toAffineSubspace_inj]

/-- The hyperplanes of the cone are the hyperplanes of `P`, so the generators of the Orlik-Solomon
algebra of the cone are indexed by `P`. -/
noncomputable def coneHyperplaneEquiv (P : ProjectiveArrangement k W) : P ≃ P.cone :=
  .ofBijective (fun H ↦ ⟨(H : Submodule k W).toAffineSubspace, toAffineSubspace_mem_cone.2 H.2⟩)
    ⟨fun H H' h ↦ Subtype.ext (Submodule.toAffineSubspace_inj.1 (congrArg Subtype.val h)),
      fun L ↦ by
        obtain ⟨H, hH, hL⟩ := mem_cone.1 L.2
        exact ⟨⟨H, hH⟩, Subtype.ext hL⟩⟩

@[simp]
theorem coe_coneHyperplaneEquiv (H : P) :
    (P.coneHyperplaneEquiv H : AffineSubspace k W) = (H : Submodule k W).toAffineSubspace :=
  rfl

theorem cone_injective : Function.Injective (cone : _ → Arrangement k W) := fun _ _ h ↦
  ext fun H ↦ by rw [← toAffineSubspace_mem_cone, h, toAffineSubspace_mem_cone]

/-- The cone has the same number of hyperplanes. -/
@[simp]
theorem card_cone (P : ProjectiveArrangement k W) : P.cone.card = P.card := by
  classical
  exact Finset.card_image_of_injective _ Submodule.toAffineSubspace_injective

/-- An affine function has zero locus in the cone exactly when it is a linear form whose kernel
belongs to `P`. -/
theorem mem_cone_zeroLocus {f : W →ᵃ[k] k} :
    zeroLocus f ∈ P.cone ↔ f = f.linear.toAffineMap ∧ LinearMap.ker f.linear ∈ P := by
  constructor
  · intro hf
    obtain ⟨H, hH, hHf⟩ := mem_cone.1 hf
    have h0 : f 0 = 0 := by
      have : (0 : W) ∈ zeroLocus f := hHf ▸ Submodule.mem_toAffineSubspace.2 H.zero_mem
      simpa using this
    have hf' : f = f.linear.toAffineMap := by
      ext v
      simpa [h0] using congrFun f.decomp v
    refine ⟨hf', ?_⟩
    rw [hf', zeroLocus_toAffineMap] at hHf
    rwa [← Submodule.toAffineSubspace_inj.1 hHf]
  · rintro ⟨hf, hker⟩
    rw [hf, zeroLocus_toAffineMap]
    simpa using hker

/-- A linear form with kernel in `P` has zero locus in the cone. -/
theorem zeroLocus_toAffineMap_mem_cone (hℓ : LinearMap.ker ℓ ∈ P) :
    zeroLocus ℓ.toAffineMap ∈ P.cone := by
  rwa [zeroLocus_toAffineMap, toAffineSubspace_mem_cone]

end ProjectiveArrangement

/-! ### Central arrangements -/

namespace Arrangement

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- An arrangement is central if its hyperplanes have a common point, so that all intersections of
its hyperplanes are nonempty. This does not refer to the origin of `V`, so it makes sense on a
restriction: see the warning at `chart`.

Blueprint: `lem:central-boundary`. -/
def IsCentral (𝒜 : Arrangement k V) : Prop :=
  ∃ p, ∀ H ∈ 𝒜, p ∈ H

/-- In a central arrangement, every intersection of hyperplanes is nonempty. -/
theorem IsCentral.inter_ne_bot {𝒜 : Arrangement k V} (h : 𝒜.IsCentral) (I : List 𝒜) :
    inter I ≠ ⊥ := by
  obtain ⟨p, hp⟩ := h
  rw [← AffineSubspace.nonempty_iff_ne_bot]
  exact ⟨p, mem_inter.2 fun H _ ↦ hp H H.2⟩

end Arrangement

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {H M M' : Submodule k W} {ℓ ℓ₀ : Dual k W}

/-- The cone of a projective arrangement is central: all its hyperplanes contain the origin. -/
theorem cone_isCentral (P : ProjectiveArrangement k W) : P.cone.IsCentral :=
  ⟨0, fun L hL ↦ by
    obtain ⟨H, -, rfl⟩ := mem_cone.1 hL
    exact Submodule.mem_toAffineSubspace.2 H.zero_mem⟩

end ProjectiveArrangement

/-! ### The slice -/

section Slice

variable {ℓ₀ : Dual k W}

/-- The affine function `ℓ₀ - 1`, an equation of the slice. -/
noncomputable def sliceEquation (ℓ₀ : Dual k W) : W →ᵃ[k] k :=
  ℓ₀.toAffineMap - AffineMap.const k W 1

/-- The slice `ℓ₀ = 1` of `W`, the affine `n`-space in which the decone lives when `W` has dimension
`n + 1`.

Blueprint: `def:projective`. -/
noncomputable def slice (ℓ₀ : Dual k W) : AffineSubspace k W :=
  zeroLocus (sliceEquation ℓ₀)

@[simp]
theorem mem_slice {v : W} : v ∈ slice ℓ₀ ↔ ℓ₀ v = 1 := by
  simp [slice, sliceEquation, sub_eq_zero]

theorem isEquation_sliceEquation (hℓ₀ : ℓ₀ ≠ 0) : IsEquation (sliceEquation ℓ₀) (slice ℓ₀) :=
  ⟨by simpa [sliceEquation] using hℓ₀, rfl⟩

/-- The slice of a nonzero linear form is a hyperplane. -/
theorem isHyperplane_slice (hℓ₀ : ℓ₀ ≠ 0) : IsHyperplane (slice ℓ₀) :=
  (isEquation_sliceEquation hℓ₀).isHyperplane

theorem slice_ne_bot (hℓ₀ : ℓ₀ ≠ 0) : slice ℓ₀ ≠ ⊥ :=
  (isHyperplane_slice hℓ₀).ne_bot

/-- The direction of the slice is the kernel of `ℓ₀`. So the slice is the affine space of the
hyperplane `H₀`. -/
theorem direction_slice (hℓ₀ : ℓ₀ ≠ 0) : (slice ℓ₀).direction = LinearMap.ker ℓ₀ := by
  simpa [sliceEquation] using (isEquation_sliceEquation hℓ₀).direction_eq

/-- The form `ℓ₀` is equal to `1` on the slice. -/
@[simp]
theorem toAffineMap_comp_chart_slice (hℓ₀ : ℓ₀ ≠ 0) :
    ℓ₀.toAffineMap.comp (chart (slice ℓ₀)) = AffineMap.const k _ 1 :=
  AffineMap.ext fun v ↦ by simpa using chart_mem (slice_ne_bot hℓ₀) v

/-- The slice of a nonzero form has dimension one less than `W`. -/
theorem finrank_direction_slice_add_one [FiniteDimensional k W] (hℓ₀ : ℓ₀ ≠ 0) :
    finrank k (slice ℓ₀).direction + 1 = finrank k W := by
  have h1 := (isHyperplane_slice hℓ₀).codim_eq_one
  have h2 := codim_add_finrank_direction (slice ℓ₀)
  omega

end Slice

/-! ### The decone -/

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {H M M' : Submodule k W} {ℓ ℓ₀ : Dual k W}

/-- The decone `d_{H₀}P` for an equation `ℓ₀` of `H₀`: the traces on the slice `ℓ₀ = 1` of the other
hyperplanes of `P`, as an arrangement on the vector space `(slice ℓ₀).direction`, identified with
the slice through `chart`. The hyperplane `H₀` itself does not meet the slice, so it is dropped. See
`mem_decone`.

Blueprint: `def:projective`. -/
noncomputable def decone (P : ProjectiveArrangement k W) (ℓ₀ : Dual k W) :
    Arrangement k (slice ℓ₀).direction :=
  P.cone.restriction (slice ℓ₀)

/-- The equation `ℓ₀` of `H₀` does not vanish on the slice, so `H₀` does not meet it. -/
theorem comap_ker_chart_slice (hℓ₀ : ℓ₀ ≠ 0) :
    (LinearMap.ker ℓ₀).toAffineSubspace.comap (chart (slice ℓ₀)) = ⊥ := by
  rw [comap_chart_eq_bot_iff (slice_ne_bot hℓ₀), ← not_ne_iff,
    ← AffineSubspace.nonempty_iff_ne_bot]
  rintro ⟨x, hx₁, hx₂⟩
  have hx₁' : ℓ₀ x = 1 := by simpa using hx₁
  have hx₂' : ℓ₀ x = 0 := by simpa using hx₂
  exact one_ne_zero (hx₁'.symm.trans hx₂')

/-- A linear subspace not contained in `ker ℓ₀` contains a point of the slice. -/
theorem exists_mem_slice_of_not_le (hM : ¬M ≤ LinearMap.ker ℓ₀) : ∃ p ∈ M, ℓ₀ p = 1 := by
  obtain ⟨v, hv, hv₀⟩ := IsConcreteLE.not_le_iff_exists.1 hM
  have hv₀' : ℓ₀ v ≠ 0 := by simpa using hv₀
  exact ⟨(ℓ₀ v)⁻¹ • v, M.smul_mem _ hv, by simp [hv₀']⟩

/-- A linear subspace meets the slice exactly when it is not contained in `ker ℓ₀`. -/
theorem slice_inf_toAffineSubspace_ne_bot_iff :
    slice ℓ₀ ⊓ M.toAffineSubspace ≠ ⊥ ↔ ¬M ≤ LinearMap.ker ℓ₀ := by
  rw [← AffineSubspace.nonempty_iff_ne_bot]
  constructor
  · rintro ⟨x, hx₁, hx₂⟩ hle
    have hx₁' : ℓ₀ x = 1 := by simpa using hx₁
    exact one_ne_zero (hx₁'.symm.trans (hle hx₂))
  · intro hM
    obtain ⟨p, hp, hp₀⟩ := exists_mem_slice_of_not_le hM
    exact ⟨p, by simpa using hp₀, hp⟩

/-- A linear hyperplane does not contain the slice of a nonzero form, as the slice does not contain
the origin. -/
theorem not_slice_le_toAffineSubspace (hℓ₀ : ℓ₀ ≠ 0) (hM : IsCoatom M) :
    ¬slice ℓ₀ ≤ M.toAffineSubspace := fun hle ↦ by
  have h := (isHyperplane_slice hℓ₀).eq_of_le (isHyperplane_toAffineSubspace_iff.2 hM) hle
  have h0 : (0 : W) ∈ slice ℓ₀ := h ▸ Submodule.mem_toAffineSubspace.2 M.zero_mem
  simp at h0

/-- A linear subspace not contained in `ker ℓ₀` is determined by its trace on the slice.

Blueprint: `lem:decone`, distinct central hyperplanes restrict to distinct affine hyperplanes. -/
theorem le_of_slice_inf_le (hM : ¬M ≤ LinearMap.ker ℓ₀)
    (h : slice ℓ₀ ⊓ M.toAffineSubspace ≤ slice ℓ₀ ⊓ M'.toAffineSubspace) : M ≤ M' := by
  obtain ⟨p, hp, hp₀⟩ := exists_mem_slice_of_not_le hM
  have key {x : W} (hx : x ∈ M) (hx₀ : ℓ₀ x = 1) : x ∈ M' := (h ⟨by simpa using hx₀, hx⟩).2
  have hp' := key hp hp₀
  intro v hv
  have hmem : v - ℓ₀ v • p + p ∈ M' :=
    key (M.add_mem (M.sub_mem hv (M.smul_mem _ hp)) hp) (by simp [hp₀])
  have hv' : v = (v - ℓ₀ v • p + p) + (ℓ₀ v - 1) • p := by
    simp only [sub_smul, one_smul]
    abel
  rw [hv']
  exact M'.add_mem hmem (M'.smul_mem _ hp')

/-- The hyperplanes of `P` other than `H₀` have traces on the slice that are hyperplanes, and in
particular they are nonempty.

Blueprint: `lem:decone`. -/
theorem isHyperplane_comap_chart_slice (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hM : M ∈ P)
    (hne : M ≠ LinearMap.ker ℓ₀) :
    IsHyperplane (M.toAffineSubspace.comap (chart (slice ℓ₀))) := by
  have h₀ := ne_zero_of_ker_mem hℓ₀
  rw [isHyperplane_comap_chart_iff (slice_ne_bot h₀)
    (isHyperplane_toAffineSubspace_iff.2 (P.isCoatom hM))]
  refine ⟨not_slice_le_toAffineSubspace h₀ (P.isCoatom hM),
    slice_inf_toAffineSubspace_ne_bot_iff.2 fun hle ↦ hne ?_⟩
  exact (((P.isCoatom hM).le_iff_eq (P.isCoatom hℓ₀).ne_top).1 hle).symm

/-- A hyperplane of `P` other than `H₀` is not contained in `H₀`. -/
theorem not_le_ker (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hM : M ∈ P) (hne : M ≠ LinearMap.ker ℓ₀) :
    ¬M ≤ LinearMap.ker ℓ₀ := fun hle ↦
  hne (((P.isCoatom hM).le_iff_eq (P.isCoatom hℓ₀).ne_top).1 hle).symm

/-- The restriction to the slice of an equation of a hyperplane of `P` other than `H₀` is an
equation of its trace on the slice.

Blueprint: `lem:decone`. -/
theorem isEquation_comp_chart_slice (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hℓ : LinearMap.ker ℓ ∈ P)
    (hne : LinearMap.ker ℓ ≠ LinearMap.ker ℓ₀) :
    IsEquation (ℓ.toAffineMap.comp (chart (slice ℓ₀)))
      ((LinearMap.ker ℓ).toAffineSubspace.comap (chart (slice ℓ₀))) :=
  (isEquation_toAffineMap (ne_zero_of_ker_mem hℓ)).comp_chart_of_not_le
    (not_slice_le_toAffineSubspace (ne_zero_of_ker_mem hℓ₀) (P.isCoatom hℓ))
    (slice_inf_toAffineSubspace_ne_bot_iff.2 (not_le_ker hℓ₀ hℓ hne))

/-- Distinct hyperplanes of `P` other than `H₀` have distinct traces on the slice.

Blueprint: `lem:decone`. -/
theorem comap_chart_slice_inj (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hM : M ∈ P)
    (hne : M ≠ LinearMap.ker ℓ₀) (hM' : M' ∈ P) (hne' : M' ≠ LinearMap.ker ℓ₀) :
    M.toAffineSubspace.comap (chart (slice ℓ₀)) = M'.toAffineSubspace.comap (chart (slice ℓ₀)) ↔
      M = M' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have h' := (comap_chart_eq_comap_chart_iff (slice_ne_bot (ne_zero_of_ker_mem hℓ₀))).1 h
  exact le_antisymm (le_of_slice_inf_le (not_le_ker hℓ₀ hM hne) h'.le)
    (le_of_slice_inf_le (not_le_ker hℓ₀ hM' hne') h'.ge)

/-- The hyperplanes of the decone are the traces on the slice of the hyperplanes of `P` other than
`H₀`.

Blueprint: `def:projective`. -/
theorem mem_decone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) {L : AffineSubspace k (slice ℓ₀).direction} :
    L ∈ P.decone ℓ₀ ↔ ∃ M ∈ P, M ≠ LinearMap.ker ℓ₀ ∧
      M.toAffineSubspace.comap (chart (slice ℓ₀)) = L := by
  rw [decone, Arrangement.mem_restriction']
  constructor
  · rintro ⟨hL, K, hK, rfl⟩
    obtain ⟨M, hM, rfl⟩ := mem_cone.1 hK
    refine ⟨M, hM, ?_, rfl⟩
    rintro rfl
    exact hL.ne_bot (comap_ker_chart_slice (ne_zero_of_ker_mem hℓ₀))
  · rintro ⟨M, hM, hne, rfl⟩
    exact ⟨isHyperplane_comap_chart_slice hℓ₀ hM hne, _, toAffineSubspace_mem_cone.2 hM, rfl⟩

/-- If `H₀` is the only hyperplane of `P`, then the decone is empty, and the projective complement
is an affine space. -/
theorem decone_eq_empty (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hP : ∀ H ∈ P, H = LinearMap.ker ℓ₀) :
    P.decone ℓ₀ = ∅ :=
  Arrangement.ext fun L ↦ by
    simp only [mem_decone hℓ₀, Arrangement.notMem_empty, iff_false]
    rintro ⟨M, hM, hne, -⟩
    exact hne (hP M hM)

theorem comap_chart_slice_mem_decone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hM : M ∈ P)
    (hne : M ≠ LinearMap.ker ℓ₀) :
    M.toAffineSubspace.comap (chart (slice ℓ₀)) ∈ P.decone ℓ₀ :=
  (mem_decone hℓ₀).2 ⟨M, hM, hne, rfl⟩

/-- The hyperplanes of the decone correspond to the hyperplanes of `P` other than `H₀`, by taking
the trace on the slice.

Blueprint: `lem:decone`. -/
noncomputable def deconeHyperplaneEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    {M : P // (M : Submodule k W) ≠ LinearMap.ker ℓ₀} ≃ P.decone ℓ₀ :=
  .ofBijective
    (fun M ↦ ⟨_, comap_chart_slice_mem_decone hℓ₀ M.1.2 M.2⟩)
    ⟨fun M M' h ↦ Subtype.ext <| Subtype.ext <|
        (comap_chart_slice_inj hℓ₀ M.1.2 M.2 M'.1.2 M'.2).1 (congrArg Subtype.val h),
      fun L ↦ by
        obtain ⟨M, hM, hne, hL⟩ := (mem_decone hℓ₀).1 L.2
        exact ⟨⟨⟨M, hM⟩, hne⟩, Subtype.ext hL⟩⟩

@[simp]
theorem coe_deconeHyperplaneEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (M : {M : P // (M : Submodule k W) ≠ LinearMap.ker ℓ₀}) :
    (deconeHyperplaneEquiv hℓ₀ M : AffineSubspace k (slice ℓ₀).direction) =
      (M.1 : Submodule k W).toAffineSubspace.comap (chart (slice ℓ₀)) :=
  rfl

/-- The decone has one hyperplane fewer than `P`.

Blueprint: `cor:projective-betti`, on counting. -/
theorem card_decone_add_one (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) : (P.decone ℓ₀).card + 1 = P.card := by
  classical
  have h : (P.decone ℓ₀).hyperplanes = (P.hyperplanes.erase (LinearMap.ker ℓ₀)).image
      fun M ↦ M.toAffineSubspace.comap (chart (slice ℓ₀)) := by
    ext L
    simp only [Arrangement.mem_hyperplanes, mem_decone hℓ₀, Finset.mem_image, Finset.mem_erase,
      mem_hyperplanes]
    constructor
    · rintro ⟨M, hM, hne, rfl⟩
      exact ⟨M, ⟨hne, hM⟩, rfl⟩
    · rintro ⟨M, ⟨hne, hM⟩, rfl⟩
      exact ⟨M, hM, hne, rfl⟩
  rw [← Arrangement.card_hyperplanes, h, Finset.card_image_of_injOn,
    Finset.card_erase_add_one hℓ₀, card_hyperplanes]
  intro M hM M' hM' e
  simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, mem_hyperplanes,
    Set.mem_singleton_iff] at hM hM'
  exact (comap_chart_slice_inj hℓ₀ hM.1 hM.2 hM'.1 hM'.2).1 e

end ProjectiveArrangement

end OrlikSolomon
