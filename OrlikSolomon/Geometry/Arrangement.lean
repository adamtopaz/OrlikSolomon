/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Chart

/-!
# Affine hyperplane arrangements

An arrangement in a vector space `V` over a field `k` is a finite set of affine hyperplanes. This
file defines arrangements, their deletion and restriction with respect to a hyperplane, and the
incidence data used by the Orlik-Solomon algebra and by induction on arrangements. It is all linear
algebra over `k`, and it has no rings of functions: complements are not subsets of `V`, and they
are constructed in `OrlikSolomon/Geometry/Complement.lean`.

## Main definitions

* `OrlikSolomon.Arrangement`: a finite set of hyperplanes. Each `𝒜 : Arrangement k V` coerces to a
  finite type `↥𝒜`, which indexes generators, and lists in `↥𝒜` are used for signed words.
* `OrlikSolomon.Arrangement.deletion`: the arrangement `𝒜' = 𝒜 ∖ {H}`.
* `OrlikSolomon.Arrangement.comap`: the pullback of an arrangement along an affine map.
* `OrlikSolomon.Arrangement.restriction`: the arrangement `𝒜''` on the vector space `H.direction`.
* `OrlikSolomon.Arrangement.representative`: a chosen hyperplane of `𝒜'` with a given trace on `H`.
* `OrlikSolomon.Arrangement.inter`: the intersection of a list of hyperplanes of `𝒜`.

## Main results

* `OrlikSolomon.Arrangement.mem_restriction`,
  `OrlikSolomon.Arrangement.mem_restriction_iff_map_chart`: the hyperplanes of `𝒜''` are the
  nonempty traces on `H` of the hyperplanes of `𝒜'`.
* `OrlikSolomon.Arrangement.card_restriction_le`, `OrlikSolomon.Arrangement.card_restriction_lt`:
  the restriction has at most as many hyperplanes as the deletion, and fewer than the arrangement.
* `OrlikSolomon.Arrangement.exists_representative`: every retained hyperplane has a representative.
* `OrlikSolomon.Arrangement.induction`: deletion-restriction induction over all spaces.
* `OrlikSolomon.Arrangement.map_chart_inter`, `OrlikSolomon.Arrangement.inter_eq_bot_iff`,
  `OrlikSolomon.Arrangement.codim_inf_inter_map_representative`: intersections and codimensions in
  the restriction, in terms of `H` and representatives.

## Blueprint

`def:arrangement`, `def:deletion`, and the incidence part of `lem:restriction-geometry` about
arrangements. See `OrlikSolomon/Geometry/Hyperplane.lean` for `lem:equations`, and
`OrlikSolomon/Geometry/Chart.lean` for the part of `lem:restriction-geometry` about a single
restricted hyperplane.
-/

@[expose] public section

open Module

universe u

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-- A hyperplane arrangement in `V`: a finite set of affine hyperplanes. Generators of the
Orlik-Solomon algebra are indexed by the subtype `↥𝒜`, which is a `Fintype`, while signed words use
lists of elements of `↥𝒜`.

Blueprint: `def:arrangement`. -/
structure Arrangement (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] where
  /-- The finite set of hyperplanes of an arrangement. -/
  hyperplanes : Finset (AffineSubspace k V)
  /-- All members of an arrangement are hyperplanes. Use `Arrangement.isHyperplane` instead. -/
  isHyperplane_of_mem' : ∀ H ∈ hyperplanes, IsHyperplane H

namespace Arrangement

variable {𝒜 ℬ : Arrangement k V} {H K : AffineSubspace k V}

instance : SetLike (Arrangement k V) (AffineSubspace k V) where
  coe 𝒜 := 𝒜.hyperplanes
  coe_injective := by
    rintro ⟨s, _⟩ ⟨t, _⟩ h
    congr
    exact Finset.coe_injective h

/-- Arrangements are ordered by inclusion, so `𝒜 ≤ ℬ` means that `𝒜` is a sub-arrangement. -/
instance : PartialOrder (Arrangement k V) := .ofSetLike (Arrangement k V)

@[simp]
theorem mem_hyperplanes : H ∈ 𝒜.hyperplanes ↔ H ∈ 𝒜 :=
  Iff.rfl

@[simp]
theorem coe_hyperplanes (𝒜 : Arrangement k V) :
    (𝒜.hyperplanes : Set (AffineSubspace k V)) = 𝒜 :=
  rfl

@[ext]
theorem ext (h : ∀ H, H ∈ 𝒜 ↔ H ∈ ℬ) : 𝒜 = ℬ :=
  SetLike.ext h

/-- Every member of an arrangement is a hyperplane. -/
theorem isHyperplane (𝒜 : Arrangement k V) (hH : H ∈ 𝒜) : IsHyperplane H :=
  𝒜.isHyperplane_of_mem' H hH

instance (𝒜 : Arrangement k V) : Fintype 𝒜 :=
  inferInstanceAs (Fintype 𝒜.hyperplanes)

/-- The number of hyperplanes of an arrangement. -/
def card (𝒜 : Arrangement k V) : ℕ :=
  𝒜.hyperplanes.card

@[simp]
theorem card_hyperplanes (𝒜 : Arrangement k V) : 𝒜.hyperplanes.card = 𝒜.card :=
  rfl

@[simp]
theorem fintypeCard_coe (𝒜 : Arrangement k V) : Fintype.card 𝒜 = 𝒜.card :=
  Fintype.card_coe 𝒜.hyperplanes

/-- The empty arrangement. -/
instance : EmptyCollection (Arrangement k V) :=
  ⟨⟨∅, by simp⟩⟩

@[simp]
theorem notMem_empty (H : AffineSubspace k V) : H ∉ (∅ : Arrangement k V) :=
  Finset.notMem_empty H

@[simp]
theorem card_empty : (∅ : Arrangement k V).card = 0 :=
  rfl

instance : IsEmpty (∅ : Arrangement k V) :=
  ⟨fun H ↦ notMem_empty _ H.2⟩

theorem eq_empty_or_exists_mem (𝒜 : Arrangement k V) : 𝒜 = ∅ ∨ ∃ H, H ∈ 𝒜 := by
  by_cases h : ∃ H, H ∈ 𝒜
  · exact Or.inr h
  · refine Or.inl (ext fun H ↦ ?_)
    simpa using fun hH ↦ h ⟨H, hH⟩

/-- A zero-dimensional space has only the empty arrangement. -/
theorem eq_empty_of_subsingleton [Subsingleton V] (𝒜 : Arrangement k V) : 𝒜 = ∅ :=
  ext fun H ↦ by simpa using fun hH ↦ not_isHyperplane_of_subsingleton H (𝒜.isHyperplane hH)

/-- The arrangement formed by the hyperplanes in a finite set of affine subspaces, discarding the
other members. This builds an arrangement from data that may contain empty sections or the whole
space. -/
noncomputable def ofFinset (s : Finset (AffineSubspace k V)) : Arrangement k V :=
  open scoped Classical in
  { hyperplanes := s.filter IsHyperplane
    isHyperplane_of_mem' := fun _ h ↦ (Finset.mem_filter.1 h).2 }

@[simp]
theorem mem_ofFinset {s : Finset (AffineSubspace k V)} :
    H ∈ ofFinset s ↔ H ∈ s ∧ IsHyperplane H := by
  classical
  exact Finset.mem_filter

/-- The inclusion of the generators of a sub-arrangement. -/
def inclusion (h : 𝒜 ≤ ℬ) (H : 𝒜) : ℬ :=
  ⟨H, mem_of_le_of_mem h H.2⟩

@[simp]
theorem coe_inclusion (h : 𝒜 ≤ ℬ) (H : 𝒜) : (inclusion h H : AffineSubspace k V) = H :=
  rfl

theorem inclusion_injective (h : 𝒜 ≤ ℬ) : Function.Injective (inclusion h) :=
  fun _ _ h' ↦ Subtype.ext (congrArg (fun H : ℬ ↦ (H : AffineSubspace k V)) h')

/-! ### Deletion -/

/-- The deletion `𝒜' = 𝒜 ∖ {H}`.

Blueprint: `def:deletion`. -/
noncomputable def deletion (𝒜 : Arrangement k V) (H : AffineSubspace k V) : Arrangement k V :=
  open scoped Classical in
  { hyperplanes := 𝒜.hyperplanes.erase H
    isHyperplane_of_mem' := fun _ h ↦ 𝒜.isHyperplane_of_mem' _ (Finset.mem_of_mem_erase h) }

@[simp]
theorem mem_deletion : K ∈ 𝒜.deletion H ↔ K ≠ H ∧ K ∈ 𝒜 := by
  classical
  exact Finset.mem_erase

theorem deletion_le (𝒜 : Arrangement k V) (H : AffineSubspace k V) : 𝒜.deletion H ≤ 𝒜 :=
  IsConcreteLE.le_iff.2 fun _ h ↦ (mem_deletion.1 h).2

theorem card_deletion_add_one (hH : H ∈ 𝒜) : (𝒜.deletion H).card + 1 = 𝒜.card := by
  classical
  exact Finset.card_erase_add_one hH

theorem card_deletion_lt (hH : H ∈ 𝒜) : (𝒜.deletion H).card < 𝒜.card :=
  Nat.lt_of_succ_le (card_deletion_add_one hH).le

/-! ### Pullback and restriction -/

section Comap

variable {W : Type u} [AddCommGroup W] [Module k W]

/-- The pullback of an arrangement along an affine map `φ`: the preimages of its hyperplanes under
`φ` that are hyperplanes, with duplicates removed. Empty preimages, and preimages equal to the whole
of `W`, are discarded. -/
noncomputable def comap (φ : W →ᵃ[k] V) (𝒜 : Arrangement k V) : Arrangement k W :=
  open scoped Classical in
  ofFinset (𝒜.hyperplanes.image (AffineSubspace.comap φ))

@[simp]
theorem mem_comap {φ : W →ᵃ[k] V} {L : AffineSubspace k W} :
    L ∈ 𝒜.comap φ ↔ IsHyperplane L ∧ ∃ K ∈ 𝒜, K.comap φ = L := by
  classical
  simp [comap, and_comm]

/-- A hyperplane of `𝒜` whose preimage is not the whole of `W` has empty preimage, or a preimage in
the pullback of `𝒜`. -/
theorem comap_eq_bot_or_mem_comap (φ : W →ᵃ[k] V) (hK : K ∈ 𝒜) (h : K.comap φ ≠ ⊤) :
    K.comap φ = ⊥ ∨ K.comap φ ∈ 𝒜.comap φ := by
  obtain hb | ht | hyp := (𝒜.isHyperplane hK).comap_eq_bot_or_top_or_isHyperplane φ
  · exact Or.inl hb
  · exact absurd ht h
  · exact Or.inr (mem_comap.2 ⟨hyp, K, hK, rfl⟩)

end Comap

/-- The restriction `𝒜''` of an arrangement to `H`, as an arrangement in the vector space
`H.direction`, identified with `H` through `chart H`. It consists of the traces on `H` of the other
hyperplanes of `𝒜` that meet `H`, with duplicates removed: see `mem_restriction` and
`mem_restriction_iff_map_chart`.

The definition makes sense for any `H`. A hyperplane `H` need not belong to `𝒜`, which is the
situation of a slice in deconing.

Blueprint: `def:deletion`. -/
noncomputable def restriction (𝒜 : Arrangement k V) (H : AffineSubspace k V) :
    Arrangement k H.direction :=
  𝒜.comap (chart H)

/-- Membership in the restriction, for an arbitrary `H`. -/
theorem mem_restriction' {L : AffineSubspace k H.direction} :
    L ∈ 𝒜.restriction H ↔ IsHyperplane L ∧ ∃ K ∈ 𝒜, K.comap (chart H) = L :=
  mem_comap

/-- Membership in the restriction: `L` is the trace on `H` of another hyperplane meeting `H`.

Blueprint: `def:deletion`. -/
theorem mem_restriction (hH : IsHyperplane H) {L : AffineSubspace k H.direction} :
    L ∈ 𝒜.restriction H ↔ ∃ K ∈ 𝒜.deletion H, H ⊓ K ≠ ⊥ ∧ K.comap (chart H) = L := by
  rw [mem_restriction']
  constructor
  · rintro ⟨hL, K, hK, rfl⟩
    obtain ⟨hne, hbot⟩ := (hH.isHyperplane_comap_chart_iff (𝒜.isHyperplane hK)).1 hL
    exact ⟨K, mem_deletion.2 ⟨hne, hK⟩, hbot, rfl⟩
  · rintro ⟨K, hK, hbot, rfl⟩
    obtain ⟨hne, hK⟩ := mem_deletion.1 hK
    exact ⟨(hH.isHyperplane_comap_chart_iff (𝒜.isHyperplane hK)).2 ⟨hne, hbot⟩, K, hK, rfl⟩

/-- Membership in the restriction, in terms of subspaces of `V`: `M` corresponds to a nonempty
intersection `H ∩ K` with another hyperplane `K` of `𝒜`.

Blueprint: `def:deletion`. -/
theorem mem_restriction_iff_map_chart (hH : IsHyperplane H) {M : AffineSubspace k H.direction} :
    M ∈ 𝒜.restriction H ↔ ∃ K ∈ 𝒜.deletion H, H ⊓ K ≠ ⊥ ∧ M.map (chart H) = H ⊓ K := by
  rw [mem_restriction hH]
  refine exists_congr fun K ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [← map_chart_comap_chart hH.ne_bot, eq_comm]
  exact map_chart_injective.eq_iff.symm

/-- Another hyperplane of `𝒜` meeting `H` has a retained trace. -/
theorem comap_chart_mem_restriction (hH : IsHyperplane H) (hK : K ∈ 𝒜.deletion H)
    (hbot : H ⊓ K ≠ ⊥) : K.comap (chart H) ∈ 𝒜.restriction H :=
  (mem_restriction hH).2 ⟨K, hK, hbot, rfl⟩

/-- A retained hyperplane corresponds to a hyperplane of `H`.

Blueprint: `lem:restriction-geometry`. -/
theorem isHyperplaneIn_map_chart {L : AffineSubspace k H.direction} (hL : L ∈ 𝒜.restriction H) :
    IsHyperplaneIn (L.map (chart H)) H :=
  have hL' := (𝒜.restriction H).isHyperplane hL
  (isHyperplaneIn_map_chart_iff (ne_bot_of_isHyperplane hL')).2 hL'

/-- Every retained hyperplane has an old representative.

Blueprint: `lem:restriction-geometry`. -/
theorem exists_representative {L : AffineSubspace k H.direction} (hL : L ∈ 𝒜.restriction H) :
    ∃ K ∈ 𝒜.deletion H, K.comap (chart H) = L := by
  obtain ⟨hL', K, hK, rfl⟩ := mem_restriction'.1 hL
  refine ⟨K, mem_deletion.2 ⟨?_, hK⟩, rfl⟩
  rintro rfl
  exact hL'.ne_top (comap_chart_self (ne_bot_of_isHyperplane hL'))

/-- A chosen old representative of a retained hyperplane.

Blueprint: `def:lift-map`. -/
noncomputable def representative (L : 𝒜.restriction H) : 𝒜.deletion H :=
  ⟨(exists_representative L.2).choose, (exists_representative L.2).choose_spec.1⟩

@[simp]
theorem comap_representative (L : 𝒜.restriction H) :
    (representative L : AffineSubspace k V).comap (chart H) = L :=
  (exists_representative L.2).choose_spec.2

theorem ne_bot_of_mem_restriction {L : AffineSubspace k H.direction} (hL : L ∈ 𝒜.restriction H) :
    H ≠ ⊥ :=
  ne_bot_of_isHyperplane ((𝒜.restriction H).isHyperplane hL)

/-- The trace on `H` of the representative of `L` is the subspace of `V` corresponding to `L`. -/
theorem inf_representative (L : 𝒜.restriction H) :
    H ⊓ (representative L : AffineSubspace k V) =
      (L : AffineSubspace k H.direction).map (chart H) := by
  rw [← map_chart_comap_chart (ne_bot_of_mem_restriction L.2), comap_representative]

theorem inf_representative_ne_bot (L : 𝒜.restriction H) :
    H ⊓ (representative L : AffineSubspace k V) ≠ ⊥ := by
  rw [inf_representative, Ne, AffineSubspace.map_eq_bot_iff]
  exact ((𝒜.restriction H).isHyperplane L.2).ne_bot

/-- A hyperplane of `𝒜'` meeting `H` has the same trace on `H` as the representative of that
trace. -/
theorem inf_representative_comap_chart (hH : IsHyperplane H) (hK : K ∈ 𝒜.deletion H)
    (hbot : H ⊓ K ≠ ⊥) :
    H ⊓ (representative ⟨K.comap (chart H), comap_chart_mem_restriction hH hK hbot⟩ :
      AffineSubspace k V) = H ⊓ K := by
  rw [inf_representative, map_chart_comap_chart hH.ne_bot]

/-- The restriction has at most as many hyperplanes as the deletion.

Blueprint: `lem:restriction-geometry`. -/
theorem card_restriction_le (𝒜 : Arrangement k V) (H : AffineSubspace k V) :
    (𝒜.restriction H).card ≤ (𝒜.deletion H).card := by
  classical
  refine le_trans (Finset.card_le_card fun L hL ↦ ?_)
    (Finset.card_image_le (s := (𝒜.deletion H).hyperplanes)
      (f := AffineSubspace.comap (chart H)))
  obtain ⟨K, hK, rfl⟩ := exists_representative hL
  exact Finset.mem_image_of_mem _ hK

/-- The restriction has fewer hyperplanes than the arrangement.

Blueprint: `lem:restriction-geometry`. -/
theorem card_restriction_lt (hH : H ∈ 𝒜) : (𝒜.restriction H).card < 𝒜.card :=
  (card_restriction_le 𝒜 H).trans_lt (card_deletion_lt hH)

/-- Deletion-restriction induction on arrangements, over all finite-dimensional spaces `V` in the
universe of `k`. A property holds for all arrangements if it holds for empty arrangements and if,
for every `𝒜` and every `H ∈ 𝒜`, it passes to `𝒜` from the deletion and the restriction of `H`. -/
theorem induction
    {motive : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Arrangement k V → Prop}
    (empty : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V], motive V ∅)
    (step : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (𝒜 : Arrangement k V) (H : AffineSubspace k V), H ∈ 𝒜 → motive V (𝒜.deletion H) →
        motive H.direction (𝒜.restriction H) → motive V 𝒜)
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V) :
    motive V 𝒜 := by
  have aux : ∀ (n : ℕ) (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (𝒜 : Arrangement k V), 𝒜.card = n → motive V 𝒜 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V _ _ _ 𝒜 hn
      obtain rfl | ⟨H, hH⟩ := 𝒜.eq_empty_or_exists_mem
      · exact empty V
      · exact step V 𝒜 H hH (ih _ (hn ▸ card_deletion_lt hH) V _ rfl)
          (ih _ (hn ▸ card_restriction_lt hH) H.direction _ rfl)
  exact aux _ V 𝒜 rfl

/-! ### Intersections of lists of hyperplanes -/

/-- The intersection `⋂ I` of a list of hyperplanes of `𝒜`, as in the relators of the
Orlik-Solomon algebra. It is `⊤` for the empty list, and `⊥` when the intersection is empty.

Blueprint: `def:os`. -/
def inter (I : List 𝒜) : AffineSubspace k V :=
  ⨅ H ∈ I, (H : AffineSubspace k V)

@[simp]
theorem mem_inter {I : List 𝒜} {x : V} :
    x ∈ inter I ↔ ∀ H ∈ I, x ∈ (H : AffineSubspace k V) := by
  simp [inter, AffineSubspace.mem_iInf_iff]

@[simp]
theorem inter_nil : inter ([] : List 𝒜) = ⊤ := by
  simp [inter]

@[simp]
theorem inter_cons (H : 𝒜) (I : List 𝒜) : inter (H :: I) = (H : AffineSubspace k V) ⊓ inter I := by
  ext x
  simp [AffineSubspace.mem_inf_iff]

@[simp]
theorem inter_map_inclusion (h : 𝒜 ≤ ℬ) (I : List 𝒜) : inter (I.map (inclusion h)) = inter I := by
  induction I with
  | nil => simp
  | cons H I ih => simp [ih]

/-- The form of `inter_map_inclusion` that survives `List.map_map`. -/
@[simp]
theorem inter_map_inclusion_comp {ι : Type*} (h : 𝒜 ≤ ℬ) (g : ι → 𝒜) (I : List ι) :
    inter (I.map (inclusion h ∘ g)) = inter (I.map g) := by
  rw [← List.map_map, inter_map_inclusion]

theorem inter_eq_iInf_get (I : List 𝒜) :
    inter I = ⨅ i : Fin I.length, (I.get i : AffineSubspace k V) := by
  ext x
  simp only [mem_inter, AffineSubspace.mem_iInf_iff]
  refine ⟨fun h i ↦ h _ (List.get_mem _ _), fun h H hH ↦ ?_⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem hH
  exact h i

/-- A nonempty intersection of a list of hyperplanes has codimension at most the length. -/
theorem codim_inter_le [FiniteDimensional k V] {I : List 𝒜} (h : inter I ≠ ⊥) :
    codim (inter I) ≤ I.length := by
  rw [inter_eq_iInf_get] at h ⊢
  simpa using codim_iInf_le_card (fun i ↦ 𝒜.isHyperplane (I.get i).2) h

/-- The codimension of a nonempty intersection of a list of hyperplanes is the rank of their
equations.

Blueprint: `lem:equations`. -/
theorem codim_inter [FiniteDimensional k V] {I : List 𝒜} (h : inter I ≠ ⊥) :
    codim (inter I) =
      finrank k (Submodule.span k
        ((fun H : 𝒜 ↦ (equation (H : AffineSubspace k V)).linear) '' {H | H ∈ I})) := by
  have hinter : inter I = ⨅ H : {H // H ∈ I}, ((H : 𝒜) : AffineSubspace k V) := by
    rw [inter, iInf_subtype']
  rw [hinter] at h ⊢
  rw [codim_iInf_of_isEquation (fun H ↦ isEquation_equation (𝒜.isHyperplane H.1.2)) h,
    Set.image_eq_range]
  rfl

/-- Restricting the representatives of a list of retained hyperplanes gives back their
intersection. -/
theorem comap_inter_map_representative (I : List (𝒜.restriction H)) :
    (inter (I.map representative)).comap (chart H) = inter I := by
  induction I with
  | nil => simp [AffineSubspace.comap_top]
  | cons L I ih => simp [AffineSubspace.comap_inf, ih]

/-- Under the identification of `H.direction` with `H`, the intersection of a list of retained
hyperplanes is the intersection of `H` with their representatives.

Blueprint: `lem:representatives`. -/
theorem map_chart_inter (hH : H ≠ ⊥) (I : List (𝒜.restriction H)) :
    (inter I).map (chart H) = H ⊓ inter (I.map representative) := by
  rw [← comap_inter_map_representative, map_chart_comap_chart hH]

/-- A list of retained hyperplanes has empty intersection exactly when `H` together with their
representatives does.

Blueprint: `lem:representatives`. -/
theorem inter_eq_bot_iff (hH : H ≠ ⊥) (I : List (𝒜.restriction H)) :
    inter I = ⊥ ↔ H ⊓ inter (I.map representative) = ⊥ := by
  rw [← map_chart_inter hH, AffineSubspace.map_eq_bot_iff]

/-- The codimension in `V` of `H` together with a list of representatives is one more than the
codimension in `H.direction` of the retained hyperplanes.

Blueprint: `lem:representatives`. -/
theorem codim_inf_inter_map_representative [FiniteDimensional k V] (hH : IsHyperplane H)
    (I : List (𝒜.restriction H)) :
    codim (H ⊓ inter (I.map representative)) = codim (inter I) + 1 := by
  rw [← map_chart_inter hH.ne_bot, codim_map_chart, hH.codim_eq_one]

end Arrangement

end OrlikSolomon
