/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Hyperplane

/-!
# Parametrizing an affine subspace by its direction

This file defines `chart X : X.direction →ᵃ[k] V`, which identifies a nonempty affine subspace `X`
of `V` with the vector space `X.direction`. It then transports hyperplanes and equations along this
identification. Restricting an arrangement to a hyperplane `H` changes the ambient vector space to
`H.direction`, and this file contains what that step needs for one hyperplane at a time. The
results about arrangements are in `OrlikSolomon/Geometry/Arrangement.lean`.

Most results here hold for an affine subspace `X` of any codimension, as `lem:small-targets` needs.

## Main definitions

* `OrlikSolomon.chart`: the parametrization. This is the only place in the library where a base
  point is chosen, and its definition is not exposed to importing modules.
* `OrlikSolomon.IsHyperplaneIn`, `OrlikSolomon.hyperplaneEquiv`: the hyperplanes of `X` correspond
  to the hyperplanes of the vector space `X.direction`.

## Main results

* `OrlikSolomon.map_chart_comap_chart`: pulling `K` back along `chart X` and pushing it forward
  again gives `X ⊓ K`.
* `OrlikSolomon.exists_retraction`, `OrlikSolomon.chart_apply_of_comp_eq_id`: `chart X` has an
  affine retraction, which is a section of it on `X`.
* `OrlikSolomon.codim_map_chart`: codimensions add up along `chart X`.
* `OrlikSolomon.isHyperplane_comap_chart_iff`, `OrlikSolomon.IsEquation.comp_chart_of_not_le`: a
  hyperplane `K` restricts to a hyperplane of `X.direction` exactly when `X` meets `K` and is not
  contained in it, and its equations restrict to equations.
* `OrlikSolomon.IsEquation.exists_comp_chart_eq_const`: an equation for a hyperplane disjoint from
  `X` restricts to a nonzero constant.
* `OrlikSolomon.IsEquation.comp_chart_eq_const_or_smul`: the restriction of an equation for `K ≠ H`
  to a hyperplane `H` is a nonzero constant or a nonzero scalar multiple of an equation for its
  trace.

## Blueprint

The identification of `H` with its direction in `def:deletion`, and the part of
`lem:restriction-geometry` about a single restricted hyperplane.
-/

@[expose] public section

open Module

universe u

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-! ### The parametrization -/

section Chart

variable {X : AffineSubspace k V}

/-- The parametrization `v ↦ v + p₀` of an affine subspace `X` by its direction, for a base point
`p₀` chosen once and for all here. It takes values in `X` when `X ≠ ⊥`. The definition is not
exposed to importing modules, so their proofs can only use the lemmas below, and they cannot depend
on how `p₀` was chosen.

The base point is not literally hidden, because `chart X 0` names it. Nothing says which point of
`X` it is, so a statement whose truth depends on that point cannot be decided. For example, for a
hyperplane `L` of `X.direction`, the statement `0 ∈ L` says that `chart X 0` lies in the hyperplane
of `X` corresponding to `L`. A notion such as "central" must therefore not be phrased as
`∀ L, 0 ∈ L` if it may be applied to a restriction. -/
@[no_expose]
noncomputable def chart (X : AffineSubspace k V) : X.direction →ᵃ[k] V :=
  X.direction.subtype.toAffineMap + AffineMap.const k X.direction (Classical.epsilon (· ∈ X))

@[simp]
theorem chart_linear (X : AffineSubspace k V) : (chart X).linear = X.direction.subtype := by
  simp [chart]

theorem chart_add (X : AffineSubspace k V) (v w : X.direction) :
    chart X (v + w) = (v : V) + chart X w := by
  simp [chart, add_assoc]

theorem chart_sub_chart (X : AffineSubspace k V) (v w : X.direction) :
    chart X v - chart X w = (v : V) - w := by
  simp [chart]

theorem chart_injective (X : AffineSubspace k V) : Function.Injective (chart X) := fun v w h ↦ by
  have := chart_sub_chart X v w
  rw [h, sub_self] at this
  exact Subtype.ext (sub_eq_zero.1 this.symm)

theorem chart_mem (hX : X ≠ ⊥) (v : X.direction) : chart X v ∈ X := by
  have h0 : Classical.epsilon (· ∈ X) ∈ X :=
    Classical.epsilon_spec ((AffineSubspace.nonempty_iff_ne_bot X).2 hX)
  simpa [chart] using AffineSubspace.vadd_mem_of_mem_direction v.2 h0

theorem exists_chart_eq (hX : X ≠ ⊥) {x : V} (hx : x ∈ X) : ∃ v, chart X v = x := by
  refine ⟨⟨x - chart X 0, AffineSubspace.vsub_mem_direction hx (chart_mem hX 0)⟩, ?_⟩
  have := chart_add X ⟨x - chart X 0, AffineSubspace.vsub_mem_direction hx (chart_mem hX 0)⟩ 0
  simpa using this

/-- The parametrization of an affine subspace has an affine retraction. By
`chart_apply_of_comp_eq_id`, any retraction is also a section of `chart X` on `X`. -/
theorem exists_retraction (X : AffineSubspace k V) :
    ∃ r : V →ᵃ[k] X.direction, r.comp (chart X) = AffineMap.id k X.direction := by
  obtain ⟨ρ, hρ⟩ := X.direction.subtype.exists_leftInverse_of_injective X.direction.ker_subtype
  refine ⟨ρ.toAffineMap - AffineMap.const k V (ρ (chart X 0)), AffineMap.ext fun v ↦ ?_⟩
  have hv : ρ v = v := LinearMap.congr_fun hρ v
  have := chart_sub_chart X v 0
  simp only [ZeroMemClass.coe_zero, sub_zero] at this
  simp [← map_sub, this, hv]

/-- A retraction of `chart X` is a section of it on `X`. So an affine map `φ` landing in `X` factors
as `(chart X).comp (r.comp φ)`. -/
theorem chart_apply_of_comp_eq_id {r : V →ᵃ[k] X.direction}
    (hr : r.comp (chart X) = AffineMap.id k X.direction) {x : V} (hx : x ∈ X) :
    chart X (r x) = x := by
  obtain ⟨v, rfl⟩ := exists_chart_eq ((AffineSubspace.nonempty_iff_ne_bot X).1 ⟨x, hx⟩) hx
  rw [← AffineMap.comp_apply r, hr, AffineMap.id_apply]

theorem map_chart_le (hX : X ≠ ⊥) (M : AffineSubspace k X.direction) :
    M.map (chart X) ≤ X := by
  rintro _ ⟨v, _, rfl⟩
  exact chart_mem hX v

/-- The base-point-free description of a subspace pulled back along `chart X` and pushed forward
again: it is the intersection with `X`. -/
theorem map_chart_comap_chart (hX : X ≠ ⊥) (K : AffineSubspace k V) :
    (K.comap (chart X)).map (chart X) = X ⊓ K := by
  ext x
  simp only [AffineSubspace.mem_map, AffineSubspace.mem_comap, AffineSubspace.mem_inf_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨chart_mem hX v, hv⟩
  · rintro ⟨hxX, hxK⟩
    obtain ⟨v, rfl⟩ := exists_chart_eq hX hxX
    exact ⟨v, hxK, rfl⟩

@[simp]
theorem comap_chart_map_chart (M : AffineSubspace k X.direction) :
    (M.map (chart X)).comap (chart X) = M :=
  AffineSubspace.comap_map_eq_of_injective (chart_injective X) M

theorem map_chart_injective :
    Function.Injective (AffineSubspace.map (chart X) : _ → AffineSubspace k V) :=
  Function.LeftInverse.injective comap_chart_map_chart

theorem comap_chart_self (hX : X ≠ ⊥) : X.comap (chart X) = ⊤ := by
  ext v
  simp [chart_mem hX]

theorem map_chart_top (hX : X ≠ ⊥) : (⊤ : AffineSubspace k X.direction).map (chart X) = X := by
  rw [← comap_chart_self hX, map_chart_comap_chart hX, inf_idem]

theorem comap_chart_inf (hX : X ≠ ⊥) (K : AffineSubspace k V) :
    (X ⊓ K).comap (chart X) = K.comap (chart X) := by
  rw [AffineSubspace.comap_inf, comap_chart_self hX, top_inf_eq]

theorem comap_chart_eq_bot_iff (hX : X ≠ ⊥) {K : AffineSubspace k V} :
    K.comap (chart X) = ⊥ ↔ X ⊓ K = ⊥ := by
  rw [← map_chart_comap_chart hX, AffineSubspace.map_eq_bot_iff]

theorem comap_chart_eq_top_iff (hX : X ≠ ⊥) {K : AffineSubspace k V} :
    K.comap (chart X) = ⊤ ↔ X ≤ K := by
  rw [eq_top_iff, ← AffineSubspace.map_le_iff_le_comap, map_chart_top hX]

/-- Two subspaces have the same pullback along `chart X` exactly when they meet `X` in the same
set, which does not mention the base point. -/
theorem comap_chart_eq_comap_chart_iff (hX : X ≠ ⊥) {K K' : AffineSubspace k V} :
    K.comap (chart X) = K'.comap (chart X) ↔ X ⊓ K = X ⊓ K' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← map_chart_comap_chart hX, h, map_chart_comap_chart hX]
  · rw [← comap_chart_inf hX K, h, comap_chart_inf hX]

/-- The intersection of the pullbacks along `chart X` of a family of subspaces corresponds to the
intersection of the family with `X`. -/
theorem map_chart_iInf_comap_chart (hX : X ≠ ⊥) {ι : Sort*} (K : ι → AffineSubspace k V) :
    (⨅ i, (K i).comap (chart X)).map (chart X) = X ⊓ ⨅ i, K i := by
  rw [← AffineSubspace.comap_supr, map_chart_comap_chart hX]

/-- The set-indexed form of `map_chart_iInf_comap_chart`. -/
theorem map_chart_sInf_image_comap_chart (hX : X ≠ ⊥) (S : Set (AffineSubspace k V)) :
    (sInf (AffineSubspace.comap (chart X) '' S)).map (chart X) = X ⊓ sInf S := by
  rw [sInf_image, sInf_eq_iInf', ← map_chart_iInf_comap_chart hX, iInf_subtype']

theorem direction_map_chart (M : AffineSubspace k X.direction) :
    (M.map (chart X)).direction = M.direction.map X.direction.subtype := by
  simp

@[simp]
theorem finrank_direction_map_chart (M : AffineSubspace k X.direction) :
    finrank k (M.map (chart X)).direction = finrank k M.direction := by
  rw [direction_map_chart]
  exact LinearEquiv.finrank_eq (Submodule.equivSubtypeMap X.direction M.direction).symm

/-- The dimension of the image of `M` under `chart X` agrees with that of `M`, so codimensions
add up. -/
theorem codim_map_chart [FiniteDimensional k V] (M : AffineSubspace k X.direction) :
    codim (M.map (chart X)) = codim M + codim X := by
  have h1 := codim_add_finrank_direction (M.map (chart X))
  have h2 := codim_add_finrank_direction M
  have h3 := codim_add_finrank_direction X
  rw [finrank_direction_map_chart] at h1
  omega

/-- Codimension in `V` versus codimension in `X` of a trace on `X`. -/
theorem codim_inf_eq_codim_comap_chart_add [FiniteDimensional k V] (hX : X ≠ ⊥)
    (K : AffineSubspace k V) : codim (X ⊓ K) = codim (K.comap (chart X)) + codim X := by
  rw [← map_chart_comap_chart hX, codim_map_chart]

/-- If the direction of `X` carries a hyperplane then `X` is nonempty. -/
theorem ne_bot_of_isHyperplane {M : AffineSubspace k X.direction} (hM : IsHyperplane M) :
    X ≠ ⊥ := by
  rintro rfl
  have : Subsingleton (⊥ : AffineSubspace k V).direction := by
    rw [AffineSubspace.direction_bot]
    infer_instance
  exact not_isHyperplane_of_subsingleton M hM

end Chart

/-! ### Hyperplanes of an affine subspace -/

section HyperplaneIn

variable {L X : AffineSubspace k V}

/-- `L` is a hyperplane of the affine space `X`: a nonempty affine subspace of `X` whose direction
is covered by that of `X`, in other words of codimension one in it.

Blueprint: `lem:restriction-geometry`. -/
structure IsHyperplaneIn (L X : AffineSubspace k V) : Prop where
  /-- A hyperplane of `X` is contained in `X`. -/
  le : L ≤ X
  /-- A hyperplane of `X` is nonempty. -/
  ne_bot : L ≠ ⊥
  /-- The direction of a hyperplane of `X` has codimension one in the direction of `X`. -/
  direction_covBy : L.direction ⋖ X.direction

theorem isHyperplaneIn_iff {L X : AffineSubspace k V} :
    IsHyperplaneIn L X ↔ L ≤ X ∧ L ≠ ⊥ ∧ L.direction ⋖ X.direction :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

@[simp]
theorem isHyperplaneIn_top_iff : IsHyperplaneIn L ⊤ ↔ IsHyperplane L := by
  rw [isHyperplaneIn_iff, AffineSubspace.direction_top k V V, covBy_top_iff]
  exact ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨le_top, h.1, h.2⟩⟩

theorem IsHyperplaneIn.ne_bot_right (hL : IsHyperplaneIn L X) : X ≠ ⊥ := by
  rintro rfl
  exact hL.ne_bot (le_bot_iff.1 hL.le)

/-- The hyperplanes of `X` in `V` are the images of the hyperplanes of the vector space
`X.direction`. -/
theorem isHyperplaneIn_map_chart_iff (hX : X ≠ ⊥) {M : AffineSubspace k X.direction} :
    IsHyperplaneIn (M.map (chart X)) X ↔ IsHyperplane M := by
  have key : M.direction.map X.direction.subtype ⋖ X.direction ↔ IsCoatom M.direction := by
    rw [covBy_iff_quot_is_simple (Submodule.map_subtype_le _ _),
      isSimpleModule_iff_isCoatom,
      Submodule.comap_map_eq_of_injective X.direction.injective_subtype]
  rw [isHyperplaneIn_iff, direction_map_chart, key, Ne, AffineSubspace.map_eq_bot_iff]
  exact ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨map_chart_le hX M, h.1, h.2⟩⟩

theorem IsHyperplaneIn.map_chart_comap_chart (hL : IsHyperplaneIn L X) :
    (L.comap (chart X)).map (chart X) = L := by
  rw [OrlikSolomon.map_chart_comap_chart hL.ne_bot_right, inf_eq_right.2 hL.le]

theorem IsHyperplaneIn.isHyperplane_comap_chart (hL : IsHyperplaneIn L X) :
    IsHyperplane (L.comap (chart X)) := by
  rw [← isHyperplaneIn_map_chart_iff hL.ne_bot_right, hL.map_chart_comap_chart]
  exact hL

/-- A hyperplane of `X` has codimension one more than `X`. -/
theorem IsHyperplaneIn.codim_eq_add_one [FiniteDimensional k V] (hL : IsHyperplaneIn L X) :
    codim L = codim X + 1 := by
  rw [← hL.map_chart_comap_chart, codim_map_chart, hL.isHyperplane_comap_chart.codim_eq_one,
    add_comm]

/-- The correspondence between the hyperplanes of the affine space `X` and those of the vector
space `X.direction`: it is `L ↦ L.comap (chart X)`, with inverse `M ↦ M.map (chart X)`.

Blueprint: `def:deletion`. -/
noncomputable def hyperplaneEquiv (X : AffineSubspace k V) :
    {L : AffineSubspace k V // IsHyperplaneIn L X} ≃
      {M : AffineSubspace k X.direction // IsHyperplane M} where
  toFun L := ⟨L.1.comap (chart X), L.2.isHyperplane_comap_chart⟩
  invFun M := ⟨M.1.map (chart X),
    (isHyperplaneIn_map_chart_iff (ne_bot_of_isHyperplane M.2)).2 M.2⟩
  left_inv L := Subtype.ext L.2.map_chart_comap_chart
  right_inv M := Subtype.ext (comap_chart_map_chart M.1)

@[simp]
theorem coe_hyperplaneEquiv (L : {L : AffineSubspace k V // IsHyperplaneIn L X}) :
    (hyperplaneEquiv X L : AffineSubspace k X.direction) = L.1.comap (chart X) :=
  rfl

@[simp]
theorem coe_hyperplaneEquiv_symm (M : {M : AffineSubspace k X.direction // IsHyperplane M}) :
    ((hyperplaneEquiv X).symm M : AffineSubspace k V) = M.1.map (chart X) :=
  rfl

end HyperplaneIn

/-! ### Restricting hyperplanes and equations -/

section Restrict

variable {f : V →ᵃ[k] k} {X H K : AffineSubspace k V}

/-- An equation for `H` vanishes on `H`. -/
theorem IsEquation.comp_chart_self (hf : IsEquation f H) : f.comp (chart H) = 0 :=
  AffineMap.ext fun v ↦ hf.apply_eq_zero_iff.2 (chart_mem hf.isHyperplane.ne_bot v)

/-- The restriction to `X` of an equation for a hyperplane `K` that meets `X` without containing it
is an equation for the trace of `K` on `X`. Here `X` has any codimension.

Blueprint: `lem:restriction-geometry`. -/
theorem IsEquation.comp_chart_of_not_le (hf : IsEquation f K) (hle : ¬X ≤ K) (hbot : X ⊓ K ≠ ⊥) :
    IsEquation (f.comp (chart X)) (K.comap (chart X)) := by
  refine ⟨fun h0 ↦ hle ?_, by rw [zeroLocus_comp, hf.zeroLocus_eq]⟩
  obtain ⟨p, hpX, hpK⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 hbot
  refine AffineSubspace.le_of_direction_le (fun v hv ↦ ?_) ⟨p, hpX, hpK⟩
  rw [hf.direction_eq, LinearMap.mem_ker]
  simpa using LinearMap.congr_fun h0 ⟨v, hv⟩

/-- The restriction to a hyperplane `H` of an equation for a different hyperplane meeting `H` is an
equation for the retained hyperplane. See `IsEquation.comp_chart_of_not_le` for any codimension.

Blueprint: `lem:restriction-geometry`. -/
theorem IsEquation.comp_chart (hH : IsHyperplane H) (hf : IsEquation f K) (hne : K ≠ H)
    (hbot : H ⊓ K ≠ ⊥) : IsEquation (f.comp (chart H)) (K.comap (chart H)) :=
  hf.comp_chart_of_not_le (hH.not_le_of_ne hf.isHyperplane hne.symm) hbot

/-- The restriction to `H` of an equation for a hyperplane disjoint from `H` is a nonzero constant.

Blueprint: `lem:restriction-geometry`. -/
theorem IsEquation.exists_comp_chart_eq_const (hH : H ≠ ⊥) (hf : IsEquation f K)
    (hbot : H ⊓ K = ⊥) : ∃ c : kˣ, f.comp (chart H) = AffineMap.const k H.direction (c : k) := by
  have hzero : zeroLocus (f.comp (chart H)) = ⊥ := by
    rw [zeroLocus_comp, hf.zeroLocus_eq, comap_chart_eq_bot_iff hH, hbot]
  have hlin : (f.comp (chart H)).linear = 0 := by
    by_contra h
    exact zeroLocus_ne_bot h hzero
  obtain ⟨c, hc⟩ := (AffineMap.linear_eq_zero_iff_exists_const _).1 hlin
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hmem : (0 : H.direction) ∈ zeroLocus (f.comp (chart H)) := by
      rw [mem_zeroLocus, hc, AffineMap.const_apply]
    rw [hzero] at hmem
    exact AffineSubspace.notMem_bot k _ _ hmem
  exact ⟨Units.mk0 c hc0, hc⟩

/-- A hyperplane `K` restricts to a hyperplane of `X.direction`, for a nonempty affine subspace `X`
of any codimension, exactly when `X` meets `K` and is not contained in it.

Blueprint: `lem:restriction-geometry`. -/
theorem isHyperplane_comap_chart_iff (hX : X ≠ ⊥) (hK : IsHyperplane K) :
    IsHyperplane (K.comap (chart X)) ↔ ¬X ≤ K ∧ X ⊓ K ≠ ⊥ := by
  refine ⟨fun h ↦ ⟨fun hle ↦ ?_, fun hb ↦ ?_⟩, fun h ↦ ?_⟩
  · exact h.ne_top ((comap_chart_eq_top_iff hX).2 hle)
  · exact h.ne_bot ((comap_chart_eq_bot_iff hX).2 hb)
  · exact ((isEquation_equation hK).comp_chart_of_not_le h.1 h.2).isHyperplane

/-- A hyperplane `K` restricts to a hyperplane of `H.direction`, for a hyperplane `H`, exactly when
`K ≠ H` and `K` meets `H`. See `isHyperplane_comap_chart_iff` for any codimension.

Blueprint: `lem:restriction-geometry`. -/
theorem IsHyperplane.isHyperplane_comap_chart_iff (hH : IsHyperplane H) (hK : IsHyperplane K) :
    IsHyperplane (K.comap (chart H)) ↔ K ≠ H ∧ H ⊓ K ≠ ⊥ := by
  rw [OrlikSolomon.isHyperplane_comap_chart_iff hH.ne_bot hK]
  refine and_congr_left fun _ ↦ ⟨?_, fun hne ↦ hH.not_le_of_ne hK hne.symm⟩
  rintro hle rfl
  exact hle le_rfl

/-- A retained intersection is a hyperplane of `H`.

Blueprint: `lem:restriction-geometry`. -/
theorem IsHyperplane.isHyperplaneIn_inf (hH : IsHyperplane H) (hK : IsHyperplane K) (hne : K ≠ H)
    (hbot : H ⊓ K ≠ ⊥) : IsHyperplaneIn (H ⊓ K) H := by
  rw [← map_chart_comap_chart hH.ne_bot, isHyperplaneIn_map_chart_iff hH.ne_bot,
    hH.isHyperplane_comap_chart_iff hK]
  exact ⟨hne, hbot⟩

/-- The restriction to `H` of an equation for a different hyperplane `K` is either a nonzero
constant or a nonzero scalar multiple of the chosen equation of its retained hyperplane.

Blueprint: `lem:restriction-geometry`. -/
theorem IsEquation.comp_chart_eq_const_or_smul (hH : IsHyperplane H) (hf : IsEquation f K)
    (hne : K ≠ H) :
    (∃ c : kˣ, f.comp (chart H) = AffineMap.const k H.direction (c : k)) ∨
      (IsHyperplane (K.comap (chart H)) ∧
        ∃ c : kˣ, f.comp (chart H) = (c : k) • equation (K.comap (chart H))) := by
  by_cases hbot : H ⊓ K = ⊥
  · exact Or.inl (hf.exists_comp_chart_eq_const hH.ne_bot hbot)
  · have hg := hf.comp_chart hH hne hbot
    exact Or.inr ⟨hg.isHyperplane,
      ((isEquation_equation hg.isHyperplane).existsUnique_smul hg).exists⟩

end Restrict

end OrlikSolomon
