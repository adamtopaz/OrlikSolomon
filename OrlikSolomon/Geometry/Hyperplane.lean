/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Affine hyperplanes and their equations

This file contains the linear algebra of a single hyperplane, or of a family of them, in a vector
space `V` over an arbitrary field `k`. It does not mention arrangements, rings of functions or
rational points of varieties: `OrlikSolomon/Geometry/Arrangement.lean` builds on it.

Affine subspaces form a complete lattice, whose bottom element `⊥` is the empty subspace, so the
intersection of a family is `⨅ i, H i` or `sInf S`, and "nonempty" is written `X ≠ ⊥`. A nonempty
intersection automatically has a `k`-point, since an affine subspace is a set of `k`-points. The
dimension of `X` is `Module.finrank k X.direction`.

## Main definitions

* `OrlikSolomon.IsHyperplane`: a nonempty affine subspace whose direction has codimension one.
* `OrlikSolomon.zeroLocus`, `OrlikSolomon.IsEquation`: an equation for `H` is an affine map
  `V →ᵃ[k] k` with nonzero linear part and zero locus `H`.
* `OrlikSolomon.equation`: a chosen equation of a hyperplane.
* `OrlikSolomon.codim`: the codimension of an affine subspace.
* `OrlikSolomon.chart`: the parametrization of a nonempty affine subspace `X` by the vector space
  `X.direction`. This is the only place in the library where a base point is chosen.
* `OrlikSolomon.IsHyperplaneIn`, `OrlikSolomon.hyperplaneEquiv`: the hyperplanes of `X` correspond
  to the hyperplanes of the vector space `X.direction`.

## Main results

* `OrlikSolomon.IsHyperplane.exists_isEquation`: every hyperplane has an equation.
* `OrlikSolomon.IsEquation.existsUnique_smul`: two equations for a hyperplane differ by a unique
  unit of `k`.
* `OrlikSolomon.direction_iInf_of_isEquation`, `OrlikSolomon.codim_iInf_of_isEquation`: the
  direction of a nonempty intersection of hyperplanes is the intersection of the kernels of the
  linear parts of their equations, and its codimension is the rank of the system.
* `OrlikSolomon.IsHyperplane.isHyperplane_comap_chart_iff`: a hyperplane `K` restricts to a
  hyperplane of `H` exactly when `K ≠ H` and `K` meets `H`.
* `OrlikSolomon.IsEquation.comp_chart_eq_const_or_smul`: the restriction of an equation for `K ≠ H`
  is a nonzero constant or a nonzero scalar multiple of an equation for its trace.

## Implementation notes

The field `k` is arbitrary and may be finite, and no statement needs `2` to be invertible. The
space `V` may have dimension zero, in which case it has no hyperplanes. It lives in the universe of
`k`, so that `H.direction`, `Fin n → k` and `V` can all be quantified over together, as induction
on arrangements requires. Finite-dimensionality is assumed only where it is used.

## Blueprint

`def:arrangement` (hyperplanes and equations), `lem:equations`, and the part of
`lem:restriction-geometry` about a single restricted hyperplane.
-/

@[expose] public section

open Module

universe u

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

/-! ### Zero loci of affine functions -/

section ZeroLocus

/-- The zero locus of an affine function `f : V → k`, as an affine subspace of `V`. It is `⊤` when
`f = 0` and `⊥` when `f` is a nonzero constant. -/
def zeroLocus (f : V →ᵃ[k] k) : AffineSubspace k V :=
  AffineSubspace.comap f {0}

@[simp]
theorem mem_zeroLocus {f : V →ᵃ[k] k} {x : V} : x ∈ zeroLocus f ↔ f x = 0 := by
  simp [zeroLocus]

theorem zeroLocus_comp {W : Type u} [AddCommGroup W] [Module k W] (f : V →ᵃ[k] k)
    (φ : W →ᵃ[k] V) : zeroLocus (f.comp φ) = (zeroLocus f).comap φ := by
  ext x
  simp

theorem zeroLocus_smul {c : k} (hc : c ≠ 0) (f : V →ᵃ[k] k) : zeroLocus (c • f) = zeroLocus f := by
  ext x
  simp [hc]

/-- A nonempty zero locus has direction the kernel of the linear part. -/
theorem direction_zeroLocus {f : V →ᵃ[k] k} (h : zeroLocus f ≠ ⊥) :
    (zeroLocus f).direction = LinearMap.ker f.linear := by
  rw [zeroLocus, AffineSubspace.direction_comap h, AffineSubspace.direction_singleton]
  rfl

/-- An affine function with nonzero linear part has a zero over `k`, for any field `k`. -/
theorem zeroLocus_ne_bot {f : V →ᵃ[k] k} (hf : f.linear ≠ 0) : zeroLocus f ≠ ⊥ := by
  obtain ⟨v, hv⟩ := LinearMap.surjective hf (-f 0)
  rw [← AffineSubspace.nonempty_iff_ne_bot]
  exact ⟨v, mem_zeroLocus.2 (by simp [congrFun f.decomp v, hv])⟩

end ZeroLocus

/-! ### Hyperplanes -/

section Hyperplane

variable {H K : AffineSubspace k V}

/-- An affine hyperplane in `V`: a nonempty affine subspace whose direction has codimension one,
which is expressed by the direction being a coatom of the lattice of linear subspaces. A zero
dimensional space has no hyperplanes.

Blueprint: `def:arrangement`. -/
structure IsHyperplane (H : AffineSubspace k V) : Prop where
  /-- A hyperplane is nonempty. -/
  ne_bot : H ≠ ⊥
  /-- The direction of a hyperplane has codimension one. -/
  isCoatom_direction : IsCoatom H.direction

theorem IsHyperplane.nonempty (hH : IsHyperplane H) : (H : Set V).Nonempty :=
  (AffineSubspace.nonempty_iff_ne_bot H).2 hH.ne_bot

theorem IsHyperplane.ne_top (hH : IsHyperplane H) : H ≠ ⊤ := by
  rintro rfl
  exact hH.isCoatom_direction.1 (AffineSubspace.direction_top k V V)

/-- A zero-dimensional space has no hyperplanes. -/
theorem IsHyperplane.not_of_subsingleton [Subsingleton V] (H : AffineSubspace k V) :
    ¬IsHyperplane H :=
  fun hH ↦ hH.isCoatom_direction.1 (Subsingleton.elim _ _)

/-- A hyperplane contained in a hyperplane is equal to it. -/
theorem IsHyperplane.eq_of_le (hH : IsHyperplane H) (hK : IsHyperplane K) (h : H ≤ K) : H = K := by
  refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_ hH.nonempty h
  obtain h' | h' := (AffineSubspace.direction_le h).eq_or_lt
  · exact h'
  · exact absurd (hH.isCoatom_direction.2 _ h') hK.isCoatom_direction.1

/-- A hyperplane is not contained in a different hyperplane. -/
theorem IsHyperplane.not_le_of_ne (hH : IsHyperplane H) (hK : IsHyperplane K) (h : H ≠ K) :
    ¬H ≤ K :=
  fun hle ↦ h (hH.eq_of_le hK hle)

/-- The zero locus of an affine function is a hyperplane exactly when its linear part is nonzero:
otherwise the function is constant, and its zero locus is empty or the whole space. -/
theorem isHyperplane_zeroLocus_iff {f : V →ᵃ[k] k} :
    IsHyperplane (zeroLocus f) ↔ f.linear ≠ 0 := by
  constructor
  · intro h hf
    have hdir := direction_zeroLocus h.ne_bot
    rw [hf, LinearMap.ker_zero] at hdir
    exact h.isCoatom_direction.1 hdir
  · intro hf
    refine ⟨zeroLocus_ne_bot hf, ?_⟩
    rw [direction_zeroLocus (zeroLocus_ne_bot hf)]
    exact LinearMap.isCoatom_ker_of_surjective (LinearMap.surjective hf)

end Hyperplane

/-! ### Equations -/

section Equation

variable {f g : V →ᵃ[k] k} {H : AffineSubspace k V}

/-- `f` is an equation for `H`: an affine function with nonzero linear part and zero locus `H`.

Blueprint: `def:arrangement`. -/
structure IsEquation (f : V →ᵃ[k] k) (H : AffineSubspace k V) : Prop where
  /-- The linear part of an equation is nonzero. -/
  linear_ne_zero : f.linear ≠ 0
  /-- The zero locus of an equation for `H` is `H`. -/
  zeroLocus_eq : zeroLocus f = H

theorem isEquation_zeroLocus (hf : f.linear ≠ 0) : IsEquation f (zeroLocus f) :=
  ⟨hf, rfl⟩

theorem IsEquation.apply_eq_zero_iff (hf : IsEquation f H) {x : V} : f x = 0 ↔ x ∈ H := by
  rw [← hf.zeroLocus_eq, mem_zeroLocus]

theorem IsEquation.isHyperplane (hf : IsEquation f H) : IsHyperplane H :=
  hf.zeroLocus_eq ▸ isHyperplane_zeroLocus_iff.2 hf.linear_ne_zero

theorem IsEquation.direction_eq (hf : IsEquation f H) : H.direction = LinearMap.ker f.linear := by
  rw [← hf.zeroLocus_eq, direction_zeroLocus (zeroLocus_ne_bot hf.linear_ne_zero)]

theorem IsEquation.smul (hf : IsEquation f H) {c : k} (hc : c ≠ 0) : IsEquation (c • f) H :=
  ⟨by simpa [hc] using hf.linear_ne_zero, by rw [zeroLocus_smul hc, hf.zeroLocus_eq]⟩

/-- Every hyperplane has an equation.

Blueprint: `lem:equations`. -/
theorem IsHyperplane.exists_isEquation (hH : IsHyperplane H) : ∃ f : V →ᵃ[k] k, IsEquation f H := by
  obtain ⟨p, hp⟩ := hH.nonempty
  obtain ⟨φ, hφ, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hH.isCoatom_direction.lt_top inferInstance
  have hker : H.direction = LinearMap.ker φ := by
    obtain h | h := (LinearMap.le_ker_iff_map.2 hmap).eq_or_lt
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 (hH.isCoatom_direction.2 _ h)) hφ
  refine ⟨φ.toAffineMap - AffineMap.const k V (φ p), by simpa using hφ, ?_⟩
  ext x
  rw [mem_zeroLocus, ← AffineSubspace.vsub_right_mem_direction_iff_mem hp, hker, LinearMap.mem_ker,
    vsub_eq_sub, map_sub]
  simp

theorem isHyperplane_iff_exists_isEquation :
    IsHyperplane H ↔ ∃ f : V →ᵃ[k] k, IsEquation f H :=
  ⟨IsHyperplane.exists_isEquation, fun ⟨_, hf⟩ ↦ hf.isHyperplane⟩

/-- An affine function vanishing on a hyperplane is a scalar multiple of any equation for it. -/
theorem IsEquation.exists_eq_smul (hf : IsEquation f H) (hg : ∀ x ∈ H, g x = 0) :
    ∃ c : k, g = c • f := by
  obtain ⟨p, hp⟩ := hf.isHyperplane.nonempty
  have hfp : f p = 0 := hf.apply_eq_zero_iff.2 hp
  have hgp : g p = 0 := hg p hp
  obtain ⟨v, hv⟩ := LinearMap.surjective hf.linear_ne_zero 1
  have key (w : V) : g.linear w = f.linear w * g.linear v := by
    have hmem : (w - f.linear w • v) +ᵥ p ∈ H := by
      rw [← hf.apply_eq_zero_iff, AffineMap.map_vadd, hfp]
      simp [hv]
    have := hg _ hmem
    rw [AffineMap.map_vadd, hgp] at this
    simpa [sub_eq_zero] using this
  refine ⟨g.linear v, AffineMap.ext fun x ↦ ?_⟩
  have hx : x = (x - p) +ᵥ p := by simp
  rw [hx, AffineMap.map_vadd, hgp, AffineMap.coe_smul, Pi.smul_apply, AffineMap.map_vadd, hfp, key]
  simp [mul_comm]

/-- Two equations for the same hyperplane differ by a unique unit of `k`.

Blueprint: `lem:equations`. -/
theorem IsEquation.existsUnique_smul (hf : IsEquation f H) (hg : IsEquation g H) :
    ∃! c : kˣ, g = (c : k) • f := by
  obtain ⟨c, rfl⟩ := hf.exists_eq_smul fun x hx ↦ hg.apply_eq_zero_iff.2 hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hg.linear_ne_zero (by simp)
  refine ⟨Units.mk0 c hc, rfl, fun c' hc' ↦ Units.ext ?_⟩
  obtain ⟨v, hv⟩ := LinearMap.surjective hf.linear_ne_zero 1
  have := congrArg (fun h : V →ᵃ[k] k ↦ h.linear v) hc'
  simpa [hv] using this.symm

/-- A chosen equation of an affine subspace, used for the hyperplanes of an arrangement. It is
characterized up to a unit by `isEquation_equation` and `IsEquation.existsUnique_smul`, and it is a
junk value when `H` is not a hyperplane.

Blueprint: `lem:equations`. -/
noncomputable def equation (H : AffineSubspace k V) : V →ᵃ[k] k :=
  Classical.epsilon fun f ↦ IsEquation f H

theorem isEquation_equation (hH : IsHyperplane H) : IsEquation (equation H) H :=
  Classical.epsilon_spec hH.exists_isEquation

end Equation

/-! ### Codimension -/

section Codim

variable {X Y H : AffineSubspace k V}

/-- The codimension of an affine subspace: the dimension of the quotient of `V` by its direction.
The dimension of `X` itself is `Module.finrank k X.direction`. The value on `⊥`, whose direction
is `⊥`, is only a convention, so statements about flats must assume `X ≠ ⊥`.

Blueprint: `lem:equations`. -/
noncomputable def codim (X : AffineSubspace k V) : ℕ :=
  finrank k (V ⧸ X.direction)

@[simp]
theorem codim_top : codim (⊤ : AffineSubspace k V) = 0 := by
  rw [codim, AffineSubspace.direction_top]
  exact finrank_zero_of_subsingleton

/-- A nonempty affine subspace is a hyperplane exactly when it has codimension one. -/
theorem isHyperplane_iff_codim_eq_one : IsHyperplane H ↔ H ≠ ⊥ ∧ codim H = 1 := by
  rw [codim, ← isSimpleModule_iff_finrank_eq_one, isSimpleModule_iff_isCoatom]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem IsHyperplane.codim_eq_one (hH : IsHyperplane H) : codim H = 1 :=
  (isHyperplane_iff_codim_eq_one.1 hH).2

variable [FiniteDimensional k V]

/-- Rank-nullity for an affine subspace. -/
theorem codim_add_finrank_direction (X : AffineSubspace k V) :
    codim X + finrank k X.direction = finrank k V :=
  X.direction.finrank_quotient_add_finrank

/-- The dimension of a hyperplane is one less than that of the ambient space.

Blueprint: `lem:restriction-geometry`. -/
theorem IsHyperplane.finrank_direction_add_one (hH : IsHyperplane H) :
    finrank k H.direction + 1 = finrank k V := by
  rw [← codim_add_finrank_direction H, hH.codim_eq_one, add_comm]

theorem isHyperplane_iff_finrank_direction_add_one :
    IsHyperplane H ↔ H ≠ ⊥ ∧ finrank k H.direction + 1 = finrank k V := by
  rw [isHyperplane_iff_codim_eq_one]
  refine and_congr_right fun _ ↦ ?_
  have := codim_add_finrank_direction H
  omega

theorem codim_le_finrank (X : AffineSubspace k V) : codim X ≤ finrank k V :=
  Nat.le.intro (codim_add_finrank_direction X)

theorem codim_le_codim (h : X ≤ Y) : codim Y ≤ codim X := by
  have := Submodule.finrank_mono (AffineSubspace.direction_le h)
  have := codim_add_finrank_direction X
  have := codim_add_finrank_direction Y
  omega

theorem codim_lt_codim (hX : X ≠ ⊥) (h : X < Y) : codim Y < codim X := by
  have := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty h ((AffineSubspace.nonempty_iff_ne_bot X).2 hX))
  have := codim_add_finrank_direction X
  have := codim_add_finrank_direction Y
  omega

/-- Cutting a nonempty affine subspace `X` by a hyperplane not containing it raises the
codimension by exactly one. -/
theorem IsHyperplane.codim_inf (hH : IsHyperplane H) (hne : H ⊓ X ≠ ⊥) (hle : ¬X ≤ H) :
    codim (H ⊓ X) = codim X + 1 := by
  obtain ⟨p, hpH, hpX⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 hne
  have hdir : (H ⊓ X).direction = H.direction ⊓ X.direction :=
    AffineSubspace.direction_inf_of_mem hpH hpX
  have hsup : H.direction ⊔ X.direction = ⊤ := by
    obtain h | h := (le_sup_left : H.direction ≤ H.direction ⊔ X.direction).eq_or_lt
    · exact absurd (AffineSubspace.le_of_direction_le (h ▸ le_sup_right) ⟨p, hpX, hpH⟩) hle
    · exact hH.isCoatom_direction.2 _ h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq H.direction X.direction
  have h2 := codim_add_finrank_direction (H ⊓ X)
  have h3 := codim_add_finrank_direction X
  have h4 := hH.finrank_direction_add_one
  rw [hsup, finrank_top] at h1
  rw [hdir] at h2
  omega

end Codim

/-! ### Systems of equations -/

section Systems

variable {ι : Sort*} {f : ι → V →ᵃ[k] k} {H : ι → AffineSubspace k V}

/-- A nonempty common zero locus has direction the intersection of the kernels of the linear
parts.

Blueprint: `lem:equations`. -/
theorem direction_iInf_zeroLocus (h : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    (⨅ i, zeroLocus (f i)).direction = ⨅ i, LinearMap.ker (f i).linear := by
  obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 h
  have hp' : ∀ i, p ∈ zeroLocus (f i) := (AffineSubspace.mem_iInf_iff _ p).1 hp
  rw [AffineSubspace.direction_iInf_of_mem _ p hp']
  refine iInf_congr fun i ↦ direction_zeroLocus ?_
  rw [← AffineSubspace.nonempty_iff_ne_bot]
  exact ⟨p, hp' i⟩

/-- The codimension of a nonempty common zero locus is the rank of the system of equations.

Blueprint: `lem:equations`. -/
theorem codim_iInf_zeroLocus [FiniteDimensional k V] (h : (⨅ i, zeroLocus (f i)) ≠ ⊥) :
    codim (⨅ i, zeroLocus (f i)) =
      finrank k (Submodule.span k (Set.range fun i ↦ (f i).linear)) := by
  have hco : (Submodule.span k (Set.range fun i ↦ (f i).linear)).dualCoannihilator =
      ⨅ i, LinearMap.ker (f i).linear := by
    ext x
    rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
    simp [Submodule.mem_iInf]
  have h1 := codim_add_finrank_direction (⨅ i, zeroLocus (f i))
  have h2 : finrank k (Submodule.span k (Set.range fun i ↦ (f i).linear)) +
      finrank k (⨅ i, LinearMap.ker (f i).linear : Submodule k V) = finrank k V := by
    rw [← hco]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  rw [direction_iInf_zeroLocus h] at h1
  omega

/-- The direction of a nonempty intersection of hyperplanes, in terms of their equations.

Blueprint: `lem:equations`. -/
theorem direction_iInf_of_isEquation (hf : ∀ i, IsEquation (f i) (H i)) (h : (⨅ i, H i) ≠ ⊥) :
    (⨅ i, H i).direction = ⨅ i, LinearMap.ker (f i).linear := by
  simp only [← fun i ↦ (hf i).zeroLocus_eq] at h ⊢
  exact direction_iInf_zeroLocus h

/-- The codimension of a nonempty intersection of hyperplanes is the rank of their equations.

Blueprint: `lem:equations`. -/
theorem codim_iInf_of_isEquation [FiniteDimensional k V] (hf : ∀ i, IsEquation (f i) (H i))
    (h : (⨅ i, H i) ≠ ⊥) :
    codim (⨅ i, H i) = finrank k (Submodule.span k (Set.range fun i ↦ (f i).linear)) := by
  simp only [← fun i ↦ (hf i).zeroLocus_eq] at h ⊢
  exact codim_iInf_zeroLocus h

/-- A nonempty intersection of `n` hyperplanes has codimension at most `n`. -/
theorem codim_iInf_le_card [FiniteDimensional k V] {ι : Type*} [Fintype ι]
    {H : ι → AffineSubspace k V} (hH : ∀ i, IsHyperplane (H i)) (h : (⨅ i, H i) ≠ ⊥) :
    codim (⨅ i, H i) ≤ Fintype.card ι := by
  rw [codim_iInf_of_isEquation (fun i ↦ isEquation_equation (hH i)) h]
  exact finrank_range_le_card _

end Systems

/-! ### Parametrizing an affine subspace by its direction -/

section Chart

variable {X : AffineSubspace k V}

/-- The parametrization `v ↦ v + p₀` of an affine subspace `X` by its direction, for a base point
`p₀ ∈ X` chosen once and for all here. It takes values in `X` when `X ≠ ⊥`, and the choice of `p₀`
is otherwise invisible: use the lemmas below rather than the definition.

This is what lets the restriction of an arrangement to `X` live on the vector space
`X.direction`. -/
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

/-- The parametrization of an affine subspace has an affine retraction. -/
theorem exists_retraction (X : AffineSubspace k V) :
    ∃ r : V →ᵃ[k] X.direction, r.comp (chart X) = AffineMap.id k X.direction := by
  obtain ⟨ρ, hρ⟩ := X.direction.subtype.exists_leftInverse_of_injective X.direction.ker_subtype
  refine ⟨ρ.toAffineMap - AffineMap.const k V (ρ (chart X 0)), AffineMap.ext fun v ↦ ?_⟩
  have hv : ρ v = v := LinearMap.congr_fun hρ v
  have := chart_sub_chart X v 0
  simp only [ZeroMemClass.coe_zero, sub_zero] at this
  simp [← map_sub, this, hv]

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

@[simp]
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
  exact IsHyperplane.not_of_subsingleton M hM

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

/-! ### Restricting a hyperplane to another one -/

section Restrict

variable {f : V →ᵃ[k] k} {H K : AffineSubspace k V}

/-- An equation for `H` vanishes on `H`. -/
theorem IsEquation.comp_chart_self (hf : IsEquation f H) : f.comp (chart H) = 0 :=
  AffineMap.ext fun v ↦ hf.apply_eq_zero_iff.2 (chart_mem hf.isHyperplane.ne_bot v)

/-- The restriction to `H` of an equation for a different hyperplane meeting `H` is an equation for
the retained hyperplane.

Blueprint: `lem:restriction-geometry`. -/
theorem IsEquation.comp_chart (hH : IsHyperplane H) (hf : IsEquation f K) (hne : K ≠ H)
    (hbot : H ⊓ K ≠ ⊥) : IsEquation (f.comp (chart H)) (K.comap (chart H)) := by
  refine ⟨fun h0 ↦ ?_, by rw [zeroLocus_comp, hf.zeroLocus_eq]⟩
  obtain ⟨p, hpH, hpK⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 hbot
  refine hH.not_le_of_ne hf.isHyperplane hne.symm
    (AffineSubspace.le_of_direction_le (fun v hv ↦ ?_) ⟨p, hpH, hpK⟩)
  rw [hf.direction_eq, LinearMap.mem_ker]
  simpa using LinearMap.congr_fun h0 ⟨v, hv⟩

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

/-- A hyperplane `K` restricts to a hyperplane of `H.direction` exactly when `K ≠ H` and `K` meets
`H`.

Blueprint: `lem:restriction-geometry`. -/
theorem IsHyperplane.isHyperplane_comap_chart_iff (hH : IsHyperplane H) (hK : IsHyperplane K) :
    IsHyperplane (K.comap (chart H)) ↔ K ≠ H ∧ H ⊓ K ≠ ⊥ := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rintro rfl
    exact h.ne_top (comap_chart_self hH.ne_bot)
  · exact fun hb ↦ h.ne_bot ((comap_chart_eq_bot_iff hH.ne_bot).2 hb)
  · exact ((isEquation_equation hK).comp_chart hH h.1 h.2).isHyperplane

/-- A retained intersection is a hyperplane of `H`.

Blueprint: `lem:restriction-geometry`. -/
theorem IsHyperplane.isHyperplaneIn_inf (hH : IsHyperplane H) (hK : IsHyperplane K) (hne : K ≠ H)
    (hbot : H ⊓ K ≠ ⊥) : IsHyperplaneIn (H ⊓ K) H := by
  rw [← map_chart_comap_chart hH.ne_bot, isHyperplaneIn_map_chart_iff hH.ne_bot,
    hH.isHyperplane_comap_chart_iff hK]
  exact ⟨hne, hbot⟩

/-- Two different hyperplanes that meet do so in codimension two. -/
theorem IsHyperplane.codim_inf_eq_two [FiniteDimensional k V] (hH : IsHyperplane H)
    (hK : IsHyperplane K) (hne : K ≠ H) (hbot : H ⊓ K ≠ ⊥) : codim (H ⊓ K) = 2 := by
  rw [hH.codim_inf hbot (hK.not_le_of_ne hH hne), hK.codim_eq_one]

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
