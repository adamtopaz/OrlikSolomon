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
rational points of varieties: `OrlikSolomon/Geometry/Chart.lean` and
`OrlikSolomon/Geometry/Arrangement.lean` build on it.

Affine subspaces form a complete lattice, whose bottom element `⊥` is the empty subspace, so the
intersection of a family is `⨅ i, H i` or `sInf S`, and "nonempty" is written `X ≠ ⊥`. A nonempty
intersection automatically has a `k`-point, since an affine subspace is a set of `k`-points.

The dimension of `X` is `Module.finrank k X.direction`, a natural number, as exponents in the
polynomials of `def:polynomials` require. For `X ≠ ⊥` this is the value of Mathlib's
`AffineSubspace.finDim : WithBot ℕ`, by `AffineSubspace.finDim_eq_finrank`, while
`AffineSubspace.finDim_bot` gives `⊥` where the natural number has only a conventional value.

## Main definitions

* `OrlikSolomon.IsHyperplane`: a nonempty affine subspace whose direction has codimension one.
* `OrlikSolomon.zeroLocus`, `OrlikSolomon.IsEquation`: an equation for `H` is an affine map
  `V →ᵃ[k] k` with nonzero linear part and zero locus `H`.
* `OrlikSolomon.equation`: a chosen equation of a hyperplane.
* `OrlikSolomon.codim`: the codimension of an affine subspace.

## Main results

* `OrlikSolomon.IsHyperplane.exists_isEquation`: every hyperplane has an equation.
* `OrlikSolomon.IsEquation.existsUnique_smul`: two equations for a hyperplane differ by a unique
  unit of `k`.
* `OrlikSolomon.direction_iInf_of_isEquation`, `OrlikSolomon.codim_iInf_of_isEquation`: the
  direction of a nonempty intersection of hyperplanes is the intersection of the kernels of the
  linear parts of their equations, and its codimension is the rank of the system.
* `OrlikSolomon.IsHyperplane.codim_inf`: cutting by a hyperplane raises the codimension by one.

## Implementation notes

The field `k` is arbitrary and may be finite, and no statement needs `2` to be invertible. The
space `V` may have dimension zero, in which case it has no hyperplanes. It lives in the universe of
`k`, so that `H.direction`, `Fin n → k` and `V` can all be quantified over together, as induction
on arrangements requires. Finite-dimensionality is assumed only where it is used.

## Blueprint

`def:arrangement` (hyperplanes and equations), `lem:equations`.
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

/-- An affine function has empty zero locus exactly when it is a nonzero constant. -/
theorem zeroLocus_eq_bot_iff {f : V →ᵃ[k] k} :
    zeroLocus f = ⊥ ↔ ∃ c : kˣ, f = AffineMap.const k V (c : k) := by
  constructor
  · intro h
    have hlin : f.linear = 0 := by
      by_contra hf
      exact zeroLocus_ne_bot hf h
    obtain ⟨c, rfl⟩ := (AffineMap.linear_eq_zero_iff_exists_const _).1 hlin
    have hc : c ≠ 0 := by
      rintro rfl
      have hmem : (0 : V) ∈ zeroLocus (AffineMap.const k V (0 : k)) := by simp
      rw [h] at hmem
      exact AffineSubspace.notMem_bot k _ _ hmem
    exact ⟨Units.mk0 c hc, rfl⟩
  · rintro ⟨c, rfl⟩
    ext x
    simp [AffineSubspace.notMem_bot]

/-- An affine function has zero locus everything exactly when it is zero. -/
theorem zeroLocus_eq_top_iff {f : V →ᵃ[k] k} : zeroLocus f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    ext x
    have hx : x ∈ zeroLocus f := h ▸ AffineSubspace.mem_top k V x
    simpa using hx
  · rintro rfl
    ext x
    simp

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
theorem not_isHyperplane_of_subsingleton [Subsingleton V] (H : AffineSubspace k V) :
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

/-- The preimage of a hyperplane under an affine map is empty, everything, or a hyperplane. -/
theorem IsHyperplane.comap_eq_bot_or_top_or_isHyperplane {W : Type u} [AddCommGroup W] [Module k W]
    (hH : IsHyperplane H) (φ : W →ᵃ[k] V) :
    H.comap φ = ⊥ ∨ H.comap φ = ⊤ ∨ IsHyperplane (H.comap φ) := by
  obtain ⟨f, hf⟩ := hH.exists_isEquation
  rw [← hf.zeroLocus_eq, ← zeroLocus_comp, isHyperplane_zeroLocus_iff]
  by_cases hlin : (f.comp φ).linear = 0
  · obtain ⟨c, hc⟩ := (AffineMap.linear_eq_zero_iff_exists_const _).1 hlin
    obtain rfl | hc0 := eq_or_ne c 0
    · exact Or.inr (Or.inl (zeroLocus_eq_top_iff.2 (hc.trans rfl)))
    · exact Or.inl (zeroLocus_eq_bot_iff.2 ⟨Units.mk0 c hc0, hc⟩)
  · exact Or.inr (Or.inr hlin)

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
The dimension of `X` itself is `Module.finrank k X.direction`. The value on `⊥` is only a
convention, given by `codim_bot`, so statements about flats must assume `X ≠ ⊥`.

Blueprint: `lem:equations`. -/
noncomputable def codim (X : AffineSubspace k V) : ℕ :=
  finrank k (V ⧸ X.direction)

@[simp]
theorem codim_top : codim (⊤ : AffineSubspace k V) = 0 := by
  rw [codim, AffineSubspace.direction_top]
  exact finrank_zero_of_subsingleton

/-- The empty subspace has direction `⊥`, so `codim` gives it the dimension of `V`. This value has
no geometric meaning. A test such as `codim X < n` therefore compiles without assuming `X ≠ ⊥` and
can succeed on an empty intersection, so such a test must be guarded. -/
@[simp]
theorem codim_bot : codim (⊥ : AffineSubspace k V) = finrank k V := by
  rw [codim, AffineSubspace.direction_bot]
  exact (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq

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

/-- Two different hyperplanes that meet do so in codimension two. -/
theorem IsHyperplane.codim_inf_eq_two {K : AffineSubspace k V} (hH : IsHyperplane H)
    (hK : IsHyperplane K) (hne : K ≠ H) (hbot : H ⊓ K ≠ ⊥) : codim (H ⊓ K) = 2 := by
  rw [hH.codim_inf hbot (hK.not_le_of_ne hH hne), hK.codim_eq_one]

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

end OrlikSolomon
