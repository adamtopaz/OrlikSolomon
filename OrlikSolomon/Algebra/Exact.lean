/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Bases from short exact sequences, and a cokernel comparison lemma

This file contains two pieces of pure linear algebra.

The first produces a basis of the middle term of a short exact sequence
`0 → M' → M → M'' → 0` from a basis of each end and *chosen* lifts of the basis of `M''`. The
resulting basis vectors are exactly the images of the basis of `M'` and the chosen lifts.

The second compares a map `a : M' → M` with a map `j : N' → N`, through maps `f' : M' → N'` and
`f : M → N`. It deduces injectivity of `a` and `f` from a computation of the cokernel `M ⧸ range a`
by a linear map `s : L → M ⧸ range a`.

## Main definitions and results

* `OrlikSolomon.basisOfShortExact`: the basis `(a (u i)) ⊔ (w j)` of `M`, for bases `u` of `M'` and
  `v` of `M''`, and lifts `w` of `v`.
* `OrlikSolomon.cokernelComparison`: the map `ψ : M ⧸ range a → T` induced by `r ∘ₗ f`.

The conclusions of the comparison lemma, for `s` surjective and `ψ ∘ₗ s` bijective, are separate
statements, each with only the hypotheses it needs:

* `OrlikSolomon.bijective_of_surjective_of_injective_cokernelComparison_comp`: `s` is bijective.
* `OrlikSolomon.cokernelComparison_bijective_of_surjective_of_bijective_comp`: `ψ` is bijective.
* `OrlikSolomon.injective_of_comp_eq_comp`: `a` is injective.
* `OrlikSolomon.injective_of_surjective_of_injective_cokernelComparison_comp`: `f` is injective.
* `OrlikSolomon.linearEquivOfCokernelComparison`: the linear equivalence `M ≃ₗ[R] N` given by `f`,
  when `f` is also surjective.

## Blueprint

This file covers `lem:basis-ses` and `lem:comparison`.

## Implementation notes

Mathlib's `Module.Basis.ofSplitExact` goes in the other direction, from a basis of the middle term
to a basis of the quotient. Two constructions go in this direction but choose their own lifts:
`Module.Basis.sumQuot`, which also requires a commutative ring, and `ModuleCat.Basis.ofShortExact`.
The lemmas behind the latter, `ModuleCat.linearIndependent_leftExact` and `ModuleCat.span_exact`, do
allow prescribed lifts, but they require a ring and a bundled `ShortComplex` with all three modules
in one universe. We therefore use the chosen lifts to split the sequence
(`OrlikSolomon.splitOfLifts`, by `Function.Exact.splitSurjectiveEquiv`), and transport the product
basis along the splitting.

Compared with `lem:basis-ses`, the map `r` need not be assumed surjective, since this follows from
the existence of the lifts. Compared with `lem:comparison`, the map `f'` need only be injective, and
injectivity of `ψ ∘ₗ s` suffices for everything except the surjectivity of `ψ`.
-/

@[expose] public section

open Module

namespace OrlikSolomon

section BasisOfShortExact

variable {B M' M M'' I J : Type*} [Semiring B] [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
  [Module B M'] [Module B M] [Module B M''] {a : M' →ₗ[B] M} {r : M →ₗ[B] M''}

/-- A linear map sending a basis of `M''` to lifts along `r` is a section of `r`. -/
private theorem comp_constr_eq_id (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) :
    r ∘ₗ v.constr ℤ w = .id :=
  v.ext fun j => by simp [v.constr_basis, hw]

/-- The splitting `M ≃ₗ[B] M' × M''` of the sequence `0 → M' → M → M''` determined by a basis `v`
of `M''` and lifts `w` of `v`. Its inverse sends `(x, 0)` to `a x` and `(0, v j)` to `w j`, and its
second component is `r`. -/
noncomputable def splitOfLifts (ha : Function.Injective a) (hex : Function.Exact a r)
    (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) : M ≃ₗ[B] M' × M'' :=
  (hex.splitSurjectiveEquiv ha ⟨v.constr ℤ w, v.ext fun j => by simp [v.constr_basis, hw]⟩).1

/-- The inverse of `splitOfLifts` sends `(x, 0)` to `a x`. -/
@[simp]
theorem splitOfLifts_symm_inl (ha : Function.Injective a) (hex : Function.Exact a r)
    (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (x : M') :
    (splitOfLifts ha hex v w hw).symm (x, 0) = a x :=
  (LinearMap.congr_fun
    (hex.splitSurjectiveEquiv ha ⟨v.constr ℤ w, comp_constr_eq_id v w hw⟩).2.1 x).symm

/-- The inverse of `splitOfLifts` sends `(0, v j)` to the chosen lift `w j`. -/
@[simp]
theorem splitOfLifts_symm_inr (ha : Function.Injective a) (hex : Function.Exact a r)
    (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (j : J) :
    (splitOfLifts ha hex v w hw).symm (0, v j) = w j :=
  -- This unfolds the `invFun` field of `Function.Exact.splitSurjectiveEquiv`, about which Mathlib
  -- states no lemma, so a refactor of that definition could break this proof at a Mathlib bump.
  (LinearMap.congr_fun (congrArg Subtype.val ((hex.splitSurjectiveEquiv ha).symm_apply_apply
    ⟨v.constr ℤ w, comp_constr_eq_id v w hw⟩)) (v j)).trans (v.constr_basis ℤ w j)

/-- The splitting `splitOfLifts` sends the image `a x` to `(x, 0)`. -/
@[simp]
theorem splitOfLifts_apply_image (ha : Function.Injective a) (hex : Function.Exact a r)
    (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (x : M') :
    splitOfLifts ha hex v w hw (a x) = (x, 0) := by
  rw [← splitOfLifts_symm_inl ha hex v w hw, LinearEquiv.apply_symm_apply]

/-- The second component of the splitting `splitOfLifts` is `r`. -/
@[simp]
theorem splitOfLifts_apply_snd (ha : Function.Injective a) (hex : Function.Exact a r)
    (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (x : M) :
    (splitOfLifts ha hex v w hw x).2 = r x :=
  (LinearMap.congr_fun
    (hex.splitSurjectiveEquiv ha ⟨v.constr ℤ w, comp_constr_eq_id v w hw⟩).2.2 x).symm

/-- The basis of the middle term of a short exact sequence `0 → M' → M → M'' → 0`, built from a
basis `u` of `M'`, a basis `v` of `M''`, and chosen lifts `w j ∈ M` of `v j`. It consists of the
vectors `a (u i)` and `w j`; see `basisOfShortExact_inl` and `basisOfShortExact_inr`.

The map `r` is not assumed surjective, since this follows from the existence of the lifts.

When `a` is the linear map underlying an algebra map `φ`, pass `ha` with the type
`Function.Injective φ.toLinearMap`, using `have` if necessary. With `ha : Function.Injective φ` this
definition still elaborates, but the two types agree only at default transparency, so `simp` does
not rewrite with `basisOfShortExact_inl` and `basisOfShortExact_inr`. Those lemmas still apply as
terms.

Blueprint: `lem:basis-ses`. -/
noncomputable def basisOfShortExact (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) :
    Basis (I ⊕ J) B M :=
  (u.prod v).map (splitOfLifts ha hex v w hw).symm

/-- The vector of `basisOfShortExact` at `Sum.inl i` is `a (u i)`. -/
@[simp]
theorem basisOfShortExact_inl (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (i : I) :
    basisOfShortExact ha hex u v w hw (Sum.inl i) = a (u i) := by
  simp [basisOfShortExact, Basis.prod_apply]

/-- The vector of `basisOfShortExact` at `Sum.inr j` is the chosen lift `w j`. -/
@[simp]
theorem basisOfShortExact_inr (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (j : J) :
    basisOfShortExact ha hex u v w hw (Sum.inr j) = w j := by
  simp [basisOfShortExact, Basis.prod_apply]

/-- As a family, `basisOfShortExact` is `(a (u i)) ⊔ (w j)`. -/
theorem coe_basisOfShortExact (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) :
    ⇑(basisOfShortExact ha hex u v w hw) = Sum.elim (a ∘ u) w := by
  ext (i | j) <;> simp

/-- The coordinates of `x` on the lifts `w j` are the coordinates of `r x` on the basis `v`. -/
@[simp]
theorem basisOfShortExact_repr_inr (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (x : M) (j : J) :
    (basisOfShortExact ha hex u v w hw).repr x (Sum.inr j) = v.repr (r x) j := by
  simp [basisOfShortExact]

/-- The coordinates of `a x` on the vectors `a (u i)` are the coordinates of `x` on the basis
`u`. -/
@[simp]
theorem basisOfShortExact_repr_apply_inl (ha : Function.Injective a) (hex : Function.Exact a r)
    (u : Basis I B M') (v : Basis J B M'') (w : J → M) (hw : ∀ j, r (w j) = v j) (x : M') (i : I) :
    (basisOfShortExact ha hex u v w hw).repr (a x) (Sum.inl i) = u.repr x i := by
  simp [basisOfShortExact]

end BasisOfShortExact

section Comparison

variable {R M' M N' N T L : Type*} [Ring R] [AddCommGroup M'] [AddCommGroup M] [AddCommGroup N']
  [AddCommGroup N] [AddCommGroup T] [AddCommGroup L] [Module R M'] [Module R M] [Module R N']
  [Module R N] [Module R T] [Module R L] {a : M' →ₗ[R] M} {j : N' →ₗ[R] N} {r : N →ₗ[R] T}
  {f' : M' →ₗ[R] N'} {f : M →ₗ[R] N} {s : L →ₗ[R] M ⧸ LinearMap.range a}

/-- The map `ψ : M ⧸ range a → T` induced by `r ∘ₗ f`, in a diagram with `f ∘ₗ a = j ∘ₗ f'` and
`r ∘ₗ j = 0`. Use `cokernelComparison_mk` to compute it. Blueprint: `lem:comparison`. -/
def cokernelComparison (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f') :
    (M ⧸ LinearMap.range a) →ₗ[R] T :=
  (LinearMap.range a).liftQ (r ∘ₗ f) <| LinearMap.range_le_ker_iff.mpr <| by
    rw [LinearMap.comp_assoc, hfa, ← LinearMap.comp_assoc, hrj, LinearMap.zero_comp]

/-- The map `cokernelComparison` sends the class of `x` to `r (f x)`. -/
@[simp]
theorem cokernelComparison_mk (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f') (x : M) :
    cokernelComparison hrj hfa (Submodule.Quotient.mk x) = r (f x) :=
  rfl

@[simp]
theorem cokernelComparison_comp_mkQ (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f') :
    cokernelComparison hrj hfa ∘ₗ (LinearMap.range a).mkQ = r ∘ₗ f :=
  rfl

/-- If `s : L → M ⧸ range a` is surjective and its composite with the map `ψ` induced by `r ∘ₗ f` is
injective, then `s` is bijective. Blueprint: `lem:comparison`. -/
theorem bijective_of_surjective_of_injective_cokernelComparison_comp (hrj : r ∘ₗ j = 0)
    (hfa : f ∘ₗ a = j ∘ₗ f') (hs : Function.Surjective s)
    (hψs : Function.Injective (cokernelComparison hrj hfa ∘ₗ s)) : Function.Bijective s :=
  ⟨Function.Injective.of_comp (f := cokernelComparison hrj hfa) hψs, hs⟩

/-- If `s : L → M ⧸ range a` is surjective and its composite with the map `ψ` induced by `r ∘ₗ f` is
bijective, then `ψ` is bijective. Blueprint: `lem:comparison`. -/
theorem cokernelComparison_bijective_of_surjective_of_bijective_comp (hrj : r ∘ₗ j = 0)
    (hfa : f ∘ₗ a = j ∘ₗ f') (hs : Function.Surjective s)
    (hψs : Function.Bijective (cokernelComparison hrj hfa ∘ₗ s)) :
    Function.Bijective (cokernelComparison hrj hfa) :=
  ⟨Function.Injective.of_comp_right (g := s) hψs.injective hs,
    Function.Surjective.of_comp (g := s) hψs.surjective⟩

/-- In a commutative square `f ∘ₗ a = j ∘ₗ f'` with `j` and `f'` injective, the map `a` is
injective. The blueprint assumes that `f'` is bijective, but only its injectivity is needed.
Blueprint: `lem:comparison`. -/
theorem injective_of_comp_eq_comp (hj : Function.Injective j) (hf' : Function.Injective f')
    (hfa : f ∘ₗ a = j ∘ₗ f') : Function.Injective a := by
  refine Function.Injective.of_comp (f := f) ?_
  rw [← LinearMap.coe_comp, hfa, LinearMap.coe_comp]
  exact hj.comp hf'

/-- If the map `M ⧸ range a → T` induced by `r ∘ₗ f` is injective, and `j` and `f'` are injective,
then `f` is injective. -/
theorem injective_of_injective_cokernelComparison (hj : Function.Injective j)
    (hf' : Function.Injective f') (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f')
    (hψ : Function.Injective (cokernelComparison hrj hfa)) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  have hmk : (Submodule.Quotient.mk x : M ⧸ LinearMap.range a) = 0 :=
    hψ <| by simp [hx]
  obtain ⟨x', rfl⟩ := (Submodule.Quotient.mk_eq_zero _).mp hmk
  have hjf' : j (f' x') = j (f' 0) := by
    simpa using (LinearMap.congr_fun hfa x').symm.trans hx
  rw [hf' (hj hjf'), map_zero]

/-- If `s : L → M ⧸ range a` is surjective, its composite with the map `ψ` induced by `r ∘ₗ f` is
injective, and `j` and `f'` are injective, then `f` is injective. The blueprint assumes that `f'`
and `ψ ∘ₗ s` are bijective, but only their injectivity is needed. Blueprint: `lem:comparison`. -/
theorem injective_of_surjective_of_injective_cokernelComparison_comp (hj : Function.Injective j)
    (hf' : Function.Injective f') (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f')
    (hs : Function.Surjective s) (hψs : Function.Injective (cokernelComparison hrj hfa ∘ₗ s)) :
    Function.Injective f :=
  injective_of_injective_cokernelComparison hj hf' hrj hfa
    (Function.Injective.of_comp_right (g := s) hψs hs)

/-- The linear equivalence `M ≃ₗ[R] N` given by `f`, when `f` is surjective and is injective by
`injective_of_surjective_of_injective_cokernelComparison_comp`. Blueprint: `lem:comparison`. -/
noncomputable def linearEquivOfCokernelComparison (hj : Function.Injective j)
    (hf' : Function.Injective f') (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f')
    (hs : Function.Surjective s) (hψs : Function.Injective (cokernelComparison hrj hfa ∘ₗ s))
    (hf : Function.Surjective f) : M ≃ₗ[R] N :=
  LinearEquiv.ofBijective f
    ⟨injective_of_surjective_of_injective_cokernelComparison_comp hj hf' hrj hfa hs hψs, hf⟩

@[simp]
theorem linearEquivOfCokernelComparison_apply (hj : Function.Injective j)
    (hf' : Function.Injective f') (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f')
    (hs : Function.Surjective s) (hψs : Function.Injective (cokernelComparison hrj hfa ∘ₗ s))
    (hf : Function.Surjective f) (x : M) :
    linearEquivOfCokernelComparison hj hf' hrj hfa hs hψs hf x = f x :=
  rfl

@[simp]
theorem coe_linearEquivOfCokernelComparison (hj : Function.Injective j)
    (hf' : Function.Injective f') (hrj : r ∘ₗ j = 0) (hfa : f ∘ₗ a = j ∘ₗ f')
    (hs : Function.Surjective s) (hψs : Function.Injective (cokernelComparison hrj hfa ∘ₗ s))
    (hf : Function.Surjective f) :
    (linearEquivOfCokernelComparison hj hf' hrj hfa hs hψs hf : M →ₗ[R] N) = f :=
  rfl

end Comparison

end OrlikSolomon
