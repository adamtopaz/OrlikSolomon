/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Internal gradings: shifted maps, homogeneous extraction and signs

This file provides the grading vocabulary of the whole project. Blueprint: `def:grading`,
`lem:extraction`.

An internal bigrading of an `R`-algebra `T` (`def:grading`) is Mathlib's
`GradedAlgebra (𝒜 : ℤ × ℤ → Submodule R T)`, and an internally graded module is
`DirectSum.Decomposition ℳ`; no new class is introduced. Mathlib's `⨁` has finite support, as the
blueprint requires.

The grading pieces of a cohomology ring are `R`-submodules, while its residue and Gysin maps are
`B`-linear for a larger coefficient ring `B`, and multiplying by `B` changes the weight. So the
grading pieces are not `B`-submodules, and nothing here ties the linearity of a map to the ring
of the grading pieces:

* `IsHomogeneousOfShift` is a predicate on plain functions, in the style of `Function.Exact`, so
  a map `f : M →ₗ[B] N` is coerced to a function and needs no change of scalars;
* the extraction results hold for any `f : F` with `[AddMonoidHomClass F M N]`, and for gradings
  in any `[AddSubmonoidClass σ M]`, as for `DirectSum.Decomposition` itself;
* `IsHomogeneousOfShift.component` restricts a `B`-linear map to an `R`-linear map of pieces.

Degrees are matched by an equation `i + a = j` rather than by computing `j - a`, so that the
statements can be used at literal bidegrees such as `(1, 1) + (-1, -1) = (0, 0)` with no
transport along an equality of degrees. Degrees need only right cancellation for homogeneous
preimages, and form an additive group where every degree must be reached by the shift.

## Main definitions

* `OrlikSolomon.IsHomogeneousOfShift ℳ 𝒩 a f`: the function `f` sends `ℳ i` into `𝒩 (i + a)`.
* `OrlikSolomon.IsHomogeneousOfShift.component`: the `R`-linear map `ℳ i →ₗ[R] 𝒩 j` induced by a
  homogeneous map, when `i + a = j`.
* `OrlikSolomon.IsHomogeneousOfShift.componentEquiv`: the same for a homogeneous equivalence.
* `OrlikSolomon.IsGradedCommutative 𝒜 d`: homogeneous elements commute up to the sign
  `(d i * d j).negOnePow`.

## Main results (`lem:extraction`)

* `OrlikSolomon.IsHomogeneousOfShift.decompose_map`: a homogeneous map commutes with taking
  homogeneous components, up to the shift.
* `OrlikSolomon.IsHomogeneousOfShift.exists_mem_preimage`: a homogeneous element in the range has
  a homogeneous preimage of the corresponding degree.
* `OrlikSolomon.IsHomogeneousOfShift.inverse`, `OrlikSolomon.IsHomogeneousOfShift.ofBijective_symm`,
  `OrlikSolomon.IsHomogeneousOfShift.linearEquiv_symm`,
  `OrlikSolomon.IsHomogeneousOfShift.algEquiv_symm`: an inverse of a homogeneous bijection of shift
  `a` is homogeneous of shift `-a`.
* `OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_mem`,
  `OrlikSolomon.IsHomogeneousOfShift.exact_iff_forall_component`: total exactness is equivalent to
  exactness in each shifted component.

## Signs

Following `docs/ARCHITECTURE.md`, the sign `ε(p)` of the blueprint is `Int.negOnePow p : ℤˣ`
acting by scalars, and `ε(p + q) = ε(p) ε(q)` is Mathlib's `Int.negOnePow_add`. The action makes
sense on every additive group, so `2` need not be invertible and no coefficient ring is
involved; `OrlikSolomon.negOnePow_smul_eq_smul` compares it with the blueprint's scalar in `R`.
-/

@[expose] public section

open DirectSum

namespace OrlikSolomon

variable {ι κ M N Q T T' σ τ υ F G : Type*}

/-! ### Internal bigradings

The blueprint's `def:grading` is realized by Mathlib's classes, with the following dictionary. -/

section Bigrading

variable {R : Type*} [CommSemiring R] [Semiring T] [Algebra R T] (𝒜 : ℤ × ℤ → Submodule R T)
  [GradedAlgebra 𝒜]

example : T ≃ₗ[R] ⨁ i, 𝒜 i := decomposeLinearEquiv 𝒜

example (i : ℤ × ℤ) (x : 𝒜 i) : (decomposeLinearEquiv 𝒜).symm (lof R _ (𝒜 ·) i x) = x :=
  decomposeLinearEquiv_symm_lof 𝒜 i x

example : (1 : T) ∈ 𝒜 0 := SetLike.one_mem_graded 𝒜

example {i j : ℤ × ℤ} {x y : T} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) : x * y ∈ 𝒜 (i + j) :=
  SetLike.mul_mem_graded hx hy

end Bigrading

/-! ### Homogeneous maps of a fixed shift -/

/-- A function `f : M → N` between internally graded types is *homogeneous of shift `a`* if it
sends `ℳ i` into `𝒩 (i + a)` for every degree `i`. The residue and Gysin maps of a cohomology
theory have shifts `(-1, -1)` and `(2, 1)`, and pullbacks have shift `0`.

This is a predicate on functions so that a map may be linear over a larger ring than the ring of
the grading pieces: for `f : M →ₗ[B] N` and `ℳ : ι → Submodule R M`, write
`IsHomogeneousOfShift ℳ 𝒩 a f`. Blueprint: `def:grading`. -/
def IsHomogeneousOfShift [Add ι] [SetLike σ M] [SetLike τ N] (ℳ : ι → σ) (𝒩 : ι → τ) (a : ι)
    (f : M → N) : Prop :=
  ∀ ⦃i : ι⦄ ⦃x : M⦄, x ∈ ℳ i → f x ∈ 𝒩 (i + a)

section Basic

variable [SetLike σ M] [SetLike τ N] [SetLike υ Q]
  {ℳ : ι → σ} {𝒩 : ι → τ} {𝒬 : ι → υ} {a b c : ι} {f : M → N} {g : N → Q}

/-- Homogeneity of shift `a`, with the target degree named by an equation. -/
theorem isHomogeneousOfShift_iff [Add ι] :
    IsHomogeneousOfShift ℳ 𝒩 a f ↔ ∀ ⦃i j : ι⦄, i + a = j → ∀ ⦃x : M⦄, x ∈ ℳ i → f x ∈ 𝒩 j :=
  ⟨fun hf _ _ hij _ hx ↦ hij ▸ hf hx, fun hf _ _ hx ↦ hf rfl hx⟩

/-- A map has shift `0` exactly when it preserves degrees. -/
theorem isHomogeneousOfShift_zero_iff [AddZeroClass ι] :
    IsHomogeneousOfShift ℳ 𝒩 0 f ↔ ∀ ⦃i : ι⦄ ⦃x : M⦄, x ∈ ℳ i → f x ∈ 𝒩 i := by
  simp only [IsHomogeneousOfShift, add_zero]

/-- For a grading by a product such as `ℤ × ℤ`, the shift acts on each coordinate. -/
theorem isHomogeneousOfShift_prod_iff [Add ι] [Add κ] {ℳ : ι × κ → σ} {𝒩 : ι × κ → τ}
    {a : ι} {b : κ} :
    IsHomogeneousOfShift ℳ 𝒩 (a, b) f ↔
      ∀ ⦃p : ι⦄ ⦃w : κ⦄ ⦃x : M⦄, x ∈ ℳ (p, w) → f x ∈ 𝒩 (p + a, w + b) :=
  ⟨fun hf _ _ _ hx ↦ hf hx, fun hf _ _ hx ↦ hf hx⟩

/-- The identity has shift `0`. -/
theorem isHomogeneousOfShift_id [AddZeroClass ι] : IsHomogeneousOfShift ℳ ℳ 0 (id : M → M) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hx ↦ hx

/-- Left multiplication by an element of degree `a` has shift `a`, when degrees commute. This is
how logarithmic classes act in `lem:gm` and `lem:ses`, and `e_H` in `def:lift-map`. -/
theorem isHomogeneousOfShift_mul_left [AddCommMagma ι] [Mul T] [SetLike σ T] {𝒜 : ι → σ}
    [SetLike.GradedMul 𝒜] {t : T} (ht : t ∈ 𝒜 a) : IsHomogeneousOfShift 𝒜 𝒜 a (t * ·) :=
  fun i _ hx ↦ add_comm a i ▸ SetLike.mul_mem_graded ht hx

namespace IsHomogeneousOfShift

/-- A homogeneous map of shift `a` sends degree `i` to degree `j`, when `i + a = j`. -/
theorem map_mem [Add ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f) {i j : ι} (hij : i + a = j) {x : M}
    (hx : x ∈ ℳ i) : f x ∈ 𝒩 j :=
  isHomogeneousOfShift_iff.1 hf hij hx

/-- Shifts add under composition: `f` is applied first, so its shift is on the left. -/
theorem comp [AddSemigroup ι] (hg : IsHomogeneousOfShift 𝒩 𝒬 b g)
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) : IsHomogeneousOfShift ℳ 𝒬 (a + b) (g ∘ f) :=
  fun i _ hx ↦ add_assoc i a b ▸ hg (hf hx)

/-- A version of `IsHomogeneousOfShift.comp` with the total shift named by an equation, for
literal bidegrees. -/
theorem comp_of_add_eq [AddSemigroup ι] (hg : IsHomogeneousOfShift 𝒩 𝒬 b g)
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hab : a + b = c) :
    IsHomogeneousOfShift ℳ 𝒬 c (g ∘ f) :=
  hab ▸ hg.comp hf

/-- A sum of maps of shift `a` has shift `a`. -/
protected theorem add [Add ι] [Add N] [AddMemClass τ N] {f₁ f₂ : M → N}
    (hf₁ : IsHomogeneousOfShift ℳ 𝒩 a f₁) (hf₂ : IsHomogeneousOfShift ℳ 𝒩 a f₂) :
    IsHomogeneousOfShift ℳ 𝒩 a (f₁ + f₂) :=
  fun _ _ hx ↦ add_mem (hf₁ hx) (hf₂ hx)

/-- A difference of maps of shift `a` has shift `a`. -/
protected theorem sub [Add ι] [AddGroup N] [AddSubgroupClass τ N] {f₁ f₂ : M → N}
    (hf₁ : IsHomogeneousOfShift ℳ 𝒩 a f₁) (hf₂ : IsHomogeneousOfShift ℳ 𝒩 a f₂) :
    IsHomogeneousOfShift ℳ 𝒩 a (f₁ - f₂) :=
  fun _ _ hx ↦ sub_mem (hf₁ hx) (hf₂ hx)

end IsHomogeneousOfShift

end Basic

/-! ### Homogeneous extraction -/

section Extraction

variable [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid N] [SetLike σ M] [AddSubmonoidClass σ M]
  [SetLike τ N] [AddSubmonoidClass τ N] {ℳ : ι → σ} {𝒩 : ι → τ} [Decomposition ℳ]
  [FunLike F M N] [AddMonoidHomClass F M N]

variable (ℳ) in
/-- Two additive maps out of an internally graded module are equal if they agree on homogeneous
elements. This applies to `B`-linear maps, unlike `DirectSum.decompose_lhom_ext`, which asks
for linearity over the ring of the grading pieces. -/
theorem decompose_hom_ext {f f' : F} (h : ∀ i, ∀ x ∈ ℳ i, f x = f' x) : f = f' := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add x y hx hy => simp [hx, hy]

omit [Decomposition ℳ] in
variable (𝒩) in
/-- An element lies in the range of an additive map if each of its components does. -/
theorem mem_range_of_forall_decompose_mem [Decomposition 𝒩] {f : F} {y : N}
    (h : ∀ j, (decompose 𝒩 y j : N) ∈ Set.range f) : y ∈ Set.range f := by
  classical
  rw [← AddMonoidHom.coe_mrange, SetLike.mem_coe, ← sum_support_decompose 𝒩 y]
  exact sum_mem fun j _ ↦ (AddMonoidHom.coe_mrange f ▸ h j :)

namespace IsHomogeneousOfShift

variable {f : F} {a b c : ι} {i j k : ι}

omit [AddSubmonoidClass τ N] in
/-- A map of shift `a` vanishes if, in each degree, its source or its target is zero. This is how
Gysin maps out of the point are shown to vanish in `lem:gm`. -/
theorem map_eq_zero_of_forall [Add ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f)
    (h : ∀ i, (∀ x ∈ ℳ i, x = 0) ∨ ∀ y ∈ 𝒩 (i + a), y = 0) (x : M) : f x = 0 := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i m =>
    obtain h₁ | h₂ := h i
    · rw [h₁ m m.2, map_zero]
    · exact h₂ _ (hf m.2)
  | add x y hx hy => simp [hx, hy]

variable [Decomposition 𝒩]

section RightCancel

variable [Add ι] [IsRightCancelAdd ι]

/-- A homogeneous map commutes with taking homogeneous components, up to its shift. This is the
fact from which everything else in `lem:extraction` follows. -/
theorem decompose_map (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hij : i + a = j) (x : M) :
    (decompose 𝒩 (f x) j : N) = f (decompose ℳ x i : M) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous k m =>
    obtain rfl | hk := eq_or_ne k i
    · rw [decompose_of_mem_same 𝒩 (hf.map_mem hij m.2), decompose_coe, of_eq_same]
    · have hkj : k + a ≠ j := fun h ↦ hk (add_right_cancel (h.trans hij.symm))
      rw [decompose_of_mem_ne 𝒩 (hf m.2) hkj, decompose_of_mem_ne ℳ m.2 hk, map_zero]
  | add x y hx hy => simp [hx, hy]

/-- A homogeneous element in the range of a homogeneous map has a homogeneous preimage of the
corresponding degree. Blueprint: `lem:extraction`. -/
theorem exists_mem_preimage (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hij : i + a = j) {y : N}
    (hy : y ∈ 𝒩 j) (hyf : y ∈ Set.range f) : ∃ x ∈ ℳ i, f x = y := by
  obtain ⟨x, rfl⟩ := hyf
  refine ⟨decompose ℳ x i, SetLike.coe_mem _, ?_⟩
  rw [← hf.decompose_map hij, decompose_of_mem_same 𝒩 hy]

/-- A homogeneous element has a homogeneous preimage under a surjective homogeneous map. -/
theorem exists_mem_preimage_of_surjective (hf : IsHomogeneousOfShift ℳ 𝒩 a f)
    (hs : Function.Surjective f) (hij : i + a = j) {y : N} (hy : y ∈ 𝒩 j) :
    ∃ x ∈ ℳ i, f x = y :=
  hf.exists_mem_preimage hij hy (hs y)

/-- A homogeneous element killed by the next map of an exact pair has a homogeneous preimage. -/
theorem exists_mem_preimage_of_exact [Zero Q] {g : N → Q} (hf : IsHomogeneousOfShift ℳ 𝒩 a f)
    (hfg : Function.Exact f g) (hij : i + a = j) {y : N} (hy : y ∈ 𝒩 j) (hgy : g y = 0) :
    ∃ x ∈ ℳ i, f x = y :=
  hf.exists_mem_preimage hij hy ((hfg y).1 hgy)

/-- In an exact pair of homogeneous maps, the middle term vanishes in degree `j` when the left
term vanishes in the degree before it and the right term in the degree after it. This is the step
used for the dimension bound in `thm:generation`. -/
theorem eq_zero_of_exact [Zero Q] [SetLike υ Q] {𝒬 : ι → υ} {g : N → Q}
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hg : IsHomogeneousOfShift 𝒩 𝒬 b g)
    (hfg : Function.Exact f g) (hij : i + a = j) (hjk : j + b = k) (hℳ : ∀ x ∈ ℳ i, x = 0)
    (h𝒬 : ∀ z ∈ 𝒬 k, z = 0) {y : N} (hy : y ∈ 𝒩 j) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hf.exists_mem_preimage_of_exact hfg hij hy (h𝒬 _ (hg.map_mem hjk hy))
  rw [hℳ x hx, map_zero]

/-- An injective homogeneous map reflects degrees. -/
theorem mem_of_map_mem (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hinj : Function.Injective f)
    (hij : i + a = j) {x : M} (hx : f x ∈ 𝒩 j) : x ∈ ℳ i := by
  obtain ⟨x', hx', h⟩ := hf.exists_mem_preimage hij hx ⟨x, rfl⟩
  exact hinj h ▸ hx'

/-- A homogeneous map is injective exactly when it is injective in each degree. -/
theorem injective_iff_forall_injOn (hf : IsHomogeneousOfShift ℳ 𝒩 a f) :
    Function.Injective f ↔ ∀ i, Set.InjOn f (ℳ i) := by
  refine ⟨fun h _ ↦ h.injOn, fun h x y hxy ↦ (decompose ℳ).injective ?_⟩
  refine DFinsupp.ext fun i ↦ Subtype.ext (h i (SetLike.coe_mem _) (SetLike.coe_mem _) ?_)
  rw [← hf.decompose_map rfl, ← hf.decompose_map rfl, hxy]

end RightCancel

/-- If `f` is an injective homogeneous map and `f ∘ h` is homogeneous, then so is `h`. In
`thm:projective`, this shows that the equivalence obtained by restricting the cone equivalence
preserves degrees, because the pullback from `U_𝒫` is injective. -/
theorem of_comp_of_injective [AddRightCancelSemigroup ι] [SetLike υ Q] {𝒬 : ι → υ} {h : Q → M}
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hinj : Function.Injective f)
    (hh : IsHomogeneousOfShift 𝒬 𝒩 c (f ∘ h)) (hba : b + a = c) :
    IsHomogeneousOfShift 𝒬 ℳ b h := by
  intro i x hx
  refine hf.mem_of_map_mem hinj rfl (hh.map_mem ?_ hx)
  rw [← hba, add_assoc]

section Group

variable [AddGroup ι]

/-- A two-sided inverse of a homogeneous map of shift `a` is homogeneous of shift `-a`. Blueprint:
`lem:extraction`. -/
theorem inverse (hf : IsHomogeneousOfShift ℳ 𝒩 a f) {g : N → M}
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) :
    IsHomogeneousOfShift 𝒩 ℳ (-a) g := by
  intro j y hy
  obtain ⟨x, hx, rfl⟩ := hf.exists_mem_preimage (neg_add_cancel_right j a) hy ⟨g y, hr y⟩
  rwa [hl x]

/-- The inverse of a bijective homogeneous map of shift `a` is homogeneous of shift `-a`.
Blueprint: `lem:extraction`. -/
theorem ofBijective_symm (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hb : Function.Bijective f) :
    IsHomogeneousOfShift 𝒩 ℳ (-a) (Equiv.ofBijective f hb).symm :=
  hf.inverse (Equiv.ofBijective f hb).left_inv (Equiv.ofBijective f hb).right_inv

/-- If `f` is a surjective homogeneous map and `h ∘ f` is homogeneous, then so is `h`. This needs
a decomposition of `N`. When the pieces of `N` are by construction the images of those of `M`, as
for `RelationQuotient.grading`, that description gives the conclusion directly. -/
theorem of_comp_of_surjective [SetLike υ Q] {𝒬 : ι → υ} {h : N → Q}
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hs : Function.Surjective f)
    (hh : IsHomogeneousOfShift ℳ 𝒬 c (h ∘ f)) (hab : a + b = c) :
    IsHomogeneousOfShift 𝒩 𝒬 b h := by
  intro j y hy
  obtain ⟨x, hx, rfl⟩ := hf.exists_mem_preimage_of_surjective hs (neg_add_cancel_right j a) hy
  refine hh.map_mem ?_ hx
  rw [← hab, ← add_assoc, neg_add_cancel_right]

/-- A homogeneous map is surjective exactly when it is surjective in each shifted degree. -/
theorem surjective_iff_forall_surjOn (hf : IsHomogeneousOfShift ℳ 𝒩 a f) :
    Function.Surjective f ↔ ∀ ⦃i j : ι⦄, i + a = j → Set.SurjOn f (ℳ i) (𝒩 j) := by
  refine ⟨fun hs _ _ hij _ hy ↦ hf.exists_mem_preimage_of_surjective hs hij hy, fun h y ↦ ?_⟩
  refine mem_range_of_forall_decompose_mem 𝒩 fun j ↦ ?_
  obtain ⟨x, -, hx⟩ := h (neg_add_cancel_right j a) (decompose 𝒩 y j).2
  exact ⟨x, hx⟩

end Group

section Exact

variable [AddCommMonoid Q] [SetLike υ Q] [AddSubmonoidClass υ Q] {𝒬 : ι → υ}
  [FunLike G N Q] [AddMonoidHomClass G N Q] {g : G} [Decomposition 𝒬]

omit [Decomposition ℳ] in
/-- A homogeneous map kills an element exactly when it kills every homogeneous component. -/
theorem map_eq_zero_iff_forall_decompose [Add ι] [IsRightCancelAdd ι]
    (hg : IsHomogeneousOfShift 𝒩 𝒬 b g) {y : N} :
    g y = 0 ↔ ∀ j, g (decompose 𝒩 y j : N) = 0 := by
  classical
  refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
  · rw [← hg.decompose_map rfl, h, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  · rw [← sum_support_decompose 𝒩 y, map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ h j

/-- Total exactness is equivalent to exactness at each homogeneous element, with the shift
recorded by `i + a = j`. Blueprint: `lem:extraction`. -/
theorem exact_iff_forall_mem [AddGroup ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f)
    (hg : IsHomogeneousOfShift 𝒩 𝒬 b g) :
    Function.Exact f g ↔ ∀ ⦃i j : ι⦄, i + a = j → ∀ ⦃y : N⦄, y ∈ 𝒩 j →
      (g y = 0 ↔ ∃ x ∈ ℳ i, f x = y) := by
  refine ⟨fun hfg i j hij y hy ↦ ⟨hf.exists_mem_preimage_of_exact hfg hij hy, ?_⟩, fun h y ↦ ?_⟩
  · rintro ⟨x, -, rfl⟩
    exact hfg.apply_apply_eq_zero x
  refine ⟨fun hy ↦ ?_, ?_⟩
  · refine mem_range_of_forall_decompose_mem 𝒩 fun j ↦ ?_
    have hj := hg.map_eq_zero_iff_forall_decompose.1 hy j
    obtain ⟨x, -, hx⟩ := (h (neg_add_cancel_right j a) (decompose 𝒩 y j).2).1 hj
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    induction x using Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous m => exact (h rfl (hf m.2)).2 ⟨m, m.2, rfl⟩
    | add x y hx hy => simp [hx, hy]

end Exact

end IsHomogeneousOfShift

end Extraction

/-! ### Equivalences -/

section Equiv

variable [DecidableEq ι] [AddGroup ι] [AddCommMonoid M] [AddCommMonoid N] [SetLike σ M]
  [AddSubmonoidClass σ M] [SetLike τ N] [AddSubmonoidClass τ N] {ℳ : ι → σ} {𝒩 : ι → τ}
  [Decomposition ℳ] [Decomposition 𝒩] {a : ι}

/-- The inverse of a homogeneous linear equivalence of shift `a` has shift `-a`. The equivalence
may be linear over any ring, not only the ring of the grading pieces. -/
theorem IsHomogeneousOfShift.linearEquiv_symm {B : Type*} [Semiring B] [Module B M] [Module B N]
    {e : M ≃ₗ[B] N} (he : IsHomogeneousOfShift ℳ 𝒩 a e) :
    IsHomogeneousOfShift 𝒩 ℳ (-a) e.symm :=
  IsHomogeneousOfShift.inverse (f := e) he e.left_inv e.right_inv

end Equiv

section AlgEquiv

variable [DecidableEq ι] [AddGroup ι] {B : Type*} [CommSemiring B] [Semiring T] [Semiring T']
  [Algebra B T] [Algebra B T'] [SetLike σ T] [AddSubmonoidClass σ T] [SetLike τ T']
  [AddSubmonoidClass τ T'] {𝒜 : ι → σ} {𝒜' : ι → τ} [Decomposition 𝒜] [Decomposition 𝒜']

/-- The inverse of a homogeneous algebra equivalence of shift `a` has shift `-a`. For a
grading-preserving equivalence, this and `neg_zero` show that the inverse preserves the grading,
as in `thm:affine`. -/
theorem IsHomogeneousOfShift.algEquiv_symm {a : ι} {e : T ≃ₐ[B] T'}
    (he : IsHomogeneousOfShift 𝒜 𝒜' a e) : IsHomogeneousOfShift 𝒜' 𝒜 (-a) e.symm :=
  IsHomogeneousOfShift.inverse (f := e) he e.left_inv e.right_inv

end AlgEquiv

/-! ### Components of a homogeneous map

The grading pieces are `R`-submodules, and the map may be linear over a larger ring `B`. The
restriction to pieces is `R`-linear as soon as `B`-linear maps are `R`-linear, which is
`LinearMap.CompatibleSMul`; it holds when `R`, `B` form a scalar tower, and when `B = R`. -/

namespace IsHomogeneousOfShift

section Component

variable {R B : Type*} [Semiring R] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
  [AddCommMonoid Q] [Module R M] [Module R N] [Module R Q] [Module B M] [Module B N] [Module B Q]
  [LinearMap.CompatibleSMul M N R B] [LinearMap.CompatibleSMul N Q R B]
  {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N} {𝒬 : ι → Submodule R Q}
  [FunLike F M N] [LinearMapClass F B M N] [FunLike G N Q] [LinearMapClass G B N Q]
  {f : F} {g : G} {a b : ι} {i j k : ι}

/-- The `R`-linear map `ℳ i →ₗ[R] 𝒩 j` induced by a homogeneous `B`-linear map of shift `a`, where
`i + a = j`. This applies to linear maps, linear equivalences and algebra maps over `B`. -/
def component [Add ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hij : i + a = j) :
    ℳ i →ₗ[R] 𝒩 j where
  toFun x := ⟨f x, hf.map_mem hij x.2⟩
  map_add' x y := Subtype.ext (map_add f (x : M) (y : M))
  map_smul' r x := Subtype.ext (LinearMapClass.map_smul_of_tower f r (x : M))

/-- The component of `f` is `f`, on underlying elements. -/
@[simp]
theorem coe_component_apply [Add ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hij : i + a = j)
    (x : ℳ i) : (hf.component hij x : N) = f x :=
  rfl

variable [DecidableEq ι] [Decomposition ℳ] [Decomposition 𝒩]

/-- A homogeneous linear map is injective exactly when each of its components is. Blueprint:
`lem:extraction`. -/
theorem injective_iff_forall_component [Add ι] [IsRightCancelAdd ι]
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) :
    Function.Injective f ↔
      ∀ ⦃i j : ι⦄ (hij : i + a = j), Function.Injective (hf.component hij) := by
  rw [hf.injective_iff_forall_injOn]
  constructor
  · intro h i j hij x y hxy
    exact Subtype.ext (h i x.2 y.2 (congrArg Subtype.val hxy))
  · intro h i x hx y hy hxy
    have hc : hf.component rfl ⟨x, hx⟩ = hf.component rfl ⟨y, hy⟩ := Subtype.ext hxy
    exact congrArg Subtype.val (h rfl hc)

/-- A homogeneous linear map is surjective exactly when each of its components is. Blueprint:
`lem:extraction`. -/
theorem surjective_iff_forall_component [AddGroup ι] (hf : IsHomogeneousOfShift ℳ 𝒩 a f) :
    Function.Surjective f ↔
      ∀ ⦃i j : ι⦄ (hij : i + a = j), Function.Surjective (hf.component hij) := by
  rw [hf.surjective_iff_forall_surjOn]
  refine ⟨fun h i j hij y ↦ ?_, fun h i j hij y hy ↦ ?_⟩
  · obtain ⟨x, hx, hxy⟩ := h hij y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · obtain ⟨x, hx⟩ := h hij ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-- Total exactness of a pair of homogeneous linear maps is equivalent to exactness of the
components `ℳ i → 𝒩 j → 𝒬 k` for all degrees with `i + a = j` and `j + b = k`. Blueprint:
`lem:extraction`. -/
theorem exact_iff_forall_component [AddGroup ι] [Decomposition 𝒬]
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) (hg : IsHomogeneousOfShift 𝒩 𝒬 b g) :
    Function.Exact f g ↔ ∀ ⦃i j k : ι⦄ (hij : i + a = j) (hjk : j + b = k),
      Function.Exact (hf.component hij) (hg.component hjk) := by
  rw [hf.exact_iff_forall_mem hg]
  refine ⟨fun h i j k hij hjk y ↦ ?_, fun h i j hij y hy ↦ ?_⟩
  · have := h hij y.2
    simp only [Subtype.ext_iff, coe_component_apply, ZeroMemClass.coe_zero, this, Set.mem_range]
    exact ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ ↦ ⟨x, x.2, hxy⟩⟩
  · have := h hij rfl ⟨y, hy⟩
    simp only [Subtype.ext_iff, coe_component_apply, ZeroMemClass.coe_zero, Set.mem_range] at this
    rw [this]
    exact ⟨fun ⟨x, hxy⟩ ↦ ⟨x, x.2, hxy⟩, fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hx⟩, hxy⟩⟩

/-- A homogeneous linear equivalence of shift `a` restricts to an `R`-linear equivalence
`ℳ i ≃ₗ[R] 𝒩 j` of each pair of pieces with `i + a = j`. For an algebra equivalence `e`, use
`(e := e.toLinearEquiv)`. -/
def componentEquiv [Add ι] [IsRightCancelAdd ι] {e : M ≃ₗ[B] N}
    (he : IsHomogeneousOfShift ℳ 𝒩 a e) (hij : i + a = j) : ℳ i ≃ₗ[R] 𝒩 j :=
  { he.component hij with
    invFun y := ⟨e.symm y, he.mem_of_map_mem e.injective hij
      (by rw [e.apply_symm_apply]; exact y.2)⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x)
    right_inv y := Subtype.ext (e.apply_symm_apply y) }

/-- The component equivalence of `e` is `e`, on underlying elements. -/
@[simp]
theorem coe_componentEquiv_apply [Add ι] [IsRightCancelAdd ι] {e : M ≃ₗ[B] N}
    (he : IsHomogeneousOfShift ℳ 𝒩 a e) (hij : i + a = j) (x : ℳ i) :
    (he.componentEquiv hij x : N) = e x :=
  rfl

/-- The inverse of the component equivalence of `e` is `e.symm`, on underlying elements. -/
@[simp]
theorem coe_componentEquiv_symm_apply [Add ι] [IsRightCancelAdd ι] {e : M ≃ₗ[B] N}
    (he : IsHomogeneousOfShift ℳ 𝒩 a e) (hij : i + a = j) (y : 𝒩 j) :
    ((he.componentEquiv hij).symm y : M) = e.symm y :=
  rfl

end Component

end IsHomogeneousOfShift

/-! ### Signs

The sign of graded commutativity is `Int.negOnePow`, acting by scalars on any additive group.
Mathlib already covers most of what this action needs: `map_zsmul_unit` for additive maps,
`zsmul_mem` for grading pieces, and `smul_comm` and `smul_add` for the module structure. This
section adds the blueprint's two cases of `ε`, its comparison with scalars in `R`, and `simp` lemmas
for products, since `smul_mul_assoc` and `mul_smul_comm` are not `simp` lemmas. -/

section Signs

variable [AddCommGroup M]

/-- The sign of an even integer acts trivially. This is one case of the blueprint's `ε`. -/
theorem negOnePow_smul_of_even {n : ℤ} (hn : Even n) (x : M) : n.negOnePow • x = x := by
  rw [Int.negOnePow_even n hn, one_smul]

/-- The sign of an odd integer acts by negation. This is the other case of the blueprint's `ε`. -/
theorem negOnePow_smul_of_odd {n : ℤ} (hn : Odd n) (x : M) : n.negOnePow • x = -x := by
  rw [Int.negOnePow_odd n hn, Units.neg_smul, one_smul]

/-- The sign acts as the image of `±1` in any coefficient ring. This is the blueprint's `ε(p)`,
with values in `R`. -/
theorem negOnePow_smul_eq_smul (R : Type*) [Ring R] [Module R M] (n : ℤ) (x : M) :
    n.negOnePow • x = (((n.negOnePow : ℤˣ) : ℤ) : R) • x := by
  rw [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- Signs move out of a product on the left. This is stated for every unit of `ℤ`, so that it also
applies to a product of signs, as produced by `Int.negOnePow_add`. -/
@[simp]
theorem zsmul_unit_mul [Ring T] (u : ℤˣ) (x y : T) : u • x * y = u • (x * y) :=
  smul_mul_assoc _ _ _

/-- Signs move out of a product on the right. This is stated for every unit of `ℤ`, so that it also
applies to a product of signs, as produced by `Int.negOnePow_add`. -/
@[simp]
theorem mul_zsmul_unit [Ring T] (u : ℤˣ) (x y : T) : x * u • y = u • (x * y) :=
  mul_smul_comm _ _ _

end Signs

/-! ### Graded commutativity -/

/-- The internally graded ring `𝒜` is *graded commutative along `d : ι → ℤ`* if
`x * y = (d i * d j).negOnePow • (y * x)` for `x ∈ 𝒜 i` and `y ∈ 𝒜 j`. The sign of the cohomology
of an arrangement depends only on the cohomological degree, which is the case `d = Prod.fst`: for
`h : IsGradedCommutative 𝒜 Prod.fst`, `x ∈ 𝒜 (p, w)` and `y ∈ 𝒜 (q, v)`, the term `h hx hy` proves
`x * y = (p * q).negOnePow • (y * x)`. Blueprint: item C2 of `def:cohomology`. -/
def IsGradedCommutative [Ring T] [SetLike σ T] (𝒜 : ι → σ) (d : ι → ℤ) : Prop :=
  ∀ ⦃i j : ι⦄ ⦃x y : T⦄, x ∈ 𝒜 i → y ∈ 𝒜 j → x * y = (d i * d j).negOnePow • (y * x)

/-- Elements of odd degree anticommute. Logarithmic classes have degree `(1, 1)`, and this is what
makes them satisfy the anticommutation of the exterior generators. -/
theorem IsGradedCommutative.mul_eq_neg_of_odd [Ring T] [SetLike σ T] {𝒜 : ι → σ} {d : ι → ℤ}
    {i j : ι} {x y : T} (h : IsGradedCommutative 𝒜 d) (hi : Odd (d i)) (hj : Odd (d j))
    (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) : x * y = -(y * x) := by
  rw [h hx hy, negOnePow_smul_of_odd (hi.mul hj)]

end OrlikSolomon
