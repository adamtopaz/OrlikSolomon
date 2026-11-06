/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# The quotient of a noncommutative algebra by a set of relators

For a ring `T` and a set `ℛ ⊆ T`, this file builds the quotient of `T` by the two-sided relation
submodule `J(ℛ) = span {a * r * b | a b : T, r ∈ ℛ}`.

The point of the file is that the quotient has **two** universal properties. Algebra maps out of
the quotient are algebra maps killing the relators, but linear maps out of the quotient are also
under control: they are linear maps killing every `a * r * b`. The second property is not a
consequence of the first, and it is what the deletion argument (`def:lift-map`) and the central
boundary (`lem:central-boundary`) use, since the maps they descend are not multiplicative.

## Main definitions

* `OrlikSolomon.relationSubmodule S ℛ`: the two-sided relation submodule `J(ℛ)`, over `S`.
* `OrlikSolomon.RelationQuotient ℛ`: the quotient, which is a ring, and an `S`-algebra for every
  `S` such that `T` is an `S`-algebra.
* `OrlikSolomon.RelationQuotient.mk`, `OrlikSolomon.RelationQuotient.mkₐ`: the quotient map.
* `OrlikSolomon.RelationQuotient.liftAlgHom`, `OrlikSolomon.RelationQuotient.map`: algebra descent.
* `OrlikSolomon.RelationQuotient.liftLinear`, `OrlikSolomon.RelationQuotient.mapLinear`: linear
  descent.
* `OrlikSolomon.RelationQuotient.quotientLinearEquiv`: the underlying module is the quotient of
  `T` by the submodule `J(ℛ)`.
* `OrlikSolomon.RelationQuotient.grading`, `OrlikSolomon.RelationQuotient.gradedAlgebra`: the
  induced internal grading when the relators are homogeneous.

## Main results

* `OrlikSolomon.mul_mem_relationSubmodule_left`, `OrlikSolomon.mul_mem_relationSubmodule_right`:
  `J(ℛ)` is stable under multiplication on both sides.
* `OrlikSolomon.relationSubmodule_le_iff`, `OrlikSolomon.relationSubmodule_le_of_span_eq_top`:
  to bound `J(ℛ)` it suffices to treat the contexts `a * r * b`, and even only those with `a` and
  `b` in fixed spanning sets of `T`.
* `OrlikSolomon.relationSubmodule_isHomogeneous`: `J(ℛ)` is homogeneous if the relators are.
* `OrlikSolomon.RelationQuotient.liftAlgHomEquiv`, `OrlikSolomon.RelationQuotient.liftLinearEquiv`:
  the two universal properties, as equivalences.
* `OrlikSolomon.RelationQuotient.decompose_mk`: homogeneous components in the quotient are computed
  on representatives.

## Scalars

`relationSubmodule S ℛ` has the same elements for every `S` (`mem_relationSubmodule_iff`), because
`s • x = algebraMap S T s * x` is itself a multiple of `x`. Accordingly `RelationQuotient ℛ` does
not mention `S` at all. This matters for the grading: the Orlik–Solomon algebra is a `B`-algebra
whose graded pieces are only `R`-submodules, as multiplying by `B_v` changes the weight, and here
both structures live on one type.

## Implementation notes

The quotient is `RingCon.Quotient` of the congruence of `TwoSidedIdeal.span ℛ`, as with
`TensorAlgebra` and `CliffordAlgebra` in Mathlib. `RelationQuotient.ringCon` is not exposed outside
this file, so the choice of congruence cannot be relied on. Use the universal properties together
with `mk_eq_zero_iff`, `mk_eq_mk_iff` and `mk_surjective`.

The scalar action is transported separately before the ring instance, following
`CliffordAlgebra`. Together with the same transport on `OSAlgebra`, this lets the canonical
integer-coefficient base change `B ⊗[ℤ] OSAlgebra ℤ 𝒜` inherit its algebra structure without a
local module instance. This does not normalize every concrete coefficient algebra: integral
tensor products of polynomial or Laurent-polynomial coefficient algebras can still encounter
scalar-action diamonds, and rewriting a literal scalar action with `Algebra.smul_def` can fail
even when the corresponding equality elaborates directly.

## Blueprint

`def:twosided`, `lem:quotient-api`.
-/

@[expose] public section

namespace OrlikSolomon

variable {S T : Type*} [Ring T]

/-! ### The two-sided relation submodule -/

section RelationSubmodule

variable (S) [CommSemiring S] [Algebra S T] {ℛ ℛ' : Set T}

/-- The two-sided relation submodule `J(ℛ)`: the `S`-span of all `a * r * b` with `a b : T` and
`r ∈ ℛ`.

Blueprint: `def:twosided`. -/
def relationSubmodule (ℛ : Set T) : Submodule S T :=
  Submodule.span S {x | ∃ a, ∃ r ∈ ℛ, ∃ b, x = a * r * b}

/-- Every context of a relator lies in `J(ℛ)`. -/
theorem mul_mul_mem_relationSubmodule (a : T) {r : T} (hr : r ∈ ℛ) (b : T) :
    a * r * b ∈ relationSubmodule S ℛ :=
  Submodule.subset_span ⟨a, r, hr, b, rfl⟩

/-- Every relator lies in `J(ℛ)`. -/
theorem subset_relationSubmodule : ℛ ⊆ relationSubmodule S ℛ := fun r hr ↦ by
  simpa using mul_mul_mem_relationSubmodule S 1 hr 1

/-- The homogeneous elements of a graded algebra span it, over any ring of scalars. -/
theorem span_isHomogeneousElem_eq_top {ι R : Type*} [CommSemiring R] [Algebra R T] [DecidableEq ι]
    [AddMonoid ι] (𝒜 : ι → Submodule R T) [GradedAlgebra 𝒜] :
    Submodule.span S {x : T | SetLike.IsHomogeneousElem 𝒜 x} = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ⟨i, (DirectSum.decompose 𝒜 x i).2⟩

variable {S}

/-- To bound `J(ℛ)` it suffices to treat the contexts `a * r * b`.

Blueprint: `lem:quotient-api`. -/
theorem relationSubmodule_le_iff {N : Submodule S T} :
    relationSubmodule S ℛ ≤ N ↔ ∀ a, ∀ r ∈ ℛ, ∀ b, a * r * b ∈ N := by
  refine ⟨fun h a r hr b ↦ h (mul_mul_mem_relationSubmodule S a hr b), fun h ↦ ?_⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, r, hr, b, rfl⟩
  exact h a r hr b

/-- A linear map kills `J(ℛ)` if and only if it kills every `a * r * b`.

Blueprint: `lem:quotient-api`. -/
theorem relationSubmodule_le_ker_iff {M : Type*} [AddCommMonoid M] [Module S M] {f : T →ₗ[S] M} :
    relationSubmodule S ℛ ≤ LinearMap.ker f ↔ ∀ a, ∀ r ∈ ℛ, ∀ b, f (a * r * b) = 0 :=
  relationSubmodule_le_iff

/-- To bound `J(ℛ)` it suffices to treat the contexts `u * r * v` with `u` and `v` in spanning sets
of `T`, such as the words of an exterior algebra or the homogeneous elements of a graded algebra
(`span_isHomogeneousElem_eq_top`). -/
theorem relationSubmodule_le_of_span_eq_top {U V : Set T} (hU : Submodule.span S U = ⊤)
    (hV : Submodule.span S V = ⊤) {N : Submodule S T}
    (h : ∀ u ∈ U, ∀ r ∈ ℛ, ∀ v ∈ V, u * r * v ∈ N) : relationSubmodule S ℛ ≤ N := by
  refine relationSubmodule_le_iff.2 fun a r hr b ↦ ?_
  have ha : a ∈ Submodule.span S U := hU ▸ Submodule.mem_top
  have hb : b ∈ Submodule.span S V := hV ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu r hr v hv
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using N.add_mem hx hy
    | smul s x _ hx => simpa using N.smul_mem s hx
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using N.add_mem hx hy
  | smul s x _ hx => simpa using N.smul_mem s hx

/-- `J(ℛ)` is stable under left multiplication.

Blueprint: `lem:quotient-api`. -/
theorem mul_mem_relationSubmodule_left (c : T) {x : T} (hx : x ∈ relationSubmodule S ℛ) :
    c * x ∈ relationSubmodule S ℛ := by
  have : relationSubmodule S ℛ ≤ (relationSubmodule S ℛ).comap (LinearMap.mulLeft S c) :=
    relationSubmodule_le_iff.2 fun a r hr b ↦ by
      simpa [mul_assoc] using mul_mul_mem_relationSubmodule S (c * a) hr b
  exact this hx

/-- `J(ℛ)` is stable under right multiplication.

Blueprint: `lem:quotient-api`. -/
theorem mul_mem_relationSubmodule_right {x : T} (hx : x ∈ relationSubmodule S ℛ) (c : T) :
    x * c ∈ relationSubmodule S ℛ := by
  have : relationSubmodule S ℛ ≤ (relationSubmodule S ℛ).comap (LinearMap.mulRight S c) :=
    relationSubmodule_le_iff.2 fun a r hr b ↦ by
      simpa [mul_assoc] using mul_mul_mem_relationSubmodule S a hr (b * c)
  exact this hx

/-- `J(ℛ)` is monotone in the relators. -/
theorem relationSubmodule_mono (h : ℛ ⊆ ℛ') : relationSubmodule S ℛ ≤ relationSubmodule S ℛ' :=
  relationSubmodule_le_iff.2 fun a _ hr b ↦ mul_mul_mem_relationSubmodule S a (h hr) b

/-- With no relators, `J(ℛ)` is zero. -/
@[simp]
theorem relationSubmodule_empty : relationSubmodule S (∅ : Set T) = ⊥ :=
  le_bot_iff.1 <| relationSubmodule_le_iff.2 fun _ _ hr ↦ absurd hr (Set.notMem_empty _)

/-- `J(ℛ)` is the two-sided ideal generated by `ℛ`. -/
theorem mem_relationSubmodule_iff_mem_span {x : T} :
    x ∈ relationSubmodule S ℛ ↔ x ∈ TwoSidedIdeal.span ℛ := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, r, hr, b, rfl⟩ := hx
      exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.mul_mem_left _ _ _ <|
        TwoSidedIdeal.subset_span hr
    | zero => exact TwoSidedIdeal.zero_mem _
    | add x y _ _ hx hy => exact TwoSidedIdeal.add_mem _ hx hy
    | smul s x _ hx =>
      rw [Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  · intro hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx => exact subset_relationSubmodule S hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => simpa using mul_mem_relationSubmodule_left (-1) hx
    | left_absorb a x _ hx => exact mul_mem_relationSubmodule_left a hx
    | right_absorb b x _ hx => exact mul_mem_relationSubmodule_right hx b

/-- The elements of `J(ℛ)` do not depend on the scalars. -/
theorem mem_relationSubmodule_iff (S S' : Type*) [CommSemiring S] [Algebra S T] [CommSemiring S']
    [Algebra S' T] {x : T} : x ∈ relationSubmodule S ℛ ↔ x ∈ relationSubmodule S' ℛ := by
  rw [mem_relationSubmodule_iff_mem_span, mem_relationSubmodule_iff_mem_span]

/-- Restricting the scalars of `J(ℛ)` gives `J(ℛ)`. -/
@[simp]
theorem restrictScalars_relationSubmodule (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R T] [Algebra S T] [SMul R S] [IsScalarTower R S T] (ℛ : Set T) :
    (relationSubmodule S ℛ).restrictScalars R = relationSubmodule R ℛ :=
  SetLike.ext fun _ ↦ mem_relationSubmodule_iff S R

variable (S) in
/-- The relation submodule of a set of homogeneous relators is homogeneous, over any ring of
scalars: the grading of `T` is by `R`-submodules, and `S` need not be `R`.

Blueprint: `lem:quotient-api`. -/
theorem relationSubmodule_isHomogeneous {ι R : Type*} [CommSemiring R] [Algebra R T] [DecidableEq ι]
    [AddMonoid ι] {𝒜 : ι → Submodule R T} [GradedAlgebra 𝒜]
    (hℛ : ∀ r ∈ ℛ, SetLike.IsHomogeneousElem 𝒜 r) :
    (relationSubmodule S ℛ).IsHomogeneous 𝒜 := by
  -- Components are `R`-linear and need not be `S`-linear, so move to `R`.
  intro i x hx
  rw [mem_relationSubmodule_iff S R] at hx ⊢
  suffices relationSubmodule R ℛ ≤
      (relationSubmodule R ℛ).comap (GradedAlgebra.proj 𝒜 i) from this hx
  refine relationSubmodule_le_of_span_eq_top (span_isHomogeneousElem_eq_top R 𝒜)
    (span_isHomogeneousElem_eq_top R 𝒜) ?_
  rintro u ⟨p, hu⟩ r hr v ⟨q, hv⟩
  obtain ⟨m, hm⟩ := hℛ r hr
  have huv := SetLike.mul_mem_graded (SetLike.mul_mem_graded hu hm) hv
  rw [Submodule.mem_comap, GradedAlgebra.proj_apply]
  obtain rfl | hi := eq_or_ne (p + m + q) i
  · rw [DirectSum.decompose_of_mem_same _ huv]
    exact mul_mul_mem_relationSubmodule R u hr v
  · rw [DirectSum.decompose_of_mem_ne _ huv hi]
    exact Submodule.zero_mem _

end RelationSubmodule

/-! ### The quotient -/

/-- The ring congruence of the relation quotient. Its definition is an implementation detail: see
`RelationQuotient.mk_eq_mk_iff`. -/
@[no_expose]
def RelationQuotient.ringCon (ℛ : Set T) : RingCon T :=
  (TwoSidedIdeal.span ℛ).ringCon

/-- The quotient of `T` by the two-sided relation submodule of `ℛ`. It is a ring, and an `S`-algebra
whenever `T` is one.

Its maps out are `RelationQuotient.liftAlgHom` and `RelationQuotient.liftLinear`, and its underlying
module is `T ⧸ relationSubmodule S ℛ` by `RelationQuotient.quotientLinearEquiv`.

Blueprint: `def:twosided`. -/
def RelationQuotient (ℛ : Set T) : Type _ :=
  (RelationQuotient.ringCon ℛ).Quotient

namespace RelationQuotient

variable (ℛ : Set T)

-- Transport the scalar action separately so the generic natural and integer module actions
-- agree at instance transparency, as checked below, following Mathlib's `CliffordAlgebra`.
instance instSMul [CommSemiring S] [Algebra S T] : SMul S (RelationQuotient ℛ) :=
  inferInstanceAs <| SMul S (RingCon.Quotient _)

instance : Ring (RelationQuotient ℛ) :=
  inferInstanceAs <| Ring (RingCon.Quotient _)

instance instAlgebra [CommSemiring S] [Algebra S T] : Algebra S (RelationQuotient ℛ) :=
  inferInstanceAs <| Algebra S (RingCon.Quotient _)

-- Verify that there is no diamond. As for `TensorAlgebra`, this does not work at
-- `reducible_and_instances`: https://github.com/leanprover-community/mathlib4/issues/10906
example : (Semiring.toNatAlgebra : Algebra ℕ (RelationQuotient ℛ)) = instAlgebra ℛ := rfl
example : (Ring.toIntAlgebra _ : Algebra ℤ (RelationQuotient ℛ)) = instAlgebra ℛ := rfl

-- Module coherence does hold at instance transparency; tensor algebra synthesis needs this.
example : (Algebra.toModule : Module ℕ (RelationQuotient ℛ)) =
    AddCommMonoid.toNatModule := by
  with_reducible_and_instances rfl

example : (Algebra.toModule : Module ℤ (RelationQuotient ℛ)) =
    AddCommGroup.toIntModule _ := by
  with_reducible_and_instances rfl

instance {S' : Type*} [CommSemiring S] [Algebra S T] [CommSemiring S'] [Algebra S' T] [SMul S S']
    [IsScalarTower S S' T] : IsScalarTower S S' (RelationQuotient ℛ) :=
  inferInstanceAs <| IsScalarTower S S' (RingCon.Quotient _)

instance {S' : Type*} [CommSemiring S] [Algebra S T] [CommSemiring S'] [Algebra S' T]
    [SMulCommClass S S' T] : SMulCommClass S S' (RelationQuotient ℛ) :=
  inferInstanceAs <| SMulCommClass S S' (RingCon.Quotient _)

/-- The quotient map, as a ring homomorphism. This is the form in which elements are written, and
`simp` rewrites `mkₐ S ℛ x` to `mk ℛ x`. -/
def mk : T →+* RelationQuotient ℛ :=
  (ringCon ℛ).mk'

/-- The quotient map, as an algebra homomorphism. -/
def mkₐ (S : Type*) [CommSemiring S] [Algebra S T] (ℛ : Set T) : T →ₐ[S] RelationQuotient ℛ :=
  (ringCon ℛ).mkₐ S

variable {ℛ}

@[simp]
theorem mkₐ_apply [CommSemiring S] [Algebra S T] (x : T) : mkₐ S ℛ x = mk ℛ x :=
  rfl

theorem mk_surjective : Function.Surjective (mk ℛ) :=
  RingCon.mk'_surjective _

theorem mkₐ_surjective [CommSemiring S] [Algebra S T] : Function.Surjective (mkₐ S ℛ) :=
  mk_surjective

/-- Every element of the quotient is represented by an element of `T`. -/
@[elab_as_elim, induction_eliminator]
protected theorem induction {motive : RelationQuotient ℛ → Prop} (mk : ∀ x, motive (mk ℛ x))
    (x : RelationQuotient ℛ) : motive x := by
  obtain ⟨y, rfl⟩ := mk_surjective x
  exact mk y

@[simp]
theorem mk_smul [CommSemiring S] [Algebra S T] (s : S) (x : T) : mk ℛ (s • x) = s • mk ℛ x :=
  map_smul (mkₐ S ℛ) s x

@[simp]
theorem mk_algebraMap [CommSemiring S] [Algebra S T] (s : S) :
    mk ℛ (algebraMap S T s) = algebraMap S (RelationQuotient ℛ) s :=
  (mkₐ S ℛ).commutes s

/-- The image of a spanning set of `T` spans the quotient. For instance, the classes of the words of
an exterior algebra span any quotient of it. -/
theorem span_image_mk_eq_top [CommSemiring S] [Algebra S T] {U : Set T}
    (hU : Submodule.span S U = ⊤) : Submodule.span S (mk ℛ '' U) = ⊤ := by
  have h : (mkₐ S ℛ).toLinearMap '' U = mk ℛ '' U := rfl
  rw [← h, ← Submodule.map_span, hU, Submodule.map_top, LinearMap.range_eq_top]
  exact mk_surjective

section Kernel

variable (S) [CommSemiring S] [Algebra S T]

/-- Two elements have the same image in the quotient if and only if they differ by `J(ℛ)`. -/
theorem mk_eq_mk_iff {x y : T} : mk ℛ x = mk ℛ y ↔ x - y ∈ relationSubmodule S ℛ := by
  rw [mem_relationSubmodule_iff_mem_span, ← TwoSidedIdeal.rel_iff]
  exact RingCon.eq _

/-- The kernel of the quotient map is `J(ℛ)`. -/
theorem mk_eq_zero_iff {x : T} : mk ℛ x = 0 ↔ x ∈ relationSubmodule S ℛ := by
  rw [← map_zero (mk ℛ), mk_eq_mk_iff S, sub_zero]

/-- The kernel of the quotient map is `J(ℛ)`. -/
@[simp]
theorem ker_mkₐ : LinearMap.ker (mkₐ S ℛ).toLinearMap = relationSubmodule S ℛ :=
  SetLike.ext fun _ ↦ mk_eq_zero_iff S

end Kernel

/-- Relators vanish in the quotient. -/
theorem mk_eq_zero_of_mem {r : T} (hr : r ∈ ℛ) : mk ℛ r = 0 :=
  (mk_eq_zero_iff ℤ).2 (subset_relationSubmodule ℤ hr)

/-! ### Algebra descent -/

section AlgHom

variable [CommSemiring S] [Algebra S T] {A : Type*} [Semiring A] [Algebra S A]

/-- Algebra maps killing the relators descend to the quotient.

Blueprint: `lem:quotient-api`. -/
def liftAlgHom (f : T →ₐ[S] A) (hf : ∀ r ∈ ℛ, f r = 0) : RelationQuotient ℛ →ₐ[S] A :=
  RingCon.liftₐ (ringCon ℛ) f <| by
    have : TwoSidedIdeal.span ℛ ≤ TwoSidedIdeal.ker (f : T →+* A) :=
      TwoSidedIdeal.span_le.2 fun r hr ↦ (TwoSidedIdeal.mem_ker _).2 (hf r hr)
    exact TwoSidedIdeal.ringCon_le_iff.1 this

@[simp]
theorem liftAlgHom_mk (f : T →ₐ[S] A) (hf : ∀ r ∈ ℛ, f r = 0) (x : T) :
    liftAlgHom f hf (mk ℛ x) = f x :=
  rfl

@[simp]
theorem liftAlgHom_comp_mkₐ (f : T →ₐ[S] A) (hf : ∀ r ∈ ℛ, f r = 0) :
    (liftAlgHom f hf).comp (mkₐ S ℛ) = f :=
  AlgHom.ext fun _ ↦ rfl

/-- Algebra maps out of the quotient agree if they agree after the quotient map. Together with the
extensionality lemma for `T`, this makes `ext` reduce to the generators of `T`. -/
@[ext high]
theorem algHom_ext {f g : RelationQuotient ℛ →ₐ[S] A}
    (h : f.comp (mkₐ S ℛ) = g.comp (mkₐ S ℛ)) : f = g :=
  AlgHom.ext fun x ↦ by
    induction x with
    | mk x => exact DFunLike.congr_fun h x

/-- The universal property for algebra maps: algebra maps out of the quotient correspond to algebra
maps killing every relator.

Blueprint: `lem:quotient-api`. -/
def liftAlgHomEquiv : {f : T →ₐ[S] A // ∀ r ∈ ℛ, f r = 0} ≃ (RelationQuotient ℛ →ₐ[S] A) where
  toFun f := liftAlgHom f.1 f.2
  invFun g := ⟨g.comp (mkₐ S ℛ), fun r hr ↦ by simp [mk_eq_zero_of_mem hr]⟩
  left_inv f := Subtype.ext (liftAlgHom_comp_mkₐ f.1 f.2)
  right_inv g := by ext; simp

variable {T' : Type*} [Ring T'] [Algebra S T'] {ℛ' : Set T'}

/-- An algebra map carrying the relators into `J(ℛ')` induces an algebra map of quotients. -/
def map (φ : T →ₐ[S] T') (hφ : ∀ r ∈ ℛ, φ r ∈ relationSubmodule S ℛ') :
    RelationQuotient ℛ →ₐ[S] RelationQuotient ℛ' :=
  liftAlgHom ((mkₐ S ℛ').comp φ) fun r hr ↦ (mk_eq_zero_iff S).2 (hφ r hr)

@[simp]
theorem map_mk (φ : T →ₐ[S] T') (hφ : ∀ r ∈ ℛ, φ r ∈ relationSubmodule S ℛ') (x : T) :
    map φ hφ (mk ℛ x) = mk ℛ' (φ x) :=
  rfl

end AlgHom

/-! ### Linear descent -/

section Linear

variable [CommSemiring S] [Algebra S T] {M : Type*} [AddCommMonoid M] [Module S M]

/-- Linear maps killing `J(ℛ)` descend to the quotient, with no multiplicativity required. By
`relationSubmodule_le_ker_iff` the hypothesis says that `f` kills every `a * r * b`, and
`relationSubmodule_le_of_span_eq_top` restricts `a` and `b` to spanning sets of `T`.

Blueprint: `lem:quotient-api`. -/
def liftLinear (f : T →ₗ[S] M) (hf : relationSubmodule S ℛ ≤ LinearMap.ker f) :
    RelationQuotient ℛ →ₗ[S] M where
  toFun := Quotient.lift f fun x y hxy ↦ by
    have hxy' : x - y ∈ relationSubmodule S ℛ :=
      mem_relationSubmodule_iff_mem_span.2 ((TwoSidedIdeal.rel_iff _ _ _).1 hxy)
    have : f (x - y) = 0 := hf hxy'
    rw [← sub_add_cancel x y, map_add, this, zero_add]
  map_add' x y := by
    induction x with | mk x
    induction y with | mk y
    exact map_add f x y
  map_smul' s x := by
    induction x with | mk x
    exact map_smul f s x

@[simp]
theorem liftLinear_mk (f : T →ₗ[S] M) (hf : relationSubmodule S ℛ ≤ LinearMap.ker f) (x : T) :
    liftLinear f hf (mk ℛ x) = f x :=
  rfl

@[simp]
theorem liftLinear_comp_mkₐ (f : T →ₗ[S] M) (hf : relationSubmodule S ℛ ≤ LinearMap.ker f) :
    liftLinear f hf ∘ₗ (mkₐ S ℛ).toLinearMap = f :=
  rfl

/-- Linear maps out of the quotient agree if they agree after the quotient map. -/
@[ext high]
theorem linearMap_ext {f g : RelationQuotient ℛ →ₗ[S] M}
    (h : f ∘ₗ (mkₐ S ℛ).toLinearMap = g ∘ₗ (mkₐ S ℛ).toLinearMap) : f = g :=
  LinearMap.ext fun x ↦ by
    induction x with
    | mk x => exact DFunLike.congr_fun h x

/-- The universal property for linear maps: linear maps out of the quotient correspond to linear
maps killing `J(ℛ)`, equivalently killing every `a * r * b` by `relationSubmodule_le_ker_iff`.

Blueprint: `lem:quotient-api`. -/
def liftLinearEquiv :
    {f : T →ₗ[S] M // relationSubmodule S ℛ ≤ LinearMap.ker f} ≃ (RelationQuotient ℛ →ₗ[S] M) where
  toFun f := liftLinear f.1 f.2
  invFun g := ⟨g ∘ₗ (mkₐ S ℛ).toLinearMap, fun x hx ↦ by
    simpa using congrArg g ((mk_eq_zero_iff S).2 hx)⟩
  left_inv _ := rfl
  right_inv g := by ext; simp

variable {T' : Type*} [Ring T'] [Algebra S T'] {ℛ' : Set T'}

/-- A linear map carrying `J(ℛ)` into `J(ℛ')` induces a linear map of quotients, even if it is not
multiplicative. Use `relationSubmodule_le_iff` or `relationSubmodule_le_of_span_eq_top` to check
the hypothesis. -/
def mapLinear (f : T →ₗ[S] T') (hf : relationSubmodule S ℛ ≤ (relationSubmodule S ℛ').comap f) :
    RelationQuotient ℛ →ₗ[S] RelationQuotient ℛ' :=
  liftLinear ((mkₐ S ℛ').toLinearMap ∘ₗ f) fun x hx ↦ by
    simpa using (mk_eq_zero_iff S).2 (hf hx)

@[simp]
theorem mapLinear_mk (f : T →ₗ[S] T')
    (hf : relationSubmodule S ℛ ≤ (relationSubmodule S ℛ').comap f) (x : T) :
    mapLinear f hf (mk ℛ x) = mk ℛ' (f x) :=
  rfl

end Linear

/-! ### The underlying module -/

section Module

variable (S) [CommRing S] [Algebra S T]

variable (ℛ) in
/-- The underlying `S`-module of the relation quotient is the quotient of `T` by the submodule
`J(ℛ)`.

Blueprint: `def:twosided`. -/
def quotientLinearEquiv : (T ⧸ relationSubmodule S ℛ) ≃ₗ[S] RelationQuotient ℛ :=
  LinearEquiv.ofLinearMap
    ((relationSubmodule S ℛ).liftQ (mkₐ S ℛ).toLinearMap (ker_mkₐ S).ge)
    (liftLinear (relationSubmodule S ℛ).mkQ (by simp))
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem quotientLinearEquiv_mk (x : T) :
    quotientLinearEquiv S ℛ (Submodule.Quotient.mk x) = mk ℛ x :=
  rfl

@[simp]
theorem quotientLinearEquiv_symm_mk (x : T) :
    (quotientLinearEquiv S ℛ).symm (mk ℛ x) = Submodule.Quotient.mk x :=
  rfl

end Module

/-! ### The induced grading -/

section Grading

variable {ι R : Type*} [CommSemiring R] [Algebra R T]

variable (ℛ) in
/-- The grading of the quotient induced by a grading of `T`: the degree `i` piece is the image of
the degree `i` piece of `T`. The pieces are `R`-submodules, for the same `R` as the pieces of `T`,
even when the quotient is considered as an algebra over a larger ring.

Blueprint: `lem:quotient-api`. -/
def grading (𝒜 : ι → Submodule R T) (i : ι) : Submodule R (RelationQuotient ℛ) :=
  (𝒜 i).map (mkₐ R ℛ).toLinearMap

variable {𝒜 : ι → Submodule R T}

/-- The elements of degree `i` in the quotient are the classes of the elements of degree `i`. -/
theorem mem_grading_iff {i : ι} {x : RelationQuotient ℛ} :
    x ∈ grading ℛ 𝒜 i ↔ ∃ y ∈ 𝒜 i, mk ℛ y = x :=
  Iff.rfl

/-- The class of an element of degree `i` has degree `i`. -/
theorem mk_mem_grading {i : ι} {x : T} (hx : x ∈ 𝒜 i) : mk ℛ x ∈ grading ℛ 𝒜 i :=
  mem_grading_iff.2 ⟨x, hx, rfl⟩

instance [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (grading ℛ 𝒜) where
  one_mem := map_one (mk ℛ) ▸ mk_mem_grading SetLike.GradedOne.one_mem
  mul_mem i j x y hx hy := by
    obtain ⟨x', hx', rfl⟩ := mem_grading_iff.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_grading_iff.1 hy
    exact map_mul (mk ℛ) x' y' ▸ mk_mem_grading (SetLike.mul_mem_graded hx' hy')

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]

/-- Homogeneous components in the quotient are computed on representatives. This holds for whatever
decomposition is in scope, since a decomposition is unique. -/
@[simp]
theorem decompose_mk [DirectSum.Decomposition (grading ℛ 𝒜)] (x : T) (i : ι) :
    (DirectSum.decompose (grading ℛ 𝒜) (mk ℛ x) i : RelationQuotient ℛ) =
      mk ℛ (DirectSum.decompose 𝒜 x i) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous j m =>
    obtain rfl | hij := eq_or_ne j i
    · rw [DirectSum.decompose_of_mem_same _ (mk_mem_grading m.2),
        DirectSum.decompose_of_mem_same _ m.2]
    · rw [DirectSum.decompose_of_mem_ne _ (mk_mem_grading m.2) hij,
        DirectSum.decompose_of_mem_ne _ m.2 hij, map_zero]
  | add x y hx hy => simp [DirectSum.decompose_add, hx, hy]

variable (ℛ 𝒜) in
/-- The `R`-linear map from `T` to the direct sum of the graded pieces of the quotient that sends
`x` to the classes of its components. It descends to the decomposition of the quotient. -/
private def decomposeAux : T →ₗ[R] DirectSum ι fun i ↦ grading ℛ 𝒜 i :=
  DirectSum.lmap (fun i ↦ ((mkₐ R ℛ).toLinearMap ∘ₗ (𝒜 i).subtype).codRestrict (grading ℛ 𝒜 i)
    fun x ↦ mk_mem_grading x.2) ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

private theorem decomposeAux_of_mem {i : ι} {x : T} (hx : x ∈ 𝒜 i) :
    decomposeAux ℛ 𝒜 x =
      DirectSum.lof R ι (fun i ↦ grading ℛ 𝒜 i) i ⟨mk ℛ x, mk_mem_grading hx⟩ := by
  have := DirectSum.decomposeLinearEquiv_apply_coe 𝒜 i ⟨x, hx⟩
  simp only [decomposeAux, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [this, DirectSum.lmap_lof]
  rfl

private theorem coeLinearMap_decomposeAux (x : T) :
    DirectSum.coeLinearMap (grading ℛ 𝒜) (decomposeAux ℛ 𝒜 x) = mk ℛ x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => simp [decomposeAux_of_mem m.2]
  | add x y hx hy => simp [hx, hy]

private theorem relationSubmodule_le_ker_decomposeAux
    (hℛ : ∀ r ∈ ℛ, SetLike.IsHomogeneousElem 𝒜 r) :
    relationSubmodule R ℛ ≤ LinearMap.ker (decomposeAux ℛ 𝒜) := fun x hx ↦ by
  refine DFinsupp.ext fun i ↦ Subtype.ext ?_
  exact (mk_eq_zero_iff R).2 (((relationSubmodule_isHomogeneous R hℛ).mem_iff 𝒜).1 hx i)

variable (𝒜) in
/-- If the relators are homogeneous, the quotient has the induced internal grading. The pieces are
`grading ℛ 𝒜`, and `decompose_mk` computes the decomposition.

Blueprint: `lem:quotient-api`. -/
@[no_expose, instance_reducible]
def gradedAlgebra (hℛ : ∀ r ∈ ℛ, SetLike.IsHomogeneousElem 𝒜 r) :
    GradedAlgebra (grading ℛ 𝒜) where
  toDecomposition := .ofLinearMap _
    (liftLinear (decomposeAux ℛ 𝒜) (relationSubmodule_le_ker_decomposeAux hℛ))
    (by
      ext x
      exact coeLinearMap_decomposeAux x)
    (by
      refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext ?_
      rintro ⟨_, y, hy, rfl⟩
      simpa using decomposeAux_of_mem hy)

end Grading

end RelationQuotient

end OrlikSolomon
