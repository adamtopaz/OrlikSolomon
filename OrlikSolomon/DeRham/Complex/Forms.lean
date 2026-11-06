/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import OrlikSolomon.DeRham.Exterior.Contraction
public import OrlikSolomon.Grading.Basic

/-!
# De Rham forms and their words

For a commutative algebra `A` over a commutative ring `k`, this file defines the algebra of forms
`Ω^•_{A/k}` as the exterior algebra of Kähler differentials, and proves that every form is a sum of
the words `a₀ da₁ ∧ ⋯ ∧ daₙ`. There is no smoothness hypothesis and no basis of differentials.

The total algebra is primary. Mathlib's `⋀[A]^n Ω[A⁄k]` is by definition a submodule of
`ExteriorAlgebra A Ω[A⁄k]`, so a form of degree `n` is an element `x : Forms k A` with
`x ∈ ⋀[A]^n Ω[A⁄k]`. Then `⋀[A]^0 Ω[A⁄k]` is the image of `A` and `⋀[A]^1 Ω[A⁄k]` is the image of
`Ω[A⁄k]`, and the blueprint's zero modules in negative degrees are never needed.

## Main definitions

* `OrlikSolomon.DeRham.Forms k A`: the algebra of forms.
* `OrlikSolomon.DeRham.diff k`: the universal derivation `a ↦ da`, with values in forms.

## Main results

Blueprint `def:dr-forms`:

* `OrlikSolomon.DeRham.span_word_diff`: the words of length `n` span the forms of degree `n` over
  `A`.
* `OrlikSolomon.DeRham.Forms.induction_exteriorPower` and `OrlikSolomon.DeRham.Forms.induction`: the
  induction principles on the expressions `a₀ da₁ ∧ ⋯ ∧ daₙ`, which are the normal form of this
  library, written `a₀ • word (diff k) [a₁, …, aₙ]`.
* `OrlikSolomon.DeRham.Forms.algHom_ext`: an algebra map out of forms is determined by its values on
  `a` and on `da`.

Blueprint `thm:dr-dga`: `OrlikSolomon.DeRham.isGradedCommutative_forms` is graded commutativity.

## Normal form

`a₀ • word (diff k) l` is the normal form for a list `l`, as in `Forms.induction`. On a list that is
explicit, `word_cons` unfolds the word, and the normal form is `a₀ • (diff k a₁ * ⋯ * diff k aₙ)`.
Each lemma about words here is therefore usable by `rw` for a variable list, and `simp` handles
explicit lists through `d_smul`, `d_diff_mul`, `Forms.map_smul` and `Forms.map_diff`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι)
open KaehlerDifferential (D)

universe u v

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- The algebra of forms `Ω^•_{A/k}`, the exterior algebra of the Kähler differentials of `A` over
`k`, with wedge multiplication. Its multiplication is written `*`. It is an `A`-algebra and a
`k`-algebra. It is graded by the submodules `⋀[A]^n Ω[A⁄k]`, which are the blueprint's `Ω_A^n`.

Blueprint: `def:dr-forms`. -/
abbrev Forms : Type v :=
  ExteriorAlgebra A Ω[A⁄k]

variable {A}

/-- The universal derivation `a ↦ da`, with values in forms of degree one. It is Mathlib's
`KaehlerDifferential.D` followed by the inclusion of degree one, and it is the normal form of that
composite, by `ι_D`. Being a derivation, it has the usual `map_add`, `Derivation.leibniz` and
`Derivation.leibniz_pow`.

Blueprint: `def:dr-forms`, the universal differential `d₀`. -/
noncomputable def diff : Derivation k A (Forms k A) :=
  (ι A : Ω[A⁄k] →ₗ[A] Forms k A).compDer (D k A)

@[simp]
theorem ι_D (a : A) : ι A (D k A a) = diff k a :=
  rfl

theorem diff_apply (a : A) : diff k a = ι A (D k A a) :=
  rfl

/-- Forms on the zero ring are zero, in every degree. -/
instance [Subsingleton A] : Subsingleton (Forms k A) :=
  Module.subsingleton A _

theorem mem_exteriorPower_zero_iff {x : Forms k A} :
    x ∈ ⋀[A]^0 Ω[A⁄k] ↔ ∃ a : A, algebraMap A (Forms k A) a = x := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one]

theorem mem_exteriorPower_one_iff {x : Forms k A} :
    x ∈ ⋀[A]^1 Ω[A⁄k] ↔ ∃ ω : Ω[A⁄k], ι A ω = x := by
  rw [ExteriorAlgebra.exteriorPower, pow_one, LinearMap.mem_range]

theorem algebraMap_mem_exteriorPower_zero (a : A) :
    algebraMap A (Forms k A) a ∈ ⋀[A]^0 Ω[A⁄k] :=
  (mem_exteriorPower_zero_iff k).2 ⟨a, rfl⟩

theorem diff_mem_exteriorPower_one (a : A) : diff k a ∈ ⋀[A]^1 Ω[A⁄k] :=
  (mem_exteriorPower_one_iff k).2 ⟨_, rfl⟩

@[simp]
theorem diff_mul_self (a : A) : diff k a * diff k a = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- Differentials anticommute. -/
theorem diff_mul_add_mul_swap (a b : A) : diff k a * diff k b + diff k b * diff k a = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

/-- Contraction by `ℓ` sends `da` to `ℓ (da)`. This is the case of `exteriorContraction_ι` that
applies to the normal form of `da`. -/
@[simp]
theorem exteriorContraction_diff (ℓ : Module.Dual A Ω[A⁄k]) (a : A) :
    exteriorContraction ℓ (diff k a) = algebraMap A (Forms k A) (ℓ (D k A a)) :=
  exteriorContraction_ι ℓ _

/-- A word `da₁ ∧ ⋯ ∧ daₙ` has degree `n`. -/
theorem word_diff_mem_exteriorPower (l : List A) : word (diff k) l ∈ ⋀[A]^l.length Ω[A⁄k] := by
  have h := word_ι_mem_exteriorPower (A := A) (l.map (D k A))
  rw [word_map, List.length_map] at h
  exact h

/-- An expression `a₀ da₁ ∧ ⋯ ∧ daₙ` has degree `n`. -/
theorem smul_word_diff_mem_exteriorPower (a : A) {l : List A} {n : ℕ} (hl : l.length = n) :
    a • word (diff k) l ∈ ⋀[A]^n Ω[A⁄k] :=
  Submodule.smul_mem _ a (hl ▸ word_diff_mem_exteriorPower k l)

/-- `da ∧ -` raises the degree by one. -/
theorem diff_mul_mem_exteriorPower (a : A) {n : ℕ} {x : Forms k A} (hx : x ∈ ⋀[A]^n Ω[A⁄k]) :
    diff k a * x ∈ ⋀[A]^(n + 1) Ω[A⁄k] :=
  ι_mul_mem_exteriorPower _ hx

variable (A) in
/-- Forms are graded commutative: homogeneous forms commute up to the sign `(-1)^(pq)`, by
`mul_comm_of_mem_exteriorPower`, with no hypothesis on `2`.

Blueprint: `thm:dr-dga`. -/
theorem isGradedCommutative_forms :
    IsGradedCommutative (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (fun n : ℕ => (n : ℤ)) :=
  fun _ _ _ _ hx hy => mul_comm_of_mem_exteriorPower hx hy

/-- If a family spans `M`, then the words of length `n` in that family span `⋀^n M`. -/
theorem span_word_length_of_span {M : Type*} [AddCommGroup M] [Module A M] {I : Type*} {x : I → M}
    (hx : Submodule.span A (Set.range x) = ⊤) (n : ℕ) :
    Submodule.span A {y | ∃ l : List I, l.length = n ∧ word (fun i => ι A (x i)) l = y} =
      ⋀[A]^n M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl, rfl⟩
    have h := word_ι_mem_exteriorPower (A := A) (l.map x)
    rwa [word_map, List.length_map] at h
  · rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top A n M hx, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    choose w hw using fun i => hv (Set.mem_range_self i)
    refine Submodule.subset_span ⟨List.ofFn w, by simp, ?_⟩
    rw [ExteriorAlgebra.ιMulti_apply]
    simp [word, List.map_ofFn, Function.comp_def, hw]

variable (A) in
/-- The words `da₁ ∧ ⋯ ∧ daₙ` span the forms of degree `n` over `A`.

Blueprint: `def:dr-forms`, the last sentence. -/
theorem span_word_diff (n : ℕ) :
    Submodule.span A {y | ∃ l : List A, l.length = n ∧ word (diff k) l = y} = ⋀[A]^n Ω[A⁄k] :=
  span_word_length_of_span (KaehlerDifferential.span_range_derivation k A) n

/-- If a family spans `M`, then induction over the `n`th exterior power may treat only scalar
multiples of the words of length `n` in that family, zero and sums. Compare
`exteriorPower_induction`, whose letters are arbitrary. -/
@[elab_as_elim]
theorem exteriorPower_induction_of_span {M : Type*} [AddCommGroup M] [Module A M] {I : Type*}
    {x : I → M} (hx : Submodule.span A (Set.range x) = ⊤) {n : ℕ}
    {p : (y : ExteriorAlgebra A M) → y ∈ ⋀[A]^n M → Prop}
    (word : ∀ (a : A) (l : List I) (_ : l.length = n)
      (h : a • word (fun i => ι A (x i)) l ∈ ⋀[A]^n M), p (a • word (fun i => ι A (x i)) l) h)
    (zero : p 0 (zero_mem _))
    (add : ∀ y hy z hz, p y hy → p z hz → p (y + z) (add_mem hy hz))
    {y : ExteriorAlgebra A M} (hy : y ∈ ⋀[A]^n M) : p y hy := by
  have key : ∀ y ∈ Submodule.span A
      {y | ∃ l : List I, l.length = n ∧ OrlikSolomon.word (fun i => ι A (x i)) l = y},
      ∀ b : A, ∃ h : b • y ∈ ⋀[A]^n M, p (b • y) h := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      intro b
      have h : OrlikSolomon.word (fun i => ι A (x i)) l ∈ ⋀[A]^n M := by
        rw [← span_word_length_of_span hx n]
        exact Submodule.subset_span ⟨l, hl, rfl⟩
      exact ⟨Submodule.smul_mem _ b h, word b l hl _⟩
    | zero =>
      intro b
      simpa using zero
    | add y z _ _ hy hz =>
      intro b
      obtain ⟨h₁, h₁'⟩ := hy b
      obtain ⟨h₂, h₂'⟩ := hz b
      simp only [smul_add]
      exact ⟨add_mem h₁ h₂, add _ h₁ _ h₂ h₁' h₂'⟩
    | smul c y _ hy =>
      intro b
      simpa only [smul_smul] using hy (b * c)
  have := key y (by rwa [span_word_length_of_span hx]) 1
  simpa using this.2

namespace Forms

variable {k}

/-- Induction over the forms of degree `n`: it suffices to treat the expressions
`a₀ da₁ ∧ ⋯ ∧ daₙ` and sums. Zero is such an expression, with `a₀ = 0`.

Blueprint: `def:dr-forms`, the last sentence. -/
@[elab_as_elim]
theorem induction_exteriorPower {n : ℕ}
    {p : (x : Forms k A) → x ∈ ⋀[A]^n Ω[A⁄k] → Prop}
    (word : ∀ (a : A) (l : List A) (hl : l.length = n),
      p (a • word (diff k) l) (smul_word_diff_mem_exteriorPower k a hl))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    {x : Forms k A} (hx : x ∈ ⋀[A]^n Ω[A⁄k]) : p x hx := by
  refine exteriorPower_induction_of_span (KaehlerDifferential.span_range_derivation k A)
    (fun a l hl h => word a l hl) ?_ add hx
  have h := word 0 (List.replicate n 0) (by simp)
  simpa using h

/-- Induction over all forms: it suffices to treat the expressions `a₀ da₁ ∧ ⋯ ∧ daₙ` and sums.

Blueprint: `def:dr-forms`, the last sentence. -/
@[elab_as_elim]
theorem induction {p : Forms k A → Prop}
    (word : ∀ (a : A) (l : List A), p (a • word (diff k) l))
    (add : ∀ x y, p x → p y → p (x + y))
    (x : Forms k A) : p x := by
  refine DirectSum.Decomposition.inductionOn (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) ?_ ?_ add x
  · simpa using word 0 []
  · rintro n ⟨y, hy⟩
    induction hy using induction_exteriorPower with
    | word a l _ => exact word a l
    | add y _ z _ hy hz => exact add y z hy hz

/-- An algebra map out of forms is determined by its values on `a` and on `da`. Mathlib's
`ExteriorAlgebra.hom_ext` is the `A`-linear version of this, and it does not apply to the maps of
this file, which are only `k`-linear. -/
@[ext]
theorem algHom_ext {T : Type*} [Semiring T] [Algebra k T] {f g : Forms k A →ₐ[k] T}
    (h₀ : ∀ a : A, f (algebraMap A (Forms k A) a) = g (algebraMap A (Forms k A) a))
    (h₁ : ∀ a : A, f (diff k a) = g (diff k a)) : f = g := by
  refine AlgHom.ext fun x => ?_
  induction x using induction with
  | word a l =>
    simp only [Algebra.smul_def, map_mul, map_word, h₀, h₁]
  | add x y hx hy => simp only [map_add, hx, hy]

end Forms

end OrlikSolomon.DeRham
