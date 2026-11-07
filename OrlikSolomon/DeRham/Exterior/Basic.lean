/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import OrlikSolomon.Algebra.ExteriorWords

/-!
# Exterior algebra: words, degrees and change of rings

This file collects what the other modules under `DeRham/Exterior` share. Everything holds over an
arbitrary commutative ring, and nothing divides by two.

Mathlib's `⋀[A]^n M` is by definition a submodule of `ExteriorAlgebra A M`, so `↥(⋀[A]^n M)` is
literally the type of homogeneous elements of degree `n`. These modules therefore state a result on
the total algebra, with membership in `⋀[A]^n M` as a hypothesis, and add a form typed by degree
when the result is a map between exterior powers. The coercion lemmas `coe_wedgeLeft`,
`coe_exteriorProj` and `coe_powerMap` pass between the two.

## Main definitions

* `OrlikSolomon.DeRham.wedgeLeft e n`: the map `e ∧ - : ⋀^n M → ⋀^(n+1) M`.
* `OrlikSolomon.DeRham.exteriorProj n`: the projection `⋀ M → ⋀^n M` onto a homogeneous component.
* `OrlikSolomon.DeRham.exteriorMap S g` and `OrlikSolomon.DeRham.powerMap S g n`: the maps
  `⋀_A M → ⋀_S M'` and `⋀_A^n M → ⋀_S^n M'` of an `A`-linear map from an `A`-module to an
  `S`-module.
* `OrlikSolomon.DeRham.exteriorCongr`: the algebra equivalence of a linear equivalence.

## Main results

Blueprint `lem:dr-exterior`, its last sentence:

* `OrlikSolomon.DeRham.span_word_ι_length`: words of length `n` span `⋀^n M`, connecting the word
  calculus of `Algebra/ExteriorWords` to Mathlib's `ExteriorAlgebra.ιMulti_span_fixedDegree`.
  Mathlib's `exteriorPower.ιMulti_span_of_span` restricts the letters to a spanning set.
* `OrlikSolomon.DeRham.mul_self_eq_zero_of_mem_exteriorPower_one`: degree-one elements square to
  zero.
* `OrlikSolomon.DeRham.mul_comm_of_mem_exteriorPower`: homogeneous elements commute with the sign
  `(-1)^(pq)`. It comes from `IsExteriorFamily.word_mul_word_comm`, through
  `OrlikSolomon.DeRham.isExteriorFamily_ι`.

`OrlikSolomon.DeRham.exteriorPower_induction` is the induction principle used for homogeneous
elements. Blueprint: `thm:dr-dga` uses the functoriality of `exteriorMap_comp` and `powerMap_comp`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι ιMulti)

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-! ### Words and signs -/

variable (A M) in
/-- The degree-one generators of an exterior algebra form an exterior family, so the word and sign
calculus of `Algebra/ExteriorWords` applies to them. -/
theorem isExteriorFamily_ι : IsExteriorFamily (ι A : M → ExteriorAlgebra A M) :=
  ⟨ExteriorAlgebra.ι_sq_zero, fun x y _ => ExteriorAlgebra.ι_add_mul_swap x y⟩

/-- `ExteriorAlgebra.ιMulti` is the word along the list of its entries. -/
theorem ιMulti_eq_word {n : ℕ} (v : Fin n → M) :
    ιMulti A n v = word (ι A) (List.ofFn v) := by
  simp [word, ExteriorAlgebra.ιMulti_apply, List.map_ofFn, Function.comp_def]

/-- A word of length `n` in degree-one generators has exterior degree `n`. -/
theorem word_ι_mem_exteriorPower (l : List M) : word (ι A) l ∈ ⋀[A]^l.length M := by
  induction l with
  | nil => exact Submodule.one_le.1 (pow_zero _).ge
  | cons i l ih =>
    rw [word_cons, List.length_cons, ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

variable (A M) in
/-- Words of length `n` in the degree-one generators span the `n`th exterior power.

Blueprint: `lem:dr-exterior`. -/
theorem span_word_ι_length (n : ℕ) :
    Submodule.span A {x | ∃ l : List M, l.length = n ∧ word (ι A) l = x} = ⋀[A]^n M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl, rfl⟩
    exact word_ι_mem_exteriorPower l
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨List.ofFn v, by simp, (ιMulti_eq_word v).symm⟩

/-- Induction over elements of the `n`th exterior power: it suffices to treat words of length `n`,
sums and scalar multiples. -/
@[elab_as_elim]
theorem exteriorPower_induction {n : ℕ} {p : (x : ExteriorAlgebra A M) → x ∈ ⋀[A]^n M → Prop}
    (word : ∀ (l : List M) (hl : l.length = n),
      p (word (ι A) l) (hl ▸ word_ι_mem_exteriorPower l))
    (zero : p 0 (zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (smul : ∀ (a : A) (x hx), p x hx → p (a • x) (Submodule.smul_mem _ a hx))
    {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^n M) : p x hx := by
  have key : ∀ y ∈ Submodule.span A
      {x | ∃ l : List M, l.length = n ∧ OrlikSolomon.word (ι A) l = x},
      ∃ h : y ∈ ⋀[A]^n M, p y h := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact ⟨_, word l hl⟩
    | zero => exact ⟨_, zero⟩
    | add y z _ _ hy hz =>
      obtain ⟨h₁, h₁'⟩ := hy
      obtain ⟨h₂, h₂'⟩ := hz
      exact ⟨_, add y z h₁ h₂ h₁' h₂'⟩
    | smul a y _ hy =>
      obtain ⟨h, h'⟩ := hy
      exact ⟨_, smul a y h h'⟩
  exact (key x (span_word_ι_length A M n ▸ hx)).2

/-- Homogeneous elements of an exterior algebra commute up to the sign `(-1)^(pq)`, over any
commutative ring.

Blueprint: `lem:dr-exterior`. -/
theorem mul_comm_of_mem_exteriorPower {p q : ℕ} {x y : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^p M) (hy : y ∈ ⋀[A]^q M) :
    x * y = ((p : ℤ) * q).negOnePow • (y * x) := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => simp only [add_mul, mul_add, h₁, h₂, smul_add]
  | smul a x _ h => simp only [smul_mul_assoc, mul_smul_comm, h, smul_comm a]
  | word l₁ hl₁ =>
    induction hy using exteriorPower_induction with
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => simp only [add_mul, mul_add, h₁, h₂, smul_add]
    | smul a y _ h => simp only [smul_mul_assoc, mul_smul_comm, h, smul_comm a]
    | word l₂ hl₂ =>
      rw [(isExteriorFamily_ι A M).word_mul_word_comm, hl₁, hl₂]

/-- An element of exterior degree one squares to zero. This is the defining relation, not a
consequence of anticommutativity, so it holds in characteristic two.

Blueprint: `lem:dr-exterior`. -/
theorem mul_self_eq_zero_of_mem_exteriorPower_one {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^1 M) : x * x = 0 := by
  rw [ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  exact ExteriorAlgebra.ι_sq_zero m

/-- The left product by a degree-one generator raises exterior degree by one. -/
theorem ι_mul_mem_exteriorPower (e : M) {n : ℕ} {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^n M) :
    ι A e * x ∈ ⋀[A]^(n + 1) M := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hx

/-! ### The left wedge -/

/-- The left wedge `e ∧ - : ⋀^n M → ⋀^(n+1) M`. -/
noncomputable def wedgeLeft (e : M) (n : ℕ) : ⋀[A]^n M →ₗ[A] ⋀[A]^(n + 1) M :=
  ((LinearMap.mulLeft A (ι A e)).comp (⋀[A]^n M).subtype).codRestrict _ fun x =>
    ι_mul_mem_exteriorPower e x.2

@[simp]
theorem coe_wedgeLeft (e : M) (n : ℕ) (x : ⋀[A]^n M) :
    (wedgeLeft e n x : ExteriorAlgebra A M) = ι A e * x :=
  rfl

@[simp]
theorem wedgeLeft_zero (n : ℕ) : wedgeLeft (0 : M) n = (0 : ⋀[A]^n M →ₗ[A] ⋀[A]^(n + 1) M) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp

theorem wedgeLeft_add (e e' : M) (n : ℕ) (x : ⋀[A]^n M) :
    wedgeLeft (e + e') n x = wedgeLeft e n x + wedgeLeft e' n x :=
  Subtype.ext (by simp [add_mul])

theorem wedgeLeft_smul (a : A) (e : M) (n : ℕ) (x : ⋀[A]^n M) :
    wedgeLeft (a • e) n x = a • wedgeLeft e n x :=
  Subtype.ext (by simp)

/-! ### Homogeneous components -/

/-- The projection of the exterior algebra onto its `n`th exterior power, split by the inclusion.
This is why the `n`th exterior power is a direct summand over any ring, with no flatness. -/
noncomputable def exteriorProj (n : ℕ) : ExteriorAlgebra A M →ₗ[A] ⋀[A]^n M :=
  (GradedAlgebra.proj (fun i : ℕ => ⋀[A]^i M) n).codRestrict _ fun x => by
    rw [GradedAlgebra.proj_apply]
    exact SetLike.coe_mem _

theorem coe_exteriorProj (n : ℕ) (x : ExteriorAlgebra A M) :
    (exteriorProj n x : ExteriorAlgebra A M) =
      DirectSum.decompose (fun i : ℕ => ⋀[A]^i M) x n :=
  rfl

@[simp]
theorem exteriorProj_coe {n : ℕ} (x : ⋀[A]^n M) :
    exteriorProj n (x : ExteriorAlgebra A M) = x :=
  Subtype.ext (DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[A]^i M) x.2)

theorem exteriorProj_of_mem {n : ℕ} {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^n M) :
    (exteriorProj n x : ExteriorAlgebra A M) = x :=
  congrArg Subtype.val (exteriorProj_coe ⟨x, hx⟩)

/-- The components of a homogeneous element in other degrees vanish. -/
theorem exteriorProj_of_mem_of_ne {m n : ℕ} (hmn : m ≠ n) {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^m M) : exteriorProj n x = 0 :=
  Subtype.ext (DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[A]^i M) hx hmn)

/-- An element of the exterior algebra is determined by its homogeneous components. -/
theorem eq_of_forall_exteriorProj_eq {x y : ExteriorAlgebra A M}
    (h : ∀ n, exteriorProj n x = exteriorProj n y) : x = y := by
  refine (DirectSum.decompose (fun i : ℕ => ⋀[A]^i M)).injective (DFinsupp.ext fun n => ?_)
  exact Subtype.ext (congrArg Subtype.val (h n))

/-- The degree `n + 1` component of `m ∧ y` is `m ∧` the degree `n` component of `y`. -/
theorem exteriorProj_ι_mul (m : M) (n : ℕ) (y : ExteriorAlgebra A M) :
    exteriorProj (n + 1) (ι A m * y) = wedgeLeft m n (exteriorProj n y) := by
  refine Subtype.ext ?_
  have hm : ι A m ∈ ⋀[A]^1 M := by simp
  rw [coe_exteriorProj,
    DirectSum.coe_decompose_mul_of_left_mem_of_le (fun i : ℕ => ⋀[A]^i M) hm (by omega)]
  simp [coe_exteriorProj]

/-- The degree zero component of `m ∧ y` vanishes. -/
@[simp]
theorem exteriorProj_zero_ι_mul (m : M) (y : ExteriorAlgebra A M) :
    exteriorProj 0 (ι A m * y) = 0 := by
  refine Subtype.ext ?_
  have hm : ι A m ∈ ⋀[A]^1 M := by simp
  rw [coe_exteriorProj,
    DirectSum.coe_decompose_mul_of_left_mem_of_not_le (fun i : ℕ => ⋀[A]^i M) hm (by omega)]
  rfl

/-! ### Functoriality along a change of rings -/

section Map

variable (S : Type*) [CommRing S] [Algebra A S]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module S M'] [IsScalarTower A S M']

/-- The algebra map `⋀_A M → ⋀_S M'` induced by an `A`-linear map `g : M → M'` to an `S`-module, for
a commutative `A`-algebra `S`. For `S = A` it is `ExteriorAlgebra.map g`, by `exteriorMap_self`.

Blueprint: the maps on forms in `thm:dr-dga` have this shape, and it is the map underlying the
identifications of `lem:dr-exterior`. -/
noncomputable def exteriorMap (g : M →ₗ[A] M') : ExteriorAlgebra A M →ₐ[A] ExteriorAlgebra S M' :=
  ExteriorAlgebra.lift A
    ⟨((ι S).restrictScalars A).comp g, fun m => ExteriorAlgebra.ι_sq_zero (g m)⟩

@[simp]
theorem exteriorMap_ι (g : M →ₗ[A] M') (m : M) : exteriorMap S g (ι A m) = ι S (g m) :=
  ExteriorAlgebra.lift_ι_apply A _ _ m

theorem exteriorMap_self (g : M →ₗ[A] M') : exteriorMap A g = ExteriorAlgebra.map g := by
  ext m
  simp

@[simp]
theorem exteriorMap_id : exteriorMap A (LinearMap.id : M →ₗ[A] M) = AlgHom.id A _ := by
  ext m
  simp

@[simp]
theorem exteriorMap_ιMulti (g : M →ₗ[A] M') {n : ℕ} (m : Fin n → M) :
    exteriorMap S g (ιMulti A n m) = ιMulti S n (g ∘ m) := by
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def]

/-- `exteriorMap` sends a word to the word along the image of its letters. As a simp lemma this is
already covered by `map_word` and `exteriorMap_ι`, which give the reindexed family instead. -/
theorem exteriorMap_word (g : M →ₗ[A] M') (l : List M) :
    exteriorMap S g (word (ι A) l) = word (ι S) (l.map g) := by
  simp [word_map]

/-- `exteriorMap` preserves exterior degree. -/
theorem exteriorMap_mem_exteriorPower (g : M →ₗ[A] M') {n : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^n M) : exteriorMap S g x ∈ ⋀[S]^n M' := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul S a]
    exact Submodule.smul_mem _ _ hx
  | word l hl =>
    rw [exteriorMap_word]
    simpa [hl] using word_ι_mem_exteriorPower (l.map g)

/-- If the ring map and the module map are surjective then so is `exteriorMap`. -/
theorem exteriorMap_surjective (hS : Function.Surjective (algebraMap A S)) {g : M →ₗ[A] M'}
    (hg : Function.Surjective g) : Function.Surjective (exteriorMap S g) := by
  intro y
  induction y using ExteriorAlgebra.induction with
  | algebraMap s =>
    obtain ⟨a, rfl⟩ := hS s
    exact ⟨algebraMap A _ a, by rw [AlgHom.commutes]; rfl⟩
  | ι m =>
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨ι A m, exteriorMap_ι S g m⟩
  | mul a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a * b, map_mul _ a b⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ a b⟩

/-- The `A`-linear map `⋀_A^n M → ⋀_S^n M'` induced by an `A`-linear map `g : M → M'` to an
`S`-module. For `S = A` it is `exteriorPower.map n g`, by `powerMap_self`.

Blueprint: the degreewise form of the maps in `lem:dr-exterior` and `thm:dr-dga`. -/
noncomputable def powerMap (g : M →ₗ[A] M') (n : ℕ) : ⋀[A]^n M →ₗ[A] ⋀[S]^n M' :=
  LinearMap.codRestrict ((⋀[S]^n M').restrictScalars A)
    ((exteriorMap S g).toLinearMap.comp (⋀[A]^n M).subtype)
    fun x => exteriorMap_mem_exteriorPower S g x.2

@[simp]
theorem coe_powerMap (g : M →ₗ[A] M') (n : ℕ) (x : ⋀[A]^n M) :
    (powerMap S g n x : ExteriorAlgebra S M') = exteriorMap S g x :=
  rfl

@[simp]
theorem powerMap_ιMulti (g : M →ₗ[A] M') {n : ℕ} (m : Fin n → M) :
    powerMap S g n (exteriorPower.ιMulti A n m) = exteriorPower.ιMulti S n (g ∘ m) :=
  Subtype.ext (exteriorMap_ιMulti S g m)

theorem powerMap_self (g : M →ₗ[A] M') (n : ℕ) : powerMap A g n = exteriorPower.map n g := by
  ext m
  simp [Function.comp_def]

section Comp

variable {S' : Type*} [CommRing S'] [Algebra A S'] [Algebra S S'] [IsScalarTower A S S']
  {M'' : Type*} [AddCommGroup M''] [Module A M''] [Module S M''] [Module S' M'']
  [IsScalarTower A S M''] [IsScalarTower S S' M''] [IsScalarTower A S' M'']

variable (S') in
/-- `exteriorMap` respects composition.

Blueprint: the functoriality in `thm:dr-dga`. -/
theorem exteriorMap_comp (h : M' →ₗ[S] M'') (g : M →ₗ[A] M') (x : ExteriorAlgebra A M) :
    exteriorMap S' h (exteriorMap S g x) = exteriorMap S' ((h.restrictScalars A) ∘ₗ g) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
    rw [AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A S (ExteriorAlgebra S M') a, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply A S (ExteriorAlgebra S' M'') a]
  | ι m => simp
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (S') in
/-- `powerMap` respects composition.

Blueprint: the functoriality in `thm:dr-dga`. -/
theorem powerMap_comp (h : M' →ₗ[S] M'') (g : M →ₗ[A] M') (n : ℕ) (x : ⋀[A]^n M) :
    powerMap S' h n (powerMap S g n x) = powerMap S' ((h.restrictScalars A) ∘ₗ g) n x :=
  Subtype.ext (exteriorMap_comp S S' h g x)

end Comp

end Map

/-- The exterior algebra equivalence induced by a linear equivalence. -/
noncomputable def exteriorCongr {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    ExteriorAlgebra A M ≃ₐ[A] ExteriorAlgebra A N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by ext; simp) (by ext; simp)

@[simp]
theorem exteriorCongr_apply {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (x : ExteriorAlgebra A M) : exteriorCongr e x = ExteriorAlgebra.map e.toLinearMap x :=
  rfl

end OrlikSolomon.DeRham
