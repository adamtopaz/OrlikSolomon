/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import OrlikSolomon.DeRham.Exterior.Basic

/-!
# Contraction of an exterior algebra by a functional

For a functional `ℓ : M → A`, contraction `ι_ℓ` is a graded antiderivation of degree `-1` on
`ExteriorAlgebra A M`. It is Mathlib's `CliffordAlgebra.contractLeft` for the zero quadratic form,
which is defined with no division by two. This file gives it the form of `lem:dr-contraction`.

## Main definitions

* `OrlikSolomon.DeRham.exteriorContraction`: contraction, linear in the functional as well, so that
  scaling a functional scales the operator.
* `OrlikSolomon.DeRham.powerContraction ℓ n`: its restriction `⋀^(n+1) M → ⋀^n M`.
* `OrlikSolomon.DeRham.IsLineSplitting e ℓ i r`: `M = K ⊕ A e`, where `ℓ e = 1`.

## Main results

Blueprint `lem:dr-contraction`:

* `OrlikSolomon.DeRham.exteriorContraction_ιMulti`: the word formula.
* `OrlikSolomon.DeRham.exteriorContraction_mul_of_mem_exteriorPower`: the signed product rule.
* `OrlikSolomon.DeRham.exteriorContraction_ι_mul_add`: `ι_ℓ (e ∧ α) + e ∧ ι_ℓ α = ℓ e • α`.
* `OrlikSolomon.DeRham.ker_wedgeLeft_succ` and `OrlikSolomon.DeRham.ker_wedgeLeft_zero`: if
  `ℓ e = 1`, then the kernel of `e ∧ -` on `⋀^n M` is `e ∧ ⋀^(n-1) M`, also stated as
  `OrlikSolomon.DeRham.exact_wedgeLeft`.

For `lem:dr-cartan` and `lem:dr-polynomial-splitting`:

* `OrlikSolomon.DeRham.exteriorMap_exteriorContraction`: contraction is natural, also along a change
  of rings.
* `OrlikSolomon.DeRham.IsLineSplitting.powerEquiv`: `⋀^(n+1) M ≃ ⋀^(n+1) K × ⋀^n K`, that is, each
  form is uniquely `α + e ∧ β` with `α` and `β` coming from `K`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι ιMulti)

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-! ### Contraction by a functional -/

/-- Contraction `ι_ℓ` of the exterior algebra by a functional `ℓ : M → A`. It kills `1` and
satisfies `ι_ℓ (m ∧ x) = ℓ m • x - m ∧ ι_ℓ x`, and it is linear in `ℓ`. It is a graded
antiderivation of degree `-1`, not a derivation in the sense of Mathlib.

This is Mathlib's `CliffordAlgebra.contractLeft` for the zero quadratic form.

Blueprint: `lem:dr-contraction`. -/
noncomputable def exteriorContraction :
    Module.Dual A M →ₗ[A] ExteriorAlgebra A M →ₗ[A] ExteriorAlgebra A M :=
  CliffordAlgebra.contractLeft

variable (ℓ ℓ' : Module.Dual A M)

@[simp]
theorem exteriorContraction_one : exteriorContraction ℓ (1 : ExteriorAlgebra A M) = 0 :=
  CliffordAlgebra.contractLeft_one _ ℓ

@[simp]
theorem exteriorContraction_algebraMap (a : A) :
    exteriorContraction ℓ (algebraMap A (ExteriorAlgebra A M) a) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ ℓ a

@[simp]
theorem exteriorContraction_ι (m : M) :
    exteriorContraction ℓ (ι A m) = algebraMap A _ (ℓ m) :=
  CliffordAlgebra.contractLeft_ι _ ℓ m

/-- The recursion defining contraction: this is the second displayed identity of
`lem:dr-contraction`, up to moving a term.

Blueprint: `lem:dr-contraction`. -/
@[simp]
theorem exteriorContraction_ι_mul (m : M) (x : ExteriorAlgebra A M) :
    exteriorContraction ℓ (ι A m * x) = ℓ m • x - ι A m * exteriorContraction ℓ x :=
  CliffordAlgebra.contractLeft_ι_mul ℓ m x

/-- The homotopy identity `ι_ℓ (e ∧ α) + e ∧ ι_ℓ α = ℓ e • α`.

Blueprint: `lem:dr-contraction`. -/
theorem exteriorContraction_ι_mul_add (e : M) (x : ExteriorAlgebra A M) :
    exteriorContraction ℓ (ι A e * x) + ι A e * exteriorContraction ℓ x = ℓ e • x := by
  simp

/-- Contraction by a fixed functional squares to zero. -/
@[simp]
theorem exteriorContraction_exteriorContraction (x : ExteriorAlgebra A M) :
    exteriorContraction ℓ (exteriorContraction ℓ x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft ℓ x

/-- Contractions by two functionals anticommute. -/
theorem exteriorContraction_comm (x : ExteriorAlgebra A M) :
    exteriorContraction ℓ (exteriorContraction ℓ' x) =
      -exteriorContraction ℓ' (exteriorContraction ℓ x) :=
  CliffordAlgebra.contractLeft_comm ℓ ℓ' x

/-- The signed product rule for a word on the left. -/
theorem exteriorContraction_word_mul (l : List M) (y : ExteriorAlgebra A M) :
    exteriorContraction ℓ (word (ι A) l * y) =
      exteriorContraction ℓ (word (ι A) l) * y +
        (l.length : ℤ).negOnePow • (word (ι A) l * exteriorContraction ℓ y) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [word_cons, mul_assoc, exteriorContraction_ι_mul, ih, mul_add, sub_mul,
      List.length_cons, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul,
      mul_smul_comm, smul_mul_assoc]
    abel

/-- The signed product rule `ι_ℓ (α ∧ β) = ι_ℓ α ∧ β + (-1)^p α ∧ ι_ℓ β` when `α` has exterior
degree `p`. The right factor need not be homogeneous.

Blueprint: `lem:dr-contraction`. -/
theorem exteriorContraction_mul_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^p M) (y : ExteriorAlgebra A M) :
    exteriorContraction ℓ (x * y) =
      exteriorContraction ℓ x * y + (p : ℤ).negOnePow • (x * exteriorContraction ℓ y) := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ =>
    simp only [add_mul, map_add, h₁, h₂, smul_add]
    abel
  | smul a x _ h =>
    simp only [smul_mul_assoc, map_smul, h, smul_add, smul_comm a]
  | word l hl =>
    rw [exteriorContraction_word_mul, hl]

/-- Contraction lowers the length of a nonempty word by one. -/
private theorem exteriorContraction_word_mem (l : List M) (n : ℕ) (hl : l.length = n + 1) :
    exteriorContraction ℓ (word (ι A) l) ∈ ⋀[A]^n M := by
  match l, hl with
  | m :: l, hl =>
    have hl' : l.length = n := by simpa using hl
    rw [word_cons, exteriorContraction_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ (hl' ▸ word_ι_mem_exteriorPower l)) ?_
    match n, l, hl' with
    | 0, [], _ => simp
    | k + 1, l', hl' => exact ι_mul_mem_exteriorPower m (exteriorContraction_word_mem l' k hl')

/-- Contraction lowers a positive exterior degree by one. -/
theorem exteriorContraction_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^(n + 1) M) : exteriorContraction ℓ x ∈ ⋀[A]^n M := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  | word l hl => exact exteriorContraction_word_mem ℓ l n hl

/-- Contraction vanishes in exterior degree zero. -/
theorem exteriorContraction_eq_zero_of_mem_exteriorPower_zero {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^0 M) : exteriorContraction ℓ x = 0 := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]
  | word l hl => simp [List.length_eq_zero_iff.1 hl]

/-- The word formula for contraction: `ι_ℓ (m₀ ∧ ⋯ ∧ mₙ) = ∑ⱼ (-1)ʲ ℓ(mⱼ) m₀ ∧ ⋯ m̂ⱼ ⋯ ∧ mₙ`.

Blueprint: `lem:dr-contraction`. -/
theorem exteriorContraction_ιMulti {n : ℕ} (m : Fin (n + 1) → M) :
    exteriorContraction ℓ (ιMulti A (n + 1) m) =
      ∑ j : Fin (n + 1), ((j : ℕ) : ℤ).negOnePow • (ℓ (m j) • ιMulti A n (m ∘ j.succAbove)) := by
  induction n with
  | zero =>
    simp [ExteriorAlgebra.ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hsucc (j : Fin (n + 1)) : ιMulti A (n + 1) (m ∘ j.succ.succAbove) =
        ι A (m 0) * ιMulti A n (Matrix.vecTail m ∘ j.succAbove) := by
      have h0 : (m ∘ j.succ.succAbove) 0 = m 0 := by simp
      have ht : Matrix.vecTail (m ∘ j.succ.succAbove) = Matrix.vecTail m ∘ j.succAbove := by
        ext i
        simp [Matrix.vecTail]
      rw [ExteriorAlgebra.ιMulti_succ_apply, h0, ht]
    have hzero : m ∘ Fin.succAbove (0 : Fin (n + 2)) = Matrix.vecTail m := by
      ext i
      simp [Matrix.vecTail]
    rw [ExteriorAlgebra.ιMulti_succ_apply, exteriorContraction_ι_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [hsucc, hzero, Fin.val_succ, Fin.val_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      Int.negOnePow_zero, one_smul, Int.negOnePow_succ, Units.neg_smul, Finset.mul_sum,
      mul_smul_comm, sub_eq_add_neg, Finset.sum_neg_distrib, Matrix.vecTail,
      Function.comp_apply]

/-! ### Degree-typed wedge and contraction -/

/-- Contraction `⋀^(n+1) M → ⋀^n M`, the restriction of `exteriorContraction ℓ`. -/
noncomputable def powerContraction (n : ℕ) : ⋀[A]^(n + 1) M →ₗ[A] ⋀[A]^n M :=
  ((exteriorContraction ℓ).comp (⋀[A]^(n + 1) M).subtype).codRestrict _ fun x =>
    exteriorContraction_mem_exteriorPower ℓ x.2

@[simp]
theorem coe_powerContraction (n : ℕ) (x : ⋀[A]^(n + 1) M) :
    (powerContraction ℓ n x : ExteriorAlgebra A M) = exteriorContraction ℓ x :=
  rfl

variable {ℓ} in
/-- If `ℓ e = 1` then `α = e ∧ ι_ℓ α` whenever `e ∧ α = 0`.

Blueprint: `lem:dr-contraction`. -/
theorem eq_ι_mul_exteriorContraction_of_ι_mul_eq_zero {e : M} (he : ℓ e = 1)
    {x : ExteriorAlgebra A M} (hx : ι A e * x = 0) :
    x = ι A e * exteriorContraction ℓ x := by
  have h := exteriorContraction_ι_mul_add ℓ e x
  rwa [hx, map_zero, zero_add, he, one_smul, eq_comm] at h

variable {ℓ} in
/-- If `ℓ e = 1`, the kernel of `e ∧ -` on `⋀^(n+1) M` is `e ∧ ⋀^n M`.

Blueprint: `lem:dr-contraction`. -/
theorem ker_wedgeLeft_succ {e : M} (he : ℓ e = 1) (n : ℕ) :
    LinearMap.ker (wedgeLeft (A := A) e (n + 1)) = LinearMap.range (wedgeLeft e n) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    have hx' : ι A e * (x : ExteriorAlgebra A M) = 0 := congrArg Subtype.val hx
    exact ⟨powerContraction ℓ n x, Subtype.ext
      (eq_ι_mul_exteriorContraction_of_ι_mul_eq_zero he hx').symm⟩
  · rintro ⟨y, rfl⟩
    refine Subtype.ext ?_
    simp [← mul_assoc]

variable {ℓ} in
/-- If `ℓ e = 1`, then `e ∧ -` is exact in positive degrees.

Blueprint: `lem:dr-contraction`. -/
theorem exact_wedgeLeft {e : M} (he : ℓ e = 1) (n : ℕ) :
    Function.Exact (wedgeLeft (A := A) e n) (wedgeLeft e (n + 1)) :=
  LinearMap.exact_iff.2 (ker_wedgeLeft_succ he n)

variable {ℓ} in
/-- If `ℓ e = 1`, then `e ∧ -` is injective on `⋀^0 M`.

Blueprint: `lem:dr-contraction`, in degree zero. -/
theorem ker_wedgeLeft_zero {e : M} (he : ℓ e = 1) :
    LinearMap.ker (wedgeLeft (A := A) e 0) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hx' : ι A e * (x : ExteriorAlgebra A M) = 0 := congrArg Subtype.val hx
  refine Subtype.ext ?_
  rw [eq_ι_mul_exteriorContraction_of_ι_mul_eq_zero he hx',
    exteriorContraction_eq_zero_of_mem_exteriorPower_zero ℓ x.2, mul_zero]
  rfl

/-! ### Naturality -/

section Naturality

variable (S : Type*) [CommRing S] [Algebra A S]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module S M'] [IsScalarTower A S M']

/-- Contraction is compatible with `exteriorMap`, when the functionals are. This covers
functoriality in the module, for `S = A`, and the extension of a contraction to a base change or a
localization.

Blueprint: `lem:dr-cartan`, where contractions extend to localizations. -/
theorem exteriorMap_exteriorContraction {g : M →ₗ[A] M'} {ℓ : Module.Dual A M}
    {ℓ' : Module.Dual S M'} (h : ∀ m, ℓ' (g m) = algebraMap A S (ℓ m))
    (x : ExteriorAlgebra A M) :
    exteriorMap S g (exteriorContraction ℓ x) = exteriorContraction ℓ' (exteriorMap S g x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a =>
    have : exteriorMap S g (algebraMap A _ a) = algebraMap S _ (algebraMap A S a) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S (ExteriorAlgebra S M') a]
    simp only [exteriorContraction_algebraMap, map_zero, this]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul x m hx =>
    simp only [exteriorContraction_ι_mul, map_sub, map_smul, map_mul, exteriorMap_ι, hx, h,
      algebraMap_smul]

end Naturality

/-! ### Splitting off a line -/

section LineSplitting

variable {K : Type*} [AddCommGroup K] [Module A K]

/-- `M` is the direct sum of `K`, embedded by `i` with retraction `r`, and the free line on `e`,
with coordinate `ℓ`. This holds for `K = LinearMap.ker ℓ` whenever `ℓ e = 1`, by
`isLineSplitting_ker`.

Blueprint: the splitting of `lem:dr-polynomial-splitting`, with `e = dz` and `ℓ = ∂_z`. -/
structure IsLineSplitting (e : M) (ℓ : Module.Dual A M) (i : K →ₗ[A] M) (r : M →ₗ[A] K) : Prop where
  /-- The line is free, with coordinate `ℓ`. -/
  apply_self : ℓ e = 1
  /-- `r` retracts `i`. -/
  retract_incl : ∀ k, r (i k) = k
  /-- The projection to `K` removes the coordinate along `e`. -/
  incl_retract : ∀ m, i (r m) = m - ℓ m • e

namespace IsLineSplitting

variable {e : M} {ℓ : Module.Dual A M} {i : K →ₗ[A] M} {r : M →ₗ[A] K}

theorem apply_incl (h : IsLineSplitting e ℓ i r) (k : K) : ℓ (i k) = 0 := by
  have h₁ := h.incl_retract (i k)
  rw [h.retract_incl, eq_comm, sub_eq_self] at h₁
  simpa [h.apply_self] using congrArg ℓ h₁

theorem retract_self (h : IsLineSplitting e ℓ i r) : r e = 0 := by
  have h₁ := h.incl_retract e
  rw [h.apply_self, one_smul, sub_self] at h₁
  rw [← h.retract_incl (r e), h₁, map_zero]

/-- The projection `i ∘ r` on exterior algebras is `x ↦ x - e ∧ ι_ℓ x`. -/
theorem map_incl_map_retract (h : IsLineSplitting e ℓ i r) (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.map i (ExteriorAlgebra.map r x) = x - ι A e * exteriorContraction ℓ x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb, mul_add]
    abel
  | ι_mul x m hx =>
    have hswap : ∀ c, ι A m * (ι A e * c) = -(ι A e * (ι A m * c)) := fun c => by
      rw [← mul_assoc, ← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m e),
        neg_mul]
    have hsq : ∀ c, ι A e * (ι A e * c) = 0 := fun c => by
      rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, hx, h.incl_retract, map_sub, map_smul,
      exteriorContraction_ι_mul, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hswap, hsq,
      smul_zero]
    abel

/-- Forms coming from `K` have zero contraction. -/
theorem exteriorContraction_map_incl (h : IsLineSplitting e ℓ i r) (y : ExteriorAlgebra A K) :
    exteriorContraction ℓ (ExteriorAlgebra.map i y) = 0 := by
  have hzero : ℓ ∘ₗ i = 0 := LinearMap.ext h.apply_incl
  have := exteriorMap_exteriorContraction A (g := i) (ℓ := ℓ ∘ₗ i) (ℓ' := ℓ) (fun _ => rfl) y
  rw [exteriorMap_self, hzero] at this
  simpa using this.symm

theorem map_retract_map_incl (h : IsLineSplitting e ℓ i r) (y : ExteriorAlgebra A K) :
    ExteriorAlgebra.map r (ExteriorAlgebra.map i y) = y := by
  have hid : r ∘ₗ i = LinearMap.id := LinearMap.ext h.retract_incl
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hid, ExteriorAlgebra.map_id]
  rfl

/-- Decomposing `x` as `α + e ∧ β` and recombining gives `x` back. -/
theorem map_incl_add_mul_map_incl (h : IsLineSplitting e ℓ i r) (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.map i (ExteriorAlgebra.map r x) +
        ι A e * ExteriorAlgebra.map i (ExteriorAlgebra.map r (exteriorContraction ℓ x)) = x := by
  simp only [h.map_incl_map_retract, exteriorContraction_exteriorContraction, mul_zero, sub_zero,
    sub_add_cancel]

/-- The component of `α + e ∧ β` along `K`, for `α` and `β` coming from `K`, is `α`. -/
theorem map_retract_add_mul (h : IsLineSplitting e ℓ i r) (a b : ExteriorAlgebra A K) :
    ExteriorAlgebra.map r (ExteriorAlgebra.map i a + ι A e * ExteriorAlgebra.map i b) = a := by
  simp [h.map_retract_map_incl, h.retract_self]

/-- The component of `α + e ∧ β` along `e`, for `α` and `β` coming from `K`, is `β`. -/
theorem map_retract_exteriorContraction_add_mul (h : IsLineSplitting e ℓ i r)
    (a b : ExteriorAlgebra A K) :
    ExteriorAlgebra.map r
        (exteriorContraction ℓ (ExteriorAlgebra.map i a + ι A e * ExteriorAlgebra.map i b)) =
      b := by
  simp [h.exteriorContraction_map_incl, h.apply_self, h.map_retract_map_incl]

/-- The decomposition of the exterior algebra of `M = K ⊕ A e`: every `x` is uniquely `α + e ∧ β`
with `α` and `β` coming from `K`, namely `β = r (ι_ℓ x)` and `α = r x`. -/
noncomputable def exteriorEquiv (h : IsLineSplitting e ℓ i r) :
    ExteriorAlgebra A M ≃ₗ[A] ExteriorAlgebra A K × ExteriorAlgebra A K where
  toFun x := (ExteriorAlgebra.map r x, ExteriorAlgebra.map r (exteriorContraction ℓ x))
  map_add' x y := by simp
  map_smul' a x := by simp
  invFun p := ExteriorAlgebra.map i p.1 + ι A e * ExteriorAlgebra.map i p.2
  left_inv := h.map_incl_add_mul_map_incl
  right_inv p := Prod.ext (h.map_retract_add_mul p.1 p.2)
    (h.map_retract_exteriorContraction_add_mul p.1 p.2)

/-- The decomposition `⋀^(n+1) M ≃ ⋀^(n+1) K × ⋀^n K` for `M = K ⊕ A e`, sending `α + e ∧ β` to the
pair `(α, β)`.

Blueprint: the decomposition in `lem:dr-polynomial-splitting`. -/
noncomputable def powerEquiv (h : IsLineSplitting e ℓ i r) (n : ℕ) :
    ⋀[A]^(n + 1) M ≃ₗ[A] ⋀[A]^(n + 1) K × ⋀[A]^n K where
  toFun x := (exteriorPower.map (n + 1) r x, exteriorPower.map n r (powerContraction ℓ n x))
  map_add' x y := by simp
  map_smul' a x := by simp
  invFun p := exteriorPower.map (n + 1) i p.1 + wedgeLeft e n (exteriorPower.map n i p.2)
  left_inv x := Subtype.ext (by simpa using h.map_incl_add_mul_map_incl x)
  right_inv p := Prod.ext (Subtype.ext (by simpa using h.map_retract_add_mul p.1 p.2))
    (Subtype.ext (by simpa using h.map_retract_exteriorContraction_add_mul p.1 p.2))

@[simp]
theorem powerEquiv_apply (h : IsLineSplitting e ℓ i r) (n : ℕ) (x : ⋀[A]^(n + 1) M) :
    h.powerEquiv n x =
      (exteriorPower.map (n + 1) r x, exteriorPower.map n r (powerContraction ℓ n x)) :=
  rfl

@[simp]
theorem powerEquiv_symm_apply (h : IsLineSplitting e ℓ i r) (n : ℕ)
    (p : ⋀[A]^(n + 1) K × ⋀[A]^n K) :
    (h.powerEquiv n).symm p =
      exteriorPower.map (n + 1) i p.1 + wedgeLeft e n (exteriorPower.map n i p.2) :=
  rfl

end IsLineSplitting

/-- The retraction `m ↦ m - ℓ m • e` onto the kernel of `ℓ`, when `ℓ e = 1`. -/
noncomputable def kerRetraction {e : M} {ℓ : Module.Dual A M} (he : ℓ e = 1) :
    M →ₗ[A] LinearMap.ker ℓ :=
  (LinearMap.id - ℓ.smulRight e).codRestrict _ fun m => by
    simp [he]

@[simp]
theorem coe_kerRetraction {e : M} {ℓ : Module.Dual A M} (he : ℓ e = 1) (m : M) :
    (kerRetraction he m : M) = m - ℓ m • e :=
  rfl

/-- A functional taking `e` to `1` splits off the line on `e`, with complement its kernel. -/
theorem isLineSplitting_ker {e : M} {ℓ : Module.Dual A M} (he : ℓ e = 1) :
    IsLineSplitting e ℓ (LinearMap.ker ℓ).subtype (kerRetraction he) where
  apply_self := he
  retract_incl k := Subtype.ext (by simp [LinearMap.mem_ker.1 k.2])
  incl_retract m := by simp

end LineSplitting
end OrlikSolomon.DeRham
