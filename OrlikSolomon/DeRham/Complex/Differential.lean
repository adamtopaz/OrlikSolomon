/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import OrlikSolomon.DeRham.Complex.Forms

/-!
# The de Rham differential

This file constructs the differential `d` on the forms of an arbitrary commutative `k`-algebra `A`.
It is `k`-linear and not `A`-linear, and it is characterized by
`d (a₀ da₁ ∧ ⋯ ∧ daₙ) = da₀ ∧ da₁ ∧ ⋯ ∧ daₙ`.

## Main definitions

* `OrlikSolomon.DeRham.d k`: the differential, as a `k`-linear operator on the total algebra of
  forms. Its definition is hidden, and everything about it follows from `d_smul_word`.
* `OrlikSolomon.DeRham.powerD k A n`: the differential in degree `n`, between the typed pieces.

## Main results

Blueprint `thm:dr-dga`:

* `OrlikSolomon.DeRham.d_smul_word`: the formula on words, the characterization of `d`.
* `OrlikSolomon.DeRham.d_d`: `d² = 0`.
* `OrlikSolomon.DeRham.d_mul_of_mem_exteriorPower`: the signed Leibniz rule, with the degree of the
  left factor as a hypothesis, and `OrlikSolomon.DeRham.d_mul`, the same rule on all forms, with
  the grade involution in place of the sign.
* `OrlikSolomon.DeRham.d_mem_exteriorPower`: `d` raises the degree by one.
* `OrlikSolomon.DeRham.eq_d_of_smul_word` and `OrlikSolomon.DeRham.eq_d_of_leibniz`: uniqueness.

Graded commutativity is `OrlikSolomon.DeRham.mul_comm_of_mem_exteriorPower`, and associativity and
unitality are part of the ring structure of the exterior algebra.

## Implementation notes

This departs from the blueprint's proof of `def:dr-complex`, which constructs `d` on a polynomial
ring and descends it through a presentation. No presentation is needed. The statements of
`lem:dr-polynomial-dga` and `lem:dr-presentation` are theorems about the operator constructed here,
in `DeRham/Complex/Polynomial` and `DeRham/Complex/Presentation`.

The operator `d` is not `A`-linear, so `ExteriorAlgebra.lift` cannot produce it directly, as the
blueprint warns. It is `A`-linear for a different `A`-module structure. Let `σ` be the grade
involution, and let `OddDual` be the ring of pairs `x + ε u` of forms, for a formal odd variable `ε`
with `ε² = 0`, so that `(x + ε u) * (y + ε v) = x y + ε (σ x * v + u * y)`. The signed Leibniz rule
for `d` says exactly that `x ↦ x + ε d x` is a ring map. So we make `OddDual` into an `A`-algebra
through `a ↦ a + ε da`, whose image is central because `da` anticommutes with odd forms. Then
`a ↦ da`, a derivation into forms, is also a derivation into `OddDual` for this module structure, by
`da ∧ db + db ∧ da = 0`. The universal properties of Kähler differentials and of the exterior
algebra produce an `A`-algebra map `Forms k A → Dual`. Its first component is the identity, and `d`
is its second component. That map is `A`-linear only for the twisted structure, which is the
content of the blueprint's warning.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι)
open KaehlerDifferential (D)
open CliffordAlgebra (involute involute_ι)

universe u v

/-! ### The grade involution -/

section Involute

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- A generator of degree one moves past a form up to the grade involution. -/
theorem ι_mul_eq_involute_mul (m : M) (y : ExteriorAlgebra A M) :
    ι A m * y = involute y * ι A m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap a => simp [Algebra.commutes]
  | ι n =>
    rw [involute_ι, neg_mul]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m n)
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, map_mul, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

private theorem involute_word_ι (l : List M) :
    involute (word (ι A) l) = (l.length : ℤ).negOnePow • word (ι A) l := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [word_cons, map_mul, involute_ι, ih, neg_mul, mul_smul_comm, List.length_cons,
      Nat.cast_succ, Int.negOnePow_succ, Units.neg_smul]

/-- The grade involution is the sign `(-1)^p` on elements of degree `p`. -/
theorem involute_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^p M) :
    involute x = (p : ℤ).negOnePow • x := by
  induction hx using exteriorPower_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]
  | word l hl =>
    subst hl
    exact involute_word_ι l

end Involute

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-! ### The ring of odd dual numbers -/

/-- Forms, as a bimodule with the left action twisted by the grade involution: `x • u = σ x * u`. -/
private def Twist : Type v := Forms k A

private noncomputable instance : AddCommGroup (Twist k A) :=
  inferInstanceAs (AddCommGroup (Forms k A))

private noncomputable instance : Module (Forms k A) (Twist k A) :=
  @Module.compHom (Forms k A) (Forms k A) (Forms k A) _ _ _ _
    (involute : Forms k A →ₐ[A] Forms k A).toRingHom

private noncomputable instance : Module (Forms k A)ᵐᵒᵖ (Twist k A) :=
  inferInstanceAs (Module (Forms k A)ᵐᵒᵖ (Forms k A))

private noncomputable instance : Module k (Twist k A) :=
  inferInstanceAs (Module k (Forms k A))

private instance : SMulCommClass (Forms k A) (Forms k A)ᵐᵒᵖ (Twist k A) where
  smul_comm x y u := (mul_assoc (involute x : Forms k A) (id u : Forms k A) y.unop).symm

private theorem twist_smul_assoc (c : k) (x u : Forms k A) :
    involute (c • x) * u = c • (involute x * u) := by
  rw [← algebraMap_smul A c x, map_smul, smul_mul_assoc, algebraMap_smul]

private instance : IsScalarTower k (Forms k A) (Twist k A) where
  smul_assoc c x u := twist_smul_assoc k A c x u

private instance : IsScalarTower k (Forms k A)ᵐᵒᵖ (Twist k A) where
  smul_assoc c x u := by
    obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
    exact mul_smul_comm c (id u : Forms k A) x

/-- The ring of `x + ε u`, for forms `x` and `u` and an odd variable `ε` with `ε² = 0`. -/
private abbrev OddDual : Type v := TrivSqZeroExt (Forms k A) (Twist k A)

variable {k A}

namespace OddDual

private def mk (x u : Forms k A) : OddDual k A := (x, u)

private def fst (r : OddDual k A) : Forms k A := r.1

private def snd (r : OddDual k A) : Forms k A := r.2

private theorem ext {r s : OddDual k A} (h₁ : fst r = fst s) (h₂ : snd r = snd s) : r = s :=
  Prod.ext h₁ h₂

@[simp] private theorem fst_mk (x u : Forms k A) : fst (mk x u) = x := rfl
@[simp] private theorem snd_mk (x u : Forms k A) : snd (mk x u) = u := rfl
@[simp] private theorem fst_add (r s : OddDual k A) : fst (r + s) = fst r + fst s := rfl
@[simp] private theorem snd_add (r s : OddDual k A) : snd (r + s) = snd r + snd s := rfl
@[simp] private theorem fst_zero : fst (0 : OddDual k A) = 0 := rfl
@[simp] private theorem snd_zero : snd (0 : OddDual k A) = 0 := rfl
@[simp] private theorem fst_one : fst (1 : OddDual k A) = 1 := rfl
@[simp] private theorem snd_one : snd (1 : OddDual k A) = 0 := rfl
@[simp] private theorem fst_mul (r s : OddDual k A) : fst (r * s) = fst r * fst s := rfl
@[simp] private theorem snd_mul (r s : OddDual k A) :
    snd (r * s) = involute (fst r) * snd s + snd r * fst s := rfl
@[simp] private theorem fst_smul (c : k) (r : OddDual k A) : fst (c • r) = c • fst r := rfl
@[simp] private theorem snd_smul (c : k) (r : OddDual k A) : snd (c • r) = c • snd r := rfl

/-- The structure map `a ↦ a + ε da`. -/
private noncomputable def ofRing : A →+* OddDual k A where
  toFun a := mk (algebraMap A _ a) (diff k a)
  map_one' := ext (by simp) (by simp)
  map_zero' := ext (by simp) (by simp)
  map_add' a b := ext (by simp) (by simp)
  map_mul' a b := ext (by simp) (by
    simp only [snd_mul, fst_mk, snd_mk, AlgHom.commutes, Derivation.leibniz, Algebra.smul_def,
      ← Algebra.commutes (R := A) b (diff k a)])

@[simp] private theorem fst_ofRing (a : A) : fst (ofRing a : OddDual k A) = algebraMap A _ a := rfl
@[simp] private theorem snd_ofRing (a : A) : snd (ofRing a : OddDual k A) = diff k a := rfl

/-- The image of `a ↦ a + ε da` is central, because `da` anticommutes with odd forms. -/
private theorem ofRing_commutes (a : A) (r : OddDual k A) : ofRing a * r = r * ofRing a := by
  refine ext ?_ ?_
  · simp [Algebra.commutes]
  · simp only [snd_mul, fst_ofRing, snd_ofRing, AlgHom.commutes]
    rw [diff_apply, ι_mul_eq_involute_mul, add_comm, Algebra.commutes]

/-- The twisted `A`-algebra structure on `OddDual`, through `a ↦ a + ε da`. The other `A`-action,
on both components, is not an instance, because `Twist` has no `A`-module structure. -/
private noncomputable instance : Algebra A (OddDual k A) :=
  (ofRing).toAlgebra' ofRing_commutes

private theorem algebraMap_eq (a : A) : algebraMap A (OddDual k A) a = ofRing a := rfl

private theorem smul_eq (a : A) (r : OddDual k A) : a • r = ofRing a * r := Algebra.smul_def a r

private instance : IsScalarTower k A (OddDual k A) := by
  refine IsScalarTower.of_algebraMap_smul fun c r => ?_
  rw [smul_eq]
  refine ext ?_ ?_
  · rw [fst_mul, fst_ofRing, fst_smul, ← Algebra.smul_def, algebraMap_smul]
  · rw [snd_mul, fst_ofRing, snd_ofRing, snd_smul, AlgHom.commutes, Derivation.map_algebraMap,
      zero_mul, add_zero, ← Algebra.smul_def, algebraMap_smul]

/-- `a ↦ da`, as a derivation into `OddDual` with its twisted module structure. -/
private noncomputable def der : Derivation k A (OddDual k A) where
  toFun a := mk (diff k a) 0
  map_add' a b := ext (by simp) (by simp)
  map_smul' c a := ext (by simp) (by simp)
  map_one_eq_zero' := ext (by simp) (by simp)
  leibniz' a b := by
    rw [smul_eq, smul_eq]
    refine ext ?_ ?_
    · simp [Algebra.smul_def]
    · simp [diff_mul_add_mul_swap]

/-- The universal map `Ω[A⁄k] → Dual`, sending `a db` to `a db + ε da ∧ db`. -/
private noncomputable def lin : Ω[A⁄k] →ₗ[A] OddDual k A :=
  der.liftKaehlerDifferential

@[simp] private theorem lin_D (a : A) : lin (D k A a) = mk (diff k a) 0 :=
  der.liftKaehlerDifferential_comp_D a

/-- The first component of `lin` is the inclusion of degree one, and the second has degree two. -/
private theorem fst_lin_snd_lin (ω : Ω[A⁄k]) :
    fst (lin ω : OddDual k A) = ι A ω ∧ snd (lin ω : OddDual k A) ∈ ⋀[A]^2 Ω[A⁄k] := by
  have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    simp
  | zero => simp
  | add ω η _ _ hω hη =>
    simp only [map_add, fst_add, snd_add]
    exact ⟨by rw [hω.1, hη.1], add_mem hω.2 hη.2⟩
  | smul a ω _ hω =>
    rw [map_smul, smul_eq, fst_mul, snd_mul, fst_ofRing, snd_ofRing, hω.1, AlgHom.commutes,
      ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    exact ⟨rfl, add_mem (Submodule.smul_mem _ a hω.2) (diff_mul_mem_exteriorPower k a (by simp))⟩

private theorem lin_mul_self (ω : Ω[A⁄k]) : (lin ω : OddDual k A) * lin ω = 0 := by
  obtain ⟨h₁, h₂⟩ := fst_lin_snd_lin (k := k) ω
  refine ext ?_ ?_
  · simp [h₁]
  · have h₃ : ι A ω ∈ ⋀[A]^1 Ω[A⁄k] := by simp
    have h := mul_comm_of_mem_exteriorPower h₂ h₃
    have hs : (((2 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)).negOnePow = 1 := by
      rw [Int.negOnePow_even]
      decide
    rw [hs, one_smul] at h
    simp only [snd_mul, h₁, involute_ι, neg_mul, snd_zero, h]
    simp

/-- The `A`-algebra map `x ↦ x + ε d x`. Here `A` acts on `OddDual` through `a ↦ a + ε da`. -/
private noncomputable def hom : Forms k A →ₐ[A] OddDual k A :=
  ExteriorAlgebra.lift A ⟨lin, lin_mul_self⟩

@[simp] private theorem hom_ι (ω : Ω[A⁄k]) : (hom (ι A ω) : OddDual k A) = lin ω :=
  ExteriorAlgebra.lift_ι_apply A _ _ ω

@[simp] private theorem hom_algebraMap (a : A) :
    (hom (algebraMap A (Forms k A) a) : OddDual k A) = ofRing a :=
  AlgHom.commutes _ a

@[simp] private theorem fst_hom (x : Forms k A) : fst (hom x : OddDual k A) = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp [algebraMap_eq]
  | ι ω => simpa using (fst_lin_snd_lin (k := k) ω).1
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

end OddDual

open OddDual

/-! ### The differential -/

variable (k) in
/-- The de Rham differential on forms. It is `k`-linear and not `A`-linear, and it has degree one by
`d_mem_exteriorPower`. It is characterized by `d_smul_word`, which is its formula on the expressions
`a₀ da₁ ∧ ⋯ ∧ daₙ`, and by `eq_d_of_smul_word`, and its construction is hidden. See the
implementation notes of this file.

Blueprint: `def:dr-complex`. -/
@[no_expose]
noncomputable def d : Forms k A →ₗ[k] Forms k A where
  toFun x := snd (hom x : OddDual k A)
  map_add' x y := by simp
  map_smul' c x := by simp [AlgHom.map_smul_of_tower]

private theorem d_eq (x : Forms k A) : d k x = snd (hom x : OddDual k A) :=
  rfl

variable (k)

/-- The Leibniz rule on all forms, with the grade involution `σ`, which is the sign `(-1)^p` on
forms of degree `p`, by `involute_of_mem_exteriorPower`. Use `d_mul_of_mem_exteriorPower` for
homogeneous forms.

Blueprint: `thm:dr-dga`. -/
theorem d_mul (x y : Forms k A) : d k (x * y) = d k x * y + involute x * d k y := by
  simp only [d_eq, map_mul, snd_mul, fst_hom]
  rw [add_comm]

/-- The signed Leibniz rule: `d (x ∧ y) = dx ∧ y + (-1)^p x ∧ dy` for `x` of degree `p`. The degree
of `y` plays no role.

Blueprint: `thm:dr-dga`. -/
theorem d_mul_of_mem_exteriorPower {p : ℕ} {x : Forms k A} (hx : x ∈ ⋀[A]^p Ω[A⁄k])
    (y : Forms k A) : d k (x * y) = d k x * y + (p : ℤ).negOnePow • (x * d k y) := by
  rw [d_mul, involute_of_mem_exteriorPower hx, smul_mul_assoc]

@[simp]
theorem d_algebraMap (a : A) : d k (algebraMap A (Forms k A) a) = diff k a := by
  rw [d_eq, hom_algebraMap, snd_ofRing]

@[simp]
theorem d_one : d k (1 : Forms k A) = 0 := by
  rw [← map_one (algebraMap A (Forms k A)), d_algebraMap, Derivation.map_one_eq_zero]

/-- `d (da) = 0`. -/
@[simp]
theorem d_diff (a : A) : d k (diff k a) = 0 := by
  rw [d_eq, diff_apply, hom_ι, lin_D, snd_mk]

/-- The rule `d (a x) = da ∧ x + a dx`, a case of the Leibniz rule, showing how `d` fails to be
`A`-linear.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem d_smul (a : A) (x : Forms k A) : d k (a • x) = diff k a * x + a • d k x := by
  rw [Algebra.smul_def, d_mul, d_algebraMap, AlgHom.commutes, ← Algebra.smul_def]

/-- `d (a • 1) = da`. -/
theorem d_smul_one (a : A) : d k (a • (1 : Forms k A)) = diff k a := by
  rw [d_smul, d_one, smul_zero, mul_one, add_zero]

/-- `d (a db) = da ∧ db`. -/
theorem d_smul_diff (a b : A) : d k (a • diff k b) = diff k a * diff k b := by
  rw [d_smul, d_diff, smul_zero, add_zero]

/-- `d (da ∧ x) = -da ∧ dx`. -/
@[simp]
theorem d_diff_mul (a : A) (x : Forms k A) : d k (diff k a * x) = -(diff k a * d k x) := by
  rw [d_mul, d_diff, zero_mul, zero_add, diff_apply, involute_ι, neg_mul]

/-- `d (da₁ ∧ ⋯ ∧ daₙ) = 0`. -/
@[simp]
theorem d_word (l : List A) : d k (word (diff k) l) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, d_diff_mul, ih, mul_zero, neg_zero]

/-- The characterization of the differential:
`d (a₀ da₁ ∧ ⋯ ∧ daₙ) = da₀ ∧ da₁ ∧ ⋯ ∧ daₙ`.

Blueprint: `thm:dr-dga`. -/
theorem d_smul_word (a : A) (l : List A) :
    d k (a • word (diff k) l) = diff k a * word (diff k) l := by
  rw [d_smul, d_word, smul_zero, add_zero]

/-- `d² = 0`, on all forms and in every characteristic.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem d_d (x : Forms k A) : d k (d k x) = 0 := by
  induction x using Forms.induction with
  | word a l => rw [d_smul_word, d_diff_mul, d_word, mul_zero, neg_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- `d² = 0`, as an equation of `k`-linear maps. -/
@[simp]
theorem d_comp_d : d k ∘ₗ d k = (0 : Forms k A →ₗ[k] Forms k A) :=
  LinearMap.ext (d_d k)

/-- `d` raises the degree by one.

Blueprint: `thm:dr-dga`. -/
theorem d_mem_exteriorPower {n : ℕ} {x : Forms k A} (hx : x ∈ ⋀[A]^n Ω[A⁄k]) :
    d k x ∈ ⋀[A]^(n + 1) Ω[A⁄k] := by
  induction hx using Forms.induction_exteriorPower with
  | word a l hl =>
    rw [d_smul_word]
    exact diff_mul_mem_exteriorPower k a (hl ▸ word_diff_mem_exteriorPower k l)
  | add x _ y _ hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- `d` anticommutes with the grade involution. This is what makes the product of a closed form with
an exact form exact, on all forms:
`x * d y = d (σ x * y)` for `d x = 0`. -/
theorem d_involute (x : Forms k A) : d k (involute x) = -involute (d k x) := by
  induction x using Forms.induction with
  | word a l =>
    have hsign : ∀ (s : ℤˣ) (y : Forms k A), d k (s • y) = s • d k y := fun s y => by
      rcases Int.units_eq_one_or s with rfl | rfl <;> simp
    rw [map_smul, involute_of_mem_exteriorPower (word_diff_mem_exteriorPower k l), smul_comm, hsign,
      d_smul_word, involute_of_mem_exteriorPower
        (diff_mul_mem_exteriorPower k a (word_diff_mem_exteriorPower k l)),
      Nat.cast_succ, Int.negOnePow_succ, Units.neg_smul, neg_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

/-- The product of a closed form with an exact form is exact: `x ∧ dy = d (σ x ∧ y)`. -/
theorem mul_d_of_d_eq_zero {x : Forms k A} (hx : d k x = 0) (y : Forms k A) :
    x * d k y = d k (involute x * y) := by
  rw [d_mul, d_involute, hx, map_zero, neg_zero, zero_mul, zero_add,
    CliffordAlgebra.involute_involute]

/-! ### Uniqueness -/

/-- The differential is the only additive operator with the formula of `d_smul_word`, so it depends
on nothing but that formula.

Blueprint: `thm:dr-dga`, the last sentence of its proof. -/
theorem eq_d_of_smul_word (f : Forms k A →+ Forms k A)
    (hf : ∀ (a : A) (l : List A), f (a • word (diff k) l) = diff k a * word (diff k) l)
    (x : Forms k A) : f x = d k x := by
  induction x using Forms.induction with
  | word a l => rw [hf, d_smul_word]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The differential is the only additive operator that extends `a ↦ da`, squares to zero and
satisfies the signed Leibniz rule.

Blueprint: `thm:dr-dga`, the last sentence of its proof. -/
theorem eq_d_of_leibniz (f : Forms k A →+ Forms k A)
    (h₀ : ∀ a : A, f (algebraMap A (Forms k A) a) = diff k a)
    (h₂ : ∀ x, f (f x) = 0)
    (hmul : ∀ (p : ℕ) (x y : Forms k A), x ∈ ⋀[A]^p Ω[A⁄k] →
      f (x * y) = f x * y + (p : ℤ).negOnePow • (x * f y))
    (x : Forms k A) : f x = d k x := by
  have hdiff (a : A) : f (diff k a) = 0 := by rw [← h₀, h₂]
  have hword (l : List A) : f (word (diff k) l) = 0 := by
    induction l with
    | nil =>
      have h := hmul 0 1 1 (by simp)
      simpa using h
    | cons a l ih =>
      rw [word_cons, hmul 1 _ _ (diff_mem_exteriorPower_one k a), hdiff, ih]
      simp
  refine eq_d_of_smul_word k f (fun a l => ?_) x
  rw [Algebra.smul_def, hmul 0 _ _ (algebraMap_mem_exteriorPower_zero k a), h₀, hword]
  simp

/-! ### The differential in each degree -/

variable (A) in
/-- The differential in degree `n`, as a `k`-linear map `⋀^n Ω → ⋀^(n+1) Ω`. This is `d` with its
domain and codomain restricted, by `coe_powerD`. Use it where a complex needs types indexed by
degree, and `d` otherwise.

Blueprint: `def:dr-complex`. -/
noncomputable def powerD (n : ℕ) : ⋀[A]^n Ω[A⁄k] →ₗ[k] ⋀[A]^(n + 1) Ω[A⁄k] :=
  LinearMap.codRestrict ((⋀[A]^(n + 1) Ω[A⁄k]).restrictScalars k)
    ((d k).comp ((⋀[A]^n Ω[A⁄k]).subtype.restrictScalars k))
    fun x => d_mem_exteriorPower k x.2

@[simp]
theorem coe_powerD (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    (powerD k A n x : Forms k A) = d k (x : Forms k A) :=
  rfl

@[simp]
theorem powerD_powerD (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) : powerD k A (n + 1) (powerD k A n x) = 0 :=
  Subtype.ext (d_d k _)

@[simp]
theorem powerD_comp_powerD (n : ℕ) : powerD k A (n + 1) ∘ₗ powerD k A n = 0 :=
  LinearMap.ext (powerD_powerD k n)

end OrlikSolomon.DeRham
