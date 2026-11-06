/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Algebra.ExteriorWords
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The signed boundary on an exterior algebra

Contraction with the linear form sending every standard basis vector to `1` computes the signed
boundary of words. It squares to zero, lowers exterior degree by one, and satisfies the signed
Leibniz rule. All results hold over arbitrary commutative rings, including characteristic two.
The contraction and its basic operator lemmas were extracted from `Algebra/ExteriorWords`.

Blueprint: the exterior-algebra operator of `lem:central-boundary`.
-/

@[expose] public section

namespace OrlikSolomon

variable (B : Type*) [CommRing B] {I : Type*}

/-! ### The boundary operator -/

/-- The linear operator on the exterior algebra sending each word to its signed boundary: it is
contraction with the linear form sending every standard basis vector to `1`. It is a graded
antiderivation of degree `-1` with square zero, and not a derivation in the sense of Mathlib.

Blueprint: the operator of `lem:central-boundary`, before passing to the quotient. -/
noncomputable def exteriorBoundary :
    ExteriorAlgebra B (I →₀ B) →ₗ[B] ExteriorAlgebra B (I →₀ B) :=
  CliffordAlgebra.contractLeft (Finsupp.linearCombination B fun _ => (1 : B))

@[simp]
theorem exteriorBoundary_one : exteriorBoundary B (1 : ExteriorAlgebra B (I →₀ B)) = 0 :=
  CliffordAlgebra.contractLeft_one _ _

/-- The boundary on a product with a standard generator on the left. -/
@[simp]
theorem exteriorBoundary_exteriorGen_mul (i : I) (y : ExteriorAlgebra B (I →₀ B)) :
    exteriorBoundary B (exteriorGen B i * y) = y - exteriorGen B i * exteriorBoundary B y := by
  simp [exteriorBoundary, exteriorGen, CliffordAlgebra.contractLeft_ι_mul]

@[simp]
theorem exteriorBoundary_exteriorGen (i : I) : exteriorBoundary B (exteriorGen B i) = 1 := by
  simpa using exteriorBoundary_exteriorGen_mul B i 1

/-- The boundary operator squares to zero.

Blueprint: `lem:central-boundary`. -/
@[simp]
theorem exteriorBoundary_exteriorBoundary (y : ExteriorAlgebra B (I →₀ B)) :
    exteriorBoundary B (exteriorBoundary B y) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

/-- The boundary operator computes the signed boundary of words. -/
@[simp]
theorem exteriorBoundary_word (l : List I) :
    exteriorBoundary B (word (exteriorGen B) l) = wordBoundary (exteriorGen B) l := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- The signed Leibniz rule for the boundary operator, for a word on the left.

Blueprint: `lem:central-boundary`. -/
theorem exteriorBoundary_word_mul (l : List I) (y : ExteriorAlgebra B (I →₀ B)) :
    exteriorBoundary B (word (exteriorGen B) l * y) =
      wordBoundary (exteriorGen B) l * y +
        (l.length : ℤ).negOnePow • (word (exteriorGen B) l * exteriorBoundary B y) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [word_cons, wordBoundary_cons, mul_assoc, exteriorBoundary_exteriorGen_mul, ih,
      mul_add, sub_mul, List.length_cons, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ,
      Units.neg_smul, mul_smul_comm]
    abel

/-- The boundary satisfies the signed Leibniz rule when the left factor has exterior degree `n`.
The right factor need not be homogeneous. Blueprint: `lem:central-boundary`. -/
theorem exteriorBoundary_mul_of_mem_exteriorPower {n : ℕ}
    {x : ExteriorAlgebra B (I →₀ B)} (hx : x ∈ ⋀[B]^n (I →₀ B))
    (y : ExteriorAlgebra B (I →₀ B)) :
    exteriorBoundary B (x * y) = exteriorBoundary B x * y +
      (n : ℤ).negOnePow • (x * exteriorBoundary B y) := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    simpa only [hl, exteriorBoundary_word] using exteriorBoundary_word_mul B l y
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [add_mul, map_add, hx, hz, smul_add]
    abel
  | smul b x _ hx =>
    simp only [smul_mul_assoc, map_smul, hx, smul_add]
    rw [smul_comm]

/-- The boundary lowers a positive exterior degree by one. -/
theorem exteriorBoundary_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra B (I →₀ B)}
    (hx : x ∈ ⋀[B]^(n + 1) (I →₀ B)) : exteriorBoundary B x ∈ ⋀[B]^n (I →₀ B) := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    simpa only [exteriorBoundary_word, hl, Nat.add_sub_cancel] using
      wordBoundary_mem_exteriorPower B l
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul b x _ hx => simpa only [map_smul] using Submodule.smul_mem _ b hx

/-- The boundary vanishes in exterior degree zero. -/
theorem exteriorBoundary_eq_zero_of_mem_exteriorPower_zero {x : ExteriorAlgebra B (I →₀ B)}
    (hx : x ∈ ⋀[B]^0 (I →₀ B)) : exteriorBoundary B x = 0 := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have : l = [] := List.length_eq_zero_iff.1 hl
    simp [this]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul b x _ hx => simp only [map_smul, hx, smul_zero]

/-- A permutation of the letters multiplies the boundary of a word in the standard generators by
its sign. -/
theorem wordBoundary_exteriorGen_ofFn_comp_perm {n : ℕ} (v : Fin n → I) (σ : Equiv.Perm (Fin n)) :
    wordBoundary (exteriorGen B) (List.ofFn (v ∘ σ)) =
      Equiv.Perm.sign σ • wordBoundary (exteriorGen B) (List.ofFn v) := by
  rw [← exteriorBoundary_word, word_exteriorGen_ofFn_comp_perm, Units.smul_def, map_zsmul,
    exteriorBoundary_word, Units.smul_def]


namespace IsExteriorFamily

variable {T : Type*} [Ring T] {x : I → T}

/-- A permutation of the letters multiplies the boundary of a word by the sign of the permutation.
-/
theorem wordBoundary_ofFn_comp_perm (hx : IsExteriorFamily x) {n : ℕ} (v : Fin n → I)
    (σ : Equiv.Perm (Fin n)) :
    wordBoundary x (List.ofFn (v ∘ σ)) = Equiv.Perm.sign σ • wordBoundary x (List.ofFn v) := by
  have h := congrArg (exteriorLift ℤ ⟨x, hx⟩) (wordBoundary_exteriorGen_ofFn_comp_perm ℤ v σ)
  simpa [Units.smul_def] using h

/-- The boundary of a word with a repeated letter is zero. -/
theorem wordBoundary_eq_zero_of_not_nodup (hx : IsExteriorFamily x) {l : List I} (h : ¬l.Nodup) :
    wordBoundary x l = 0 := by
  have h' := congrArg (exteriorLift ℤ ⟨x, hx⟩ ∘ exteriorBoundary ℤ)
    ((isExteriorFamily_exteriorGen ℤ).word_eq_zero_of_not_nodup h)
  simpa using h'


end IsExteriorFamily

end OrlikSolomon
