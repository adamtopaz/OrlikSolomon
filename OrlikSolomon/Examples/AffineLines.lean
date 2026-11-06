/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Examples.Cokernel
public import OrlikSolomon.Examples.Parallel
public import OrlikSolomon.Examples.Polynomials
public import OrlikSolomon.Presentation.Grading
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The affine triangle regression

The three lines `x = 0`, `y = 0` and `x + y = 1` have empty triple intersection.
Their triple product vanishes, while `triangle_boundary_ne` proves that the degree-two boundary
does not vanish over any nonzero coefficient ring. A concrete exterior-algebra matrix model
detects this boundary, including in characteristic two. `triangle_not_comm` also detects the
ordinary noncommutativity over the integers. The same concrete triangle has polynomial
`1 + 3 X + 3 X²`, whereas the three concurrent lines from `Examples/Cokernel` have polynomial
`1 + 3 X + 2 X²` and satisfy the standard degree-two boundary relation.

## Main results

* `triangle_triple`: the empty triple intersection kills the triple product.
* `triangle_boundary_ne`: the triple boundary is nonzero over every nonzero coefficient ring.
* `triangle_not_comm`: the algebra is not ordinarily commutative over the integers.
* `poincarePolynomial_triangle` and `poincarePolynomial_threeConcurrent`: the two polynomials.
* `threeConcurrent_boundary`: the guarded dependence relation for the concurrent arrangement.

These regressions adapt Claude's independent review consumer for PR #45. Their statements
test the empty-intersection guard and do not use the cohomology structure theorem.

Blueprint: item 6 of "Required mathematical regression examples".
-/

@[expose] public section

noncomputable section

open Module OrlikSolomon OSAlgebra Arrangement

universe u v

namespace OrlikSolomon.AffineLineExamples

variable {k : Type u} [Field k]

/-- The line `f = c` in the affine plane. -/
private def line (f : (k × k) →ₗ[k] k) (c : k) : AffineSubspace k (k × k) :=
  zeroLocus (f.toAffineMap - AffineMap.const k (k × k) c)

@[simp] private theorem mem_line (f : (k × k) →ₗ[k] k) (c : k) (p : k × k) :
    p ∈ line f c ↔ f p = c := by
  simp [line, sub_eq_zero, mem_zeroLocus]

private abbrev fX : (k × k) →ₗ[k] k := LinearMap.fst k k k
private abbrev fY : (k × k) →ₗ[k] k := LinearMap.snd k k k

private theorem isHyperplane_line {f : (k × k) →ₗ[k] k} (hf : f ≠ 0) (c : k) :
    IsHyperplane (line f c) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  apply hf
  refine LinearMap.ext fun p ↦ ?_
  simpa using congrArg (fun g : (k × k) →ₗ[k] k ↦ g p) h

private theorem fX_ne : (fX : (k × k) →ₗ[k] k) ≠ 0 := fun h ↦ by
  simpa using congrArg (fun g : (k × k) →ₗ[k] k ↦ g (1, 0)) h
private theorem fY_ne : (fY : (k × k) →ₗ[k] k) ≠ 0 := fun h ↦ by
  simpa using congrArg (fun g : (k × k) →ₗ[k] k ↦ g (0, 1)) h
private theorem fXY_ne : ((fX + fY : (k × k) →ₗ[k] k)) ≠ 0 := fun h ↦ by
  simpa using congrArg (fun g : (k × k) →ₗ[k] k ↦ g (1, 0)) h

private theorem finrank_plane : Module.finrank k (k × k) = 2 := by simp

/-! ### Triangle `x = 0`, `y = 0`, `x + y = 1` -/

/-- The three pairwise meeting lines `x = 0`, `y = 0` and `x + y = 1`. -/
@[no_expose]
def triangle (k : Type u) [Field k] : Arrangement k (k × k) := by
  classical
  exact ofFinset {line fX 0, line fY 0, line (fX + fY) 1}

private theorem mem_triangle {H : AffineSubspace k (k × k)} :
    H ∈ triangle k ↔ H = line fX 0 ∨ H = line fY 0 ∨ H = line (fX + fY) 1 := by
  classical
  simp only [triangle, mem_ofFinset, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  rcases h with rfl | rfl | rfl
  · exact isHyperplane_line fX_ne 0
  · exact isHyperplane_line fY_ne 0
  · exact isHyperplane_line fXY_ne 1

/-- The line `x = 0` as a label of the triangle. -/
@[no_expose]
def t1 : triangle k := ⟨line fX 0, mem_triangle.2 (by simp)⟩

/-- The line `y = 0` as a label of the triangle. -/
@[no_expose]
def t2 : triangle k := ⟨line fY 0, mem_triangle.2 (by simp)⟩

/-- The line `x + y = 1` as a label of the triangle. -/
@[no_expose]
def t3 : triangle k := ⟨line (fX + fY) 1, mem_triangle.2 (by simp)⟩

private theorem t_cases (H : triangle k) : H = t1 ∨ H = t2 ∨ H = t3 := by
  rcases mem_triangle.1 H.2 with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

private theorem t1_ne_t2 : (t1 : triangle k) ≠ t2 := fun h ↦ by
  have : ((0 : k), (1 : k)) ∈ ((t1 : triangle k) : AffineSubspace k (k × k)) := by simp [t1]
  rw [h] at this; simp [t2] at this
private theorem t1_ne_t3 : (t1 : triangle k) ≠ t3 := fun h ↦ by
  have : ((0 : k), (0 : k)) ∈ ((t1 : triangle k) : AffineSubspace k (k × k)) := by simp [t1]
  rw [h] at this; simp [t3] at this
private theorem t2_ne_t3 : (t2 : triangle k) ≠ t3 := fun h ↦ by
  have : ((0 : k), (0 : k)) ∈ ((t2 : triangle k) : AffineSubspace k (k × k)) := by simp [t2]
  rw [h] at this; simp [t3] at this

/-- The three lines of the triangle have no common point. -/
theorem triangle_inter_triple : inter [t1 (k := k), t2, t3] = ⊥ := by
  ext p
  simp only [mem_inter, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    t1, t2, t3, mem_line]
  constructor
  · rintro ⟨h1, h2, h3⟩
    simp only [LinearMap.add_apply, h1, h2] at h3
    simp at h3
  · intro h
    exact False.elim (AffineSubspace.notMem_bot k _ _ h)

/-- The triangle has Poincaré polynomial `1 + 3 X + 3 X²`, in contrast to three
concurrent lines. Every pair meets, but the triple intersection is empty. -/
theorem poincarePolynomial_triangle :
    (triangle k).poincarePolynomial = 1 + 3 * Polynomial.X + 3 * Polynomial.X ^ 2 := by
  classical
  apply Examples.poincarePolynomial_three_nonconcurrent (triangle k)
    (H := (t1 : triangle k)) (K := (t2 : triangle k)) (L := (t3 : triangle k))
  · ext H
    simp only [Arrangement.mem_hyperplanes, mem_triangle, Finset.mem_insert,
      Finset.mem_singleton, t1, t2, t3]
  · exact fun h ↦ t1_ne_t2 (Subtype.ext h)
  · exact fun h ↦ t1_ne_t3 (Subtype.ext h)
  · exact fun h ↦ t2_ne_t3 (Subtype.ext h)
  · exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨(0, 0), by simp [t1, t2]⟩
  · exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨(0, 1), by simp [t1, t3]⟩
  · exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨(1, 0), by simp [t2, t3]⟩
  · simpa only [inter_cons, inter_nil, inf_top_eq] using triangle_inter_triple (k := k)

/-- The blueprint's empty relation for the triangle. -/
theorem triangle_triple (B : Type v) [CommRing B] :
    generator B (triangle k) t1 * generator B _ t2 * generator B _ t3 = 0 := by
  have := word_eq_zero_of_inter_eq_bot B (triangle k) (triangle_inter_triple (k := k))
  simpa [word_cons, mul_assoc] using this

/-- If a nodup list has nonempty intersection, then it has at most two letters. -/
private theorem triangle_length_le {I : List (triangle k)} (hI : I.Nodup) (h : inter I ≠ ⊥) :
    I.length ≤ 2 := by
  match I, hI, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | [_, _], _, _ => simp
  | a :: b :: c :: l, hI, h =>
    exfalso
    apply h
    have hsub : ∀ x ∈ [t1 (k := k), t2, t3], x ∈ a :: b :: c :: l := by
      have hab : a ≠ b := by simp only [List.nodup_cons, List.mem_cons] at hI; tauto
      have hac : a ≠ c := by simp only [List.nodup_cons, List.mem_cons] at hI; tauto
      have hbc : b ≠ c := by simp only [List.nodup_cons, List.mem_cons] at hI; tauto
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons]
      rcases t_cases a with rfl | rfl | rfl <;> rcases t_cases b with rfl | rfl | rfl <;>
        rcases t_cases c with rfl | rfl | rfl <;> simp_all <;> tauto
    refine le_antisymm ?_ bot_le
    rw [← triangle_inter_triple (k := k)]
    intro p hp
    rw [mem_inter] at hp ⊢
    exact fun H hH ↦ hp H (hsub H hH)

/-- No list of distinct lines of the triangle has a guarded dependence relation. -/
theorem triangle_not_dependent {I : List (triangle k)} (hI : I.Nodup) : ¬ IsDependent I := by
  rintro ⟨hne, hlt⟩
  have hle := triangle_length_le hI hne
  match I, hI, hne, hlt, hle with
  | [], _, _, h, _ => simp at h
  | [H], _, _, h, _ =>
    have h1 := ((triangle k).isHyperplane H.2).codim_eq_one
    simp [h1] at h
  | [H, K], hI, hne, h, _ =>
    have hHK : H ≠ K := by simpa using hI
    have hne' : (H : AffineSubspace k (k × k)) ⊓ K ≠ ⊥ := by simpa using hne
    have h2 := ((triangle k).isHyperplane H.2).codim_inf_eq_two ((triangle k).isHyperplane K.2)
      (fun e ↦ hHK (Subtype.ext e.symm)) hne'
    simp [h2] at h
  | _ :: _ :: _ :: _, _, _, _, h => simp at h

/-! A matrix model of `Λ(a, b)`, valid over any commutative ring. -/
section Model
variable (B : Type v) [CommRing B]
private def mA : Matrix (Fin 4) (Fin 4) B := !![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0]
private def mB : Matrix (Fin 4) (Fin 4) B := !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,-1,0,0]

private theorem mA_sq : mA B * mA B = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mA, Matrix.mul_apply, Fin.sum_univ_four]
private theorem mB_sq : mB B * mB B = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mB, Matrix.mul_apply, Fin.sum_univ_four]
private theorem mA_mB : mA B * mB B + mB B * mA B = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mA, mB]
private theorem mA_mB_ne [Nontrivial B] : mA B * mB B ≠ 0 := fun h ↦ by
  have := congrFun (congrFun h 3) 0
  simp [mA, mB] at this
end Model

/-- The family `e₁ ↦ a`, `e₂ ↦ b`, `e₃ ↦ 0`. -/
private def triFam (B : Type v) [CommRing B] (H : triangle k) : Matrix (Fin 4) (Fin 4) B := by
  classical
  exact if H = t1 then mA B else if H = t2 then mB B else 0

@[simp] private theorem triFam_t1 (B : Type v) [CommRing B] : triFam (k := k) B t1 = mA B := by
  simp [triFam]
@[simp] private theorem triFam_t2 (B : Type v) [CommRing B] : triFam (k := k) B t2 = mB B := by
  simp [triFam, t1_ne_t2.symm]
@[simp] private theorem triFam_t3 (B : Type v) [CommRing B] : triFam (k := k) B t3 = 0 := by
  simp [triFam, t1_ne_t3.symm, t2_ne_t3.symm]

private theorem triFam_isFamily (B : Type v) [CommRing B] :
    IsFamily (triangle k) (triFam (k := k) B) where
  mul_self H := by
    rcases t_cases H with rfl | rfl | rfl <;> simp [mA_sq, mB_sq]
  mul_add_mul_swap_of_ne {H K} _ := by
    have h := mA_mB B
    rcases t_cases H with rfl | rfl | rfl <;> rcases t_cases K with rfl | rfl | rfl <;>
      simp_all [add_comm]
  word_eq_zero I hnd hI := by
    -- an empty list intersection forces `t3 ∈ I`, as `(0, 0)` lies on the other two lines
    have ht3 : t3 ∈ I := by
      by_contra h3
      have : (0 : k × k) ∈ inter I := by
        rw [mem_inter]
        intro H hH
        rcases t_cases H with rfl | rfl | rfl
        · simp [t1]
        · simp [t2]
        · exact (h3 hH).elim
      rw [hI] at this
      exact AffineSubspace.notMem_bot k _ _ this
    clear hI hnd
    induction I with
    | nil => simp at ht3
    | cons H I ih =>
      rw [word_cons]
      rcases List.mem_cons.1 ht3 with rfl | h
      · simp
      · rw [ih h, mul_zero]
  wordBoundary_eq_zero _ hI hd := (triangle_not_dependent hI hd).elim

/-- **There is no degree-two boundary relation for the triangle.** -/
theorem triangle_boundary_ne (B : Type v) [CommRing B] [Nontrivial B] :
    generator B (triangle k) t2 * generator B _ t3
      - generator B _ t1 * generator B _ t3
      + generator B _ t1 * generator B _ t2 ≠ 0 := by
  intro h
  have h' := congrArg (lift (B := B) (triFam (k := k) B) (triFam_isFamily B)) h
  simp only [map_add, map_sub, map_mul, lift_generator, triFam_t1, triFam_t2, triFam_t3, mul_zero,
    sub_zero, zero_add, map_zero] at h'
  exact mA_mB_ne B h'

/-- The triple boundary would be forced to vanish without the guard, since `codim ⊥ = 2`. -/
theorem triangle_unguarded :
    codim (inter [t1 (k := k), t2, t3]) < [t1 (k := k), t2, t3].length := by
  rw [triangle_inter_triple, codim_bot, finrank_plane]; simp

/-! ### `Ring`, not `CommRing`: over `ℤ` the algebra really is noncommutative -/
/-- The triangle algebra over the integers is not ordinarily commutative. -/
theorem triangle_not_comm :
    generator ℤ (triangle k) t1 * generator ℤ _ t2 ≠ generator ℤ _ t2 * generator ℤ _ t1 := by
  intro h
  have h' := congrArg (lift (B := ℤ) (triFam (k := k) ℤ) (triFam_isFamily ℤ)) h
  simp only [map_mul, lift_generator, triFam_t1, triFam_t2] at h'
  have := congrFun (congrFun h' 3) 0
  simp [mA, mB, Matrix.mul_apply, Fin.sum_univ_four] at this

/-- Over `ℤ/2` the same two generators do commute, which is why the box says "in general". -/
example : generator (ZMod 2) (triangle k) t1 * generator _ _ t2 =
    generator (ZMod 2) (triangle k) t2 * generator _ _ t1 := by
  have h := (isExteriorFamily_generator (ZMod 2) (triangle k)).mul_add_mul_swap t1 t2
  have h2 : ∀ x : OSAlgebra (ZMod 2) (triangle k), x + x = 0 := fun x ↦ by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have h3 := h2 (generator (ZMod 2) (triangle k) t2 * generator _ _ t1)
  exact add_right_cancel (h.trans h3.symm)
/-! ### Three concurrent lines -/

/-- Three concurrent lines have polynomial `1 + 3 X + 2 X²`: the two old traces on the
chosen line coincide and must be counted only once. -/
theorem poincarePolynomial_threeConcurrent :
    (PresentationExamples.threeConcurrent k).poincarePolynomial =
      1 + 3 * Polynomial.X + 2 * Polynomial.X ^ 2 := by
  classical
  open PresentationExamples in
    apply Examples.poincarePolynomial_three_same_trace (threeConcurrent k)
      (H := verticalLine 0) (K := horizontalZero k) (L := diagonalZero k)
  · ext H
    simp only [Arrangement.mem_hyperplanes, PresentationExamples.mem_threeConcurrent,
      Finset.mem_insert, Finset.mem_singleton]
  · intro h
    have := congrArg (fun L : AffineSubspace k (k × k) ↦ ((0 : k), 1) ∈ L) h
    simp at this
  · intro h
    have := congrArg (fun L : AffineSubspace k (k × k) ↦ ((0 : k), 1) ∈ L) h
    simp at this
  · intro h
    have := congrArg (fun L : AffineSubspace k (k × k) ↦ ((1 : k), 0) ∈ L) h
    simp at this
  · ext p
    simp only [AffineSubspace.mem_inf_iff, PresentationExamples.mem_verticalLine,
      PresentationExamples.mem_horizontalZero, PresentationExamples.mem_diagonalZero]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, hx.trans hy.symm⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, hxy ▸ hx⟩
  · exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨(0, 0), by simp⟩

/-- The guarded dependence relation for three concurrent lines, with its usual alternating
signs. It holds over every commutative coefficient ring, including characteristic two and
the zero ring. -/
theorem threeConcurrent_boundary (B : Type v) [CommRing B] :
    let 𝒜 := PresentationExamples.threeConcurrent k
    let H := PresentationExamples.concurrentBase k
    let K := Arrangement.inclusion (𝒜.deletion_le H)
      (PresentationExamples.concurrentHorizontal k)
    let L := Arrangement.inclusion (𝒜.deletion_le H)
      (PresentationExamples.concurrentDiagonal k)
    generator B 𝒜 K * generator B 𝒜 L - generator B 𝒜 H * generator B 𝒜 L +
      generator B 𝒜 H * generator B 𝒜 K = 0 := by
  dsimp only
  let I : List (PresentationExamples.threeConcurrent k) :=
    [PresentationExamples.concurrentBase k,
      Arrangement.inclusion ((PresentationExamples.threeConcurrent k).deletion_le _)
        (PresentationExamples.concurrentHorizontal k),
      Arrangement.inclusion ((PresentationExamples.threeConcurrent k).deletion_le _)
        (PresentationExamples.concurrentDiagonal k)]
  have hdep : Arrangement.IsDependent I := by
    constructor
    · apply (AffineSubspace.nonempty_iff_ne_bot _).1
      refine ⟨0, ?_⟩
      simp only [I, inter_cons, inter_nil, inf_top_eq]
      change (0 : k × k) ∈ PresentationExamples.verticalLine 0 ⊓
        (PresentationExamples.horizontalZero k ⊓ PresentationExamples.diagonalZero k)
      simp only [AffineSubspace.mem_inf_iff, PresentationExamples.mem_verticalLine,
        PresentationExamples.mem_horizontalZero, PresentationExamples.mem_diagonalZero]
      exact ⟨rfl, rfl, rfl⟩
    · exact lt_of_le_of_lt (codim_le_finrank _) (by simp [I])
  simpa only [I, wordBoundary_triple] using
    wordBoundary_eq_zero_of_isDependent B (PresentationExamples.threeConcurrent k) hdep

end OrlikSolomon.AffineLineExamples
