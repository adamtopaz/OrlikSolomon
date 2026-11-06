/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Cohomology.Degree

/-!
# De Rham cohomology in degree zero, and of the point

Projecting a closed form to its component in degree zero gives a `k`-algebra map from the total
cohomology of `A` to `A`, whose image is the closed functions. On `H⁰` it is injective, since degree
`-1` is zero.

If `k → A` is surjective, then `Ω[A⁄k]` is zero, so the de Rham complex of `A` is `A` in degree
zero, and that map is an equivalence. For `A = k` this is the point fact `H^*(k) = k`. It uses no
hypothesis on `k`: over a field of characteristic zero it is what `lem:dr-ordinary-basic` needs.

## Main definitions

* `OrlikSolomon.DeRham.Cohomology.toDegreeZero k A`: the map `H^*(A/k) → A`.
* `OrlikSolomon.DeRham.Cohomology.degreeZeroEquiv k A`: `H⁰` is the kernel of `A → Ω[A⁄k]`.
* `OrlikSolomon.DeRham.Cohomology.equivOfSurjective`: `H^*(A/k) ≃ A` if `k → A` is surjective.

## Main results

* `OrlikSolomon.DeRham.Cohomology.toDegreeZero_map`: that map is natural in `A`.
* `OrlikSolomon.DeRham.Cohomology.bijective_algebraMap_point`: `k → H^*(k/k)` is bijective.
* `OrlikSolomon.DeRham.Cohomology.eq_zero_of_mem_grading_point`: `H^p(k/k) = 0` for every integer
  `p ≠ 0`.
-/

@[expose] public section

noncomputable section

open ExteriorAlgebra (algebraMapInv)
open KaehlerDifferential (D)

namespace OrlikSolomon.DeRham

universe u v

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

/-- The part of a differential in degree zero is zero. -/
@[simp]
theorem algebraMapInv_diff (a : A) : algebraMapInv (diff k a) = 0 := by
  simp [-ι_D, diff_apply, algebraMapInv]

/-- An exact form has no part in degree zero. This is `decompose_d_zero`, for the projection of the
exterior algebra to its coefficients. -/
@[simp]
theorem algebraMapInv_d (y : Forms k A) : algebraMapInv (d k y) = 0 := by
  induction y using Forms.induction with
  | word a l => rw [d_smul_word, map_mul, algebraMapInv_diff, zero_mul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- A form of positive degree has no part in degree zero. -/
theorem algebraMapInv_eq_zero_of_mem_exteriorPower_succ {n : ℕ} {x : Forms k A}
    (hx : x ∈ ⋀[A]^(n + 1) Ω[A⁄k]) : algebraMapInv x = 0 := by
  induction hx using Forms.induction_exteriorPower with
  | word a l hl =>
    cases l with
    | nil => exact absurd hl (by simp)
    | cons b l => rw [word_cons, map_smul, map_mul, algebraMapInv_diff, zero_mul, smul_zero]
  | add x _ y _ hx hy => rw [map_add, hx, hy, add_zero]

/-- A function is closed as a form exactly when its differential is zero. -/
theorem d_algebraMap_eq_zero_iff {a : A} : d k (algebraMap A (Forms k A) a) = 0 ↔ diff k a = 0 := by
  rw [d_algebraMap]

namespace Cohomology

variable (k A) in
/-- The `k`-algebra map from total cohomology to `A` that sends the class of a closed form to its
component in degree zero, identified with an element of `A`. Its image is the kernel of
`a ↦ da`, and it is injective on `H⁰`, by `degreeZeroEquiv`.

Blueprint: `def:dr-cohomology`, the point fact of `lem:dr-ordinary-basic`. -/
def toDegreeZero : Cohomology k A →ₐ[k] A :=
  lift ((algebraMapInv.restrictScalars k).comp (cycles k A).val) fun y => algebraMapInv_d y

@[simp]
theorem toDegreeZero_mk (x : Forms k A) (hx : d k x = 0) :
    toDegreeZero k A (mk x hx) = algebraMapInv x :=
  rfl

/-- Cohomology of a nonzero algebra is nonzero, since the unit is sent to the unit of `A`. -/
instance [Nontrivial A] : Nontrivial (Cohomology k A) :=
  (toDegreeZero k A).toRingHom.domain_nontrivial

/-- The class of a closed function is sent to that function. -/
theorem toDegreeZero_mk_algebraMap (a : A) (h : d k (algebraMap A (Forms k A) a) = 0) :
    toDegreeZero k A (mk (algebraMap A (Forms k A) a) h) = a := by
  rw [toDegreeZero_mk]
  exact ExteriorAlgebra.algebraMap_leftInverse _ a

/-- `H⁰` consists of the classes of the closed functions. -/
theorem mem_degree_zero_iff {c : Cohomology k A} :
    c ∈ degree k A 0 ↔
      ∃ (a : A) (h : d k (algebraMap A (Forms k A) a) = 0),
        mk (algebraMap A (Forms k A) a) h = c := by
  rw [mem_degree_iff]
  constructor
  · rintro ⟨x, hx, hxn, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_exteriorPower_zero_iff k).1 hxn
    exact ⟨a, hx, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨_, h, algebraMap_mem_exteriorPower_zero k a, rfl⟩

/-- The map to `A` is natural in `A`. -/
@[simp]
theorem toDegreeZero_map {A' : Type*} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
    (c : Cohomology k A) : toDegreeZero k A' (map φ c) = φ (toDegreeZero k A c) := by
  induction c using induction_degree with
  | mk n x hxn hx =>
    cases n with
    | zero =>
      obtain ⟨a, rfl⟩ := (mem_exteriorPower_zero_iff k).1 hxn
      rw [map_mk, toDegreeZero_mk_algebraMap, mk_congr (Forms.map_algebraMap φ a),
        toDegreeZero_mk_algebraMap]
    | succ n =>
      rw [map_mk, toDegreeZero_mk, toDegreeZero_mk,
        algebraMapInv_eq_zero_of_mem_exteriorPower_succ hxn, map_zero,
        algebraMapInv_eq_zero_of_mem_exteriorPower_succ (Forms.map_mem_exteriorPower φ hxn)]
  | add c c' hc hc' => simp only [map_add, hc, hc']

/-- A class in `H⁰` is the class of its value in `A`, viewed as a function. -/
theorem exists_eq_mk_toDegreeZero {c : Cohomology k A} (hc : c ∈ degree k A 0) :
    ∃ h : d k (algebraMap A (Forms k A) (toDegreeZero k A c)) = 0,
      mk (algebraMap A (Forms k A) (toDegreeZero k A c)) h = c := by
  obtain ⟨a, h, rfl⟩ := mem_degree_zero_iff.1 hc
  rw [toDegreeZero_mk_algebraMap]
  exact ⟨h, rfl⟩

/-- The map to `A` is injective on `H⁰`: degree `-1` is zero, so no nonzero function is exact. -/
theorem toDegreeZero_injOn : Set.InjOn (toDegreeZero k A) (degree k A 0) := by
  intro c hc c' hc' h
  obtain ⟨h₁, h₂⟩ := exists_eq_mk_toDegreeZero hc
  obtain ⟨h₁', h₂'⟩ := exists_eq_mk_toDegreeZero hc'
  rw [← h₂, ← h₂']
  exact mk_congr (by rw [h]) _

/-- The map to `A` lands in the closed functions. -/
theorem diff_toDegreeZero (c : Cohomology k A) : diff k (toDegreeZero k A c) = 0 := by
  induction c using induction_degree with
  | mk n x hxn hx =>
    cases n with
    | zero =>
      obtain ⟨a, rfl⟩ := (mem_exteriorPower_zero_iff k).1 hxn
      rw [toDegreeZero_mk_algebraMap, ← d_algebraMap]
      exact hx
    | succ n =>
      rw [toDegreeZero_mk, algebraMapInv_eq_zero_of_mem_exteriorPower_succ hxn, map_zero]
  | add c c' hc hc' => rw [map_add, map_add, hc, hc', add_zero]

variable (k A) in
/-- `H⁰` is the kernel of `a ↦ da`, as in the blueprint's formula in degree zero.

Blueprint: `def:dr-cohomology`. -/
def degreeZeroEquiv :
    degree k A 0 ≃ₗ[k] LinearMap.ker ((diff k : Derivation k A (Forms k A)) : A →ₗ[k] Forms k A) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((toDegreeZero k A).toLinearMap ∘ₗ (degree k A 0).subtype)
      fun c => diff_toDegreeZero (c : Cohomology k A))
    ⟨fun _ _ h => Subtype.ext (toDegreeZero_injOn (Subtype.coe_prop _) (Subtype.coe_prop _)
        (congrArg Subtype.val h)),
      fun ⟨a, ha⟩ => ⟨⟨mk (algebraMap A (Forms k A) a) (d_algebraMap_eq_zero_iff.2 ha),
        mk_mem_degree (algebraMap_mem_exteriorPower_zero k a) _⟩,
          Subtype.ext (toDegreeZero_mk_algebraMap a (d_algebraMap_eq_zero_iff.2 ha))⟩⟩

@[simp]
theorem coe_degreeZeroEquiv (c : degree k A 0) :
    (degreeZeroEquiv k A c : A) = toDegreeZero k A c :=
  rfl

/-! ### Algebras with no differentials -/

section Surjective

variable (hs : Function.Surjective (algebraMap k A))

include hs

/-- If `k → A` is surjective, then every differential is zero. -/
theorem diff_eq_zero_of_surjective (a : A) : diff k a = 0 := by
  have := KaehlerDifferential.subsingleton_of_surjective k A hs
  rw [diff_apply, Subsingleton.elim (D k A a) 0, map_zero]

/-- If `k → A` is surjective, then forms are concentrated in degree zero. -/
theorem eq_zero_of_mem_exteriorPower_of_surjective {n : ℕ} (hn : n ≠ 0) {x : Forms k A}
    (hx : x ∈ ⋀[A]^n Ω[A⁄k]) : x = 0 := by
  induction hx using Forms.induction_exteriorPower with
  | word a l hl =>
    cases l with
    | nil => exact absurd hl.symm hn
    | cons b l => rw [word_cons, diff_eq_zero_of_surjective hs, zero_mul, smul_zero]
  | add x _ y _ hx hy => rw [hx, hy, add_zero]

/-- If `k → A` is surjective, then every form is a function. -/
theorem algebraMap_algebraMapInv_of_surjective (x : Forms k A) :
    algebraMap A (Forms k A) (algebraMapInv x) = x := by
  induction x using Forms.induction with
  | word a l =>
    cases l with
    | nil => simp [Algebra.smul_def]
    | cons b l => simp [word_cons, diff_eq_zero_of_surjective hs]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- If `k → A` is surjective, then `d` is zero. -/
theorem d_eq_zero_of_surjective (x : Forms k A) : d k x = 0 := by
  rw [← algebraMap_algebraMapInv_of_surjective hs x, d_algebraMap,
    diff_eq_zero_of_surjective hs]

/-- If `k → A` is surjective, then the map to `A` is bijective. -/
theorem bijective_toDegreeZero_of_surjective : Function.Bijective (toDegreeZero k A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun a =>
    ⟨mk (algebraMap A (Forms k A) a) (d_eq_zero_of_surjective hs _),
      toDegreeZero_mk_algebraMap a _⟩⟩
  induction c with
  | mk x hx =>
    rw [toDegreeZero_mk] at hc
    rw [mk_congr (algebraMap_algebraMapInv_of_surjective hs x).symm hx]
    exact mk_congr (by rw [hc, map_zero]) _ |>.trans (mk_zero _)

/-- If `k → A` is surjective, then the total cohomology of `A` is `A`, as a `k`-algebra. -/
def equivOfSurjective : Cohomology k A ≃ₐ[k] A :=
  AlgEquiv.ofBijective (toDegreeZero k A) (bijective_toDegreeZero_of_surjective hs)

@[simp]
theorem equivOfSurjective_apply (c : Cohomology k A) :
    equivOfSurjective hs c = toDegreeZero k A c :=
  rfl

/-- If `k → A` is surjective, then cohomology is concentrated in degree zero. -/
theorem degree_eq_bot_of_surjective {n : ℕ} (hn : n ≠ 0) : degree k A n = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  exact mk_congr (eq_zero_of_mem_exteriorPower_of_surjective hs hn hxn) hx |>.trans (mk_zero _)

end Surjective

/-! ### The point -/

variable (k) in
/-- The structure map of the point is bijective: `H^*(k/k) = k`. This is the point field of
`lem:dr-ordinary-basic`, before extending coefficients.

Blueprint: `lem:dr-ordinary-basic`, using `Ω[k⁄k] = 0`. -/
theorem bijective_algebraMap_point : Function.Bijective (algebraMap k (Cohomology k k)) := by
  have hs : Function.Surjective (algebraMap k k) := Function.surjective_id
  have h : Function.LeftInverse (toDegreeZero k k) (algebraMap k (Cohomology k k)) :=
    fun c => (toDegreeZero k k).commutes c
  have hb := bijective_toDegreeZero_of_surjective hs
  exact ⟨h.injective, Function.RightInverse.surjective
    (g := toDegreeZero k k) fun c => hb.1 (h _)⟩

/-- The point has no cohomology in a nonzero natural degree.

Blueprint: `lem:dr-ordinary-basic`. -/
theorem eq_zero_of_mem_degree_point {n : ℕ} (hn : n ≠ 0) {c : Cohomology k k}
    (hc : c ∈ degree k k n) : c = 0 := by
  rwa [degree_eq_bot_of_surjective Function.surjective_id hn, Submodule.mem_bot] at hc

/-- The point has no cohomology in a nonzero degree.

Blueprint: `lem:dr-ordinary-basic`. -/
theorem eq_zero_of_mem_grading_point {p : ℤ} (hp : p ≠ 0) {c : Cohomology k k}
    (hc : c ∈ grading k k p) : c = 0 := by
  obtain hp₀ | hp₀ := lt_or_ge p 0
  · exact eq_zero_of_mem_grading_of_neg hp₀ hc
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp₀
    rw [grading_natCast] at hc
    exact eq_zero_of_mem_degree_point (by simpa using hp) hc

end Cohomology

end OrlikSolomon.DeRham
