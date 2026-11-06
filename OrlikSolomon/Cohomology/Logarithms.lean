/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Algebra.ExteriorWords
public import OrlikSolomon.Cohomology.Axioms

/-!
# Logarithmic classes

The axioms `OrdinaryTheory` contain no logarithmic class. This file constructs one: first the class
`τ` of `𝔾ₘ` from the standard pair `(𝔸¹, 0, 𝔾ₘ)`, and then `[u] = u^* τ` for a unit `u` of a smooth
algebra. A unit of `A` is the same thing as a regular map `Spec A → 𝔾ₘ`, namely `SmoothAlg.gmHom u`.
Blueprint: `lem:gm`, `def:log`, `lem:log-basic`, `lem:log-mul`, `lem:log-residue`,
`lem:gm-product`.

## Main definitions

* `OrdinaryTheory.tau`: the unique class of degree `(1, 1)` on `𝔾ₘ` with residue `1`.
* `OrdinaryTheory.gmEquiv`: the equivalence `B ⊕ B ≃ C(𝔾ₘ)`, `(a, b) ↦ a + τ b`.
* `OrdinaryTheory.logClass u`: the logarithmic class `[u]` of a unit `u`.
* `OrdinaryTheory.gmProductEquiv A`: the equivalence `C(X) ⊕ C(X) ≃ C(X × 𝔾ₘ)`,
  `(b, c) ↦ p^* b + [t] p^* c`.

## Main results

* `lem:gm`: `existsUnique_tau`, `gmEquiv`, with the grading described by
  `gmEquiv_mem_grading_zero_iff`, `gmEquiv_mem_grading_one_iff` and `eq_zero_of_mem_grading_gm`, and
  `tau_mul_tau`.
* `def:log`: `logClass`, `logClass_mem_grading`.
* `lem:log-basic`: `map_logClass`, `logClass_units_map_algebraMap`, `logClass_mul_self`.
* `lem:log-mul`: `logClass_mul`, `logClass_inv`, `logClass_div`,
  `logClass_units_map_algebraMap_mul`.
* `lem:log-residue`: `residue_logClass_eqnUnit`, `residue_logClass_eqnUnit_mul`, for every divisor
  pair. `Cohomology/DeletionPair` states them for deletion pairs.
* `lem:gm-product`: `gmProductEquiv`, with its inverse in `gmProductEquiv_symm_apply` and its
  degrees in `gmProductEquiv_mem_grading_iff`.

## How the later modules use this file

* `lem:restriction-surj`: `map_logClass` and `map_word_logClass` for the old monomials, and
  `logClass_eq_of_coe_eq_algebraMap_mul` because equations differ by a scalar.
* `lem:ses`: `surjective_residue_of_surjective_map_i`, `gysin_eq_zero_of_surjective_map_i` and
  `injective_map_j_of_surjective_map_i`. They need only that `i^*` is surjective, so they hold for
  every pair.
* `thm:generation`: `exists_eq_map_j_add_logClass_mul` is the step that subtracts `[f_H] j^* β`, and
  `word_logClass_mem_grading` gives the bidegree of a monomial.
* `def:realization`: `isExteriorFamily_logClass`, together with `exteriorLift`.
* `lem:realization-basic`, `lem:comparison-residue`: the naturality and scalar lemmas above, and
  `residue_logClass_mapUnits_j` for the old logarithms.
* `thm:projective`: `logClass_mul`, `logClass_div` and `gmProductEquiv`.

## Implementation notes

**`τ² = 0` comes from degree two, not from `2τ² = 0`.** `tau_mul_tau` applies
`eq_zero_of_mem_grading_gm`, since `C(𝔾ₘ)` has nothing in cohomological degree two.
Supercommutativity only gives `2τ² = 0`, which says nothing when `2` is not invertible, so these
statements are valid with coefficients in `ℤ/2` and in the zero ring.

**The order in `[f_H] j^* β` matters.** `residue_mul_map` is stated with the class of degree
`(1, 1)` on the left, and moving it to the right changes a sign. Every formula here keeps it on the
left, as `lem:log-residue` asks.

**`lem:log-mul` works over a general `A`.** The blueprint proves `[xy] - [x] = [y]` on
`𝔸¹_x × 𝔾ₘ,y` and pulls it back along `(f, g)`. Taking `y` to be the unit `f` of `A` itself, on the
pair `standardPair A`, proves the same identity with only one pullback, along `x ↦ g`. As in the
blueprint, no Künneth theorem is involved. Unlike the blueprint, no homogeneous extraction is needed
either, because no degree of the class `β` is ever used.

**Constants.** A unit `c` of `k` gives the unit `Units.map (algebraMap k A : k →* A) c` of `A`, and
`(point k)ˣ` is `kˣ` only at default transparency. Prefer the forms stated with `kˣ`. The hypothesis
that `c` is a unit of `k` is essential: `2` is a unit of `ℤ[1/2]`, which is smooth over `ℤ`, and
nothing makes its logarithmic class vanish.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.SmoothAlg OrlikSolomon.DivisorPair

universe u v w z

namespace OrlikSolomon

namespace OrdinaryTheory

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {A D : SmoothAlg k}

/-! ### The standard pair of the point -/

section Point

/-- `C(𝔸¹)` is concentrated in cohomological degree zero, like the point. -/
lemma eq_zero_of_mem_grading_polynomial_point {p w : ℤ} (hp : p ≠ 0)
    {x : T.C.obj (polynomial (point k))} (hx : x ∈ T.grading (polynomial (point k)) (p, w)) :
    x = 0 := by
  obtain ⟨y, hy, rfl⟩ := T.exists_mem_grading_map_polynomialC_eq hx
  rw [T.eq_zero_of_mem_grading_point hp hy, map_zero]

/-- The Gysin map of `(𝔸¹, 0, 𝔾ₘ)` vanishes for degree reasons: it has shift `(2, 1)`, and its
source and target are both concentrated in cohomological degree zero. -/
lemma stdGysin_point_eq_zero : T.stdGysin (point k) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  refine (T.isHomogeneousOfShift_stdGysin (point k)).map_eq_zero_of_forall (fun ⟨p, w⟩ ↦ ?_) x
  by_cases hp : p = 0
  · refine Or.inr fun y hy ↦
      T.eq_zero_of_mem_grading_polynomial_point (p := p + 2) (w := w + 1) ?_ hy
    simp [hp]
  · exact Or.inl fun y hy ↦ T.eq_zero_of_mem_grading_point hp hy

/-- The residue of `(𝔸¹, 0, 𝔾ₘ)` is surjective, since the Gysin map vanishes. -/
lemma surjective_stdResidue_point : Function.Surjective (T.stdResidue (point k)) := fun x ↦
  (T.exact_stdResidue_stdGysin (point k) x).1 (by simp [stdGysin_point_eq_zero])

/-- A class on `𝔾ₘ` of nonzero cohomological degree and zero residue vanishes: it comes from `𝔸¹`,
in the same degree. -/
lemma eq_zero_of_mem_grading_of_stdResidue_eq_zero {p w : ℤ} (hp : p ≠ 0) {x : T.C.obj (gm k)}
    (hx : x ∈ T.grading (gm k) (p, w)) (hr : T.stdResidue (point k) x = 0) : x = 0 := by
  obtain ⟨y, hy, rfl⟩ := T.exists_mem_grading_map_polynomialToLaurent_eq hx hr
  rw [T.eq_zero_of_mem_grading_polynomial_point hp hy, map_zero]

/-- `C(𝔾ₘ)` vanishes outside cohomological degrees `0` and `1`. The residue lands in the cohomology
of the point in degree `p - 1 ≠ 0`, so it vanishes, and the class then comes from `𝔸¹` in degree
`p ≠ 0`. Blueprint: the grading description in `lem:gm`. -/
theorem eq_zero_of_mem_grading_gm {p w : ℤ} (h₀ : p ≠ 0) (h₁ : p ≠ 1) {x : T.C.obj (gm k)}
    (hx : x ∈ T.grading (gm k) (p, w)) : x = 0 :=
  T.eq_zero_of_mem_grading_of_stdResidue_eq_zero h₀ hx <|
    T.eq_zero_of_mem_grading_point (sub_ne_zero.2 h₁) (T.stdResidue_mem_grading hx)

/-- A class on `𝔾ₘ` with zero residue comes from the coefficients. -/
lemma exists_algebraMap_eq_of_stdResidue_eq_zero {x : T.C.obj (gm k)}
    (hx : T.stdResidue (point k) x = 0) : ∃ a : B, algebraMap B _ a = x := by
  obtain ⟨y, rfl⟩ := (T.exact_map_stdResidue (point k) x).1 hx
  obtain ⟨z, rfl⟩ := (T.bijective_map_polynomialC (point k)).2 y
  obtain ⟨a, rfl⟩ := T.bijective_algebraMap_point.2 z
  exact ⟨a, by simp⟩

end Point

/-! ### The class `τ` -/

section Tau

/-- There is a class of degree `(1, 1)` on `𝔾ₘ` with residue `1`: lift `1` through the surjective
residue, and extract its homogeneous component. -/
lemma exists_tau : ∃ τ ∈ T.grading (gm k) (1, 1), T.stdResidue (point k) τ = 1 :=
  (T.isHomogeneousOfShift_stdResidue (point k)).exists_mem_preimage_of_surjective
    T.surjective_stdResidue_point (by simp) (T.one_mem_grading (point k))

/-- The class `τ` of `𝔾ₘ`: the unique class of degree `(1, 1)` with residue `1`
(`existsUnique_tau`). It is not a field of `OrdinaryTheory`: it is constructed from the fields.
Blueprint: `lem:gm`. -/
@[no_expose] def tau : T.C.obj (gm k) := T.exists_tau.choose

/-- `τ` has degree `(1, 1)`. Blueprint: `lem:gm`. -/
lemma tau_mem_grading : T.tau ∈ T.grading (gm k) (1, 1) := T.exists_tau.choose_spec.1

/-- `τ` has residue `1`. Blueprint: `lem:gm`. -/
@[simp] lemma stdResidue_tau : T.stdResidue (point k) T.tau = 1 := T.exists_tau.choose_spec.2

/-- The residue of `τ b` is `b`, because the residue is `B`-linear. -/
@[simp] lemma stdResidue_tau_mul_algebraMap (b : B) :
    T.stdResidue (point k) (T.tau * algebraMap B _ b) = algebraMap B _ b := by
  rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, stdResidue_tau, Algebra.smul_def, mul_one]

/-- `τ` is characterized by its degree and its residue, because the kernel of the residue has no
part in cohomological degree one. Blueprint: `lem:gm`. -/
theorem eq_tau_of_mem_grading {x : T.C.obj (gm k)} (hx : x ∈ T.grading (gm k) (1, 1))
    (hr : T.stdResidue (point k) x = 1) : x = T.tau :=
  sub_eq_zero.1 <| T.eq_zero_of_mem_grading_of_stdResidue_eq_zero one_ne_zero
    (sub_mem hx T.tau_mem_grading) (by simp [hr])

/-- There is a unique class of degree `(1, 1)` on `𝔾ₘ` with residue `1`. Blueprint: `lem:gm`. -/
theorem existsUnique_tau :
    ∃! τ : T.C.obj (gm k), τ ∈ T.grading (gm k) (1, 1) ∧ T.stdResidue (point k) τ = 1 :=
  ⟨T.tau, ⟨T.tau_mem_grading, T.stdResidue_tau⟩, fun _ h ↦ T.eq_tau_of_mem_grading h.1 h.2⟩

/-- `τ² = 0`, because `C(𝔾ₘ)` has nothing in cohomological degree two. Supercommutativity alone
would only give `2τ² = 0`, which says nothing when `2` is not invertible. Blueprint: `lem:gm`. -/
@[simp] theorem tau_mul_tau : T.tau * T.tau = 0 :=
  T.eq_zero_of_mem_grading_gm (p := 2) (w := 2) two_ne_zero (by norm_num)
    (T.mul_mem_grading T.tau_mem_grading T.tau_mem_grading)

/-- The section `t = 1` kills `τ`, because the point has nothing in cohomological degree one. -/
@[simp] lemma map_laurentSection_tau : T.C.map (laurentSection (point k)) T.tau = 0 :=
  T.eq_zero_of_mem_grading_point one_ne_zero (T.map_mem_grading _ T.tau_mem_grading)

end Tau

/-! ### The cohomology of `𝔾ₘ` -/

section GmEquiv

/-- Every class on `𝔾ₘ` is `a + τ b`, with `b` read off the residue and `a` off the section `t = 1`:
the class `x - τ b` has zero residue, so it comes from the coefficients. -/
private lemma algebraMap_add_tau_mul_eq (x : T.C.obj (gm k)) :
    algebraMap B _ (T.pointEquiv.symm (T.C.map (laurentSection (point k)) x)) +
      T.tau * algebraMap B _ (T.pointEquiv.symm (T.stdResidue (point k) x)) = x := by
  set b := T.pointEquiv.symm (T.stdResidue (point k) x)
  have hb : algebraMap B _ b = T.stdResidue (point k) x := T.pointEquiv.apply_symm_apply _
  have hr : T.stdResidue (point k) (x - T.tau * algebraMap B _ b) = 0 := by
    rw [map_sub, stdResidue_tau_mul_algebraMap, hb, sub_self]
  obtain ⟨a, ha⟩ := T.exists_algebraMap_eq_of_stdResidue_eq_zero hr
  have hx : x = algebraMap B _ a + T.tau * algebraMap B _ b := by rw [ha, sub_add_cancel]
  have hs : T.pointEquiv.symm (T.C.map (laurentSection (point k)) x) = a :=
    T.pointEquiv.symm_apply_eq.2 <| by
      rw [hx]
      simp
  rw [hs, ← hx]

/-- The equivalence `B ⊕ B ≃ C(𝔾ₘ)` of `lem:gm`, sending `(a, b)` to `a + τ b`. Its second summand
is shifted by `(1, 1)`: see `gmEquiv_mem_grading_zero_iff`, `gmEquiv_mem_grading_one_iff` and
`eq_zero_of_mem_grading_gm` for the grading.

The inverse reads `b` off the residue and `a` off the section `t = 1` (`gmEquiv_symm_apply`). This
`a` is the blueprint's: the class `x - τ b` has zero residue, so it comes from the coefficients, and
the section does not change it because it kills `τ`.

Blueprint: `lem:gm`. -/
@[no_expose] def gmEquiv : (B × B) ≃ₗ[B] T.C.obj (gm k) :=
  { (Algebra.linearMap B (T.C.obj (gm k))).coprod
      (LinearMap.mulLeft B T.tau ∘ₗ Algebra.linearMap B (T.C.obj (gm k))) with
    invFun x :=
      (T.pointEquiv.symm (T.C.map (laurentSection (point k)) x),
        T.pointEquiv.symm (T.stdResidue (point k) x))
    left_inv := fun ⟨a, b⟩ ↦ by
      refine Prod.ext (T.pointEquiv.symm_apply_eq.2 ?_) (T.pointEquiv.symm_apply_eq.2 ?_)
      · change T.C.map (laurentSection (point k))
          (algebraMap B _ a + T.tau * algebraMap B _ b) = algebraMap B _ a
        simp
      · change T.stdResidue (point k)
          (algebraMap B _ a + T.tau * algebraMap B _ b) = algebraMap B _ b
        simp
    right_inv := T.algebraMap_add_tau_mul_eq }

/-- `gmEquiv` sends `(a, b)` to `a + τ b`. Blueprint: `lem:gm`. -/
@[simp] lemma gmEquiv_apply (a b : B) :
    T.gmEquiv (a, b) = algebraMap B _ a + T.tau * algebraMap B _ b := by
  rfl

/-- The inverse of `gmEquiv` in terms of the section `t = 1` and the residue. This is not a `simp`
lemma, so that `LinearEquiv.apply_symm_apply` still fires on `gmEquiv`. -/
lemma gmEquiv_symm_apply (x : T.C.obj (gm k)) :
    T.gmEquiv.symm x =
      (T.pointEquiv.symm (T.C.map (laurentSection (point k)) x),
        T.pointEquiv.symm (T.stdResidue (point k) x)) := by
  rfl

/-- The residue reads off the second coordinate of `gmEquiv`. -/
lemma stdResidue_gmEquiv (a b : B) :
    T.stdResidue (point k) (T.gmEquiv (a, b)) = algebraMap B _ b := by
  simp

/-- The section `t = 1` reads off the first coordinate of `gmEquiv`. -/
lemma map_laurentSection_gmEquiv (a b : B) :
    T.C.map (laurentSection (point k)) (T.gmEquiv (a, b)) = algebraMap B _ a := by
  simp

/-- The grading of `gmEquiv` in cohomological degree zero: the first summand `B`, unshifted.
Blueprint: `lem:gm`. -/
theorem gmEquiv_mem_grading_zero_iff {a b : B} {w : ℤ} :
    T.gmEquiv (a, b) ∈ T.grading (gm k) (0, w) ↔ a ∈ ℬ w ∧ b = 0 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · have hs := T.map_mem_grading (laurentSection (point k)) h
    rw [map_laurentSection_gmEquiv] at hs
    exact T.algebraMap_mem_grading_point_iff.1 hs
  · have hr := T.stdResidue_mem_grading h
    rw [stdResidue_gmEquiv] at hr
    exact T.bijective_algebraMap_point.1 <| by
      rw [map_zero]
      exact T.eq_zero_of_mem_grading_point (by norm_num) hr
  · rintro ⟨ha, rfl⟩
    simpa using T.algebraMap_mem_grading (gm k) ha

/-- The grading of `gmEquiv` in cohomological degree one: the second summand `B`, shifted by
`(1, 1)`. Blueprint: `lem:gm`. -/
theorem gmEquiv_mem_grading_one_iff {a b : B} {w : ℤ} :
    T.gmEquiv (a, b) ∈ T.grading (gm k) (1, w) ↔ a = 0 ∧ b ∈ ℬ (w - 1) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · have hs := T.map_mem_grading (laurentSection (point k)) h
    rw [map_laurentSection_gmEquiv] at hs
    exact T.bijective_algebraMap_point.1 <| by
      rw [map_zero]
      exact T.eq_zero_of_mem_grading_point one_ne_zero hs
  · have hr := T.stdResidue_mem_grading h
    rw [stdResidue_gmEquiv, sub_self] at hr
    exact T.algebraMap_mem_grading_point_iff.1 hr
  · rintro ⟨rfl, hb⟩
    simpa using T.mul_mem_grading T.tau_mem_grading (T.algebraMap_mem_grading (gm k) hb)

end GmEquiv

/-! ### Logarithmic classes -/

section LogClass

/-- The *logarithmic class* `[u] = u^* τ` of a unit `u` of `A`, where `u` is viewed as the regular
map `Spec A → 𝔾ₘ` (`SmoothAlg.gmHom u`). It has degree `(1, 1)` (`logClass_mem_grading`).

Blueprint: `def:log`. -/
def logClass (u : Aˣ) : T.C.obj A := T.C.map (gmHom u) T.tau

/-- A logarithmic class has degree `(1, 1)`. Blueprint: `def:log`. -/
theorem logClass_mem_grading (u : Aˣ) : T.logClass u ∈ T.grading A (1, 1) :=
  T.map_mem_grading _ T.tau_mem_grading

/-- Logarithmic classes commute with pullback. Blueprint: `lem:log-basic`. -/
@[simp] theorem map_logClass (f : A ⟶ D) (u : Aˣ) :
    T.C.map f (T.logClass u) = T.logClass (mapUnits f u) := by
  rw [logClass, T.map_map, gmHom_comp, logClass]

/-- `τ` is the logarithmic class of the coordinate of `𝔾ₘ`. -/
@[simp] theorem logClass_laurentT_point : T.logClass (laurentT (point k)) = T.tau := by
  simp [logClass]

/-- A logarithmic class on the point vanishes, since the point has nothing in cohomological degree
one. -/
theorem logClass_point (c : (point k)ˣ) : T.logClass c = 0 :=
  T.eq_zero_of_mem_grading_point one_ne_zero (T.logClass_mem_grading c)

/-- The logarithmic class of a constant vanishes, because a constant map factors through the point.
This is the form with `c` a unit of the point, for use with `fromPoint A`. -/
@[simp] theorem logClass_mapUnits_fromPoint (c : (point k)ˣ) :
    T.logClass (mapUnits (fromPoint A) c) = 0 := by
  rw [← map_logClass, logClass_point, map_zero]

/-- `[c] = 0` for a unit `c` of `k`. It is essential that `c` is a unit of `k`, and not merely a
unit of `A` in the image of `k`: see the implementation notes. Blueprint: `lem:log-basic`. -/
@[simp] theorem logClass_units_map_algebraMap (c : kˣ) :
    T.logClass (Units.map (algebraMap k A : k →* A) c) = 0 :=
  T.logClass_mapUnits_fromPoint c

/-- `[c] = 0` for a unit of `A` given as the image of a unit `c` of `k`. -/
theorem logClass_eq_zero_of_coe_eq_algebraMap {u : Aˣ} (c : kˣ) (h : (u : A) = algebraMap k A c) :
    T.logClass u = 0 := by
  rw [show u = Units.map (algebraMap k A : k →* A) c from Units.ext h,
    logClass_units_map_algebraMap]

/-- `[1] = 0`. -/
@[simp] theorem logClass_one : T.logClass (1 : Aˣ) = 0 := by
  simpa using T.logClass_mapUnits_fromPoint (A := A) 1

/-- `[u]² = 0`, by pulling back `τ² = 0`. This holds with coefficients in `ℤ/2`, since it comes from
the vanishing of `C(𝔾ₘ)` in degree two and not from anticommutativity. Blueprint:
`lem:log-basic`. -/
@[simp] theorem logClass_mul_self (u : Aˣ) : T.logClass u * T.logClass u = 0 := by
  rw [logClass, ← map_mul, tau_mul_tau, map_zero]

/-- Logarithmic classes anticommute, because they have odd cohomological degree. -/
theorem logClass_mul_eq_neg_mul_swap (u v : Aˣ) :
    T.logClass u * T.logClass v = -(T.logClass v * T.logClass u) :=
  T.mul_eq_neg_of_odd odd_one odd_one (T.logClass_mem_grading u) (T.logClass_mem_grading v)

/-- The logarithmic classes of a family of units are an exterior family. This is the input to the
exterior universal property in `def:realization`. -/
theorem isExteriorFamily_logClass {I : Type*} (g : I → Aˣ) :
    IsExteriorFamily fun i ↦ T.logClass (g i) where
  mul_self i := T.logClass_mul_self (g i)
  mul_add_mul_swap_of_ne i j _ := by
    rw [logClass_mul_eq_neg_mul_swap, neg_add_cancel]

/-- A word of length `q` in logarithmic classes has bidegree `(q, q)`. Blueprint: the degree of a
basis vector in `thm:cohom-basis`. -/
theorem word_logClass_mem_grading {I : Type*} (g : I → Aˣ) (l : List I) :
    word (fun i ↦ T.logClass (g i)) l ∈ T.grading A ((l.length : ℤ), (l.length : ℤ)) := by
  induction l with
  | nil => simpa using T.one_mem_grading A
  | cons i l ih =>
    rw [word_cons, List.length_cons, Nat.cast_add_one, add_comm (l.length : ℤ)]
    exact T.mul_mem_grading (T.logClass_mem_grading (g i)) ih

/-- A pullback of a word in logarithmic classes is the word in the pulled back units. This is how
a monomial is lifted in `lem:restriction-surj`. -/
theorem map_word_logClass {I : Type*} (f : A ⟶ D) (g : I → Aˣ) (l : List I) :
    T.C.map f (word (fun i ↦ T.logClass (g i)) l) =
      word (fun i ↦ T.logClass (mapUnits f (g i))) l := by
  simp

end LogClass

/-! ### Multiplicativity -/

section Multiplicativity

/-- On `X × 𝔾ₘ`, the coordinate `t` has logarithmic class of residue `1`, by transverse naturality
for `z ↦ t`. -/
@[simp] theorem stdResidue_logClass_laurentT : T.stdResidue A (T.logClass (laurentT A)) = 1 := by
  rw [logClass, T.stdResidue_map_gmHom_laurentT, stdResidue_tau, map_one]

/-- The heart of `lem:log-mul`: `[y t] = [y] + [t]` on `X × 𝔾ₘ`, for a unit `y` of `A`. The maps
`t` and `y t` are both transverse to the standard pair, so `[y t]` and `[t]` have residue `1`. So
their difference comes from `X × 𝔸¹`, hence from `X`, and the section `t = 1` identifies it as
`[y]`. -/
private theorem logClass_mapUnits_laurentC_mul_laurentT (y : Aˣ) :
    T.logClass (mapUnits (laurentC A) y * laurentT A) =
      T.logClass (mapUnits (laurentC A) y) + T.logClass (laurentT A) := by
  have hd : T.stdResidue A
      (T.logClass (mapUnits (laurentC A) y * laurentT A) - T.logClass (laurentT A)) = 0 := by
    rw [map_sub, logClass, T.stdResidue_map_gmHom, stdResidue_tau, map_one,
      stdResidue_logClass_laurentT, sub_self]
  obtain ⟨β, hβ⟩ := (T.exact_map_stdResidue A _).1 hd
  obtain ⟨β, rfl⟩ := (T.bijective_map_polynomialC A).2 β
  rw [T.map_polynomialToLaurent_map_polynomialC] at hβ
  have hs := congrArg (T.C.map (laurentSection A)) hβ
  simp only [T.map_laurentSection_map_laurentC, map_sub, map_logClass, map_mul,
    mapUnits_laurentSection_mapUnits_laurentC, mapUnits_laurentSection_laurentT, mul_one,
    logClass_one, sub_zero] at hs
  rw [← sub_eq_iff_eq_add, ← hβ, hs, map_logClass]

/-- `[f g] = [f] + [g]`. No Künneth theorem is needed. Blueprint: `lem:log-mul`. -/
@[simp] theorem logClass_mul (f g : Aˣ) : T.logClass (f * g) = T.logClass f + T.logClass g := by
  have h := congrArg (T.C.map (laurentLift (𝟙 A) g)) (T.logClass_mapUnits_laurentC_mul_laurentT f)
  simpa only [map_add, map_logClass, map_mul, mapUnits_laurentLift_mapUnits_laurentC, mapUnits_id,
    mapUnits_laurentLift_laurentT] using h

/-- `[f⁻¹] = -[f]`. -/
@[simp] theorem logClass_inv (f : Aˣ) : T.logClass f⁻¹ = -T.logClass f := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← logClass_mul, inv_mul_cancel, logClass_one]

/-- `[f / g] = [f] - [g]`. Blueprint: `lem:log-mul`. -/
@[simp] theorem logClass_div (f g : Aˣ) : T.logClass (f / g) = T.logClass f - T.logClass g := by
  rw [div_eq_mul_inv, logClass_mul, logClass_inv, sub_eq_add_neg]

/-- `[c f] = [f]` for a unit `c` of `k`. Blueprint: `lem:log-mul`. -/
theorem logClass_units_map_algebraMap_mul (c : kˣ) (f : Aˣ) :
    T.logClass (Units.map (algebraMap k A : k →* A) c * f) = T.logClass f := by
  simp

/-- Two equations differing by a unit `c` of `k` have the same logarithmic class. This is the form
in which `lem:restriction-surj` and `lem:realization-basic` use `lem:log-mul`. -/
theorem logClass_eq_of_coe_eq_algebraMap_mul {u v : Aˣ} (c : kˣ)
    (h : (u : A) = algebraMap k A c * v) : T.logClass u = T.logClass v := by
  rw [show u = Units.map (algebraMap k A : k →* A) c * v from Units.ext h,
    logClass_units_map_algebraMap_mul]

end Multiplicativity

/-! ### Residues of logarithms -/

section Residue

variable (P : DivisorPair k)

/-- The residue of the logarithm of the equation of a divisor is `1`, by transverse naturality for
the map `z ↦ P.eqn` and the normalization of `τ`. The blueprint states this for a deletion pair, and
it holds for every divisor pair. Blueprint: `lem:log-residue`. -/
@[simp] theorem residue_logClass_eqnUnit : T.residue P (T.logClass P.eqnUnit) = 1 := by
  rw [logClass, T.residue_map_gmHom_eqnUnit, stdResidue_tau, map_one]

/-- `r([f] j^* β) = i^* β`, by the boundary projection formula. The logarithm must stay on the left:
moving it introduces a sign. Blueprint: `lem:log-residue`. -/
@[simp] theorem residue_logClass_eqnUnit_mul (β : T.C.obj P.ambient) :
    T.residue P (T.logClass P.eqnUnit * T.C.map P.j β) = T.C.map P.i β := by
  rw [T.residue_mul_map P (T.logClass_mem_grading _), residue_logClass_eqnUnit, one_mul]

/-- The logarithm of a unit of the ambient ring has zero residue, because it is pulled back from the
ambient space. -/
@[simp] theorem residue_logClass_mapUnits_j (u : P.ambientˣ) :
    T.residue P (T.logClass (mapUnits P.j u)) = 0 := by
  rw [← map_logClass, residue_map_j]

/-- A unit multiple of the equation has a logarithm of residue `1`. -/
theorem residue_logClass_mapUnits_j_mul_eqnUnit (u : P.ambientˣ) :
    T.residue P (T.logClass (mapUnits P.j u * P.eqnUnit)) = 1 := by
  simp

/-- Every class on the complement is `j^* a + [f] j^* β`, for any `β` restricting to its residue.
This is the step of `thm:generation` that subtracts the product with `[f_H]`. -/
theorem exists_eq_map_j_add_logClass_mul {x : T.C.obj P.compl} {β : T.C.obj P.ambient}
    (hβ : T.C.map P.i β = T.residue P x) :
    ∃ a : T.C.obj P.ambient, x = T.C.map P.j a + T.logClass P.eqnUnit * T.C.map P.j β := by
  have h : T.residue P (x - T.logClass P.eqnUnit * T.C.map P.j β) = 0 := by
    rw [map_sub, residue_logClass_eqnUnit_mul, hβ, sub_self]
  obtain ⟨a, ha⟩ := (T.exact_map_residue P _).1 h
  exact ⟨a, by rw [ha, sub_add_cancel]⟩

variable {P}

/-- If restriction to the divisor is surjective, then so is the residue: `[f] j^* β` lifts `i^* β`.
This is the first step of `lem:ses`, and it holds for every divisor pair. -/
theorem surjective_residue_of_surjective_map_i (hi : Function.Surjective (T.C.map P.i)) :
    Function.Surjective (T.residue P) := fun z ↦ by
  obtain ⟨β, rfl⟩ := hi z
  exact ⟨_, T.residue_logClass_eqnUnit_mul P β⟩

/-- If restriction to the divisor is surjective, then the Gysin map vanishes. This is where the
vanishing of Gysin maps comes from in `lem:ses`. -/
theorem gysin_eq_zero_of_surjective_map_i (hi : Function.Surjective (T.C.map P.i)) :
    T.gysin P = 0 :=
  T.gysin_eq_zero_of_surjective_residue P (T.surjective_residue_of_surjective_map_i hi)

/-- If restriction to the divisor is surjective, then the open pullback is injective. Blueprint:
`lem:ses`. -/
theorem injective_map_j_of_surjective_map_i (hi : Function.Surjective (T.C.map P.i)) :
    Function.Injective (T.C.map P.j) :=
  T.injective_map_j_of_gysin_eq_zero P (T.gysin_eq_zero_of_surjective_map_i hi)

end Residue

/-! ### The product with `𝔾ₘ` -/

section GmProduct

/-- `r([t] p^* c) = c` on `X × 𝔾ₘ`. This is `lem:log-residue` for the standard pair of `X`. -/
@[simp] theorem stdResidue_logClass_laurentT_mul (c : T.C.obj A) :
    T.stdResidue A (T.logClass (laurentT A) * T.C.map (laurentC A) c) = c := by
  rw [T.stdResidue_mul_map_laurentC (T.logClass_mem_grading _), stdResidue_logClass_laurentT,
    one_mul]

/-- The logarithm of a unit pulled back from `X` has zero residue on `X × 𝔾ₘ`. -/
@[simp] theorem stdResidue_logClass_mapUnits_laurentC (u : Aˣ) :
    T.stdResidue A (T.logClass (mapUnits (laurentC A) u)) = 0 := by
  rw [← map_logClass, stdResidue_map_laurentC]

variable (A)

/-- The residue of the standard pair of `X` is surjective: `[t] p^* c` lifts `c`. Blueprint:
`lem:gm-product`. -/
theorem surjective_stdResidue : Function.Surjective (T.stdResidue A) := fun c ↦
  ⟨_, T.stdResidue_logClass_laurentT_mul c⟩

/-- The Gysin map of the standard pair of `X` vanishes. Blueprint: `lem:gm-product`. -/
theorem stdGysin_eq_zero : T.stdGysin A = 0 :=
  T.gysin_eq_zero_of_surjective_residue (standardPair A) (T.surjective_stdResidue A)

/-- The open pullback of the standard pair of `X` is injective. Blueprint: `lem:gm-product`. -/
theorem injective_map_polynomialToLaurent :
    Function.Injective (T.C.map (polynomialToLaurent A)) :=
  T.injective_map_j_of_gysin_eq_zero (standardPair A) (T.stdGysin_eq_zero A)

/-- The equivalence `C(X) ⊕ C(X) ≃ C(X × 𝔾ₘ)`, sending `(b, c)` to `p^* b + [t] p^* c`, where
`p : X × 𝔾ₘ → X` is the projection and `t` the coordinate. Its second summand is shifted by `(1, 1)`
(`gmProductEquiv_mem_grading_iff`). The inverse is given by the section `t = 1` and the residue
(`gmProductEquiv_symm_apply`).

Blueprint: `lem:gm-product`. -/
@[no_expose] def gmProductEquiv : (T.C.obj A × T.C.obj A) ≃ₗ[B] T.C.obj (laurent A) :=
  { (T.C.map (laurentC A)).hom.toLinearMap.coprod
      (LinearMap.mulLeft B (T.logClass (laurentT A)) ∘ₗ (T.C.map (laurentC A)).hom.toLinearMap) with
    invFun x := (T.C.map (laurentSection A) x, T.stdResidue A x)
    left_inv := fun ⟨b, c⟩ ↦ by
      change (T.C.map (laurentSection A)
          (T.C.map (laurentC A) b + T.logClass (laurentT A) * T.C.map (laurentC A) c),
        T.stdResidue A
          (T.C.map (laurentC A) b + T.logClass (laurentT A) * T.C.map (laurentC A) c)) = (b, c)
      simp
    right_inv := fun x ↦ by
      change T.C.map (laurentC A) (T.C.map (laurentSection A) x) +
        T.logClass (laurentT A) * T.C.map (laurentC A) (T.stdResidue A x) = x
      have hd : T.stdResidue A
          (x - T.logClass (laurentT A) * T.C.map (laurentC A) (T.stdResidue A x)) = 0 := by
        rw [map_sub, stdResidue_logClass_laurentT_mul, sub_self]
      obtain ⟨β, hβ⟩ := (T.exact_map_stdResidue A _).1 hd
      obtain ⟨β, rfl⟩ := (T.bijective_map_polynomialC A).2 β
      rw [T.map_polynomialToLaurent_map_polynomialC] at hβ
      have hs : T.C.map (laurentSection A) x = β := by
        simpa using (congrArg (T.C.map (laurentSection A)) hβ).symm
      rw [hs, hβ, sub_add_cancel] }

variable {A}

/-- `gmProductEquiv` sends `(b, c)` to `p^* b + [t] p^* c`. Blueprint: `lem:gm-product`. -/
@[simp] lemma gmProductEquiv_apply (b c : T.C.obj A) :
    T.gmProductEquiv A (b, c) =
      T.C.map (laurentC A) b + T.logClass (laurentT A) * T.C.map (laurentC A) c := by
  rfl

/-- The inverse of `gmProductEquiv` is given by the section `t = 1` and the residue. This is not a
`simp` lemma, so that `LinearEquiv.apply_symm_apply` still fires on `gmProductEquiv`. Blueprint:
`lem:gm-product`. -/
lemma gmProductEquiv_symm_apply (x : T.C.obj (laurent A)) :
    (T.gmProductEquiv A).symm x = (T.C.map (laurentSection A) x, T.stdResidue A x) := by
  rfl

/-- The section `t = 1` reads off the first coordinate of `gmProductEquiv`. Blueprint:
`lem:gm-product`. -/
theorem map_laurentSection_gmProductEquiv (b c : T.C.obj A) :
    T.C.map (laurentSection A) (T.gmProductEquiv A (b, c)) = b := by
  simp

/-- The residue reads off the second coordinate of `gmProductEquiv`. Blueprint: `lem:gm-product`. -/
theorem stdResidue_gmProductEquiv (b c : T.C.obj A) :
    T.stdResidue A (T.gmProductEquiv A (b, c)) = c := by
  simp

/-- `gmProductEquiv` preserves degrees with its second summand shifted by `(1, 1)`: the class
`p^* b + [t] p^* c` has degree `i` exactly when `b` has degree `i` and `c` has degree `j`, where
`j + (1, 1) = i`. Blueprint: `lem:gm-product`. -/
theorem gmProductEquiv_mem_grading_iff {i j : ℤ × ℤ} (hij : j + (1, 1) = i) {b c : T.C.obj A} :
    T.gmProductEquiv A (b, c) ∈ T.grading (laurent A) i ↔
      b ∈ T.grading A i ∧ c ∈ T.grading A j := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hb, hc⟩ ↦ ?_⟩
  · simpa [T.map_laurentSection_gmProductEquiv] using T.map_mem_grading (laurentSection A) h
  · have hj : i + (-1, -1) = j := by
      rw [← hij]
      ext <;> simp
    have h' := (T.isHomogeneousOfShift_stdResidue A).map_mem hj h
    rwa [stdResidue_gmProductEquiv] at h'
  · rw [gmProductEquiv_apply]
    exact add_mem (T.map_mem_grading _ hb)
      ((isHomogeneousOfShift_mul_left (T.logClass_mem_grading _)).map_mem hij
        (T.map_mem_grading _ hc))

end GmProduct

end OrdinaryTheory

end OrlikSolomon
