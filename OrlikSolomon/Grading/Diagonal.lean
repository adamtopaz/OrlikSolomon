/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The diagonal of a bigrading, and homogeneous bases

This file contains two pieces of pure algebra about a bigrading `𝒜 : ℤ × ℤ → Submodule R A`.

The first is the diagonal. The pieces `𝒜 (q, q)`, for natural numbers `q`, are closed under
multiplication, so their external direct sum `⨁ q, 𝒜 (q, q)` is an `R`-algebra by Mathlib's
instances, and it embeds in `A` by `DirectSum.coeAlgHom`. An algebra map `φ : M → A` from an
`ℕ`-graded algebra that restricts to a bijection `ℳ q → 𝒜 (q, q)` for each `q` is then an algebra
equivalence from `M` to this direct sum.

The second is about a `B`-basis `e` of an `R`-bigraded module, where `B` is an `R`-algebra graded by
weights, and each `e i` has diagonal bidegree `(s i, s i)`. The piece of bidegree `(p, w)` is then
`R`-linearly a direct sum of copies of the piece `ℬ (w - p)` of `B`, one for each `e i` with
`s i = p`. That piece is an `R`-module and not a ring, so this is not freeness. In particular, the
coordinates of a homogeneous element are homogeneous, and if `R ≃ ℬ 0` then the vectors `e i` with
`s i = q` form an `R`-basis of the piece `(q, q)`.

## Main definitions

* `OrlikSolomon.diagonalGrading 𝒜 q`: the piece `𝒜 (q, q)`.
* `OrlikSolomon.diagonalPieceEquiv`: the equivalence `ℳ q ≃ₗ[R] diagonalGrading 𝒜 q` given by `φ`.
* `OrlikSolomon.diagonalAlgEquiv`: the equivalence `M ≃ₐ[R] ⨁ q, diagonalGrading 𝒜 q`.
* `OrlikSolomon.homogeneousBasisEquiv`: the equivalence `𝒩 (p, w) ≃ₗ[R] ({i // s i = p} → ℬ v)`, for
  `p + v = w`.
* `OrlikSolomon.homogeneousDiagonalBasis`: the `R`-basis of `𝒩 (q, q)` of the `e i` with `s i = q`.

## Main results

* `OrlikSolomon.injective_coeAlgHom_diagonalGrading`: the direct sum embeds in `A`.
* `OrlikSolomon.coe_diagonalAlgEquiv_apply`, `OrlikSolomon.coeAlgHom_diagonalAlgEquiv`: the
  equivalence is `φ` on components, and in `A`.
* `OrlikSolomon.injective_of_forall_bijOn`: such a `φ` is injective.
* `OrlikSolomon.repr_eq_zero_of_mem_of_ne`, `OrlikSolomon.repr_mem_of_mem_of_eq`: the coordinates of
  a homogeneous element.

## Blueprint

These are the algebra behind the diagonal and the homogeneous pieces of a basis in `cor:ordinary`
and `thm:betti`. The diagonal applies equally to `thm:projective`.
-/

@[expose] public section

noncomputable section

open DirectSum Module

namespace OrlikSolomon

/-! ### The diagonal -/

section Diagonal

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring M] [Algebra R M]
  (𝒜 : ℤ × ℤ → Submodule R A)

/-- The diagonal piece `𝒜 (q, q)` of a bigrading, indexed by a natural number. Its external direct
sum is the blueprint's `⨁_{q ≥ 0} H^{q, q}`. -/
def diagonalGrading (q : ℕ) : Submodule R A :=
  𝒜 (q, q)

variable {𝒜} in
@[simp]
theorem mem_diagonalGrading {q : ℕ} {x : A} : x ∈ diagonalGrading 𝒜 q ↔ x ∈ 𝒜 (q, q) :=
  Iff.rfl

instance [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (diagonalGrading 𝒜) where
  one_mem := by
    rw [mem_diagonalGrading, Nat.cast_zero]
    exact SetLike.one_mem_graded 𝒜
  mul_mem i j x y hx hy := by
    rw [mem_diagonalGrading, Nat.cast_add]
    exact SetLike.mul_mem_graded (mem_diagonalGrading.1 hx) (mem_diagonalGrading.1 hy)

section

variable {𝒜} (ℳ : ℕ → Submodule R M) {φ : M →ₐ[R] A}

/-- The linear equivalence of a piece given by an algebra map that is bijective on it. -/
def diagonalPieceEquiv (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) (q : ℕ) :
    ℳ q ≃ₗ[R] diagonalGrading 𝒜 q :=
  LinearEquiv.ofBijective (φ.toLinearMap.restrict fun _ hx ↦ (hφ q).mapsTo hx)
    ⟨fun _ _ hxy ↦ Subtype.ext ((hφ q).injOn (Subtype.coe_prop _) (Subtype.coe_prop _)
        (congrArg Subtype.val hxy)),
      fun y ↦ let ⟨x, hx, hxy⟩ := (hφ q).surjOn y.2; ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp]
theorem coe_diagonalPieceEquiv_apply (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) (q : ℕ)
    (x : ℳ q) : (diagonalPieceEquiv ℳ hφ q x : A) = φ x :=
  rfl

end

variable [GradedAlgebra 𝒜]

/-- The component in `A` of the image of an element of the direct sum is its component there. -/
theorem coe_decompose_coeAlgHom_diagonalGrading (x : ⨁ q, diagonalGrading 𝒜 q) (q : ℕ) :
    (decompose 𝒜 (coeAlgHom (diagonalGrading 𝒜) x) ((q : ℤ), (q : ℤ)) : A) = x q := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [coeAlgHom_of]
    obtain rfl | hpq := eq_or_ne p q
    · rw [decompose_of_mem_same 𝒜 x.2, of_eq_same]
    · rw [decompose_of_mem_ne 𝒜 x.2 (by simpa using hpq), of_eq_of_ne _ _ _ hpq.symm,
        ZeroMemClass.coe_zero]
  | add x y hx hy => simp [hx, hy]

/-- The direct sum of the diagonal pieces embeds in `A`. -/
theorem injective_coeAlgHom_diagonalGrading :
    Function.Injective (coeAlgHom (diagonalGrading 𝒜)) := fun x y h ↦
  DFinsupp.ext fun q ↦ Subtype.ext <| by
    rw [← coe_decompose_coeAlgHom_diagonalGrading, ← coe_decompose_coeAlgHom_diagonalGrading, h]

variable {𝒜} (ℳ : ℕ → Submodule R M) [GradedAlgebra ℳ] {φ : M →ₐ[R] A}

/-- The linear equivalence underlying `diagonalAlgEquiv`. -/
def diagonalLinearEquiv (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) :
    M ≃ₗ[R] ⨁ q, diagonalGrading 𝒜 q :=
  decomposeLinearEquiv ℳ ≪≫ₗ DFinsupp.mapRange.linearEquiv (diagonalPieceEquiv ℳ hφ)

theorem coeAlgHom_diagonalLinearEquiv (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ))))
    (x : M) : coeAlgHom (diagonalGrading 𝒜) (diagonalLinearEquiv ℳ hφ x) = φ x := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q x =>
    have h : diagonalLinearEquiv ℳ hφ (x : M) = of _ q (diagonalPieceEquiv ℳ hφ q x) := by
      change DFinsupp.mapRange.linearEquiv (diagonalPieceEquiv ℳ hφ) (decompose ℳ (x : M)) = _
      rw [decompose_coe]
      exact DFinsupp.mapRange_single (hf := fun _ ↦ map_zero _)
    rw [h, coeAlgHom_of, coe_diagonalPieceEquiv_apply]
  | add x y hx hy => simp [hx, hy]

/-- An algebra map from an `ℕ`-graded algebra `M` to a bigraded algebra `A` that restricts to a
bijection `ℳ q → 𝒜 (q, q)` for each `q` is an algebra equivalence from `M` to the direct sum of the
diagonal pieces of `A`. Its characterizing property is `coeAlgHom_diagonalAlgEquiv`, and it
preserves the grading by `coe_diagonalAlgEquiv_apply` and `diagonalAlgEquiv_of_mem`. -/
def diagonalAlgEquiv (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) :
    M ≃ₐ[R] ⨁ q, diagonalGrading 𝒜 q :=
  AlgEquiv.ofLinearEquiv (diagonalLinearEquiv ℳ hφ)
    (injective_coeAlgHom_diagonalGrading 𝒜 <| by
      rw [coeAlgHom_diagonalLinearEquiv, map_one, map_one])
    fun x y ↦ injective_coeAlgHom_diagonalGrading 𝒜 <| by
      rw [map_mul (coeAlgHom _), coeAlgHom_diagonalLinearEquiv, coeAlgHom_diagonalLinearEquiv,
        coeAlgHom_diagonalLinearEquiv, map_mul]

/-- The image in `A` of `diagonalAlgEquiv` is `φ`. -/
@[simp]
theorem coeAlgHom_diagonalAlgEquiv (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) (x : M) :
    coeAlgHom (diagonalGrading 𝒜) (diagonalAlgEquiv ℳ hφ x) = φ x :=
  coeAlgHom_diagonalLinearEquiv ℳ hφ x

/-- The component of degree `q` of `diagonalAlgEquiv` is `φ` of the component of degree `q`. This
says that `diagonalAlgEquiv` preserves the grading. -/
theorem coe_diagonalAlgEquiv_apply (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) (x : M)
    (q : ℕ) : (diagonalAlgEquiv ℳ hφ x q : A) = φ (decompose ℳ x q) :=
  rfl

/-- On an element of degree `q`, `diagonalAlgEquiv` is the inclusion of the piece of degree `q`. -/
theorem diagonalAlgEquiv_of_mem (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) {q : ℕ} {x : M}
    (hx : x ∈ ℳ q) : diagonalAlgEquiv ℳ hφ x = of _ q ⟨φ x, (hφ q).mapsTo hx⟩ :=
  injective_coeAlgHom_diagonalGrading 𝒜 <| by
    rw [coeAlgHom_diagonalAlgEquiv, coeAlgHom_of]

/-- An algebra map from an `ℕ`-graded algebra to a bigraded algebra that restricts to a bijection
`ℳ q → 𝒜 (q, q)` for each `q` is injective. -/
theorem injective_of_forall_bijOn (hφ : ∀ q, Set.BijOn φ (ℳ q) (𝒜 ((q : ℤ), (q : ℤ)))) :
    Function.Injective φ := fun x y h ↦
  (diagonalAlgEquiv ℳ hφ).injective <| injective_coeAlgHom_diagonalGrading 𝒜 <| by
    rw [coeAlgHom_diagonalAlgEquiv, coeAlgHom_diagonalAlgEquiv, h]

end Diagonal

/-! ### Homogeneous bases -/

section HomogeneousBasis

variable {R B M ι : Type*} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
  [Module B M] {ℬ : ℤ → Submodule R B} {𝒩 : ℤ × ℤ → Submodule R M}
  [Decomposition ℬ] [Decomposition 𝒩] (e : Basis ι B M) {s : ι → ℕ}
  (hsmul : ∀ ⦃v p w : ℤ⦄ ⦃c : B⦄ ⦃x : M⦄, c ∈ ℬ v → x ∈ 𝒩 (p, w) → c • x ∈ 𝒩 (p, w + v))
  (he : ∀ i, e i ∈ 𝒩 ((s i : ℤ), (s i : ℤ)))

include hsmul he

/-- The component of `c • e i` in bidegree `(p, w)`, where `e i` has bidegree `(s i, s i)`. -/
private theorem coe_decompose_smul_of_mem (i : ι) (c : B) {p v w : ℤ} (hw : p + v = w) :
    (decompose 𝒩 (c • e i) (p, w) : M) =
      if (s i : ℤ) = p then (decompose ℬ c v : B) • e i else 0 := by
  classical
  induction c using Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous t c =>
    have hmem := hsmul c.2 (he i)
    obtain rfl | hp := eq_or_ne (s i : ℤ) p
    · rw [ite_eq_left rfl]
      obtain rfl | ht := eq_or_ne t v
      · rw [decompose_of_mem_same 𝒩 (show (c : B) • e i ∈ 𝒩 ((s i : ℤ), w) from hw ▸ hmem),
          decompose_coe, of_eq_same]
      · rw [decompose_of_mem_ne 𝒩 hmem (by simpa [← hw] using ht), decompose_coe,
          of_eq_of_ne _ _ _ ht.symm, ZeroMemClass.coe_zero, zero_smul]
    · rw [ite_eq_right hp, decompose_of_mem_ne 𝒩 hmem (by simpa using fun h ↦ absurd h hp)]
  | add c d hc hd =>
    simp only [add_smul, decompose_add, add_apply, Submodule.coe_add, hc, hd]
    split_ifs <;> simp

/-- The element `x` of bidegree `(p, w)` is the sum of `c_i • e i`, with `c_i` the component of
weight `v` of its coordinate at `i`, over those `i` with `s i = p`. -/
private theorem eq_sum_decompose_repr [Fintype ι] {p v w : ℤ} (hw : p + v = w) {x : M}
    (hx : x ∈ 𝒩 (p, w)) :
    x = ∑ i, (if (s i : ℤ) = p then (decompose ℬ (e.repr x i) v : B) else 0) • e i := by
  classical
  have h : (decompose 𝒩 (∑ i, e.repr x i • e i) (p, w) : M) =
      ∑ i, (decompose 𝒩 (e.repr x i • e i) (p, w) : M) := by
    rw [decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [e.sum_repr, decompose_of_mem_same 𝒩 hx] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [coe_decompose_smul_of_mem e hsmul he i _ hw]
  split_ifs <;> simp

/-- The coordinates of an element of bidegree `(p, w)` vanish at every basis vector whose bidegree
`(s i, s i)` has `s i ≠ p`. -/
theorem repr_eq_zero_of_mem_of_ne [Finite ι] {p w : ℤ} {x : M} (hx : x ∈ 𝒩 (p, w)) {i : ι}
    (hi : (s i : ℤ) ≠ p) : e.repr x i = 0 := by
  classical
  have := Fintype.ofFinite ι
  have h := congrArg (fun y : M ↦ e.repr y i)
    (eq_sum_decompose_repr e hsmul he (add_sub_cancel p w) hx)
  simpa only [Basis.repr_sum_self, hi, ite_false] using h

/-- The coordinates of an element of bidegree `(p, w)` have weight `v`, for `p + v = w`, at every
basis vector of bidegree `(p, p)`. -/
theorem repr_mem_of_mem_of_eq [Finite ι] {p v w : ℤ} (hw : p + v = w) {x : M} (hx : x ∈ 𝒩 (p, w))
    {i : ι} (hi : (s i : ℤ) = p) : e.repr x i ∈ ℬ v := by
  classical
  have := Fintype.ofFinite ι
  have h := congrArg (fun y : M ↦ e.repr y i) (eq_sum_decompose_repr e hsmul he hw hx)
  simp only [Basis.repr_sum_self, hi, ite_true] at h
  rw [h]
  exact (decompose ℬ _ v).2

omit [Decomposition ℬ] [Decomposition 𝒩] in
/-- The sum of `c i • e i`, for coefficients of weight `v` and `i` with `s i = p`, has bidegree
`(p, w)`, where `p + v = w`. -/
theorem sum_smul_mem [Fintype ι] {p : ℕ} {v w : ℤ} (hw : (p : ℤ) + v = w)
    (c : {i // s i = p} → ℬ v) : ∑ i, (c i : B) • e i ∈ 𝒩 ((p : ℤ), w) := by
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h := hsmul (c i).2 (he i)
  rwa [i.2, hw] at h

variable [Fintype ι] [IsScalarTower R B M]

/-- If `e` is a `B`-basis of `M` with each `e i` of bidegree `(s i, s i)`, then the piece of `M` of
bidegree `(p, w)` is `R`-linearly a direct sum of copies of the piece `ℬ v` of `B`, where
`p + v = w`, one for each `e i` with `s i = p`. The equivalence sends an element to its coordinates.

This applies to any `R`-module with a `B`-module structure for which the weights of `B` add to the
second degree, as `hsmul` says. No rank is involved, and `R` can be the zero ring. -/
def homogeneousBasisEquiv {p : ℕ} {v w : ℤ} (hw : (p : ℤ) + v = w) :
    𝒩 ((p : ℤ), w) ≃ₗ[R] ({i // s i = p} → ℬ v) where
  toFun x i := ⟨e.repr x i, repr_mem_of_mem_of_eq e hsmul he hw x.2 (by rw [i.2])⟩
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    have h := LinearMapClass.map_smul_of_tower e.repr r (x : M)
    simpa using DFunLike.congr_fun h (i : ι)
  invFun c := ⟨∑ i, (c i : B) • e i, sum_smul_mem e hsmul he hw c⟩
  left_inv x := by
    classical
    refine Subtype.ext ?_
    have hsum : ∑ i ∈ Finset.univ.filter (fun i ↦ s i = p), e.repr (x : M) i • e i =
        ∑ i : {i // s i = p}, e.repr (x : M) i • e i :=
      Finset.sum_subtype _ (by simp) _
    rw [Finset.sum_filter_of_ne fun i _ hne ↦ ?_, e.sum_repr] at hsum
    · exact hsum.symm
    · by_contra hi
      exact hne (by
        rw [repr_eq_zero_of_mem_of_ne e hsmul he x.2 (i := i) (by exact_mod_cast hi), zero_smul])
  right_inv c := by
    classical
    ext i
    simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ Finsupp.single_eq_of_ne (by
      exact fun h ↦ hj (Subtype.ext h.symm))) (by simp), Finsupp.single_eq_same]

@[simp]
theorem coe_homogeneousBasisEquiv_apply {p : ℕ} {v w : ℤ} (hw : (p : ℤ) + v = w)
    (x : 𝒩 ((p : ℤ), w)) (i : {i // s i = p}) :
    (homogeneousBasisEquiv e hsmul he hw x i : B) = e.repr x i :=
  rfl

@[simp]
theorem coe_homogeneousBasisEquiv_symm_apply {p : ℕ} {v w : ℤ} (hw : (p : ℤ) + v = w)
    (c : {i // s i = p} → ℬ v) :
    ((homogeneousBasisEquiv e hsmul he hw).symm c : M) = ∑ i, (c i : B) • e i :=
  rfl

/-- If `z : R ≃ ℬ 0`, then the `e i` with `s i = q` form an `R`-basis of the piece `(q, q)`. See
`coe_homogeneousDiagonalBasis_apply`. -/
def homogeneousDiagonalBasis (z : R ≃ₗ[R] ℬ 0) (q : ℕ) :
    Basis {i // s i = q} R (𝒩 ((q : ℤ), (q : ℤ))) :=
  Basis.ofEquivFun (homogeneousBasisEquiv e hsmul he (add_zero (q : ℤ)) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ z.symm)

/-- The vectors of `homogeneousDiagonalBasis` are the `e i`, when `z` sends `1` to `1`. -/
theorem coe_homogeneousDiagonalBasis_apply (z : R ≃ₗ[R] ℬ 0) (hz : (z 1 : B) = 1) (q : ℕ)
    (i : {i // s i = q}) : (homogeneousDiagonalBasis e hsmul he z q i : M) = e i := by
  classical
  rw [homogeneousDiagonalBasis, Basis.coe_ofEquivFun]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    coe_homogeneousBasisEquiv_symm_apply]
  rw [Finset.sum_eq_single i]
  · simp [hz]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

end HomogeneousBasis

end OrlikSolomon
