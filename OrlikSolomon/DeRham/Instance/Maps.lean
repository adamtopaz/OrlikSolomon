/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import OrlikSolomon.DeRham.Instance.Twisted
public import OrlikSolomon.DeRham.Maps

/-!
# The twisted Gysin and residue maps

For a smooth principal pair `(f, φ : A → S)` and a localization `L` of `A` away from `f`, this file
extends the maps of `DeRham/Maps` to `C(-) = k[T;T⁻¹] ⊗[k] H^•_dR(-)` and proves that the
extensions have every property that `OrdinaryTheory` asks of a Gysin map and a residue:
`g(T^w y) = T^(w+1) G(y)` and `R(T^w x) = T^(w-1) r(x)`.

This file does not mention `SmoothAlg k` or `DivisorPair k`, and `k` is any commutative ring in
which positive integers are units. `DeRham/Instance` applies it to a divisor pair.

## Main definitions

* `OrlikSolomon.DeRham.TwistedCohomology.twistMap w f`: the `k[T;T⁻¹]`-linear extension of a
  `k`-linear map `f`, times `T^w`, for any `k`-modules.
* `OrlikSolomon.DeRham.TwistedCohomology.gysin L h`: the map `g`, with `w = 1`.
* `OrlikSolomon.DeRham.TwistedCohomology.residue L hUnits h`: the map `R`, with `w = -1`.

## Main results

Blueprint `thm:dr-ordinary-localization`:

* `TwistedCohomology.isHomogeneousOfShift_gysin`, `TwistedCohomology.isHomogeneousOfShift_residue`:
  the shifts `(2, 1)` and `(-1, -1)`.
* `TwistedCohomology.exact_gysin_map`, `TwistedCohomology.exact_map_residue`,
  `TwistedCohomology.exact_residue_gysin`: the three exactness statements.
* `TwistedCohomology.gysin_map`, `TwistedCohomology.residue_map`: naturality for a map of pairs.
* `TwistedCohomology.residue_mul_map`: the projection formula, with the first factor first and no
  sign. It has no degree hypothesis, which is stronger than `OrdinaryTheory` asks.

## Exactness

The blueprint proves total exactness from exactness in each bidegree. Here it is one step shorter:
`k[T;T⁻¹]` is free over `k`, so tensoring with it preserves exactness, and `T^w` is a unit. This is
`exact_twistMap`, and it needs nothing about `k`. In particular it uses no field and no dimension.

## Blueprint

`def:dr-twisted-maps`, `thm:dr-ordinary-localization`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial (T)

namespace OrlikSolomon.DeRham.TwistedCohomology

/-! ### Twisting a linear map -/

section Twist

variable {k M N Q : Type*} [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup Q] [Module k Q]

/-- The `k[T;T⁻¹]`-linear extension of a `k`-linear map `f`, times `T^w`. It sends `T^v c` to
`T^(v+w) f(c)`, by `twistMap_T_tmul`. It is well defined and linear because multiplication by `T^w`
is linear over `k[T;T⁻¹]`.

Blueprint: `def:dr-twisted-maps`. -/
def twistMap (w : ℤ) (f : M →ₗ[k] N) : k[T;T⁻¹] ⊗[k] M →ₗ[k[T;T⁻¹]] k[T;T⁻¹] ⊗[k] N :=
  (T w : k[T;T⁻¹]) • f.baseChange k[T;T⁻¹]

@[simp]
theorem twistMap_tmul (w : ℤ) (f : M →ₗ[k] N) (b : k[T;T⁻¹]) (c : M) :
    twistMap w f (b ⊗ₜ[k] c) = (T w * b) ⊗ₜ[k] f c := by
  rw [twistMap, LinearMap.smul_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul',
    smul_eq_mul]

theorem twistMap_T_tmul (w v : ℤ) (f : M →ₗ[k] N) (c : M) :
    twistMap w f (T v ⊗ₜ[k] c) = T (v + w) ⊗ₜ[k] f c := by
  rw [twistMap_tmul, add_comm, LaurentPolynomial.T_add]

/-- The value of `twistMap` is `T^w` times the value of the base change. -/
theorem twistMap_apply (w : ℤ) (f : M →ₗ[k] N) (x : k[T;T⁻¹] ⊗[k] M) :
    twistMap w f x = (T w : k[T;T⁻¹]) • f.baseChange k[T;T⁻¹] x :=
  rfl

/-- Multiplication by `T^w` is injective on any `k[T;T⁻¹]`-module, since `T^w` is a unit. -/
theorem T_smul_eq_zero {M : Type*} [AddCommGroup M] [Module k[T;T⁻¹] M] {w : ℤ} {x : M} :
    (T w : k[T;T⁻¹]) • x = 0 ↔ x = 0 :=
  ((LaurentPolynomial.isUnit_T w).smul_eq_zero)

/-- **Twisting preserves exactness**, for any powers of `T`: `k[T;T⁻¹]` is free over `k`, and `T^w`
is a unit. Nothing is assumed about `k`.

Blueprint: `thm:dr-ordinary-localization`, the total exactness. -/
theorem exact_twistMap {f : M →ₗ[k] N} {g : N →ₗ[k] Q} (h : Function.Exact f g) (v w : ℤ) :
    Function.Exact (twistMap v f) (twistMap w g) := by
  have hb : Function.Exact (f.baseChange k[T;T⁻¹]) (g.baseChange k[T;T⁻¹]) := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_exact k[T;T⁻¹] h
  intro y
  rw [twistMap_apply, T_smul_eq_zero, hb y]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(T (-v) : k[T;T⁻¹]) • x, ?_⟩
    rw [twistMap_apply, map_smul, smul_smul, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, one_smul]
  · rintro ⟨x, rfl⟩
    exact ⟨(T v : k[T;T⁻¹]) • x, by rw [twistMap_apply, map_smul]⟩

end Twist

variable {k : Type*} [CommRing k]

section Graded

variable {A A' : Type*} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']

/-- The pullback `1 ⊗ H(φ)` is the twist by `T^0` of `H(φ)`. -/
theorem map_eq_twistMap (φ : A →ₐ[k] A') :
    ⇑(map φ) = twistMap 0 (Cohomology.map φ).toLinearMap := by
  funext x
  induction x using induction_on with
  | T_tmul w c => rw [map_tmul, twistMap_T_tmul, add_zero]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Removing the powers of `T` after twisting is the same as twisting after removing them. -/
@[simp]
theorem evalOne_twistMap (w : ℤ) (f : Cohomology k A →ₗ[k] Cohomology k A')
    (x : TwistedCohomology k A) : evalOne k A' (twistMap w f x) = f (evalOne k A x) := by
  induction x using induction_on with
  | T_tmul v c => rw [twistMap_T_tmul, evalOne_T_tmul, evalOne_T_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If `f` has cohomological shift `p`, then `T^w f` has shift `(p, w)`. -/
theorem isHomogeneousOfShift_twistMap {p : ℤ} (w : ℤ) {f : Cohomology k A →ₗ[k] Cohomology k A'}
    (hf : IsHomogeneousOfShift (Cohomology.grading k A) (Cohomology.grading k A') p f) :
    IsHomogeneousOfShift (grading k A) (grading k A') (p, w) (twistMap w f) := by
  rintro ⟨q, v⟩ x hx
  obtain ⟨c, hc, rfl⟩ := mem_grading_iff.1 hx
  rw [twistMap_T_tmul]
  exact T_tmul_mem_grading (hf hc)

end Graded

/-! ### The maps of a smooth principal pair -/

variable {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}
  (L : Type*) [CommRing L] [Algebra k L] [Algebra A L] [IsScalarTower k A L]
  [IsLocalization.Away f L] (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))

local notation "j" => IsScalarTower.toAlgHom k A L

/-- The twisted Gysin map `g : C(S) → C(A)`, with `g(T^w y) = T^(w+1) G(y)`, by `gysin_T_tmul`.

Blueprint: `def:dr-twisted-maps`. -/
def gysin (h : IsSmoothPrincipalPair f φ) :
    TwistedCohomology k S →ₗ[k[T;T⁻¹]] TwistedCohomology k A :=
  twistMap 1 (DeRham.gysin L h)

/-- The twisted residue `R : C(L) → C(S)`, with `R(T^w x) = T^(w-1) r(x)`, by `residue_T_tmul`.

Blueprint: `def:dr-twisted-maps`. -/
def residue (h : IsSmoothPrincipalPair f φ) :
    TwistedCohomology k L →ₗ[k[T;T⁻¹]] TwistedCohomology k S :=
  twistMap (-1) (DeRham.residue L hUnits h)

variable {L}

/-- `g(T^w y) = T^(w+1) G(y)`.

Blueprint: `def:dr-twisted-maps`. -/
@[simp]
theorem gysin_T_tmul (h : IsSmoothPrincipalPair f φ) (w : ℤ) (c : Cohomology k S) :
    gysin L h (T w ⊗ₜ[k] c) = T (w + 1) ⊗ₜ[k] DeRham.gysin L h c :=
  twistMap_T_tmul _ _ _ _

/-- `R(T^w x) = T^(w-1) r(x)`.

Blueprint: `def:dr-twisted-maps`. -/
@[simp]
theorem residue_T_tmul (h : IsSmoothPrincipalPair f φ) (w : ℤ) (c : Cohomology k L) :
    residue L hUnits h (T w ⊗ₜ[k] c) = T (w - 1) ⊗ₜ[k] DeRham.residue L hUnits h c := by
  rw [sub_eq_add_neg]
  exact twistMap_T_tmul _ _ _ _

/-- Removing the powers of `T` from `g` gives `G`. -/
@[simp]
theorem evalOne_gysin (h : IsSmoothPrincipalPair f φ) (x : TwistedCohomology k S) :
    evalOne k A (gysin L h x) = DeRham.gysin L h (evalOne k S x) :=
  evalOne_twistMap _ _ _

/-- Removing the powers of `T` from `R` gives `r`. -/
@[simp]
theorem evalOne_residue (h : IsSmoothPrincipalPair f φ) (x : TwistedCohomology k L) :
    evalOne k S (residue L hUnits h x) = DeRham.residue L hUnits h (evalOne k L x) :=
  evalOne_twistMap _ _ _

variable (L)

/-- The twisted Gysin map has shift `(2, 1)`: the map `G` has cohomological shift `2`, and the
factor `T` adds `1` to the weight.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem isHomogeneousOfShift_gysin (h : IsSmoothPrincipalPair f φ) :
    IsHomogeneousOfShift (grading k S) (grading k A) (2, 1) (gysin L h) :=
  isHomogeneousOfShift_twistMap 1 (DeRham.isHomogeneousOfShift_gysin L h)

/-- The twisted residue has shift `(-1, -1)`: the map `r` has cohomological shift `-1`, and the
factor `T⁻¹` subtracts `1` from the weight.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem isHomogeneousOfShift_residue (h : IsSmoothPrincipalPair f φ) :
    IsHomogeneousOfShift (grading k L) (grading k S) (-1, -1) (residue L hUnits h) :=
  isHomogeneousOfShift_twistMap (-1) (DeRham.isHomogeneousOfShift_residue L hUnits h)

include hUnits in
/-- `im g = ker C(j)`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem exact_gysin_map (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (gysin L h) (map (j)) := by
  rw [map_eq_twistMap]
  exact exact_twistMap (DeRham.exact_gysin_map L hUnits h) 1 0

/-- `im C(j) = ker R`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem exact_map_residue (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (map (j)) (residue L hUnits h) := by
  rw [map_eq_twistMap]
  exact exact_twistMap (DeRham.exact_map_residue L hUnits h) 0 (-1)

/-- `im R = ker g`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem exact_residue_gysin (h : IsSmoothPrincipalPair f φ) :
    Function.Exact (residue L hUnits h) (gysin L h) :=
  exact_twistMap (DeRham.exact_residue_gysin L hUnits h) (-1) 1

variable {L}

/-- **The projection formula** `R(α C(j)β) = R(α) C(i)β`, with no sign. It reduces to `T^w a` and
`T^v b`, for which it is `thm:dr-projection` with the powers of `T` pulled out, since `T` is
central.
It holds for every `α`, and not only for `α` of bidegree `(1, 1)`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem residue_mul_map (h : IsSmoothPrincipalPair f φ) (a : TwistedCohomology k L)
    (b : TwistedCohomology k A) :
    residue L hUnits h (a * map (j) b) = residue L hUnits h a * map φ b := by
  induction a using induction_on with
  | T_tmul w a =>
    induction b using induction_on with
    | T_tmul v b =>
      rw [map_tmul, map_tmul, T_tmul_mul_T_tmul, residue_T_tmul, DeRham.residue_mul_map,
        residue_T_tmul, T_tmul_mul_T_tmul, sub_add_eq_add_sub]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]

/-! ### Naturality -/

section Naturality

variable {L' : Type*} [CommRing L'] {A' : Type*} [CommRing A'] [Algebra k A'] {f' : A'}
  {S' : Type*} [CommRing S'] [Algebra k S'] {π : A →ₐ[k] S} {π' : A' →ₐ[k] S'}
  [Algebra k L'] [Algebra A' L'] [IsScalarTower k A' L'] [IsLocalization.Away f' L']
  {φ' : A →ₐ[k] A'} {ψ : S →ₐ[k] S'} {χ : L →ₐ[k] L'}

/-- `g' C(ψ) = C(φ') g`, for any map of pairs: the Laurent factor is untouched, so this is
`thm:dr-naturality` for `G`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem gysin_map (H : IsPairHom f π f' π' φ' ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (x : TwistedCohomology k S) :
    gysin L' h' (map ψ x) = map φ' (gysin L h x) := by
  induction x using induction_on with
  | T_tmul w c => simp only [map_tmul, gysin_T_tmul, DeRham.gysin_map H h h' c]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `R' C(χ) = C(ψ) R`, for any map of pairs: the Laurent factor is untouched, so this is
`thm:dr-naturality` for `r`.

Blueprint: `thm:dr-ordinary-localization`. -/
theorem residue_map (H : IsPairHom f π f' π' φ' ψ χ) (h : IsSmoothPrincipalPair f π)
    (h' : IsSmoothPrincipalPair f' π') (x : TwistedCohomology k L) :
    residue L' hUnits h' (map χ x) = map ψ (residue L hUnits h x) := by
  induction x using induction_on with
  | T_tmul w c => simp only [map_tmul, residue_T_tmul, DeRham.residue_map hUnits H h h' c]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality

end OrlikSolomon.DeRham.TwistedCohomology
