/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Grading.Diagonal
public import OrlikSolomon.Presentation.Structure

/-!
# Ordinary groups, the diagonal and bases

The structure theorem `OrdinaryTheory.affineEquiv` is an equivalence with the presentation over the
whole coefficient ring `B`. This file restates it with coefficients in `R`, where `R ≃ ℬ 0`, in the
forms that the blueprint displays in its first section.

* For each `p ≥ 0` and each weight `w`, `H^{p, w}(U_𝒜) ≃ OS_R^p(𝒜) ⊗[R] B_{w - p}`, canonically, and
  these groups vanish for `p < 0` and for `p > dim V`.
* The diagonal `⨁_{q ≥ 0} H^{q, q}(U_𝒜)` is canonically `OS_R(𝒜)`, as a graded `R`-algebra.
* A logarithmic monomial basis of `C(U_𝒜)` over `B` corresponds to a monomial basis of `OS_B(𝒜)`
  over `B`, and also to a monomial basis of `OS_R(𝒜)` over `R`.

None of this assumes that `R` is nonzero, that `2` is invertible, or that `B` is flat over `R`.
`Examples/Ordinary` instantiates the statements at `R = ℤ`, at `R = ZMod 2` and at the zero ring.

## Main definitions

* `OrdinaryTheory.realizationOverR 𝒜 : OS_R(𝒜) →ₐ[R] C(U_𝒜)`: the realization map with coefficients
  in `R`, which is injective by `OrdinaryTheory.injective_realizationOverR`.
* `OrdinaryTheory.ordinaryComponentEquiv 𝒜 p w : OS_R^p(𝒜) ⊗[R] B_{w - p} ≃ₗ[R] H^{p, w}(U_𝒜)`.
* `OrdinaryTheory.degreeEquiv 𝒜 q : OS_R^q(𝒜) ≃ₗ[R] H^{q, q}(U_𝒜)`.
* `OrdinaryTheory.diagonalEquiv 𝒜 : OS_R(𝒜) ≃ₐ[R] ⨁ q : ℕ, H^{q, q}(U_𝒜)`, where the summand is
  `diagonalGrading (T.grading (complement 𝒜)) q`.
* For a logarithmic monomial basis `b`:
  - `LogMonomialBasis.osBasis`, the monomial basis of `OS_B(𝒜)`;
  - `LogMonomialBasis.osBasisOverR`, the monomial basis of `OS_R(𝒜)`;
  - `LogMonomialBasis.degreeBasis`, its part in degree `q`;
  - `LogMonomialBasis.diagonalBasis`, the basis of `H^{q, q}(U_𝒜)`;
  - `LogMonomialBasis.gradingEquiv`, which says that `H^{p, w}(U_𝒜)` is free over `B_{w - p}` on the
    words of length `p`.

## Main results

* `cor:ordinary`: the definitions above, with `OrdinaryTheory.coe_ordinaryComponentEquiv_tmul`,
  `OrdinaryTheory.grading_complement_eq_bot`, `OrdinaryTheory.degree_eq_bot_of_finrank_lt`,
  `OrdinaryTheory.coeAlgHom_diagonalEquiv`, `OrdinaryTheory.coe_diagonalEquiv_apply`,
  `OrdinaryTheory.diagonalEquiv_of_mem_degree` and the generator lemmas
  `OrdinaryTheory.diagonalEquiv_generator_zeroLocus` and
  `OrdinaryTheory.diagonalEquiv_generator_of_isEquation`.
* `thm:betti`, the part about cohomology:
  `OrdinaryTheory.nonempty_grading_linearEquiv_bettiNumber`,
  `OrdinaryTheory.nonempty_basis_grading_bettiNumber`,
  `OrdinaryTheory.nonempty_basis_degree_bettiNumber`.

## Implementation notes

**The total ring and the diagonal.** `OrdinaryTheory.affineEquiv` is the stronger statement. The
diagonal is deduced from it, and the two are compared by `coeAlgHom_diagonalEquiv`: the embedding of
the direct sum in `C(U_𝒜)` sends `diagonalEquiv 𝒜 x` to the realization of the image of `x` in
`OS_B(𝒜)`.

**Why `R` and `B` stay separate.** At `R = B`, the object `T.C.obj A` has two `B`-algebra
structures, which agree only propositionally. The statements here are stated with `R` and `B`
separate, so they use the structure `T.algebra` throughout. See "The case `R = B`" in
`Cohomology/Axioms`.

**The case `R = ℤ`.** The same happens at `R = ℤ`, since `T.algebra` is a field and the object also
has the canonical `ℤ`-algebra structure of a ring. Everything here specializes and applies to
elements, including `map_add`, `map_zsmul` and the `simp` lemmas. A literal `≃ₗ[ℤ]` or `≃ₐ[ℤ]` picks
the canonical structure on the target, so it does not match, and neither does a function such as
`LinearEquiv.toAddEquiv` that searches for a `ℤ`-module structure. Use a coercion, as in
`AddEquiv.toIntLinearEquiv (T.ordinaryComponentEquiv 𝒜 p w : _ ≃+ _)` and
`RingEquiv.toIntAlgEquiv (T.diagonalEquiv 𝒜 : _ ≃+* _)`, which `Examples/Ordinary` tests.

**Injectivity of `OS_R → OS_B`.** This is `OrdinaryTheory.injective_coefficientMap`. It uses no
flatness: the map `R → B` is split over `R` by the projection to `ℬ 0`, which is what the component
equivalence at `(q, q)` encodes.

**Bases.** `exists_logMonomialBasis` gives a basis over `B`. Its homogeneous pieces are extracted by
`homogeneousBasisEquiv` in `Grading/Diagonal`: an element of bidegree `(p, w)` has coordinates of
weight `w - p` on the words of length `p`, and zero coordinates on other words.

## Blueprint

`cor:ordinary`, the direct sum decomposition and the basis of the diagonal in `thm:betti`.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum Module
open scoped TensorProduct
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon

namespace OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {𝒜 : Arrangement k V}

/-! ### The realization map with coefficients in `R` -/

section OverR

variable (𝒜) in
/-- The realization map `OS_R(𝒜) → C(U_𝒜)` with coefficients in `R`, the algebra map sending the
generator `e_H` to the logarithm of any equation of `H`. It is the composite of the coefficient map
with `Φ_𝒜`, and it is injective by `injective_realizationOverR`.

Blueprint: `cor:ordinary`. -/
def realizationOverR : OSAlgebra R 𝒜 →ₐ[R] T.C.obj (complement 𝒜) :=
  ((T.realization 𝒜).restrictScalars R).comp (coefficientMap R B 𝒜)

/-- The realization map with coefficients in `R` factors through the structure theorem. -/
theorem realizationOverR_apply (x : OSAlgebra R 𝒜) :
    T.realizationOverR 𝒜 x = T.affineEquiv 𝒜 (coefficientMap R B 𝒜 x) :=
  rfl

/-- The realization map with coefficients in `R` sends a generator to the logarithm of the chosen
equation of its hyperplane. `realizationOverR_generator_of_isEquation` is the same formula for any
equation. -/
@[simp]
theorem realizationOverR_generator (H : 𝒜) :
    T.realizationOverR 𝒜 (generator R 𝒜 H) = T.logClass (equationUnit 𝒜 H) := by
  rw [realizationOverR_apply, coefficientMap_generator, affineEquiv_generator]

/-- The realization map with coefficients in `R` sends a generator to the logarithm of **any**
equation of its hyperplane. Since `f` is not on the left, `simp` needs the equation to be given.

Blueprint: `cor:ordinary`. -/
theorem realizationOverR_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    T.realizationOverR 𝒜 (generator R 𝒜 H) = T.logClass (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [realizationOverR_apply, coefficientMap_generator, T.affineEquiv_generator_of_isEquation H hf]

/-- The generator formula for a label presented by an equation, as `affineEquiv_generator_zeroLocus`
is for `affineEquiv`. Here `f` is on the left, so `simp` uses this with no further input.

Blueprint: `cor:ordinary`. -/
@[simp high]
theorem realizationOverR_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.realizationOverR 𝒜 (generator R 𝒜 ⟨zeroLocus f, hf⟩) =
      T.logClass (complementUnit 𝒜 f (.of_mem hf)) := by
  rw [realizationOverR_apply, coefficientMap_generator, affineEquiv_generator_zeroLocus]

/-- The realization map with coefficients in `R` sends a word to its logarithmic monomial. -/
@[simp high]
theorem realizationOverR_word (I : List 𝒜) :
    T.realizationOverR 𝒜 (word (generator R 𝒜) I) = T.logMonomial 𝒜 I := by
  rw [realizationOverR_apply, coefficientMap_word, affineEquiv_word]

/-- The realization map with coefficients in `R` sends degree `q` to the diagonal piece `(q, q)`. -/
theorem realizationOverR_mem_grading {q : ℕ} {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 q) :
    T.realizationOverR 𝒜 x ∈ T.grading (complement 𝒜) ((q : ℤ), (q : ℤ)) :=
  T.affineEquiv_mem_grading_iff.2 (coefficientMap_mem_bigrading 𝒜 ℬ hx)

end OverR

/-! ### `cor:ordinary`: the groups `H^{p, w}` -/

section Components

variable (𝒜) in
/-- **The ordinary groups.** The canonical isomorphism `OS_R^p(𝒜) ⊗[R] B_{w - p} ≃ H^{p, w}(U_𝒜)`,
which sends `x ⊗ b` to `b • Φ(x)`, by `coe_ordinaryComponentEquiv_tmul`. It holds for all `p : ℕ`,
and both sides vanish for `p > dim V`, by `grading_complement_eq_bot` and
`degree_eq_bot_of_finrank_lt`. The groups with `p < 0` vanish by `grading_complement_eq_bot`.

This requires no flatness and no invertibility of `2`, and `R` can be `ℤ`, `ZMod 2` or the zero
ring.

Blueprint: `cor:ordinary`. -/
def ordinaryComponentEquiv (p : ℕ) (w : ℤ) :
    degree R 𝒜 p ⊗[R] ℬ (w - p) ≃ₗ[R] T.grading (complement 𝒜) ((p : ℤ), w) :=
  bigradingComponentEquiv 𝒜 ℬ p w ≪≫ₗ T.affineComponentEquiv 𝒜 ((p : ℤ), w)

/-- The isomorphism of `ordinaryComponentEquiv` sends `x ⊗ b` to `b • Φ(x)`.

Blueprint: `cor:ordinary`. -/
@[simp]
theorem coe_ordinaryComponentEquiv_tmul (p : ℕ) (w : ℤ) (x : degree R 𝒜 p) (b : ℬ (w - p)) :
    (T.ordinaryComponentEquiv 𝒜 p w (x ⊗ₜ[R] b) : T.C.obj (complement 𝒜)) =
      (b : B) • T.realizationOverR 𝒜 x := by
  simp [ordinaryComponentEquiv, realizationOverR_apply]

/-- The groups `H^{p, w}(U_𝒜)` vanish outside `0 ≤ p ≤ dim V`.

Blueprint: `cor:ordinary`. -/
theorem grading_complement_eq_bot {p w : ℤ} (hp : p < 0 ∨ (finrank k V : ℤ) < p) :
    T.grading (complement 𝒜) (p, w) = ⊥ :=
  (Submodule.eq_bot_iff _).2 (T.bounded 𝒜 p w hp)

variable (𝒜) in
/-- The diagonal piece: `OS_R^q(𝒜) ≃ H^{q, q}(U_𝒜)`, given by the realization map. This is
`ordinaryComponentEquiv` at `w = q`, with `B₀ ≃ R` from `gradeZeroEquiv`.

Blueprint: `cor:ordinary`. -/
def degreeEquiv (q : ℕ) :
    degree R 𝒜 q ≃ₗ[R] T.grading (complement 𝒜) ((q : ℤ), (q : ℤ)) :=
  (TensorProduct.rid R _).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R _)
      (T.gradeZeroEquiv.toLinearEquiv ≪≫ₗ LinearEquiv.ofEq _ _ (by rw [sub_self])) ≪≫ₗ
    T.ordinaryComponentEquiv 𝒜 q q

/-- The equivalence of the diagonal piece is the realization map. -/
@[simp]
theorem coe_degreeEquiv_apply (q : ℕ) (x : degree R 𝒜 q) :
    (T.degreeEquiv 𝒜 q x : T.C.obj (complement 𝒜)) = T.realizationOverR 𝒜 x := by
  simp [degreeEquiv]

variable (𝒜) in
/-- The realization map with coefficients in `R` restricts to a bijection from degree `q` to the
diagonal piece `(q, q)`. -/
theorem bijOn_realizationOverR (q : ℕ) :
    Set.BijOn (T.realizationOverR 𝒜) (degree R 𝒜 q)
      (T.grading (complement 𝒜) ((q : ℤ), (q : ℤ))) := by
  refine ⟨fun x hx ↦ T.realizationOverR_mem_grading hx, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · have h : T.degreeEquiv 𝒜 q ⟨x, hx⟩ = T.degreeEquiv 𝒜 q ⟨y, hy⟩ := by
      ext
      simpa using hxy
    exact congrArg Subtype.val ((T.degreeEquiv 𝒜 q).injective h)
  · refine ⟨(T.degreeEquiv 𝒜 q).symm ⟨y, hy⟩, Subtype.coe_prop _, ?_⟩
    rw [← coe_degreeEquiv_apply, LinearEquiv.apply_symm_apply]

variable (𝒜) in
/-- The realization map with coefficients in `R` is injective. This is the form of `thm:affine` over
`R`: it uses `R ≃ ℬ 0`, and no flatness.

Blueprint: `cor:ordinary`. -/
theorem injective_realizationOverR : Function.Injective (T.realizationOverR 𝒜) :=
  injective_of_forall_bijOn (degree R 𝒜) (T.bijOn_realizationOverR 𝒜)

include T in
variable (𝒜) in
/-- The coefficient map `OS_R(𝒜) → OS_B(𝒜)` is injective. -/
theorem injective_coefficientMap : Function.Injective (coefficientMap R B 𝒜) := fun x y h ↦
  T.injective_realizationOverR 𝒜 (by rw [realizationOverR_apply, realizationOverR_apply, h])

include T in
/-- The presentation vanishes above the dimension of `V`.

Blueprint: `cor:ordinary`. -/
theorem degree_eq_bot_of_finrank_lt {q : ℕ} (hq : finrank k V < q) : degree R 𝒜 q = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hx ↦ T.injective_realizationOverR 𝒜 <| by
    rw [map_zero]
    exact T.eq_zero_of_mem_grading_of_finrank_lt 𝒜 (by exact_mod_cast hq)
      (T.realizationOverR_mem_grading hx)

end Components

/-! ### `cor:ordinary`: the diagonal -/

section Diagonal

/-- A logarithm lies in the diagonal piece of degree one. -/
theorem logClass_mem_diagonalGrading {A : SmoothAlg k} (u : Aˣ) :
    T.logClass u ∈ diagonalGrading (T.grading A) 1 := by
  simpa using T.logClass_mem_grading u

/-- A logarithmic monomial lies in the diagonal piece given by its length. -/
theorem logMonomial_mem_diagonalGrading (I : List 𝒜) :
    T.logMonomial 𝒜 I ∈ diagonalGrading (T.grading (complement 𝒜)) I.length :=
  T.logMonomial_mem_grading I

variable (𝒜) in
/-- **The diagonal theorem.** The canonical isomorphism of graded `R`-algebras
`OS_R(𝒜) ≃ ⨁_{q ≥ 0} H^{q, q}(U_𝒜)`, which sends a generator `e_H` to the logarithm of any equation
of `H`. The summand `diagonalGrading (T.grading (complement 𝒜)) q` is `H^{q, q}(U_𝒜)`, and it is
Mathlib's direct sum of a graded family of submodules, with its multiplication.

It sends degree `q` to the summand of degree `q`, by `coe_diagonalEquiv_apply` and
`diagonalEquiv_of_mem_degree`. It is compared with the structure theorem by
`coeAlgHom_diagonalEquiv`. The formula on generators is `diagonalEquiv_generator_of_isEquation`,
which says that it does not depend on the equations.

It holds for every coefficient ring `R`, including `ℤ`, `ZMod 2` and the zero ring.

Blueprint: `cor:ordinary`, and the principal theorem in the first section of the blueprint. -/
def diagonalEquiv :
    OSAlgebra R 𝒜 ≃ₐ[R] ⨁ q : ℕ, diagonalGrading (T.grading (complement 𝒜)) q :=
  diagonalAlgEquiv (degree R 𝒜) (T.bijOn_realizationOverR 𝒜)

/-- The embedding of the diagonal in `C(U_𝒜)` sends the image of `x` to the realization of `x`. This
characterizes `diagonalEquiv`, by `injective_coeAlgHom_diagonalGrading`.

Blueprint: `cor:ordinary`. -/
@[simp]
theorem coeAlgHom_diagonalEquiv (x : OSAlgebra R 𝒜) :
    coeAlgHom (diagonalGrading (T.grading (complement 𝒜))) (T.diagonalEquiv 𝒜 x) =
      T.realizationOverR 𝒜 x :=
  coeAlgHom_diagonalAlgEquiv _ _ x

/-- The component of degree `q` of the image of `x` is the realization of the component of degree
`q` of `x`. This says that the isomorphism is graded.

Blueprint: `cor:ordinary`. -/
theorem coe_diagonalEquiv_apply (x : OSAlgebra R 𝒜) (q : ℕ) :
    (T.diagonalEquiv 𝒜 x q : T.C.obj (complement 𝒜)) =
      T.realizationOverR 𝒜 (decompose (degree R 𝒜) x q) :=
  rfl

/-- On an element of degree `q`, the isomorphism is the realization, in the summand of degree `q`.

Blueprint: `cor:ordinary`. -/
theorem diagonalEquiv_of_mem_degree {q : ℕ} {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 q) :
    T.diagonalEquiv 𝒜 x = of _ q ⟨T.realizationOverR 𝒜 x, T.realizationOverR_mem_grading hx⟩ :=
  diagonalAlgEquiv_of_mem _ _ hx

/-- The inverse of the isomorphism on the summand of degree `q` is the inverse of `degreeEquiv`.

Blueprint: `cor:ordinary`. -/
theorem diagonalEquiv_symm_of (q : ℕ) (y : diagonalGrading (T.grading (complement 𝒜)) q) :
    (T.diagonalEquiv 𝒜).symm (of _ q y) =
      (T.degreeEquiv 𝒜 q).symm ⟨y, mem_diagonalGrading.1 y.2⟩ := by
  rw [AlgEquiv.symm_apply_eq]
  refine injective_coeAlgHom_diagonalGrading _ ?_
  rw [coeAlgHom_of, coeAlgHom_diagonalEquiv, ← coe_degreeEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The isomorphism sends a generator to the logarithm of **any** equation of its hyperplane, in the
summand of degree one. Since `f` is not on the left, `simp` needs the equation to be given.

Blueprint: `cor:ordinary`. -/
theorem diagonalEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    T.diagonalEquiv 𝒜 (generator R 𝒜 H) =
      of _ 1 ⟨T.logClass (complementUnit 𝒜 f (hf.covers H.2)), T.logClass_mem_diagonalGrading _⟩ :=
  injective_coeAlgHom_diagonalGrading _ <| by
    rw [coeAlgHom_diagonalEquiv, coeAlgHom_of, T.realizationOverR_generator_of_isEquation H hf]

/-- The generator formula for a label presented by an equation. Here `f` is on the left, so `simp`
uses this with no further input.

Blueprint: `cor:ordinary`. -/
@[simp high]
theorem diagonalEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.diagonalEquiv 𝒜 (generator R 𝒜 ⟨zeroLocus f, hf⟩) =
      of _ 1 ⟨T.logClass (complementUnit 𝒜 f (.of_mem hf)), T.logClass_mem_diagonalGrading _⟩ :=
  T.diagonalEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The isomorphism sends a word to its logarithmic monomial, in the summand given by its length. -/
@[simp high]
theorem diagonalEquiv_word (I : List 𝒜) :
    T.diagonalEquiv 𝒜 (word (generator R 𝒜) I) =
      of _ I.length ⟨T.logMonomial 𝒜 I, T.logMonomial_mem_diagonalGrading I⟩ :=
  injective_coeAlgHom_diagonalGrading _ <| by
    rw [coeAlgHom_diagonalEquiv, coeAlgHom_of, realizationOverR_word]

end Diagonal

/-! ### `cor:ordinary` and `thm:betti`: bases -/

namespace LogMonomialBasis

variable {T} (b : T.LogMonomialBasis 𝒜)

/-- The monomial basis of `OS_B(𝒜)` over `B` corresponding to a logarithmic monomial basis: its
vector at an index is the word of that index.

Blueprint: `cor:ordinary`. -/
def osBasis : Basis b.Index B (OSAlgebra B 𝒜) :=
  b.basis.map (T.affineEquiv 𝒜).symm.toLinearEquiv

@[simp]
theorem osBasis_apply (i : b.Index) :
    b.osBasis i = OrlikSolomon.word (generator B 𝒜) (b.word i) := by
  simp [osBasis]

/-- The structure theorem sends the monomial basis of `OS_B(𝒜)` to the logarithmic monomial basis.

Blueprint: `cor:ordinary`. -/
theorem affineEquiv_osBasis (i : b.Index) : T.affineEquiv 𝒜 (b.osBasis i) = b.basis i := by
  simp [osBasis]

/-- The piece `H^{p, w}(U_𝒜)` is free over `B_{w - p}` on the logarithmic monomials of the words of
length `p`: the map sends a class to its coordinates in the basis `b`. This depends on `b`, unlike
`ordinaryComponentEquiv`.

Blueprint: `cor:ordinary`, `thm:betti`. -/
def gradingEquiv (p : ℕ) (w : ℤ) :
    T.grading (complement 𝒜) ((p : ℤ), w) ≃ₗ[R] ({i // (b.word i).length = p} → ℬ (w - p)) :=
  homogeneousBasisEquiv b.basis (fun _ _ _ _ _ hc hx ↦ T.smul_mem_grading hc hx)
    b.basis_mem_grading (add_sub_cancel _ _)

@[simp]
theorem coe_gradingEquiv_apply (p : ℕ) (w : ℤ) (x : T.grading (complement 𝒜) ((p : ℤ), w))
    (i : {i // (b.word i).length = p}) :
    (b.gradingEquiv p w x i : B) = b.basis.repr x i :=
  rfl

@[simp]
theorem coe_gradingEquiv_symm_apply (p : ℕ) (w : ℤ) (c : {i // (b.word i).length = p} → ℬ (w - p)) :
    ((b.gradingEquiv p w).symm c : T.C.obj (complement 𝒜)) =
      ∑ i, (c i : B) • T.logMonomial 𝒜 (b.word i) := by
  simp [gradingEquiv]

/-- The logarithmic monomials of the words of length `q` form an `R`-basis of the diagonal piece
`H^{q, q}(U_𝒜)`, by `B₀ ≃ R`.

Blueprint: `cor:ordinary`, `thm:betti`. -/
def diagonalBasis (q : ℕ) :
    Basis {i // (b.word i).length = q} R (T.grading (complement 𝒜) ((q : ℤ), (q : ℤ))) :=
  homogeneousDiagonalBasis b.basis (fun _ _ _ _ _ hc hx ↦ T.smul_mem_grading hc hx)
    b.basis_mem_grading T.gradeZeroEquiv.toLinearEquiv q

@[simp]
theorem coe_diagonalBasis_apply (q : ℕ) (i : {i // (b.word i).length = q}) :
    (b.diagonalBasis q i : T.C.obj (complement 𝒜)) = T.logMonomial 𝒜 (b.word i) := by
  rw [diagonalBasis, coe_homogeneousDiagonalBasis_apply _ _ _ _ (by simp), b.basis_apply]

/-- The words of length `q` form an `R`-basis of the degree `q` part of `OS_R(𝒜)`.

Blueprint: `cor:ordinary`, `thm:betti`. -/
def degreeBasis (q : ℕ) : Basis {i // (b.word i).length = q} R (degree R 𝒜 q) :=
  (b.diagonalBasis q).map (T.degreeEquiv 𝒜 q).symm

@[simp]
theorem coe_degreeBasis_apply (q : ℕ) (i : {i // (b.word i).length = q}) :
    (b.degreeBasis q i : OSAlgebra R 𝒜) = OrlikSolomon.word (generator R 𝒜) (b.word i) := by
  refine T.injective_realizationOverR 𝒜 ?_
  rw [← coe_degreeEquiv_apply, degreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    coe_diagonalBasis_apply, realizationOverR_word]

/-- The monomial basis of `OS_R(𝒜)` over `R` corresponding to a logarithmic monomial basis: its
vector at an index is the word of that index. So a logarithmic monomial basis over `B` gives a
monomial basis with coefficients in `R`, with the same words.

Blueprint: `cor:ordinary`, `thm:betti`. -/
def osBasisOverR : Basis b.Index R (OSAlgebra R 𝒜) :=
  ((Decomposition.isInternal (degree R 𝒜)).collectedBasis b.degreeBasis).reindex
    (Equiv.sigmaFiberEquiv fun i ↦ (b.word i).length)

@[simp]
theorem osBasisOverR_apply (i : b.Index) :
    b.osBasisOverR i = OrlikSolomon.word (generator R 𝒜) (b.word i) := by
  simp [osBasisOverR, DirectSum.IsInternal.collectedBasis_coe]

/-- The realization map sends the monomial basis of `OS_R(𝒜)` to the logarithmic monomial basis.

Blueprint: `cor:ordinary`. -/
theorem realizationOverR_osBasisOverR (i : b.Index) :
    T.realizationOverR 𝒜 (b.osBasisOverR i) = b.basis i := by
  simp

end LogMonomialBasis

/-- Each `H^{p, w}(U_𝒜)` is a direct sum of `b_p(𝒜)` copies of `B_{w - p}`. The isomorphism depends
on a choice of basis and is not canonical: `ordinaryComponentEquiv` is the canonical statement.

Blueprint: `thm:betti`. -/
theorem nonempty_grading_linearEquiv_bettiNumber (𝒜 : Arrangement k V) (p : ℕ) (w : ℤ) :
    Nonempty (T.grading (complement 𝒜) ((p : ℤ), w) ≃ₗ[R] (Fin (𝒜.bettiNumber p) → ℬ (w - p))) :=
  let ⟨b, hb⟩ := T.exists_logMonomialBasis 𝒜
  ⟨b.gradingEquiv p w ≪≫ₗ
    LinearEquiv.funCongrLeft R (ℬ (w - p)) (Fintype.equivFinOfCardEq (hb p)).symm⟩

/-- The ordinary diagonal piece `H^{q, q}(U_𝒜)` has an `R`-basis of cardinality `b_q(𝒜)`.

Blueprint: `thm:betti`. -/
theorem nonempty_basis_grading_bettiNumber (𝒜 : Arrangement k V) (q : ℕ) :
    Nonempty (Basis (Fin (𝒜.bettiNumber q)) R (T.grading (complement 𝒜) ((q : ℤ), (q : ℤ)))) :=
  let ⟨b, hb⟩ := T.exists_logMonomialBasis 𝒜
  ⟨(b.diagonalBasis q).reindex (Fintype.equivFinOfCardEq (hb q))⟩

include T in
/-- The degree `q` part of `OS_R(𝒜)` has an `R`-basis of cardinality `b_q(𝒜)`.

Blueprint: `thm:betti`. -/
theorem nonempty_basis_degree_bettiNumber (𝒜 : Arrangement k V) (q : ℕ) :
    Nonempty (Basis (Fin (𝒜.bettiNumber q)) R (degree R 𝒜 q)) :=
  let ⟨b, hb⟩ := T.exists_logMonomialBasis 𝒜
  ⟨(b.degreeBasis q).reindex (Fintype.equivFinOfCardEq (hb q))⟩

end OrdinaryTheory

end OrlikSolomon
