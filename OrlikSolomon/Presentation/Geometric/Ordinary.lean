/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Combinatorics.Moebius
public import OrlikSolomon.Presentation.Geometric.Affine
public import OrlikSolomon.Presentation.Ordinary

/-!
# Ordinary groups, the diagonal and bases of an arrangement complement on schemes

The geometric structure theorem `Geometric.OrdinaryTheory.affineEquiv` is an equivalence with the
presentation over the whole coefficient ring `B`. This file restates it with coefficients in `R`,
where `R ≃ ℬ 0`, for the complement `U_𝒜` as an open subscheme of affine space, in the forms of
`cor:ordinary` and `thm:betti`.

* For each `p ≥ 0` and each weight `w`, `H^{p, w}(U_𝒜) ≃ OS_R^p(𝒜) ⊗[R] B_{w - p}`, canonically,
  and these groups vanish for `p < 0` and for `p > dim V`.
* The diagonal `⨁_{q ≥ 0} H^{q, q}(U_𝒜)` is canonically `OS_R(𝒜)`, as a graded `R`-algebra.
* `C(U_𝒜)` has a basis of logarithmic monomials with exactly `b_q(𝒜)` words of length `q`, and
  `H^{q, q}(U_𝒜)` has an `R`-basis with `b_q(𝒜)` elements, where `b_q(𝒜)` is given by the Möbius
  function of the intersection poset.

Each statement is the existing one for `T.toAlgebraic`, transported along the comparison
`s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` by `transportAffineDevelopment`. None of this assumes that `R` is nonzero,
that `2` is invertible, that `B` is flat over `R`, or that `U_𝒜` has a rational point.

## Main definitions

* `Geometric.OrdinaryTheory.realizationOverR 𝒜 : OS_R(𝒜) →ₐ[R] C(U_𝒜)`.
* `Geometric.OrdinaryTheory.ordinaryComponentEquiv 𝒜 p w :
  OS_R^p(𝒜) ⊗[R] B_{w - p} ≃ₗ[R] H^{p, w}(U_𝒜)`.
* `Geometric.OrdinaryTheory.degreeEquiv 𝒜 q : OS_R^q(𝒜) ≃ₗ[R] H^{q, q}(U_𝒜)`.
* `Geometric.OrdinaryTheory.diagonalEquiv 𝒜 : OS_R(𝒜) ≃ₐ[R] ⨁ q : ℕ, H^{q, q}(U_𝒜)`.

## Main results

* `cor:ordinary`: the definitions above, with `coe_ordinaryComponentEquiv_tmul`,
  `grading_complement_eq_bot`, `coeAlgHom_diagonalEquiv`, `diagonalEquiv_of_mem_degree` and
  `diagonalEquiv_generator_of_isEquation`.
* `thm:cohom-basis` and `thm:betti`: `exists_basis_logMonomial`,
  `nonempty_grading_linearEquiv_bettiNumber`, `nonempty_basis_grading_bettiNumber`, and the Möbius
  form `exists_basis_grading_moebius`.

## Implementation notes

As in `Presentation/Ordinary`, `R` and `B` stay separate, so that the statements use the specified
`R`-algebra structure `T.algebra` even when specialized to `R = B`; at `R = ℤ` convert the
equivalences through `AddEquiv.toIntLinearEquiv` and `RingEquiv.toIntAlgEquiv`. Over the zero ring
the basis and module statements hold for every count, so they do not determine `b_q(𝒜)`; the word
count of `exists_basis_logMonomial` comes from the recursive construction.

## Blueprint

`thm:geo-affine`: its component and diagonal forms, vanishing bounds, bases and Betti numbers.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Module
open scoped TensorProduct
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.Geometric.OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {𝒜 : Arrangement k V}

/-! ### The realization map with coefficients in `R` -/

section OverR

variable (𝒜) in
/-- The realization map `OS_R(𝒜) → C(U_𝒜)` with coefficients in `R`: the algebra map sending the
generator `e_H` to the logarithmic class of the restriction of any equation of `H`. It is the
coefficient map followed by `Φ_𝒜`, and it is injective by `injective_realizationOverR`.

Blueprint: `thm:geo-affine`. -/
def realizationOverR : OSAlgebra R 𝒜 →ₐ[R] T.obj (D.complement 𝒜) :=
  ((T.affineEquiv 𝒜 : OSAlgebra B 𝒜 →ₐ[B] T.obj (D.complement 𝒜)).restrictScalars R).comp
    (coefficientMap R B 𝒜)

/-- The realization map with coefficients in `R` factors through the structure theorem. -/
theorem realizationOverR_apply (x : OSAlgebra R 𝒜) :
    T.realizationOverR 𝒜 x = T.affineEquiv 𝒜 (coefficientMap R B 𝒜 x) :=
  rfl

/-- The realization map with coefficients in `R` is the existing one for `T.toAlgebraic`, followed
by pullback along `s_𝒜`. -/
theorem realizationOverR_eq_pull (x : OSAlgebra R 𝒜) :
    T.realizationOverR 𝒜 x =
      T.pull (D.complementIsoSpec 𝒜).hom (T.toAlgebraic.realizationOverR 𝒜 x) :=
  rfl

/-- The realization map with coefficients in `R` sends a generator to the logarithmic class of the
restriction of **any** equation of its hyperplane.

Blueprint: `thm:geo-affine`. -/
theorem realizationOverR_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    T.realizationOverR 𝒜 (generator R 𝒜 H) = T.logClass (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [realizationOverR_apply, coefficientMap_generator, T.affineEquiv_generator_of_isEquation H hf]

/-- The generator formula for a label presented by an equation. Here `f` is on the left, so `simp`
uses this with no further input. -/
@[simp high]
theorem realizationOverR_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.realizationOverR 𝒜 (generator R 𝒜 ⟨zeroLocus f, hf⟩) =
      T.logClass (complementUnit 𝒜 f (.of_mem hf)) :=
  T.realizationOverR_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The realization map with coefficients in `R` sends a word to its logarithmic monomial. -/
@[simp high]
theorem realizationOverR_word (I : List 𝒜) :
    T.realizationOverR 𝒜 (word (generator R 𝒜) I) = T.logMonomial 𝒜 I := by
  rw [realizationOverR_apply, coefficientMap_word, affineEquiv_word]

/-- The realization map with coefficients in `R` sends degree `q` to the diagonal piece `(q, q)`. -/
theorem realizationOverR_mem_grading {q : ℕ} {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 q) :
    T.realizationOverR 𝒜 x ∈ T.grading (D.complement 𝒜) ((q : ℤ), (q : ℤ)) :=
  T.affineEquiv_mem_grading_iff.2 (coefficientMap_mem_bigrading 𝒜 ℬ hx)

variable (𝒜) in
/-- The realization map with coefficients in `R` restricts to a bijection from degree `q` to the
diagonal piece `(q, q)`. -/
theorem bijOn_realizationOverR (q : ℕ) :
    Set.BijOn (T.realizationOverR 𝒜) (degree R 𝒜 q)
      (T.grading (D.complement 𝒜) ((q : ℤ), (q : ℤ))) :=
  (bijOn_transportAffineDevelopment T _ _).comp (T.toAlgebraic.bijOn_realizationOverR 𝒜 q)

variable (𝒜) in
/-- The realization map with coefficients in `R` is injective. It uses `R ≃ ℬ 0`, and no
flatness. -/
theorem injective_realizationOverR : Function.Injective (T.realizationOverR 𝒜) :=
  injective_of_forall_bijOn (degree R 𝒜) (T.bijOn_realizationOverR 𝒜)

end OverR

/-! ### The groups `H^{p, w}` -/

section Components

variable (𝒜) in
/-- **The ordinary groups.** The canonical isomorphism `OS_R^p(𝒜) ⊗[R] B_{w - p} ≃ H^{p, w}(U_𝒜)`,
which sends `x ⊗ b` to `b • Φ(x)`, by `coe_ordinaryComponentEquiv_tmul`. Both sides vanish for
`p > dim V`, and the groups with `p < 0` vanish, by `grading_complement_eq_bot`. No flatness and no
invertibility of `2` is needed, and `R` can be `ℤ`, `ZMod 2` or the zero ring.

Blueprint: `thm:geo-affine`. -/
def ordinaryComponentEquiv (p : ℕ) (w : ℤ) :
    degree R 𝒜 p ⊗[R] ℬ (w - p) ≃ₗ[R] T.grading (D.complement 𝒜) ((p : ℤ), w) :=
  bigradingComponentEquiv 𝒜 ℬ p w ≪≫ₗ T.affineComponentEquiv 𝒜 ((p : ℤ), w)

/-- The isomorphism of `ordinaryComponentEquiv` sends `x ⊗ b` to `b • Φ(x)`.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem coe_ordinaryComponentEquiv_tmul (p : ℕ) (w : ℤ) (x : degree R 𝒜 p) (b : ℬ (w - p)) :
    (T.ordinaryComponentEquiv 𝒜 p w (x ⊗ₜ[R] b) : T.obj (D.complement 𝒜)) =
      (b : B) • T.realizationOverR 𝒜 x := by
  simp [ordinaryComponentEquiv, realizationOverR_apply]

/-- **Vanishing.** The groups `H^{p, w}(U_𝒜)` vanish outside `0 ≤ p ≤ dim V`.

Blueprint: `thm:geo-affine`. -/
theorem grading_complement_eq_bot {p w : ℤ} (hp : p < 0 ∨ (finrank k V : ℤ) < p) :
    T.grading (D.complement 𝒜) (p, w) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦
    (map_eq_zero_iff _ (transportAffineDevelopment T (D.complementIsoSpec 𝒜)).symm.injective).1 ?_
  have h := (transportAffineDevelopment_symm_mem_grading_iff T (D.complementIsoSpec 𝒜)).2 hy
  rwa [T.toAlgebraic.grading_complement_eq_bot hp, Submodule.mem_bot] at h

include T in
/-- The presentation vanishes above the dimension of `V`.

Blueprint: `thm:geo-affine`. -/
theorem degree_eq_bot_of_finrank_lt {q : ℕ} (hq : finrank k V < q) : degree R 𝒜 q = ⊥ :=
  T.toAlgebraic.degree_eq_bot_of_finrank_lt hq

variable (𝒜) in
/-- The diagonal piece: `OS_R^q(𝒜) ≃ H^{q, q}(U_𝒜)`, given by the realization map.

Blueprint: `thm:geo-affine`. -/
def degreeEquiv (q : ℕ) :
    degree R 𝒜 q ≃ₗ[R] T.grading (D.complement 𝒜) ((q : ℤ), (q : ℤ)) :=
  diagonalPieceEquiv (degree R 𝒜) (T.bijOn_realizationOverR 𝒜) q

@[simp]
theorem coe_degreeEquiv_apply (q : ℕ) (x : degree R 𝒜 q) :
    (T.degreeEquiv 𝒜 q x : T.obj (D.complement 𝒜)) = T.realizationOverR 𝒜 x :=
  rfl

end Components

/-! ### The diagonal -/

section Diagonal

/-- A logarithmic class lies in the diagonal piece of degree one. -/
theorem logClass_mem_diagonalGrading {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass u ∈ diagonalGrading (T.grading X) 1 := by
  simpa using T.logClass_mem_grading u

variable (𝒜) in
/-- **The diagonal theorem.** The canonical isomorphism of graded `R`-algebras
`OS_R(𝒜) ≃ ⨁_{q ≥ 0} H^{q, q}(U_𝒜)` for the complement as an open subscheme, which sends a
generator `e_H` to the logarithmic class of the restriction of any equation of `H`. It sends degree
`q` to the summand of degree `q` (`diagonalEquiv_of_mem_degree`), and it is compared with the
structure theorem by `coeAlgHom_diagonalEquiv`. It holds for every coefficient ring `R`, including
`ℤ`, `ZMod 2` and the zero ring.

Blueprint: `thm:geo-affine`. -/
def diagonalEquiv :
    OSAlgebra R 𝒜 ≃ₐ[R] ⨁ q : ℕ, diagonalGrading (T.grading (D.complement 𝒜)) q :=
  diagonalAlgEquiv (degree R 𝒜) (T.bijOn_realizationOverR 𝒜)

/-- The embedding of the diagonal in `C(U_𝒜)` sends the image of `x` to the realization of `x`.
This characterizes `diagonalEquiv`, by `injective_coeAlgHom_diagonalGrading`.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem coeAlgHom_diagonalEquiv (x : OSAlgebra R 𝒜) :
    coeAlgHom (diagonalGrading (T.grading (D.complement 𝒜))) (T.diagonalEquiv 𝒜 x) =
      T.realizationOverR 𝒜 x :=
  coeAlgHom_diagonalAlgEquiv _ _ x

/-- The component of degree `q` of the image of `x` is the realization of the component of degree
`q` of `x`. -/
theorem coe_diagonalEquiv_apply (x : OSAlgebra R 𝒜) (q : ℕ) :
    (T.diagonalEquiv 𝒜 x q : T.obj (D.complement 𝒜)) =
      T.realizationOverR 𝒜 (decompose (degree R 𝒜) x q) :=
  coe_diagonalAlgEquiv_apply _ _ x q

/-- On an element of degree `q`, the isomorphism is the realization, in the summand of degree `q`.

Blueprint: `thm:geo-affine`. -/
theorem diagonalEquiv_of_mem_degree {q : ℕ} {x : OSAlgebra R 𝒜} (hx : x ∈ degree R 𝒜 q) :
    T.diagonalEquiv 𝒜 x = of _ q ⟨T.realizationOverR 𝒜 x, T.realizationOverR_mem_grading hx⟩ :=
  diagonalAlgEquiv_of_mem _ _ hx

/-- The isomorphism sends a generator to the logarithmic class of the restriction of **any**
equation of its hyperplane, in the summand of degree one.

Blueprint: `thm:geo-affine`. -/
theorem diagonalEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    T.diagonalEquiv 𝒜 (generator R 𝒜 H) =
      of _ 1 ⟨T.logClass (complementUnit 𝒜 f (hf.covers H.2)),
        T.logClass_mem_diagonalGrading _⟩ :=
  injective_coeAlgHom_diagonalGrading _ <| by
    rw [coeAlgHom_diagonalEquiv, coeAlgHom_of, T.realizationOverR_generator_of_isEquation H hf]

/-- The generator formula for a label presented by an equation. Here `f` is on the left, so `simp`
uses this with no further input. -/
@[simp high]
theorem diagonalEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.diagonalEquiv 𝒜 (generator R 𝒜 ⟨zeroLocus f, hf⟩) =
      of _ 1 ⟨T.logClass (complementUnit 𝒜 f (.of_mem hf)), T.logClass_mem_diagonalGrading _⟩ :=
  T.diagonalEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

end Diagonal

/-! ### Bases and Betti numbers -/

section Bases

variable (𝒜) in
/-- **Logarithmic monomial bases.** `C(U_𝒜)` has a basis over `B` of logarithmic monomials of words
of length at most `dim V`, with exactly `b_q(𝒜)` words of length `q`. It is the recursive basis of
`thm:cohom-basis` for `T.toAlgebraic`, transported along `s_𝒜`. Over the zero ring such bases
exist for every count; the count here comes from the recursion.

Blueprint: `thm:geo-affine`. -/
theorem exists_basis_logMonomial :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → List 𝒜) (b : Basis ι B (T.obj (D.complement 𝒜))),
      (∀ i, b i = T.logMonomial 𝒜 (I i)) ∧ (∀ i, (I i).length ≤ finrank k V) ∧
        ∀ q, Fintype.card {i // (I i).length = q} = 𝒜.bettiNumber q := by
  obtain ⟨b, hb⟩ := T.toAlgebraic.exists_logMonomialBasis 𝒜
  refine ⟨b.Index, inferInstance, b.word,
    b.basis.map (transportAffineDevelopment T (D.complementIsoSpec 𝒜)).toLinearEquiv,
    fun i ↦ ?_, b.length_le, hb⟩
  rw [Basis.map_apply, AlgEquiv.toLinearEquiv_apply, b.basis_apply,
    transportAffineDevelopment_apply, pull_complementIsoSpec_logMonomial]

variable (𝒜) in
/-- Each `H^{p, w}(U_𝒜)` is a direct sum of `b_p(𝒜)` copies of `B_{w - p}`. The isomorphism depends
on a choice of basis and is not canonical: `ordinaryComponentEquiv` is the canonical statement.

Blueprint: `thm:geo-affine`. -/
theorem nonempty_grading_linearEquiv_bettiNumber (p : ℕ) (w : ℤ) :
    Nonempty (T.grading (D.complement 𝒜) ((p : ℤ), w) ≃ₗ[R]
      (Fin (𝒜.bettiNumber p) → ℬ (w - p))) :=
  let ⟨e⟩ := T.toAlgebraic.nonempty_grading_linearEquiv_bettiNumber 𝒜 p w
  ⟨(transportAffineDevelopmentComponentEquiv T (D.complementIsoSpec 𝒜) _).symm ≪≫ₗ e⟩

variable (𝒜) in
/-- The ordinary diagonal piece `H^{q, q}(U_𝒜)` has an `R`-basis of cardinality `b_q(𝒜)`.

Blueprint: `thm:geo-affine`. -/
theorem nonempty_basis_grading_bettiNumber (q : ℕ) :
    Nonempty (Basis (Fin (𝒜.bettiNumber q)) R
      (T.grading (D.complement 𝒜) ((q : ℤ), (q : ℤ)))) :=
  let ⟨b⟩ := T.toAlgebraic.nonempty_basis_grading_bettiNumber 𝒜 q
  ⟨b.map (transportAffineDevelopmentComponentEquiv T (D.complementIsoSpec 𝒜) _)⟩

variable (𝒜) in
/-- **The Möbius formula.** `H^{q, q}(U_𝒜)` has an `R`-basis whose cardinality `n` satisfies
`n = (-1)^q ∑_{codim X = q} μ(V, X)`, the sum over the flats of codimension `q` of the poset of
nonempty intersections. Over the zero ring a basis exists for every cardinality.

Blueprint: `thm:geo-affine`, with `lem:mobius`. -/
theorem exists_basis_grading_moebius (q : ℕ) :
    ∃ n : ℕ, (n : ℤ) = (-1 : ℤ) ^ q *
        ∑ X : 𝒜.IntersectionPoset with codim X.carrier = q, X.moebius ∧
      Nonempty (Basis (Fin n) R (T.grading (D.complement 𝒜) ((q : ℤ), (q : ℤ)))) :=
  ⟨𝒜.bettiNumber q, natCast_bettiNumber_eq_sum_moebius 𝒜 q,
    T.nonempty_basis_grading_bettiNumber 𝒜 q⟩

end Bases

end OrlikSolomon.Geometric.OrdinaryTheory
