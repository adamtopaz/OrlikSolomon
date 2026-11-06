/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Combinatorics.Multiplicities
public import OrlikSolomon.Examples.Sanity
public import OrlikSolomon.Presentation.ProjectiveOrdinary

/-!
# Projective cohomology regressions

One projective hyperplane has coefficient-algebra cohomology. A nonempty arrangement of `m`
points of the projective line has polynomial `1 + (m - 1) X`, and its first diagonal cohomology
has a basis indexed by `Fin (m - 1)` over every coefficient ring, including the zero ring.

The example of the three rational points over `F₂` has a complement without rational points.
Its polynomial is still `1 + 2 X`. Bases with the polynomial index size exist for every supplied
theory, including the actual zero theory. Over the zero ring, neither a basis statement nor an
existential word family determines the count: other sizes are possible. The integer polynomial
defines the Betti numbers, and the empty/deletion recursion in the proof supplies a word family
with matching counts. `exists_logMonomialBasis_decone_threePoints_zeroTheory` checks this matching
family in the concrete example. No nonzero theory instance is built.
The integer example checks the documented scalar conversion for the diagonal theorem.

Blueprint: regression example 8 and the projective form of example 7.
-/

@[expose] public section

noncomputable section

open DirectSum Module Polynomial
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.ProjectiveOrdinaryExamples

section DimensionBound

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

private theorem poincare_coeff_above_dimension (𝒜 : Arrangement k V) {q : ℕ}
    (hq : finrank k V < q) : 𝒜.poincarePolynomial.coeff q = 0 := by
  classical
  rw [Arrangement.poincarePolynomial_eq_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro S _
  rw [Polynomial.coeff_C_mul_X_pow]
  exact ite_eq_right (ne_of_lt ((codim_le_finrank _).trans_lt hq)).symm

end DimensionBound

section OneHyperplane

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {P : ProjectiveArrangement k V} [Nonempty P] {ℓ : Dual k V}

/-- Removing a single projective hyperplane gives the coefficient algebra in cohomology. -/
def singleHyperplaneCohomologyEquiv (hℓ : LinearMap.ker ℓ ∈ P)
    (hP : ∀ H ∈ P, H = LinearMap.ker ℓ) : B ≃ₐ[B] T.C.obj (projectiveComplement P) :=
  (T.affineSpaceEquiv (slice ℓ).direction).trans
    (T.C.mapIso (projectiveComplementIsoAffineSpace hℓ hP)).toAlgEquiv.symm

/-- The coefficient equivalence for a single hyperplane is the structural coefficient map. -/
@[simp]
theorem singleHyperplaneCohomologyEquiv_apply (hℓ : LinearMap.ker ℓ ∈ P)
    (hP : ∀ H ∈ P, H = LinearMap.ker ℓ) (b : B) :
    singleHyperplaneCohomologyEquiv T hℓ hP b =
      algebraMap B (T.C.obj (projectiveComplement P)) b := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    (singleHyperplaneCohomologyEquiv T hℓ hP).commutes b

/-- The projective boundary kernel for a single hyperplane is the coefficient algebra. This
checks the projective structure theorem against the affine-space geometry of the complement. -/
def singleHyperplaneProjectiveAlgebraEquiv (hℓ : LinearMap.ker ℓ ∈ P)
    (hP : ∀ H ∈ P, H = LinearMap.ker ℓ) : projectiveAlgebra B P.cone_isCentral ≃ₐ[B] B :=
  (T.projectiveEquiv P).trans (singleHyperplaneCohomologyEquiv T hℓ hP).symm

omit T in
/-- A single projective hyperplane has Poincaré polynomial one. -/
theorem singleHyperplanePolynomial (hℓ : LinearMap.ker ℓ ∈ P)
    (hP : ∀ H ∈ P, H = LinearMap.ker ℓ) : P.poincarePolynomial = 1 := by
  rw [ProjectiveArrangement.poincarePolynomial_eq_decone hℓ,
    ProjectiveArrangement.decone_eq_empty hℓ hP, Arrangement.poincarePolynomial_empty]

end OneHyperplane

section ProjectiveLine

variable {k : Type u} [Field k] (P : ProjectiveArrangement k (Fin 2 → k)) [Nonempty P]

/-- For any nonempty set of `m` distinct points in `P¹`, the Poincaré polynomial is
`1 + (m - 1) X`. This is an integral polynomial identity, independent of a cohomology theory. -/
theorem poincarePolynomial_points :
    P.poincarePolynomial = 1 + Polynomial.C ((P.card : ℤ) - 1) * Polynomial.X := by
  ext q
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
  by_cases hq0 : q = 0
  · subst q
    simp
  by_cases hq1 : q = 1
  · subst q
    simp [ProjectiveArrangement.poincarePolynomial_coeff_one]
  have hq : 1 < q := by omega
  have hz : P.poincarePolynomial.coeff q = 0 := by
    obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
    rw [ProjectiveArrangement.poincarePolynomial_eq_decone hℓ]
    apply poincare_coeff_above_dimension
    have hd := finrank_direction_slice_add_one (ProjectiveArrangement.ne_zero_of_ker_mem hℓ)
    have hdim : finrank k (Fin 2 → k) = 2 := by simp
    omega
  rw [hz]
  simp [hq0, hq1]

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)

/-- The first diagonal group of the complement of `m` points admits a basis indexed by
`Fin (m - 1)`. Over the zero ring this holds for every index size. The polynomial defines the count;
the recursive construction in the proof supplies a matching word family, whose existence alone
also does not determine the count over the zero ring. -/
theorem nonempty_basis_points_grading_one :
    Nonempty (Basis (Fin (P.card - 1)) R
      (T.grading (projectiveComplement P) (1, 1))) :=
  T.nonempty_basis_projective_grading_one P

include T in
/-- The projective diagonal equivalence transports the same indexed basis to degree one of
the projective presentation over `R`. -/
theorem nonempty_basis_points_projective_degree_one :
    Nonempty (Basis (Fin (P.card - 1)) R (projectiveDegree R P.cone_isCentral 1)) := by
  obtain ⟨b⟩ := nonempty_basis_points_grading_one P T
  exact ⟨b.map (T.projectiveDegreeEquiv P 1).symm⟩

end ProjectiveLine

section ThreePoints

open Sanity

/-- The three rational points over `F₂` are a nonempty projective arrangement. -/
instance threePoints_nonempty : Nonempty threePoints :=
  ⟨⟨LinearMap.ker formX, ProjectiveArrangement.ker_mem_ofForms (by simp)⟩⟩

/-- The three equations in the fixture have three distinct kernels. -/
theorem card_threePoints : threePoints.card = 3 := by
  classical
  have hxy : LinearMap.ker formX ≠ LinearMap.ker formY := by
    intro h
    have hm : ![0, 1] ∈ LinearMap.ker formX := by simp [LinearMap.mem_ker, formX]
    rw [h] at hm
    norm_num [LinearMap.mem_ker, formY] at hm
  have hxz : LinearMap.ker formX ≠ LinearMap.ker (formX + formY) := by
    intro h
    have hm : ![0, 1] ∈ LinearMap.ker formX := by simp [LinearMap.mem_ker, formX]
    rw [h] at hm
    norm_num [LinearMap.mem_ker, formX, formY] at hm
  have hyz : LinearMap.ker formY ≠ LinearMap.ker (formX + formY) := by
    intro h
    have hm : ![1, 0] ∈ LinearMap.ker formY := by simp [LinearMap.mem_ker, formY]
    rw [h] at hm
    norm_num [LinearMap.mem_ker, formX, formY] at hm
  simp [ProjectiveArrangement.card, threePoints, ProjectiveArrangement.ofForms,
    hxy, hxz, hyz]

/-- The complement of all rational points of `P¹(F₂)` has polynomial `1 + 2 X`, despite having
no rational points itself. -/
theorem poincarePolynomial_threePoints : threePoints.poincarePolynomial = 1 + 2 * Polynomial.X := by
  rw [poincarePolynomial_points, card_threePoints]
  norm_num

/-- The basis indexed by `Fin 2` exists for the actual zero theory over `F₂`. This conclusion
also holds for any other index size, so it does not determine the polynomial Betti number. -/
theorem nonempty_basis_threePoints_zeroTheory :
    Nonempty (Basis (Fin 2) PUnit
      ((zeroTheory.{0, 0, 0, 0} (ZMod 2)).grading (projectiveComplement threePoints) (1, 1))) := by
  simpa [card_threePoints] using
    nonempty_basis_points_grading_one threePoints (zeroTheory.{0, 0, 0, 0} (ZMod 2))

/-- A decone of the three `F₂`-points admits a logarithmic monomial basis with two words of length
one, matching its polynomial Betti number. The proof uses the empty/deletion recursion. Over the
zero ring, analogous existential statements hold with other word counts, so this conclusion does
not define the Betti number. -/
theorem exists_logMonomialBasis_decone_threePoints_zeroTheory :
    ∃ b : (zeroTheory.{0, 0, 0, 0} (ZMod 2)).LogMonomialBasis (threePoints.decone formX),
      b.wordCount 1 = 2 := by
  have hx : LinearMap.ker formX ∈ threePoints :=
    ProjectiveArrangement.ker_mem_ofForms (by simp)
  obtain ⟨b, hb⟩ := (zeroTheory.{0, 0, 0, 0} (ZMod 2)).exists_logMonomialBasis_decone threePoints hx
  refine ⟨b, (hb 1).trans ?_⟩
  simp [ProjectiveArrangement.bettiNumber_one, card_threePoints]

/-- The projective diagonal equivalence exists for the actual zero theory on the point-free
projective complement. -/
example : projectiveAlgebra PUnit threePoints.cone_isCentral ≃ₐ[PUnit]
    ⨁ q : ℕ, diagonalGrading
      ((zeroTheory.{0, 0, 0, 0} (ZMod 2)).grading (projectiveComplement threePoints)) q :=
  (zeroTheory.{0, 0, 0, 0} (ZMod 2)).projectiveDiagonalEquiv threePoints

/-- With characteristic-two coefficients the same indexed basis exists for any
supplied theory, with no assumption that the complement has rational points. -/
example {B : Type w} [CommRing B] [Algebra (ZMod 2) B]
    {ℬ : ℤ → Submodule (ZMod 2) B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{0, 0, w, z} (ZMod 2) ℬ) :
    Nonempty (Basis (Fin 2) (ZMod 2)
      (T.grading (projectiveComplement threePoints) (1, 1))) := by
  simpa [card_threePoints] using nonempty_basis_points_grading_one threePoints T

end ThreePoints

section CharacteristicFour

/-- Logarithmic squares vanish with `ℤ/4` coefficients, where the signed commutativity identity
alone does not force square zero. -/
example {k : Type u} [CommRing k] {B : Type w} [CommRing B] [Algebra (ZMod 4) B]
    {ℬ : ℤ → Submodule (ZMod 4) B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, 0, w, z} k ℬ) {A : SmoothAlg k} (a : Aˣ) :
    T.logClass a * T.logClass a = 0 := T.logClass_mul_self a

end CharacteristicFour

section Integers

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {B : Type w} [CommRing B]
  {ℬ : ℤ → Submodule ℤ B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, 0, w, z} k ℬ)
  (P : ProjectiveArrangement k V) [Nonempty P]

/-- The projective diagonal theorem admits a literal integer-algebra type using the documented
conversion, without assuming that a nonzero integer-coefficient theory has been constructed. -/
example : projectiveAlgebra ℤ P.cone_isCentral ≃ₐ[ℤ]
    ⨁ q : ℕ, diagonalGrading (T.grading (projectiveComplement P)) q :=
  RingEquiv.toIntAlgEquiv (T.projectiveDiagonalEquiv P : _ ≃+* _)

end Integers

end OrlikSolomon.ProjectiveOrdinaryExamples
