/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.Combinatorics.ProjectiveBetti
public import OrlikSolomon.Geometry.Projective
public import OrlikSolomon.Presentation.Ordinary

/-!
# Projective cohomology and decone word counts

Decone pullback identifies the cohomology of a nonempty projective complement with that of any
of its affine decones. The recursive logarithmic basis of a decone has exactly the number of
words of each length given by the projective polynomial. This word-count witness remains
meaningful over zero coefficients. A bare basis or module equivalence over the zero ring holds
for every cardinality and does not determine the Betti numbers.

## Main results

* `OrdinaryTheory.projectiveDeconeComponentEquiv` identifies the actual cohomological pieces
  with those of any decone.
* `OrdinaryTheory.exists_logMonomialBasis_decone` retains the recursive basis and the equality
  of its word counts with the projective polynomial coefficients.
* `OrdinaryTheory.nonempty_projective_grading_linearEquiv_bettiNumber` and
  `OrdinaryTheory.nonempty_basis_projective_grading_bettiNumber` give the module equivalences
  and diagonal bases indexed by these numbers. At zero coefficients these conclusions alone
  carry no information about the counts; the preceding word-count statement supplies it.

The polynomial definitions and identities are in `Combinatorics/ProjectiveBetti`, which imports
no cohomology.
Blueprint: `cor:projective-betti`.
-/

@[expose] public section

noncomputable section

open Module

universe u v w z

namespace OrlikSolomon

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace OrdinaryTheory

open CategoryTheory SmoothAlg

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {P : ProjectiveArrangement k W} [FiniteDimensional k W] [Nonempty P]
  {ℓ₀ : Dual k W}

/-- Pullback along the decone isomorphism identifies projective cohomology with the cohomology
of any affine decone, over the full coefficient ring. -/
def projectiveDeconeEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    T.C.obj (projectiveComplement P) ≃ₐ[B] T.C.obj (complement (P.decone ℓ₀)) :=
  (T.C.mapIso (deconeIso hℓ₀)).toAlgEquiv

/-- The cohomological decone equivalence is pullback along the geometric decone isomorphism. -/
@[simp]
theorem projectiveDeconeEquiv_apply (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (x : T.C.obj (projectiveComplement P)) :
    T.projectiveDeconeEquiv hℓ₀ x = T.C.map (deconeIso hℓ₀).hom x := rfl

/-- Deconing preserves every cohomological bidegree, as an equivalence of the actual
`R`-submodule pieces. -/
def projectiveDeconeComponentEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (i : ℤ × ℤ) :
    T.grading (projectiveComplement P) i ≃ₗ[R] T.grading (complement (P.decone ℓ₀)) i :=
  (T.isHomogeneousOfShift_map (deconeIso hℓ₀).hom).componentEquiv
    (e := (T.projectiveDeconeEquiv hℓ₀).toLinearEquiv) (add_zero i)

/-- The component equivalence is the decone pullback on underlying classes. -/
@[simp]
theorem coe_projectiveDeconeComponentEquiv_apply (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (i : ℤ × ℤ)
    (x : T.grading (projectiveComplement P) i) :
    (T.projectiveDeconeComponentEquiv hℓ₀ i x : T.C.obj (complement (P.decone ℓ₀))) =
      T.C.map (deconeIso hℓ₀).hom x := rfl

/-- The recursive logarithmic basis of every decone has exactly the projective Betti number
of words of each length. The words and this equality are retained, so the count is still a
combinatorial assertion over zero coefficients, where a basis alone cannot determine it.
Blueprint: `cor:projective-betti`. -/
theorem exists_logMonomialBasis_decone (P : ProjectiveArrangement k W) [Nonempty P]
    {ℓ : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P) :
    ∃ b : T.LogMonomialBasis (P.decone ℓ), ∀ q, b.wordCount q = P.bettiNumber q :=
  let ⟨b, hb⟩ := T.exists_logMonomialBasis (P.decone ℓ)
  ⟨b, fun q ↦ (hb q).trans (ProjectiveArrangement.bettiNumber_eq_decone hℓ q).symm⟩

/-- Every projective piece `H^{p,w}` is a direct sum of the projective Betti number of copies of
the coefficient piece `B_{w-p}`. Over the zero ring such an equivalence exists with any number
of copies, so it does not determine `b_p`; `exists_logMonomialBasis_decone` records the recursive
word count that agrees with the polynomial coefficient.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_projective_grading_linearEquiv_bettiNumber (P : ProjectiveArrangement k W)
    [Nonempty P] (p : ℕ) (w : ℤ) :
    Nonempty (T.grading (projectiveComplement P) ((p : ℤ), w) ≃ₗ[R]
      (Fin (P.bettiNumber p) → ℬ (w - p))) := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  obtain ⟨e⟩ := T.nonempty_grading_linearEquiv_bettiNumber (P.decone ℓ) p w
  rw [← ProjectiveArrangement.bettiNumber_eq_decone hℓ] at e
  exact ⟨T.projectiveDeconeComponentEquiv hℓ _ ≪≫ₗ e⟩

/-- The projective diagonal piece has a basis indexed by its combinatorial Betti number.
Over the zero ring a basis exists for every cardinality; this conclusion does not determine the
number. `exists_logMonomialBasis_decone` retains the recursive words and their polynomial count.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_basis_projective_grading_bettiNumber (P : ProjectiveArrangement k W)
    [Nonempty P] (q : ℕ) :
    Nonempty (Basis (Fin (P.bettiNumber q)) R
      (T.grading (projectiveComplement P) ((q : ℤ), (q : ℤ)))) := by
  obtain ⟨ℓ, hℓ⟩ := P.exists_ker_mem
  obtain ⟨b⟩ := T.nonempty_basis_grading_bettiNumber (P.decone ℓ) q
  rw [← ProjectiveArrangement.bettiNumber_eq_decone hℓ] at b
  exact ⟨b.map (T.projectiveDeconeComponentEquiv hℓ _).symm⟩

/-- The first projective diagonal piece admits a basis indexed by `Fin (|P|-1)`.
Over the zero ring this does not assert uniqueness of the basis cardinality.
Blueprint: `cor:projective-betti`. -/
theorem nonempty_basis_projective_grading_one (P : ProjectiveArrangement k W) [Nonempty P] :
    Nonempty (Basis (Fin (P.card - 1)) R (T.grading (projectiveComplement P) (1, 1))) := by
  simpa using T.nonempty_basis_projective_grading_bettiNumber P 1

end OrdinaryTheory

end OrlikSolomon
