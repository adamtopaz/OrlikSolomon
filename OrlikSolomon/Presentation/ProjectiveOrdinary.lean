/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Ordinary
public import OrlikSolomon.Presentation.Projective
public import OrlikSolomon.Presentation.ProjectiveGrading

/-!
# The ordinary diagonal of a projective complement

For a nonempty projective arrangement `P`, the projective presentation with coefficients in `R`
is canonically the direct sum of the groups `H^{q,q}(U_P)`, as a graded `R`-algebra. A difference
of generators goes to the logarithm of the ratio of their equations. Neither the map nor this
formula chooses a hyperplane at infinity.

The total projective theorem has coefficients in `B`. Here coefficient extension gives a map
from the projective algebra over `R`, and the degreewise statement follows from the affine
diagonal theorem on the cone. The injectivity of coefficient extension detects the vanishing
of the boundary, so no flatness assumption is needed.

* `projectiveRealizationOverR` is the projective realization with coefficients in `R`.
* `projectiveDegreeEquiv` identifies ordinary projective degree `q` with `H^{q,q}(U_P)`.
* `projectiveDiagonalEquiv` is the resulting equivalence of graded `R`-algebras.

At `R = ℤ`, literal equivalence types can select the canonical integer scalar structure rather
than the structure in `T`. The same conversions as in `Presentation/Ordinary` apply: coerce to
an additive or ring equivalence, then use `AddEquiv.toIntLinearEquiv` or
`RingEquiv.toIntAlgEquiv`.

Blueprint: the diagonal in `thm:projective` and the projective display in the introduction.
-/

@[expose] public section

noncomputable section

open DirectSum
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (P : ProjectiveArrangement k V) [Nonempty P]

/-- The canonical projective realization with coefficients in `R`.
Blueprint: the diagonal in `thm:projective`. -/
def projectiveRealizationOverR :
    projectiveAlgebra R P.cone_isCentral →ₐ[R] T.C.obj (projectiveComplement P) :=
  ((T.projectiveRealization P).restrictScalars R).comp
    (projectiveCoefficientMap R B P.cone_isCentral)

/-- Pullback to the cone identifies projective realization over `R` with affine realization of
the underlying boundary-closed element. -/
@[simp]
theorem map_projectiveToCone_projectiveRealizationOverR (x : projectiveAlgebra R P.cone_isCentral) :
    T.C.map (projectiveToCone P) (T.projectiveRealizationOverR P x) =
      T.realizationOverR P.cone (x : OSAlgebra R P.cone) := by
  change T.C.map (projectiveToCone P)
    (T.projectiveRealization P (projectiveCoefficientMap R B P.cone_isCentral x)) = _
  rw [T.map_projectiveToCone_projectiveRealization]
  rfl

/-- The projective realization over `R` is injective, as seen after pullback to the cone. -/
theorem injective_projectiveRealizationOverR :
    Function.Injective (T.projectiveRealizationOverR P) := by
  intro x y hxy
  apply Subtype.ext
  apply T.injective_realizationOverR P.cone
  rw [← T.map_projectiveToCone_projectiveRealizationOverR P x,
    ← T.map_projectiveToCone_projectiveRealizationOverR P y, hxy]

/-- Compatibility with affine realization on the cone characterizes the projective map over
`R`, independently of any hyperplane at infinity used in a proof. -/
theorem projectiveRealizationOverR_unique
    (φ : projectiveAlgebra R P.cone_isCentral →ₐ[R] T.C.obj (projectiveComplement P))
    (hφ : ∀ x, T.C.map (projectiveToCone P) (φ x) = T.realizationOverR P.cone x) :
    φ = T.projectiveRealizationOverR P := by
  ext x
  apply T.injective_map_projectiveToCone P
  rw [hφ, T.map_projectiveToCone_projectiveRealizationOverR]

/-- A projective difference over `R` realizes as the logarithm of the ratio of any linear
equations of its hyperplanes.
Blueprint: the diagonal in `thm:projective`. -/
theorem projectiveRealizationOverR_difference {ℓ ℓ' : Module.Dual k V}
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    T.projectiveRealizationOverR P (projectiveDifference R P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      T.logClass (projectiveRatioUnit hℓ hℓ') := by
  change T.projectiveRealization P (projectiveCoefficientMap R B P.cone_isCentral _) = _
  rw [projectiveCoefficientMap_difference]
  exact T.projectiveRealization_difference P hℓ hℓ'

/-- Ordinary projective degree `q` realizes in bidegree `(q,q)`. -/
theorem projectiveRealizationOverR_mem_grading {q : ℕ}
    {x : projectiveAlgebra R P.cone_isCentral}
    (hx : x ∈ projectiveDegree R P.cone_isCentral q) :
    T.projectiveRealizationOverR P x ∈ T.grading (projectiveComplement P) ((q : ℤ), (q : ℤ)) := by
  apply (T.isHomogeneousOfShift_map (projectiveToCone P)).mem_of_map_mem
    (T.injective_map_projectiveToCone P) (add_zero ((q : ℤ), (q : ℤ)))
  rw [T.map_projectiveToCone_projectiveRealizationOverR]
  exact T.realizationOverR_mem_grading hx

/-- Projective realization over `R` identifies each ordinary degree with the corresponding
diagonal cohomology group.
Blueprint: the diagonal in `thm:projective`. -/
theorem bijOn_projectiveRealizationOverR (q : ℕ) :
    Set.BijOn (T.projectiveRealizationOverR P) (projectiveDegree R P.cone_isCentral q)
      (T.grading (projectiveComplement P) ((q : ℤ), (q : ℤ))) := by
  refine ⟨fun _ hx ↦ T.projectiveRealizationOverR_mem_grading P hx,
    fun _ _ _ _ hxy ↦ T.injective_projectiveRealizationOverR P hxy, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (T.bijOn_realizationOverR P.cone q).surjOn
    (T.map_mem_grading (projectiveToCone P) hy)
  let z := (T.projectiveEquiv P).symm y
  have hcoeff : coefficientMap R B P.cone x = (z : OSAlgebra B P.cone) := by
    apply (T.bijective_realization P.cone).injective
    change T.realizationOverR P.cone x = T.affineEquiv P.cone z
    rw [hxy, ← T.map_projectiveToCone_projectiveEquiv P z, AlgEquiv.apply_symm_apply]
  have hboundary : boundary R P.cone_isCentral x = 0 := by
    apply T.injective_coefficientMap P.cone
    rw [map_zero, ← boundary_coefficientMap, hcoeff]
    exact z.property
  let xp : projectiveAlgebra R P.cone_isCentral := ⟨x, hboundary⟩
  refine ⟨xp, hx, ?_⟩
  apply T.injective_map_projectiveToCone P
  rw [T.map_projectiveToCone_projectiveRealizationOverR]
  exact hxy

/-- Ordinary degree `q` of the projective presentation is `H^{q,q}(U_P)`, canonically and without
flatness or restrictions on the coefficient ring.
Blueprint: the diagonal in `thm:projective`. -/
def projectiveDegreeEquiv (q : ℕ) :
    projectiveDegree R P.cone_isCentral q ≃ₗ[R]
      T.grading (projectiveComplement P) ((q : ℤ), (q : ℤ)) :=
  diagonalPieceEquiv (projectiveDegree R P.cone_isCentral) (T.bijOn_projectiveRealizationOverR P) q

/-- The degreewise projective equivalence is projective realization on underlying elements. -/
@[simp]
theorem coe_projectiveDegreeEquiv_apply (q : ℕ) (x : projectiveDegree R P.cone_isCentral q) :
    (T.projectiveDegreeEquiv P q x : T.C.obj (projectiveComplement P)) =
      T.projectiveRealizationOverR P x := rfl

/-- **The projective diagonal theorem.** The boundary kernel over `R` is the external direct sum
of the groups `H^{q,q}(U_P)`, as a graded `R`-algebra. It holds for arbitrary coefficient rings,
including characteristic two and the zero ring.
Blueprint: `thm:projective` and the projective display in the introduction. -/
def projectiveDiagonalEquiv :
    projectiveAlgebra R P.cone_isCentral ≃ₐ[R]
      ⨁ q : ℕ, diagonalGrading (T.grading (projectiveComplement P)) q :=
  diagonalAlgEquiv (projectiveDegree R P.cone_isCentral) (T.bijOn_projectiveRealizationOverR P)

/-- Embedding the projective diagonal in total cohomology recovers projective realization. -/
@[simp]
theorem coeAlgHom_projectiveDiagonalEquiv (x : projectiveAlgebra R P.cone_isCentral) :
    coeAlgHom (diagonalGrading (T.grading (projectiveComplement P)))
      (T.projectiveDiagonalEquiv P x) = T.projectiveRealizationOverR P x :=
  coeAlgHom_diagonalAlgEquiv _ _ x

/-- The degree `q` component of the projective diagonal equivalence is the realization of the
degree `q` component in the projective algebra. -/
theorem coe_projectiveDiagonalEquiv_apply (x : projectiveAlgebra R P.cone_isCentral) (q : ℕ) :
    (T.projectiveDiagonalEquiv P x q : T.C.obj (projectiveComplement P)) =
      T.projectiveRealizationOverR P (decompose (projectiveDegree R P.cone_isCentral) x q) :=
  coe_diagonalAlgEquiv_apply _ _ x q

/-- A homogeneous projective class realizes in the summand indexed by its degree. -/
theorem projectiveDiagonalEquiv_of_mem_degree {q : ℕ}
    {x : projectiveAlgebra R P.cone_isCentral} (hx : x ∈ projectiveDegree R P.cone_isCentral q) :
    T.projectiveDiagonalEquiv P x = of _ q
      ⟨T.projectiveRealizationOverR P x, T.projectiveRealizationOverR_mem_grading P hx⟩ :=
  diagonalAlgEquiv_of_mem _ _ hx

/-- A difference of projective generators maps to the logarithm of the ratio of their equations,
in the summand of degree one. The equations are arbitrary, and no hyperplane at infinity occurs.
Blueprint: the diagonal in `thm:projective`. -/
theorem projectiveDiagonalEquiv_difference {ℓ ℓ' : Module.Dual k V}
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    T.projectiveDiagonalEquiv P (projectiveDifference R P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      of _ 1 ⟨T.logClass (projectiveRatioUnit hℓ hℓ'), T.logClass_mem_diagonalGrading _⟩ := by
  rw [T.projectiveDiagonalEquiv_of_mem_degree P (projectiveDifference_mem_degree R _ _ _)]
  simp only [T.projectiveRealizationOverR_difference]

end OrlikSolomon.OrdinaryTheory
