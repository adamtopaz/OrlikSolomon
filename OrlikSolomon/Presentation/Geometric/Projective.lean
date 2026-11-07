/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Combinatorics.Multiplicities
public import OrlikSolomon.Geometry.Schemes.Decone
public import OrlikSolomon.Presentation.Geometric.Ordinary
public import OrlikSolomon.Presentation.ProjectiveOrdinary

/-!
# The geometric projective structure theorem

For a nonempty projective arrangement `P` in a finite-dimensional space `W`, every geometric
ordinary theory `T` on every admissible domain `D` has a canonical bigrading-preserving equivalence
of `B`-algebras `OS̄_B(P) ≃ C(U_P)`, where `U_P` is the complement as an actual open subscheme of
`ℙ(W) = Proj Sym(W*)`, sending `e_i - e_j` to the logarithmic class `[ℓ_i / ℓ_j]` of the ratio of
any equations. Here `OS̄_B(P)` is the existing kernel of the boundary on the cone, not a new
presentation. This is `Geometric.OrdinaryTheory.projectiveEquiv`.

As in the affine case, it is the existing projective theorem for `T.toAlgebraic`, followed by
pullback along the comparison `s_P : U_P ≅ Spec O(U_P)` (`projectiveEquiv_apply`). It does not
depend on the equations (`projectiveEquiv_difference_of_ker_eq`, `toAlgHom_projectiveEquiv_unique`)
or on a hyperplane at infinity: it is characterized by its pullback along the canonical projection
`q : V_P → U_P` from the complement of the cone (`pull_coneComplementProjection_projectiveEquiv`,
`eq_projectiveEquiv_of_pull_coneComplementProjection`), and `projectiveEquiv_eq_pull_oneSection`
gives it explicitly in the chart of every hyperplane.

**The empty arrangement is excluded**, as in the blueprint: `[Nonempty P]` is a hypothesis of every
statement here. The complement of the empty projective arrangement is `ℙ(W)` itself, which is
usually not affine and has different cohomology; dropping the hypothesis would change the
mathematics.

## Main definitions

* `Geometric.OrdinaryTheory.projectiveEquiv P : OS̄_B(P) ≃ₐ[B] T.obj (D.projectiveComplement P)`.
* `Geometric.OrdinaryTheory.projectiveComponentEquiv P i`: its restriction to bidegree `i`.
* `Geometric.OrdinaryTheory.projectiveRealizationOverR P`, `projectiveDegreeEquiv P q` and
  `projectiveDiagonalEquiv P : OS̄_R(P) ≃ₐ[R] ⨁ q : ℕ, H^{q, q}(U_P)`.
* `Geometric.OrdinaryTheory.projectiveDeconeComponentEquiv`: the pieces of `C(U_P)` and of the
  cohomology of a decone.

## Main results

* `projectiveEquiv_difference`, `projectiveEquiv_difference_of_ker_eq`: `e_i - e_j ↦ [ℓ_i / ℓ_j]`.
* `pull_coneComplementProjection_projectiveEquiv`: compatibility with the affine theorem of the
  cone.
* `isHomogeneousOfShift_projectiveEquiv`, `isHomogeneousOfShift_projectiveEquiv_symm`.
* `projectiveDiagonalEquiv_difference`, `projectiveDiagonalEquiv_of_mem_degree`.
* `cor:projective-betti`: `nonempty_projective_grading_linearEquiv_bettiNumber`,
  `nonempty_basis_projective_grading_bettiNumber`, `nonempty_basis_projective_grading_one`,
  `exists_basis_logMonomial_decone`.
* `ofAlgebraic_projectiveEquiv`: for the transport of an algebraic theory, the existing theorem.

## Blueprint

`thm:geo-projective`, with `thm:projective` and `cor:projective-betti` transported along
`thm:geo-transport-all`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Module
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.Geometric.OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)
  {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

/-! ### The equivalence -/

section Projective

/-- **The geometric projective structure theorem.** For a nonempty projective arrangement `P`, the
cohomology of its complement `U_P`, an open subscheme of `ℙ(W)`, is the projective Orlik–Solomon
algebra, the kernel of the boundary on the cone: there is a canonical equivalence of `B`-algebras,
sending `e_i - e_j` to the logarithmic class `[ℓ_i / ℓ_j]` of the ratio of any equations, by
`projectiveEquiv_difference_of_ker_eq`. It preserves the bigrading in both directions, does not
depend on the equations or on a hyperplane at infinity, and commutes with pullback along the
canonical projection from the complement of the cone.

It holds for every geometric theory on every admissible domain and every coefficient ring. It is
the existing equivalence for `T.toAlgebraic` followed by pullback along `s_P : U_P ≅ Spec O(U_P)`
(`projectiveEquiv_apply`).

Blueprint: `thm:geo-projective`. -/
def projectiveEquiv :
    projectiveAlgebra B P.cone_isCentral ≃ₐ[B] T.obj (D.projectiveComplement P) :=
  (T.toAlgebraic.projectiveEquiv P).trans
    (transportAffineDevelopment T (D.projectiveComplementIsoSpec P))

/-- The geometric projective theorem is the existing one for `T.toAlgebraic` followed by pullback
along `s_P`. This is for `rw`, and it is not a `simp` lemma.

Blueprint: `thm:geo-projective`. -/
theorem projectiveEquiv_apply (x : projectiveAlgebra B P.cone_isCentral) :
    T.projectiveEquiv P x =
      T.pull (D.projectiveComplementIsoSpec P).hom (T.toAlgebraic.projectiveEquiv P x) :=
  rfl

/-- The inverse of the geometric projective theorem. -/
theorem projectiveEquiv_symm_apply (y : T.obj (D.projectiveComplement P)) :
    (T.projectiveEquiv P).symm y =
      (T.toAlgebraic.projectiveEquiv P).symm (T.pull (D.projectiveComplementIsoSpec P).inv y) :=
  rfl

/-- The equivalence sends a difference of cone generators to the logarithmic class of the ratio
`ℓ / ℓ'` of any equations of the two hyperplanes.

Blueprint: `thm:geo-projective`. -/
@[simp]
theorem projectiveEquiv_difference {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    T.projectiveEquiv P (projectiveDifference B P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      T.logClass (projectiveRatio hℓ hℓ') := by
  rw [projectiveEquiv_apply, T.toAlgebraic.projectiveEquiv_difference P hℓ hℓ']
  exact T.pull_toAlgebraic_logClass _ _ (D.coe_projectiveRatio hℓ hℓ')

/-- The ratio formula for arbitrary hyperplane labels and any equations of those labels.

Blueprint: `thm:geo-projective`. -/
theorem projectiveEquiv_difference_of_ker_eq (H K : P) {ℓ ℓ' : Dual k W}
    (hℓ : LinearMap.ker ℓ = (H : Submodule k W)) (hℓ' : LinearMap.ker ℓ' = (K : Submodule k W)) :
    T.projectiveEquiv P (projectiveDifference B P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      T.logClass (projectiveRatio (ℓ := ℓ) (ℓ' := ℓ')
        (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)) := by
  have hH : (⟨LinearMap.ker ℓ, by rw [hℓ]; exact H.2⟩ : P) = H := Subtype.ext hℓ
  have hK : (⟨LinearMap.ker ℓ', by rw [hℓ']; exact K.2⟩ : P) = K := Subtype.ext hℓ'
  simpa only [hH, hK] using T.projectiveEquiv_difference P (ℓ := ℓ) (ℓ' := ℓ')
    (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)

/-- The inverse equivalence sends the logarithmic class of a ratio of equations to the
corresponding difference of cone generators. -/
@[simp]
theorem projectiveEquiv_symm_logClass_ratio {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (T.projectiveEquiv P).symm (T.logClass (projectiveRatio hℓ hℓ')) =
      projectiveDifference B P.cone_isCentral (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
        (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩) := by
  rw [← T.projectiveEquiv_difference P hℓ hℓ', AlgEquiv.symm_apply_apply]

/-- Replacing either equation by any form with the same kernel leaves the logarithmic class of the
ratio unchanged: the classes do not depend on the equations.

Blueprint: `thm:geo-projective`. -/
theorem logClass_projectiveRatio_eq_of_ker_eq {ℓ ℓ' η η' : Dual k W}
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P)
    (hη : LinearMap.ker η ∈ P) (hη' : LinearMap.ker η' ∈ P)
    (h : LinearMap.ker ℓ = LinearMap.ker η) (h' : LinearMap.ker ℓ' = LinearMap.ker η') :
    T.logClass (X := D.projectiveComplement P) (projectiveRatio hℓ hℓ') =
      T.logClass (X := D.projectiveComplement P) (projectiveRatio hη hη') := by
  have hH : (⟨LinearMap.ker ℓ, hℓ⟩ : P) = ⟨LinearMap.ker η, hη⟩ := Subtype.ext h
  have hH' : (⟨LinearMap.ker ℓ', hℓ'⟩ : P) = ⟨LinearMap.ker η', hη'⟩ := Subtype.ext h'
  rw [← T.projectiveEquiv_difference P hℓ hℓ', ← T.projectiveEquiv_difference P hη hη', hH, hH']

/-- **Uniqueness.** For arbitrary choices of defining forms, the equivalence is the unique algebra
map sending each difference to the logarithmic class of the corresponding ratio.

Blueprint: `thm:geo-projective`. -/
theorem toAlgHom_projectiveEquiv_unique (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = (H : Submodule k W))
    (φ : projectiveAlgebra B P.cone_isCentral →ₐ[B] T.obj (D.projectiveComplement P))
    (hφ : ∀ H K : P, φ (projectiveDifference B P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      T.logClass (projectiveRatio (ℓ := F H) (ℓ' := F K)
        (by rw [hF H]; exact H.2) (by rw [hF K]; exact K.2))) :
    φ = T.projectiveEquiv P := by
  let H₀ : P := Classical.choice inferInstance
  apply AlgHom.ext_of_eq_adjoin
    (projectiveAlgebra_eq_adjoin B P.cone_isCentral (P.coneHyperplaneEquiv H₀))
  rintro _ ⟨H, rfl⟩
  obtain ⟨K, rfl⟩ := P.coneHyperplaneEquiv.surjective H
  exact (hφ K H₀).trans (T.projectiveEquiv_difference_of_ker_eq P K H₀ (hF K) (hF H₀)).symm

end Projective

/-! ### The cone -/

section Cone

/-- The projective equivalence pulls back along the canonical projection `q : V_P → U_P` from the
complement of the cone to the affine equivalence of the cone.

Blueprint: `thm:geo-projective`. -/
@[simp]
theorem pull_coneComplementProjection_projectiveEquiv (x : projectiveAlgebra B P.cone_isCentral) :
    T.pull (D.coneComplementProjection (P := P)) (T.projectiveEquiv P x) =
      T.affineEquiv P.cone x := by
  rw [projectiveEquiv_apply, affineEquiv_apply,
    ← T.toAlgebraic.map_projectiveToCone_projectiveEquiv]
  exact (transportAffineDevelopment_map T _ _ _ _
    D.coneComplementProjection_comp_projectiveComplementIsoSpec_hom _).symm

/-- The section `t = 1` of the decomposition `V_P ≅ U_P ×_S 𝔾ₘ` of an equation `ℓ₀` splits the
projection `q : V_P → U_P`. -/
private lemma oneSection_comp_coneComplementIsoProdGm_inv_comp {ℓ₀ : Dual k W}
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    D.oneSection (D.projectiveComplement P) ≫ (D.coneComplementIsoProdGm hℓ₀).inv ≫
      D.coneComplementProjection = 𝟙 _ := by
  rw [← D.coneComplementIsoProdGm_hom_prodGmFst hℓ₀, Iso.inv_hom_id_assoc,
    SmoothDomain.oneSection_prodGmFst]

/-- Pullback along the cone projection is injective: the decomposition with `𝔾ₘ` has the section
`t = 1`. No rational point of the complement is used. -/
theorem injective_pull_coneComplementProjection :
    Function.Injective (T.pull (D.coneComplementProjection (P := P))) := by
  obtain ⟨ℓ₀, h₀⟩ := P.exists_ker_mem
  refine Function.LeftInverse.injective
    (g := T.pull (D.oneSection _ ≫ (D.coneComplementIsoProdGm h₀).inv)) fun x ↦ ?_
  rw [← pull_comp, Category.assoc, oneSection_comp_coneComplementIsoProdGm_inv_comp, pull_id]

/-- The projective equivalence is uniquely characterized by its pullback to the complement of the
cone. In particular it does not depend on any hyperplane at infinity.

Blueprint: `thm:geo-projective`. -/
theorem eq_projectiveEquiv_of_pull_coneComplementProjection
    (φ : projectiveAlgebra B P.cone_isCentral →ₐ[B] T.obj (D.projectiveComplement P))
    (hφ : ∀ x, T.pull (D.coneComplementProjection (P := P)) (φ x) = T.affineEquiv P.cone x) :
    φ = T.projectiveEquiv P :=
  AlgHom.ext fun x ↦ T.injective_pull_coneComplementProjection P <| by
    rw [hφ, AlgEquiv.coe_toAlgHom, pull_coneComplementProjection_projectiveEquiv]

/-- In the chart of every hyperplane `ℓ₀ = 0` at infinity, the projective equivalence is the affine
equivalence of the cone restricted along the section `t = 1` of `V_P ≅ U_P ×_S 𝔾ₘ`. This formula
exhibits the independence of that choice; it is not the definition.

Blueprint: `thm:geo-projective`. -/
theorem projectiveEquiv_eq_pull_oneSection {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (x : projectiveAlgebra B P.cone_isCentral) :
    T.projectiveEquiv P x =
      T.pull (D.oneSection _ ≫ (D.coneComplementIsoProdGm hℓ₀).inv) (T.affineEquiv P.cone x) := by
  rw [← pull_coneComplementProjection_projectiveEquiv, ← pull_comp, Category.assoc,
    oneSection_comp_coneComplementIsoProdGm_inv_comp, pull_id]

end Cone

/-! ### The bigrading -/

section Grading

/-- The projective equivalence preserves the bigrading.

Blueprint: `thm:geo-projective`. -/
theorem isHomogeneousOfShift_projectiveEquiv :
    IsHomogeneousOfShift (projectiveBigrading B ℬ P.cone_isCentral)
      (T.grading (D.projectiveComplement P)) 0 (T.projectiveEquiv P) :=
  (isHomogeneousOfShift_transportAffineDevelopment T _).comp_of_add_eq
    (T.toAlgebraic.isHomogeneousOfShift_projectiveEquiv P) (add_zero 0)

/-- The inverse projective equivalence preserves the bigrading.

Blueprint: `thm:geo-projective`. -/
theorem isHomogeneousOfShift_projectiveEquiv_symm :
    IsHomogeneousOfShift (T.grading (D.projectiveComplement P))
      (projectiveBigrading B ℬ P.cone_isCentral) 0 (T.projectiveEquiv P).symm := by
  simpa only [neg_zero] using (T.isHomogeneousOfShift_projectiveEquiv P).algEquiv_symm

/-- A projective class has bidegree `i` exactly when its image does. -/
theorem projectiveEquiv_mem_grading_iff {i : ℤ × ℤ} {x : projectiveAlgebra B P.cone_isCentral} :
    T.projectiveEquiv P x ∈ T.grading (D.projectiveComplement P) i ↔
      x ∈ projectiveBigrading B ℬ P.cone_isCentral i :=
  (transportAffineDevelopment_mem_grading_iff T _).trans
    (T.toAlgebraic.projectiveEquiv_mem_grading_iff P)

/-- The projective equivalence on the pieces of bidegree `i`, as an `R`-linear equivalence.

Blueprint: `thm:geo-projective`. -/
def projectiveComponentEquiv (i : ℤ × ℤ) :
    projectiveBigrading B ℬ P.cone_isCentral i ≃ₗ[R] T.grading (D.projectiveComplement P) i :=
  (T.isHomogeneousOfShift_projectiveEquiv P).componentEquiv
    (e := (T.projectiveEquiv P).toLinearEquiv) (add_zero i)

@[simp]
theorem coe_projectiveComponentEquiv_apply (i : ℤ × ℤ)
    (x : projectiveBigrading B ℬ P.cone_isCentral i) :
    (T.projectiveComponentEquiv P i x : T.obj (D.projectiveComplement P)) = T.projectiveEquiv P x :=
  rfl

@[simp]
theorem coe_projectiveComponentEquiv_symm_apply (i : ℤ × ℤ)
    (y : T.grading (D.projectiveComplement P) i) :
    ((T.projectiveComponentEquiv P i).symm y : projectiveAlgebra B P.cone_isCentral) =
      (T.projectiveEquiv P).symm y :=
  rfl

end Grading

/-! ### The diagonal -/

section Diagonal

/-- The canonical projective realization with coefficients in `R`: coefficient extension followed
by the projective equivalence.

Blueprint: `thm:geo-projective`. -/
def projectiveRealizationOverR :
    projectiveAlgebra R P.cone_isCentral →ₐ[R] T.obj (D.projectiveComplement P) :=
  ((T.projectiveEquiv P : projectiveAlgebra B P.cone_isCentral →ₐ[B]
      T.obj (D.projectiveComplement P)).restrictScalars R).comp
    (projectiveCoefficientMap R B P.cone_isCentral)

theorem projectiveRealizationOverR_apply (x : projectiveAlgebra R P.cone_isCentral) :
    T.projectiveRealizationOverR P x =
      T.projectiveEquiv P (projectiveCoefficientMap R B P.cone_isCentral x) :=
  rfl

/-- A projective difference over `R` goes to the logarithmic class of the ratio of any equations of
its hyperplanes. -/
@[simp]
theorem projectiveRealizationOverR_difference {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    T.projectiveRealizationOverR P (projectiveDifference R P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      T.logClass (projectiveRatio hℓ hℓ') := by
  rw [projectiveRealizationOverR_apply, projectiveCoefficientMap_difference,
    projectiveEquiv_difference]

/-- Ordinary projective degree `q` realizes in bidegree `(q, q)`. -/
theorem projectiveRealizationOverR_mem_grading {q : ℕ} {x : projectiveAlgebra R P.cone_isCentral}
    (hx : x ∈ projectiveDegree R P.cone_isCentral q) :
    T.projectiveRealizationOverR P x ∈
      T.grading (D.projectiveComplement P) ((q : ℤ), (q : ℤ)) :=
  (transportAffineDevelopment_mem_grading_iff T _).2
    (T.toAlgebraic.projectiveRealizationOverR_mem_grading P hx)

/-- Projective realization over `R` identifies each ordinary degree with the corresponding diagonal
group. -/
theorem bijOn_projectiveRealizationOverR (q : ℕ) :
    Set.BijOn (T.projectiveRealizationOverR P) (projectiveDegree R P.cone_isCentral q)
      (T.grading (D.projectiveComplement P) ((q : ℤ), (q : ℤ))) :=
  (bijOn_transportAffineDevelopment T _ _).comp (T.toAlgebraic.bijOn_projectiveRealizationOverR P q)

/-- Ordinary degree `q` of the projective presentation is `H^{q, q}(U_P)`, canonically.

Blueprint: `thm:geo-projective`. -/
def projectiveDegreeEquiv (q : ℕ) :
    projectiveDegree R P.cone_isCentral q ≃ₗ[R]
      T.grading (D.projectiveComplement P) ((q : ℤ), (q : ℤ)) :=
  diagonalPieceEquiv (projectiveDegree R P.cone_isCentral) (T.bijOn_projectiveRealizationOverR P) q

@[simp]
theorem coe_projectiveDegreeEquiv_apply (q : ℕ) (x : projectiveDegree R P.cone_isCentral q) :
    (T.projectiveDegreeEquiv P q x : T.obj (D.projectiveComplement P)) =
      T.projectiveRealizationOverR P x :=
  rfl

/-- **The projective diagonal theorem.** The boundary kernel over `R` is the direct sum of the
groups `H^{q, q}(U_P)` of the complement as an open subscheme of `ℙ(W)`, as a graded `R`-algebra,
for every coefficient ring, including `ℤ / 2` and the zero ring.

Blueprint: `thm:geo-projective`. -/
def projectiveDiagonalEquiv :
    projectiveAlgebra R P.cone_isCentral ≃ₐ[R]
      ⨁ q : ℕ, diagonalGrading (T.grading (D.projectiveComplement P)) q :=
  diagonalAlgEquiv (projectiveDegree R P.cone_isCentral) (T.bijOn_projectiveRealizationOverR P)

/-- Embedding the projective diagonal in total cohomology recovers projective realization.

Blueprint: `thm:geo-projective`. -/
@[simp]
theorem coeAlgHom_projectiveDiagonalEquiv (x : projectiveAlgebra R P.cone_isCentral) :
    coeAlgHom (diagonalGrading (T.grading (D.projectiveComplement P)))
      (T.projectiveDiagonalEquiv P x) = T.projectiveRealizationOverR P x :=
  coeAlgHom_diagonalAlgEquiv _ _ x

/-- A homogeneous projective class goes to the summand indexed by its degree.

Blueprint: `thm:geo-projective`. -/
theorem projectiveDiagonalEquiv_of_mem_degree {q : ℕ} {x : projectiveAlgebra R P.cone_isCentral}
    (hx : x ∈ projectiveDegree R P.cone_isCentral q) :
    T.projectiveDiagonalEquiv P x = of _ q
      ⟨T.projectiveRealizationOverR P x, T.projectiveRealizationOverR_mem_grading P hx⟩ :=
  diagonalAlgEquiv_of_mem _ _ hx

/-- A difference of projective generators goes to the logarithmic class of the ratio of their
equations, in the summand of degree one.

Blueprint: `thm:geo-projective`. -/
@[simp]
theorem projectiveDiagonalEquiv_difference {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    T.projectiveDiagonalEquiv P (projectiveDifference R P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      of _ 1 ⟨T.logClass (projectiveRatio hℓ hℓ'), T.logClass_mem_diagonalGrading _⟩ := by
  rw [T.projectiveDiagonalEquiv_of_mem_degree P (projectiveDifference_mem_degree R _ _ _)]
  simp only [T.projectiveRealizationOverR_difference]

end Diagonal

/-! ### Multiplicities -/

section Multiplicities

/-- Pullback along the decone isomorphism `U_{decone_{ℓ₀} P} ≅ U_P` identifies each piece of the
cohomology of `U_P` with that of the complement of the decone.

Blueprint: `thm:geo-projective`. -/
def projectiveDeconeComponentEquiv {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (i : ℤ × ℤ) :
    T.grading (D.projectiveComplement P) i ≃ₗ[R] T.grading (D.complement (P.decone ℓ₀)) i :=
  (T.isHomogeneousOfShift_map (D.projectiveDeconeComplementIso hℓ₀).inv).componentEquiv
    (e := (T.pullIso (D.projectiveDeconeComplementIso hℓ₀).symm).toLinearEquiv) (add_zero i)

@[simp]
theorem coe_projectiveDeconeComponentEquiv_apply {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (i : ℤ × ℤ) (x : T.grading (D.projectiveComplement P) i) :
    (T.projectiveDeconeComponentEquiv P hℓ₀ i x : T.obj (D.complement (P.decone ℓ₀))) =
      T.pull (D.projectiveDeconeComplementIso hℓ₀).inv x :=
  rfl

/-- The complement of every decone has a logarithmic monomial basis with exactly the projective
Betti number of words of each length. Over the zero ring such bases exist for every count; the
count here comes from the recursion.

Blueprint: `thm:geo-projective`. -/
theorem exists_basis_logMonomial_decone {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → List (P.decone ℓ₀))
      (b : Basis ι B (T.obj (D.complement (P.decone ℓ₀)))),
      (∀ i, b i = T.logMonomial (P.decone ℓ₀) (I i)) ∧
        ∀ q, Fintype.card {i // (I i).length = q} = P.bettiNumber q := by
  obtain ⟨ι, _, I, b, hb, -, hc⟩ := T.exists_basis_logMonomial (P.decone ℓ₀)
  exact ⟨ι, inferInstance, I, b, hb, fun q ↦
    (hc q).trans (ProjectiveArrangement.bettiNumber_eq_decone hℓ₀ q).symm⟩

/-- Every projective piece `H^{p, w}(U_P)` is a direct sum of `b_p(P)` copies of `B_{w - p}`. Over
the zero ring such an equivalence exists with any number of copies.

Blueprint: `thm:geo-projective`. -/
theorem nonempty_projective_grading_linearEquiv_bettiNumber (p : ℕ) (w : ℤ) :
    Nonempty (T.grading (D.projectiveComplement P) ((p : ℤ), w) ≃ₗ[R]
      (Fin (P.bettiNumber p) → ℬ (w - p))) :=
  let ⟨e⟩ := T.toAlgebraic.nonempty_projective_grading_linearEquiv_bettiNumber P p w
  ⟨(transportAffineDevelopmentComponentEquiv T (D.projectiveComplementIsoSpec P) _).symm ≪≫ₗ e⟩

/-- The projective diagonal piece `H^{q, q}(U_P)` has an `R`-basis of cardinality `b_q(P)`. Over
the zero ring a basis exists for every cardinality.

Blueprint: `thm:geo-projective`. -/
theorem nonempty_basis_projective_grading_bettiNumber (q : ℕ) :
    Nonempty (Basis (Fin (P.bettiNumber q)) R
      (T.grading (D.projectiveComplement P) ((q : ℤ), (q : ℤ)))) :=
  let ⟨b⟩ := T.toAlgebraic.nonempty_basis_projective_grading_bettiNumber P q
  ⟨b.map (transportAffineDevelopmentComponentEquiv T (D.projectiveComplementIsoSpec P) _)⟩

/-- `H^{1, 1}(U_P)` has an `R`-basis indexed by `Fin (|P| - 1)`.

Blueprint: `thm:geo-projective`. -/
theorem nonempty_basis_projective_grading_one :
    Nonempty (Basis (Fin (P.card - 1)) R (T.grading (D.projectiveComplement P) (1, 1))) := by
  simpa using T.nonempty_basis_projective_grading_bettiNumber P 1

end Multiplicities

/-! ### Compatibility with the existing theorem -/

section Compatibility

variable (E : OrlikSolomon.OrdinaryTheory.{u, v, w, z} k ℬ)

/-- **The two transports agree on the projective theorem.** For an algebraic theory `E`, the
geometric projective theorem of `ofAlgebraic E` is the existing projective theorem of `E`, followed
by `E` of the canonical isomorphism `O(U_P) ≅ Γ(U_P, 𝒪)`, the unit of affine duality followed by
global sections of `s_P`. The proof is uniqueness on differences.

Blueprint: `thm:geo-transport-all`, with `thm:geo-from-algebraic`. -/
theorem ofAlgebraic_projectiveEquiv (x : projectiveAlgebra B P.cone_isCentral) :
    (ofAlgebraic E).projectiveEquiv P x =
      E.C.map ((smoothAffineUnitIso k).hom.app (SmoothAlg.projectiveComplement P) ≫
          (affineGlobalSectionsFunctor k).map
            ((SmoothDomain.aff k).projectiveComplementIsoSpec P).hom.op)
        (E.projectiveEquiv P x) := by
  have h := (ofAlgebraic E).toAlgebraic.toAlgHom_projectiveEquiv_unique P
    (fun H ↦ Classical.choose (ProjectiveArrangement.exists_ker_eq H.2))
    (fun H ↦ Classical.choose_spec (ProjectiveArrangement.exists_ker_eq H.2))
    ((algebraicRoundTripEquiv E (SmoothAlg.projectiveComplement P)).toAlgHom.comp
      (E.projectiveEquiv P : projectiveAlgebra B P.cone_isCentral →ₐ[B]
        E.C.obj (SmoothAlg.projectiveComplement P)))
    fun H K ↦ by
      change algebraicRoundTripEquiv E _ (E.projectiveEquiv P _) = _
      rw [E.projectiveEquiv_difference_of_ker_eq P H K
        (Classical.choose_spec (ProjectiveArrangement.exists_ker_eq H.2))
        (Classical.choose_spec (ProjectiveArrangement.exists_ker_eq K.2))]
      exact algebraicRoundTripEquiv_logClass E _
  exact (congrArg ((ofAlgebraic E).pull _) (AlgHom.congr_fun h x).symm).trans (E.map_map _ _ _)

end Compatibility

end OrlikSolomon.Geometric.OrdinaryTheory
