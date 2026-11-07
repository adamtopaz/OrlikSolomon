/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Schemes.Instance
public import OrlikSolomon.Presentation.Geometric

/-!
# The Orlik–Solomon theorems for de Rham cohomology of arrangement complements on schemes

For every field `k` of characteristic zero, with no further hypothesis, this file states the affine
and projective structure theorems for the de Rham cohomology `H^•_dR(U/k)` of
`def:geo-dr-cohomology`, where `U` is the actual open subscheme `U_𝒜` of affine space or `U_P` of
projective space. The statements mention no cohomology theory: only `Cohomology U` and the
Orlik–Solomon algebras.

* `affineEquiv 𝒜 : OS_k(𝒜) ≃ₐ[k] H^•_dR(U_𝒜/k)`, graded, with `e_H ↦ [df_H / f_H]` for any equation
  `f_H` of `H`.
* `projectiveEquiv P : pOS_k(P) ≃ₐ[k] H^•_dR(U_P/k)` for nonempty `P`, graded, with
  `e_i - e_j ↦ [d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]` for any equations.

Each is the diagonal theorem of `Presentation/Geometric` for the geometric de Rham instance
`ordinaryTheory k`, followed by the removal of the powers of `t` by the inverse of
`TwistedCohomology.diagonalEquiv`. No mathematics about arrangements is repeated.
`affineEquiv_eq_map` and `projectiveEquiv_eq_map` say that this is also the existing de Rham
corollary `OrlikSolomon.DeRham.affineEquiv`, respectively `OrlikSolomon.DeRham.projectiveEquiv`, of
the coordinate ring, transported along the comparison `s` of the complement with the spectrum of
that ring: the two routes of the blueprint's proof agree.

## Main definitions

* `affineEquiv 𝒜`, with `affineDegreeEquiv` in each degree and `affineDirectSumEquiv` onto
  `⨁ q, H^q_dR(U_𝒜/k)`.
* `projectiveEquiv P`, with `projectiveDegreeEquiv` and `projectiveDirectSumEquiv`.

## Main results

* `affineEquiv_generator_of_isEquation`, `affineEquiv_mem_degree_iff`, `affineEquiv_eq_map` and
  `finrank_degree_complement`.
* `projectiveEquiv_difference_of_ker_eq`, `projectiveEquiv_mem_degree_iff`,
  `pull_coneComplementProjection_projectiveEquiv`, which says that the map uses no hyperplane at
  infinity, `projectiveEquiv_eq_map` and `finrank_degree_projectiveComplement`.

## Blueprint

`cor:geo-dr-arrangements`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry DirectSum Module
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra
open OrlikSolomon.DeRham (dlogClass TwistedCohomology)

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [Field k] [CharZero k]

/-! ### The affine theorem -/

section Affine

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V)

/-- **The Orlik–Solomon theorem for de Rham cohomology of the complement as a scheme.** For every
field `k` of characteristic zero and every arrangement `𝒜` of affine hyperplanes in a
finite-dimensional `k`-vector space `V`, the Orlik–Solomon algebra `OS_k(𝒜)` is isomorphic, as a
graded `k`-algebra, to the de Rham cohomology `H^•_dR(U_𝒜/k)` of the complement `U_𝒜`, the open
subscheme of the affine space of `V`. It sends `e_H` to the class `[df_H / f_H]` of any equation
`f_H` of `H`, by `affineEquiv_generator_of_isEquation`, and degree `q` to `H^q_dR(U_𝒜/k)`, by
`affineEquiv_mem_degree_iff`.

Blueprint: `cor:geo-dr-arrangements`. -/
def affineEquiv : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology ((SmoothDomain.aff k).complement 𝒜) :=
  ((ordinaryTheory k).diagonalEquiv 𝒜).trans
    (TwistedCohomology.diagonalEquiv k
      (globalSections ((SmoothDomain.aff k).complement 𝒜).obj)).symm

/-- How `affineEquiv` is built: the realization map of the geometric de Rham instance, followed by
the removal of the powers of `t`. -/
theorem affineEquiv_apply (x : OSAlgebra k 𝒜) :
    affineEquiv 𝒜 x =
      TwistedCohomology.evalOne k (globalSections ((SmoothDomain.aff k).complement 𝒜).obj)
        ((ordinaryTheory k).realizationOverR 𝒜 x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <|
    congrArg (TwistedCohomology.evalOne k _) ((ordinaryTheory k).coeAlgHom_diagonalEquiv x)

/-- **The two constructions agree.** The isomorphism is the existing de Rham corollary
`OrlikSolomon.DeRham.affineEquiv` for the coordinate ring `O(U_𝒜)`, followed by the map induced by
the canonical isomorphism `O(U_𝒜) ≅ Γ(U_𝒜, 𝒪)`: the unit of affine duality followed by global
sections of the comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)`.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem affineEquiv_eq_map (x : OSAlgebra k 𝒜) :
    affineEquiv 𝒜 x = OrlikSolomon.DeRham.Cohomology.map
      (SmoothAlg.algHom ((smoothAffineUnitIso k).hom.app (SmoothAlg.complement 𝒜) ≫
        (affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).complementIsoSpec 𝒜).hom.op))
      (OrlikSolomon.DeRham.affineEquiv 𝒜 x) := by
  have h : (ordinaryTheory k).realizationOverR 𝒜 x = TwistedCohomology.map
      (SmoothAlg.algHom ((smoothAffineUnitIso k).hom.app (SmoothAlg.complement 𝒜) ≫
        (affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).complementIsoSpec 𝒜).hom.op))
      ((OrlikSolomon.DeRham.ordinaryTheory k).realizationOverR 𝒜 x) := by
    rw [(OrlikSolomon.DeRham.ordinaryTheory k).realizationOverR_apply x]
    exact ((ordinaryTheory k).realizationOverR_apply x).trans
      (OrdinaryTheory.ofAlgebraic_affineEquiv 𝒜 (OrlikSolomon.DeRham.ordinaryTheory k)
        (coefficientMap k _ 𝒜 x))
  rw [affineEquiv_apply, h, OrlikSolomon.DeRham.affineEquiv_apply]
  exact TwistedCohomology.evalOne_map _ _

variable {𝒜}

/-- **The isomorphism sends `e_H` to `[df/f]` for any equation `f` of `H`**, restricted to the
complement. So the map does not depend on the equations. Since `f` is not on the left, `simp` needs
the equation to be given.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem affineEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    affineEquiv 𝒜 (generator k 𝒜 H) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).complement 𝒜).obj)
        (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [affineEquiv_apply, (ordinaryTheory k).realizationOverR_generator_of_isEquation H hf,
    evalOne_logClass]

/-- The generator formula for a label presented by an equation. Here `f` is on the left, so `simp`
uses this with no further input. -/
@[simp high]
theorem affineEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    affineEquiv 𝒜 (generator k 𝒜 ⟨zeroLocus f, hf⟩) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).complement 𝒜).obj)
        (complementUnit 𝒜 f (.of_mem hf)) :=
  affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The isomorphism sends degree `q` into `H^q_dR(U_𝒜/k)`. -/
theorem isHomogeneousOfShift_affineEquiv :
    IsHomogeneousOfShift (degree k 𝒜) (Cohomology.degree ((SmoothDomain.aff k).complement 𝒜)) 0
      (affineEquiv 𝒜) := by
  intro q x hx
  obtain ⟨c, hc, hcx⟩ := mem_grading_natCast_iff.1
    ((ordinaryTheory k).realizationOverR_mem_grading hx)
  rw [add_zero, affineEquiv_apply, ← hcx, evalOne_twistedClass]
  exact hc

/-- **The isomorphism is graded**: it identifies `OS_k^q(𝒜)` with `H^q_dR(U_𝒜/k)`.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem affineEquiv_mem_degree_iff {q : ℕ} {x : OSAlgebra k 𝒜} :
    affineEquiv 𝒜 x ∈ Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q ↔
      x ∈ degree k 𝒜 q :=
  ⟨isHomogeneousOfShift_affineEquiv.mem_of_map_mem (affineEquiv 𝒜).injective (add_zero q),
    isHomogeneousOfShift_affineEquiv.map_mem (add_zero q)⟩

variable (𝒜) in
/-- The isomorphism in degree `q`: `OS_k^q(𝒜) ≃ₗ[k] H^q_dR(U_𝒜/k)`.

Blueprint: `cor:geo-dr-arrangements`. -/
def affineDegreeEquiv (q : ℕ) :
    degree k 𝒜 q ≃ₗ[k] Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q :=
  isHomogeneousOfShift_affineEquiv.componentEquiv (e := (affineEquiv 𝒜).toLinearEquiv) (add_zero q)

@[simp]
theorem coe_affineDegreeEquiv_apply (q : ℕ) (x : degree k 𝒜 q) :
    (affineDegreeEquiv 𝒜 q x : Cohomology ((SmoothDomain.aff k).complement 𝒜)) = affineEquiv 𝒜 x :=
  rfl

variable (𝒜) in
/-- **The theorem as a direct sum**: `OS_k(𝒜) ≃ₐ[k] ⨁_{q ≥ 0} H^q_dR(U_𝒜/k)`, the display of
`cor:geo-dr-arrangements`. It sends degree `q` to the summand of degree `q`, by
`affineDirectSumEquiv_of_mem_degree`.

Blueprint: `cor:geo-dr-arrangements`. -/
def affineDirectSumEquiv :
    OSAlgebra k 𝒜 ≃ₐ[k] ⨁ q : ℕ, Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q :=
  (affineEquiv 𝒜).trans (decomposeAlgEquiv (Cohomology.degree ((SmoothDomain.aff k).complement 𝒜)))

/-- The component of degree `q` of the image of `x` is the image of the component of degree `q` of
`x`. -/
@[simp]
theorem coe_affineDirectSumEquiv_apply (x : OSAlgebra k 𝒜) (q : ℕ) :
    (affineDirectSumEquiv 𝒜 x q : Cohomology ((SmoothDomain.aff k).complement 𝒜)) =
      affineEquiv 𝒜 (decompose (degree k 𝒜) x q) :=
  isHomogeneousOfShift_affineEquiv.decompose_map (add_zero q) x

/-- On an element of degree `q`, the direct sum form is `affineEquiv`, in the summand of degree
`q`. -/
theorem affineDirectSumEquiv_of_mem_degree {q : ℕ} {x : OSAlgebra k 𝒜} (hx : x ∈ degree k 𝒜 q) :
    affineDirectSumEquiv 𝒜 x =
      of (fun q ↦ Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q) q
        ⟨affineEquiv 𝒜 x, affineEquiv_mem_degree_iff.2 hx⟩ :=
  decompose_of_mem (Cohomology.degree ((SmoothDomain.aff k).complement 𝒜))
    (affineEquiv_mem_degree_iff.2 hx)

/-- The direct sum form sends `e_H` to `[df/f]` in the summand of degree one, for any equation `f`
of `H`. -/
theorem affineDirectSumEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜)
    (hf : IsEquation f H) :
    affineDirectSumEquiv 𝒜 (generator k 𝒜 H) =
      of (fun q ↦ Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q) 1
        ⟨dlogClass k (A := globalSections ((SmoothDomain.aff k).complement 𝒜).obj)
          (complementUnit 𝒜 f (hf.covers H.2)), OrlikSolomon.DeRham.dlogClass_mem_degree _⟩ :=
  (affineDirectSumEquiv_of_mem_degree (generator_mem_degree k 𝒜 H)).trans <|
    congrArg (of _ 1) (Subtype.ext (affineEquiv_generator_of_isEquation H hf))

variable (𝒜) in
/-- **`dim_k H^q_dR(U_𝒜/k) = b_q(𝒜)`**, the coefficient of `X^q` in the Poincaré polynomial of `𝒜`.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem finrank_degree_complement (q : ℕ) :
    finrank k (Cohomology.degree ((SmoothDomain.aff k).complement 𝒜) q) = 𝒜.bettiNumber q := by
  obtain ⟨b⟩ := (ordinaryTheory k).nonempty_basis_grading_bettiNumber 𝒜 q
  rw [(gradingEquiv ((SmoothDomain.aff k).complement 𝒜) q q).finrank_eq]
  exact (finrank_eq_card_basis b).trans (Fintype.card_fin _)

end Affine

/-! ### The projective theorem -/

section Projective

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

/-- **The projective Orlik–Solomon theorem for de Rham cohomology of the complement as a scheme.**
For every field `k` of characteristic zero and every nonempty arrangement `P` of hyperplanes in
`ℙ(W)`, the projective Orlik–Solomon algebra `pOS_k(P)`, the kernel of the boundary on `OS_k` of the
cone, is isomorphic, as a graded `k`-algebra, to the de Rham cohomology `H^•_dR(U_P/k)` of the
complement `U_P`, the open subscheme of `ℙ(W)`. It sends `e_i - e_j` to
`[d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]` for any equations `ℓ_i` and `ℓ_j`, by
`projectiveEquiv_difference_of_ker_eq`, and degree `q` to `H^q_dR(U_P/k)`, by
`projectiveEquiv_mem_degree_iff`.

No hyperplane at infinity is chosen: `pull_coneComplementProjection_projectiveEquiv` says that the
map is the affine one of the cone after pullback to the complement of the cone. The empty
arrangement is excluded by `[Nonempty P]`, as in the blueprint.

Blueprint: `cor:geo-dr-arrangements`. -/
def projectiveEquiv :
    projectiveAlgebra k P.cone_isCentral ≃ₐ[k]
      Cohomology ((SmoothDomain.aff k).projectiveComplement P) :=
  ((ordinaryTheory k).projectiveDiagonalEquiv P).trans
    (TwistedCohomology.diagonalEquiv k
      (globalSections ((SmoothDomain.aff k).projectiveComplement P).obj)).symm

/-- How `projectiveEquiv` is built: the projective realization map of the geometric de Rham
instance, followed by the removal of the powers of `t`. -/
theorem projectiveEquiv_apply (x : projectiveAlgebra k P.cone_isCentral) :
    projectiveEquiv P x =
      TwistedCohomology.evalOne k (globalSections ((SmoothDomain.aff k).projectiveComplement P).obj)
        ((ordinaryTheory k).projectiveRealizationOverR P x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <| congrArg (TwistedCohomology.evalOne k _)
    ((ordinaryTheory k).coeAlgHom_projectiveDiagonalEquiv P x)

/-- **The two constructions agree.** The projective isomorphism is the existing de Rham corollary
`OrlikSolomon.DeRham.projectiveEquiv` for the coordinate ring `O(U_P)`, followed by the map induced
by the canonical isomorphism `O(U_P) ≅ Γ(U_P, 𝒪)`: the unit of affine duality followed by global
sections of the comparison `s_P : U_P ≅ Spec O(U_P)`.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem projectiveEquiv_eq_map (x : projectiveAlgebra k P.cone_isCentral) :
    projectiveEquiv P x = OrlikSolomon.DeRham.Cohomology.map
      (SmoothAlg.algHom ((smoothAffineUnitIso k).hom.app (SmoothAlg.projectiveComplement P) ≫
        (affineGlobalSectionsFunctor k).map
          ((SmoothDomain.aff k).projectiveComplementIsoSpec P).hom.op))
      (OrlikSolomon.DeRham.projectiveEquiv P x) := by
  have h : (ordinaryTheory k).projectiveRealizationOverR P x = TwistedCohomology.map
      (SmoothAlg.algHom ((smoothAffineUnitIso k).hom.app (SmoothAlg.projectiveComplement P) ≫
        (affineGlobalSectionsFunctor k).map
          ((SmoothDomain.aff k).projectiveComplementIsoSpec P).hom.op))
      ((OrlikSolomon.DeRham.ordinaryTheory k).projectiveRealizationOverR P x) := by
    rw [(OrlikSolomon.DeRham.ordinaryTheory k).projectiveRealizationOverR_apply P x]
    exact ((ordinaryTheory k).projectiveRealizationOverR_apply P x).trans
      (OrdinaryTheory.ofAlgebraic_projectiveEquiv P (OrlikSolomon.DeRham.ordinaryTheory k)
        (projectiveCoefficientMap k _ P.cone_isCentral x))
  rw [projectiveEquiv_apply, h, OrlikSolomon.DeRham.projectiveEquiv_apply]
  exact TwistedCohomology.evalOne_map _ _

/-- **The projective isomorphism is the affine one of the cone**, after pullback along the
canonical projection `V_P → U_P` from the complement of the cone. It involves no hyperplane at
infinity.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem pull_coneComplementProjection_projectiveEquiv (x : projectiveAlgebra k P.cone_isCentral) :
    Cohomology.pull ((SmoothDomain.aff k).coneComplementProjection (P := P)) (projectiveEquiv P x) =
      affineEquiv P.cone (x : OSAlgebra k P.cone) := by
  rw [projectiveEquiv_apply, affineEquiv_apply, ← evalOne_pull]
  congr 1
  change (ordinaryTheory k).pull _ ((ordinaryTheory k).projectiveEquiv P
    (projectiveCoefficientMap k _ P.cone_isCentral x)) = _
  rw [OrdinaryTheory.pull_coneComplementProjection_projectiveEquiv]
  rfl

variable {P}

/-- The isomorphism sends `e_ℓ - e_ℓ'` to `[d(ℓ/ℓ') / (ℓ/ℓ')]`, for the hyperplanes `ker ℓ` and
`ker ℓ'` of `P`. Here the equations are on the left, so `simp` uses this with no further input.

Blueprint: `cor:geo-dr-arrangements`. -/
@[simp]
theorem projectiveEquiv_difference {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    projectiveEquiv P (projectiveDifference k P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).projectiveComplement P).obj)
        (projectiveRatio hℓ hℓ') := by
  rw [projectiveEquiv_apply, OrdinaryTheory.projectiveRealizationOverR_difference,
    evalOne_logClass]

/-- **The isomorphism sends `e_i - e_j` to `[d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]` for any equations `ℓ_i` and
`ℓ_j` of the hyperplanes `H` and `K`.** So the map does not depend on the equations.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem projectiveEquiv_difference_of_ker_eq (H K : P) {ℓ ℓ' : Dual k W}
    (hℓ : LinearMap.ker ℓ = (H : Submodule k W)) (hℓ' : LinearMap.ker ℓ' = (K : Submodule k W)) :
    projectiveEquiv P (projectiveDifference k P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      dlogClass k (A := globalSections ((SmoothDomain.aff k).projectiveComplement P).obj)
        (projectiveRatio (ℓ := ℓ) (ℓ' := ℓ') (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)) := by
  have hH : (⟨LinearMap.ker ℓ, by rw [hℓ]; exact H.2⟩ : P) = H := Subtype.ext hℓ
  have hK : (⟨LinearMap.ker ℓ', by rw [hℓ']; exact K.2⟩ : P) = K := Subtype.ext hℓ'
  simpa only [hH, hK] using projectiveEquiv_difference (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)

/-- The projective isomorphism sends degree `q` into `H^q_dR(U_P/k)`. -/
theorem isHomogeneousOfShift_projectiveEquiv :
    IsHomogeneousOfShift (projectiveDegree k P.cone_isCentral)
      (Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P)) 0 (projectiveEquiv P) := by
  intro q x hx
  obtain ⟨c, hc, hcx⟩ := mem_grading_natCast_iff.1
    ((ordinaryTheory k).projectiveRealizationOverR_mem_grading P hx)
  rw [add_zero, projectiveEquiv_apply, ← hcx, evalOne_twistedClass]
  exact hc

/-- **The projective isomorphism is graded**: it identifies the degree `q` part of `pOS_k(P)` with
`H^q_dR(U_P/k)`.

Blueprint: `cor:geo-dr-arrangements`. -/
theorem projectiveEquiv_mem_degree_iff {q : ℕ} {x : projectiveAlgebra k P.cone_isCentral} :
    projectiveEquiv P x ∈ Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P) q ↔
      x ∈ projectiveDegree k P.cone_isCentral q :=
  ⟨isHomogeneousOfShift_projectiveEquiv.mem_of_map_mem (projectiveEquiv P).injective (add_zero q),
    isHomogeneousOfShift_projectiveEquiv.map_mem (add_zero q)⟩

variable (P) in
/-- The projective isomorphism in degree `q`.

Blueprint: `cor:geo-dr-arrangements`. -/
def projectiveDegreeEquiv (q : ℕ) :
    projectiveDegree k P.cone_isCentral q ≃ₗ[k]
      Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P) q :=
  isHomogeneousOfShift_projectiveEquiv.componentEquiv (e := (projectiveEquiv P).toLinearEquiv)
    (add_zero q)

@[simp]
theorem coe_projectiveDegreeEquiv_apply (q : ℕ) (x : projectiveDegree k P.cone_isCentral q) :
    (projectiveDegreeEquiv P q x : Cohomology ((SmoothDomain.aff k).projectiveComplement P)) =
      projectiveEquiv P x :=
  rfl

variable (P) in
/-- **The projective theorem as a direct sum**: `pOS_k(P) ≃ₐ[k] ⨁_{q ≥ 0} H^q_dR(U_P/k)`, the
display of `cor:geo-dr-arrangements`.

Blueprint: `cor:geo-dr-arrangements`. -/
def projectiveDirectSumEquiv :
    projectiveAlgebra k P.cone_isCentral ≃ₐ[k]
      ⨁ q : ℕ, Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P) q :=
  (projectiveEquiv P).trans
    (decomposeAlgEquiv (Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P)))

/-- The component of degree `q` of the image of `x` is the image of the component of degree `q` of
`x`. -/
@[simp]
theorem coe_projectiveDirectSumEquiv_apply (x : projectiveAlgebra k P.cone_isCentral) (q : ℕ) :
    (projectiveDirectSumEquiv P x q : Cohomology ((SmoothDomain.aff k).projectiveComplement P)) =
      projectiveEquiv P (decompose (projectiveDegree k P.cone_isCentral) x q) :=
  isHomogeneousOfShift_projectiveEquiv.decompose_map (add_zero q) x

/-- On an element of degree `q`, the direct sum form is `projectiveEquiv`, in the summand of degree
`q`. -/
theorem projectiveDirectSumEquiv_of_mem_degree {q : ℕ} {x : projectiveAlgebra k P.cone_isCentral}
    (hx : x ∈ projectiveDegree k P.cone_isCentral q) :
    projectiveDirectSumEquiv P x =
      of (fun q ↦ Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P) q) q
        ⟨projectiveEquiv P x, projectiveEquiv_mem_degree_iff.2 hx⟩ :=
  decompose_of_mem (Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P))
    (projectiveEquiv_mem_degree_iff.2 hx)

variable (P) in
/-- **`dim_k H^q_dR(U_P/k)` is the projective Betti number `b_q(P)`.**

Blueprint: `cor:geo-dr-arrangements`. -/
theorem finrank_degree_projectiveComplement (q : ℕ) :
    finrank k (Cohomology.degree ((SmoothDomain.aff k).projectiveComplement P) q) =
      P.bettiNumber q := by
  obtain ⟨b⟩ := (ordinaryTheory k).nonempty_basis_projective_grading_bettiNumber P q
  rw [(gradingEquiv ((SmoothDomain.aff k).projectiveComplement P) q q).finrank_eq]
  exact (finrank_eq_card_basis b).trans (Fintype.card_fin _)

end Projective

end OrlikSolomon.Geometric.DeRham
