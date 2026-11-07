/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Combinatorics.Multiplicities
public import OrlikSolomon.DeRham.Instance
public import OrlikSolomon.Presentation.ProjectiveOrdinary

/-!
# The Orlik–Solomon theorems for algebraic de Rham cohomology

For every field `k` of characteristic zero, with no further hypothesis, this file states the affine
and projective structure theorems for the algebraic de Rham cohomology `H^•_dR(U/k)` of an
arrangement complement `U`. These corollaries have no cohomology theory as a parameter: they
mention de Rham cohomology `DeRham.Cohomology k (complement 𝒜)` and the
Orlik–Solomon algebra, and nothing else.

* `cor:dr-affine`: for an arrangement `𝒜` in a finite-dimensional `k`-vector space,
  `OS_k(𝒜) ≃ₐ[k] H^•_dR(U_𝒜/k)`, graded, with `e_H ↦ [df_H / f_H]` for any equation `f_H` of `H`.
* `cor:dr-projective`: for a nonempty projective arrangement `P`,
  `pOS_k(P) ≃ₐ[k] H^•_dR(U_P/k)`, graded, with `e_i - e_j ↦ [d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]`.

Both are proved by instantiating `OrdinaryTheory.diagonalEquiv` and
`OrdinaryTheory.projectiveDiagonalEquiv` at the de Rham instance `ordinaryTheory k`, and removing
the powers of `t` from the diagonal with `TwistedCohomology.diagonalEquiv`. No mathematics about
arrangements is repeated. The one new computation is `lem:dr-tau`, which identifies the logarithmic
classes of the instance with the classes `[du/u] t`.

## Main definitions

* `OrlikSolomon.DeRham.dlogClass k u`: the de Rham class `[du/u] ∈ H^1_dR(A/k)` of a unit `u`, for
  any commutative algebra `A` over any commutative ring `k`.
* `OrlikSolomon.DeRham.affineEquiv 𝒜 : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology k (complement 𝒜)`, with its
  forms `affineDirectSumEquiv` onto `⨁ q, H^q_dR(U_𝒜/k)` and `affineDegreeEquiv` in each degree.
* `OrlikSolomon.DeRham.projectiveEquiv P`, with `projectiveDirectSumEquiv` and
  `projectiveDegreeEquiv`.

## Main results

* `lem:dr-tau`: `ordinaryTheory_tau`, `τ = [dx/x] t`, and `ordinaryTheory_logClass`,
  `[u] = [du/u] t`. The input is `residue_dlogClass`: the residue of `[df/f]` is `1`.
* `cor:dr-affine`: `affineEquiv`, `affineEquiv_generator_of_isEquation` and
  `affineEquiv_mem_degree_iff`.
* `cor:dr-projective`: `projectiveEquiv`, `projectiveEquiv_difference_of_ker_eq`,
  `projectiveEquiv_mem_degree_iff` and `map_projectiveToCone_projectiveEquiv`, which says that the
  map is compatible with the affine one on the cone and so uses no hyperplane at infinity.
* `finrank_degree_complement` and `finrank_degree_projectiveComplement`: `dim H^q_dR = b_q`.

## Implementation notes

The corollary statements concern `DeRham.Cohomology k A` and its degrees
`Cohomology.degree k A q`, and mention neither `OrdinaryTheory` nor the coefficient `k[t, t⁻¹]` of
the instance. The lemmas
`affineEquiv_apply` and `projectiveEquiv_apply`, which say how the maps are built, are the only
exceptions.

`ordinaryTheory_logClass`, which rewrites a logarithmic class of the instance to
`twistedClass 1 (dlogClass k u)`, is not a `simp` lemma, so that the generic `simp` lemmas about
`OrdinaryTheory.logClass`, such as `OrdinaryTheory.residue_logClass_eqnUnit`, still fire on the
instance.

## Blueprint

`lem:dr-tau`, `cor:dr-affine`, `cor:dr-projective`.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum Module
open OrlikSolomon.SmoothAlg OrlikSolomon.DivisorPair OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u

namespace OrlikSolomon.DeRham

/-! ### The class `[du/u]` -/

section DlogClass

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {A' : Type*} [CommRing A'] [Algebra k A']

/-- The de Rham class `[du/u] ∈ H^1_dR(A/k)` of a unit `u` of `A`: the class of the closed form
`dlog k u = u⁻¹ du`. For an equation `f` of a hyperplane, which is a unit on the complement, it is
the class `[df/f]` of `cor:dr-affine`.

Blueprint: `lem:dr-tau`. -/
def dlogClass (u : Aˣ) : Cohomology k A :=
  Cohomology.mk (dlog k u) (d_dlog k u)

variable {k}

/-- `[du/u]` is the class of the form `du/u`. -/
theorem mk_dlog (u : Aˣ) (h : d k (dlog k u) = 0) : Cohomology.mk (dlog k u) h = dlogClass k u :=
  rfl

/-- `[du/u]` has degree one. -/
theorem dlogClass_mem_degree (u : Aˣ) : dlogClass k u ∈ Cohomology.degree k A 1 :=
  Cohomology.mk_mem_degree (dlog_mem_exteriorPower_one k u) (d_dlog k u)

/-- `[du/u]` has degree one, for the grading by the integers. -/
theorem dlogClass_mem_grading (u : Aˣ) : dlogClass k u ∈ Cohomology.grading k A 1 :=
  Cohomology.mk_mem_grading (n := 1) (dlog_mem_exteriorPower_one k u) (d_dlog k u)

/-- `[du/u]` is natural. -/
@[simp]
theorem map_dlogClass (φ : A →ₐ[k] A') (u : Aˣ) :
    Cohomology.map φ (dlogClass k u) = dlogClass k (Units.map (φ : A →* A') u) :=
  Cohomology.mk_congr (Forms.map_dlog φ u) _

@[simp]
theorem dlogClass_one : dlogClass k (1 : Aˣ) = 0 :=
  (Cohomology.mk_congr (dlog_one k) _).trans (Cohomology.mk_zero _)

/-- `[d(uv)/uv] = [du/u] + [dv/v]`. -/
@[simp]
theorem dlogClass_mul (u v : Aˣ) : dlogClass k (u * v) = dlogClass k u + dlogClass k v :=
  (Cohomology.mk_congr (dlog_mul k u v) _).trans (Cohomology.mk_add _ _ _ _).symm

@[simp]
theorem dlogClass_inv (u : Aˣ) : dlogClass k u⁻¹ = -dlogClass k u :=
  (Cohomology.mk_congr (dlog_inv k u) _).trans (Cohomology.mk_neg _ _).symm

@[simp]
theorem dlogClass_div (u v : Aˣ) : dlogClass k (u / v) = dlogClass k u - dlogClass k v := by
  rw [div_eq_mul_inv, dlogClass_mul, dlogClass_inv, sub_eq_add_neg]

end DlogClass

/-! ### The residue of `[df/f]` -/

section Residue

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A] {f : A}
  {S : Type*} [CommRing S] [Algebra k S] {φ : A →ₐ[k] S}
  {T : Type*} [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T] (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))

/-- **The residue of `[df/f]` is `1`**, for a smooth principal pair, with no sign: the form `df/f`
is closed and logarithmic, and its form residue is `1`. Here `u` is any unit of the localization
whose value is the image of `f`.

Blueprint: the proof of `lem:dr-tau`, from `lem:dr-exactness` with `ω = 0` and `η = 1`. -/
theorem residue_dlogClass (h : IsSmoothPrincipalPair f φ) {u : Tˣ}
    (hu : (u : T) = algebraMap A T f) : residue T hUnits h (dlogClass k u) = 1 := by
  rw [dlogClass, ← Cohomology.mk_congr (theta_eq_dlog k f T hu) (d_theta k f T),
    residue_mk_of_mem_logForms hUnits h (theta_mem_logForms k f T), ← Cohomology.mk_one (by simp)]
  exact Cohomology.mk_congr (logResidue_theta h) _

end Residue

variable {k : Type u} [Field k] [CharZero k]

/-- The residue of `[df/f]` at a divisor pair, for its equation `f`, is `1`. -/
@[simp]
theorem residue_dlogClass_eqnUnit (P : DivisorPair k) :
    residue P.compl (isUnit_natCast_add_one k) P.isSmoothPrincipalPair (dlogClass k P.eqnUnit) =
      1 :=
  residue_dlogClass _ _ (by simp)

/-! ### `lem:dr-tau`: the logarithmic classes of the instance -/

section Tau

/-- **The class `τ` of the de Rham instance is `[dx/x] t`.** Here `x` is the coordinate of
`k[x, x⁻¹]`, and `t` is the coefficient `T 1` of the instance. The class `[dx/x] t` has bidegree
`(1, 1)` and residue `1`, and `τ` is the unique such class.

Blueprint: `lem:dr-tau`. -/
theorem ordinaryTheory_tau :
    (ordinaryTheory k).tau = twistedClass 1 (dlogClass k (laurentT (point k))) := by
  refine ((ordinaryTheory k).eq_tau_of_mem_grading
    (twistedClass_mem_grading 1 (dlogClass_mem_grading _)) ?_).symm
  -- `(standardPair A).compl` is `laurent A` only at default transparency, so `rw` cannot use the
  -- residue lemma: the last step is an `exact`.
  have h := residue_dlogClass (T := (standardPair (point k)).compl) (isUnit_natCast_add_one k)
    (standardPair (point k)).isSmoothPrincipalPair (u := laurentT (point k))
    (polynomialToLaurent_polynomialX (point k)).symm
  rw [stdResidue_twistedClass, sub_self]
  exact (congrArg (twistedClass (A := (standardPair (point k)).closed) 0) h).trans
    twistedClass_zero_one

/-- **The logarithmic class of a unit `u` in the de Rham instance is `[du/u] t`**, on every smooth
algebra. It is the pullback of `τ = [dx/x] t` along `x ↦ u`, and `dx/x` pulls back to `du/u`.

Not a `simp` lemma, so that the generic lemmas about `logClass` fire on the instance.

Blueprint: `lem:dr-tau`. -/
theorem ordinaryTheory_logClass {A : SmoothAlg k} (u : Aˣ) :
    (ordinaryTheory k).logClass u = twistedClass 1 (dlogClass k u) := by
  rw [OrdinaryTheory.logClass, ordinaryTheory_tau, map_twistedClass, map_dlogClass]
  congr 2
  ext
  simp

/-- Removing the power of `t` from the logarithmic class of `u` gives `[du/u]`. -/
@[simp]
theorem evalOne_logClass {A : SmoothAlg k} (u : Aˣ) :
    TwistedCohomology.evalOne k A ((ordinaryTheory k).logClass u) = dlogClass k u := by
  rw [ordinaryTheory_logClass, evalOne_twistedClass]

end Tau

/-! ### `cor:dr-affine` -/

section Affine

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (𝒜 : Arrangement k V)

/-- **The Orlik–Solomon theorem for de Rham cohomology.** For every field `k` of characteristic zero
and every arrangement `𝒜` of affine hyperplanes in a finite-dimensional `k`-vector space, the
Orlik–Solomon algebra `OS_k(𝒜)` is isomorphic, as a graded `k`-algebra, to the algebraic de Rham
cohomology `H^•_dR(U_𝒜/k)` of the complement. It sends the generator `e_H` to the class
`[df_H / f_H]` of any equation `f_H` of `H`, by `affineEquiv_generator_of_isEquation`, and degree
`q` to `H^q_dR(U_𝒜/k)`, by `affineEquiv_mem_degree_iff`.

`affineDirectSumEquiv` is the same map with its target written as `⨁ q, H^q_dR(U_𝒜/k)`.

Blueprint: `cor:dr-affine`. -/
def affineEquiv : OSAlgebra k 𝒜 ≃ₐ[k] Cohomology k (complement 𝒜) :=
  ((ordinaryTheory k).diagonalEquiv 𝒜).trans
    (TwistedCohomology.diagonalEquiv k (complement 𝒜)).symm

/-- How `affineEquiv` is built: the realization map of the de Rham instance, followed by the removal
of the powers of `t`. -/
theorem affineEquiv_apply (x : OSAlgebra k 𝒜) :
    affineEquiv 𝒜 x = TwistedCohomology.evalOne k _ ((ordinaryTheory k).realizationOverR 𝒜 x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <|
    congrArg (TwistedCohomology.evalOne k _) ((ordinaryTheory k).coeAlgHom_diagonalEquiv x)

variable {𝒜}

/-- The isomorphism sends a generator `e_H` to `[df/f]`, for the chosen equation `f` of `H`.
`affineEquiv_generator_of_isEquation` allows any equation.

Blueprint: `cor:dr-affine`. -/
@[simp]
theorem affineEquiv_generator (H : 𝒜) :
    affineEquiv 𝒜 (generator k 𝒜 H) = dlogClass k (equationUnit 𝒜 H) := by
  rw [affineEquiv_apply, OrdinaryTheory.realizationOverR_generator, evalOne_logClass]

/-- **The isomorphism sends `e_H` to `[df/f]` for any equation `f` of `H`.** So the map does not
depend on the equations. Since `f` is not on the left, `simp` needs the equation to be given.

Blueprint: `cor:dr-affine`. -/
theorem affineEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    affineEquiv 𝒜 (generator k 𝒜 H) = dlogClass k (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [affineEquiv_apply, OrdinaryTheory.realizationOverR_generator_of_isEquation _ H hf,
    evalOne_logClass]

/-- The generator formula for a label presented by an equation. Here `f` is on the left, so `simp`
uses this with no further input. -/
@[simp high]
theorem affineEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    affineEquiv 𝒜 (generator k 𝒜 ⟨zeroLocus f, hf⟩) =
      dlogClass k (complementUnit 𝒜 f (.of_mem hf)) :=
  affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The isomorphism sends degree `q` into `H^q_dR(U_𝒜/k)`. -/
theorem isHomogeneousOfShift_affineEquiv :
    IsHomogeneousOfShift (degree k 𝒜) (Cohomology.degree k (complement 𝒜)) 0 (affineEquiv 𝒜) := by
  intro q x hx
  obtain ⟨c, hc, hcx⟩ := mem_grading_ordinaryTheory_iff.1
    ((ordinaryTheory k).realizationOverR_mem_grading hx)
  rw [add_zero, affineEquiv_apply, ← hcx, evalOne_twistedClass, ← Cohomology.grading_natCast]
  exact hc

/-- **The isomorphism is graded**: it identifies `OS_k^q(𝒜)` with `H^q_dR(U_𝒜/k)`.

Blueprint: `cor:dr-affine`. -/
theorem affineEquiv_mem_degree_iff {q : ℕ} {x : OSAlgebra k 𝒜} :
    affineEquiv 𝒜 x ∈ Cohomology.degree k (complement 𝒜) q ↔ x ∈ degree k 𝒜 q :=
  ⟨isHomogeneousOfShift_affineEquiv.mem_of_map_mem (affineEquiv 𝒜).injective (add_zero q),
    isHomogeneousOfShift_affineEquiv.map_mem (add_zero q)⟩

variable (𝒜) in
/-- The isomorphism in degree `q`: `OS_k^q(𝒜) ≃ₗ[k] H^q_dR(U_𝒜/k)`.

Blueprint: `cor:dr-affine`. -/
def affineDegreeEquiv (q : ℕ) : degree k 𝒜 q ≃ₗ[k] Cohomology.degree k (complement 𝒜) q :=
  isHomogeneousOfShift_affineEquiv.componentEquiv (e := (affineEquiv 𝒜).toLinearEquiv) (add_zero q)

@[simp]
theorem coe_affineDegreeEquiv_apply (q : ℕ) (x : degree k 𝒜 q) :
    (affineDegreeEquiv 𝒜 q x : Cohomology k (complement 𝒜)) = affineEquiv 𝒜 x :=
  rfl

variable (𝒜) in
/-- **The Orlik–Solomon theorem for de Rham cohomology, as a direct sum**:
`OS_k(𝒜) ≃ₐ[k] ⨁_{q ≥ 0} H^q_dR(U_𝒜/k)`, the display of `cor:dr-affine`. It is `affineEquiv`
followed by the decomposition of de Rham cohomology into its degrees, and it sends degree `q` to the
summand of degree `q`, by `affineDirectSumEquiv_of_mem_degree`.

Blueprint: `cor:dr-affine`. -/
def affineDirectSumEquiv : OSAlgebra k 𝒜 ≃ₐ[k] ⨁ q : ℕ, Cohomology.degree k (complement 𝒜) q :=
  (affineEquiv 𝒜).trans (decomposeAlgEquiv (Cohomology.degree k (complement 𝒜)))

/-- The component of degree `q` of the image of `x` is the image of the component of degree `q` of
`x`. -/
@[simp]
theorem coe_affineDirectSumEquiv_apply (x : OSAlgebra k 𝒜) (q : ℕ) :
    (affineDirectSumEquiv 𝒜 x q : Cohomology k (complement 𝒜)) =
      affineEquiv 𝒜 (decompose (degree k 𝒜) x q) :=
  isHomogeneousOfShift_affineEquiv.decompose_map (add_zero q) x

/-- On an element of degree `q`, the direct sum form is `affineEquiv`, in the summand of degree
`q`. -/
theorem affineDirectSumEquiv_of_mem_degree {q : ℕ} {x : OSAlgebra k 𝒜} (hx : x ∈ degree k 𝒜 q) :
    affineDirectSumEquiv 𝒜 x =
      of (fun q ↦ Cohomology.degree k (complement 𝒜) q) q
        ⟨affineEquiv 𝒜 x, affineEquiv_mem_degree_iff.2 hx⟩ :=
  decompose_of_mem (Cohomology.degree k (complement 𝒜)) (affineEquiv_mem_degree_iff.2 hx)

/-- The direct sum form sends `e_H` to `[df/f]` in the summand of degree one. -/
@[simp]
theorem affineDirectSumEquiv_generator (H : 𝒜) :
    affineDirectSumEquiv 𝒜 (generator k 𝒜 H) =
      of (fun q ↦ Cohomology.degree k (complement 𝒜) q) 1
        ⟨dlogClass k (equationUnit 𝒜 H), dlogClass_mem_degree _⟩ :=
  (affineDirectSumEquiv_of_mem_degree (generator_mem_degree k 𝒜 H)).trans <|
    congrArg (of _ 1) (Subtype.ext (affineEquiv_generator H))

variable (𝒜) in
/-- **`dim_k H^q_dR(U_𝒜/k) = b_q(𝒜)`**, the coefficient of `X^q` in the Poincaré polynomial of `𝒜`.

Blueprint: `cor:dr-affine` with `thm:betti`. -/
theorem finrank_degree_complement (q : ℕ) :
    finrank k (Cohomology.degree k (complement 𝒜) q) = 𝒜.bettiNumber q := by
  obtain ⟨b⟩ := (ordinaryTheory k).nonempty_basis_degree_bettiNumber 𝒜 q
  rw [← (affineDegreeEquiv 𝒜 q).finrank_eq, finrank_eq_card_basis b, Fintype.card_fin]

end Affine

/-! ### `cor:dr-projective` -/

section Projective

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

/-- **The projective Orlik–Solomon theorem for de Rham cohomology.** For every field `k` of
characteristic zero and every nonempty arrangement `P` of hyperplanes in `ℙ(W)`, the projective
Orlik–Solomon algebra `pOS_k(P)`, the kernel of the boundary on `OS_k` of the cone, is isomorphic,
as a graded `k`-algebra, to the algebraic de Rham cohomology `H^•_dR(U_P/k)` of the complement. It
sends `e_i - e_j` to `[d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]` for any equations `ℓ_i` and `ℓ_j`, by
`projectiveEquiv_difference_of_ker_eq`, and degree `q` to `H^q_dR(U_P/k)`, by
`projectiveEquiv_mem_degree_iff`.

No hyperplane at infinity is chosen: `map_projectiveToCone_projectiveEquiv` says that the map is
the affine one of the cone, after pullback to the complement of the cone. The empty arrangement is
excluded by `[Nonempty P]`, as in the blueprint.

Blueprint: `cor:dr-projective`. -/
def projectiveEquiv :
    projectiveAlgebra k P.cone_isCentral ≃ₐ[k] Cohomology k (projectiveComplement P) :=
  ((ordinaryTheory k).projectiveDiagonalEquiv P).trans
    (TwistedCohomology.diagonalEquiv k (projectiveComplement P)).symm

/-- How `projectiveEquiv` is built: the projective realization map of the de Rham instance,
followed by the removal of the powers of `t`. -/
theorem projectiveEquiv_apply (x : projectiveAlgebra k P.cone_isCentral) :
    projectiveEquiv P x =
      TwistedCohomology.evalOne k _ ((ordinaryTheory k).projectiveRealizationOverR P x) :=
  (TwistedCohomology.diagonalEquiv_symm_apply _).trans <| congrArg (TwistedCohomology.evalOne k _)
    ((ordinaryTheory k).coeAlgHom_projectiveDiagonalEquiv P x)

/-- **The projective isomorphism is the affine one of the cone**, after pullback to the complement
of the cone. Pullback is injective, so this characterizes it, and it involves no hyperplane at
infinity.

Blueprint: `cor:dr-projective`. -/
theorem map_projectiveToCone_projectiveEquiv (x : projectiveAlgebra k P.cone_isCentral) :
    Cohomology.map (algHom (projectiveToCone P)) (projectiveEquiv P x) =
      affineEquiv P.cone (x : OSAlgebra k P.cone) := by
  rw [projectiveEquiv_apply, affineEquiv_apply]
  exact (TwistedCohomology.evalOne_map _ _).symm.trans <| congrArg (TwistedCohomology.evalOne k _)
    ((ordinaryTheory k).map_projectiveToCone_projectiveRealizationOverR P x)

variable {P}

/-- The isomorphism sends `e_ℓ - e_ℓ'` to `[d(ℓ/ℓ') / (ℓ/ℓ')]`, for the hyperplanes `ker ℓ` and
`ker ℓ'` of `P`. Here the equations are on the left, so `simp` uses this with no further input.

Blueprint: `cor:dr-projective`. -/
@[simp]
theorem projectiveEquiv_difference {ℓ ℓ' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    projectiveEquiv P (projectiveDifference k P.cone_isCentral
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ, hℓ⟩)
      (P.coneHyperplaneEquiv ⟨LinearMap.ker ℓ', hℓ'⟩)) =
      dlogClass k (projectiveRatioUnit hℓ hℓ') := by
  rw [projectiveEquiv_apply, OrdinaryTheory.projectiveRealizationOverR_difference,
    evalOne_logClass]

/-- **The isomorphism sends `e_i - e_j` to `[d(ℓ_i/ℓ_j) / (ℓ_i/ℓ_j)]` for any equations `ℓ_i` and
`ℓ_j` of the hyperplanes `H` and `K`.** So the map does not depend on the equations.

Blueprint: `cor:dr-projective`. -/
theorem projectiveEquiv_difference_of_ker_eq (H K : P) {ℓ ℓ' : Dual k W}
    (hℓ : LinearMap.ker ℓ = (H : Submodule k W)) (hℓ' : LinearMap.ker ℓ' = (K : Submodule k W)) :
    projectiveEquiv P (projectiveDifference k P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      dlogClass k (projectiveRatioUnit (ℓ := ℓ) (ℓ' := ℓ')
        (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)) := by
  rw [projectiveEquiv_apply, OrdinaryTheory.projectiveRealizationOverR_difference_of_ker_eq _ P H K
    hℓ hℓ', evalOne_logClass]

/-- The projective isomorphism sends degree `q` into `H^q_dR(U_P/k)`. -/
theorem isHomogeneousOfShift_projectiveEquiv :
    IsHomogeneousOfShift (projectiveDegree k P.cone_isCentral)
      (Cohomology.degree k (projectiveComplement P)) 0 (projectiveEquiv P) := by
  intro q x hx
  obtain ⟨c, hc, hcx⟩ := mem_grading_ordinaryTheory_iff.1
    ((ordinaryTheory k).projectiveRealizationOverR_mem_grading P hx)
  rw [add_zero, projectiveEquiv_apply, ← hcx, evalOne_twistedClass, ← Cohomology.grading_natCast]
  exact hc

/-- **The projective isomorphism is graded**: it identifies the degree `q` part of `pOS_k(P)` with
`H^q_dR(U_P/k)`.

Blueprint: `cor:dr-projective`. -/
theorem projectiveEquiv_mem_degree_iff {q : ℕ} {x : projectiveAlgebra k P.cone_isCentral} :
    projectiveEquiv P x ∈ Cohomology.degree k (projectiveComplement P) q ↔
      x ∈ projectiveDegree k P.cone_isCentral q :=
  ⟨isHomogeneousOfShift_projectiveEquiv.mem_of_map_mem (projectiveEquiv P).injective (add_zero q),
    isHomogeneousOfShift_projectiveEquiv.map_mem (add_zero q)⟩

variable (P) in
/-- The projective isomorphism in degree `q`.

Blueprint: `cor:dr-projective`. -/
def projectiveDegreeEquiv (q : ℕ) :
    projectiveDegree k P.cone_isCentral q ≃ₗ[k] Cohomology.degree k (projectiveComplement P) q :=
  isHomogeneousOfShift_projectiveEquiv.componentEquiv (e := (projectiveEquiv P).toLinearEquiv)
    (add_zero q)

@[simp]
theorem coe_projectiveDegreeEquiv_apply (q : ℕ) (x : projectiveDegree k P.cone_isCentral q) :
    (projectiveDegreeEquiv P q x : Cohomology k (projectiveComplement P)) = projectiveEquiv P x :=
  rfl

variable (P) in
/-- **The projective theorem as a direct sum**: `pOS_k(P) ≃ₐ[k] ⨁_{q ≥ 0} H^q_dR(U_P/k)`, the
display of `cor:dr-projective`.

Blueprint: `cor:dr-projective`. -/
def projectiveDirectSumEquiv :
    projectiveAlgebra k P.cone_isCentral ≃ₐ[k]
      ⨁ q : ℕ, Cohomology.degree k (projectiveComplement P) q :=
  (projectiveEquiv P).trans (decomposeAlgEquiv (Cohomology.degree k (projectiveComplement P)))

/-- The component of degree `q` of the image of `x` is the image of the component of degree `q` of
`x`. -/
@[simp]
theorem coe_projectiveDirectSumEquiv_apply (x : projectiveAlgebra k P.cone_isCentral) (q : ℕ) :
    (projectiveDirectSumEquiv P x q : Cohomology k (projectiveComplement P)) =
      projectiveEquiv P (decompose (projectiveDegree k P.cone_isCentral) x q) :=
  isHomogeneousOfShift_projectiveEquiv.decompose_map (add_zero q) x

/-- On an element of degree `q`, the direct sum form is `projectiveEquiv`, in the summand of degree
`q`. -/
theorem projectiveDirectSumEquiv_of_mem_degree {q : ℕ} {x : projectiveAlgebra k P.cone_isCentral}
    (hx : x ∈ projectiveDegree k P.cone_isCentral q) :
    projectiveDirectSumEquiv P x =
      of (fun q ↦ Cohomology.degree k (projectiveComplement P) q) q
        ⟨projectiveEquiv P x, projectiveEquiv_mem_degree_iff.2 hx⟩ :=
  decompose_of_mem (Cohomology.degree k (projectiveComplement P))
    (projectiveEquiv_mem_degree_iff.2 hx)

variable (P) in
/-- **`dim_k H^q_dR(U_P/k)` is the projective Betti number `b_q(P)`.**

Blueprint: `cor:dr-projective` with `cor:projective-betti`. -/
theorem finrank_degree_projectiveComplement (q : ℕ) :
    finrank k (Cohomology.degree k (projectiveComplement P) q) = P.bettiNumber q := by
  obtain ⟨b⟩ := (ordinaryTheory k).nonempty_basis_projective_grading_bettiNumber P q
  rw [(TwistedCohomology.degreeEquiv k (projectiveComplement P) q q).finrank_eq]
  exact (finrank_eq_card_basis b).trans (Fintype.card_fin _)

end Projective

end OrlikSolomon.DeRham
