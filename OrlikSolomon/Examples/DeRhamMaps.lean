/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Maps.Naturality
public import OrlikSolomon.Examples.DeRhamLog

/-!
# Regressions for the Gysin map, the logarithmic residue and naturality

These check what is easy to get wrong about `DeRham/Maps/Gysin` and `DeRham/Maps/Naturality`: the
signs, the empty divisor, the zero algebra, a map of pairs that is not flat, and that everything
applies to divisor pairs and their morphisms directly.

## Main results

* `OrlikSolomon.DeRham.Examples.residue_mk_theta`: the class of `θ` has residue one.
* `OrlikSolomon.DeRham.Examples.residue_mk_theta_mul` and
  `OrlikSolomon.DeRham.Examples.residue_ofCohomology_mul_mk_theta`: the right projection formula has
  no sign, and the left one has the grade involution.
* `OrlikSolomon.DeRham.Examples.gysin_mk_eq_neg_mk`: the sign in `G[γ] = [-θ ∧ dη]`.
* `OrlikSolomon.DeRham.Examples.ofCohomology_bijective_of_subsingleton`: for an empty divisor, the
  exact sequence says that `H^•(A) → H^•(L)` is bijective.
* `OrlikSolomon.DeRham.Examples.nonFlatHom`, with
  `OrlikSolomon.DeRham.Examples.not_flat_nonFlatAmbient`: the morphism
  `(k[z, v], z) → (k[x, y, y⁻¹], x)`, `z ↦ x y`, `v ↦ 0`, of `prop:dr-morphism-examples`, which is
  not flat, and to which naturality applies.
-/

@[expose] public section

namespace OrlikSolomon.DeRham.Examples

open CategoryTheory
open CliffordAlgebra (involute)

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {S : Type*} [CommRing S] [Algebra k S] {f : A} {φ : A →ₐ[k] S}

section Signs

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

variable (k f) in
/-- The class of `θ` in `H^1(L)`. -/
noncomputable abbrev thetaClass : LogCohomology k f T :=
  LogCohomology.mk ⟨θ, theta_mem_logForms k f T⟩ (Subtype.ext (d_theta k f T))

/-- `H(ρ)[θ] = 1`. -/
theorem residue_mk_theta (h : IsSmoothPrincipalPair f φ) :
    LogCohomology.residue T h (thetaClass k f T) = 1 := by
  rw [LogCohomology.residue_mk, ← Cohomology.mk_one (by simp)]
  exact Cohomology.mk_congr (logResidue_theta h) _

/-- `H(ρ)([θ] ∧ j_* b) = i_* b`, with no sign in any degree. -/
theorem residue_mk_theta_mul (h : IsSmoothPrincipalPair f φ) (b : Cohomology k A) :
    LogCohomology.residue T h (thetaClass k f T * LogCohomology.ofCohomology k f T b) =
      Cohomology.map φ b := by
  rw [LogCohomology.residue_mul_ofCohomology, residue_mk_theta, one_mul]

/-- `H(ρ)(j_*[β] ∧ [θ]) = [σ(β|_S)]`, with `σ` the grade involution, so that the left projection
formula has the sign `(-1)^q` for `β` of degree `q`. -/
theorem residue_ofCohomology_mul_mk_theta (h : IsSmoothPrincipalPair f φ) {β : Forms k A}
    (hβ : d k β = 0) (hσ : d k (involute (Forms.map φ β)) = 0) :
    LogCohomology.residue T h
        (LogCohomology.ofCohomology k f T (Cohomology.mk β hβ) * thetaClass k f T) =
      Cohomology.mk (involute (Forms.map φ β)) hσ := by
  rw [LogCohomology.ofCohomology_mk, LogCohomology.mk_mul, LogCohomology.residue_mk]
  exact Cohomology.mk_congr
    ((logResidue_ofRegular_mul h β _).trans (by rw [logResidue_theta, mul_one])) _

/-- The sign in `G[γ] = [-θ ∧ dη]`: if `θ ∧ dη` is the regular form `ω`, then `G[γ] = -[ω]`. It is
the minus sign of `d(θ ∧ η) = -θ ∧ dη`. It is not `(-1)^q`. -/
theorem gysin_mk_eq_neg_mk (h : IsSmoothPrincipalPair f φ) {γ : Forms k S} (hγ : d k γ = 0)
    {η : Forms k A} (hη : Forms.map φ η = γ) {ω : Forms k A} (hω : reg ω = θ * reg (d k η))
    (hc : d k ω = 0) : gysin T h (Cohomology.mk γ hγ) = -Cohomology.mk ω hc := by
  rw [Cohomology.mk_neg]
  exact gysin_mk_of_map_eq h hγ hη (by rw [map_neg, hω])

end Signs

section Empty

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- If the divisor is empty, in the sense that the closed part is zero, then the exact sequence says
that `H^•(A) → H^•(L)` is bijective. This includes the unit equation, and the zero algebra.

Blueprint: `prop:dr-unit-example`, `prop:dr-zero-example`. -/
theorem ofCohomology_bijective_of_subsingleton [Subsingleton S] (h : IsSmoothPrincipalPair f φ) :
    Function.Bijective (LogCohomology.ofCohomology k f T) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := (exact_gysin_ofCohomology T h c).1 hc
    rw [Subsingleton.elim y 0, map_zero]
  · exact (LogCohomology.exact_ofCohomology_residue T h c).1 (Subsingleton.elim _ _)

end Empty

section DivisorPair

variable (P Q : DivisorPair k) (F : P ⟶ Q)

/-- The logarithmic long exact sequence applies directly to a divisor pair. -/
example : Function.Exact (gysin P.compl P.isSmoothPrincipalPair)
    (LogCohomology.ofCohomology k P.eqn P.compl) :=
  exact_gysin_ofCohomology _ _

/-- The map `χ_*` takes logarithmic forms to logarithmic forms, for a morphism of divisor pairs. -/
example {x : Forms k P.compl} (hx : x ∈ logForms k P.eqn P.compl) :
    Forms.map (SmoothAlg.algHom F.compl) x ∈ logForms k Q.eqn Q.compl :=
  F.isPairHom.map_mem_logForms hx

/-- The Gysin map is natural for a morphism of divisor pairs. -/
example (c : Cohomology k P.closed) :
    gysin Q.compl Q.isSmoothPrincipalPair (Cohomology.map (SmoothAlg.algHom F.closed) c) =
      Cohomology.map (SmoothAlg.algHom F.ambient) (gysin P.compl P.isSmoothPrincipalPair c) :=
  gysin_map F.isPairHom _ _ c

/-- `H(ρ)` is natural for a morphism of divisor pairs. -/
example (c : LogCohomology k P.eqn P.compl) :
    LogCohomology.residue Q.compl Q.isSmoothPrincipalPair (LogCohomology.map F.isPairHom c) =
      Cohomology.map (SmoothAlg.algHom F.closed)
        (LogCohomology.residue P.compl P.isSmoothPrincipalPair c) :=
  LogCohomology.residue_map F.isPairHom _ _ c

end DivisorPair

section NonFlat

open DivisorPair SmoothAlg

variable (k)

/-- The map `k[v] → k[y, y⁻¹]` with `v ↦ 0`. -/
noncomputable def killVariable : polynomial (point k) ⟶ laurent (point k) :=
  polynomialLift (fromPoint _) 0

/-- The map of ambient algebras `k[v][z] → k[y, y⁻¹][x]` with `z ↦ y x` and `v ↦ 0`. -/
noncomputable def nonFlatAmbient :
    polynomial (polynomial (point k)) ⟶ polynomial (laurent (point k)) :=
  polynomialLift (killVariable k ≫ polynomialC _)
    (polynomialC _ (laurentT (point k) : laurent (point k)) * polynomialX _)

/-- The map `nonFlatAmbient` sends `z` to `y x`. -/
@[simp]
theorem nonFlatAmbient_polynomialX :
    nonFlatAmbient k (polynomialX _) =
      polynomialC _ (laurentT (point k) : laurent (point k)) * polynomialX _ :=
  polynomialLift_polynomialX _ _

/-- The map `nonFlatAmbient` kills `v`. -/
@[simp]
theorem nonFlatAmbient_polynomialC_polynomialX :
    nonFlatAmbient k (polynomialC _ (polynomialX (point k))) = 0 := by
  rw [nonFlatAmbient, polynomialLift_polynomialC]
  change polynomialC _ (killVariable k (polynomialX (point k))) = 0
  rw [killVariable, polynomialLift_polynomialX, map_zero]

/-- The morphism of pairs `(k[v][z], z) → (k[y, y⁻¹][x], x)` with `z ↦ y x` and `v ↦ 0`. Its map of
ambient algebras is `nonFlatAmbient`. It is not flat, by `not_flat_nonFlatAmbient`, and everything
natural for morphisms of pairs applies to it.

Blueprint: `prop:dr-morphism-examples`. -/
noncomputable def nonFlatHom :
    standardPair (polynomial (point k)) ⟶ standardPair (laurent (point k)) :=
  standardMap (killVariable k) (laurentT (point k))

theorem nonFlatHom_ambient : (nonFlatHom k).ambient = nonFlatAmbient k :=
  rfl

/-- The constant `X` is left regular in `R[X][X]`. -/
theorem isLeftRegular_C_X (R : Type*) [CommRing R] :
    IsLeftRegular (Polynomial.C Polynomial.X : Polynomial (Polynomial R)) := by
  intro p q hpq
  ext n : 2
  refine Polynomial.isRegular_X.left ?_
  simpa only [Polynomial.coeff_C_mul] using
    congrArg (fun r : Polynomial (Polynomial R) => r.coeff n) hpq

/-- The map `nonFlatAmbient` is not flat: multiplication by `v` is injective on `k[v][z]`, and `v`
goes to zero in a nonzero algebra.

Blueprint: `prop:dr-morphism-examples`. -/
theorem not_flat_nonFlatAmbient [Nontrivial k] :
    letI := (algHom (nonFlatAmbient k)).toRingHom.toAlgebra
    ¬ Module.Flat (polynomial (polynomial (point k))) (polynomial (laurent (point k))) := by
  let := (algHom (nonFlatAmbient k)).toRingHom.toAlgebra
  intro hflat
  have hreg : IsSMulRegular (polynomial (polynomial (point k)))
      (polynomialC (polynomial (point k)) (polynomialX (point k))) :=
    isLeftRegular_C_X k
  have h0 := hreg.of_flat (S := polynomial (laurent (point k)))
  have hv : algebraMap (polynomial (polynomial (point k))) (polynomial (laurent (point k)))
      (polynomialC (polynomial (point k)) (polynomialX (point k))) = 0 :=
    nonFlatAmbient_polynomialC_polynomialX k
  rw [hv] at h0
  have : Nontrivial (polynomial (laurent (point k))) :=
    inferInstanceAs (Nontrivial (Polynomial (LaurentPolynomial k)))
  exact one_ne_zero (h0 (a₁ := 1) (a₂ := 0) (by simp only [zero_smul]))

/-- Naturality of the Gysin map for the morphism that is not flat. -/
example (c : Cohomology k (polynomial (point k))) :
    gysin (standardPair (laurent (point k))).compl (standardPair _).isSmoothPrincipalPair
        (Cohomology.map (algHom (nonFlatHom k).closed) c) =
      Cohomology.map (algHom (nonFlatHom k).ambient)
        (gysin (standardPair (polynomial (point k))).compl (standardPair _).isSmoothPrincipalPair
          c) :=
  gysin_map (nonFlatHom k).isPairHom _ _ c

end NonFlat

end OrlikSolomon.DeRham.Examples
