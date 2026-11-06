/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.ProjectiveRing

/-!
# Decone and cone geometry

For an equation `ℓ₀` of a hyperplane `H₀` of a projective arrangement `P`, this file proves that the
projective complement `U_P` is the complement of the decone in the slice `ℓ₀ = 1`, and that the
complement `V_P` of the central cone is the product `U_P × 𝔾ₘ`. Everything is an identity of
coordinate rings, so the maps are inverse on the level of schemes, and not only on rational points.
It then defines the objects of `SmoothAlg k`.

## Main definitions

* `ComplementRing.restrictSlice`: restriction of functions from `V_P` to the decone complement.
* `ComplementRing.deconeEquiv`: the isomorphism `O(U_P) ≃ O(U_{d_{H₀}P})`.
* `ComplementRing.coneEquiv`: the isomorphism `O(V_P) ≃ O(U_P)[t;t⁻¹]`, for the map
  `v ↦ (v / ℓ₀(v), ℓ₀(v))` with inverse `(u, t) ↦ t u`.
* `SmoothAlg.projectiveComplement P`: the object `O(U_P)` of `SmoothAlg k`, for nonempty `P`.
* `SmoothAlg.projectiveToCone`, `SmoothAlg.projectiveRatioUnit`: the pullback along `V_P → U_P`, and
  the units given by ratios of equations.
* `SmoothAlg.deconeIso`, `SmoothAlg.coneIso`: the isomorphisms, in `SmoothAlg k`.

## Main results

* `ComplementRing.coneEquiv_algebraMap_coord`, `SmoothAlg.mapUnits_coneIso_hom_complementUnit`:
  under `V_P ≃ U_P × 𝔾ₘ`, an equation `ℓ` is `t (ℓ / ℓ₀)`.
* `ComplementRing.deconeEquiv_ratio_mul`, `SmoothAlg.mapUnits_deconeIso_hom_projectiveRatioUnit`:
  under the decone isomorphism, a ratio is the quotient of the restrictions to the slice.
* `SmoothAlg.projectiveToCone_comp_coneIso_hom_comp_laurentSection`: the pullback along `V_P → U_P`
  has a retraction, by the section `t = 1`, so it is injective on cohomology.

## Implementation notes

The hypothesis `hℓ₀ : LinearMap.ker ℓ₀ ∈ P` says that `ℓ₀` is an equation of a hyperplane of `P`,
and it is all that these statements need. The empty arrangement is excluded because it has no such
`ℓ₀`: no fake hyperplane at infinity is chosen.

## Blueprint

`lem:decone`, and the cone and decone part of `lem:geometry-adapter`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Module
open scoped LaurentPolynomial

universe u

namespace OrlikSolomon

open CoordinateRing

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {ℓ ℓ' ℓ₀ ξ η : Dual k W}

namespace ComplementRing

/-! ### The decone

The ring `O(U_P)` is identified with the ring of the decone complement by restricting functions to
the slice in one direction, and by dehomogenizing in the other. -/

section Decone

/-- Every hyperplane of the cone has a trace on the slice that is covered by the decone: it is `⊥`
for `H₀`, and a hyperplane of the decone for the others. So restricting to the slice takes the
complement of the decone to the complement of the cone. -/
theorem decone_covers_comap (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) {K : AffineSubspace k W}
    (hK : K ∈ P.cone) : (P.decone ℓ₀).Covers (K.comap (chart (slice ℓ₀))) := by
  have h₀ := ne_zero_of_ker_mem hℓ₀
  refine Arrangement.covers_comap_comap hK fun htop ↦ ?_
  obtain ⟨M, hM, rfl⟩ := mem_cone.1 hK
  exact not_slice_le_toAffineSubspace h₀ (P.isCoatom hM)
    ((comap_chart_eq_top_iff (slice_ne_bot h₀)).1 htop)

/-- A linear form with kernel in `P` restricts to an affine function on the slice whose zero locus
is covered by the decone. It is a nonzero constant for an equation of `H₀`, and an equation of a
hyperplane of the decone otherwise. -/
theorem decone_covers (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (hℓ : LinearMap.ker ℓ ∈ P) :
    (P.decone ℓ₀).Covers (zeroLocus (ℓ.toAffineMap.comp (chart (slice ℓ₀)))) := by
  rw [zeroLocus_comp]
  exact decone_covers_comap hℓ₀ (zeroLocus_toAffineMap_mem_cone hℓ)

/-- The restriction of functions from the complement of the cone to the complement of the decone in
the slice. -/
def restrictSlice (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.ComplementRing →ₐ[k] (P.decone ℓ₀).ComplementRing :=
  Arrangement.ComplementRing.map (chart (slice ℓ₀)) P.cone (P.decone ℓ₀)
    fun _ hK ↦ decone_covers_comap hℓ₀ hK

@[simp]
theorem restrictSlice_algebraMap (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    restrictSlice hℓ₀ (algebraMap _ _ x) = algebraMap _ _ (pull (chart (slice ℓ₀)) x) :=
  Arrangement.ComplementRing.map_algebraMap _ _ x

/-- Restricting to the slice after dehomogenizing is restricting to the slice. -/
theorem restrictSlice_toCone_dehomogenize (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    restrictSlice hℓ₀ (toCone P (dehomogenize hℓ₀ x)) =
      algebraMap _ _ (pull (chart (slice ℓ₀)) x) := by
  have h₀ := ne_zero_of_ker_mem hℓ₀
  have hu : restrictSlice hℓ₀ (algebraMap _ _ (coord ℓ₀.toAffineMap)) = 1 := by
    simp [h₀]
  have : ((restrictSlice hℓ₀).comp (toCone P)).comp (dehomogenize hℓ₀) =
      (Arrangement.ComplementRing.toComplementRing (P.decone ℓ₀)).comp
        (pull (chart (slice ℓ₀))) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun ξ ↦ ?_)
    change restrictSlice hℓ₀ (toCone P (dehomogenize hℓ₀ (SymmetricAlgebra.ι k _ ξ))) =
      algebraMap _ _ (pull (chart (slice ℓ₀)) (SymmetricAlgebra.ι k _ ξ))
    rw [← coord_toAffineMap, dehomogenize_coord_toAffineMap, ← mul_one (restrictSlice hℓ₀ _), ← hu,
      ← map_mul, toCone_ratio_mul, restrictSlice_algebraMap]
  exact congr($this x)

/-- The map `O((slice ℓ₀).direction) → O(U_P)` given by dehomogenizing. It is well defined because
the equation `ℓ₀ - 1` of the slice dehomogenizes to `ℓ₀ / ℓ₀ - 1 = 0`. -/
def dehomogenizeSlice (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    CoordinateRing k (slice ℓ₀).direction →ₐ[k] P.ComplementRing :=
  liftChart (slice_ne_bot (ne_zero_of_ker_mem hℓ₀)) ⟨dehomogenize hℓ₀, fun f hf ↦ by
    obtain ⟨c, rfl⟩ := (isEquation_sliceEquation (ne_zero_of_ker_mem hℓ₀)).exists_eq_smul hf
    simp [sliceEquation]⟩

@[simp]
theorem dehomogenizeSlice_pull (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    dehomogenizeSlice hℓ₀ (pull (chart (slice ℓ₀)) x) = dehomogenize hℓ₀ x :=
  liftChart_pull_chart _ _ x

/-- The map `O(U_{d_{H₀}P}) → O(U_P)` given by dehomogenizing. An equation of a hyperplane of the
decone is the trace of a form `ℓ` with kernel in `P`, and it goes to the unit `ℓ / ℓ₀`. -/
def deconeToComplement (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (P.decone ℓ₀).ComplementRing →ₐ[k] P.ComplementRing :=
  Arrangement.ComplementRing.lift (P.decone ℓ₀) (dehomogenizeSlice hℓ₀) fun L hL ↦ by
    obtain ⟨M, hM, hne, rfl⟩ := (mem_decone hℓ₀).1 hL
    obtain ⟨ℓ, rfl⟩ := exists_ker_eq hM
    refine ⟨ℓ.toAffineMap.comp (chart (slice ℓ₀)), isEquation_comp_chart_slice hℓ₀ hM hne, ?_⟩
    rw [← pull_coord, dehomogenizeSlice_pull, dehomogenize_coord_toAffineMap]
    exact (ratioUnit hM hℓ₀).isUnit

@[simp]
theorem deconeToComplement_algebraMap_pull (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (x : CoordinateRing k W) :
    deconeToComplement hℓ₀ (algebraMap _ _ (pull (chart (slice ℓ₀)) x)) = dehomogenize hℓ₀ x := by
  rw [deconeToComplement, Arrangement.ComplementRing.lift_algebraMap, dehomogenizeSlice_pull]

theorem deconeToComplement_restrictSlice_toCone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (x : P.ComplementRing) : deconeToComplement hℓ₀ (restrictSlice hℓ₀ (toCone P x)) = x := by
  obtain ⟨n, a, b, ha, hb, hbS, rfl⟩ := exists_mk_eq x
  have hx := toCone_mk_mul ha hb hbS
  refine (isUnit_dehomogenize hℓ₀ hbS).mul_left_injective ?_
  dsimp only
  rw [mul_dehomogenize_eq hℓ₀ ha hb hx]
  have := congr(deconeToComplement hℓ₀ (restrictSlice hℓ₀ $hx))
  simpa using this

/-- The projective complement is the decone complement: restricting functions to the slice is an
isomorphism `O(U_P) ≃ O(U_{d_{H₀}P})`, for an equation `ℓ₀` of any `H₀ ∈ P`. Its inverse
dehomogenizes with respect to `ℓ₀`. These are maps of coordinate rings, so they are inverse on the
level of schemes, not only on rational points.

Blueprint: `lem:decone`. -/
def deconeEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.ComplementRing ≃ₐ[k] (P.decone ℓ₀).ComplementRing :=
  .ofAlgHom ((restrictSlice hℓ₀).comp (toCone P)) (deconeToComplement hℓ₀)
    (Arrangement.ComplementRing.algHom_ext <| AlgHom.ext fun y ↦ by
      obtain ⟨x, rfl⟩ := pull_chart_surjective (slice ℓ₀) y
      simp [restrictSlice_toCone_dehomogenize])
    (AlgHom.ext <| deconeToComplement_restrictSlice_toCone hℓ₀)

theorem deconeEquiv_apply (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : P.ComplementRing) :
    deconeEquiv hℓ₀ x = restrictSlice hℓ₀ (toCone P x) :=
  rfl

@[simp]
theorem deconeEquiv_symm_algebraMap_pull (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    (deconeEquiv hℓ₀).symm (algebraMap _ _ (pull (chart (slice ℓ₀)) x)) = dehomogenize hℓ₀ x :=
  deconeToComplement_algebraMap_pull hℓ₀ x

@[simp]
theorem deconeEquiv_dehomogenize (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    deconeEquiv hℓ₀ (dehomogenize hℓ₀ x) = algebraMap _ _ (pull (chart (slice ℓ₀)) x) :=
  restrictSlice_toCone_dehomogenize hℓ₀ x

/-- Under the decone isomorphism, a ratio `ξ / ℓ` is the quotient of the restrictions of `ξ` and `ℓ`
to the slice.

Blueprint: `lem:decone`. -/
theorem deconeEquiv_ratio_mul (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (ξ : Dual k W)
    (hℓ : LinearMap.ker ℓ ∈ P) :
    deconeEquiv hℓ₀ (ratio ξ hℓ) *
        algebraMap _ _ (coord (ℓ.toAffineMap.comp (chart (slice ℓ₀)))) =
      algebraMap _ _ (coord (ξ.toAffineMap.comp (chart (slice ℓ₀)))) := by
  have := congr(restrictSlice hℓ₀ $(toCone_ratio_mul ξ hℓ))
  simpa [deconeEquiv_apply] using this

/-- Under the decone isomorphism, the ratio `ξ / ℓ₀` is the restriction of `ξ` to the slice, since
`ℓ₀` is `1` there.

Blueprint: `lem:decone`. -/
@[simp]
theorem deconeEquiv_ratio_self (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (ξ : Dual k W) :
    deconeEquiv hℓ₀ (ratio ξ hℓ₀) =
      algebraMap _ _ (coord (ξ.toAffineMap.comp (chart (slice ℓ₀)))) := by
  rw [← dehomogenize_coord_toAffineMap, deconeEquiv_dehomogenize, pull_coord]

end Decone

/-! ### The cone

The complement of the cone is the product of the projective complement with `𝔾ₘ`, by the maps
`v ↦ (v / ℓ₀(v), ℓ₀(v))` and `(u, t) ↦ t u`. -/

section Cone

variable {n : ℕ} {a b : CoordinateRing k W}

/-- The map `O(W) → O(U_P)[t;t⁻¹]` sending a linear form `ξ` to `t (ξ / ℓ₀)`. Geometrically, this is
the pullback along `U_P × 𝔾ₘ → W`, `(u, t) ↦ t u`. -/
def coneCoord (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) : CoordinateRing k W →ₐ[k] P.ComplementRing[T;T⁻¹] :=
  SymmetricAlgebra.lift <| LinearMap.mulLeft k (LaurentPolynomial.T 1) ∘ₗ
    (IsScalarTower.toAlgHom k P.ComplementRing P.ComplementRing[T;T⁻¹]).toLinearMap ∘ₗ
      ratioLinear hℓ₀

@[simp]
theorem coneCoord_coord_toAffineMap (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (ξ : Dual k W) :
    coneCoord hℓ₀ (coord ξ.toAffineMap) =
      LaurentPolynomial.T 1 * LaurentPolynomial.C (ratio ξ hℓ₀) := by
  rw [coord_toAffineMap, coneCoord, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- An element `a` of degree `n` is homogeneous of degree `n` in the coordinate `t`. -/
theorem coneCoord_of_mem (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (ha : a ∈ symmetricGrading k (Dual k W) n) :
    coneCoord hℓ₀ a =
      (LaurentPolynomial.T 1 : P.ComplementRing[T;T⁻¹]) ^ n *
        LaurentPolynomial.C (dehomogenize hℓ₀ a) :=
  apply_eq_pow_mul_of_mem_symmetricGrading
    (ψ := (IsScalarTower.toAlgHom k P.ComplementRing P.ComplementRing[T;T⁻¹]).comp
      (dehomogenize hℓ₀))
    (fun ξ ↦ by
      rw [← coord_toAffineMap, coneCoord_coord_toAffineMap, AlgHom.comp_apply,
        dehomogenize_coord_toAffineMap]
      rfl) ha

/-- The pullback `O(V_P) → O(U_P)[t;t⁻¹]` along `(u, t) ↦ t u`. An equation `ℓ` goes to the unit
`t (ℓ / ℓ₀)`. -/
def coneToLaurent (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.ComplementRing →ₐ[k] P.ComplementRing[T;T⁻¹] :=
  Arrangement.ComplementRing.lift P.cone (coneCoord hℓ₀) fun L hL ↦ by
    obtain ⟨M, hM, rfl⟩ := mem_cone.1 hL
    obtain ⟨ℓ, rfl⟩ := exists_ker_eq hM
    refine ⟨ℓ.toAffineMap, isEquation_toAffineMap (ne_zero_of_ker_mem hM), ?_⟩
    rw [coneCoord_coord_toAffineMap]
    exact (LaurentPolynomial.isUnit_T 1).mul ((ratioUnit hM hℓ₀).isUnit.map LaurentPolynomial.C)

@[simp]
theorem coneToLaurent_algebraMap (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : CoordinateRing k W) :
    coneToLaurent hℓ₀ (algebraMap _ _ x) = coneCoord hℓ₀ x :=
  Arrangement.ComplementRing.lift_algebraMap _ _ x

/-- A function on the projective complement, pulled back to its cone, is constant in `t`. -/
@[simp]
theorem coneToLaurent_toCone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : P.ComplementRing) :
    coneToLaurent hℓ₀ (toCone P x) = LaurentPolynomial.C x := by
  obtain ⟨n, a, b, ha, hb, hbS, rfl⟩ := exists_mk_eq x
  have hx := toCone_mk_mul ha hb hbS
  have hu : IsUnit (coneCoord hℓ₀ b) := by
    rw [← coneToLaurent_algebraMap]
    exact (IsLocalization.map_units P.cone.ComplementRing
      (⟨b, hbS⟩ : P.cone.equationSubmonoid)).map _
  refine hu.mul_left_injective ?_
  dsimp only
  have h := congr(coneToLaurent hℓ₀ $hx)
  rw [map_mul, coneToLaurent_algebraMap, coneToLaurent_algebraMap] at h
  rw [h, coneCoord_of_mem hℓ₀ ha, coneCoord_of_mem hℓ₀ hb, mul_left_comm, ← map_mul,
    mul_dehomogenize_eq hℓ₀ ha hb hx]

/-- The pullback `O(U_P)[t;t⁻¹] → O(V_P)` along `v ↦ (v / ℓ₀(v), ℓ₀(v))`: it is the inclusion on
`O(U_P)`, and it sends `t` to `ℓ₀`. -/
def laurentToCone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.ComplementRing[T;T⁻¹] →ₐ[k] P.cone.ComplementRing :=
  laurentPolynomialLift (toCone P) (coneUnit hℓ₀)

/-- The complement of the cone is the product of the projective complement with `𝔾ₘ`: for an
equation `ℓ₀` of any `H₀ ∈ P`, the maps `v ↦ (v / ℓ₀(v), ℓ₀(v))` and `(u, t) ↦ t u` are inverse.
This
is an isomorphism of coordinate rings, so they are inverse on the level of schemes, and not only on
rational points. The form `ℓ₀` is the coordinate `t` of the product.

Blueprint: `lem:decone`. -/
def coneEquiv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    P.cone.ComplementRing ≃ₐ[k] P.ComplementRing[T;T⁻¹] :=
  .ofAlgHom (coneToLaurent hℓ₀) (laurentToCone hℓ₀)
    (laurentPolynomial_algHom_ext (fun a ↦ by simp [laurentToCone]) (by simp [laurentToCone]))
    (Arrangement.ComplementRing.algHom_ext <| SymmetricAlgebra.algHom_ext <|
      LinearMap.ext fun ξ ↦ by
      change laurentToCone hℓ₀ (coneToLaurent hℓ₀ (algebraMap _ _ (SymmetricAlgebra.ι k _ ξ))) =
        algebraMap _ _ (SymmetricAlgebra.ι k _ ξ)
      rw [← coord_toAffineMap, coneToLaurent_algebraMap, coneCoord_coord_toAffineMap, map_mul,
        laurentToCone, laurentPolynomialLift_T, laurentPolynomialLift_C, toCone_ratio,
        mul_left_comm, Units.mul_inv, mul_one])

/-- Under the isomorphism with the product, an equation `ℓ` is `t (ℓ / ℓ₀)`, the formula
`ℓ_i = t (ℓ_i / ℓ_0)` of the blueprint.

Blueprint: `lem:decone`. -/
@[simp]
theorem coneEquiv_algebraMap_coord (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (ξ : Dual k W) :
    coneEquiv hℓ₀ (algebraMap _ _ (coord ξ.toAffineMap)) =
      LaurentPolynomial.T 1 * LaurentPolynomial.C (ratio ξ hℓ₀) :=
  (coneToLaurent_algebraMap hℓ₀ _).trans (coneCoord_coord_toAffineMap hℓ₀ ξ)

/-- Functions pulled back from the projective complement are the constants of the product. -/
@[simp]
theorem coneEquiv_toCone (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : P.ComplementRing) :
    coneEquiv hℓ₀ (toCone P x) = LaurentPolynomial.C x :=
  coneToLaurent_toCone hℓ₀ x

@[simp]
theorem coneEquiv_symm_C (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) (x : P.ComplementRing) :
    (coneEquiv hℓ₀).symm (LaurentPolynomial.C x) = toCone P x :=
  laurentPolynomialLift_C _ _ x

/-- The coordinate `t` of the product is the equation `ℓ₀`. -/
@[simp]
theorem coneEquiv_symm_T (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (coneEquiv hℓ₀).symm (LaurentPolynomial.T 1) = algebraMap _ _ (coord ℓ₀.toAffineMap) :=
  laurentPolynomialLift_T _ _

end Cone

/-- For finite-dimensional `W`, the coordinate ring of a nonempty projective complement is smooth,
since it is the ring of a decone complement. -/
instance [FiniteDimensional k W] [Nonempty P] : Algebra.Smooth k P.ComplementRing := by
  obtain ⟨ℓ₀, hℓ₀⟩ := P.exists_ker_mem
  exact .of_equiv (deconeEquiv hℓ₀).symm

end ComplementRing

end ProjectiveArrangement

/-! ### The objects of `SmoothAlg k` -/

namespace SmoothAlg

open ProjectiveArrangement ProjectiveArrangement.ComplementRing

section Projective

variable [FiniteDimensional k W] {P : ProjectiveArrangement k W} [Nonempty P]
variable {ℓ ℓ' ℓ₀ : Dual k W}

variable (P) in
/-- The coordinate ring `O(U_P)` of the complement of a nonempty projective arrangement, as an
object of `SmoothAlg k`.

Blueprint: `def:projective`, `lem:geometry-adapter`. -/
def projectiveComplement : SmoothAlg k := of k P.ComplementRing

instance : IsDomain (projectiveComplement P) := inferInstanceAs (IsDomain P.ComplementRing)

variable (P) in
/-- The pullback `O(U_P) ⟶ O(V_P)` along the projection from the complement of the cone to the
projective complement. -/
def projectiveToCone : projectiveComplement P ⟶ complement P.cone := ofHom (toCone P)

lemma projectiveToCone_apply (x : P.ComplementRing) :
    projectiveToCone P x = (toCone P x : P.cone.ComplementRing) := rfl

lemma projectiveToCone_injective : Function.Injective (projectiveToCone P) :=
  toCone_injective

/-- Maps out of `O(U_P)` agree if they agree on all ratios `ξ / ℓ`. -/
lemma projectiveComplement_hom_ext {B : SmoothAlg k} {f g : projectiveComplement P ⟶ B}
    (h : ∀ (ξ ℓ : Dual k W) (hℓ : LinearMap.ker ℓ ∈ P),
      f (ratio ξ hℓ : P.ComplementRing) = g (ratio ξ hℓ : P.ComplementRing)) : f = g :=
  ConcreteCategory.ext <| ComplementRing.algHom_ext h

/-- The ratio `ℓ / ℓ'` of two equations of hyperplanes of `P`, as a unit of `O(U_P)`. It involves no
hyperplane at infinity.

Blueprint: `thm:projective`. -/
def projectiveRatioUnit (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (projectiveComplement P)ˣ :=
  ratioUnit hℓ hℓ'

@[simp]
lemma projectiveRatioUnit_self (hℓ : LinearMap.ker ℓ ∈ P) : projectiveRatioUnit hℓ hℓ = 1 :=
  ratioUnit_self hℓ

@[simp]
lemma projectiveRatioUnit_inv (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (projectiveRatioUnit hℓ hℓ')⁻¹ = projectiveRatioUnit hℓ' hℓ :=
  rfl

lemma projectiveRatioUnit_mul {ℓ'' : Dual k W} (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) (hℓ'' : LinearMap.ker ℓ'' ∈ P) :
    projectiveRatioUnit hℓ hℓ' * projectiveRatioUnit hℓ' hℓ'' = projectiveRatioUnit hℓ hℓ'' :=
  ratioUnit_mul_ratioUnit hℓ hℓ' hℓ''

/-- Changing an equation in a ratio changes the ratio by a nonzero constant. So a logarithm of the
ratio does not depend on the equations.

Blueprint: `thm:projective`. -/
lemma exists_projectiveRatioUnit_eq_constUnit_mul {ℓ₁ : Dual k W} (hℓ₁ : LinearMap.ker ℓ₁ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P)
    (hker : LinearMap.ker ℓ₁ = LinearMap.ker ℓ) :
    ∃ c : kˣ, projectiveRatioUnit hℓ₁ hℓ' =
      constUnit (projectiveComplement P) c * projectiveRatioUnit hℓ hℓ' := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_ker_eq hker (ne_zero_of_ker_mem hℓ)
  exact ⟨c, Units.ext (coe_ratioUnit_smul hℓ₁ hℓ hℓ')⟩

/-- The pullback to `O(V_P)` of a ratio of equations is the quotient of their units. -/
lemma mapUnits_projectiveToCone_projectiveRatioUnit (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    mapUnits (projectiveToCone P) (projectiveRatioUnit hℓ hℓ') =
      complementUnit P.cone ℓ.toAffineMap (cone_covers hℓ) *
        (complementUnit P.cone ℓ'.toAffineMap (cone_covers hℓ'))⁻¹ :=
  Units.ext (toCone_ratio ℓ hℓ')

/-! #### The decone -/

/-- The projective complement is the decone complement, for an equation `ℓ₀` of any hyperplane of
`P`.

Blueprint: `lem:decone`. -/
def deconeIso (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    projectiveComplement P ≅ complement (P.decone ℓ₀) :=
  isoOfAlgEquiv (deconeEquiv hℓ₀)

/-- The decone isomorphism is the restriction of functions to the slice. -/
@[reassoc]
lemma projectiveToCone_comp_complementMap (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    projectiveToCone P ≫ complementMap (chart (slice ℓ₀)) P.cone (P.decone ℓ₀)
        (fun _ hK ↦ decone_covers_comap hℓ₀ hK) = (deconeIso hℓ₀).hom :=
  rfl

/-- The decone isomorphism sends the ratio `ℓ / ℓ₀` to the unit given by the restriction of `ℓ` to
the slice.

Blueprint: `lem:decone`. -/
@[simp]
lemma mapUnits_deconeIso_hom_projectiveRatioUnit_self (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) :
    mapUnits (deconeIso hℓ₀).hom (projectiveRatioUnit hℓ hℓ₀) =
      complementUnit (P.decone ℓ₀) (ℓ.toAffineMap.comp (chart (slice ℓ₀)))
        (decone_covers hℓ₀ hℓ) :=
  Units.ext (deconeEquiv_ratio_self hℓ₀ ℓ)

/-- The decone isomorphism sends the ratio `ℓ / ℓ'` to the quotient of the units given by the
restrictions of `ℓ` and `ℓ'` to the slice. So it is compatible with all ratios, for any choice of
hyperplane at infinity.

Blueprint: `lem:decone`. -/
lemma mapUnits_deconeIso_hom_projectiveRatioUnit (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    mapUnits (deconeIso hℓ₀).hom (projectiveRatioUnit hℓ hℓ') =
      complementUnit (P.decone ℓ₀) (ℓ.toAffineMap.comp (chart (slice ℓ₀)))
          (decone_covers hℓ₀ hℓ) *
        (complementUnit (P.decone ℓ₀) (ℓ'.toAffineMap.comp (chart (slice ℓ₀)))
          (decone_covers hℓ₀ hℓ'))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (deconeEquiv_ratio_mul hℓ₀ ℓ hℓ')

/-- The projective complement of one hyperplane is an affine space.

Blueprint: the regression list, "one projective hyperplane". -/
def projectiveComplementIsoAffineSpace (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hP : ∀ H ∈ P, H = LinearMap.ker ℓ₀) :
    projectiveComplement P ≅ affineSpace k (slice ℓ₀).direction :=
  deconeIso hℓ₀ ≪≫ eqToIso (congrArg complement (decone_eq_empty hℓ₀ hP)) ≪≫
    complementEmptyIso k _

/-! #### The cone -/

/-- The isomorphism `V_P ≃ U_P × 𝔾ₘ`, for an equation `ℓ₀` of any hyperplane of `P`.

Blueprint: `lem:decone`. -/
def coneIso (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    complement P.cone ≅ laurent (projectiveComplement P) :=
  isoOfAlgEquiv (coneEquiv hℓ₀)

/-- Under `V_P ≃ U_P × 𝔾ₘ`, the projection to `U_P` is the projection of the product. -/
@[reassoc (attr := simp)]
lemma projectiveToCone_comp_coneIso_hom (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    projectiveToCone P ≫ (coneIso hℓ₀).hom = laurentC (projectiveComplement P) :=
  ConcreteCategory.ext <| AlgHom.ext fun x ↦ coneEquiv_toCone hℓ₀ x

/-- Under `V_P ≃ U_P × 𝔾ₘ`, the projection of the product to `U_P` is the projection to `U_P`. -/
@[reassoc (attr := simp)]
lemma laurentC_comp_coneIso_inv (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    laurentC (projectiveComplement P) ≫ (coneIso hℓ₀).inv = projectiveToCone P := by
  rw [Iso.comp_inv_eq, projectiveToCone_comp_coneIso_hom]

/-- Under `V_P ≃ U_P × 𝔾ₘ`, the coordinate `t` is the equation `ℓ₀`. -/
@[simp]
lemma mapUnits_coneIso_inv_laurentT (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    mapUnits (coneIso hℓ₀).inv (laurentT (projectiveComplement P)) =
      complementUnit P.cone ℓ₀.toAffineMap (cone_covers hℓ₀) :=
  Units.ext (coneEquiv_symm_T hℓ₀)

/-- Under `V_P ≃ U_P × 𝔾ₘ`, an equation `ℓ` is `t (ℓ / ℓ₀)`.

Blueprint: `lem:decone`. -/
lemma mapUnits_coneIso_hom_complementUnit (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) :
    mapUnits (coneIso hℓ₀).hom (complementUnit P.cone ℓ.toAffineMap (cone_covers hℓ)) =
      laurentT (projectiveComplement P) *
        mapUnits (laurentC (projectiveComplement P)) (projectiveRatioUnit hℓ hℓ₀) :=
  Units.ext (coneEquiv_algebraMap_coord hℓ₀ ℓ)

/-- The pullback along the projection `V_P → U_P` has a retraction, given by the section `t = 1`
of the product. It is the pullback along `U_P → V_P`, `v ↦ v / ℓ₀(v)`, which lands in the slice. -/
@[reassoc]
lemma projectiveToCone_comp_coneIso_hom_comp_laurentSection (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    projectiveToCone P ≫ (coneIso hℓ₀).hom ≫ laurentSection (projectiveComplement P) =
      𝟙 (projectiveComplement P) := by
  simp

end Projective

end SmoothAlg

end OrlikSolomon
