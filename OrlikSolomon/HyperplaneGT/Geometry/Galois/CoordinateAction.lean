/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates

/-!
# Field automorphisms on coordinate affine subspaces

A field automorphism acts on points coordinatewise. Its image on affine subspaces is an order
isomorphism, including the empty subspace. The corresponding direction map is semilinear and
preserves dimension. These are the linear-algebra ingredients of the coefficient Galois action.

## Main results

* `fieldAffineSubspaceOrderIso` preserves all intersections and emptiness.
* `codim_fieldAffineSubspace` preserves codimensions, including the empty-subspace convention.
* `isEquation_fieldAffineForm` identifies transformed equations with transformed subspaces.
* `coefficientPoint_fieldHyperplaneEquiv` gives the projective coefficient comparison.

Blueprint: `lem:g04`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

open scoped Pointwise

universe u v

variable {k : Type u} [Field k] {ι : Type v}

local instance (σ : k ≃+* k) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

/-- Coordinatewise application of a field automorphism as an additive equivalence. This point
map requires no auxiliary inverse-pair instances in downstream consumers. -/
def fieldCoordinateAddEquiv (σ : k ≃+* k) (ι : Type v) : (ι → k) ≃+ (ι → k) :=
  AddEquiv.piCongrRight fun _ ↦ σ.toAddEquiv

@[simp]
theorem fieldCoordinateAddEquiv_apply (σ : k ≃+* k) (x : ι → k) (i : ι) :
    fieldCoordinateAddEquiv σ ι x i = σ (x i) := rfl

@[simp]
theorem fieldCoordinateAddEquiv_symm_apply (σ : k ≃+* k) (x : ι → k) (i : ι) :
    (fieldCoordinateAddEquiv σ ι).symm x i = σ.symm (x i) := rfl

/-- Coordinatewise application of a field automorphism is a semilinear equivalence. -/
def fieldCoordinateEquiv (σ : k ≃+* k) (ι : Type v) :
    (ι → k) ≃ₛₗ[σ.toRingHom] (ι → k) :=
  { fieldCoordinateAddEquiv σ ι with
    map_smul' c x := by ext i; simp }

@[simp]
theorem fieldCoordinateEquiv_apply (σ : k ≃+* k) (x : ι → k) (i : ι) :
    fieldCoordinateEquiv σ ι x i = σ (x i) := rfl

@[simp]
theorem fieldCoordinateEquiv_symm_apply (σ : k ≃+* k) (x : ι → k) (i : ι) :
    (fieldCoordinateEquiv σ ι).symm x i = σ.symm (x i) := rfl

/-- The affine subspace obtained by applying a field automorphism to all coordinates. -/
def fieldAffineSubspace (σ : k ≃+* k) (X : AffineSubspace k (ι → k)) :
    AffineSubspace k (ι → k) where
  carrier := fieldCoordinateAddEquiv σ ι '' (X : Set (ι → k))
  smul_vsub_vadd_mem' c := by
    rintro _ _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    refine ⟨σ.symm c • (x -ᵥ y) +ᵥ z, X.smul_vsub_vadd_mem (σ.symm c) hx hy hz, ?_⟩
    ext i
    change σ (σ.symm c * (x i - y i) + z i) = c * (σ (x i) - σ (y i)) + σ (z i)
    simp

@[simp]
theorem mem_fieldAffineSubspace (σ : k ≃+* k) (X : AffineSubspace k (ι → k)) (x : ι → k) :
    x ∈ fieldAffineSubspace σ X ↔ (fieldCoordinateAddEquiv σ ι).symm x ∈ X := by
  change x ∈ fieldCoordinateAddEquiv σ ι '' (X : Set (ι → k)) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((fieldCoordinateAddEquiv σ ι).symm_apply_apply y).symm ▸ hy
  · intro hx
    exact ⟨(fieldCoordinateAddEquiv σ ι).symm x, hx,
      (fieldCoordinateAddEquiv σ ι).apply_symm_apply x⟩

@[simp]
theorem fieldAffineSubspace_symm (σ : k ≃+* k) (X : AffineSubspace k (ι → k)) :
    fieldAffineSubspace σ.symm (fieldAffineSubspace σ X) = X := by
  ext x
  simp only [mem_fieldAffineSubspace]
  have hx : (fieldCoordinateAddEquiv σ ι).symm
      ((fieldCoordinateAddEquiv σ.symm ι).symm x) = x := by
    ext i
    exact σ.symm_apply_apply (x i)
  rw [hx]

/-- The action on all affine subspaces is an order isomorphism, so preserves intersections
and the empty subspace. -/
def fieldAffineSubspaceOrderIso (σ : k ≃+* k) :
    AffineSubspace k (ι → k) ≃o AffineSubspace k (ι → k) where
  toFun := fieldAffineSubspace σ
  invFun := fieldAffineSubspace σ.symm
  left_inv := fieldAffineSubspace_symm σ
  right_inv X := by simpa using fieldAffineSubspace_symm σ.symm X
  map_rel_iff' := by
    intro X Y
    constructor
    · intro h x hx
      have himage : fieldCoordinateAddEquiv σ ι x ∈ fieldAffineSubspace σ X :=
        ⟨x, hx, rfl⟩
      have hy := (mem_fieldAffineSubspace σ Y _).mp (h himage)
      exact (fieldCoordinateAddEquiv σ ι).symm_apply_apply x ▸ hy
    · intro h x hx
      exact (mem_fieldAffineSubspace σ Y x).mpr (h ((mem_fieldAffineSubspace σ X x).mp hx))

@[simp]
theorem fieldAffineSubspace_inf (σ : k ≃+* k) (X Y : AffineSubspace k (ι → k)) :
    fieldAffineSubspace σ (X ⊓ Y) = fieldAffineSubspace σ X ⊓ fieldAffineSubspace σ Y :=
  (fieldAffineSubspaceOrderIso σ).map_inf X Y

/-- The coordinate field transformation preserves arbitrary intersections. -/
theorem fieldAffineSubspace_iInf {η : Sort*} (σ : k ≃+* k)
    (X : η → AffineSubspace k (ι → k)) :
    fieldAffineSubspace σ (⨅ i, X i) = ⨅ i, fieldAffineSubspace σ (X i) :=
  (fieldAffineSubspaceOrderIso σ).map_iInf X

@[simp]
theorem fieldAffineSubspace_bot (σ : k ≃+* k) :
    fieldAffineSubspace σ (⊥ : AffineSubspace k (ι → k)) = ⊥ :=
  (fieldAffineSubspaceOrderIso σ).map_bot

@[simp]
theorem fieldAffineSubspace_eq_bot_iff (σ : k ≃+* k) (X : AffineSubspace k (ι → k)) :
    fieldAffineSubspace σ X = ⊥ ↔ X = ⊥ := by
  constructor
  · intro h
    apply (fieldAffineSubspaceOrderIso σ).injective
    exact h.trans (fieldAffineSubspace_bot σ).symm
  · rintro rfl
    exact fieldAffineSubspace_bot σ

/-- Applying a field automorphism to an affine subspace carries its direction to the
semilinear image of the original direction. This includes the empty subspace. -/
theorem direction_fieldAffineSubspace (σ : k ≃+* k) (X : AffineSubspace k (ι → k)) :
    (fieldAffineSubspace σ X).direction =
      X.direction.map (fieldCoordinateEquiv σ ι).toLinearMap := by
  rw [AffineSubspace.direction_eq_vectorSpan, AffineSubspace.direction_eq_vectorSpan,
    vectorSpan_def, vectorSpan_def, Submodule.map_span]
  change Submodule.span k ((fieldCoordinateEquiv σ ι '' (X : Set (ι → k))) -
      (fieldCoordinateEquiv σ ι '' (X : Set (ι → k)))) =
    Submodule.span k (fieldCoordinateEquiv σ ι '' ((X : Set (ι → k)) - (X : Set (ι → k))))
  rw [Set.image_sub]

/-- A coordinatewise field automorphism preserves the dimension of every affine direction.
The argument reuses Mathlib's dimension invariance under compatible additive equivalences. -/
theorem finrank_direction_fieldAffineSubspace (σ : k ≃+* k)
    (X : AffineSubspace k (ι → k)) :
    Module.finrank k (fieldAffineSubspace σ X).direction = Module.finrank k X.direction := by
  rw [direction_fieldAffineSubspace]
  let e := (fieldCoordinateEquiv σ ι).submoduleMap X.direction
  have h := rank_eq_of_equiv_equiv σ e.toAddEquiv σ.bijective
    (fun r m ↦ e.map_smulₛₗ r m)
  exact congrArg Cardinal.toNat h.symm

@[simp]
theorem fieldAffineSubspace_refl (X : AffineSubspace k (ι → k)) :
    fieldAffineSubspace (RingEquiv.refl k) X = X := by
  ext x
  rw [mem_fieldAffineSubspace]
  rfl

/-- Successive coordinate field transformations compose in the same order as the point maps.
-/
theorem fieldAffineSubspace_trans (σ τ : k ≃+* k) (X : AffineSubspace k (ι → k)) :
    fieldAffineSubspace (σ.trans τ) X = fieldAffineSubspace τ (fieldAffineSubspace σ X) := by
  ext x
  simp only [mem_fieldAffineSubspace]
  rfl

section FiniteCoordinates

variable {n : ℕ}

/-- Coordinatewise field automorphisms preserve codimension, including the conventional value
on the empty affine subspace. -/
theorem codim_fieldAffineSubspace (σ : k ≃+* k) (X : AffineSubspace k (Fin n → k)) :
    codim (fieldAffineSubspace σ X) = codim X := by
  have hX := codim_add_finrank_direction X
  have hσX := codim_add_finrank_direction (fieldAffineSubspace σ X)
  rw [finrank_direction_fieldAffineSubspace] at hσX
  omega

@[simp]
theorem isHyperplane_fieldAffineSubspace_iff (σ : k ≃+* k)
    (X : AffineSubspace k (Fin n → k)) :
    IsHyperplane (fieldAffineSubspace σ X) ↔ IsHyperplane X := by
  rw [isHyperplane_iff_codim_eq_one, isHyperplane_iff_codim_eq_one,
    ne_eq, fieldAffineSubspace_eq_bot_iff, codim_fieldAffineSubspace]

/-- A field automorphism acts bijectively on affine hyperplanes by transforming their points.
-/
@[implicit_reducible]
def fieldHyperplaneEquiv (σ : k ≃+* k) : Hyperplane k n ≃ Hyperplane k n where
  toFun H := ⟨fieldAffineSubspace σ H.val,
    (isHyperplane_fieldAffineSubspace_iff σ H.val).mpr H.property⟩
  invFun H := ⟨fieldAffineSubspace σ.symm H.val,
    (isHyperplane_fieldAffineSubspace_iff σ.symm H.val).mpr H.property⟩
  left_inv H := Subtype.ext (fieldAffineSubspace_symm σ H.val)
  right_inv H := Subtype.ext (by simpa using fieldAffineSubspace_symm σ.symm H.val)

@[simp]
theorem fieldHyperplaneEquiv_val (σ : k ≃+* k) (H : Hyperplane k n) :
    (fieldHyperplaneEquiv σ H).val = fieldAffineSubspace σ H.val := rfl

/-- Applying a field automorphism to the coefficients of an affine form. -/
noncomputable def fieldAffineForm (σ : k ≃+* k) (f : (Fin n → k) →ᵃ[k] k) :
    (Fin n → k) →ᵃ[k] k :=
  coefficientForm (fun i ↦ σ (affineCoefficients f i))

@[simp]
theorem affineCoefficients_fieldAffineForm (σ : k ≃+* k) (f : (Fin n → k) →ᵃ[k] k) :
    affineCoefficients (fieldAffineForm σ f) = fun i ↦ σ (affineCoefficients f i) :=
  affineCoefficients_coefficientForm _

/-- The transformed equation evaluates to the field transform of the original value on
transformed points. -/
theorem fieldAffineForm_apply (σ : k ≃+* k) (f : (Fin n → k) →ᵃ[k] k) (x : Fin n → k) :
    fieldAffineForm σ f (fieldCoordinateAddEquiv σ (Fin n) x) = σ (f x) := by
  have hfx : f x = affineCoefficients f 0 + ∑ i : Fin n, affineCoefficients f i.succ * x i := by
    rw [← coefficientForm_apply, coefficientForm_affineCoefficients]
  simp only [fieldAffineForm, coefficientForm_apply]
  change σ (affineCoefficients f 0) +
    ∑ i : Fin n, σ (affineCoefficients f i.succ) * σ (x i) = σ (f x)
  rw [hfx, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (σ.map_mul _ _).symm

/-- Transforming coefficients preserves the nonzero-normal condition. -/
theorem fieldAffineForm_linear_ne_zero_iff (σ : k ≃+* k) (f : (Fin n → k) →ᵃ[k] k) :
    (fieldAffineForm σ f).linear ≠ 0 ↔ f.linear ≠ 0 := by
  simp only [ne_eq, linear_eq_zero_iff_coefficients, affineCoefficients_fieldAffineForm,
    map_eq_zero_iff σ σ.injective]

/-- Every equation transforms to an equation of the transformed hyperplane. -/
theorem isEquation_fieldAffineForm (σ : k ≃+* k) {H : AffineSubspace k (Fin n → k)}
    {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    IsEquation (fieldAffineForm σ f) (fieldAffineSubspace σ H) := by
  refine ⟨(fieldAffineForm_linear_ne_zero_iff σ f).mpr hf.linear_ne_zero, ?_⟩
  ext x
  rw [mem_zeroLocus, mem_fieldAffineSubspace]
  have hx := fieldAffineForm_apply σ f ((fieldCoordinateAddEquiv σ (Fin n)).symm x)
  rw [(fieldCoordinateAddEquiv σ (Fin n)).apply_symm_apply] at hx
  rw [hx, map_eq_zero_iff σ σ.injective, hf.apply_eq_zero_iff]

/-- The map on projective coefficient points induced by the semilinear coordinate map. -/
def fieldCoefficientPoint (σ : k ≃+* k)
    (p : Projectivization k (Fin (n + 1) → k)) :
    Projectivization k (Fin (n + 1) → k) :=
  Projectivization.map (fieldCoordinateEquiv σ (Fin (n + 1))).toLinearMap
    (fieldCoordinateEquiv σ (Fin (n + 1))).injective p

/-- The actions on hyperplanes and on projective equation coefficients agree, independently
of the equation used for the hyperplane. -/
theorem coefficientPoint_fieldHyperplaneEquiv (σ : k ≃+* k) (H : Hyperplane k n) :
    coefficientPoint (fieldHyperplaneEquiv σ H) = fieldCoefficientPoint σ (coefficientPoint H) := by
  have hf := isEquation_equation H.property
  rw [coefficientPoint_eq_mk H hf]
  have hp := coefficientPoint_eq_mk (fieldHyperplaneEquiv σ H) (isEquation_fieldAffineForm σ hf)
  apply hp.trans
  unfold fieldCoefficientPoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  simp only [one_smul, affineCoefficients_fieldAffineForm]
  rfl

/-- Coordinate field transformations preserve strict parallelism in both directions. -/
theorem parallel_fieldHyperplaneEquiv_iff (σ : k ≃+* k) (H K : Hyperplane k n) :
    Parallel (fieldHyperplaneEquiv σ H) (fieldHyperplaneEquiv σ K) ↔ Parallel H K := by
  have hne : fieldHyperplaneEquiv σ H ≠ fieldHyperplaneEquiv σ K ↔ H ≠ K :=
    not_congr (fieldHyperplaneEquiv σ).injective.eq_iff
  simp only [Parallel, hne, fieldHyperplaneEquiv_val, ← fieldAffineSubspace_inf,
    fieldAffineSubspace_eq_bot_iff]

/-- Coordinate field transformations preserve guarded dependent triples in both directions.
-/
theorem dependentTriple_fieldHyperplaneEquiv_iff (σ : k ≃+* k) (H K L : Hyperplane k n) :
    DependentTriple (fieldHyperplaneEquiv σ H) (fieldHyperplaneEquiv σ K)
      (fieldHyperplaneEquiv σ L) ↔ DependentTriple H K L := by
  have hne (X Y : Hyperplane k n) :
      fieldHyperplaneEquiv σ X ≠ fieldHyperplaneEquiv σ Y ↔ X ≠ Y :=
    not_congr (fieldHyperplaneEquiv σ).injective.eq_iff
  simp only [DependentTriple, hne, fieldHyperplaneEquiv_val, ← fieldAffineSubspace_inf,
    ne_eq, fieldAffineSubspace_eq_bot_iff, codim_fieldAffineSubspace]

/-- Coordinate field transformations preserve verticality over any fixed coordinate set.
-/
theorem isVertical_fieldHyperplaneEquiv_iff (σ : k ≃+* k)
    (J : Finset (Fin n)) (H : Hyperplane k n) :
    IsVertical J (fieldHyperplaneEquiv σ H) ↔ IsVertical J H := by
  have hf := isEquation_equation H.property
  rw [isVertical_iff_of_isEquation J _ (isEquation_fieldAffineForm σ hf),
    isVertical_iff_of_isEquation J H hf, affineCoefficients_fieldAffineForm]
  simp only [map_eq_zero_iff σ σ.injective]

end FiniteCoordinates

end OrlikSolomon.HyperplaneGT
