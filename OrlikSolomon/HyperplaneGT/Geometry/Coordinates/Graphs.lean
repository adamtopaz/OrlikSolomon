/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Equations
public import Mathlib.Logic.Equiv.Prod

/-!
# Vertical hyperplanes and coordinate graphs

Coordinate subsets are finite sets and their coordinate spaces use the member subtype.
`IsVertical` is independent of the equation used to test its normal coefficients.
Splitting off one coordinate identifies a nonvertical hyperplane with an affine graph.
The projection of the intersection of two graphs is the zero locus of their difference.

Blueprint: G03 (`lem:g03`), independently of the parallel-pair incidence API.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u

section Coordinates

variable {k : Type u} [Semiring k] {n : ℕ}

/-- The coordinates remaining after deleting `i`. -/
def omittedCoordinates (i : Fin n) : Finset (Fin n) := Finset.univ.erase i

@[simp]
theorem mem_omittedCoordinates (i j : Fin n) : j ∈ omittedCoordinates i ↔ j ≠ i := by
  simp [omittedCoordinates]

/-- Restriction to a finite set of coordinate indices. -/
def coordinateProjection (J : Finset (Fin n)) : (Fin n → k) →ₗ[k] (J → k) :=
  LinearMap.pi fun j ↦ LinearMap.proj j.val

@[simp]
theorem coordinateProjection_apply (J : Finset (Fin n)) (x : Fin n → k) (j : J) :
    coordinateProjection J x j = x j.val := rfl

/-- Splitting off a coordinate, using Mathlib's coordinate splitting and reindexing its
complement by the member subtype of a finite set. -/
def coordinateSplit (i : Fin n) : (Fin n → k) ≃ₗ[k] k × (omittedCoordinates i → k) :=
  let e : {j : Fin n // j ≠ i} ≃ omittedCoordinates i :=
    Equiv.subtypeEquivRight fun j ↦ (mem_omittedCoordinates i j).symm
  { toEquiv := (Equiv.funSplitAt i k).trans
      (Equiv.prodCongr (Equiv.refl k) (Equiv.arrowCongr e (Equiv.refl k)))
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem coordinateSplit_apply (i : Fin n) (x : Fin n → k) :
    coordinateSplit i x = (x i, coordinateProjection (omittedCoordinates i) x) := rfl

@[simp]
theorem coordinateSplit_symm_apply_self (i : Fin n) (t : k)
    (z : omittedCoordinates i → k) : (coordinateSplit i).symm (t, z) i = t := by
  have h := congrArg Prod.fst ((coordinateSplit i).apply_symm_apply (t, z))
  simpa only [coordinateSplit_apply] using h

@[simp]
theorem coordinateProjection_coordinateSplit_symm (i : Fin n) (t : k)
    (z : omittedCoordinates i → k) :
    coordinateProjection (omittedCoordinates i) ((coordinateSplit i).symm (t, z)) = z := by
  have h := congrArg Prod.snd ((coordinateSplit i).apply_symm_apply (t, z))
  simpa only [coordinateSplit_apply] using h

/-- Insertion of zero in the omitted coordinate. -/
def coordinateSection (i : Fin n) : (omittedCoordinates i → k) →ₗ[k] (Fin n → k) :=
  (coordinateSplit i).symm.toLinearMap.comp (LinearMap.inr k k (omittedCoordinates i → k))

@[simp]
theorem coordinateSection_apply (i : Fin n) (z : omittedCoordinates i → k) :
    coordinateSection i z = (coordinateSplit i).symm (0, z) := rfl

end Coordinates

variable {k : Type u} [Field k] {n : ℕ}

/-- A hyperplane is vertical over `J` when all coefficients outside `J` vanish. -/
def IsVertical (J : Finset (Fin n)) (H : Hyperplane k n) : Prop :=
  ∀ j ∉ J, affineCoefficients (equation H.val) j.succ = 0

/-- Verticality can be tested using any equation of the hyperplane.

Blueprint: G03 (`lem:g03`), equation independence. -/
theorem isVertical_iff_of_isEquation (J : Finset (Fin n)) (H : Hyperplane k n)
    {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H.val) :
    IsVertical J H ↔ ∀ j ∉ J, affineCoefficients f j.succ = 0 := by
  obtain ⟨c, hc, -⟩ := (isEquation_equation H.property).existsUnique_smul hf
  simp only [IsVertical, hc, map_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
    c.ne_zero, false_or]

/-- Omitting just `i`, nonverticality means that the `i`th normal coefficient is nonzero. -/
theorem not_isVertical_iff_of_isEquation (i : Fin n) (H : Hyperplane k n)
    {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H.val) :
    ¬ IsVertical (omittedCoordinates i) H ↔ affineCoefficients f i.succ ≠ 0 := by
  rw [isVertical_iff_of_isEquation _ H hf]
  simp

/-- The normalized graph equation `x_i - h(z)`. -/
def graphEquation (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    (Fin n → k) →ᵃ[k] k :=
  (LinearMap.proj i).toAffineMap - h.comp (coordinateProjection (omittedCoordinates i)).toAffineMap

@[simp]
theorem graphEquation_apply (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    (x : Fin n → k) :
    graphEquation i h x = x i - h (coordinateProjection (omittedCoordinates i) x) := rfl

private theorem coordinateProjection_single (i : Fin n) (r : k) :
    coordinateProjection (omittedCoordinates i) (Pi.single i r) = 0 := by
  ext j
  simp [(mem_omittedCoordinates i j.val).mp j.property]

/-- The coefficient of the distinguished variable in a graph equation is one. -/
theorem graphEquation_normal_coefficient (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    affineCoefficients (graphEquation i h) i.succ = 1 := by
  simp [affineCoefficients_succ, graphEquation, coordinateProjection_single]

/-- The linear part of a graph equation takes value one on its distinguished basis vector. -/
@[simp]
theorem graphEquation_linear_single_self (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    (graphEquation i h).linear (Pi.single i 1) = 1 := by
  simpa only [affineCoefficients_succ] using graphEquation_normal_coefficient i h

/-- The affine subspace of the graph of `h`, expressed by its normalized equation. -/
def graphSubspace (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    AffineSubspace k (Fin n → k) := zeroLocus (graphEquation i h)

@[simp]
theorem mem_graphSubspace (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    (x : Fin n → k) :
    x ∈ graphSubspace i h ↔ x i = h (coordinateProjection (omittedCoordinates i) x) := by
  simp [graphSubspace, sub_eq_zero]

/-- The graph equation is an equation for a hyperplane. -/
theorem isEquation_graphEquation (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    IsEquation (graphEquation i h) (graphSubspace i h) := by
  apply isEquation_zeroLocus
  intro hz
  have hc := graphEquation_normal_coefficient i h
  simp only [affineCoefficients_succ, hz, LinearMap.zero_apply] at hc
  exact zero_ne_one hc

/-- The hyperplane represented by an affine graph. -/
def graphHyperplane (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) : Hyperplane k n :=
  ⟨graphSubspace i h, (isEquation_graphEquation i h).isHyperplane⟩

@[simp]
theorem coe_graphHyperplane (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    (graphHyperplane i h).val = graphSubspace i h := rfl

/-- A graph is nonvertical over the complementary coordinates. -/
theorem not_isVertical_graphHyperplane (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    ¬ IsVertical (omittedCoordinates i) (graphHyperplane i h) := by
  rw [not_isVertical_iff_of_isEquation i _ (isEquation_graphEquation i h)]
  rw [graphEquation_normal_coefficient]
  exact one_ne_zero

/-- The affine graph parametrization, inserting the value of `h` as the omitted coordinate. -/
def graphParam (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    (omittedCoordinates i → k) →ᵃ[k] (Fin n → k) :=
  (coordinateSplit i).symm.toAffineMap.comp (h.prod (AffineMap.id k _))

@[simp]
theorem graphParam_apply (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    (z : omittedCoordinates i → k) :
    graphParam i h z = (coordinateSplit i).symm (h z, z) := rfl

/-- Projection is inverse to graph parametrization. -/
theorem coordinateProjection_graphParam (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    (z : omittedCoordinates i → k) :
    coordinateProjection (omittedCoordinates i) (graphParam i h z) = z := by
  simp

/-- The graph parametrization has image in its graph. -/
theorem graphParam_mem (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    (z : omittedCoordinates i → k) : graphParam i h z ∈ graphSubspace i h := by
  simp

/-- Parametrization is inverse to projection on a graph. -/
theorem graphParam_projection (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k)
    {x : Fin n → k} (hx : x ∈ graphSubspace i h) :
    graphParam i h (coordinateProjection (omittedCoordinates i) x) = x := by
  apply (coordinateSplit i).injective
  simpa only [graphParam_apply, LinearEquiv.apply_symm_apply, coordinateSplit_apply,
    Prod.mk.injEq, and_true] using (mem_graphSubspace i h x).mp hx |>.symm

/-- Distinct graph functions define distinct affine hyperplanes. -/
theorem graphSubspace_injective (i : Fin n) :
    Function.Injective (graphSubspace (k := k) i) := by
  intro h₀ h₁ hh
  ext z
  have hx := hh ▸ graphParam_mem i h₀ z
  simpa using (mem_graphSubspace i h₁ _).mp hx

/-- Every graph has its canonical point above the zero vector. -/
instance (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    Nonempty (graphSubspace i h) := ⟨⟨graphParam i h 0, graphParam_mem i h 0⟩⟩

/-- The coordinate projection restricted to an affine graph. -/
def graphProjection (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    graphSubspace i h →ᵃ[k] (omittedCoordinates i → k) :=
  (coordinateProjection (omittedCoordinates i)).toAffineMap.comp (graphSubspace i h).subtype

private theorem graphProjection_bijective (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) : Function.Bijective (graphProjection i h) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    rw [← graphParam_projection i h x.property, ← graphParam_projection i h y.property]
    exact congrArg (graphParam i h) hxy
  · intro z
    exact ⟨⟨graphParam i h z, graphParam_mem i h z⟩, coordinateProjection_graphParam i h z⟩

/-- Projection from the graph of an affine function is an affine isomorphism, whose inverse
inserts the value of that function in the omitted coordinate.

Blueprint: G03 (`lem:g03`). -/
def graphProjectionEquiv (i : Fin n) (h : (omittedCoordinates i → k) →ᵃ[k] k) :
    graphSubspace i h ≃ᵃ[k] (omittedCoordinates i → k) :=
  AffineEquiv.ofBijective (φ := graphProjection i h) (by exact graphProjection_bijective i h)

@[simp]
theorem graphProjectionEquiv_apply (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) (x : graphSubspace i h) :
    graphProjectionEquiv i h x = coordinateProjection (omittedCoordinates i) x.val := rfl

/-- The inverse of graph projection is the explicit insertion map. -/
@[simp]
theorem coe_graphProjectionEquiv_symm (i : Fin n)
    (h : (omittedCoordinates i → k) →ᵃ[k] k) (z : omittedCoordinates i → k) :
    ((graphProjectionEquiv i h).symm z).val = graphParam i h z := by
  have hx := graphParam_projection i h ((graphProjectionEquiv i h).symm z).property
  have hz := (graphProjectionEquiv i h).apply_symm_apply z
  change coordinateProjection (omittedCoordinates i) ((graphProjectionEquiv i h).symm z).val = z
    at hz
  simpa only [hz] using hx.symm

/-- A coordinate vector is its distinguished component plus its zero-coordinate section. -/
theorem coordinate_decompose (i : Fin n) (x : Fin n → k) :
    x = (x i) • Pi.single i 1 +
      coordinateSection i (coordinateProjection (omittedCoordinates i) x) := by
  apply (coordinateSplit i).injective
  simp [coordinateSplit_apply, coordinateProjection_single]

/-- Evaluation separates the distinguished coefficient of an affine form from its restriction
to the remaining coordinates. -/
theorem affineForm_decompose (i : Fin n) (f : (Fin n → k) →ᵃ[k] k) (x : Fin n → k) :
    f x = affineCoefficients f i.succ * x i +
      f (coordinateSection i (coordinateProjection (omittedCoordinates i) x)) := by
  calc
    f x = f ((x i) • Pi.single i 1 +
        coordinateSection i (coordinateProjection (omittedCoordinates i) x)) :=
      congrArg f (coordinate_decompose i x)
    _ = _ := by rw [← vadd_eq_add, AffineMap.map_vadd]; simp [mul_comm]

/-- Solving an affine equation for coordinate `i`, by division by its normal coefficient. -/
def graphFunctionOfEquation (i : Fin n) (f : (Fin n → k) →ᵃ[k] k) :
    (omittedCoordinates i → k) →ᵃ[k] k :=
  (-(affineCoefficients f i.succ)⁻¹) • f.comp (coordinateSection i).toAffineMap

/-- Dividing an equation by its nonzero distinguished coefficient gives the normalized graph
equation. No division by any integer is involved. -/
theorem graphEquation_graphFunctionOfEquation (i : Fin n)
    (f : (Fin n → k) →ᵃ[k] k) (hc : affineCoefficients f i.succ ≠ 0) :
    graphEquation i (graphFunctionOfEquation i f) = (affineCoefficients f i.succ)⁻¹ • f := by
  ext x
  change x i - (-(affineCoefficients f i.succ)⁻¹) *
      f (coordinateSection i (coordinateProjection (omittedCoordinates i) x)) =
    (affineCoefficients f i.succ)⁻¹ * f x
  rw [affineForm_decompose i f x]
  field_simp
  ring

/-- Every hyperplane nonvertical over the complementary coordinates has a unique affine graph
function.

Blueprint: G03 (`lem:g03`), normalized graph form and uniqueness. -/
theorem existsUnique_graph_of_not_isVertical (i : Fin n) (H : Hyperplane k n)
    (hH : ¬ IsVertical (omittedCoordinates i) H) :
    ∃! h : (omittedCoordinates i → k) →ᵃ[k] k, graphSubspace i h = H.val := by
  have hf := isEquation_equation H.property
  have hc := (not_isVertical_iff_of_isEquation i H hf).mp hH
  have hh : graphSubspace i (graphFunctionOfEquation i (equation H.val)) = H.val := by
    rw [graphSubspace, graphEquation_graphFunctionOfEquation i _ hc,
      zeroLocus_smul (inv_ne_zero hc)]
    exact hf.zeroLocus_eq
  exact ⟨_, hh, fun h hh' ↦ graphSubspace_injective i (hh'.trans hh.symm)⟩

/-- A finite coordinate set omitting exactly `i` is the canonical complement of `i`. -/
theorem eq_omittedCoordinates (J : Finset (Fin n)) (i : Fin n)
    (hJ : ∀ j, j ∈ J ↔ j ≠ i) : J = omittedCoordinates i := by
  ext j
  exact (hJ j).trans (mem_omittedCoordinates i j).symm

/-- The graph form applies to any coordinate set omitting exactly one index; identifying that
set with its canonical complement uses no ordering of its members. -/
theorem existsUnique_graph_of_omits_coordinate (J : Finset (Fin n)) (i : Fin n)
    (hJ : ∀ j, j ∈ J ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬ IsVertical J H) :
    ∃! h : (omittedCoordinates i → k) →ᵃ[k] k, graphSubspace i h = H.val := by
  rw [eq_omittedCoordinates J i hJ] at hH
  exact existsUnique_graph_of_not_isVertical i H hH

/-- The exact projected intersection of two graphs is the zero locus of their difference.

Blueprint: G03 (`lem:g03`), common traces. -/
theorem map_graphSubspace_inf (i : Fin n)
    (h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k) :
    (graphSubspace i h₀ ⊓ graphSubspace i h₁).map
      (coordinateProjection (omittedCoordinates i)).toAffineMap = zeroLocus (h₁ - h₀) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h₀x := (mem_graphSubspace i h₀ x).mp hx.1
    have h₁x := (mem_graphSubspace i h₁ x).mp hx.2
    simpa [sub_eq_zero] using h₁x.symm.trans h₀x
  · intro hz
    have hz' : h₁ z = h₀ z := by simpa [sub_eq_zero] using hz
    refine ⟨graphParam i h₀ z, ⟨graphParam_mem i h₀ z, ?_⟩, by simp⟩
    simpa using hz'.symm

/-- A nonzero constant difference forces two graphs to be disjoint. -/
theorem graphSubspace_inf_eq_bot_of_sub_eq_const (i : Fin n)
    {h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k} {c : k}
    (hc : c ≠ 0) (hconst : h₁ - h₀ = AffineMap.const k _ c) :
    graphSubspace i h₀ ⊓ graphSubspace i h₁ = ⊥ := by
  have hz : zeroLocus (h₁ - h₀) = ⊥ := by
    rw [hconst]
    exact zeroLocus_eq_bot_iff.mpr ⟨Units.mk0 c hc, rfl⟩
  have hm := map_graphSubspace_inf i h₀ h₁
  rw [hz] at hm
  exact (AffineSubspace.map_eq_bot_iff _).mp hm

/-- A nonzero constant difference gives distinct graphs, as needed by the parallel-pair API. -/
theorem graphSubspace_ne_of_sub_eq_const (i : Fin n)
    {h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k} {c : k}
    (hc : c ≠ 0) (hconst : h₁ - h₀ = AffineMap.const k _ c) :
    graphSubspace i h₀ ≠ graphSubspace i h₁ := by
  intro hh
  have hbot := graphSubspace_inf_eq_bot_of_sub_eq_const i hc hconst
  rw [hh, inf_idem] at hbot
  exact (isEquation_graphEquation i h₁).isHyperplane.ne_bot hbot

/-- A nonconstant difference forces two graphs to meet. -/
theorem graphSubspace_inf_ne_bot_of_sub_linear_ne_zero (i : Fin n)
    {h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k} (hlin : (h₁ - h₀).linear ≠ 0) :
    graphSubspace i h₀ ⊓ graphSubspace i h₁ ≠ ⊥ := by
  intro hz
  have hm := map_graphSubspace_inf i h₀ h₁
  rw [hz, AffineSubspace.map_bot] at hm
  exact zeroLocus_ne_bot hlin hm.symm

/-- The common trace of graphs with nonconstant difference projects to a hyperplane in the
remaining coordinates. -/
theorem isHyperplane_map_graphSubspace_inf (i : Fin n)
    {h₀ h₁ : (omittedCoordinates i → k) →ᵃ[k] k} (hlin : (h₁ - h₀).linear ≠ 0) :
    IsHyperplane ((graphSubspace i h₀ ⊓ graphSubspace i h₁).map
      (coordinateProjection (omittedCoordinates i)).toAffineMap) := by
  rw [map_graphSubspace_inf]
  exact isHyperplane_zeroLocus_iff.mpr hlin

end OrlikSolomon.HyperplaneGT
