/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Decomposition

/-!
# Vertical restriction of decomposition functionals

A hyperplane nonvertical over all but one coordinate is an affine graph. Its projection
identifies vertical hyperplanes with the actual intrinsic hyperplanes of the graph. This
bijection is derived from the existing graph projection equivalence and affine chart:
vertical equations factor through coordinate projection, and intrinsic hyperplanes pull
back along that projection.

The vertical module is the actual supported submodule of the universal Finsupp module;
restriction is Mathlib's dual restriction to that submodule. The explicit decomposition
coordinates extend every functional on the vertical module. Their restriction has kernel
exactly inertia, and the distinguished delta restricts to zero. Coefficient rings may be
zero and live in a universe independent of the geometric field. No reflexivity assertion
or lower dimension bound is used.

## Main results

* `verticalTraceEquiv` is the actual vertical-label/intrinsic-trace bijection.
* `map_decomposition_verticalRestriction` gives the whole dual of the vertical module.
* `ker_verticalRestriction_inf_decomposition` identifies the ambient kernel with inertia.
* `verticalRestriction_delta` gives the zero restriction of the distinguished delta.
* `decompositionVerticalRestriction_surjective` and `ker_decompositionVerticalRestriction`
  give the corresponding statements on the restricted map.

Blueprint: L03 (`lem:l03`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u

variable {k : Type u} [Field k] {n : ℕ}

private def chartProjection (i : Fin n) (H : Hyperplane k n) :
    H.val.direction →ᵃ[k] (omittedCoordinates i → k) :=
  (coordinateProjection (omittedCoordinates i)).toAffineMap.comp (chart H.val)

private theorem chartProjection_bijective (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (omittedCoordinates i) H) : Function.Bijective (chartProjection i H) := by
  obtain ⟨h, hh, -⟩ := existsUnique_graph_of_not_isVertical i H hH
  have heq : graphHyperplane i h = H := Subtype.ext hh
  subst H
  constructor
  · intro x y hxy
    apply chart_injective
    have hx := chart_mem (isEquation_graphEquation i h).isHyperplane.ne_bot x
    have hy := chart_mem (isEquation_graphEquation i h).isHyperplane.ne_bot y
    have he : graphProjectionEquiv i h ⟨chart (graphSubspace i h) x, hx⟩ =
        graphProjectionEquiv i h ⟨chart (graphSubspace i h) y, hy⟩ := hxy
    exact congrArg Subtype.val ((graphProjectionEquiv i h).injective he)
  · intro y
    obtain ⟨x, hx⟩ := (graphProjectionEquiv i h).surjective y
    obtain ⟨v, hv⟩ := exists_chart_eq (isEquation_graphEquation i h).isHyperplane.ne_bot x.property
    refine ⟨v, ?_⟩
    change coordinateProjection (omittedCoordinates i) (chart (graphSubspace i h) v) = y
    rw [hv]
    exact hx

private def chartProjectionEquiv (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (omittedCoordinates i) H) :
    H.val.direction ≃ᵃ[k] (omittedCoordinates i → k) :=
  AffineEquiv.ofBijective (φ := chartProjection i H) (chartProjection_bijective i H hH)

private theorem equation_factor_of_vertical (i : Fin n) (K : Hyperplane k n)
    (hK : IsVertical (omittedCoordinates i) K) :
    equation K.val = ((equation K.val).comp (coordinateSection i).toAffineMap).comp
      (coordinateProjection (omittedCoordinates i)).toAffineMap := by
  have hc := (isVertical_iff_of_isEquation _ K (isEquation_equation K.property)).mp hK i (by simp)
  apply AffineMap.ext
  intro x
  simpa only [hc, zero_mul, zero_add, AffineMap.comp_apply, LinearMap.coe_toAffineMap] using
    affineForm_decompose i (equation K.val) x

private theorem exists_base_of_vertical (i : Fin n) (K : Hyperplane k n)
    (hK : IsVertical (omittedCoordinates i) K) :
    ∃ B : AffineSubspace k (omittedCoordinates i → k), IsHyperplane B ∧
      B.comap (coordinateProjection (omittedCoordinates i)).toAffineMap = K.val := by
  let f := (equation K.val).comp (coordinateSection i).toAffineMap
  have hfactor := equation_factor_of_vertical i K hK
  have hlin : f.linear ≠ 0 := by
    intro hz
    apply (isEquation_equation K.property).linear_ne_zero
    have heq := congrArg AffineMap.linear hfactor
    change (equation K.val).linear =
      f.linear.comp (coordinateProjection (omittedCoordinates i)) at heq
    rw [hz, LinearMap.zero_comp] at heq
    exact heq
  refine ⟨zeroLocus f, isHyperplane_zeroLocus_iff.mpr hlin, ?_⟩
  rw [← zeroLocus_comp, ← hfactor, (isEquation_equation K.property).zeroLocus_eq]

private theorem isHyperplane_comap_projection (i : Fin n)
    (B : AffineSubspace k (omittedCoordinates i → k)) (hB : IsHyperplane B) :
    IsHyperplane (B.comap (coordinateProjection (omittedCoordinates i)).toAffineMap) := by
  obtain ⟨f, hf⟩ := hB.exists_isEquation
  have hcomp : (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).comp
      (coordinateSection i).toAffineMap = f := by
    ext x
    simp
  have hlin : (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).linear ≠ 0 := by
    intro hz
    apply hf.linear_ne_zero
    have heq := congrArg AffineMap.linear hcomp
    change (f.comp (coordinateProjection (omittedCoordinates i)).toAffineMap).linear.comp
      (coordinateSection i) = f.linear at heq
    rw [hz, LinearMap.zero_comp] at heq
    exact heq.symm
  rw [← hf.zeroLocus_eq, ← zeroLocus_comp]
  exact isHyperplane_zeroLocus_iff.mpr hlin

private theorem isVertical_comap_projection (i : Fin n)
    (B : AffineSubspace k (omittedCoordinates i → k)) (hB : IsHyperplane B) :
    IsVertical (omittedCoordinates i)
      ⟨B.comap (coordinateProjection (omittedCoordinates i)).toAffineMap,
        isHyperplane_comap_projection i B hB⟩ := by
  obtain ⟨f, hf⟩ := hB.exists_isEquation
  rw [isVertical_iff_of_isEquation _ _
    (hf.comp _ (isHyperplane_comap_projection i B hB))]
  intro j hj
  have hji : j = i := by simpa using hj
  subst j
  have hz : coordinateProjection (omittedCoordinates i) (Pi.single i (1 : k)) = 0 := by
    ext j
    simp [(mem_omittedCoordinates i j.val).mp j.property]
  rw [affineCoefficients_succ]
  change f.linear (coordinateProjection (omittedCoordinates i) (Pi.single i 1)) = 0
  rw [hz, map_zero]

private theorem isHyperplane_vertical_comap_chart (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (omittedCoordinates i) H)
    (K : Hyperplane k n) (hK : IsVertical (omittedCoordinates i) K) :
    IsHyperplane (K.val.comap (chart H.val)) := by
  obtain ⟨B, hB, hBK⟩ := exists_base_of_vertical i K hK
  rw [← hBK, AffineSubspace.comap_comap]
  exact hB.comap_affineEquiv (chartProjectionEquiv i H hH)

private theorem vertical_comap_chart_injective (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (omittedCoordinates i) H)
    (K L : {K : Hyperplane k n // IsVertical (omittedCoordinates i) K})
    (hKL : K.val.val.comap (chart H.val) = L.val.val.comap (chart H.val)) : K = L := by
  obtain ⟨B, -, hBK⟩ := exists_base_of_vertical i K.val K.property
  obtain ⟨D, -, hDL⟩ := exists_base_of_vertical i L.val L.property
  have he : B.comap (chartProjectionEquiv i H hH).toAffineMap =
      D.comap (chartProjectionEquiv i H hH).toAffineMap := by
    change B.comap ((coordinateProjection (omittedCoordinates i)).toAffineMap.comp
      (chart H.val)) = D.comap ((coordinateProjection (omittedCoordinates i)).toAffineMap.comp
      (chart H.val))
    rw [← AffineSubspace.comap_comap, ← AffineSubspace.comap_comap, hBK, hDL]
    exact hKL
  have hBD := comap_affineEquiv_injective (chartProjectionEquiv i H hH) he
  apply Subtype.ext
  apply Subtype.ext
  rw [← hBK, ← hDL, hBD]

private theorem exists_vertical_comap_chart (i : Fin n) (H : Hyperplane k n)
    (hH : ¬IsVertical (omittedCoordinates i) H) (J : IntrinsicHyperplane H) :
    ∃ K : {K : Hyperplane k n // IsVertical (omittedCoordinates i) K},
      K.val.val.comap (chart H.val) = J.val := by
  let e := chartProjectionEquiv i H hH
  let B := J.val.comap e.symm.toAffineMap
  have hB : IsHyperplane B := J.property.comap_affineEquiv e.symm
  let K : Hyperplane k n :=
    ⟨B.comap (coordinateProjection (omittedCoordinates i)).toAffineMap,
      isHyperplane_comap_projection i B hB⟩
  have hKv : IsVertical (omittedCoordinates i) K := isVertical_comap_projection i B hB
  refine ⟨⟨K, hKv⟩, ?_⟩
  change (B.comap (coordinateProjection (omittedCoordinates i)).toAffineMap).comap
    (chart H.val) = J.val
  rw [AffineSubspace.comap_comap]
  change (J.val.comap e.symm.toAffineMap).comap e.toAffineMap = J.val
  exact comap_symm_comap e J.val

/-- Every vertical hyperplane meets a nonvertical graph in an intrinsic hyperplane.
The projection from that graph supplies an affine equivalence with the remaining coordinates.
Blueprint: the geometric trace assertion in `lem:l03`. -/
theorem isHyperplane_comap_chart_of_isVertical (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H)
    (K : Hyperplane k n) (hK : IsVertical z K) :
    IsHyperplane (K.val.comap (chart H.val)) := by
  obtain rfl := eq_omittedCoordinates z i hzi
  exact isHyperplane_vertical_comap_chart i H hH K hK

/-- The actual chart comap of a vertical hyperplane, as an intrinsic hyperplane of a graph. -/
def verticalTrace (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H)
    (K : {K : Hyperplane k n // IsVertical z K}) : IntrinsicHyperplane H :=
  ⟨K.val.val.comap (chart H.val),
    isHyperplane_comap_chart_of_isVertical z i hzi H hH K.val K.property⟩

/-- Each intrinsic graph hyperplane is the trace of exactly one vertical hyperplane.
This includes the vacuous one-dimensional case, without assuming a trace bijection. -/
theorem verticalTrace_bijective (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    Function.Bijective (verticalTrace z i hzi H hH) := by
  obtain rfl := eq_omittedCoordinates z i hzi
  constructor
  · intro K L heq
    exact vertical_comap_chart_injective i H hH K L (congrArg Subtype.val heq)
  · intro J
    obtain ⟨K, hK⟩ := exists_vertical_comap_chart i H hH J
    exact ⟨K, Subtype.ext hK⟩

/-- Graph projection identifies actual vertical labels with all intrinsic trace labels.
Blueprint: the vertical trace bijection used in `lem:l03`. -/
def verticalTraceEquiv (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    {K : Hyperplane k n // IsVertical z K} ≃ IntrinsicHyperplane H :=
  Equiv.ofBijective _ (verticalTrace_bijective z i hzi H hH)

/-- The trace bijection records the actual chart comap. -/
@[simp]
theorem verticalTraceEquiv_val (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H)
    (K : {K : Hyperplane k n // IsVertical z K}) :
    (verticalTraceEquiv z i hzi H hH K).val = K.val.val.comap (chart H.val) := rfl

/-- The optional trace map retains every vertical label with exactly its graph trace. -/
theorem traceLabel_verticalTraceEquiv (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H)
    (K : {K : Hyperplane k n // IsVertical z K}) (hKH : K.val ≠ H) :
    traceLabel H ⟨K.val, hKH⟩ = some (verticalTraceEquiv z i hzi H hH K) := by
  exact (traceLabel_eq_some_iff H _ _).mpr rfl

section Restriction

universe v

variable (R : Type v) [CommSemiring R]

/-- The actual free span of all hyperplanes vertical over the given coordinate set.
Blueprint: `M_z` in `lem:l03`. -/
def verticalModule (z : Finset (Fin n)) : Submodule R (Hyperplane k n →₀ R) :=
  Finsupp.supported R R {K | IsVertical z K}

/-- Vertical-module membership means vanishing at each nonvertical coordinate. -/
@[simp]
theorem mem_verticalModule (z : Finset (Fin n)) (x : Hyperplane k n →₀ R) :
    x ∈ verticalModule (k := k) R z ↔ ∀ K, ¬IsVertical z K → x K = 0 := by
  exact Finsupp.mem_supported' R x

/-- The supported vertical module has its ordinary basis indexed by the vertical labels. -/
def verticalModuleEquiv (z : Finset (Fin n)) :
    verticalModule (k := k) R z ≃ₗ[R] ({K : Hyperplane k n // IsVertical z K} →₀ R) :=
  Finsupp.supportedEquivFinsupp {K : Hyperplane k n | IsVertical z K}

/-- The supported-module basis vector at an actual vertical hyperplane. -/
def verticalSingle (z : Finset (Fin n)) (K : {K : Hyperplane k n // IsVertical z K}) (r : R) :
    verticalModule (k := k) R z :=
  (verticalModuleEquiv (k := k) R z).symm (Finsupp.single K r)

/-- A vertical basis vector is the same single in the universal Finsupp module. -/
@[simp]
theorem coe_verticalSingle (z : Finset (Fin n))
    (K : {K : Hyperplane k n // IsVertical z K}) (r : R) :
    (verticalSingle (k := k) R z K r : Hyperplane k n →₀ R) = Finsupp.single K.val r :=
  Finsupp.supportedEquivFinsupp_symm_single _ _ _

/-- The actual restriction of the universal dual to the supported vertical module.
Blueprint: `p_z` in `lem:l03`. -/
def verticalRestriction (z : Finset (Fin n)) :
    Module.Dual R (Hyperplane k n →₀ R) →ₗ[R] Module.Dual R (verticalModule (k := k) R z) :=
  (verticalModule (k := k) R z).dualRestrict

/-- Dual restriction evaluates on the same underlying universal vector. -/
@[simp]
theorem verticalRestriction_apply (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R)) (x : verticalModule (k := k) R z) :
    verticalRestriction (k := k) R z φ x = φ x.val := rfl

/-- A functional restricts to zero exactly when it vanishes at every vertical basis label. -/
theorem verticalRestriction_eq_zero_iff (z : Finset (Fin n))
    (φ : Module.Dual R (Hyperplane k n →₀ R)) :
    verticalRestriction (k := k) R z φ = 0 ↔
      ∀ K, IsVertical z K → φ (Finsupp.single K 1) = 0 := by
  constructor
  · intro h K hK
    have hv := LinearMap.congr_fun h (verticalSingle (k := k) R z ⟨K, hK⟩ 1)
    simpa only [verticalRestriction_apply, coe_verticalSingle, LinearMap.zero_apply] using hv
  · intro h
    have heq : (verticalRestriction (k := k) R z φ).comp
        (verticalModuleEquiv (k := k) R z).symm.toLinearMap = 0 := by
      apply Finsupp.lhom_ext
      intro K r
      change φ (verticalSingle (k := k) R z K r).val = 0
      rw [coe_verticalSingle,
        show Finsupp.single K.val r = r • Finsupp.single K.val (1 : R) by simp,
        map_smul, h K.val K.property, smul_zero]
    ext x
    have hv := LinearMap.congr_fun heq (verticalModuleEquiv (k := k) R z x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
      LinearMap.zero_apply] using hv

/-- The delta at any nonvertical hyperplane vanishes on the vertical module.
Blueprint: the final assertion of `lem:l03`. -/
@[simp]
theorem verticalRestriction_delta (z : Finset (Fin n)) (H : Hyperplane k n)
    (hH : ¬IsVertical z H) : verticalRestriction (k := k) R z (Finsupp.lapply H) = 0 := by
  ext x
  exact (mem_verticalModule (k := k) R z x.val).mp x.property H hH

end Restriction

section DecompositionRestriction

universe v

variable (R : Type v) [CommRing R]

/-- Vertical restriction with its domain restricted to actual decomposition functionals. -/
def decompositionVerticalRestriction (z : Finset (Fin n)) (H : Hyperplane k n) :
    decomposition R H →ₗ[R] Module.Dual R (verticalModule (k := k) R z) :=
  (verticalRestriction R z).comp (decomposition R H).subtype

/-- Restriction from decomposition evaluates the same functional on the same universal vector. -/
@[simp]
theorem decompositionVerticalRestriction_apply (z : Finset (Fin n)) (H : Hyperplane k n)
    (φ : decomposition R H) (x : verticalModule (k := k) R z) :
    decompositionVerticalRestriction R z H φ x = φ.val x.val := rfl

/-- Every functional on the actual vertical module extends to a decomposition functional.
The extension uses the derived vertical-trace bijection and explicit trace coordinates.
Blueprint: the surjectivity assertion in `lem:l03`. -/
theorem decompositionVerticalRestriction_surjective (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    Function.Surjective (decompositionVerticalRestriction R z H) := by
  let e := verticalTraceEquiv z i hzi H hH
  intro ψ
  let b : IntrinsicHyperplane H → R := fun J ↦
    ψ (verticalSingle R z (e.symm J) 1)
  refine ⟨⟨traceFunctional R H (0, b), traceFunctional_mem_decomposition R H 0 b⟩, ?_⟩
  have heq : (verticalRestriction R z (traceFunctional R H (0, b))).comp
      (verticalModuleEquiv R z).symm.toLinearMap =
      ψ.comp (verticalModuleEquiv R z).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro K r
    rw [show Finsupp.single K r = r • Finsupp.single K (1 : R) by simp]
    simp only [map_smul]
    congr 1
    change traceFunctional R H (0, b) (verticalSingle R z K 1).val = ψ (verticalSingle R z K 1)
    rw [coe_verticalSingle]
    have hKH : K.val ≠ H := fun h ↦ hH (h ▸ K.property)
    rw [traceFunctional_of_traceLabel R H ⟨K.val, hKH⟩ (e K)
      (traceLabel_verticalTraceEquiv z i hzi H hH K hKH)]
    change ψ (verticalSingle R z (e.symm (e K)) 1) = _
    rw [e.symm_apply_apply]
  ext x
  change verticalRestriction R z (traceFunctional R H (0, b)) x = ψ x
  have hv := LinearMap.congr_fun heq (verticalModuleEquiv R z x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] using hv

/-- The vertical restriction image of decomposition is the whole actual vertical dual.
Blueprint: `p_z(D_H) = P_z` in `lem:l03`. -/
theorem map_decomposition_verticalRestriction (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    (decomposition R H).map (verticalRestriction R z) = ⊤ := by
  apply top_unique
  intro ψ _
  obtain ⟨φ, hφ⟩ := decompositionVerticalRestriction_surjective R z i hzi H hH ψ
  exact ⟨φ.val, φ.property, hφ⟩

/-- Decomposition functionals vanishing on the vertical module are exactly inertia.
Blueprint: the ambient kernel assertion in `lem:l03`. -/
theorem ker_verticalRestriction_inf_decomposition (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    LinearMap.ker (verticalRestriction R z) ⊓ decomposition R H = inertia R H := by
  ext φ
  constructor
  · rintro ⟨hφz, hφD⟩
    let φ' : decomposition R H := ⟨φ, hφD⟩
    have ht : decompositionTrace R H φ' = 0 := by
      funext J
      let K := (verticalTraceEquiv z i hzi H hH).symm J
      have hKH : K.val ≠ H := fun h ↦ hH (h ▸ K.property)
      have hK : traceLabel H ⟨K.val, hKH⟩ = some J := by
        have he := traceLabel_verticalTraceEquiv z i hzi H hH K hKH
        simpa only [K, Equiv.apply_symm_apply] using he
      rw [decompositionTrace_apply,
        decompositionEquiv_snd_apply_of_traceLabel R H φ' ⟨K.val, hKH⟩ J hK]
      exact (verticalRestriction_eq_zero_iff R z φ).mp hφz K.val K.property
    have hk : φ' ∈ LinearMap.ker (decompositionTrace R H) := ht
    rw [ker_decompositionTrace] at hk
    exact hk
  · intro hφ
    refine ⟨?_, inertia_le_decomposition R H hφ⟩
    obtain ⟨a, rfl⟩ := (mem_inertia R H φ).mp hφ
    change verticalRestriction R z (a • Finsupp.lapply H) = 0
    rw [map_smul, verticalRestriction_delta R z H hH, smul_zero]

/-- The kernel on the restricted decomposition domain is precisely its actual inertia line.
Blueprint: the restricted kernel assertion in `lem:l03`. -/
theorem ker_decompositionVerticalRestriction (z : Finset (Fin n)) (i : Fin n)
    (hzi : ∀ j, j ∈ z ↔ j ≠ i) (H : Hyperplane k n) (hH : ¬IsVertical z H) :
    LinearMap.ker (decompositionVerticalRestriction R z H) =
      (inertia R H).comap (decomposition R H).subtype := by
  ext φ
  have he := congrArg (fun W : Submodule R (Module.Dual R (Hyperplane k n →₀ R)) ↦
    φ.val ∈ W) (ker_verticalRestriction_inf_decomposition R z i hzi H hH)
  change (verticalRestriction R z φ.val = 0) ↔ φ.val ∈ inertia R H
  simpa only [Submodule.mem_inf, LinearMap.mem_ker, φ.property, and_true] using Iff.of_eq he

end DecompositionRestriction

end OrlikSolomon.HyperplaneGT
