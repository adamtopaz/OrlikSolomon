/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import OrlikSolomon.Algebra.FinsuppKernel
public import OrlikSolomon.HyperplaneGT.Reconstruction.Trace.Geometry

/-!
# The surjective hyperplane trace map

The trace domain is the actual submodule of finitely supported functions whose coefficient
at the fixed hyperplane vanishes. Mathlib's supported-function equivalence identifies it
with the free module on the other hyperplanes. Optional relabeling then discards parallel
hyperplanes and merges equal retained traces. Geometric surjectivity on labels makes the
resulting linear map surjective, including over the zero semiring.

## Main results

* `mem_traceDomain` gives the coefficient-zero description of the domain.
* `traceDomainEquiv` reuses the supported-function equivalence.
* `traceMap_traceSingle` gives the ordered basis formula.
* `traceMap_surjective` proves surjectivity without any coefficient nontriviality hypothesis.

Blueprint: the trace map and its surjectivity in L01 (`lem:l01`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} [Field k] {n : ℕ} (R : Type v) [Semiring R]

/-- The submodule of the literal universal free module having coefficient zero at `H`.

Blueprint: the submodule `U_H` in `lem:l01`. -/
def traceDomain (H : Hyperplane k n) : Submodule R (Hyperplane k n →₀ R) :=
  Finsupp.supported R R {K | K ≠ H}

/-- Domain membership is the vanishing of exactly the fixed hyperplane's coefficient. -/
@[simp]
theorem mem_traceDomain (H : Hyperplane k n) (x : Hyperplane k n →₀ R) :
    x ∈ traceDomain R H ↔ x H = 0 := by
  simp [traceDomain, Finsupp.mem_supported']

/-- The domain is canonically the free module on the off-hyperplane labels. -/
def traceDomainEquiv (H : Hyperplane k n) :
    traceDomain R H ≃ₗ[R] ({K : Hyperplane k n // K ≠ H} →₀ R) :=
  Finsupp.supportedEquivFinsupp {K : Hyperplane k n | K ≠ H}

/-- The trace-domain basis vector associated to an off-hyperplane label and a coefficient. -/
def traceSingle (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H}) (r : R) :
    traceDomain R H :=
  (traceDomainEquiv R H).symm (Finsupp.single K r)

/-- The domain basis vector is the ordinary single in the literal universal module. -/
@[simp]
theorem coe_traceSingle (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H}) (r : R) :
    (traceSingle R H K r : Hyperplane k n →₀ R) = Finsupp.single K.val r :=
  Finsupp.supportedEquivFinsupp_symm_single _ _ _

/-- The inverse supported-function equivalence is extension by zero on the ambient labels. -/
theorem traceDomain_subtype_comp_symm (H : Hyperplane k n) :
    (traceDomain R H).subtype.comp (traceDomainEquiv R H).symm.toLinearMap =
      Finsupp.lmapDomain R R (Subtype.val : {K : Hyperplane k n // K ≠ H} → Hyperplane k n) := by
  apply Finsupp.lhom_ext
  intro K r
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  change (traceSingle R H K r : Hyperplane k n →₀ R) = Finsupp.single K.val r
  exact coe_traceSingle R H K r

/-- The hyperplane trace map discards strict parallel labels and retains each other actual
intrinsic trace. Its domain is the coefficient-zero submodule of the universal free module.

Blueprint: the map `s_H` in `lem:l01`. -/
def traceMap (H : Hyperplane k n) : traceDomain R H →ₗ[R] (IntrinsicHyperplane H →₀ R) :=
  (finsuppOptionMap (traceLabel H)).comp (traceDomainEquiv R H).toLinearMap

/-- On the canonical basis the trace map is optional relabeling. -/
@[simp]
theorem traceMap_traceSingle (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H})
    (r : R) :
    traceMap R H (traceSingle R H K r) =
      (traceLabel H K).elim 0 (fun J ↦ Finsupp.single J r) := by
  change (finsuppOptionMap (traceLabel H))
    ((traceDomainEquiv R H) ((traceDomainEquiv R H).symm (Finsupp.single K r))) = _
  rw [(traceDomainEquiv R H).apply_symm_apply]
  exact finsuppOptionMap_single _ _ _

/-- Conjugating the trace map by supported functions recovers the generic optional label map.
-/
theorem traceMap_comp_symm (H : Hyperplane k n) :
    (traceMap R H).comp (traceDomainEquiv R H).symm.toLinearMap =
      finsuppOptionMap (traceLabel H) := by
  apply LinearMap.ext
  intro x
  change (finsuppOptionMap (traceLabel H))
    ((traceDomainEquiv R H) ((traceDomainEquiv R H).symm x)) = _
  rw [(traceDomainEquiv R H).apply_symm_apply]

/-- Every finitely supported function on the intrinsic trace hyperplanes has a preimage.
This remains valid for the zero semiring and empty intrinsic label type. -/
theorem traceMap_surjective (H : Hyperplane k n) : Function.Surjective (traceMap R H) :=
  (finsuppOptionMap_surjective (traceLabel H) (traceLabel_surjective H)).comp
    (traceDomainEquiv R H).surjective

end OrlikSolomon.HyperplaneGT
