/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import OrlikSolomon.DeRham.Exterior.Contraction
public import OrlikSolomon.DeRham.SmoothPair

/-!
# Wedge exactness modulo a smooth principal divisor

For a regular element `f` with formally smooth quotient `S = A/(f)`, the conormal functional
takes the class of `df` to one. Contraction therefore makes left wedge by this class exact in
positive exterior degrees and injective in degree zero. If `df ∧ η` is divisible by `f`, then
the restriction of `η` to `S` vanishes, in every degree.

These assertions require neither formal smoothness of the ambient algebra nor nontrivial rings.
The unit equation and zero algebra are included. This module imports exterior algebra separately
from the one-form splitting in `SmoothPair`.

* `ker_wedgeLeft_df_mod_succ` and `ker_wedgeLeft_df_mod_zero` give the modulo-`f` Koszul kernels.
* `powerMap_eq_zero_of_wedgeLeft_df_eq_smul` gives restriction zero for a divisible left wedge.
* `powerMap_eq_zero_of_wedgeLeft_df_mem_smul` states the same conclusion using membership in
  `(f) Ω^(q+1)`.

The proofs adapt Claude's independent review consumer for PR #88.
Blueprint: `lem:dr-modf-koszul`.
-/

@[expose] public section

open scoped TensorProduct
open KaehlerDifferential
open ExteriorAlgebra (ι)

namespace OrlikSolomon.DeRham

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (f : A)

private theorem mapBaseChange_comp_mk_principal :
    ((mapBaseChange k A (A ⧸ Ideal.span {f})).restrictScalars A) ∘ₗ
        (TensorProduct.mk A (A ⧸ Ideal.span {f}) Ω[A⁄k] 1) =
      KaehlerDifferential.map k k A (A ⧸ Ideal.span {f}) := by
  ext a
  simp [mapBaseChange_tmul]

variable [Algebra.FormallySmooth k (A ⧸ Ideal.span {f})]

/-- Modulo `f`, the kernel of left wedge by `df` in degree `n+1` is its image from degree `n`.
Blueprint: the positive-degree kernel assertion of `lem:dr-modf-koszul`. -/
theorem ker_wedgeLeft_df_mod_succ (hf : f ∈ nonZeroDivisors A) (n : ℕ) :
    LinearMap.ker (wedgeLeft (A := A ⧸ Ideal.span {f})
        ((1 : A ⧸ Ideal.span {f}) ⊗ₜ[A] D k A f) (n + 1)) =
      LinearMap.range (wedgeLeft (A := A ⧸ Ideal.span {f})
        ((1 : A ⧸ Ideal.span {f}) ⊗ₜ[A] D k A f) n) :=
  ker_wedgeLeft_succ (ℓ := conormalFunctional (k := k) f hf)
    (conormalFunctional_df (k := k) f hf) n

/-- Modulo `f`, left wedge by `df` is injective on exterior degree zero.
Blueprint: the degree-zero kernel assertion of `lem:dr-modf-koszul`. -/
theorem ker_wedgeLeft_df_mod_zero (hf : f ∈ nonZeroDivisors A) :
    LinearMap.ker (wedgeLeft (A := A ⧸ Ideal.span {f})
        ((1 : A ⧸ Ideal.span {f}) ⊗ₜ[A] D k A f) 0) = ⊥ :=
  ker_wedgeLeft_zero (ℓ := conormalFunctional (k := k) f hf)
    (conormalFunctional_df (k := k) f hf)

/-- If `df ∧ η = f ω`, then `η` restricts to zero on `A/(f)`, including when `η` has degree zero.
The forms are the actual exterior powers of Kähler differentials.
Blueprint: `lem:dr-modf-koszul`. -/
theorem powerMap_eq_zero_of_wedgeLeft_df_eq_smul (hf : f ∈ nonZeroDivisors A) {q : ℕ}
    (η : ⋀[A]^q Ω[A⁄k]) (ω : ⋀[A]^(q + 1) Ω[A⁄k])
    (h : wedgeLeft (D k A f) q η = f • ω) :
    powerMap (A ⧸ Ideal.span {f}) (KaehlerDifferential.map k k A (A ⧸ Ideal.span {f})) q η =
      0 := by
  let S := A ⧸ Ideal.span {f}
  let j : Ω[A⁄k] →ₗ[A] S ⊗[A] Ω[A⁄k] := TensorProduct.mk A S Ω[A⁄k] 1
  let e : S ⊗[A] Ω[A⁄k] := 1 ⊗ₜ[A] D k A f
  have hmod : ι S e * exteriorMap S j (η : ExteriorAlgebra A Ω[A⁄k]) = 0 := by
    have h' : ι A (D k A f) * (η : ExteriorAlgebra A Ω[A⁄k]) =
        f • (ω : ExteriorAlgebra A Ω[A⁄k]) := congrArg Subtype.val h
    have h'' := congrArg (exteriorMap S j) h'
    rw [map_mul, exteriorMap_ι, map_smul, ← algebraMap_smul S f] at h''
    have hf0 : algebraMap A S f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    rw [hf0, zero_smul] at h''
    exact h''
  have hcontract := eq_ι_mul_exteriorContraction_of_ι_mul_eq_zero
    (ℓ := conormalFunctional (k := k) f hf) (conormalFunctional_df (k := k) f hf) hmod
  have he : mapBaseChange k A S e = 0 := by
    have hf0 : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simp [e, S, mapBaseChange_tmul, map_D, hf0]
  apply Subtype.ext
  rw [coe_powerMap, ← mapBaseChange_comp_mk_principal (k := k) f, ← exteriorMap_comp S S
    (mapBaseChange k A S) j]
  change exteriorMap S (mapBaseChange k A S) (exteriorMap S j η) = 0
  rw [hcontract, map_mul, exteriorMap_ι, he, map_zero, zero_mul]

/-- If `df ∧ η` belongs to `(f) Ω^(q+1)`, then `η` restricts to zero on `A/(f)`.
This formulation includes degree zero without using truncated negative exterior degrees.
Blueprint: `lem:dr-modf-koszul`. -/
theorem powerMap_eq_zero_of_wedgeLeft_df_mem_smul (hf : f ∈ nonZeroDivisors A) {q : ℕ}
    (η : ⋀[A]^q Ω[A⁄k])
    (h : wedgeLeft (D k A f) q η ∈
      (Ideal.span {f}) • (⊤ : Submodule A (⋀[A]^(q + 1) Ω[A⁄k]))) :
    powerMap (A ⧸ Ideal.span {f}) (KaehlerDifferential.map k k A (A ⧸ Ideal.span {f})) q η =
      0 := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨ω, _, hω⟩ := h
  exact powerMap_eq_zero_of_wedgeLeft_df_eq_smul f hf η ω hω.symm

end OrlikSolomon.DeRham
