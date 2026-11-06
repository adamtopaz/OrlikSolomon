/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import OrlikSolomon.Presentation.Basic

/-!
# Coefficient base change of the affine presentation

For any homomorphism of commutative rings `R → B`, the canonical coefficient map induces
`OSAlgebra.baseChangeEquiv : B ⊗[R] OSAlgebra R 𝒜 ≃ₐ[B] OSAlgebra B 𝒜`.
Both maps are defined on the presentation generators. Checking the inverse identities on
generators proves the equivalence without any flatness assumption or restriction on two.

Blueprint: coefficient base change in `lem:os-basic`.
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u

namespace OrlikSolomon.OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] (𝒜 : Arrangement k V)

/-- The coefficient map between affine presentations, sending each hyperplane generator to
the corresponding generator over the new coefficient ring. -/
def coefficientMap : OSAlgebra R 𝒜 →ₐ[R] OSAlgebra B 𝒜 :=
  lift (generator B 𝒜) isFamily_generator

@[simp]
theorem coefficientMap_generator (H : 𝒜) :
    coefficientMap R B 𝒜 (generator R 𝒜 H) = generator B 𝒜 H :=
  lift_generator _ _ H

@[simp]
theorem coefficientMap_word (I : List 𝒜) :
    coefficientMap R B 𝒜 (word (generator R 𝒜) I) = word (generator B 𝒜) I := by
  simp

/-- The canonical map from the coefficient tensor product to the presentation over `B`. -/
def baseChangeHom : B ⊗[R] OSAlgebra R 𝒜 →ₐ[B] OSAlgebra B 𝒜 :=
  Algebra.TensorProduct.lift (Algebra.ofId B (OSAlgebra B 𝒜)) (coefficientMap R B 𝒜)
    fun b x ↦ Algebra.commutes b (coefficientMap R B 𝒜 x)

@[simp]
theorem baseChangeHom_tmul (b : B) (x : OSAlgebra R 𝒜) :
    baseChangeHom R B 𝒜 (b ⊗ₜ[R] x) = b • coefficientMap R B 𝒜 x :=
  rfl

/-- The inverse coefficient map sends each generator to the tensor with coefficient one. -/
def baseChangeInv : OSAlgebra B 𝒜 →ₐ[B] B ⊗[R] OSAlgebra R 𝒜 :=
  lift (fun H ↦ 1 ⊗ₜ[R] generator R 𝒜 H)
    (isFamily_generator.map
      (Algebra.TensorProduct.includeRight :
        OSAlgebra R 𝒜 →ₐ[R] B ⊗[R] OSAlgebra R 𝒜).toRingHom)

@[simp]
theorem baseChangeInv_generator (H : 𝒜) :
    baseChangeInv R B 𝒜 (generator B 𝒜 H) = 1 ⊗ₜ[R] generator R 𝒜 H :=
  lift_generator _ _ H

/-- The inverse map agrees with the tensor inclusion on the original coefficients. -/
theorem baseChangeInv_comp_coefficientMap :
    ((baseChangeInv R B 𝒜).restrictScalars R).comp (coefficientMap R B 𝒜) =
      Algebra.TensorProduct.includeRight := by
  ext H
  simp

@[simp]
theorem baseChangeInv_coefficientMap (x : OSAlgebra R 𝒜) :
    baseChangeInv R B 𝒜 (coefficientMap R B 𝒜 x) = 1 ⊗ₜ[R] x :=
  DFunLike.congr_fun (baseChangeInv_comp_coefficientMap R B 𝒜) x

/-- The two canonical coefficient maps are inverse on the tensor product. -/
theorem baseChangeInv_comp_baseChangeHom :
    (baseChangeInv R B 𝒜).comp (baseChangeHom R B 𝒜) =
      AlgHom.id B (B ⊗[R] OSAlgebra R 𝒜) := by
  apply Algebra.TensorProduct.ext'
  intro b x
  simp [TensorProduct.smul_tmul']

/-- The two canonical coefficient maps are inverse on the affine presentation. -/
theorem baseChangeHom_comp_baseChangeInv :
    (baseChangeHom R B 𝒜).comp (baseChangeInv R B 𝒜) = AlgHom.id B (OSAlgebra B 𝒜) := by
  ext H
  simp

/-- Coefficient extension commutes with the affine Orlik–Solomon presentation. This equivalence
requires neither flatness nor that the coefficient rings be nontrivial.

Blueprint: `lem:os-basic`. -/
def baseChangeEquiv : B ⊗[R] OSAlgebra R 𝒜 ≃ₐ[B] OSAlgebra B 𝒜 where
  __ := baseChangeHom R B 𝒜
  invFun := baseChangeInv R B 𝒜
  left_inv x := DFunLike.congr_fun (baseChangeInv_comp_baseChangeHom R B 𝒜) x
  right_inv x := DFunLike.congr_fun (baseChangeHom_comp_baseChangeInv R B 𝒜) x

@[simp]
theorem baseChangeEquiv_tmul (b : B) (x : OSAlgebra R 𝒜) :
    baseChangeEquiv R B 𝒜 (b ⊗ₜ[R] x) = b • coefficientMap R B 𝒜 x :=
  rfl

@[simp]
theorem baseChangeEquiv_symm_generator (H : 𝒜) :
    (baseChangeEquiv R B 𝒜).symm (generator B 𝒜 H) = 1 ⊗ₜ[R] generator R 𝒜 H :=
  baseChangeInv_generator R B 𝒜 H

/-- The coefficient map commutes with inclusions of arrangements. -/
theorem coefficientMap_comp_map {ℬ : Arrangement k V} (h : 𝒜 ≤ ℬ) :
    (coefficientMap R B ℬ).comp (map R h) =
      ((map B h).restrictScalars R).comp (coefficientMap R B 𝒜) := by
  ext H
  simp

end OrlikSolomon.OSAlgebra
