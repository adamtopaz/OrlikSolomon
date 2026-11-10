/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.QuadraticKernel
public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.LinearExtension

/-!
# Coefficient extension of the actual quadratic relation spans

The exterior coefficient map sends each standard generator to the generator with the same
label over the new coefficient ring. It preserves every exterior degree and sends both A02
relation families to those same relations. Consequently finite linear witnesses in the
original relation span extend to witnesses in the new span. Naturality with extended linear
maps then proves preservation of the new relation span by coefficient-extended matrices.

Blueprint: the relation-witness extension in S05 (`thm:s05`). No flatness or injectivity
assumption, cohomology base change, or quadratic presentation of the full OS algebra is used.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

open Module

universe r s u v

variable (R : Type r) [CommRing R] (A : Type s) [CommRing A] [Algebra R A]
  (ι : Type u)

/-- The actual exterior-algebra coefficient map, with the same free generator labels. -/
def exteriorCoefficientMap :
    ExteriorAlgebra R (ι →₀ R) →ₐ[R] ExteriorAlgebra A (ι →₀ A) :=
  exteriorLift R ⟨exteriorGen A, isExteriorFamily_exteriorGen A⟩

/-- The exterior coefficient map keeps every free generator label. -/
@[simp]
theorem exteriorCoefficientMap_exteriorGen (i : ι) :
    exteriorCoefficientMap R A ι (exteriorGen R i) = exteriorGen A i :=
  exteriorLift_exteriorGen _ _ _

/-- The exterior coefficient map preserves each whole exterior degree. -/
theorem exteriorCoefficientMap_mem_exteriorPower (q : ℕ)
    {x : ExteriorAlgebra R (ι →₀ R)} (hx : x ∈ ⋀[R]^q (ι →₀ R)) :
    exteriorCoefficientMap R A ι x ∈ ⋀[A]^q (ι →₀ A) := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    rw [map_word]
    simp only [exteriorCoefficientMap_exteriorGen]
    simpa only [hI] using word_mem_exteriorPower A I
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [map_smul, ← IsScalarTower.algebraMap_smul A r]
    exact Submodule.smul_mem _ _ ih

/-- On the full degree-one module, the exterior coefficient map is coefficientwise. -/
theorem exteriorCoefficientMap_ι (x : ι →₀ R) :
    exteriorCoefficientMap R A ι (ExteriorAlgebra.ι R x) =
      ExteriorAlgebra.ι A (Finsupp.mapRange.linearMap (Algebra.linearMap R A) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single i r =>
    rw [show Finsupp.single i r = r • Finsupp.single i (1 : R) by simp]
    simp only [map_smul]
    change r • exteriorCoefficientMap R A ι (exteriorGen R i) = _
    rw [exteriorCoefficientMap_exteriorGen]
    simp only [exteriorGen]
    rw [← (ExteriorAlgebra.ι A).map_smul_of_tower]
    simp

/-- The exterior map restricted to degree q, linear over the original coefficient ring. -/
def exteriorPowerCoefficientMap (q : ℕ) :
    (⋀[R]^q (ι →₀ R)) →ₗ[R] (⋀[A]^q (ι →₀ A)) :=
  (((exteriorCoefficientMap R A ι).toLinearMap).comp (⋀[R]^q (ι →₀ R)).subtype).codRestrict
    ((⋀[A]^q (ι →₀ A)).restrictScalars R)
    (fun x ↦ exteriorCoefficientMap_mem_exteriorPower R A ι q x.property)

/-- The restricted map is the actual exterior coefficient map after forgetting the subtype. -/
@[simp]
theorem coe_exteriorPowerCoefficientMap (q : ℕ) (x : ⋀[R]^q (ι →₀ R)) :
    (exteriorPowerCoefficientMap R A ι q x : ExteriorAlgebra A (ι →₀ A)) =
      exteriorCoefficientMap R A ι x := rfl

variable {ι} {κ : Type v}

/-- Exterior coefficient change commutes with extending a linear map's matrix. -/
theorem exteriorCoefficientMap_naturality (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) :
    (exteriorCoefficientMap R A κ).comp (ExteriorAlgebra.map f) =
      ((ExteriorAlgebra.map (coefficientExtendLinearMap R A f)).restrictScalars R).comp
        (exteriorCoefficientMap R A ι) := by
  apply exteriorAlgHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    exteriorGen, ExteriorAlgebra.map_apply_ι, exteriorCoefficientMap_ι]
  rw [coefficientExtendLinearMap_mapRange]

/-- Naturality of coefficient change on the actual internal exterior-power subtypes. -/
theorem exteriorPowerCoefficientMap_naturality (q : ℕ)
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (x : ⋀[R]^q (ι →₀ R)) :
    exteriorPowerCoefficientMap R A κ q (exteriorPower.map q f x) =
      exteriorPower.map q (coefficientExtendLinearMap R A f)
        (exteriorPowerCoefficientMap R A ι q x) := by
  apply Subtype.ext
  simp only [coe_exteriorPowerCoefficientMap, exteriorPower.coe_map]
  exact DFunLike.congr_fun (exteriorCoefficientMap_naturality R A f)
    (x : ExteriorAlgebra R (ι →₀ R))

variable {k : Type u} [Field k] {n : ℕ} (𝒜 : Arrangement k (Fin n → k))

/-- Coefficient extension preserves the actual pair wedge and both labels. -/
@[simp]
theorem exteriorPowerCoefficientMap_pair (H K : 𝒜) :
    exteriorPowerCoefficientMap R A 𝒜 2 (osExteriorPair R 𝒜 H K) =
      osExteriorPair A 𝒜 H K := by
  apply Subtype.ext
  simp

/-- Coefficient extension preserves the guarded dependent-triple wedge, including its signs.
-/
@[simp]
theorem exteriorPowerCoefficientMap_differencePair (H K L : 𝒜) :
    exteriorPowerCoefficientMap R A 𝒜 2 (osExteriorDifferencePair R 𝒜 H K L) =
      osExteriorDifferencePair A 𝒜 H K L := by
  simp [osExteriorDifferencePair]

/-- An actual finite linear witness in A02's relation span extends along any coefficient
algebra map. No injectivity or flatness hypothesis is needed. -/
theorem exteriorPowerCoefficientMap_mem_quadraticRelationSpan
    {x : ⋀[R]^2 (𝒜 →₀ R)} (hx : x ∈ quadraticRelationSpan R 𝒜) :
    exteriorPowerCoefficientMap R A 𝒜 2 x ∈ quadraticRelationSpan A 𝒜 := by
  rw [quadraticRelationSpan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨H, K, h, rfl⟩ | ⟨H, K, L, h, rfl⟩
    · rw [exteriorPowerCoefficientMap_pair]
      exact osExteriorPair_mem_quadraticRelationSpan A 𝒜 H K h
    · rw [exteriorPowerCoefficientMap_differencePair]
      exact osExteriorDifferencePair_mem_quadraticRelationSpan A 𝒜 H K L h
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [map_smul, ← IsScalarTower.algebraMap_smul A r]
    exact Submodule.smul_mem _ _ ih

/-- A matrix preserving the full quadratic relation span continues to preserve it after
coefficient extension. The proof extends witnesses for each of the two actual A02 families.
-/
theorem coefficientExtendLinearMap_preserves_quadraticRelationSpan
    (f : (𝒜 →₀ R) →ₗ[R] (𝒜 →₀ R))
    (hf : (quadraticRelationSpan R 𝒜).map (exteriorPower.map 2 f) ≤
      quadraticRelationSpan R 𝒜) :
    (quadraticRelationSpan A 𝒜).map
        (exteriorPower.map 2 (coefficientExtendLinearMap R A f)) ≤
      quadraticRelationSpan A 𝒜 := by
  rw [Submodule.map_le_iff_le_comap, quadraticRelationSpan, Submodule.span_le]
  rintro x (⟨H, K, h, rfl⟩ | ⟨H, K, L, h, rfl⟩)
  · change exteriorPower.map 2 (coefficientExtendLinearMap R A f)
      (osExteriorPair A 𝒜 H K) ∈ quadraticRelationSpan A 𝒜
    rw [← exteriorPowerCoefficientMap_pair R A 𝒜 H K,
      ← exteriorPowerCoefficientMap_naturality]
    apply exteriorPowerCoefficientMap_mem_quadraticRelationSpan
    exact hf ⟨_, osExteriorPair_mem_quadraticRelationSpan R 𝒜 H K h, rfl⟩
  · change exteriorPower.map 2 (coefficientExtendLinearMap R A f)
      (osExteriorDifferencePair A 𝒜 H K L) ∈ quadraticRelationSpan A 𝒜
    rw [← exteriorPowerCoefficientMap_differencePair R A 𝒜 H K L,
      ← exteriorPowerCoefficientMap_naturality]
    apply exteriorPowerCoefficientMap_mem_quadraticRelationSpan
    exact hf ⟨_, osExteriorDifferencePair_mem_quadraticRelationSpan R 𝒜 H K L h, rfl⟩

end OrlikSolomon.HyperplaneGT
