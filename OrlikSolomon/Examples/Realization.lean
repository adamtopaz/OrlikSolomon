/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Examples.Cokernel
public import OrlikSolomon.Presentation.Realization

/-!
# Regressions for the realization map

These test `OrdinaryTheory.realization` on the blueprint's regression list, for an arbitrary theory
unless stated otherwise.

* The two rational points of `𝔸¹` over `F₂`: the relation is `e₁ e₂ = 0`, whose realization holds on
  a complement with no `F₂`-points (`logClass_mul_logClass_twoPoints`). The translation `x ↦ x + 1`
  exchanges the two points, so a coordinate change can permute generators
  (`map_logClass_translation`).
* Three distinct concurrent lines: `e₂ e₃ - e₁ e₃ + e₁ e₂ = 0`, whatever the field and the
  coefficients (`logClass_threeConcurrent`).
* Dimension zero: the realization map is bijective (`bijective_realization_of_subsingleton`).
* The zero coefficient ring: the realization map is bijective
  (`bijective_realization_zeroTheory`).
* An equality of arrangements is a relabeling along the identity of `V`
  (`mem_iff_comap_refl_mem`).
* The case `R = B`, in which the grading and the coefficients could be confused: the realization map
  preserves the bigrading all the same (`isHomogeneousOfShift_realization_self`).

Blueprint: the regression list, for `lem:empty-relation`, `lem:dependent-relation`,
`def:realization` and `lem:realization-basic`.
-/

@[expose] public section

noncomputable section

open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.RealizationExamples

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]

/-! ### Two points of the line over `F₂` -/

section TwoPoints

open Sanity

/-- The point `x = 0` of `twoPoints`, as a label. -/
abbrev pointZero : twoPoints :=
  ⟨_, zeroLocus_id_mem_twoPoints⟩

/-- The point `x = 1` of `twoPoints`, as a label. -/
abbrev pointOne : twoPoints :=
  ⟨_, zeroLocus_id_sub_one_mem_twoPoints⟩

/-- `[x] [x - 1] = 0` on the complement of the two rational points of `𝔸¹` over `F₂`, for every
theory: the two points are disjoint. The complement has no `F₂`-points, by
`isEmpty_algHom_twoPoints`, so this cannot be proved on points.

Blueprint: `lem:empty-relation`, the regression list. -/
theorem logClass_mul_logClass_twoPoints (T : OrdinaryTheory.{0, v, w, z} (ZMod 2) ℬ) :
    T.logClass (complementUnit twoPoints (AffineMap.id _ _)
        (.of_mem zeroLocus_id_mem_twoPoints)) *
      T.logClass (complementUnit twoPoints (AffineMap.id _ _ - AffineMap.const _ _ 1)
        (.of_mem zeroLocus_id_sub_one_mem_twoPoints)) = 0 := by
  simpa using congrArg (T.realization twoPoints)
    (generator_mul_eq_zero_of_disjoint B twoPoints pointZero pointOne inf_zeroLocus_id_twoPoints)

/-- The translation `x ↦ x + 1` of the affine line over `F₂`. -/
def translation : ZMod 2 ≃ᵃ[ZMod 2] ZMod 2 :=
  AffineEquiv.constVAdd _ _ 1

/-- The translation pulls the point `0` back to the point `1`, since `x + 1 = x - 1` over `F₂`. -/
theorem comap_translation_zero :
    (zeroLocus (AffineMap.id (ZMod 2) (ZMod 2))).comap (translation : ZMod 2 →ᵃ[ZMod 2] ZMod 2) =
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) := by
  ext x
  revert x
  simp only [AffineSubspace.mem_comap, mem_zeroLocus]
  decide

/-- The translation pulls the point `1` back to the point `0`. -/
theorem comap_translation_one :
    (zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1)).comap
        (translation : ZMod 2 →ᵃ[ZMod 2] ZMod 2) =
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) := by
  ext x
  revert x
  simp only [AffineSubspace.mem_comap, mem_zeroLocus]
  decide

/-- The hyperplanes of `twoPoints` are its two points. -/
theorem mem_twoPoints {K : AffineSubspace (ZMod 2) (ZMod 2)} :
    K ∈ twoPoints ↔ K = zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) ∨
      K = zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) := by
  classical
  constructor
  · intro h
    simpa [twoPoints] using (mem_ofFinset.1 h).1
  · rintro (rfl | rfl)
    exacts [zeroLocus_id_mem_twoPoints, zeroLocus_id_sub_one_mem_twoPoints]

/-- The translation is a relabeling of `twoPoints` by itself. -/
theorem mem_twoPoints_iff_comap_translation (K : AffineSubspace (ZMod 2) (ZMod 2)) :
    K ∈ twoPoints ↔ K.comap (translation : ZMod 2 →ᵃ[ZMod 2] ZMod 2) ∈ twoPoints := by
  have hinj := comap_affineEquiv_injective translation
  simp only [mem_twoPoints]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inr comap_translation_zero
    · exact Or.inl comap_translation_one
  · rintro (h | h)
    · exact Or.inr (hinj (h.trans comap_translation_one.symm))
    · exact Or.inl (hinj (h.trans comap_translation_zero.symm))

/-- A coordinate change can permute the generators: the translation exchanges the two points. -/
theorem comapEquiv_translation_generator :
    comapEquiv B translation mem_twoPoints_iff_comap_translation (generator B twoPoints pointZero) =
      generator B twoPoints pointOne := by
  rw [comapEquiv_generator]
  exact congrArg (generator B twoPoints) (Subtype.ext comap_translation_zero)

/-- The realization map commutes with the coordinate change that exchanges the two points: `[x]`
pulls back to `[x - 1]`.

Blueprint: `lem:realization-basic`. -/
theorem map_logClass_translation (T : OrdinaryTheory.{0, v, w, z} (ZMod 2) ℬ) :
    T.C.map (complementIso twoPoints twoPoints translation mem_twoPoints_iff_comap_translation).hom
        (T.logClass (equationUnit twoPoints pointZero)) =
      T.logClass (equationUnit twoPoints pointOne) := by
  rw [← T.realization_generator, ← T.realization_comapEquiv, comapEquiv_translation_generator,
    T.realization_generator]

end TwoPoints

/-! ### Three concurrent lines -/

section ThreeConcurrent

open PresentationExamples

variable {k : Type u} [Field k] (T : OrdinaryTheory.{u, v, w, z} k ℬ)

/-- The three concurrent lines form a dependent family, as their intersection contains the origin
and they lie in the plane. -/
theorem isDependent_threeConcurrent (a b c : threeConcurrent k) : IsDependent [a, b, c] := by
  have h₀ : ∀ K : threeConcurrent k, (0 : k × k) ∈ (K : AffineSubspace k (k × k)) := by
    rintro ⟨K, hK⟩
    obtain rfl | rfl | rfl := (mem_threeConcurrent K).1 hK <;> simp [verticalLine]
  refine ⟨?_, ?_⟩
  · rw [← AffineSubspace.nonempty_iff_ne_bot]
    exact ⟨0, mem_inter.2 fun K _ ↦ h₀ K⟩
  · refine (codim_le_finrank _).trans_lt ?_
    simp

/-- `e₂ e₃ - e₁ e₃ + e₁ e₂ = 0` for three concurrent lines, realized in cohomology. This holds over
any field and with any coefficients, and there is no assumption on `2`.

Blueprint: `lem:dependent-relation`, the regression list. -/
theorem logClass_threeConcurrent (a b c : threeConcurrent k) :
    T.logClass (equationUnit _ b) * T.logClass (equationUnit _ c) -
        T.logClass (equationUnit _ a) * T.logClass (equationUnit _ c) +
      T.logClass (equationUnit _ a) * T.logClass (equationUnit _ b) = 0 :=
  (wordBoundary_triple _ a b c).symm.trans
    (T.log_dependentRelation (isDependent_threeConcurrent a b c))

end ThreeConcurrent

/-! ### Degenerate cases -/

section Degenerate

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- In dimension zero the only arrangement is empty, and the realization map is bijective.

Blueprint: the regression list. -/
theorem bijective_realization_of_subsingleton [Subsingleton V]
    (T : OrdinaryTheory.{u, v, w, z} k ℬ) (𝒜 : Arrangement k V) :
    Function.Bijective (T.realization 𝒜) := by
  obtain rfl := 𝒜.eq_empty_of_subsingleton
  exact T.bijective_realization_empty V

/-- With zero coefficients the realization map is bijective, between zero modules.

Blueprint: the regression list. -/
theorem bijective_realization_zeroTheory (𝒜 : Arrangement k V) :
    Function.Bijective ((Sanity.zeroTheory.{u, v, w, z} k).realization 𝒜) :=
  have : Subsingleton ((Sanity.zeroTheory.{u, v, w, z} k).C.obj (complement 𝒜)) :=
    inferInstanceAs (Subsingleton ((Sanity.zeroFunctor.{u, w, z} k).obj _))
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

omit [FiniteDimensional k V] in
/-- An equality of arrangements is the relabeling along the identity of `V`. -/
theorem mem_iff_comap_refl_mem {𝒜 𝒟 : Arrangement k V} (h : 𝒜 = 𝒟) (K : AffineSubspace k V) :
    K ∈ 𝒜 ↔ K.comap ((AffineEquiv.refl k V : V ≃ᵃ[k] V) : V →ᵃ[k] V) ∈ 𝒟 := by
  simp [h, AffineSubspace.comap_id]

/-- At `R = B`, the realization map preserves the bigrading all the same. Here `T.C.obj A` has two
`B`-algebra structures, see `Cohomology/Axioms`, and this tests that the statement mixes them
correctly. -/
theorem isHomogeneousOfShift_realization_self {ℬ' : ℤ → Submodule B B} [GradedAlgebra ℬ']
    (T : OrdinaryTheory.{u, w, w, z} k ℬ') (𝒜 : Arrangement k V) :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ') (T.grading (complement 𝒜)) 0 (T.realization 𝒜) :=
  T.isHomogeneousOfShift_realization

end Degenerate

end OrlikSolomon.RealizationExamples
