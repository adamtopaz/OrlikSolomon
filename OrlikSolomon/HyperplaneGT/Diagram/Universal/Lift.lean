/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Support

/-!
# The linear universal property of the hyperplane module

A compatible family of linear maps on the chosen finite stages extends uniquely to the
literal free module on all hyperplanes. For each hyperplane, cofinality supplies a stage
containing it. Evaluation on its basis vector is independent of this choice by passing to
a common upper stage; Mathlib's free-module linear extension then gives the universal map.

Blueprint: the explicit direct-limit universal property in U01 (`lem:u01`).
-/

@[expose] public section

noncomputable section

universe u v w z

namespace OrlikSolomon.HyperplaneGT.CofinalSystem

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n)
variable {N : Type z} [AddCommMonoid N] [Module R N]
variable (f : ∀ 𝒜 : C.Stage, (𝒜.val.val →₀ R) →ₗ[R] N)
variable (hf : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
  (f ℬ).comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) = f 𝒜)

include hf in
private theorem compatible_single_eq (𝒜 ℬ : C.Stage) (H : 𝒜.val.val) (K : ℬ.val.val)
    (hHK : arrangementHyperplane 𝒜.val.val H = arrangementHyperplane ℬ.val.val K) (r : R) :
    f 𝒜 (Finsupp.single H r) = f ℬ (Finsupp.single K r) := by
  obtain ⟨𝒟, h𝒜, hℬ⟩ := exists_ge_ge 𝒜 ℬ
  have ha := DFunLike.congr_fun (hf 𝒜 𝒟 h𝒜) (Finsupp.single H r)
  have hb := DFunLike.congr_fun (hf ℬ 𝒟 hℬ) (Finsupp.single K r)
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at ha hb
  have heq : Arrangement.inclusion h𝒜 H = Arrangement.inclusion hℬ K :=
    Subtype.ext (congrArg (fun X : Hyperplane k n ↦ X.val) hHK)
  exact ha.symm.trans ((congrArg (fun L ↦ f 𝒟 (Finsupp.single L r)) heq).trans hb)

/-- The unique linear extension of a compatible family on the chosen cofinal stages.
The formula chooses a stage for each basis label; compatibility makes this choice irrelevant.

Blueprint: U01 (`lem:u01`). -/
def universalLift (_hf : ∀ (𝒜 ℬ : C.Stage) (h : 𝒜 ≤ ℬ),
    (f ℬ).comp (Finsupp.lmapDomain R R (Arrangement.inclusion h)) = f 𝒜) :
    (Hyperplane k n →₀ R) →ₗ[R] N := by
  classical
  exact Finsupp.linearCombination R fun H ↦
    let h := C.exists_stage_containing {H}
    let 𝒜 := h.choose
    f 𝒜 (Finsupp.single ⟨H.val, h.choose_spec H (by simp)⟩ 1)

/-- The extension agrees with the supplied family on every finite-stage basis vector. -/
theorem universalLift_single (𝒜 : C.Stage) (H : 𝒜.val.val) (r : R) :
    C.universalLift R f hf (Finsupp.single (arrangementHyperplane 𝒜.val.val H) r) =
      f 𝒜 (Finsupp.single H r) := by
  classical
  let h := C.exists_stage_containing {arrangementHyperplane 𝒜.val.val H}
  let ℬ := h.choose
  let K : ℬ.val.val := ⟨H.val,
    h.choose_spec (arrangementHyperplane 𝒜.val.val H) (Finset.mem_singleton_self _)⟩
  have hKH : arrangementHyperplane ℬ.val.val K = arrangementHyperplane 𝒜.val.val H :=
    Subtype.ext rfl
  rw [universalLift, Finsupp.linearCombination_single]
  change r • f ℬ (Finsupp.single K 1) = f 𝒜 (Finsupp.single H r)
  rw [← map_smul, Finsupp.smul_single_one]
  exact compatible_single_eq R C f hf ℬ 𝒜 K H hKH r

/-- The universal extension restricts to the original linear map at every selected stage. -/
theorem universalLift_comp_finiteStageMap (𝒜 : C.Stage) :
    (C.universalLift R f hf).comp (finiteStageMap R 𝒜.val.val) = f 𝒜 := by
  apply Finsupp.lhom_ext
  intro H r
  simpa only [LinearMap.comp_apply, finiteStageMap_single] using
    C.universalLift_single R f hf 𝒜 H r

omit f hf in
/-- Linear maps on the universal module agree when their finite-stage restrictions agree. -/
theorem linearMap_ext {l m : (Hyperplane k n →₀ R) →ₗ[R] N}
    (h : ∀ 𝒜 : C.Stage,
      l.comp (finiteStageMap R 𝒜.val.val) = m.comp (finiteStageMap R 𝒜.val.val)) : l = m := by
  apply LinearMap.ext
  intro x
  obtain ⟨𝒜, a, rfl⟩ := C.exists_stage_vector R x
  exact DFunLike.congr_fun (h 𝒜) a

/-- Compatibility characterizes the universal extension uniquely.

Blueprint: U01 (`lem:u01`). -/
theorem universalLift_unique (l : (Hyperplane k n →₀ R) →ₗ[R] N) :
    (∀ 𝒜 : C.Stage, l.comp (finiteStageMap R 𝒜.val.val) = f 𝒜) ↔
      l = C.universalLift R f hf := by
  constructor
  · intro hl
    apply C.linearMap_ext R
    intro 𝒜
    rw [universalLift_comp_finiteStageMap, hl]
  · rintro rfl
    exact C.universalLift_comp_finiteStageMap R f hf

end OrlikSolomon.HyperplaneGT.CofinalSystem
