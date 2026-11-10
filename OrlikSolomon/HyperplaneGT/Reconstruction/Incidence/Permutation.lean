/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Inertia

/-!
# The recovered hyperplane permutation and its dual unit cocycle

Unique unit-delta recognition constructs the hyperplane permutation from the actual
contragredient action. Applying recognition to inverse diagrams supplies its inverse;
recognition of products supplies the action law and the dual-unit cocycle. Evaluation
against the transformed coordinate deltas determines the primal generator formula with
the inverse unit and the same label permutation. Actual inertia, decomposition and
primal generator lines are preserved by equality.

Blueprint: I01 (`prop:i01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DiagramAut

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {R : Type w} [CommRing R] [IsLocalRing R]
  {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The uniquely recovered label and unit of a transformed delta, before packaging the
labels as a permutation. The public permutation and unit projections hide this choice. -/
def inertiaImage (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) : Hyperplane k n × Rˣ :=
  Classical.choose (g.exists_unit_delta_dualAction hS hn H).exists

private theorem inertiaImage_spec (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    dualAction g (Finsupp.lapply H) =
      ((inertiaImage g hS hn H).2 : R) • Finsupp.lapply (inertiaImage g hS hn H).1 :=
  Classical.choose_spec (g.exists_unit_delta_dualAction hS hn H).exists

private theorem inertiaImage_eq_of (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) (p : Hyperplane k n × Rˣ)
    (hp : dualAction g (Finsupp.lapply H) = (p.2 : R) • Finsupp.lapply p.1) :
    p = inertiaImage g hS hn H :=
  (g.exists_unit_delta_dualAction hS hn H).unique hp (inertiaImage_spec g hS hn H)

private theorem inertiaImage_one (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) :
    inertiaImage (1 : DiagramAut R C S) hS hn H = (H, 1) := by
  apply (inertiaImage_eq_of 1 hS hn H (H, 1) ?_).symm
  simp

private theorem inertiaImage_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    inertiaImage (g * h) hS hn H =
      ((inertiaImage g hS hn (inertiaImage h hS hn H).1).1,
        (inertiaImage g hS hn (inertiaImage h hS hn H).1).2 * (inertiaImage h hS hn H).2) := by
  apply (inertiaImage_eq_of (g * h) hS hn H _ ?_).symm
  rw [map_mul, mul_apply_eq_comp, inertiaImage_spec h hS hn H, map_smul,
    inertiaImage_spec g hS hn (inertiaImage h hS hn H).1, smul_smul]
  simp only [Units.val_mul, mul_comm]

/-- The uniquely recovered permutation of actual hyperplanes. Its inverse is obtained from
recognition for the inverse diagram, not an assumed monomial action. Blueprint: I01 (`prop:i01`).
-/
def hyperplanePerm (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    Equiv.Perm (Hyperplane k n) where
  toFun H := (inertiaImage g hS hn H).1
  invFun H := (inertiaImage g⁻¹ hS hn H).1
  left_inv H := by
    have he := congrArg Prod.fst (inertiaImage_mul g⁻¹ g hS hn H)
    simpa only [inv_mul_cancel, inertiaImage_one] using he.symm
  right_inv H := by
    have he := congrArg Prod.fst (inertiaImage_mul g g⁻¹ hS hn H)
    simpa only [mul_inv_cancel, inertiaImage_one] using he.symm

/-- The unit multiplying the transformed dual delta. The corresponding primal unit is its
inverse. Blueprint: the unit-delta construction in I01 (`prop:i01`). -/
def hyperplaneUnit (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) : Rˣ :=
  (inertiaImage g hS hn H).2

/-- The actual contragredient image is the dual unit times the recovered coordinate delta.
Blueprint: I01 (`prop:i01`). -/
theorem dualAction_delta (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    dualAction g (Finsupp.lapply H) =
      (g.hyperplaneUnit hS hn H : R) • Finsupp.lapply (g.hyperplanePerm hS hn H) :=
  inertiaImage_spec g hS hn H

/-- The identity diagram induces the identity label permutation. -/
@[simp]
theorem hyperplanePerm_one (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (1 : DiagramAut R C S).hyperplanePerm hS hn = 1 := by
  ext H
  change (inertiaImage (1 : DiagramAut R C S) hS hn H).1 = H
  rw [inertiaImage_one]

/-- The label permutation respects diagram composition in the same covariant order. -/
theorem hyperplanePerm_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (g * h).hyperplanePerm hS hn = g.hyperplanePerm hS hn * h.hyperplanePerm hS hn := by
  ext H
  have he := congrArg Prod.fst (inertiaImage_mul g h hS hn H)
  exact he

/-- Composition acts on labels by ordinary function composition. -/
@[simp]
theorem hyperplanePerm_mul_apply (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    (g * h).hyperplanePerm hS hn H = g.hyperplanePerm hS hn (h.hyperplanePerm hS hn H) := by
  rw [hyperplanePerm_mul]
  rfl

/-- The recovered hyperplane permutations form a group action. Blueprint: I01 (`prop:i01`). -/
def hyperplaneAction (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    DiagramAut R C S →* Equiv.Perm (Hyperplane k n) where
  toFun g := g.hyperplanePerm hS hn
  map_one' := hyperplanePerm_one hS hn
  map_mul' g h := hyperplanePerm_mul g h hS hn

/-- Evaluation of the permutation action is the recovered permutation. -/
@[simp]
theorem hyperplaneAction_apply (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    hyperplaneAction hS hn g = g.hyperplanePerm hS hn := rfl

/-- Inverse diagrams give inverse permutations, in the standard cancellation normal form. -/
@[simp]
theorem hyperplanePerm_inv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (g⁻¹).hyperplanePerm hS hn = (g.hyperplanePerm hS hn).symm :=
  map_inv (hyperplaneAction hS hn) g

/-- Applying a permutation and then the inverse diagram's permutation cancels. -/
theorem hyperplanePerm_inv_apply_apply (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    (g⁻¹).hyperplanePerm hS hn (g.hyperplanePerm hS hn H) = H := by simp

/-- Applying the inverse diagram's permutation and then the original cancels. -/
theorem hyperplanePerm_apply_inv_apply (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hn : 2 ≤ n) (H : Hyperplane k n) :
    g.hyperplanePerm hS hn ((g⁻¹).hyperplanePerm hS hn H) = H := by simp

/-- The identity diagram has dual unit one at every label. -/
@[simp]
theorem hyperplaneUnit_one (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) :
    (1 : DiagramAut R C S).hyperplaneUnit hS hn H = 1 :=
  congrArg Prod.snd (inertiaImage_one hS hn H)

/-- The dual units satisfy the cocycle law associated with the recovered label action. -/
theorem hyperplaneUnit_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (g * h).hyperplaneUnit hS hn H =
      g.hyperplaneUnit hS hn (h.hyperplanePerm hS hn H) * h.hyperplaneUnit hS hn H :=
  congrArg Prod.snd (inertiaImage_mul g h hS hn H)

/-- The inverse dual unit at the transported label cancels the original dual unit. -/
@[simp]
theorem hyperplaneUnit_inv_apply (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (g⁻¹).hyperplaneUnit hS hn (g.hyperplanePerm hS hn H) =
      (g.hyperplaneUnit hS hn H)⁻¹ := by
  have he := hyperplaneUnit_mul g⁻¹ g hS hn H
  rw [inv_mul_cancel, hyperplaneUnit_one] at he
  exact mul_eq_one_iff_eq_inv.mp he.symm

/-- The recovered pair is exactly the public permutation and dual-unit projections. -/
@[simp]
theorem inertiaImage_eq (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    g.inertiaImage hS hn H = (g.hyperplanePerm hS hn H, g.hyperplaneUnit hS hn H) := rfl

/-- Each actual inertia line is carried onto the recovered inertia line.
Blueprint: the inertia equality of I01 (`prop:i01`). -/
theorem map_inertia (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (inertia R H).map (dualAction g).toLinearMap = inertia R (g.hyperplanePerm hS hn H) := by
  rw [inertia, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_toLinearMap,
    g.dualAction_delta hS hn H]
  exact Submodule.span_singleton_smul_eq (g.hyperplaneUnit hS hn H).isUnit _

/-- Each actual decomposition submodule is carried onto the recovered decomposition
submodule, by the equality of centralizers. Blueprint: I01 (`prop:i01`). -/
theorem map_decomposition (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (decomposition R H).map (dualAction g).toLinearMap =
      decomposition R (g.hyperplanePerm hS hn H) := by
  have he := g.map_centralizer_dualAction (Finsupp.lapply H)
  have hδ : centralizer (universalQuadraticRelationSpan R)
      (Finsupp.lapply H : Module.Dual R (Hyperplane k n →₀ R)) = decomposition R H := by
    simpa using centralizer_unit_smul_delta R H 1
  rw [hδ, g.dualAction_delta hS hn H, centralizer_unit_smul_delta] at he
  exact he

/-- The actual primal generator has the same recovered label as the dual delta and the
inverse dual unit. Evaluation invariance determines every coefficient, without assuming
monomiality. Blueprint: the generator-line clause of I01 (`prop:i01`). -/
theorem universalEquiv_single (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    g.universalEquiv (Finsupp.single H 1) =
      (((g.hyperplaneUnit hS hn H)⁻¹ : Rˣ) : R) •
        Finsupp.single (g.hyperplanePerm hS hn H) 1 := by
  classical
  ext J
  obtain ⟨K, rfl⟩ := (g.hyperplanePerm hS hn).surjective J
  have he := g.dualAction_apply_universalEquiv (Finsupp.lapply K) (Finsupp.single H 1)
  rw [g.dualAction_delta hS hn K] at he
  simp only [LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul] at he
  have hv := congrArg (fun r : R ↦ (((g.hyperplaneUnit hS hn K)⁻¹ : Rˣ) : R) * r) he
  rw [Units.inv_mul_cancel_left] at hv
  by_cases hKH : K = H
  · subst K
    simpa using hv
  · have hp : g.hyperplanePerm hS hn H ≠ g.hyperplanePerm hS hn K :=
      fun h ↦ hKH ((g.hyperplanePerm hS hn).injective h).symm
    simpa [hKH, Ne.symm hKH, hp] using hv

/-- The primal generator line is carried onto the line with the same recovered label.
Blueprint: I01 (`prop:i01`). -/
theorem map_generatorLine (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (H : Hyperplane k n) :
    (Submodule.span R {Finsupp.single H (1 : R)}).map g.universalEquiv.toLinearMap =
      Submodule.span R {Finsupp.single (g.hyperplanePerm hS hn H) 1} := by
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_toLinearMap,
    g.universalEquiv_single hS hn H]
  exact Submodule.span_singleton_smul_eq (g.hyperplaneUnit hS hn H)⁻¹.isUnit _

/-- The inertia-image equalities uniquely determine the recovered label permutation.
Blueprint: uniqueness in I01 (`prop:i01`). -/
theorem hyperplanePerm_unique (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (π : Equiv.Perm (Hyperplane k n))
    (hπ : ∀ H, (inertia R H).map (dualAction g).toLinearMap = inertia R (π H)) :
    π = g.hyperplanePerm hS hn := by
  ext H
  exact inertia_injective ((hπ H).symm.trans (g.map_inertia hS hn H))

end OrlikSolomon.HyperplaneGT.DiagramAut
