/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Finsupp.Span
public import OrlikSolomon.HyperplaneGT.Algebra.Dual.DiagramAction
public import OrlikSolomon.HyperplaneGT.Reconstruction.Projections.Recognition

/-!
# Invariant coordinate spans and their actual dual restrictions

The existing common-target marking squares preserve each actual marking plane. Coordinate
span recognition then preserves every supported coordinate submodule. Restricting the
universal equivalence to that submodule induces the contragredient action on its full dual,
with the actual restriction square. No projection naturality or dual exactness is assumed.

Blueprint: P02 (`prop:p02`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {S : Set k₀}

/-- The actual universal plane on the two ordered fibers of a tagged marking. The same
definition applies to coordinate translates and to ordered differences. -/
def Marking.plane (R : Type w) [Semiring R] (w : Marking S n) :
    Submodule R (Hyperplane k n →₀ R) :=
  Submodule.span R {Finsupp.single (w.fiber (k := k) 0) (1 : R),
    Finsupp.single (w.fiber (k := k) 1) 1}

variable {R : Type w} [CommRing R] {C : CofinalSystem k₀ k n}

/-- An available marking's actual universal plane is the range of its existing finite-stage
arrow followed by extension by zero. -/
theorem Marking.plane_eq_range (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) :
    w.plane R = LinearMap.range ((finiteStageMap R 𝒜).comp (w.basisMap R hw)) := by
  rw [finiteStageMap, Marking.basisMap, ← Finsupp.lmapDomain_comp, Finsupp.range_lmapDomain]
  apply congrArg (Submodule.span R)
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · refine ⟨0, ?_⟩
      congr 1
    · refine ⟨1, ?_⟩
      congr 1
  · rintro ⟨a, rfl⟩
    fin_cases a
    · apply Or.inl
      congr 1
    · apply Or.inr
      congr 1

/-- The common-target marking square preserves each actual universal marking plane by
equality, with no hypothesis on the set of marking constants. -/
theorem DiagramAut.map_markingPlane (g : DiagramAut R C S) (w : Marking S n) :
    (w.plane R).map g.universalEquiv.toLinearMap = w.plane R := by
  obtain ⟨𝒜, hw⟩ := C.exists_stage_marking w
  rw [w.plane_eq_range hw, ← LinearMap.range_comp, g.universalEquiv_marking 𝒜 w hw,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr g.targetEquiv.surjective)]

/-- The coordinate plane is the actual plane of the tagged zero translate. Only the
availability of the constant zero in the marking set is required. -/
theorem coordinatePlane_eq_markingPlane (hS : (0 : k₀) ∈ S) (i : Fin n) :
    coordinatePlane (k := k) R i =
      (Marking.coordinate i (⟨0, hS⟩ : S)).plane (k := k) R := by
  have hf (t : k₀) : (Marking.coordinate i (⟨0, hS⟩ : S)).fiber (k := k) t =
      coordinateHyperplane i (algebraMap k₀ k t) := by
    apply Subtype.ext
    ext x
    simp
  simp only [coordinatePlane, Marking.plane, hf, map_zero, map_one]

/-- The tagged zero-coordinate marking makes each coordinate plane invariant. -/
theorem DiagramAut.map_coordinatePlane (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (i : Fin n) :
    (coordinatePlane (k := k) R i).map g.universalEquiv.toLinearMap = coordinatePlane R i := by
  rw [coordinatePlane_eq_markingPlane hS]
  exact g.map_markingPlane _

private theorem dualAction_inv_apply (g : DiagramAut R C S)
    (φ : Module.Dual R (Hyperplane k n →₀ R)) (x : Hyperplane k n →₀ R) :
    DiagramAut.dualAction g⁻¹ φ x = φ (g.universalEquiv x) := by
  rw [DiagramAut.dualAction_apply, ← g.universalEquiv_symm, LinearEquiv.symm_symm]

private theorem map_verticalModule_insert_le (g : DiagramAut R C S)
    (z : Finset (Fin n)) (i : Fin n) (hi : i ∉ z)
    (hz : (verticalModule (k := k) R z).map g.universalEquiv.toLinearMap = verticalModule R z)
    (hp : (coordinatePlane (k := k) R i).map g.universalEquiv.toLinearMap = coordinatePlane R i) :
    (verticalModule R (insert i z)).map g.universalEquiv.toLinearMap ≤
      verticalModule R (insert i z) := by
  rintro _ ⟨a, ha, rfl⟩
  apply (coordinateSpan_recognition R z i hi (g.universalEquiv a)).mpr
  intro b hb φ ψ hφ hψ hc
  have hb' : g.universalEquiv.symm b ∈ coordinatePlane R i := by
    rw [← hp] at hb
    obtain ⟨b', hb', heq⟩ := hb
    rw [← heq]
    change g.universalEquiv.symm (g.universalEquiv b') ∈ coordinatePlane R i
    rw [LinearEquiv.symm_apply_apply]
    exact hb'
  have hAnn (χ : Module.Dual R (Hyperplane k n →₀ R))
      (hχ : χ ∈ (verticalModule R z).dualAnnihilator) :
      DiagramAut.dualAction g⁻¹ χ ∈ (verticalModule R z).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    rw [dualAction_inv_apply]
    apply (Submodule.mem_dualAnnihilator χ).mp hχ
    rw [← hz]
    exact ⟨x, hx, rfl⟩
  have hc' := (DiagramAut.commutes_dualAction_iff g⁻¹ φ ψ).mpr hc
  have hdet := (coordinateSpan_recognition R z i hi a).mp ha
    (g.universalEquiv.symm b) hb' _ _ (hAnn φ hφ) (hAnn ψ hψ) hc'
  simpa only [dualDeterminant_ιMulti_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    dualAction_inv_apply, LinearEquiv.apply_symm_apply] using hdet

/-- Every actual quadratic diagram automorphism preserves each literal supported coordinate
span. Only the zero marking constant is used, with no generation or field-extension condition.
Blueprint: P02 (`prop:p02`). -/
theorem DiagramAut.map_verticalModule (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) :
    (verticalModule (k := k) R z).map g.universalEquiv.toLinearMap = verticalModule R z := by
  suffices ∀ g : DiagramAut R C S,
      (verticalModule (k := k) R z).map g.universalEquiv.toLinearMap = verticalModule R z from
    this g
  induction z using Finset.induction_on with
  | empty =>
    intro g
    rw [verticalModule_empty, Submodule.map_bot]
  | @insert i z hi ih =>
    have hle (g : DiagramAut R C S) := map_verticalModule_insert_le g z i hi
      (ih g) (g.map_coordinatePlane hS i)
    intro g
    apply le_antisymm (hle g)
    intro a ha
    refine ⟨(g⁻¹).universalEquiv a, hle g⁻¹ ⟨a, ha, rfl⟩, ?_⟩
    rw [← g.universalEquiv_symm]
    exact g.universalEquiv.apply_symm_apply a

/-- The contragredient action preserves the actual evaluation annihilator of each coordinate
span by equality. Blueprint: P02 (`prop:p02`). -/
theorem DiagramAut.map_verticalAnnihilator (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) :
    ((verticalModule (k := k) R z).dualAnnihilator).map
        (DiagramAut.dualAction g).toLinearMap = (verticalModule R z).dualAnnihilator := by
  have hmem (g : DiagramAut R C S) (φ : Module.Dual R (Hyperplane k n →₀ R))
      (hφ : φ ∈ (verticalModule R z).dualAnnihilator) :
      DiagramAut.dualAction g φ ∈ (verticalModule R z).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    rw [DiagramAut.dualAction_apply, g.universalEquiv_symm]
    apply (Submodule.mem_dualAnnihilator φ).mp hφ
    rw [← (g⁻¹).map_verticalModule hS z]
    exact ⟨x, hx, rfl⟩
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact hmem g ψ hψ
  · intro hφ
    refine ⟨DiagramAut.dualAction g⁻¹ φ, hmem g⁻¹ φ hφ, ?_⟩
    simp

namespace DiagramAut

/-- The universal equivalence restricted to the actual invariant supported coordinate module.
Blueprint: the induced primal equivalence in P02 (`prop:p02`). -/
def verticalEquiv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) : verticalModule (k := k) R z ≃ₗ[R] verticalModule (k := k) R z :=
  g.universalEquiv.ofSubmodules _ _ (g.map_verticalModule hS z)

/-- The restricted equivalence acts on the same underlying universal vector. -/
@[simp]
theorem coe_verticalEquiv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) (x : verticalModule (k := k) R z) :
    (g.verticalEquiv hS z x : Hyperplane k n →₀ R) = g.universalEquiv x.val :=
  LinearEquiv.ofSubmodules_apply g.universalEquiv (g.map_verticalModule hS z) x

/-- The inverse restricted equivalence is the actual inverse universal action on vectors. -/
@[simp]
theorem coe_verticalEquiv_symm (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) (x : verticalModule (k := k) R z) :
    ((g.verticalEquiv hS z).symm x : Hyperplane k n →₀ R) = g.universalEquiv.symm x.val :=
  LinearEquiv.ofSubmodules_symm_apply g.universalEquiv (g.map_verticalModule hS z) x

/-- Diagram automorphisms act on every actual supported coordinate module. -/
def verticalAction (hS : (0 : k₀) ∈ S) (z : Finset (Fin n)) :
    DiagramAut R C S →* (verticalModule (k := k) R z ≃ₗ[R] verticalModule (k := k) R z) where
  toFun g := g.verticalEquiv hS z
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [coe_verticalEquiv, universalEquiv_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp only [mul_apply_eq_comp, coe_verticalEquiv, universalEquiv_mul]

/-- Evaluation of the supported-coordinate action is its restricted equivalence. -/
@[simp]
theorem verticalAction_apply (hS : (0 : k₀) ∈ S) (z : Finset (Fin n))
    (g : DiagramAut R C S) : verticalAction hS z g = g.verticalEquiv hS z := rfl

/-- The identity diagram acts identically on the supported coordinate module. -/
@[simp]
theorem verticalEquiv_one (hS : (0 : k₀) ∈ S) (z : Finset (Fin n)) :
    (1 : DiagramAut R C S).verticalEquiv hS z = 1 :=
  (verticalAction hS z).map_one

/-- Restricted coordinate equivalences compose in the diagram group's order. -/
theorem verticalEquiv_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) :
    (g * h).verticalEquiv hS z = g.verticalEquiv hS z * h.verticalEquiv hS z :=
  (verticalAction hS z).map_mul g h

/-- Inversion retains the standard inverse-equivalence cancellation normal form. -/
@[simp]
theorem verticalEquiv_inv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) : (g⁻¹).verticalEquiv hS z = (g.verticalEquiv hS z).symm :=
  map_inv (verticalAction hS z) g

/-- Inverse precomposition through the actual restricted universal equivalence acts on the
full vertical dual. Blueprint: the induced dual equivalence in P02 (`prop:p02`). -/
def verticalDualEquiv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) :
    Module.Dual R (verticalModule (k := k) R z) ≃ₗ[R] Module.Dual R (verticalModule (k := k) R z) :=
  OrlikSolomon.HyperplaneGT.dualAction (g.verticalEquiv hS z)

/-- The induced vertical dual action is explicitly inverse precomposition. -/
theorem verticalDualEquiv_apply (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) (ψ : Module.Dual R (verticalModule (k := k) R z))
    (x : verticalModule (k := k) R z) :
    g.verticalDualEquiv hS z ψ x = ψ ((g.verticalEquiv hS z).symm x) := rfl

/-- The actual diagram group acts contragrediently on the full vertical dual. -/
def verticalDualAction (hS : (0 : k₀) ∈ S) (z : Finset (Fin n)) :
    DiagramAut R C S →*
      (Module.Dual R (verticalModule (k := k) R z) ≃ₗ[R]
        Module.Dual R (verticalModule (k := k) R z)) :=
  OrlikSolomon.HyperplaneGT.dualAction.comp (verticalAction hS z)

/-- Evaluation of the vertical dual action is its induced equivalence. -/
@[simp]
theorem verticalDualAction_apply (hS : (0 : k₀) ∈ S) (z : Finset (Fin n))
    (g : DiagramAut R C S) : verticalDualAction hS z g = g.verticalDualEquiv hS z := rfl

/-- The identity diagram fixes the entire vertical dual. -/
@[simp]
theorem verticalDualEquiv_one (hS : (0 : k₀) ∈ S) (z : Finset (Fin n)) :
    (1 : DiagramAut R C S).verticalDualEquiv hS z = 1 :=
  (verticalDualAction hS z).map_one

/-- The induced dual equivalences form a left action, using inverse precomposition. -/
theorem verticalDualEquiv_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) :
    (g * h).verticalDualEquiv hS z = g.verticalDualEquiv hS z * h.verticalDualEquiv hS z :=
  (verticalDualAction hS z).map_mul g h

/-- The induced inverse dual action has the standard cancellation normal form. -/
@[simp]
theorem verticalDualEquiv_inv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (z : Finset (Fin n)) : (g⁻¹).verticalDualEquiv hS z = (g.verticalDualEquiv hS z).symm :=
  map_inv (verticalDualAction hS z) g

/-- The actual full-dual restriction commutes with the induced contragredient action.
It is proved by evaluation on the same supported vectors, with no dual exactness assertion.
Blueprint: the equivariance square of P02 (`prop:p02`). -/
theorem verticalRestriction_dualAction (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (z : Finset (Fin n)) :
    (verticalRestriction (k := k) R z).comp (DiagramAut.dualAction g).toLinearMap =
      (g.verticalDualEquiv hS z).toLinearMap.comp (verticalRestriction R z) := by
  apply LinearMap.ext
  intro φ
  ext x
  change DiagramAut.dualAction g φ x.val =
    g.verticalDualEquiv hS z (verticalRestriction R z φ) x
  rw [DiagramAut.dualAction_apply, verticalDualEquiv_apply, verticalRestriction_apply,
    coe_verticalEquiv_symm]

end DiagramAut

end OrlikSolomon.HyperplaneGT
