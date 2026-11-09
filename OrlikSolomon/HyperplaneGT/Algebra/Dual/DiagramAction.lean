/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Configurations
public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Automorphisms

/-!
# The contragredient diagram action and universal centralizers

The actual marked quadratic diagram automorphisms act on the full dual of the literal
universal free module by inverse precomposition. This is the composite of the universal
action homomorphism with the generic contragredient homomorphism. The universal action
preserves the actual global quadratic relation span by equality, so paired dual actions
preserve commuting in both directions and carry each centralizer onto the corresponding
centralizer. No additional relation module or diagram data is introduced.

Blueprint: the paired-action assertion in U04 (`lem:u04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DiagramAut

universe u v w

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable {R : Type w} [CommRing R] {C : CofinalSystem k₀ k n} {S : Set k₀}

/-- The actual diagram group acts contragrediently on the full universal dual.
Blueprint: U04 (`lem:u04`), using U02–U03. -/
def dualAction : DiagramAut R C S →*
    (Module.Dual R (Hyperplane k n →₀ R) ≃ₗ[R] Module.Dual R (Hyperplane k n →₀ R)) :=
  OrlikSolomon.HyperplaneGT.dualAction.comp universalAction

/-- The contragredient diagram action evaluates by inverse precomposition. -/
theorem dualAction_apply (g : DiagramAut R C S)
    (φ : Module.Dual R (Hyperplane k n →₀ R)) (m : Hyperplane k n →₀ R) :
    dualAction g φ m = φ (g.universalEquiv.symm m) := rfl

/-- Simultaneous universal and dual actions preserve evaluation. -/
theorem dualAction_apply_universalEquiv (g : DiagramAut R C S)
    (φ : Module.Dual R (Hyperplane k n →₀ R)) (m : Hyperplane k n →₀ R) :
    dualAction g φ (g.universalEquiv m) = φ m :=
  OrlikSolomon.HyperplaneGT.dualAction_apply_apply g.universalEquiv φ m

/-- The actual paired diagram action preserves commuting in both directions.
The relation-image equality is supplied by the diagram's universal action.
Blueprint: U04 (`lem:u04`). -/
theorem commutes_dualAction_iff (g : DiagramAut R C S)
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) :
    Commutes (universalQuadraticRelationSpan R) (dualAction g φ) (dualAction g ψ) ↔
      Commutes (universalQuadraticRelationSpan R) φ ψ :=
  OrlikSolomon.HyperplaneGT.commutes_dualAction_iff
    (universalQuadraticRelationSpan R) g.universalEquiv g.map_universalQuadraticRelationSpan φ ψ

/-- Paired diagram action preserves universal-centralizer membership in both directions.
Blueprint: U04 (`lem:u04`). -/
theorem mem_centralizer_dualAction_iff (g : DiagramAut R C S)
    (φ ψ : Module.Dual R (Hyperplane k n →₀ R)) :
    dualAction g ψ ∈ centralizer (universalQuadraticRelationSpan R) (dualAction g φ) ↔
      ψ ∈ centralizer (universalQuadraticRelationSpan R) φ := by
  rw [mem_centralizer_iff, mem_centralizer_iff, commutes_dualAction_iff]

/-- The actual contragredient equivalence carries a universal centralizer onto the
centralizer of the transformed functional, as an equality of submodules.
Blueprint: U04 (`lem:u04`). -/
theorem map_centralizer_dualAction (g : DiagramAut R C S)
    (φ : Module.Dual R (Hyperplane k n →₀ R)) :
    (centralizer (universalQuadraticRelationSpan R) φ).map (dualAction g).toLinearMap =
      centralizer (universalQuadraticRelationSpan R) (dualAction g φ) := by
  ext ψ
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact (mem_centralizer_dualAction_iff g φ χ).mpr hχ
  · intro hψ
    refine ⟨(dualAction g).symm ψ, ?_, (dualAction g).apply_symm_apply ψ⟩
    apply (mem_centralizer_dualAction_iff g φ ((dualAction g).symm ψ)).mp
    simpa only [LinearEquiv.apply_symm_apply] using hψ

end OrlikSolomon.HyperplaneGT.DiagramAut
