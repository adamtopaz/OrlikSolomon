/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.Dual.Coordinates
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# Determinant functionals and relation centralizers

Two functionals determine an alternating determinant, hence a functional on the exterior
square. Fixing the first functional makes this construction linear in the second. The
functionals commuting with the first relative to any explicit relation submodule form a
submodule, using Mathlib's dual annihilator. Paired contragredient actions preserve this
relation when the exterior-square action preserves the relation submodule by equality.

These are the generic prerequisites of `def:u04` and `lem:u04`; the specific hyperplane
relation generators and diagram automorphisms are not defined in this file.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v w

variable {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The determinant pairing, linear in its second functional. This is a partial evaluation of
Mathlib's alternating dual pairing, with no assumption on the size or freeness of the module. -/
def dualDeterminantLinear (φ : Module.Dual R M) :
    Module.Dual R M →ₗ[R] Module.Dual R (⋀[R]^2 M) :=
  (exteriorPower.alternatingMapToDual R M 2).toMultilinearMap.toLinearMap ![φ, 0] 1

/-- The alternating determinant of two functionals, lifted to the exterior square.
Blueprint: generic determinant in `def:u04`. -/
def dualDeterminant (φ ψ : Module.Dual R M) : Module.Dual R (⋀[R]^2 M) :=
  dualDeterminantLinear φ ψ

@[simp]
theorem dualDeterminantLinear_apply (φ ψ : Module.Dual R M) :
    dualDeterminantLinear φ ψ = dualDeterminant φ ψ := rfl

private theorem dualDeterminant_eq_alternatingMapToDual (φ ψ : Module.Dual R M) :
    dualDeterminant φ ψ = exteriorPower.alternatingMapToDual R M 2 ![φ, ψ] := by
  change exteriorPower.alternatingMapToDual R M 2 (Function.update ![φ, 0] 1 ψ) = _
  congr 1
  ext i
  fin_cases i <;> simp

/-- The determinant formula on an arbitrary two-vector exterior product.
Blueprint: the exterior lift in `def:u04`. -/
@[simp]
theorem dualDeterminant_ιMulti_apply (φ ψ : Module.Dual R M) (v : Fin 2 → M) :
    dualDeterminant φ ψ (exteriorPower.ιMulti R 2 v) =
      φ (v 0) * ψ (v 1) - φ (v 1) * ψ (v 0) := by
  rw [dualDeterminant_eq_alternatingMapToDual,
    exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two]
  simp [mul_comm]

/-- The alternating determinant vanishes on a repeated vector, including in characteristic two.
Blueprint: `def:u04`. -/
theorem dualDeterminant_ιMulti_self (φ ψ : Module.Dual R M) (a : M) :
    dualDeterminant φ ψ (exteriorPower.ιMulti R 2 ![a, a]) = 0 := by simp

/-- Swapping the two functionals negates their determinant. -/
theorem dualDeterminant_swap (φ ψ : Module.Dual R M) :
    dualDeterminant ψ φ = -dualDeterminant φ ψ := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, dualDeterminant_ιMulti_apply,
    LinearMap.neg_apply]
  ring

/-- A relation submodule is annihilated by the determinant of two commuting functionals.
The relation submodule is an explicit argument, not additional diagram data.
Blueprint: the relation in `def:u04`. -/
def Commutes (Q : Submodule R (⋀[R]^2 M)) (φ ψ : Module.Dual R M) : Prop :=
  Q ≤ LinearMap.ker (dualDeterminant φ ψ)

/-- Functionals commuting with a fixed functional form a submodule, obtained by pulling back
the dual annihilator of the relations. Blueprint: generic centralizer in `def:u04`, `lem:u04`. -/
def centralizer (Q : Submodule R (⋀[R]^2 M)) (φ : Module.Dual R M) :
    Submodule R (Module.Dual R M) := Q.dualAnnihilator.comap (dualDeterminantLinear φ)

@[simp]
theorem mem_centralizer_iff (Q : Submodule R (⋀[R]^2 M)) (φ ψ : Module.Dual R M) :
    ψ ∈ centralizer Q φ ↔ Commutes Q φ ψ := by
  simp only [centralizer, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    dualDeterminantLinear_apply, Commutes, IsConcreteLE.le_iff, LinearMap.mem_ker]

/-- Commuting is symmetric. -/
theorem commutes_comm (Q : Submodule R (⋀[R]^2 M)) (φ ψ : Module.Dual R M) :
    Commutes Q φ ψ ↔ Commutes Q ψ φ := by
  simp only [Commutes, dualDeterminant_swap ψ φ, IsConcreteLE.le_iff, LinearMap.mem_ker,
    LinearMap.neg_apply, neg_eq_zero]

/-- The paired contragredient action is compatible with the inverse exterior-square map.
Blueprint: the generic paired identity in `lem:u04`. -/
theorem dualDeterminant_dualAction (g : M ≃ₗ[R] M) (φ ψ : Module.Dual R M) :
    dualDeterminant (dualAction g φ) (dualAction g ψ) =
      (dualDeterminant φ ψ).comp (exteriorPower.map 2 g.symm.toLinearMap) := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [dualDeterminant_ιMulti_apply]

/-- An action preserving all relations by equality preserves commuting in both directions.
The hypothesis is equality of relation submodules, not just forward preservation.
Blueprint: generic paired invariance in `lem:u04`. -/
theorem commutes_dualAction_iff (Q : Submodule R (⋀[R]^2 M)) (g : M ≃ₗ[R] M)
    (hQ : Q.map (exteriorPower.map 2 g.toLinearMap) = Q) (φ ψ : Module.Dual R M) :
    Commutes Q (dualAction g φ) (dualAction g ψ) ↔ Commutes Q φ ψ := by
  let F := exteriorPower.map 2 g.toLinearMap
  let G := exteriorPower.map 2 g.symm.toLinearMap
  have hGF (q : ⋀[R]^2 M) : G (F q) = q := by
    change (exteriorPower.map 2 g.symm.toLinearMap)
      ((exteriorPower.map 2 g.toLinearMap) q) = q
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have hid : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by ext; simp
    rw [hid, exteriorPower.map_id]
    rfl
  have hFQ (q : ⋀[R]^2 M) (hq : q ∈ Q) : F q ∈ Q := by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hGQ (q : ⋀[R]^2 M) (hq : q ∈ Q) : G q ∈ Q := by
    have hq' : q ∈ Q.map F := hQ.symm ▸ hq
    obtain ⟨p, hp, rfl⟩ := hq'
    rw [hGF]
    exact hp
  simp only [Commutes, IsConcreteLE.le_iff, LinearMap.mem_ker,
    dualDeterminant_dualAction, LinearMap.comp_apply]
  constructor
  · intro h q hq
    have := h (hFQ q hq)
    change dualDeterminant φ ψ (G (F q)) = 0 at this
    rw [hGF] at this
    exact this
  · intro h q hq
    exact h (hGQ q hq)

/-- Commuting relative to a span can be checked on its chosen generators.
Blueprint: the generic generator test in `lem:u04`. -/
theorem commutes_span_iff (s : Set (⋀[R]^2 M)) (φ ψ : Module.Dual R M) :
    Commutes (Submodule.span R s) φ ψ ↔ ∀ q ∈ s, dualDeterminant φ ψ q = 0 := by
  rw [Commutes, Submodule.span_le]
  rfl

variable {ι : Type v}

/-- The pair-coordinate determinant equation for an arbitrary index type.
Blueprint: the generic pair calculation in `lem:u04`. -/
theorem dualDeterminant_single (φ ψ : Module.Dual R (ι →₀ R)) (i j : ι) :
    dualDeterminant φ ψ
      (exteriorPower.ιMulti R 2 ![Finsupp.single i 1, Finsupp.single j 1]) =
      dualCoordinates φ i * dualCoordinates ψ j -
        dualCoordinates φ j * dualCoordinates ψ i := by simp

/-- The difference-coordinate determinant equation, including in characteristic two.
Geometric dependent-triple relators will specialize this formula.
Blueprint: the generic triple calculation in `lem:u04`. -/
theorem dualDeterminant_sub_single (φ ψ : Module.Dual R (ι →₀ R)) (i j k : ι) :
    dualDeterminant φ ψ (exteriorPower.ιMulti R 2
      ![Finsupp.single i 1 - Finsupp.single k 1, Finsupp.single j 1 - Finsupp.single k 1]) =
      (dualCoordinates φ i - dualCoordinates φ k) *
          (dualCoordinates ψ j - dualCoordinates ψ k) -
        (dualCoordinates φ j - dualCoordinates φ k) *
          (dualCoordinates ψ i - dualCoordinates ψ k) := by simp

end OrlikSolomon.HyperplaneGT
