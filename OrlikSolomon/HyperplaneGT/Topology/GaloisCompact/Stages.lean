/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Topology.GaloisCompact.FiniteOrbits
public import OrlikSolomon.HyperplaneGT.Topology.Krull.Hyperplanes
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits

/-!
# Finite scalar orbits from stable stages or algebraicity

A supplied cofinal system in positive dimension makes every scalar orbit finite: its
arbitrary geometric coordinate fiber belongs to a finite stable stage, and distinct scalar
values have distinct fibers. Algebraicity gives finite scalar orbits separately through the
existing minimal-polynomial bound. Either input therefore makes the actual pointwise
automorphism group compact, without normality, separability or a classification theorem.

These are pointwise conclusions. A supplied system does not assert the Krull comparison
criterion, and importing this module changes no global topology or compactness instance.

Blueprint: the supplied-system and algebraic corollaries of T07 (`prop:t07`).
-/

@[expose] public section

universe u v

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]

namespace CofinalSystem

variable {n : ℕ} (C : CofinalSystem k₀ k n)

include C

/-- The actual orbit of every geometric scalar is finite when a supplied stable cofinal
system has at least one coordinate. No algebraicity is assumed. Blueprint: T07 (`prop:t07`). -/
theorem galoisOrbit_finite (hn : 1 ≤ n) (a : k) :
    (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite := by
  classical
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨A, hA⟩ := C.exists_stage_containing {coordinateFiber i a}
  have ha : (coordinateFiber i a).val ∈ A.val.val := hA _ (by simp)
  have hstage : {H : Hyperplane k n | H.val ∈ A.val.val}.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn A.val.val.hyperplanes.finite_toSet
  have himage : (coordinateFiber i '' MulAction.orbit (k ≃ₐ[k₀] k) a).Finite := by
    apply hstage.subset
    rintro _ ⟨b, ⟨σ, rfl⟩, rfl⟩
    change (coordinateFiber i (σ a)).val ∈ A.val.val
    rw [← galois_smul_coordinateFiber]
    exact A.val.property σ _ ha
  exact himage.of_finite_image (coordinateFiber_injective i).injOn

/-- A supplied stable cofinal system in positive dimension makes the existing pointwise
field-automorphism group compact. It need not imply the Krull comparison criterion.
Blueprint: T07 (`prop:t07`). -/
theorem galoisPointwise_compactSpace (hn : 1 ≤ n) :
    @CompactSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) :=
  galoisPointwise_compactSpace_of_finite_orbits k₀ k (C.galoisOrbit_finite hn)

end CofinalSystem

variable (k₀ k)

/-- Algebraicity bounds every actual scalar orbit by the finite root set of its minimal
polynomial. Normality and separability are unnecessary. Blueprint: T07 (`prop:t07`). -/
theorem galoisOrbit_finite_of_isAlgebraic [Algebra.IsAlgebraic k₀ k] (a : k) :
    (MulAction.orbit (k ≃ₐ[k₀] k) a).Finite := by
  simpa only [MulAction.orbit, AlgEquiv.smul_def] using
    finite_scalarOrbit (k₀ := k₀) a (Algebra.IsAlgebraic.isAlgebraic a)

/-- The pointwise automorphism group of any algebraic field extension is compact, including
nonnormal and inseparable extensions. Blueprint: T07 (`prop:t07`). -/
theorem galoisPointwise_compactSpace_of_isAlgebraic [Algebra.IsAlgebraic k₀ k] :
    @CompactSpace (k ≃ₐ[k₀] k) (galoisPointwiseTopology k₀ k) :=
  galoisPointwise_compactSpace_of_finite_orbits k₀ k
    (galoisOrbit_finite_of_isAlgebraic k₀ k)

end OrlikSolomon.HyperplaneGT
