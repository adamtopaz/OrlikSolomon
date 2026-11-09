/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Restriction
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Field.ZMod

/-!
# Coefficient and common-target consumers of the marked diagrams

Concrete constructors use the full cofinal system over `𝔽₂`. Marking maps work with zero,
characteristic-two and Laurent-polynomial coefficients. In dimension zero the marking type
is empty, and a target interchange can have identity stage maps; retaining the common target
component in extensionality is therefore necessary.

Blueprint: regression consumers for A03 (`def:a03`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DiagramExamples

open Module OSAlgebra

/-- A concrete cofinal system over the two-element field, in any dimension. -/
def binarySystem (n : ℕ) : CofinalSystem (ZMod 2) (ZMod 2) n :=
  fullCofinalSystem (ZMod 2) (ZMod 2) n

/-- The coordinate marking with zero translate in the affine line over `𝔽₂`. -/
def coordinateMarking : Marking ({0} : Set (ZMod 2)) 1 := .coordinate 0 ⟨0, by simp⟩

/-- A selected stage at which this concrete marking is available. -/
def markingStage : (binarySystem 1).Stage :=
  ((binarySystem 1).exists_stage_marking coordinateMarking).choose

/-- Cofinality supplies both ordered labels at the chosen stage. -/
theorem coordinate_available : coordinateMarking.Available markingStage.val.val :=
  ((binarySystem 1).exists_stage_marking coordinateMarking).choose_spec

variable (R : Type*) [CommRing R]

/-- The identity family constructed through the public quadratic constructor. -/
def quadraticIdentity : DiagramAut R (binarySystem 1) ({0} : Set (ZMod 2)) :=
  DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.refl R _) (LinearEquiv.refl R _)
    (by intro 𝒜; simp) (by intro 𝒜 ℬ h; rfl) (by intro 𝒜 w hw; rfl)

/-- The identity family constructed through the full graded constructor. -/
def gradedIdentity : GradedDiagramAut R (binarySystem 1) ({0} : Set (ZMod 2)) :=
  GradedDiagramAut.ofEquivs (R := R) (C := binarySystem 1) (S := ({0} : Set (ZMod 2)))
    (fun _ ↦ AlgEquiv.refl) AlgEquiv.refl
    (by intro 𝒜 q; change (degree R 𝒜.val.val q).map LinearMap.id = _; exact Submodule.map_id _)
    (by intro q; change (degree R (twoPunctureArrangement (ZMod 2)) q).map LinearMap.id = _
        exact Submodule.map_id _)
    (by intro 𝒜 ℬ h; rfl) (by intro 𝒜 w hw; rfl)

/-- The two concrete identity constructors agree under faithful degree-one restriction. -/
theorem identity_restriction :
    GradedDiagramAut.toQuadratic R (binarySystem 1) ({0} : Set (ZMod 2)) (gradedIdentity R) =
      quadraticIdentity R := by
  change GradedDiagramAut.toQuadratic R (binarySystem 1) ({0} : Set (ZMod 2)) 1 = 1
  exact map_one _

/-- There are no markings in dimension zero, so the common target may be interchanged while
every stage map is the identity. This uses exactly the public constructor's hypotheses. -/
def zeroDimensionSwap : DiagramAut R (binarySystem 0) ({0} : Set (ZMod 2)) :=
  DiagramAut.ofEquivs (fun _ ↦ LinearEquiv.refl R _)
    (Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1))
    (by intro 𝒜; simp) (by intro 𝒜 ℬ h; rfl) (by intro 𝒜 w hw; exact (IsEmpty.false w).elim)

/-- The target interchange acts on the literal common ordered source. -/
theorem zeroDimensionSwap_target :
    (zeroDimensionSwap R).targetEquiv (Finsupp.single 0 1) = Finsupp.single 1 1 := by
  simp [zeroDimensionSwap]

/-- All finite-stage maps of this interchange are identities. -/
theorem zeroDimensionSwap_stage (𝒜 : (binarySystem 0).Stage) :
    (zeroDimensionSwap R).stageEquiv 𝒜 = LinearEquiv.refl R _ := by
  simp [zeroDimensionSwap]

/-- Stage maps alone do not determine a quadratic automorphism in dimension zero. -/
theorem zeroDimensionSwap_ne_one : zeroDimensionSwap (ZMod 2) ≠ 1 := by
  intro h
  have hh := congrArg (fun g : DiagramAut (ZMod 2) (binarySystem 0) ({0} : Set (ZMod 2)) ↦
    g.targetEquiv (Finsupp.single 0 1) 0) h
  simp [zeroDimensionSwap] at hh

/-- The zero coefficient ring admits the concrete diagram constructors and their group laws.
-/
theorem zeroRing_identity : quadraticIdentity (ZMod 1) * (quadraticIdentity (ZMod 1))⁻¹ = 1 :=
  mul_inv_cancel _

/-- All quadratic automorphisms over the zero ring coincide, with the original group type. -/
theorem zeroRing_aut_eq_one
    (g : DiagramAut (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2))) : g = 1 :=
  Subsingleton.elim _ _

/-- The full graded group also retains its expected triviality over zero coefficients. -/
theorem zeroRing_graded_aut_eq_one
    (g : GradedDiagramAut (ZMod 1) (binarySystem 1) ({0} : Set (ZMod 2))) : g = 1 :=
  Subsingleton.elim _ _

/-- An actual characteristic-two marking sends the full target quadratic module into Q. -/
theorem charTwo_quadratic_relation :
    exteriorPower.map 2 (coordinateMarking.basisMap (ZMod 2) coordinate_available)
      (exteriorPower.ιMulti (ZMod 2) 2 ![Finsupp.single 0 1, Finsupp.single 1 1]) ∈
        quadraticRelationSpan (ZMod 2) markingStage.val.val :=
  coordinateMarking.basisMap_quadraticRelationSpan (ZMod 2) coordinate_available
    ⟨_, Submodule.mem_top, rfl⟩

/-- Both ordered marking generators multiply to zero in characteristic two. -/
theorem charTwo_marking_product :
    generator (ZMod 2) markingStage.val.val (coordinateMarking.fiberLabel coordinate_available 0) *
      generator (ZMod 2) markingStage.val.val
        (coordinateMarking.fiberLabel coordinate_available 1) = 0 := by
  exact coordinateMarking.generator_mul_generator_fiberLabel (ZMod 2) coordinate_available 0 1

/-- A nonconstant Laurent coefficient is preserved by the concrete linear marking pullback. -/
theorem laurent_basisMap :
    coordinateMarking.basisMap (LaurentPolynomial ℤ) coordinate_available
      (Finsupp.single 1 (LaurentPolynomial.T (-1))) =
        Finsupp.single (coordinateMarking.fiberLabel coordinate_available 1)
          (LaurentPolynomial.T (-1)) := by
  exact coordinateMarking.basisMap_single (LaurentPolynomial ℤ) coordinate_available 1
    (LaurentPolynomial.T (-1))

/-- Full presentation marking pullback is linear over the independent Laurent coefficient ring.
Its ordered generator formula needs no coefficient map from the geometric field. -/
theorem laurent_osMap :
    coordinateMarking.osMap (LaurentPolynomial ℤ) coordinate_available
      (algebraMap (LaurentPolynomial ℤ) (OSAlgebra (LaurentPolynomial ℤ)
          (twoPunctureArrangement (ZMod 2))) (LaurentPolynomial.T (-1)) *
        generator (LaurentPolynomial ℤ) _ (twoPunctureLabel (ZMod 2) 0)) =
      algebraMap (LaurentPolynomial ℤ) (OSAlgebra (LaurentPolynomial ℤ) markingStage.val.val)
        (LaurentPolynomial.T (-1)) * generator (LaurentPolynomial ℤ) markingStage.val.val
          (coordinateMarking.fiberLabel coordinate_available 0) := by
  simp

/-- The concrete full graded constructor remains available over Laurent polynomial coefficients.
-/
theorem laurent_full_constructor :
    (gradedIdentity (LaurentPolynomial ℤ)).targetEquiv = AlgEquiv.refl := by
  simp [gradedIdentity]

end OrlikSolomon.HyperplaneGT.DiagramExamples
