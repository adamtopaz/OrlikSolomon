/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Graded
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Canonical quotients by the central scalar families

The quadratic and full graded scalar ranges are actual central normal subgroups. Their
quotients use Mathlib's group quotient. The reconstructed Galois projection descends to
each quotient, with inverse given by the class of the existing direct Galois action.

The subgroup, quotient maps and direct Galois class maps exist over arbitrary commutative
coefficient rings. The mutually inverse equivalences retain the explicit local, dimension
and generating-marking hypotheses. The quotient is by the scalar subgroup, which need not
be the full center. Blueprint: the two scalar quotients in S04 (`thm:s04`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The quadratic scalar range is normal because it is central, without reconstruction. -/
instance DiagramAut.scalarSubgroup_normal : (DiagramAut.scalarSubgroup R C S).Normal :=
  Subgroup.normal_of_le_center (DiagramAut.scalarSubgroup_le_center R C S)

/-- The full graded scalar range is normal because it is central, without reconstruction. -/
instance GradedDiagramAut.scalarSubgroup_normal :
    (GradedDiagramAut.scalarSubgroup R C S).Normal :=
  Subgroup.normal_of_le_center (GradedDiagramAut.scalarSubgroup_le_center R C S)

/-- The canonical quadratic quotient homomorphism by the literal scalar range. -/
def DiagramAut.scalarQuotientMap :
    DiagramAut R C S →* (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.mk' (DiagramAut.scalarSubgroup R C S)

/-- The canonical full graded quotient homomorphism by the literal scalar range. -/
def GradedDiagramAut.scalarQuotientMap :
    GradedDiagramAut R C S →*
      (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.mk' (GradedDiagramAut.scalarSubgroup R C S)

/-- The direct Galois family defines a canonical class in the quadratic scalar quotient.
This map exists over arbitrary coefficients; inverse claims require reconstruction. -/
def DiagramAut.scalarQuotientSection :
    (k ≃ₐ[k₀] k) →* (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  (DiagramAut.scalarQuotientMap R C S).comp (galoisQuadraticAction R C S)

/-- The existing full Galois family defines a canonical class in the graded scalar quotient.
This map exists over arbitrary coefficients; inverse claims require reconstruction. -/
def GradedDiagramAut.scalarQuotientSection :
    (k ≃ₐ[k₀] k) →*
      (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :=
  (GradedDiagramAut.scalarQuotientMap R C S).comp (galoisGradedAction R C S)

/-- The quadratic Galois class is the quotient of the existing direct family. -/
@[simp]
theorem DiagramAut.scalarQuotientSection_apply (σ : k ≃ₐ[k₀] k) :
    scalarQuotientSection R C S σ = scalarQuotientMap R C S (galoisQuadraticAut R C S σ) := rfl

/-- The graded Galois class is the quotient of the existing full direct family. -/
@[simp]
theorem GradedDiagramAut.scalarQuotientSection_apply (σ : k ≃ₐ[k₀] k) :
    scalarQuotientSection R C S σ = scalarQuotientMap R C S (galoisGradedAut R C S σ) := rfl

variable [IsLocalRing R]

/-- The full graded Galois projection is the existing quadratic projection after the actual
degree-one restriction. It performs no independent field extraction. -/
def GradedDiagramAut.toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S →* (k ≃ₐ[k₀] k) :=
  (DiagramAut.toGalois R C S hS hgen hn).comp (GradedDiagramAut.toQuadratic R C S)

/-- The full projection agrees with the quadratic extraction on the actual restriction. -/
theorem GradedDiagramAut.toGalois_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    toGalois R C S hS hgen hn g =
      DiagramAut.toGalois R C S hS hgen hn (toQuadratic R C S g) := rfl

/-- The existing direct full Galois family is a section of the full projection. -/
@[simp]
theorem GradedDiagramAut.toGalois_galoisGradedAut (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    toGalois R C S hS hgen hn (galoisGradedAut R C S σ) = σ :=
  galoisGradedAut_toGalois R C S hS hgen hn σ

/-- The kernel of the full Galois projection is precisely the literal full scalar range.
Faithful restriction retains the common target as well as every stage. -/
theorem GradedDiagramAut.ker_toGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (toGalois R C S hS hgen hn).ker = scalarSubgroup R C S := by
  ext g
  change DiagramAut.toGalois R C S hS hgen hn (toQuadratic R C S g) = 1 ↔
    ∃ a : Rˣ, scalarGradedAction R C S a = g
  constructor
  · intro hg
    have hm : toQuadratic R C S g ∈ DiagramAut.scalarSubgroup R C S := by
      rw [← DiagramAut.ker_toGalois R C S hS hgen hn]
      exact hg
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, toQuadratic_injective ?_⟩
    exact (toQuadratic_scalarGradedAut R C S a).trans ha
  · rintro ⟨a, rfl⟩
    simp

/-- The quadratic diagram modulo its central scalar range is canonically the Galois group.
Its inverse uses the class of the existing direct Galois family. Blueprint: S04 (`thm:s04`). -/
def DiagramAut.scalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) ≃* (k ≃ₐ[k₀] k) :=
  (QuotientGroup.quotientMulEquivOfEq (DiagramAut.ker_toGalois R C S hS hgen hn).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (DiagramAut.toGalois R C S hS hgen hn)
      (galoisQuadraticAut R C S) (galoisQuadraticAut_toGalois R C S hS hgen hn))

/-- The full graded diagram modulo its central scalar range is canonically the Galois group.
Its inverse uses the class of the existing full Galois family. Blueprint: S04 (`thm:s04`). -/
def GradedDiagramAut.scalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃* (k ≃ₐ[k₀] k) :=
  (QuotientGroup.quotientMulEquivOfEq (GradedDiagramAut.ker_toGalois R C S hS hgen hn).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (GradedDiagramAut.toGalois R C S hS hgen hn)
      (galoisGradedAut R C S) (GradedDiagramAut.toGalois_galoisGradedAut R C S hS hgen hn))

/-- The quadratic quotient equivalence is induced by exactly the reconstructed projection. -/
@[simp]
theorem DiagramAut.scalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
      toGalois R C S hS hgen hn g := by
  simp [scalarQuotientEquiv, scalarQuotientMap]

/-- The full quotient equivalence is induced by restriction followed by extraction. -/
@[simp]
theorem GradedDiagramAut.scalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
      toGalois R C S hS hgen hn g := by
  simp [scalarQuotientEquiv, scalarQuotientMap]

/-- The explicit inverse sends a Galois automorphism to its quadratic Galois class. -/
theorem DiagramAut.scalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ := by
  apply (scalarQuotientEquiv R C S hS hgen hn).injective
  simp

/-- The explicit inverse sends a Galois automorphism to its full graded Galois class. -/
theorem GradedDiagramAut.scalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ := by
  apply (scalarQuotientEquiv R C S hS hgen hn).injective
  simp

/-- Quadratic quotient projection followed by its explicit Galois section cancels. -/
theorem DiagramAut.scalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientSection R C S σ) = σ := by simp

/-- The explicit quadratic Galois section followed by the quotient equivalence cancels. -/
theorem DiagramAut.scalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ scalarSubgroup R C S) :
    scalarQuotientSection R C S (scalarQuotientEquiv R C S hS hgen hn q) = q := by
  rw [← scalarQuotientEquiv_symm_apply R C S hS hgen hn]
  exact (scalarQuotientEquiv R C S hS hgen hn).symm_apply_apply q

/-- Full quotient projection followed by its explicit Galois section cancels. -/
theorem GradedDiagramAut.scalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientSection R C S σ) = σ := by
  simp

/-- The explicit full Galois section followed by the quotient equivalence cancels. -/
theorem GradedDiagramAut.scalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ scalarSubgroup R C S) :
    scalarQuotientSection R C S (scalarQuotientEquiv R C S hS hgen hn q) = q := by
  rw [← scalarQuotientEquiv_symm_apply R C S hS hgen hn]
  exact (scalarQuotientEquiv R C S hS hgen hn).symm_apply_apply q

/-- The actual graded restriction induces a multiplicative equivalence of the two quotients
by their corresponding literal scalar ranges. -/
def scalarQuotientRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃*
      (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C S)
    (gradedAutEquiv R C S hS hgen hn) (GradedDiagramAut.map_scalarSubgroup_toQuadratic R C S)

/-- On each actual diagram class, quotient restriction is the class of the existing
degree-one restriction. -/
@[simp]
theorem scalarQuotientRestrictionEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    scalarQuotientRestrictionEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g) =
        DiagramAut.scalarQuotientMap R C S (GradedDiagramAut.toQuadratic R C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

/-- The two canonical Galois quotient equivalences commute with actual graded restriction.
This compares the same extracted field automorphism, with no independent quotient choice. -/
theorem scalarQuotientEquiv_restriction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    DiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (scalarQuotientRestrictionEquiv R C S hS hgen hn q) =
        GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change DiagramAut.scalarQuotientEquiv R C S hS hgen hn
    (scalarQuotientRestrictionEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)) =
    GradedDiagramAut.scalarQuotientEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)
  rw [scalarQuotientRestrictionEquiv_map, DiagramAut.scalarQuotientEquiv_map,
    GradedDiagramAut.scalarQuotientEquiv_map, GradedDiagramAut.toGalois_apply]

end OrlikSolomon.HyperplaneGT
