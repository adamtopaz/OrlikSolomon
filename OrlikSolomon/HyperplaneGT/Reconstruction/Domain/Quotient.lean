/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Graded
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quotient

/-!
# Scalar quotients over integral coefficients

The original quadratic and full graded scalar subgroups are central and normal over any
commutative coefficient ring. Domain classification identifies their literal quotients
with the Galois group. Both inverses are the already constructed direct Galois sections,
and the two quotient equivalences commute with actual degree-one restriction.

## Main definitions and results

* `DiagramAut.domainScalarQuotientEquiv`: the actual quadratic scalar quotient.
* `GradedDiagramAut.domainScalarQuotientEquiv`: the actual full graded scalar quotient.
* `domainScalarQuotientRestrictionEquiv`: the quotient of the actual restriction map.

Blueprint: the scalar-quotient conclusions of S05 (`thm:s05`). These are scalar ranges,
not full centers, and all constructions agree with the local versions on the overlap.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (R : Type r) [CommRing R] [IsDomain R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- The full domain Galois coordinate is extracted after the existing degree-one restriction.
-/
def GradedDiagramAut.domainToGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    GradedDiagramAut R C S →* (k ≃ₐ[k₀] k) :=
  (DiagramAut.domainToGalois R C S hS hgen hn).comp
    (GradedDiagramAut.toQuadratic R C S)

/-- The full domain projection is the quadratic projection on the actual restriction. -/
theorem GradedDiagramAut.domainToGalois_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainToGalois R C S hS hgen hn g =
      DiagramAut.domainToGalois R C S hS hgen hn (toQuadratic R C S g) := rfl

/-- The existing direct full Galois action is a section of the domain projection. -/
@[simp]
theorem GradedDiagramAut.domainToGalois_galoisGradedAut (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainToGalois R C S hS hgen hn (galoisGradedAut R C S σ) = σ :=
  DiagramAut.domainToGalois_galoisQuadraticAut R C S hS hgen hn σ

/-- The full domain projection has exactly the original central scalar range as kernel. -/
theorem GradedDiagramAut.ker_domainToGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainToGalois R C S hS hgen hn).ker = scalarSubgroup R C S := by
  ext g
  change DiagramAut.domainToGalois R C S hS hgen hn (toQuadratic R C S g) = 1 ↔
    ∃ a : Rˣ, scalarGradedAction R C S a = g
  constructor
  · intro hg
    have hm : toQuadratic R C S g ∈ DiagramAut.scalarSubgroup R C S := by
      rw [← DiagramAut.ker_domainToGalois R C S hS hgen hn]
      exact hg
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, toQuadratic_injective ?_⟩
    exact (toQuadratic_scalarGradedAut R C S a).trans ha
  · rintro ⟨a, rfl⟩
    change DiagramAut.domainToGalois R C S hS hgen hn
      (toQuadratic R C S (scalarGradedAut R C S a)) = 1
    rw [toQuadratic_scalarGradedAut]
    exact DiagramAut.domainToGalois_scalarQuadraticAut R C S hS hgen hn a

/-- The quadratic diagram modulo its original central scalar range is canonically Galois.
The inverse is the class of the existing direct Galois action. Blueprint: S05 (`thm:s05`). -/
def DiagramAut.domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) ≃* (k ≃ₐ[k₀] k) :=
  (QuotientGroup.quotientMulEquivOfEq
    (DiagramAut.ker_domainToGalois R C S hS hgen hn).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (DiagramAut.domainToGalois R C S hS hgen hn)
      (galoisQuadraticAut R C S) (DiagramAut.domainToGalois_galoisQuadraticAut R C S hS hgen hn))

/-- The full diagram modulo its original central scalar range is canonically Galois.
The inverse is the class of the existing full Galois action. Blueprint: S05 (`thm:s05`). -/
def GradedDiagramAut.domainScalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃* (k ≃ₐ[k₀] k) :=
  (QuotientGroup.quotientMulEquivOfEq
    (GradedDiagramAut.ker_domainToGalois R C S hS hgen hn).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse
      (GradedDiagramAut.domainToGalois R C S hS hgen hn)
      (galoisGradedAut R C S) (GradedDiagramAut.domainToGalois_galoisGradedAut R C S hS hgen hn))

/-- The quadratic quotient forward map is exactly the descended Galois coordinate. -/
@[simp]
theorem DiagramAut.domainScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
      domainToGalois R C S hS hgen hn g := by
  simp [domainScalarQuotientEquiv, scalarQuotientMap]

/-- The full quotient forward map is exactly its restriction's descended Galois coordinate.
-/
@[simp]
theorem GradedDiagramAut.domainScalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
      domainToGalois R C S hS hgen hn g := by
  simp [domainScalarQuotientEquiv, scalarQuotientMap]

/-- The explicit quadratic inverse is the already defined Galois class map. -/
theorem DiagramAut.domainScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ := by
  apply (domainScalarQuotientEquiv R C S hS hgen hn).injective
  simp

/-- The explicit full inverse is the already defined full Galois class map. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (domainScalarQuotientEquiv R C S hS hgen hn).symm σ = scalarQuotientSection R C S σ := by
  apply (domainScalarQuotientEquiv R C S hS hgen hn).injective
  simp

/-- Quadratic quotient projection cancels the existing direct Galois class section. -/
theorem DiagramAut.domainScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientSection R C S σ) = σ := by
  simp

/-- The explicit quadratic Galois section cancels the domain quotient equivalence. -/
theorem DiagramAut.domainScalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : DiagramAut R C S ⧸ scalarSubgroup R C S) :
    scalarQuotientSection R C S (domainScalarQuotientEquiv R C S hS hgen hn q) = q := by
  rw [← domainScalarQuotientEquiv_symm_apply R C S hS hgen hn]
  exact (domainScalarQuotientEquiv R C S hS hgen hn).symm_apply_apply q

/-- Full quotient projection cancels the existing direct Galois class section. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientSection R C S σ) = σ := by
  simp

/-- The explicit full Galois section cancels the domain quotient equivalence. -/
theorem GradedDiagramAut.domainScalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ scalarSubgroup R C S) :
    scalarQuotientSection R C S (domainScalarQuotientEquiv R C S hS hgen hn q) = q := by
  rw [← domainScalarQuotientEquiv_symm_apply R C S hS hgen hn]
  exact (domainScalarQuotientEquiv R C S hS hgen hn).symm_apply_apply q

/-- The actual degree-one restriction induces an equivalence of both literal scalar quotients.
-/
def domainScalarQuotientRestrictionEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) ≃*
      (DiagramAut R C S ⧸ DiagramAut.scalarSubgroup R C S) :=
  QuotientGroup.congr (GradedDiagramAut.scalarSubgroup R C S) (DiagramAut.scalarSubgroup R C S)
    (coefficientDomainGradedAutEquiv R C S hS hgen hn)
    (GradedDiagramAut.map_scalarSubgroup_toQuadratic R C S)

/-- On actual representatives, quotient restriction is the original degree-one restriction.
-/
@[simp]
theorem domainScalarQuotientRestrictionEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut R C S) :
    domainScalarQuotientRestrictionEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g) =
        DiagramAut.scalarQuotientMap R C S (GradedDiagramAut.toQuadratic R C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

/-- The two domain scalar quotient equivalences commute with the actual restriction. -/
theorem domainScalarQuotientEquiv_restriction (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (q : GradedDiagramAut R C S ⧸ GradedDiagramAut.scalarSubgroup R C S) :
    DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (domainScalarQuotientRestrictionEquiv R C S hS hgen hn q) =
        GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change DiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
    (domainScalarQuotientRestrictionEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)) =
    GradedDiagramAut.domainScalarQuotientEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)
  rw [domainScalarQuotientRestrictionEquiv_map, DiagramAut.domainScalarQuotientEquiv_map,
    GradedDiagramAut.domainScalarQuotientEquiv_map, GradedDiagramAut.domainToGalois_apply]

/-- The actual restriction equivalences agree when the domain is also local. -/
theorem coefficientDomainGradedAutEquiv_eq_gradedAutEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainGradedAutEquiv R C S hS hgen hn =
      gradedAutEquiv R C S hS hgen hn := by
  apply MulEquiv.ext
  intro g
  rfl

/-- The full scalar/Galois classifications agree on the local/domain overlap. -/
theorem coefficientDomainGradedClassificationEquiv_eq_gradedClassificationEquiv
    [IsLocalRing R] (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainGradedClassificationEquiv R C S hS hgen hn =
      gradedClassificationEquiv R C S hS hgen hn := by
  unfold coefficientDomainGradedClassificationEquiv gradedClassificationEquiv
  rw [coefficientDomainAutEquiv_eq_quadraticAutEquiv,
    coefficientDomainGradedAutEquiv_eq_gradedAutEquiv]

/-- The full Galois projections agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainToGalois_eq_toGalois [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainToGalois R C S hS hgen hn = toGalois R C S hS hgen hn := by
  apply MonoidHom.ext
  intro g
  rw [domainToGalois_apply, DiagramAut.domainToGalois_eq_toGalois]
  rfl

/-- The quadratic scalar quotient equivalences agree on the local/domain overlap. -/
theorem DiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientEquiv R C S hS hgen hn = scalarQuotientEquiv R C S hS hgen hn := by
  apply MulEquiv.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup R C S) q
  change domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g)
  rw [domainScalarQuotientEquiv_map, scalarQuotientEquiv_map,
    domainToGalois_eq_toGalois]

/-- The full scalar quotient equivalences agree on the local/domain overlap. -/
theorem GradedDiagramAut.domainScalarQuotientEquiv_eq_scalarQuotientEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientEquiv R C S hS hgen hn = scalarQuotientEquiv R C S hS hgen hn := by
  apply MulEquiv.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup R C S) q
  change domainScalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g) =
    scalarQuotientEquiv R C S hS hgen hn (scalarQuotientMap R C S g)
  rw [domainScalarQuotientEquiv_map, scalarQuotientEquiv_map,
    domainToGalois_eq_toGalois]

/-- Quotient restriction is the same actual map on the local/domain overlap. -/
theorem domainScalarQuotientRestrictionEquiv_eq_scalarQuotientRestrictionEquiv
    [IsLocalRing R] (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    domainScalarQuotientRestrictionEquiv R C S hS hgen hn =
      scalarQuotientRestrictionEquiv R C S hS hgen hn := by
  apply MulEquiv.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GradedDiagramAut.scalarSubgroup R C S) q
  change domainScalarQuotientRestrictionEquiv R C S hS hgen hn
    (GradedDiagramAut.scalarQuotientMap R C S g) =
    scalarQuotientRestrictionEquiv R C S hS hgen hn
      (GradedDiagramAut.scalarQuotientMap R C S g)
  rw [domainScalarQuotientRestrictionEquiv_map, scalarQuotientRestrictionEquiv_map]

end OrlikSolomon.HyperplaneGT
