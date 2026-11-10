/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.DeRham.Reconstruction

/-!
# Algebraic scalar quotients of the ordinary de Rham diagram

These genuinely new wrappers use the existing ordinary scalar and Galois actions. The
scalar subgroup is their literal scalar range, central and normal without reconstruction
hypotheses. Its Mathlib quotient is compared by the old twists with the existing actual
quotient. The quotient-to-Galois equivalence only composes the old theory-level map and
retains its exact marking/dimension hypotheses; no classification argument is repeated.

This algebraic-only leaf imports no new topology module. It honestly imports the old
ordinary Reconstruction file because that file names the existing actions. Neither a
scalar range nor a quotient twist is identified with the full center.

Blueprint: algebraic prerequisites of T17 (`cor:t17`), whose final topology remains separate.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] [CharZero k]
  {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

local notation "Tdr" => Geometric.DeRham.ordinaryTheory k

/-- The existing ordinary scalar action has exactly the old actual-theory action under twist. -/
theorem quadraticTwistEquiv_scalarQuadraticAction (a : kˣ) :
    quadraticTwistEquiv C S (scalarQuadraticAction C S a) =
      Cohomology.scalarQuadraticAction Tdr C S a :=
  (quadraticTwistEquiv C S).apply_symm_apply _

/-- The existing ordinary galois action has exactly the old actual-theory action under twist. -/
theorem quadraticTwistEquiv_galoisQuadraticAction (σ : k ≃ₐ[k₀] k) :
    quadraticTwistEquiv C S (galoisQuadraticAction C S σ) =
      Cohomology.galoisQuadraticAction Tdr C S σ :=
  (quadraticTwistEquiv C S).apply_symm_apply _

/-- The existing ordinary scalar action has exactly the old actual-theory action under twist. -/
theorem gradedTwistEquiv_scalarGradedAction (a : kˣ) :
    gradedTwistEquiv C S (scalarGradedAction C S a) = Cohomology.scalarGradedAction Tdr C S a :=
  (gradedTwistEquiv C S).apply_symm_apply _

/-- The existing ordinary galois action has exactly the old actual-theory action under twist. -/
theorem gradedTwistEquiv_galoisGradedAction (σ : k ≃ₐ[k₀] k) :
    gradedTwistEquiv C S (galoisGradedAction C S σ) = Cohomology.galoisGradedAction Tdr C S σ :=
  (gradedTwistEquiv C S).apply_symm_apply _

/-- Every ordinary scalar family commutes with every ordinary diagram automorphism. -/
theorem scalarQuadraticAction_commute (a : kˣ) (g : DiagramAut C S) :
    Commute (scalarQuadraticAction C S a) g := by
  apply (quadraticTwistEquiv C S).injective
  simpa only [map_mul, quadraticTwistEquiv_scalarQuadraticAction] using
    (Cohomology.scalarQuadraticAction_commute Tdr C S a (quadraticTwistEquiv C S g)).eq

namespace DiagramAut

/-- The ordinary scalar subgroup is the literal range of the already defined action. -/
def scalarSubgroup : Subgroup (DiagramAut C S) := (scalarQuadraticAction C S).range

/-- The ordinary scalar range is central; no equality with the entire center is asserted. -/
theorem scalarSubgroup_le_center : scalarSubgroup C S ≤ Subgroup.center (DiagramAut C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarQuadraticAction_commute C S a g).eq.symm

/-- Centrality supplies the single normality instance for the new ordinary scalar range. -/
instance scalarSubgroup_normal : (scalarSubgroup C S).Normal :=
  Subgroup.normal_of_le_center (scalarSubgroup_le_center C S)

end DiagramAut

/-- The old twist maps the entire new ordinary scalar range onto the old actual range. -/
theorem quadraticTwistEquiv_map_scalarSubgroup :
    (DiagramAut.scalarSubgroup C S).map (quadraticTwistEquiv C S).toMonoidHom =
      Cohomology.DiagramAut.scalarSubgroup Tdr C S := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (quadraticTwistEquiv_scalarQuadraticAction C S a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarQuadraticAction C S a, ⟨a, rfl⟩, quadraticTwistEquiv_scalarQuadraticAction C S a⟩

namespace DiagramAut

/-- The actual Mathlib quotient projection by the new literal ordinary scalar range. -/
def scalarQuotientMap : DiagramAut C S →* (DiagramAut C S ⧸ scalarSubgroup C S) :=
  QuotientGroup.mk' (scalarSubgroup C S)

/-- The existing ordinary Galois family defines its canonical scalar-quotient class. -/
def scalarQuotientSection : (k ≃ₐ[k₀] k) →* (DiagramAut C S ⧸ scalarSubgroup C S) :=
  (scalarQuotientMap C S).comp (galoisQuadraticAction C S)

/-- The section is exactly the quotient of the old ordinary direct Galois action. -/
theorem scalarQuotientSection_apply (σ : k ≃ₐ[k₀] k) :
    scalarQuotientSection C S σ = scalarQuotientMap C S (galoisQuadraticAction C S σ) := rfl

/-- Every old ordinary scalar action becomes identity in its literal range quotient. -/
theorem scalarQuotientMap_scalar (a : kˣ) :
    scalarQuotientMap C S (scalarQuadraticAction C S a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

/-- The new ordinary quotient twist is induced by the old twist and whole scalar-range equality. -/
def scalarQuotientTwistEquiv :
    (DiagramAut C S ⧸ scalarSubgroup C S) ≃*
      (Cohomology.DiagramAut Tdr C S ⧸ Cohomology.DiagramAut.scalarSubgroup Tdr C S) :=
  QuotientGroup.congr (scalarSubgroup C S) (Cohomology.DiagramAut.scalarSubgroup Tdr C S)
    (quadraticTwistEquiv C S) (quadraticTwistEquiv_map_scalarSubgroup C S)

/-- The quotient twist sends every ordinary representative through the exact old twist. -/
theorem scalarQuotientTwistEquiv_map (g : DiagramAut C S) :
    scalarQuotientTwistEquiv C S (scalarQuotientMap C S g) =
      Cohomology.DiagramAut.scalarQuotientMap Tdr C S (quadraticTwistEquiv C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

/-- The inverse quotient twist uses the exact old ordinary inverse on representatives. -/
theorem scalarQuotientTwistEquiv_symm_map (g : Cohomology.DiagramAut Tdr C S) :
    (scalarQuotientTwistEquiv C S).symm
        (Cohomology.DiagramAut.scalarQuotientMap Tdr C S g) =
      scalarQuotientMap C S ((quadraticTwistEquiv C S).symm g) := by
  apply (scalarQuotientTwistEquiv C S).symm_apply_eq.mpr
  exact ((scalarQuotientTwistEquiv_map C S ((quadraticTwistEquiv C S).symm g)).trans
    (congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C S)
      ((quadraticTwistEquiv C S).apply_symm_apply g))).symm

/-- The quotient twists retain the same canonical direct Galois class section. -/
theorem scalarQuotientTwistEquiv_section (σ : k ≃ₐ[k₀] k) :
    scalarQuotientTwistEquiv C S (scalarQuotientSection C S σ) =
      Cohomology.DiagramAut.scalarQuotientSection Tdr C S σ := by
  exact (scalarQuotientTwistEquiv_map C S (galoisQuadraticAction C S σ)).trans
    (congrArg (Cohomology.DiagramAut.scalarQuotientMap Tdr C S)
      (quadraticTwistEquiv_galoisQuadraticAction C S σ))

/-- The new ordinary scalar quotient equivalence is precisely the old theory-level map
following the new quotient twist. It retains the old classification hypotheses. -/
def scalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (DiagramAut C S ⧸ scalarSubgroup C S) ≃* (k ≃ₐ[k₀] k) :=
  (scalarQuotientTwistEquiv C S).trans
    (Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn)

/-- The exact old theory/twist composite defining the new ordinary quotient wrapper. -/
theorem scalarQuotientEquiv_eq_composite (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    scalarQuotientEquiv C S hS hgen hn = (scalarQuotientTwistEquiv C S).trans
      (Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn) := rfl

/-- An ordinary representative has the Galois coordinate of its exact old reconstruction. -/
theorem scalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut C S) :
    scalarQuotientEquiv C S hS hgen hn (scalarQuotientMap C S g) =
      ((quadraticReconstruction C S hS hgen hn).symm g).2 := by
  change Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn
    (scalarQuotientTwistEquiv C S (scalarQuotientMap C S g)) = _
  rw [scalarQuotientTwistEquiv_map, Cohomology.DiagramAut.localScalarQuotientEquiv_map]
  rfl

/-- The canonical direct ordinary Galois section cancels quotient extraction. -/
theorem scalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientEquiv C S hS hgen hn (scalarQuotientSection C S σ) = σ := by
  change Cohomology.DiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn
    (scalarQuotientTwistEquiv C S (scalarQuotientSection C S σ)) = σ
  rw [scalarQuotientTwistEquiv_section]
  exact Cohomology.DiagramAut.localScalarQuotientEquiv_section Tdr C S hS hgen hn σ

/-- The inverse is exactly the new class of the old ordinary direct Galois family. -/
theorem scalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientEquiv C S hS hgen hn).symm σ = scalarQuotientSection C S σ := by
  exact (scalarQuotientEquiv C S hS hgen hn).symm_apply_eq.mpr
    (scalarQuotientEquiv_section C S hS hgen hn σ).symm

/-- The section recovers every original ordinary quotient class after extraction. -/
theorem scalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : DiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientEquiv C S hS hgen hn q) = q := by
  rw [← scalarQuotientEquiv_symm_apply]
  exact (scalarQuotientEquiv C S hS hgen hn).symm_apply_apply q

/-- Local and domain old-theory descriptions agree for the same coefficient field. -/
theorem scalarQuotientEquiv_eq_domain_composite (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    scalarQuotientEquiv C S hS hgen hn = (scalarQuotientTwistEquiv C S).trans
      (Cohomology.DiagramAut.domainScalarQuotientEquiv Tdr C S hS hgen hn) := by
  exact congrArg (fun e ↦ (scalarQuotientTwistEquiv C S).trans e)
    (Cohomology.DiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv
      Tdr C S hS hgen hn).symm

end DiagramAut

/-- Every ordinary scalar family commutes with every ordinary diagram automorphism. -/
theorem scalarGradedAction_commute (a : kˣ) (g : GradedDiagramAut C S) :
    Commute (scalarGradedAction C S a) g := by
  apply (gradedTwistEquiv C S).injective
  simpa only [map_mul, gradedTwistEquiv_scalarGradedAction] using
    (Cohomology.scalarGradedAction_commute Tdr C S a (gradedTwistEquiv C S g)).eq

namespace GradedDiagramAut

/-- The ordinary scalar subgroup is the literal range of the already defined action. -/
def scalarSubgroup : Subgroup (GradedDiagramAut C S) := (scalarGradedAction C S).range

/-- The ordinary scalar range is central; no equality with the entire center is asserted. -/
theorem scalarSubgroup_le_center : scalarSubgroup C S ≤ Subgroup.center (GradedDiagramAut C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarGradedAction_commute C S a g).eq.symm

/-- Centrality supplies the single normality instance for the new ordinary scalar range. -/
instance scalarSubgroup_normal : (scalarSubgroup C S).Normal :=
  Subgroup.normal_of_le_center (scalarSubgroup_le_center C S)

end GradedDiagramAut

/-- The old twist maps the entire new ordinary scalar range onto the old actual range. -/
theorem gradedTwistEquiv_map_scalarSubgroup :
    (GradedDiagramAut.scalarSubgroup C S).map (gradedTwistEquiv C S).toMonoidHom =
      Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (gradedTwistEquiv_scalarGradedAction C S a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAction C S a, ⟨a, rfl⟩, gradedTwistEquiv_scalarGradedAction C S a⟩

namespace GradedDiagramAut

/-- The actual Mathlib quotient projection by the new literal ordinary scalar range. -/
def scalarQuotientMap : GradedDiagramAut C S →* (GradedDiagramAut C S ⧸ scalarSubgroup C S) :=
  QuotientGroup.mk' (scalarSubgroup C S)

/-- The existing ordinary Galois family defines its canonical scalar-quotient class. -/
def scalarQuotientSection : (k ≃ₐ[k₀] k) →* (GradedDiagramAut C S ⧸ scalarSubgroup C S) :=
  (scalarQuotientMap C S).comp (galoisGradedAction C S)

/-- The section is exactly the quotient of the old ordinary direct Galois action. -/
theorem scalarQuotientSection_apply (σ : k ≃ₐ[k₀] k) :
    scalarQuotientSection C S σ = scalarQuotientMap C S (galoisGradedAction C S σ) := rfl

/-- Every old ordinary scalar action becomes identity in its literal range quotient. -/
theorem scalarQuotientMap_scalar (a : kˣ) :
    scalarQuotientMap C S (scalarGradedAction C S a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

/-- The new ordinary quotient twist is induced by the old twist and whole scalar-range equality. -/
def scalarQuotientTwistEquiv :
    (GradedDiagramAut C S ⧸ scalarSubgroup C S) ≃*
      (Cohomology.GradedDiagramAut Tdr C S ⧸ Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S) :=
  QuotientGroup.congr (scalarSubgroup C S) (Cohomology.GradedDiagramAut.scalarSubgroup Tdr C S)
    (gradedTwistEquiv C S) (gradedTwistEquiv_map_scalarSubgroup C S)

/-- The quotient twist sends every ordinary representative through the exact old twist. -/
theorem scalarQuotientTwistEquiv_map (g : GradedDiagramAut C S) :
    scalarQuotientTwistEquiv C S (scalarQuotientMap C S g) =
      Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S (gradedTwistEquiv C S g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

/-- The inverse quotient twist uses the exact old ordinary inverse on representatives. -/
theorem scalarQuotientTwistEquiv_symm_map (g : Cohomology.GradedDiagramAut Tdr C S) :
    (scalarQuotientTwistEquiv C S).symm
        (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S g) =
      scalarQuotientMap C S ((gradedTwistEquiv C S).symm g) := by
  apply (scalarQuotientTwistEquiv C S).symm_apply_eq.mpr
  exact ((scalarQuotientTwistEquiv_map C S ((gradedTwistEquiv C S).symm g)).trans
    (congrArg (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S)
      ((gradedTwistEquiv C S).apply_symm_apply g))).symm

/-- The quotient twists retain the same canonical direct Galois class section. -/
theorem scalarQuotientTwistEquiv_section (σ : k ≃ₐ[k₀] k) :
    scalarQuotientTwistEquiv C S (scalarQuotientSection C S σ) =
      Cohomology.GradedDiagramAut.scalarQuotientSection Tdr C S σ := by
  exact (scalarQuotientTwistEquiv_map C S (galoisGradedAction C S σ)).trans
    (congrArg (Cohomology.GradedDiagramAut.scalarQuotientMap Tdr C S)
      (gradedTwistEquiv_galoisGradedAction C S σ))

/-- The new ordinary scalar quotient equivalence is precisely the old theory-level map
following the new quotient twist. It retains the old classification hypotheses. -/
def scalarQuotientEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (GradedDiagramAut C S ⧸ scalarSubgroup C S) ≃* (k ≃ₐ[k₀] k) :=
  (scalarQuotientTwistEquiv C S).trans
    (Cohomology.GradedDiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn)

/-- The exact old theory/twist composite defining the new ordinary quotient wrapper. -/
theorem scalarQuotientEquiv_eq_composite (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    scalarQuotientEquiv C S hS hgen hn = (scalarQuotientTwistEquiv C S).trans
      (Cohomology.GradedDiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn) := rfl

/-- An ordinary representative has the Galois coordinate of its exact old reconstruction. -/
theorem scalarQuotientEquiv_map (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : GradedDiagramAut C S) :
    scalarQuotientEquiv C S hS hgen hn (scalarQuotientMap C S g) =
      ((gradedReconstruction C S hS hgen hn).symm g).2 := by
  change Cohomology.GradedDiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn
    (scalarQuotientTwistEquiv C S (scalarQuotientMap C S g)) = _
  rw [scalarQuotientTwistEquiv_map, Cohomology.GradedDiagramAut.localScalarQuotientEquiv_map]
  rfl

/-- The canonical direct ordinary Galois section cancels quotient extraction. -/
theorem scalarQuotientEquiv_section (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    scalarQuotientEquiv C S hS hgen hn (scalarQuotientSection C S σ) = σ := by
  change Cohomology.GradedDiagramAut.localScalarQuotientEquiv Tdr C S hS hgen hn
    (scalarQuotientTwistEquiv C S (scalarQuotientSection C S σ)) = σ
  rw [scalarQuotientTwistEquiv_section]
  exact Cohomology.GradedDiagramAut.localScalarQuotientEquiv_section Tdr C S hS hgen hn σ

/-- The inverse is exactly the new class of the old ordinary direct Galois family. -/
theorem scalarQuotientEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    (scalarQuotientEquiv C S hS hgen hn).symm σ = scalarQuotientSection C S σ := by
  exact (scalarQuotientEquiv C S hS hgen hn).symm_apply_eq.mpr
    (scalarQuotientEquiv_section C S hS hgen hn σ).symm

/-- The section recovers every original ordinary quotient class after extraction. -/
theorem scalarQuotientSection_equiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (q : GradedDiagramAut C S ⧸ scalarSubgroup C S) :
    scalarQuotientSection C S (scalarQuotientEquiv C S hS hgen hn q) = q := by
  rw [← scalarQuotientEquiv_symm_apply]
  exact (scalarQuotientEquiv C S hS hgen hn).symm_apply_apply q

/-- Local and domain old-theory descriptions agree for the same coefficient field. -/
theorem scalarQuotientEquiv_eq_domain_composite (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    scalarQuotientEquiv C S hS hgen hn = (scalarQuotientTwistEquiv C S).trans
      (Cohomology.GradedDiagramAut.domainScalarQuotientEquiv Tdr C S hS hgen hn) := by
  exact congrArg (fun e ↦ (scalarQuotientTwistEquiv C S).trans e)
    (Cohomology.GradedDiagramAut.domainScalarQuotientEquiv_eq_localScalarQuotientEquiv
      Tdr C S hS hgen hn).symm

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
