/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Diagram
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quadratic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Descending the classification from the coefficient fraction field

Extend the actual diagram matrices to the fraction field and use the local classification
there. The common target recovers the scalar and its inverse as original matrix entries.
Injectivity of the coefficient map then descends the unit equations and every component.

## Main definitions and results

* `DiagramAut.domainToGalois`: the canonical fraction-field Galois coordinate.
* `DiagramAut.existsUnique_scalar_mul_galois`: descent of the unique original scalar.
* `coefficientDomainAutEquiv`: the actual quadratic classification over an integral domain.
* `coefficientDomainAutEquiv_eq_quadraticAutEquiv`: agreement on the local/domain overlap.

Blueprint: the quadratic classification in S05 (`thm:s05`). The only additional coefficient
hypothesis for descent is that the original commutative ring is an integral domain.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r s

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
  (R : Type r) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)
  (A : Type s) [CommRing A] [Algebra R A]

/-- Coefficient extension carries a primal scalar to its image unit. -/
@[simp]
theorem coefficientExtend_scalarQuadraticAut (u : Rˣ) :
    DiagramAut.coefficientExtend R C S A (scalarQuadraticAut R C S u) =
      scalarQuadraticAut A C S (Units.map (algebraMap R A) u) := by
  apply DiagramAut.ext
  · intro B
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro H a
    change (DiagramAut.coefficientExtend R C S A
      (scalarQuadraticAut R C S u)).stageEquiv B (Finsupp.single H a) =
        (scalarQuadraticAut A C S (Units.map (algebraMap R A) u)).stageEquiv B
          (Finsupp.single H a)
    rw [show Finsupp.single H a = a • Finsupp.single H (1 : A) by simp,
      map_smul, map_smul, DiagramAut.coefficientExtend_stage_single,
      scalarQuadraticAut_stageEquiv_apply, scalarQuadraticAut_stageEquiv_apply]
    simp [Algebra.smul_def]
  · apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro i a
    change (DiagramAut.coefficientExtend R C S A
      (scalarQuadraticAut R C S u)).targetEquiv (Finsupp.single i a) =
        (scalarQuadraticAut A C S (Units.map (algebraMap R A) u)).targetEquiv
          (Finsupp.single i a)
    rw [show Finsupp.single i a = a • Finsupp.single i (1 : A) by simp,
      map_smul, map_smul, DiagramAut.coefficientExtend_target_single,
      scalarQuadraticAut_targetEquiv_apply, scalarQuadraticAut_targetEquiv_apply]
    simp [Algebra.smul_def]

/-- Coefficient extension keeps the direct Galois family and its identity common target. -/
@[simp]
theorem coefficientExtend_galoisQuadraticAut (σ : k ≃ₐ[k₀] k) :
    DiagramAut.coefficientExtend R C S A (galoisQuadraticAut R C S σ) =
      galoisQuadraticAut A C S σ := by
  apply DiagramAut.ext
  · intro B
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro H a
    change (DiagramAut.coefficientExtend R C S A
      (galoisQuadraticAut R C S σ)).stageEquiv B (Finsupp.single H a) =
        (galoisQuadraticAut A C S σ).stageEquiv B (Finsupp.single H a)
    rw [show Finsupp.single H a = a • Finsupp.single H (1 : A) by simp,
      map_smul, map_smul, DiagramAut.coefficientExtend_stage_single,
      galoisQuadraticAut_stageEquiv_single, galoisQuadraticAut_stageEquiv_single]
    simp
  · rw [DiagramAut.coefficientExtend_targetEquiv, galoisQuadraticAut_targetEquiv,
      galoisQuadraticAut_targetEquiv]
    exact coefficientExtendLinearEquiv_refl R A

variable [IsDomain R]

namespace DiagramAut

/-- Recover the Galois coordinate over the canonical coefficient fraction field.
No choice of fraction field appears among the parameters. Blueprint: S05 (`thm:s05`). -/
def domainToGalois (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut R C S →* (k ≃ₐ[k₀] k) :=
  (toGalois (FractionRing R) C S hS hgen hn).comp
    (coefficientExtend R C S (FractionRing R))

/-- The recovered domain Galois coordinate is exactly fraction-field extraction. -/
theorem domainToGalois_eq_fractionField (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    domainToGalois R C S hS hgen hn g =
      toGalois (FractionRing R) C S hS hgen hn
        (coefficientExtend R C S (FractionRing R) g) := rfl

/-- The domain Galois coordinate recovers the direct geometric field action. -/
@[simp]
theorem domainToGalois_galoisQuadraticAut (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    domainToGalois R C S hS hgen hn (galoisQuadraticAut R C S σ) = σ := by
  rw [domainToGalois_eq_fractionField, coefficientExtend_galoisQuadraticAut]
  exact galoisQuadraticAut_toGalois (FractionRing R) C S hS hgen hn σ

/-- Scalar families have trivial Galois coordinate over an integral domain. -/
@[simp]
theorem domainToGalois_scalarQuadraticAut (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) :
    domainToGalois R C S hS hgen hn (scalarQuadraticAut R C S u) = 1 := by
  rw [domainToGalois_eq_fractionField, coefficientExtend_scalarQuadraticAut]
  exact scalarQuadraticAut_toGalois (FractionRing R) C S hS hgen hn _

/-- The fraction-field scalar and its inverse descend from the original common-target
matrix entries. Faithful coefficient extension then descends every diagram component.
Blueprint: the descent step of S05 (`thm:s05`). -/
theorem existsUnique_scalar_mul_galois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    ∃! u : Rˣ, scalarQuadraticAut R C S u *
      galoisQuadraticAut R C S (domainToGalois R C S hS hgen hn g) = g := by
  let gK : DiagramAut (FractionRing R) C S := coefficientExtend R C S (FractionRing R) g
  let c : (FractionRing R)ˣ := gK.scalarPart hS hgen hn
  let r : R := g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0
  let s : R := g⁻¹.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0
  have hr : algebraMap R (FractionRing R) r = (c : FractionRing R) := by
    have he := coefficientExtend_target_single R C S (FractionRing R) g (0 : Fin 2)
    change gK.targetEquiv (Finsupp.single 0 1) = _ at he
    rw [gK.scalarPart_targetEquiv_apply hS hgen hn] at he
    simpa [r, c] using (congrArg (fun x : Fin 2 →₀ FractionRing R ↦ x 0) he).symm
  have hs : algebraMap R (FractionRing R) s = (↑c⁻¹ : FractionRing R) := by
    have he := coefficientExtend_target_single R C S (FractionRing R) g⁻¹ (0 : Fin 2)
    rw [map_inv] at he
    change (gK⁻¹).targetEquiv (Finsupp.single 0 1) = _ at he
    rw [scalarPart_targetEquiv_apply, scalarPart_inv] at he
    simpa [s, c] using (congrArg (fun x : Fin 2 →₀ FractionRing R ↦ x 0) he).symm
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_mul, map_one, hr, hs]
    simp
  let u : Rˣ := ⟨r, s, hrs, by simpa only [mul_comm] using hrs⟩
  have hu : Units.map (algebraMap R (FractionRing R)) u = c := Units.ext hr
  have hfactor : scalarQuadraticAut R C S u *
      galoisQuadraticAut R C S (domainToGalois R C S hS hgen hn g) = g := by
    apply coefficientExtend_injective R C S (FractionRing R)
      (IsFractionRing.injective R (FractionRing R))
    rw [map_mul, coefficientExtend_scalarQuadraticAut, coefficientExtend_galoisQuadraticAut,
      hu]
    change scalarQuadraticAut (FractionRing R) C S c *
      galoisQuadraticAut (FractionRing R) C S
        (toGalois (FractionRing R) C S hS hgen hn gK) = gK
    exact quadraticAutEquiv_right_inv (FractionRing R) C S hS hgen hn gK
  refine ⟨u, hfactor, ?_⟩
  intro v hv
  apply scalarQuadraticAction_injective R C S
  change scalarQuadraticAut R C S v = scalarQuadraticAut R C S u
  exact mul_right_cancel (hv.trans hfactor.symm)

variable {R C S}

/-- The unique descended primal unit of the original diagram. Its value is computed by
the original common target, not a chosen fraction-field representative. -/
def domainScalarPart (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : Rˣ :=
  (existsUnique_scalar_mul_galois R C S hS hgen hn g).exists.choose

/-- The descended unit and Galois coordinate reconstruct the whole actual diagram. -/
theorem domainScalarPart_factor (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    scalarQuadraticAut R C S (g.domainScalarPart hS hgen hn) *
      galoisQuadraticAut R C S (domainToGalois R C S hS hgen hn g) = g :=
  (existsUnique_scalar_mul_galois R C S hS hgen hn g).exists.choose_spec

/-- The (0,0) entry of the original common-target matrix computes the descended primal unit.
-/
theorem domainScalarPart_val (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (g.domainScalarPart hS hgen hn : R) = g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 := by
  have he := congrArg (fun f : DiagramAut R C S ↦
    f.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0) (g.domainScalarPart_factor hS hgen hn)
  simpa using he

end DiagramAut

/-- The actual marked quadratic diagram over any integral domain is canonically the
product of coefficient units and geometric Galois automorphisms. The inverse descends the
fraction-field scalar to its original common-target matrix entry. Blueprint: S05 (`thm:s05`).
-/
def coefficientDomainAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut R C S where
  toFun p := scalarQuadraticAut R C S p.1 * galoisQuadraticAut R C S p.2
  invFun g := (g.domainScalarPart hS hgen hn, DiagramAut.domainToGalois R C S hS hgen hn g)
  left_inv := by
    rintro ⟨u, σ⟩
    apply Prod.ext
    · apply Units.ext
      rw [DiagramAut.domainScalarPart_val]
      simp
    · simp
  right_inv g := g.domainScalarPart_factor hS hgen hn
  map_mul' p q := ((scalarQuadraticAction R C S).noncommCoprod
    (galoisQuadraticAction R C S) (fun u σ ↦
      scalarQuadraticAut_commute R C S u (galoisQuadraticAut R C S σ))).map_mul p q

/-- The domain classification has the same primal scalar and direct Galois formula as the
local classification, without a localness hypothesis on the domain. -/
theorem coefficientDomainAutEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k) :
    coefficientDomainAutEquiv R C S hS hgen hn (u, σ) =
      scalarQuadraticAut R C S u * galoisQuadraticAut R C S σ := rfl

/-- The inverse returns the descended common scalar and the fraction-field Galois coordinate.
-/
theorem coefficientDomainAutEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (coefficientDomainAutEquiv R C S hS hgen hn).symm g =
      (g.domainScalarPart hS hgen hn, DiagramAut.domainToGalois R C S hS hgen hn g) := rfl

/-- Classification recovers the prescribed Galois coordinate. -/
@[simp]
theorem domainToGalois_coefficientDomainAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k) :
    DiagramAut.domainToGalois R C S hS hgen hn
      (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)) = σ := by
  simp [coefficientDomainAutEquiv_apply]

namespace DiagramAut

/-- Classification recovers the prescribed primal coefficient unit. -/
@[simp]
theorem domainScalarPart_coefficientDomainAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k) :
    (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).domainScalarPart hS hgen hn = u :=
  congrArg Prod.fst ((coefficientDomainAutEquiv R C S hS hgen hn).left_inv (u, σ))

/-- The fraction-field Galois coordinate has precisely the original literal scalar range
as its kernel. All stage and common-target equalities are descended, not assumed. -/
theorem ker_domainToGalois (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (domainToGalois R C S hS hgen hn).ker = scalarSubgroup R C S := by
  ext g
  change domainToGalois R C S hS hgen hn g = 1 ↔
    ∃ u : Rˣ, scalarQuadraticAut R C S u = g
  constructor
  · intro hg
    refine ⟨g.domainScalarPart hS hgen hn, ?_⟩
    have hf := g.domainScalarPart_factor hS hgen hn
    simpa only [hg, galoisQuadraticAut_one, mul_one] using hf
  · rintro ⟨u, rfl⟩
    exact domainToGalois_scalarQuadraticAut R C S hS hgen hn u

end DiagramAut

/-- Both original coordinates are recovered by the inverse domain classification. -/
theorem coefficientDomainAutEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k) :
    (coefficientDomainAutEquiv R C S hS hgen hn).symm
      (scalarQuadraticAut R C S u * galoisQuadraticAut R C S σ) = (u, σ) :=
  (coefficientDomainAutEquiv R C S hS hgen hn).left_inv (u, σ)

/-- The inverse domain coordinates reconstruct every actual diagram component. -/
theorem coefficientDomainAutEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    scalarQuadraticAut R C S (g.domainScalarPart hS hgen hn) *
      galoisQuadraticAut R C S (DiagramAut.domainToGalois R C S hS hgen hn g) = g :=
  g.domainScalarPart_factor hS hgen hn

/-- Every universal generator has the primal coefficient and covariant Galois label. -/
theorem coefficientDomainAutEquiv_universalEquiv_single (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).universalEquiv
      (Finsupp.single H 1) = (u : R) • Finsupp.single (σ • H) 1 := by
  rw [coefficientDomainAutEquiv_apply, DiagramAut.universalEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAut_universalEquiv_single, scalarQuadraticAut_universalEquiv_apply]

/-- Every original stage has the same primal coefficient at its transformed label. -/
theorem coefficientDomainAutEquiv_stageEquiv_single (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (B : C.Stage) (H : B.val.val) :
    (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).stageEquiv B
      (Finsupp.single H 1) = (u : R) • Finsupp.single (galoisLabelEquiv B.val σ H) 1 := by
  rw [coefficientDomainAutEquiv_apply, DiagramAut.stageEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAut_stageEquiv_single, scalarQuadraticAut_stageEquiv_apply]

/-- The original common target is acted on by the same descended primal unit. -/
@[simp]
theorem coefficientDomainAutEquiv_targetEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : Fin 2 →₀ R) :
    (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).targetEquiv x = (u : R) • x := by
  simp [coefficientDomainAutEquiv_apply]

/-- The actual marking square retains the same scalar on its one common source. -/
theorem coefficientDomainAutEquiv_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (B : C.Stage) (w : Marking S n) (hw : w.Available B.val.val) (x : Fin 2 →₀ R) :
    (coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).stageEquiv B
      (w.basisMap R hw x) = w.basisMap R hw ((u : R) • x) := by
  have he := LinearMap.congr_fun
    ((coefficientDomainAutEquiv R C S hS hgen hn (u, σ)).marking_naturality B w hw) x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    coefficientDomainAutEquiv_targetEquiv_apply] using he

/-- The actual full-dual action has inverse primal scalar and the SAME covariant label,
also over integral domains which are not local. -/
theorem coefficientDomainAutEquiv_dualAction_delta (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (u : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    DiagramAut.dualAction (coefficientDomainAutEquiv R C S hS hgen hn (u, σ))
      (Finsupp.lapply H) = (↑u⁻¹ : R) • Finsupp.lapply (σ • H) := by
  classical
  have hi : (coefficientDomainAutEquiv R C S hS hgen hn (u, σ))⁻¹ =
      coefficientDomainAutEquiv R C S hS hgen hn (u⁻¹, σ⁻¹) :=
    (map_inv (coefficientDomainAutEquiv R C S hS hgen hn) (u, σ)).symm
  apply Finsupp.lhom_ext
  intro K r
  rw [DiagramAut.dualAction_apply, DiagramAut.universalEquiv_symm, hi,
    show Finsupp.single K r = r • Finsupp.single K (1 : R) by simp, map_smul,
    coefficientDomainAutEquiv_universalEquiv_single]
  by_cases hK : K = σ • H
  · subst K
    simp [mul_comm]
  · have hinv : σ⁻¹ • K ≠ H := by
      intro he
      exact hK (inv_smul_eq_iff.mp he)
    simp [Ne.symm hK, Ne.symm hinv]

/-- On a local integral domain, the domain and local constructions are the same canonical
classification, as their actual forward scalar/Galois maps coincide. -/
theorem coefficientDomainAutEquiv_eq_quadraticAutEquiv [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    coefficientDomainAutEquiv R C S hS hgen hn = quadraticAutEquiv R C S hS hgen hn := by
  apply MulEquiv.ext
  intro p
  rfl

/-- The two Galois projections agree on the local/domain overlap, independently of the
fraction-field construction used by the domain proof. -/
theorem DiagramAut.domainToGalois_eq_toGalois [IsLocalRing R]
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut.domainToGalois R C S hS hgen hn = DiagramAut.toGalois R C S hS hgen hn := by
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨u, σ⟩, rfl⟩ := (coefficientDomainAutEquiv R C S hS hgen hn).surjective g
  rw [domainToGalois_coefficientDomainAutEquiv, coefficientDomainAutEquiv_eq_quadraticAutEquiv,
    toGalois_quadraticAutEquiv]

end OrlikSolomon.HyperplaneGT
