/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Field
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Action
public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Markings
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Extracting the base-field automorphism

The incidence permutation and its fixed marked frame give a field automorphism by C03.
Its action on actual coordinate levels fixes the marking constants; field generation then
descends it to the base field. The field action and its composition follow the coefficient
point action, with no field automorphism stored as diagram data.

The pure coordinate helpers concern actual coefficient points and coordinate hyperplanes
and use no coefficient-ring assumption. The diagram results retain the local-ring hypothesis.
Blueprint: C04 (`prop:c04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r

variable {k : Type u} [Field k] {n : ℕ}

private theorem fieldCoefficientPoint_mk (σ : k ≃+* k)
    (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    fieldCoefficientPoint σ (Projectivization.mk k a ha) =
      Projectivization.mk k (fun i ↦ σ (a i)) (coordinateMap_ne_zero σ ha) := rfl

private theorem fieldCoefficientPoint_one (p : Projectivization k (Fin (n + 1) → k)) :
    fieldCoefficientPoint (1 : k ≃+* k) p = p := by
  induction p using Projectivization.ind with | h a ha => rfl

private theorem fieldCoefficientPoint_mul (σ τ : k ≃+* k)
    (p : Projectivization k (Fin (n + 1) → k)) :
    fieldCoefficientPoint (σ * τ) p = fieldCoefficientPoint σ (fieldCoefficientPoint τ p) := by
  induction p using Projectivization.ind with | h a ha => rfl

private theorem fieldCoefficientPoint_injective (hn : 1 ≤ n) (σ τ : k ≃+* k)
    (he : ∀ p : Projectivization k (Fin (n + 1) → k),
      fieldCoefficientPoint σ p = fieldCoefficientPoint τ p) : σ = τ := by
  apply coordinateRingEquiv_eq_of_projective_action hn
  intro a ha
  simpa only [fieldCoefficientPoint_mk] using he (Projectivization.mk k a ha)

private theorem coordinateHyperplane_injective (i : Fin n) :
    Function.Injective (coordinateHyperplane (k := k) i) := by
  intro a b he
  have hm : Pi.single i a ∈ (coordinateHyperplane i a).val := by simp
  rw [he] at hm
  simpa only [mem_coordinateHyperplane, Pi.single_eq_same] using hm

private theorem fieldHyperplaneEquiv_coordinateHyperplane (σ : k ≃+* k)
    (i : Fin n) (a : k) :
    fieldHyperplaneEquiv σ (coordinateHyperplane i a) = coordinateHyperplane i (σ a) := by
  apply Subtype.ext
  ext x
  simp only [fieldHyperplaneEquiv_val, mem_fieldAffineSubspace, mem_coordinateHyperplane,
    fieldCoordinateAddEquiv_symm_apply]
  exact σ.symm_apply_eq

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k] {S : Set k₀}

private theorem coordinate_marking_zero (i : Fin n) (s : S) :
    (Marking.coordinate i s).fiber (k := k) 0 =
      coordinateHyperplane i (algebraMap k₀ k s.val) := by
  apply Subtype.ext
  ext x
  simp [Marking.function_coordinate, sub_eq_zero]

namespace DiagramAut

variable {R : Type r} [CommRing R] [IsLocalRing R] {C : CofinalSystem k₀ k n}

/-- The field automorphism extracted from the actual incidence action and the individually
fixed marking frame. No field automorphism is part of the diagram data.
Blueprint: C04 (`prop:c04`). -/
def fieldEquiv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) : k ≃+* k :=
  coordinateFieldEquiv (g.projectivePerm hS hn)
    (g.preservesProjectiveLines_projectivePerm hS hn) (g.projectivePerm_basisPoint hS hn) hn
    (fun i ↦ g.projectivePerm_differencePoint hS hn i.succ 0 i.succ_ne_zero)
    (fun i j hij ↦ g.projectivePerm_differencePoint hS hn i.succ j.succ
      (fun he ↦ (ne_of_lt hij) (Fin.succ_inj.mp he)))

/-- The extracted field automorphism computes the projective action at every point,
including the constant point and the hyperplane at infinity. Blueprint: C04 (`prop:c04`). -/
theorem projectivePerm_eq_fieldCoefficientPoint (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n)
    (p : Projectivization k (Fin (n + 1) → k)) :
    g.projectivePerm hS hn p = fieldCoefficientPoint (g.fieldEquiv hS hn) p := by
  induction p using Projectivization.ind with
  | h a ha =>
    exact coordinateFieldEquiv_mk (g.projectivePerm hS hn)
      (g.preservesProjectiveLines_projectivePerm hS hn) (g.projectivePerm_basisPoint hS hn) hn
      (fun i ↦ g.projectivePerm_differencePoint hS hn i.succ 0 i.succ_ne_zero)
      (fun i j hij ↦ g.projectivePerm_differencePoint hS hn i.succ j.succ
        (fun he ↦ (ne_of_lt hij) (Fin.succ_inj.mp he))) a ha

/-- On actual affine hyperplanes the recovered permutation is coordinatewise field action.
Blueprint: C04 (`prop:c04`). -/
theorem hyperplanePerm_eq_fieldHyperplaneEquiv (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (H : Hyperplane k n) :
    g.hyperplanePerm hS hn H = fieldHyperplaneEquiv (g.fieldEquiv hS hn) H := by
  apply coefficientPoint_injective
  rw [coefficientPoint_fieldHyperplaneEquiv,
    ← g.projectivePerm_eq_fieldCoefficientPoint hS hn, g.projectivePerm_coefficientPoint]

/-- Each marked coordinate level fixes its actual base-field constant under extraction.
Blueprint: the marked-constant clause of C04 (`prop:c04`). -/
theorem fieldEquiv_algebraMap_of_mem (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (s : k₀) (hs : s ∈ S) :
    g.fieldEquiv hS hn (algebraMap k₀ k s) = algebraMap k₀ k s := by
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  apply coordinateHyperplane_injective i
  rw [← fieldHyperplaneEquiv_coordinateHyperplane,
    ← g.hyperplanePerm_eq_fieldHyperplaneEquiv hS hn,
    ← coordinate_marking_zero i (⟨s, hs⟩ : S), g.hyperplanePerm_marking_zero]

/-- Generation by the marked constants, together with the prime field, forces the extracted
field automorphism to fix the whole base field. Blueprint: C04 (`prop:c04`). -/
theorem fieldEquiv_algebraMap (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (s : k₀) :
    g.fieldEquiv hS hn (algebraMap k₀ k s) = algebraMap k₀ k s := by
  have he : (g.fieldEquiv hS hn).toRingHom.comp (algebraMap k₀ k) = algebraMap k₀ k :=
    RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
      (fun t ht ↦ g.fieldEquiv_algebraMap_of_mem hS hn t ht)
  exact RingHom.congr_fun he s

/-- The identity diagram extracts the identity field automorphism. -/
@[simp]
theorem fieldEquiv_one (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (1 : DiagramAut R C S).fieldEquiv hS hn = 1 := by
  apply fieldCoefficientPoint_injective (le_trans (by decide : 1 ≤ 2) hn)
  intro p
  rw [← projectivePerm_eq_fieldCoefficientPoint, projectivePerm_one,
    Equiv.Perm.one_apply, fieldCoefficientPoint_one]

/-- Extraction respects composition in the same order as the recovered projective action. -/
@[simp]
theorem fieldEquiv_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    (g * h).fieldEquiv hS hn = g.fieldEquiv hS hn * h.fieldEquiv hS hn := by
  apply fieldCoefficientPoint_injective (le_trans (by decide : 1 ≤ 2) hn)
  intro p
  rw [← projectivePerm_eq_fieldCoefficientPoint, projectivePerm_mul_apply,
    fieldCoefficientPoint_mul, ← projectivePerm_eq_fieldCoefficientPoint,
    ← projectivePerm_eq_fieldCoefficientPoint]

/-- Extraction respects inversion. -/
@[simp]
theorem fieldEquiv_inv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) :
    g⁻¹.fieldEquiv hS hn = (g.fieldEquiv hS hn)⁻¹ := by
  have he := fieldEquiv_mul g⁻¹ g hS hn
  rw [inv_mul_cancel, fieldEquiv_one] at he
  exact mul_eq_one_iff_eq_inv.mp he.symm

/-- The Galois automorphism extracted from the marked quadratic diagram.
Base-field linearity follows from generation by the marking constants, and composition
follows from the actual projective action. Blueprint: C04 (`prop:c04`). -/
def toGalois (R : Type r) [CommRing R] [IsLocalRing R] (C : CofinalSystem k₀ k n)
    (S : Set k₀) (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    DiagramAut R C S →* (k ≃ₐ[k₀] k) where
  toFun g := { g.fieldEquiv hS hn with commutes' := g.fieldEquiv_algebraMap hS hgen hn }
  map_one' := by ext x; exact RingEquiv.congr_fun (fieldEquiv_one hS hn) x
  map_mul' g h := by ext x; exact RingEquiv.congr_fun (fieldEquiv_mul g h hS hn) x

/-- Forgetting base-field linearity recovers exactly the extracted ring equivalence. -/
@[simp]
theorem toGalois_toRingEquiv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (toGalois R C S hS hgen hn g).toRingEquiv = g.fieldEquiv hS hn := rfl

/-- The extracted Galois automorphism has exactly the recovered action on hyperplanes.
Blueprint: C04 (`prop:c04`). -/
theorem hyperplanePerm_toGalois (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (H : Hyperplane k n) :
    g.hyperplanePerm hS hn H = (toGalois R C S hS hgen hn g) • H :=
  g.hyperplanePerm_eq_fieldHyperplaneEquiv hS hn H

/-- Equality with any Galois automorphism is detected by its actual action on hyperplanes.
The coordinate hyperplanes prove faithfulness, with no additional classification hypothesis.
Blueprint: the recovered-action clause of C04 (`prop:c04`). -/
theorem toGalois_eq_iff_hyperplanePerm (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (σ : k ≃ₐ[k₀] k) :
    toGalois R C S hS hgen hn g = σ ↔ ∀ H, g.hyperplanePerm hS hn H = σ • H := by
  constructor
  · intro he H
    rw [g.hyperplanePerm_toGalois hS hgen hn, he]
  · intro he
    ext a
    let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
    have hh := he (coordinateHyperplane i a)
    change g.hyperplanePerm hS hn (coordinateHyperplane i a) =
      fieldHyperplaneEquiv σ.toRingEquiv (coordinateHyperplane i a) at hh
    rw [g.hyperplanePerm_eq_fieldHyperplaneEquiv, fieldHyperplaneEquiv_coordinateHyperplane,
      fieldHyperplaneEquiv_coordinateHyperplane] at hh
    exact coordinateHyperplane_injective i hh

/-- Trivial extracted Galois action is equivalent to trivial recovered label permutation.
This uses the actual coordinate hyperplanes, so no faithfulness hypothesis is added. -/
theorem toGalois_eq_one_iff_hyperplanePerm_eq_one (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    toGalois R C S hS hgen hn g = 1 ↔ g.hyperplanePerm hS hn = 1 := by
  rw [g.toGalois_eq_iff_hyperplanePerm hS hgen hn]
  constructor
  · intro he
    ext H
    simpa using he H
  · intro he H
    rw [he, Equiv.Perm.one_apply, one_smul]

end DiagramAut

end OrlikSolomon.HyperplaneGT
