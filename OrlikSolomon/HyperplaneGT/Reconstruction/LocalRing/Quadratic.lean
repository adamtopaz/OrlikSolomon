/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Splitting
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Classification of the marked quadratic diagram over a local ring

Normalize an actual diagram automorphism by the inverse of its recovered Galois family
on the right. The scalar-kernel theorem supplies its unique common primal unit. The
resulting `quadraticAutEquiv` is a multiplicative equivalence from coefficient units times
base-field automorphisms to the original quadratic diagram group. Its inverse and both
inverse equations retain the one common marking target.

Blueprint: S03 (`thm:s03`). The supplied cofinal system requires no algebraicity or
perfectness hypothesis. Graded extension and scalar quotients belong to S04.
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable {R : Type w} [CommRing R] [IsLocalRing R]
variable {C : CofinalSystem k₀ k n} {S : Set k₀}

namespace DiagramAut

/-- The unique common primal unit after right normalization by the recovered Galois family.
Blueprint: the explicit inverse in S03 (`thm:s03`). -/
def scalarPart (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) : Rˣ :=
  Classical.choose (scalar_of_toGalois_eq_one
    (g * (galoisQuadraticAut R C S (toGalois R C S hS hgen hn g))⁻¹)
    hS hgen hn (by simp)).exists

private theorem scalarPart_spec (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (∀ (A : C.Stage) (x : A.val.val →₀ R),
      (g * (galoisQuadraticAut R C S (toGalois R C S hS hgen hn g))⁻¹).stageEquiv A x =
        (g.scalarPart hS hgen hn : R) • x) ∧
    ∀ x : Fin 2 →₀ R,
      (g * (galoisQuadraticAut R C S (toGalois R C S hS hgen hn g))⁻¹).targetEquiv x =
        (g.scalarPart hS hgen hn : R) • x :=
  Classical.choose_spec (scalar_of_toGalois_eq_one
    (g * (galoisQuadraticAut R C S (toGalois R C S hS hgen hn g))⁻¹)
    hS hgen hn (by simp)).exists

/-- Right normalization is precisely the actual common scalar family, as an equality of
diagram automorphisms rather than just their universal maps. Blueprint: S03 (`thm:s03`). -/
theorem scalarPart_normalized (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    g * (galoisQuadraticAut R C S (toGalois R C S hS hgen hn g))⁻¹ =
      scalarQuadraticAut R C S (g.scalarPart hS hgen hn) := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    exact (g.scalarPart_spec hS hgen hn).1 A
  · apply LinearEquiv.ext
    exact (g.scalarPart_spec hS hgen hn).2

/-- The unnormalized common target already acts by the recovered primal unit, because the
direct Galois factor has identity common target. -/
theorem scalarPart_targetEquiv_apply (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (x : Fin 2 →₀ R) :
    g.targetEquiv x = (g.scalarPart hS hgen hn : R) • x := by
  have he := congrArg (fun f : DiagramAut R C S ↦ f.targetEquiv x)
    (g.scalarPart_normalized hS hgen hn)
  simpa only [targetEquiv_mul, targetEquiv_inv, galoisQuadraticAut_targetEquiv,
    mul_apply_eq_comp, scalarQuadraticAut_targetEquiv_apply, LinearEquiv.one_eq_refl,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply] using he

/-- Evaluation at an ordered common-target generator computes the recovered primal unit. -/
theorem scalarPart_val (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (g.scalarPart hS hgen hn : R) = g.targetEquiv (Finsupp.single (0 : Fin 2) 1) 0 := by
  simpa using (congrArg (fun x : Fin 2 →₀ R ↦ x 0)
    (g.scalarPart_targetEquiv_apply hS hgen hn (Finsupp.single 0 1))).symm

end DiagramAut

variable (R C S)

/-- Every quadratic diagram family is the product of its unique primal scalar and its
recovered direct Galois family. This is the explicit right-inverse equation of S03. -/
theorem quadraticAutEquiv_right_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    scalarQuadraticAut R C S (g.scalarPart hS hgen hn) *
      galoisQuadraticAut R C S (DiagramAut.toGalois R C S hS hgen hn g) = g :=
  ((mul_inv_eq_iff_eq_mul).mp (g.scalarPart_normalized hS hgen hn)).symm

/-- The canonical classification of the actual marked quadratic diagram over a nonzero
local ring, with explicit common scalar and Galois inverse components.
Blueprint: S03 (`thm:s03`). -/
def quadraticAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (Rˣ × (k ≃ₐ[k₀] k)) ≃* DiagramAut R C S where
  toFun p := scalarQuadraticAut R C S p.1 * galoisQuadraticAut R C S p.2
  invFun g := (g.scalarPart hS hgen hn, DiagramAut.toGalois R C S hS hgen hn g)
  left_inv := by
    rintro ⟨a, σ⟩
    apply Prod.ext
    · apply Units.ext
      rw [DiagramAut.scalarPart_val]
      simp
    · simp
  right_inv := quadraticAutEquiv_right_inv R C S hS hgen hn
  map_mul' x y := ((scalarQuadraticAction R C S).noncommCoprod
    (galoisQuadraticAction R C S) (fun a σ ↦
      scalarQuadraticAut_commute R C S a (galoisQuadraticAut R C S σ))).map_mul x y

/-- The classification sends a unit and field automorphism to their actual scalar and
direct Galois families. -/
theorem quadraticAutEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    quadraticAutEquiv R C S hS hgen hn (a, σ) =
      scalarQuadraticAut R C S a * galoisQuadraticAut R C S σ := rfl

/-- The inverse classification retains the actual common-target scalar and extracted
base-field automorphism. -/
theorem quadraticAutEquiv_symm_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (g : DiagramAut R C S) :
    (quadraticAutEquiv R C S hS hgen hn).symm g =
      (g.scalarPart hS hgen hn, DiagramAut.toGalois R C S hS hgen hn g) := rfl

/-- The explicit left-inverse equation recovers both the original primal unit and the
original field automorphism. Blueprint: S03 (`thm:s03`). -/
theorem quadraticAutEquiv_left_inv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    (quadraticAutEquiv R C S hS hgen hn).symm
      (scalarQuadraticAut R C S a * galoisQuadraticAut R C S σ) = (a, σ) :=
  (quadraticAutEquiv R C S hS hgen hn).left_inv (a, σ)

/-- The Galois projection of the classification is its field-automorphism coordinate. -/
@[simp]
theorem toGalois_quadraticAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    DiagramAut.toGalois R C S hS hgen hn
      (quadraticAutEquiv R C S hS hgen hn (a, σ)) = σ := by
  simp [quadraticAutEquiv_apply]

namespace DiagramAut

/-- The primal scalar projection of the classification is its coefficient-unit coordinate. -/
@[simp]
theorem scalarPart_quadraticAutEquiv (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).scalarPart hS hgen hn = a := by
  exact congrArg Prod.fst ((quadraticAutEquiv R C S hS hgen hn).left_inv (a, σ))

variable {R C S}

/-- The identity family has common primal unit one. -/
@[simp]
theorem scalarPart_one (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (1 : DiagramAut R C S).scalarPart hS hgen hn = 1 :=
  congrArg Prod.fst ((quadraticAutEquiv R C S hS hgen hn).symm.map_one)

/-- The recovered common primal unit is multiplicative. -/
@[simp]
theorem scalarPart_mul (g h : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    (g * h).scalarPart hS hgen hn = g.scalarPart hS hgen hn * h.scalarPart hS hgen hn :=
  congrArg Prod.fst ((quadraticAutEquiv R C S hS hgen hn).symm.map_mul g h)

/-- Inverting a diagram inverts its recovered primal unit. -/
@[simp]
theorem scalarPart_inv (g : DiagramAut R C S) (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    g⁻¹.scalarPart hS hgen hn = (g.scalarPart hS hgen hn)⁻¹ :=
  congrArg Prod.fst ((quadraticAutEquiv R C S hS hgen hn).symm.map_inv g)

end DiagramAut

/-- The universal generator formula has primal coefficient unit and covariant Galois label. -/
theorem quadraticAutEquiv_universalEquiv_single (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).universalEquiv (Finsupp.single H 1) =
      (a : R) • Finsupp.single (σ • H) 1 := by
  rw [quadraticAutEquiv_apply, DiagramAut.universalEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAut_universalEquiv_single, scalarQuadraticAut_universalEquiv_apply]

/-- The finite-stage generator formula uses the restricted transformed label. -/
theorem quadraticAutEquiv_stageEquiv_single (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).stageEquiv A (Finsupp.single H 1) =
      (a : R) • Finsupp.single (galoisLabelEquiv A.val σ H) 1 := by
  rw [quadraticAutEquiv_apply, DiagramAut.stageEquiv_mul, mul_apply_eq_comp,
    galoisQuadraticAut_stageEquiv_single, scalarQuadraticAut_stageEquiv_apply]

/-- The one common target has exactly the primal scalar coordinate. -/
@[simp]
theorem quadraticAutEquiv_targetEquiv_apply (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (x : Fin 2 →₀ R) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).targetEquiv x = (a : R) • x := by
  simp [quadraticAutEquiv_apply]

/-- The actual whole marking square uses the same scalar on the ordered common target. -/
theorem quadraticAutEquiv_marking (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (A : C.Stage) (m : Marking S n) (hm : m.Available A.val.val) (x : Fin 2 →₀ R) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).stageEquiv A (m.basisMap R hm x) =
      m.basisMap R hm ((a : R) • x) := by
  have he := LinearMap.congr_fun
    ((quadraticAutEquiv R C S hS hgen hn (a, σ)).marking_naturality A m hm) x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    quadraticAutEquiv_targetEquiv_apply] using he

/-- Classification gives the same label permutation on primal generators and dual deltas. -/
theorem quadraticAutEquiv_hyperplanePerm (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).hyperplanePerm hS hn H = σ • H := by
  rw [(quadraticAutEquiv R C S hS hgen hn (a, σ)).hyperplanePerm_toGalois hS hgen hn,
    toGalois_quadraticAutEquiv]

/-- The recovered dual inertia unit is the inverse of the classification's primal unit. -/
theorem quadraticAutEquiv_hyperplaneUnit (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    (quadraticAutEquiv R C S hS hgen hn (a, σ)).hyperplaneUnit hS hn H = a⁻¹ := by
  classical
  have he := (quadraticAutEquiv R C S hS hgen hn (a, σ)).universalEquiv_single hS hn H
  rw [quadraticAutEquiv_universalEquiv_single, quadraticAutEquiv_hyperplanePerm] at he
  have ha : a = ((quadraticAutEquiv R C S hS hgen hn (a, σ)).hyperplaneUnit hS hn H)⁻¹ := by
    apply Units.ext
    simpa using congrArg (fun x : Hyperplane k n →₀ R ↦ x (σ • H)) he
  simpa only [inv_inv] using (congrArg Inv.inv ha).symm

/-- The actual contragredient action uses the inverse primal unit and the same Galois label.
Blueprint: the component formula in S03 (`thm:s03`). -/
theorem quadraticAutEquiv_dualAction_delta (hS : (0 : k₀) ∈ S)
    (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) (a : Rˣ) (σ : k ≃ₐ[k₀] k)
    (H : Hyperplane k n) :
    DiagramAut.dualAction (quadraticAutEquiv R C S hS hgen hn (a, σ)) (Finsupp.lapply H) =
      (↑a⁻¹ : R) • Finsupp.lapply (σ • H) := by
  rw [(quadraticAutEquiv R C S hS hgen hn (a, σ)).dualAction_delta hS hn H,
    quadraticAutEquiv_hyperplaneUnit,
    quadraticAutEquiv_hyperplanePerm]

end OrlikSolomon.HyperplaneGT
