/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Hyperplane
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Coefficients of affine hyperplane equations

An affine form on `Fin n → k` is represented by its constant coefficient followed by the
coefficients of its linear part. This gives the coefficient-point description of affine
hyperplanes as projective points other than the constant form.

## Main definitions and results

* `affineCoefficients` and `coefficientForm` extract and evaluate coefficient tuples.
* `affineCoefficientsEquiv` identifies affine forms with their coefficient vectors.
* `coefficientPointEquiv` identifies hyperplanes with nonconstant projective coefficient points.

Blueprint: `lem:g01`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u

section AffineForms

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Affine forms are linearly equivalent to their constant and normal coefficient tuples.

Blueprint: `lem:g01`. -/
noncomputable def affineCoefficientsEquiv :
    ((Fin n → k) →ᵃ[k] k) ≃ₗ[k] (Fin (n + 1) → k) :=
  AffineMap.toConstProdLinearMap k ≪≫ₗ
    (LinearEquiv.refl k k).prodCongr (Module.piEquiv (Fin n) k k).symm ≪≫ₗ
    Fin.consLinearEquiv k (fun _ ↦ k)

/-- The constant coefficient followed by the normal coefficients of an affine form.

Blueprint: `lem:g01`. -/
noncomputable def affineCoefficients : ((Fin n → k) →ᵃ[k] k) →ₗ[k] (Fin (n + 1) → k) :=
  affineCoefficientsEquiv.toLinearMap

@[simp]
theorem affineCoefficients_zero (f : (Fin n → k) →ᵃ[k] k) :
    affineCoefficients f 0 = f 0 := by
  simp [affineCoefficients, affineCoefficientsEquiv]

@[simp]
theorem affineCoefficients_succ (f : (Fin n → k) →ᵃ[k] k) (i : Fin n) :
    affineCoefficients f i.succ = f.linear (Pi.single i 1) := by
  simp [affineCoefficients, affineCoefficientsEquiv, Module.piEquiv]

/-- The affine form with the specified constant and normal coefficients.

Blueprint: `lem:g01`. -/
noncomputable def coefficientForm : (Fin (n + 1) → k) →ₗ[k] ((Fin n → k) →ᵃ[k] k) :=
  affineCoefficientsEquiv.symm.toLinearMap

@[simp]
theorem coefficientForm_apply (a : Fin (n + 1) → k) (x : Fin n → k) :
    coefficientForm a x = a 0 + ∑ i : Fin n, a i.succ * x i := by
  simp [coefficientForm, affineCoefficientsEquiv, Module.piEquiv_apply_apply,
    Fin.tail, mul_comm, add_comm]

@[simp]
theorem coefficientForm_linear_apply (a : Fin (n + 1) → k) (x : Fin n → k) :
    (coefficientForm a).linear x = ∑ i : Fin n, a i.succ * x i := by
  simp [coefficientForm, affineCoefficientsEquiv, Module.piEquiv_apply_apply, Fin.tail, mul_comm]

@[simp]
theorem affineCoefficients_coefficientForm (a : Fin (n + 1) → k) :
    affineCoefficients (coefficientForm a) = a := by
  exact affineCoefficientsEquiv.apply_symm_apply a

@[simp]
theorem coefficientForm_affineCoefficients (f : (Fin n → k) →ᵃ[k] k) :
    coefficientForm (affineCoefficients f) = f := by
  exact affineCoefficientsEquiv.symm_apply_apply f

@[simp]
theorem affineCoefficientsEquiv_apply (f : (Fin n → k) →ᵃ[k] k) :
    affineCoefficientsEquiv f = affineCoefficients f := rfl

@[simp]
theorem affineCoefficientsEquiv_symm_apply (a : Fin (n + 1) → k) :
    affineCoefficientsEquiv.symm a = coefficientForm a := rfl

/-- The linear part vanishes exactly when all normal coefficients vanish. -/
theorem linear_eq_zero_iff_coefficients (f : (Fin n → k) →ᵃ[k] k) :
    f.linear = 0 ↔ ∀ i : Fin n, affineCoefficients f i.succ = 0 := by
  constructor
  · intro h i
    simp [h]
  · intro h
    apply LinearMap.ext
    intro x
    rw [← coefficientForm_affineCoefficients f, coefficientForm_linear_apply]
    simp [h]

/-- A coefficient form is nonconstant exactly when some normal coefficient is nonzero. -/
theorem coefficientForm_linear_ne_zero_iff (a : Fin (n + 1) → k) :
    (coefficientForm a).linear ≠ 0 ↔ ∃ i : Fin n, a i.succ ≠ 0 := by
  rw [ne_eq, linear_eq_zero_iff_coefficients, affineCoefficients_coefficientForm, not_forall]

end AffineForms

variable {k : Type u} [Field k] {n : ℕ}

/-- An affine hyperplane equation has a nonzero normal coefficient. -/
theorem exists_normal_coefficient_ne_zero_of_isEquation
    {H : AffineSubspace k (Fin n → k)} {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    ∃ i : Fin n, affineCoefficients f i.succ ≠ 0 :=
  not_forall.mp (mt (linear_eq_zero_iff_coefficients f).mpr hf.linear_ne_zero)

/-- Nonconstant coefficient tuples define the same hyperplane exactly when they differ by
a nonzero scalar. -/
theorem zeroLocus_coefficientForm_eq_iff {a b : Fin (n + 1) → k}
    (ha : ∃ i : Fin n, a i.succ ≠ 0) (hb : ∃ i : Fin n, b i.succ ≠ 0) :
    zeroLocus (coefficientForm a) = zeroLocus (coefficientForm b) ↔
      ∃ c : kˣ, b = (c : k) • a := by
  constructor
  · intro h
    have hf := isEquation_zeroLocus ((coefficientForm_linear_ne_zero_iff a).mpr ha)
    have hg : IsEquation (coefficientForm b) (zeroLocus (coefficientForm a)) :=
      ⟨(coefficientForm_linear_ne_zero_iff b).mpr hb, h.symm⟩
    obtain ⟨c, hc, -⟩ := hf.existsUnique_smul hg
    refine ⟨c, ?_⟩
    simpa only [map_smul, affineCoefficients_coefficientForm] using
      congrArg affineCoefficients hc
  · rintro ⟨c, rfl⟩
    rw [map_smul, zeroLocus_smul c.ne_zero]

/-- The type of affine hyperplanes in the coordinate space. It is the existing affine-subspace
type with its hyperplane certificate, rather than a new incidence structure.

Blueprint: `lem:g01`. -/
@[instance_reducible]
def Hyperplane (k : Type u) [Field k] (n : ℕ) :=
  {H : AffineSubspace k (Fin n → k) // IsHyperplane H}

/-- The coefficient point of a nonzero constant form, omitted from affine hyperplane space.

Blueprint: `lem:g01`. -/
def constantPoint (k : Type u) [Field k] (n : ℕ) :
    Projectivization k (Fin (n + 1) → k) :=
  Projectivization.mk k (Fin.cons 1 (fun _ ↦ 0)) (by
    intro h
    have := congrFun h 0
    simp at this)

/-- A projective coefficient tuple is the constant point exactly when all normal coefficients
vanish. -/
theorem mk_eq_constantPoint_iff {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    Projectivization.mk k a ha = constantPoint k n ↔ ∀ i : Fin n, a i.succ = 0 := by
  change Projectivization.mk k a ha =
    Projectivization.mk k (Fin.cons 1 (fun _ ↦ 0)) _ ↔ _
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩ i
    have := congrFun hc i.succ
    simpa using this.symm
  · intro h
    refine ⟨a 0, ?_⟩
    funext i
    cases i using Fin.cases <;> simp [h]

/-- The coefficient vector of a hyperplane equation is nonzero. -/
theorem affineCoefficients_ne_zero_of_isEquation
    {H : AffineSubspace k (Fin n → k)} {f : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H) :
    affineCoefficients f ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_normal_coefficient_ne_zero_of_isEquation hf
  intro h
  exact hi (congrFun h i.succ)

/-- The projective coefficient point of an affine hyperplane, independent of its equation.

Blueprint: `lem:g01`. -/
@[implicit_reducible]
noncomputable def coefficientPoint (H : Hyperplane k n) :
    Projectivization k (Fin (n + 1) → k) :=
  Projectivization.mk k (affineCoefficients (equation H.val))
    (affineCoefficients_ne_zero_of_isEquation (isEquation_equation H.property))

/-- Any equation computes the same projective coefficient point. -/
theorem coefficientPoint_eq_mk (H : Hyperplane k n) {f : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H.val) :
    coefficientPoint H = Projectivization.mk k (affineCoefficients f)
      (affineCoefficients_ne_zero_of_isEquation hf) := by
  obtain ⟨c, hc, -⟩ := (isEquation_equation H.property).existsUnique_smul hf
  apply Eq.symm
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  exact ⟨(c : k), by rw [hc, map_smul]⟩

/-- A hyperplane coefficient point is never the point of constant equations. -/
theorem coefficientPoint_ne_constantPoint (H : Hyperplane k n) :
    coefficientPoint H ≠ constantPoint k n := by
  intro h
  obtain ⟨i, hi⟩ :=
    exists_normal_coefficient_ne_zero_of_isEquation (isEquation_equation H.property)
  exact hi ((mk_eq_constantPoint_iff _).mp h i)

/-- The hyperplane defined by a projective coefficient point other than the constant point.

Blueprint: `lem:g01`. -/
noncomputable def hyperplaneOfCoefficientPoint (p : Projectivization k (Fin (n + 1) → k))
    (hp : p ≠ constantPoint k n) : Hyperplane k n :=
  ⟨zeroLocus (coefficientForm p.rep), isHyperplane_zeroLocus_iff.mpr (by
    intro hlin
    have hnormal : ∀ i : Fin n, p.rep i.succ = 0 := by
      simpa only [affineCoefficients_coefficientForm] using
        (linear_eq_zero_iff_coefficients (coefficientForm p.rep)).mp hlin
    exact hp (p.mk_rep.symm.trans ((mk_eq_constantPoint_iff p.rep_ne_zero).mpr hnormal)))⟩

/-- The representative coefficient form is an equation for its associated hyperplane. -/
theorem isEquation_hyperplaneOfCoefficientPoint
    (p : Projectivization k (Fin (n + 1) → k)) (hp : p ≠ constantPoint k n) :
    IsEquation (coefficientForm p.rep) (hyperplaneOfCoefficientPoint p hp).val :=
  ⟨isHyperplane_zeroLocus_iff.mp (hyperplaneOfCoefficientPoint p hp).property, rfl⟩

/-- The inverse construction computes the zero locus of any representative tuple, without
depending on the representative chosen by projectivization. -/
theorem hyperplaneOfCoefficientPoint_mk (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (hp : Projectivization.mk k a ha ≠ constantPoint k n) :
    (hyperplaneOfCoefficientPoint (Projectivization.mk k a ha) hp).val =
      zeroLocus (coefficientForm a) := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k a ha
  change (c : k) • a = (Projectivization.mk k a ha).rep at hc
  change zeroLocus (coefficientForm (Projectivization.mk k a ha).rep) = _
  rw [← hc, map_smul, zeroLocus_smul c.ne_zero]

@[simp]
theorem coefficientPoint_hyperplaneOfCoefficientPoint
    (p : Projectivization k (Fin (n + 1) → k)) (hp : p ≠ constantPoint k n) :
    coefficientPoint (hyperplaneOfCoefficientPoint p hp) = p := by
  rw [coefficientPoint_eq_mk _ (isEquation_hyperplaneOfCoefficientPoint p hp)]
  simp only [affineCoefficients_coefficientForm, Projectivization.mk_rep]

@[simp]
theorem hyperplaneOfCoefficientPoint_coefficientPoint (H : Hyperplane k n) :
    hyperplaneOfCoefficientPoint (coefficientPoint H)
      (coefficientPoint_ne_constantPoint H) = H := by
  apply Subtype.ext
  change (hyperplaneOfCoefficientPoint
    (Projectivization.mk k (affineCoefficients (equation H.val)) _) _).val = H.val
  rw [hyperplaneOfCoefficientPoint_mk, coefficientForm_affineCoefficients]
  exact (isEquation_equation H.property).zeroLocus_eq

/-- Affine hyperplanes are exactly the projective coefficient points other than the constant
point. Both directions are independent of the chosen equations.

Blueprint: `lem:g01`. -/
noncomputable def coefficientPointEquiv (k : Type u) [Field k] (n : ℕ) :
    Hyperplane k n ≃ {p : Projectivization k (Fin (n + 1) → k) // p ≠ constantPoint k n} where
  toFun H := ⟨coefficientPoint H, coefficientPoint_ne_constantPoint H⟩
  invFun p := hyperplaneOfCoefficientPoint p.val p.property
  left_inv := hyperplaneOfCoefficientPoint_coefficientPoint
  right_inv p := Subtype.ext (coefficientPoint_hyperplaneOfCoefficientPoint p.val p.property)

@[simp]
theorem coe_coefficientPointEquiv_apply (H : Hyperplane k n) :
    (coefficientPointEquiv k n H).val = coefficientPoint H := rfl

@[simp]
theorem coefficientPointEquiv_symm_apply
    (p : {p : Projectivization k (Fin (n + 1) → k) // p ≠ constantPoint k n}) :
    (coefficientPointEquiv k n).symm p = hyperplaneOfCoefficientPoint p.val p.property := rfl

end OrlikSolomon.HyperplaneGT
