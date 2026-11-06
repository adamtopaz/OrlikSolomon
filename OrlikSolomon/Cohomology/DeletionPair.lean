/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Logarithms
public import OrlikSolomon.Geometry.Deletion

/-!
# The exact sequence of a deletion

For a hyperplane `H` of an arrangement `𝒜`, with deletion `𝒜'` and restriction `𝒜''`, this file
gives the fields of `OrdinaryTheory` at the deletion pair the types that do not mention the pair:
the residue `T.deletionResidue hH : C(U_𝒜) →ₗ[B] C(U_𝒜'')` and the Gysin map
`T.deletionGysin hH : C(U_𝒜'') →ₗ[B] C(U_𝒜')`, with the pullbacks along `complementRestriction` and
`complementInclusion`. It then says what these maps do to logarithms of equations.

The sequence here is the long exact one. This file does not prove `lem:ses`, since the surjectivity
of `i^*` that it needs comes from the induction in `Cohomology/Deletion`.

## Working with deletion pairs

Write `T.deletionResidue hH` and `T.deletionGysin hH`, never `T.residue (deletionPair 𝒜 hH hf)`. The
object `(deletionPair 𝒜 hH hf).closed` is `complement (𝒜.restriction H)` only at default
transparency, so `rw` and `simp` cannot work under `T.residue (deletionPair 𝒜 hH hf)`; see
`Cohomology/Axioms` and the implementation notes in `Geometry/SmoothAlg`.

**The maps do not depend on an equation.** A pair needs a chosen equation of `H`, but these wrappers
take none, and `residue_deletionPair` and `gysin_deletionPair` show that they are the maps of the
pair of every equation. The wrappers are `@[no_expose]`, so no importer can see which equation is
used to define them. To specialize a result about a general pair `P`, apply it at
`deletionPair 𝒜 hH hf` and rewrite with `residue_deletionPair` and `deletionPair_eqnUnit`, as the
proof of `deletionResidue_logClass` does.

## Main definitions

* `OrdinaryTheory.deletionResidue`, `OrdinaryTheory.deletionGysin`: the residue and Gysin maps of a
  deletion.

## Main results

* `OrdinaryTheory.residue_deletionPair`, `OrdinaryTheory.gysin_deletionPair`: they are the maps of
  the deletion pair of every equation of `H`.
* `OrdinaryTheory.exact_deletionGysin_map`, `OrdinaryTheory.exact_map_deletionResidue`,
  `OrdinaryTheory.exact_deletionResidue_deletionGysin`: the long exact sequence.
* `OrdinaryTheory.deletionResidue_mul_map`: the boundary projection formula.
* `OrdinaryTheory.deletionResidue_logClass`, `OrdinaryTheory.deletionResidue_logClass_mul`:
  `lem:log-residue`, for every equation of `H`.
* `OrdinaryTheory.exists_eq_map_complementInclusion_add_logClass_mul`: the step of `thm:generation`
  that subtracts the product with `[f_H]`.
* `OrdinaryTheory.surjective_deletionResidue_of_surjective_map`,
  `OrdinaryTheory.deletionGysin_eq_zero_of_surjective_map`,
  `OrdinaryTheory.injective_map_complementInclusion_of_surjective_map`: the content of `lem:ses`,
  given that `i^*` is surjective.
* The restriction of old logarithms, for every equation:
  - `OrdinaryTheory.map_complementRestriction_logClass_of_inf_eq_bot`: an old hyperplane missing `H`
    restricts to zero;
  - `OrdinaryTheory.map_complementRestriction_logClass_of_comap_eq`: an old hyperplane restricts to
    the logarithm of its retained hyperplane;
  - `OrdinaryTheory.map_complementRestriction_logClass_of_inf_eq`: two old hyperplanes with the same
    trace on `H` restrict to the same class.

## Blueprint

`lem:log-residue` for deletion pairs, and the deletion pairs of `def:cohomology`, items C4 and C5.
This is the input to `lem:restriction-surj`, `lem:ses`, `thm:generation` and `thm:cohom-basis`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.SmoothAlg OrlikSolomon.DivisorPair

universe u v w z

namespace OrlikSolomon

namespace OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {𝒜 : Arrangement k V} {H K : AffineSubspace k V} {f g : V →ᵃ[k] k}

/-- The deletion pair that defines the wrappers. Which equation it uses cannot be seen from outside,
by `residue_deletionPair` and `gysin_deletionPair`. -/
private abbrev chosenPair (hH : H ∈ 𝒜) : DivisorPair k :=
  deletionPair 𝒜 hH (isEquation_equation (𝒜.isHyperplane hH))

/-- The residue `C(U_𝒜) → C(U_𝒜'')` of a hyperplane `H` of `𝒜`, typed so that `rw` and `simp` work.
It does not depend on an equation of `H`: by `residue_deletionPair`, it is the residue of the
deletion pair of every equation. -/
@[no_expose]
def deletionResidue (hH : H ∈ 𝒜) :
    T.C.obj (complement 𝒜) →ₗ[B] T.C.obj (complement (𝒜.restriction H)) :=
  T.residue (chosenPair hH)

/-- The Gysin map `C(U_𝒜'') → C(U_𝒜')` of a hyperplane `H` of `𝒜`, typed so that `rw` and `simp`
work. It does not depend on an equation of `H`: by `gysin_deletionPair`, it is the Gysin map of the
deletion pair of every equation. -/
@[no_expose]
def deletionGysin (hH : H ∈ 𝒜) :
    T.C.obj (complement (𝒜.restriction H)) →ₗ[B] T.C.obj (complement (𝒜.deletion H)) :=
  T.gysin (chosenPair hH)

/-- The residue of a deletion pair does not depend on the equation, by naturality along the
transverse morphism `deletionPairHom`, which is the identity on all three rings. -/
lemma residue_deletionPair_eq (hH : H ∈ 𝒜) (hf : IsEquation f H) (hg : IsEquation g H) :
    T.residue (deletionPair 𝒜 hH hf) = T.residue (deletionPair 𝒜 hH hg) :=
  LinearMap.ext fun x ↦ by
    have h := T.residue_map (deletionPairHom 𝒜 hH hf hg) x
    have hid {A : SmoothAlg k} (y : T.C.obj A) : T.C.map (𝟙 A) y = y := by simp
    exact (hid _).symm.trans (h.symm.trans (congrArg _ (hid x)))

/-- The Gysin map of a deletion pair does not depend on the equation, by naturality along the
transverse morphism `deletionPairHom`. -/
lemma gysin_deletionPair_eq (hH : H ∈ 𝒜) (hf : IsEquation f H) (hg : IsEquation g H) :
    T.gysin (deletionPair 𝒜 hH hf) = T.gysin (deletionPair 𝒜 hH hg) :=
  LinearMap.ext fun x ↦ by
    have h := T.gysin_map (deletionPairHom 𝒜 hH hf hg) x
    have hid {A : SmoothAlg k} (y : T.C.obj A) : T.C.map (𝟙 A) y = y := by simp
    exact (hid _).symm.trans (h.symm.trans (congrArg _ (hid x)))

/-- The wrapper is the residue of the deletion pair of every equation of `H`. To specialize a result
about a general pair `P`, apply it at `deletionPair 𝒜 hH hf`, rewrite with this lemma and
`deletionPair_eqnUnit`, and finish with `exact`, as in the proof of `deletionResidue_logClass`. -/
lemma residue_deletionPair (hH : H ∈ 𝒜) (hf : IsEquation f H) :
    T.residue (deletionPair 𝒜 hH hf) = T.deletionResidue hH :=
  T.residue_deletionPair_eq hH hf _

/-- The wrapper is the Gysin map of the deletion pair of every equation of `H`. -/
lemma gysin_deletionPair (hH : H ∈ 𝒜) (hf : IsEquation f H) :
    T.gysin (deletionPair 𝒜 hH hf) = T.deletionGysin hH :=
  T.gysin_deletionPair_eq hH hf _

/-- The residue of a deletion has shift `(-1, -1)`. Blueprint: `lem:ses`. -/
lemma isHomogeneousOfShift_deletionResidue (hH : H ∈ 𝒜) :
    IsHomogeneousOfShift (T.grading (complement 𝒜)) (T.grading (complement (𝒜.restriction H)))
      (-1, -1) (T.deletionResidue hH) :=
  T.isHomogeneousOfShift_residue (chosenPair hH)

/-- The Gysin map of a deletion has shift `(2, 1)`. -/
lemma isHomogeneousOfShift_deletionGysin (hH : H ∈ 𝒜) :
    IsHomogeneousOfShift (T.grading (complement (𝒜.restriction H)))
      (T.grading (complement (𝒜.deletion H))) (2, 1) (T.deletionGysin hH) :=
  T.isHomogeneousOfShift_gysin (chosenPair hH)

/-- Exactness of the deletion sequence at `C(U_𝒜')`. -/
lemma exact_deletionGysin_map (hH : H ∈ 𝒜) :
    Function.Exact (T.deletionGysin hH) (T.C.map (complementInclusion (𝒜.deletion_le H))) :=
  T.exact_gysin_map (chosenPair hH)

/-- Exactness of the deletion sequence at `C(U_𝒜)`. -/
lemma exact_map_deletionResidue (hH : H ∈ 𝒜) :
    Function.Exact (T.C.map (complementInclusion (𝒜.deletion_le H))) (T.deletionResidue hH) :=
  T.exact_map_residue (chosenPair hH)

/-- Exactness of the deletion sequence at `C(U_𝒜'')`. -/
lemma exact_deletionResidue_deletionGysin (hH : H ∈ 𝒜) :
    Function.Exact (T.deletionResidue hH) (T.deletionGysin hH) :=
  T.exact_residue_gysin (chosenPair hH)

/-- Classes pulled back from `U_𝒜'` have zero residue. -/
@[simp] lemma deletionResidue_map_complementInclusion (hH : H ∈ 𝒜)
    (x : T.C.obj (complement (𝒜.deletion H))) :
    T.deletionResidue hH (T.C.map (complementInclusion (𝒜.deletion_le H)) x) = 0 :=
  (T.exact_map_deletionResidue hH).apply_apply_eq_zero x

/-- Gysin classes vanish on `U_𝒜`. -/
@[simp] lemma map_complementInclusion_deletionGysin (hH : H ∈ 𝒜)
    (x : T.C.obj (complement (𝒜.restriction H))) :
    T.C.map (complementInclusion (𝒜.deletion_le H)) (T.deletionGysin hH x) = 0 :=
  (T.exact_deletionGysin_map hH).apply_apply_eq_zero x

@[simp] lemma deletionGysin_deletionResidue (hH : H ∈ 𝒜) (x : T.C.obj (complement 𝒜)) :
    T.deletionGysin hH (T.deletionResidue hH x) = 0 :=
  (T.exact_deletionResidue_deletionGysin hH).apply_apply_eq_zero x

/-- Coefficients have zero residue. -/
@[simp] lemma deletionResidue_algebraMap (hH : H ∈ 𝒜) (b : B) :
    T.deletionResidue hH (algebraMap B (T.C.obj (complement 𝒜)) b) = 0 :=
  T.residue_algebraMap (chosenPair hH) b

@[simp] lemma deletionResidue_one (hH : H ∈ 𝒜) : T.deletionResidue hH 1 = 0 :=
  T.residue_one (chosenPair hH)

/-- Homogeneous extraction at `im j^* = ker r`, for a deletion. -/
lemma exists_mem_grading_map_complementInclusion_eq (hH : H ∈ 𝒜) {i : ℤ × ℤ}
    {x : T.C.obj (complement 𝒜)} (hx : x ∈ T.grading (complement 𝒜) i)
    (h : T.deletionResidue hH x = 0) :
    ∃ y ∈ T.grading (complement (𝒜.deletion H)) i,
      T.C.map (complementInclusion (𝒜.deletion_le H)) y = x :=
  T.exists_mem_grading_map_j_eq (chosenPair hH) hx h

/-- Homogeneous extraction at `im r = ker g`, for a deletion. -/
lemma exists_mem_grading_deletionResidue_eq (hH : H ∈ 𝒜) {i j : ℤ × ℤ} (hij : i + (-1, -1) = j)
    {x : T.C.obj (complement (𝒜.restriction H))}
    (hx : x ∈ T.grading (complement (𝒜.restriction H)) j) (h : T.deletionGysin hH x = 0) :
    ∃ y ∈ T.grading (complement 𝒜) i, T.deletionResidue hH y = x :=
  T.exists_mem_grading_residue_eq (chosenPair hH) hij hx h

/-- The boundary projection formula of a deletion. Blueprint: item C5 of `def:cohomology`. -/
lemma deletionResidue_mul_map (hH : H ∈ 𝒜) {α : T.C.obj (complement 𝒜)}
    (hα : α ∈ T.grading (complement 𝒜) (1, 1)) (β : T.C.obj (complement (𝒜.deletion H))) :
    T.deletionResidue hH (α * T.C.map (complementInclusion (𝒜.deletion_le H)) β) =
      T.deletionResidue hH α * T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) β :=
  T.residue_mul_map (chosenPair hH) hα β

/-! ### Logarithms -/

/-- The residue of the logarithm of an equation of `H` is `1`, for every equation.

Blueprint: `lem:log-residue`. -/
@[simp] theorem deletionResidue_logClass (hH : H ∈ 𝒜) (hf : IsEquation f H) :
    T.deletionResidue hH (T.logClass (complementUnit 𝒜 f (hf.covers hH))) = 1 := by
  have h := T.residue_logClass_eqnUnit (deletionPair 𝒜 hH hf)
  rw [T.residue_deletionPair hH hf, deletionPair_eqnUnit] at h
  exact h

/-- `r([f] j^* β) = i^* β`, for every equation `f` of `H`. The logarithm must stay on the left:
moving it introduces a sign.

Blueprint: `lem:log-residue`. -/
@[simp] theorem deletionResidue_logClass_mul (hH : H ∈ 𝒜) (hf : IsEquation f H)
    (β : T.C.obj (complement (𝒜.deletion H))) :
    T.deletionResidue hH (T.logClass (complementUnit 𝒜 f (hf.covers hH)) *
        T.C.map (complementInclusion (𝒜.deletion_le H)) β) =
      T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) β := by
  rw [T.deletionResidue_mul_map hH (T.logClass_mem_grading _), T.deletionResidue_logClass hH hf,
    one_mul]

/-- The logarithm of a unit of `U_𝒜'` has zero residue, because it is pulled back from `U_𝒜'`. So do
the logarithms of all old equations. -/
@[simp] theorem deletionResidue_logClass_complementUnit (hH : H ∈ 𝒜)
    (hg : (𝒜.deletion H).Covers (zeroLocus g)) :
    T.deletionResidue hH (T.logClass (complementUnit 𝒜 g (hg.mono (𝒜.deletion_le H)))) = 0 := by
  rw [← mapUnits_complementInclusion_complementUnit (𝒜.deletion_le H) hg, ← map_logClass,
    deletionResidue_map_complementInclusion]

/-- Every class on `U_𝒜` is `j^* a + [f] j^* β`, for any equation `f` of `H` and any `β` restricting
to its residue. This is the step of `thm:generation` that subtracts the product with `[f_H]`. -/
theorem exists_eq_map_complementInclusion_add_logClass_mul (hH : H ∈ 𝒜) (hf : IsEquation f H)
    {x : T.C.obj (complement 𝒜)} {β : T.C.obj (complement (𝒜.deletion H))}
    (hβ : T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) β = T.deletionResidue hH x) :
    ∃ a, x = T.C.map (complementInclusion (𝒜.deletion_le H)) a +
      T.logClass (complementUnit 𝒜 f (hf.covers hH)) *
        T.C.map (complementInclusion (𝒜.deletion_le H)) β := by
  have h : T.deletionResidue hH (x - T.logClass (complementUnit 𝒜 f (hf.covers hH)) *
      T.C.map (complementInclusion (𝒜.deletion_le H)) β) = 0 := by
    rw [map_sub, T.deletionResidue_logClass_mul hH hf, hβ, sub_self]
  obtain ⟨a, ha⟩ := (T.exact_map_deletionResidue hH _).1 h
  exact ⟨a, by rw [ha, sub_add_cancel]⟩

/-- If `i^*` is surjective, then so is the residue: `[f] j^* β` lifts `i^* β`. This is the first
step of `lem:ses`. -/
theorem surjective_deletionResidue_of_surjective_map (hH : H ∈ 𝒜)
    (hi : Function.Surjective (T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)))) :
    Function.Surjective (T.deletionResidue hH) :=
  T.surjective_residue_of_surjective_map_i (P := chosenPair hH) hi

/-- If `i^*` is surjective, then the Gysin map of the deletion vanishes. This is where the vanishing
of Gysin maps comes from in `lem:ses`. -/
theorem deletionGysin_eq_zero_of_surjective_map (hH : H ∈ 𝒜)
    (hi : Function.Surjective (T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)))) :
    T.deletionGysin hH = 0 :=
  T.gysin_eq_zero_of_surjective_map_i (P := chosenPair hH) hi

/-- If `i^*` is surjective, then `j^*` is injective. Blueprint: `lem:ses`. -/
theorem injective_map_complementInclusion_of_surjective_map (hH : H ∈ 𝒜)
    (hi : Function.Surjective (T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)))) :
    Function.Injective (T.C.map (complementInclusion (𝒜.deletion_le H))) :=
  T.injective_map_j_of_surjective_map_i (P := chosenPair hH) hi

/-- The empty case: the logarithm of any equation of an old hyperplane missing `H` restricts to
zero, since the equation restricts to a nonzero constant.

Blueprint: `lem:restriction-surj`. -/
theorem map_complementRestriction_logClass_of_inf_eq_bot (hH : IsHyperplane H)
    (hK : K ∈ 𝒜.deletion H) (hf : IsEquation f K) (hbot : H ⊓ K = ⊥) :
    T.C.map (complementRestriction 𝒜 hH)
      (T.logClass (complementUnit (𝒜.deletion H) f (hf.covers hK))) = 0 := by
  obtain ⟨c, hc⟩ := exists_mapUnits_complementRestriction_eq_constUnit hH hK hf hbot
  rw [T.map_logClass, hc]
  exact T.logClass_units_map_algebraMap c

/-- The retained case: the logarithm of any equation of an old hyperplane with trace `L` restricts
to the logarithm of any equation of `L`, since equations differ by a nonzero constant.

Blueprint: `lem:restriction-surj`. -/
theorem map_complementRestriction_logClass_of_comap_eq (hH : IsHyperplane H)
    (hK : K ∈ 𝒜.deletion H) (hf : IsEquation f K) {L : AffineSubspace k H.direction}
    (hL : L ∈ 𝒜.restriction H) (hKL : K.comap (chart H) = L) {g : H.direction →ᵃ[k] k}
    (hg : IsEquation g L) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.logClass (complementUnit (𝒜.deletion H) f (hf.covers hK))) =
      T.logClass (complementUnit (𝒜.restriction H) g (hg.covers hL)) := by
  obtain ⟨c, hc⟩ := exists_mapUnits_complementRestriction_eq_constUnit_mul hH hK hf hL hKL hg
  rw [T.map_logClass, hc]
  exact T.logClass_units_map_algebraMap_mul c _

/-- The duplicate case: old hyperplanes with the same intersection with `H` have the same restricted
logarithm, for any of their equations.

Blueprint: `lem:restriction-surj`. -/
theorem map_complementRestriction_logClass_of_inf_eq (hH : IsHyperplane H)
    {K₁ K₂ : AffineSubspace k V} (hK₁ : K₁ ∈ 𝒜.deletion H) (hK₂ : K₂ ∈ 𝒜.deletion H)
    {f₁ f₂ : V →ᵃ[k] k} (hf₁ : IsEquation f₁ K₁) (hf₂ : IsEquation f₂ K₂) (h : H ⊓ K₁ = H ⊓ K₂) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.logClass (complementUnit (𝒜.deletion H) f₁ (hf₁.covers hK₁))) =
      T.C.map (complementRestriction 𝒜 hH)
        (T.logClass (complementUnit (𝒜.deletion H) f₂ (hf₂.covers hK₂))) := by
  obtain ⟨c, hc⟩ :=
    exists_mapUnits_complementRestriction_eq_constUnit_mul_of_inf_eq hH hK₁ hK₂ hf₁ hf₂ h
  rw [T.map_logClass, T.map_logClass, hc]
  exact T.logClass_units_map_algebraMap_mul c _

end OrdinaryTheory

end OrlikSolomon
