/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Axioms
public import OrlikSolomon.Geometry.Deletion

/-!
# The exact sequence of a deletion

For a hyperplane `H` of an arrangement `𝒜`, with deletion `𝒜'` and restriction `𝒜''`, this file
gives the fields of `OrdinaryTheory` at the deletion pair the types that do not mention the pair:
the residue `T.deletionResidue hH : C(U_𝒜) →ₗ[B] C(U_𝒜'')` and the Gysin map
`T.deletionGysin hH : C(U_𝒜'') →ₗ[B] C(U_𝒜')`, with the pullbacks along `complementRestriction` and
`complementInclusion`. It proves nothing about arrangements beyond the axioms, and in particular it
does not prove `lem:ses`: the sequence here is the long exact one.

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
proof of `deletionResidue_map_gmHom` does.

## Main definitions

* `OrdinaryTheory.deletionResidue`, `OrdinaryTheory.deletionGysin`: the residue and Gysin maps of a
  deletion.

## Main results

* `OrdinaryTheory.residue_deletionPair`, `OrdinaryTheory.gysin_deletionPair`: they are the maps of
  the deletion pair of every equation of `H`.
* `OrdinaryTheory.exact_deletionGysin_map`, `OrdinaryTheory.exact_map_deletionResidue`,
  `OrdinaryTheory.exact_deletionResidue_deletionGysin`: the long exact sequence.
* `OrdinaryTheory.deletionResidue_mul_map`: the boundary projection formula.
* `OrdinaryTheory.deletionResidue_map_gmHom`: residue naturality along any equation of `H`, the
  first half of `lem:log-residue`.

## Blueprint

The deletion pairs of `def:cohomology`, items C4 and C5. This is the input to `lem:log-residue`,
`lem:restriction-surj`, `lem:ses`, `thm:generation` and `thm:cohom-basis`.
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
  {𝒜 : Arrangement k V} {H : AffineSubspace k V} {f g : V →ᵃ[k] k}

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
about a general pair `P`, use it with `exact`, since `rw` cannot see through the types. -/
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

/-- The boundary projection formula of a deletion. Blueprint: `lem:log-residue`. -/
lemma deletionResidue_mul_map (hH : H ∈ 𝒜) {α : T.C.obj (complement 𝒜)}
    (hα : α ∈ T.grading (complement 𝒜) (1, 1)) (β : T.C.obj (complement (𝒜.deletion H))) :
    T.deletionResidue hH (α * T.C.map (complementInclusion (𝒜.deletion_le H)) β) =
      T.deletionResidue hH α * T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) β :=
  T.residue_mul_map (chosenPair hH) hα β

/-- Residue naturality along `z ↦ f`, for every equation `f` of `H`. This is the first half of
`lem:log-residue`, without the logarithm: the residue on `U_𝒜` of the pullback of a class on `𝔾ₘ`
along the unit of `f` is the pullback of its residue at the origin. -/
lemma deletionResidue_map_gmHom (hH : H ∈ 𝒜) (hf : IsEquation f H) (x : T.C.obj (gm k)) :
    T.deletionResidue hH (T.C.map (gmHom (complementUnit 𝒜 f (hf.covers hH))) x) =
      T.C.map (fromPoint (complement (𝒜.restriction H))) (T.stdResidue (point k) x) := by
  have h := T.residue_map_gmHom_eqnUnit (deletionPair 𝒜 hH hf) x
  rw [T.residue_deletionPair hH hf, deletionPair_eqnUnit] at h
  exact h

end OrdinaryTheory

end OrlikSolomon
