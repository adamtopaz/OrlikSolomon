/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.DegreeOne
import Mathlib.Tactic.FinCases

/-!
# The actual alternating cup product and its complete kernel

Every actual degree-one class on an arrangement complement squares to zero, by transport
from the OS algebra through the existing structure theorem. This supplies alternation in
characteristic two, where graded commutativity alone would not suffice. The resulting
exterior-square map is actual multiplication on arbitrary degree-one classes. Its complete
kernel is the transported parallel-pair and guarded dependent-triple relation span of A02.

The common two-puncture target has its entire exterior square as kernel. All statements use
a supplied full geometric ordinary theory and construct no new realization.

Blueprint: the full cup-kernel comparison in A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u r b h

open CategoryTheory AlgebraicGeometry

namespace OrlikSolomon.HyperplaneGT.Cohomology

open OSAlgebra

variable {k : Type u} [Field k] {R : Type r} [CommRing R]
  {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Every actual degree-one class squares to zero, through the OS structure theorem.
This argument uses exterior squares themselves and remains valid with 2-torsion.

Blueprint: characteristic-two alternation in A04 (`thm:a04`). -/
theorem degreeOne_mul_self (A : Arrangement k V) (x : degreeOne T A) :
    (x : T.obj (D.complement A)) * (x : T.obj (D.complement A)) = 0 := by
  obtain ⟨c, rfl⟩ := (degreeOneEquiv T A).surjective x
  change T.realizationOverR A (osDegreeOneEquiv R A c) *
    T.realizationOverR A (osDegreeOneEquiv R A c) = 0
  rw [← map_mul]
  simpa only [coe_osDegreeOneEquiv_apply, map_zero] using
    congrArg (T.realizationOverR A)
      ((isExteriorFamily_generator R A).linearCombination_mul_self c)

/-- The actual bilinear product, viewed as a two-variable multilinear map into degree two. -/
def cupMultilinear (A : Arrangement k V) :
    (Fin 2 → degreeOne T A) →ₘₗ[R] degreeTwo T A where
  toFun v := ⟨(v 0 : T.obj (D.complement A)) * (v 1 : T.obj (D.complement A)), by
    have hm := SetLike.mul_mem_graded (v 0).property (v 1).property
    simpa [degreeOne, degreeTwo] using hm⟩
  map_update_add' v i x y := by
    apply Subtype.ext
    fin_cases i <;> simp [add_mul, mul_add]
  map_update_smul' v i c x := by
    apply Subtype.ext
    fin_cases i <;> simp

/-- Actual multiplication is alternating on degree one by the OS square-zero theorem. -/
def cupAlternating (A : Arrangement k V) :
    (degreeOne T A) [⋀^Fin 2]→ₗ[R] degreeTwo T A where
  __ := cupMultilinear T A
  map_eq_zero_of_eq' v i j hij hne := by
    apply Subtype.ext
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change (v 0 : T.obj (D.complement A)) * (v 1 : T.obj (D.complement A)) = 0
      change v 0 = v 1 at hij
      rw [congrArg Subtype.val hij]
      exact degreeOne_mul_self T A _
    · change (v 0 : T.obj (D.complement A)) * (v 1 : T.obj (D.complement A)) = 0
      change v 1 = v 0 at hij
      rw [congrArg Subtype.val hij]
      exact degreeOne_mul_self T A _
    · exact (hne rfl).elim

/-- The actual alternating cup product on all degree-one classes of an open complement.
It is the exterior lift of literal multiplication, with alternation proved above.

Blueprint: A04 (`thm:a04`). -/
def cupMap (A : Arrangement k V) :
    (⋀[R]^2 (degreeOne T A)) →ₗ[R] degreeTwo T A :=
  exteriorPower.alternatingMapLinearEquiv (cupAlternating T A)

/-- On an arbitrary exterior two-vector the cup map is the product of its two actual
cohomology classes. -/
@[simp]
theorem coe_cupMap_ιMulti (A : Arrangement k V) (v : Fin 2 → degreeOne T A) :
    (cupMap T A (exteriorPower.ιMulti R 2 v) : T.obj (D.complement A)) =
      (v 0 : T.obj (D.complement A)) * (v 1 : T.obj (D.complement A)) := by
  rw [cupMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- On a pair wedge the actual cup map is precisely multiplication. -/
theorem coe_cupMap_pair (A : Arrangement k V) (x y : degreeOne T A) :
    (cupMap T A (exteriorPower.ιMulti R 2 ![x, y]) : T.obj (D.complement A)) =
      (x : T.obj (D.complement A)) * (y : T.obj (D.complement A)) :=
  coe_cupMap_ιMulti T A ![x, y]

private theorem quotient_ι_eq_degreeOne (A : Arrangement k V) (x : A →₀ R) :
    quotient R A (ExteriorAlgebra.ι R x) = (osDegreeOneEquiv R A x : OSAlgebra R A) := by
  have he : (quotient R A).toLinearMap.comp (ExteriorAlgebra.ι R) =
      (degree R A 1).subtype.comp (osDegreeOneEquiv R A).toLinearMap := by
    ext H
    change quotient R A (ExteriorAlgebra.ι R (Finsupp.single H 1)) =
      (osDegreeOneEquiv R A (Finsupp.single H 1) : OSAlgebra R A)
    simpa only [exteriorGen, osDegreeOneEquiv_single, Submodule.coe_smul, one_smul] using
      quotient_exteriorGen R A H
  exact DFunLike.congr_fun he x

/-- In canonical coordinates the actual cup map is the actual exterior quotient, followed
by the existing degree-two structure theorem. -/
theorem cupMap_comp_coordinates (A : Arrangement k V) :
    (cupMap T A).comp (exteriorPower.map 2 (degreeOneEquiv T A).toLinearMap) =
      (T.degreeEquiv A 2).toLinearMap.comp (osExteriorSquareMap R A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply Subtype.ext
  change (cupMap T A (exteriorPower.map 2 (degreeOneEquiv T A).toLinearMap
      (exteriorPower.ιMulti R 2 v)) : T.obj (D.complement A)) =
    (T.degreeEquiv A 2 (osExteriorSquareMap R A (exteriorPower.ιMulti R 2 v)) :
      T.obj (D.complement A))
  rw [exteriorPower.map_apply_ιMulti, coe_cupMap_ιMulti,
    T.coe_degreeEquiv_apply, coe_osExteriorSquareMap_apply]
  simp [ExteriorAlgebra.ιMulti_apply, quotient_ι_eq_degreeOne, Matrix.vecTail]

/-- In canonical free coordinates, the preimage of the entire actual cup kernel is exactly
the geometric quadratic relation span. -/
theorem comap_cupKernel_eq {n : ℕ} (A : Arrangement k (Fin n → k)) :
    (LinearMap.ker (cupMap T A)).comap
      (exteriorPower.map 2 (degreeOneEquiv T A).toLinearMap) = quadraticRelationSpan R A := by
  calc
    _ = LinearMap.ker ((cupMap T A).comp
        (exteriorPower.map 2 (degreeOneEquiv T A).toLinearMap)) :=
      (LinearMap.ker_comp _ _).symm
    _ = LinearMap.ker ((T.degreeEquiv A 2).toLinearMap.comp
        (osExteriorSquareMap R A)) := congrArg LinearMap.ker (cupMap_comp_coordinates T A)
    _ = LinearMap.ker (osExteriorSquareMap R A) :=
      LinearEquiv.ker_comp (T.degreeEquiv A 2) _
    _ = quadraticRelationSpan R A := quadraticKernel_eq_span R A

/-- The complete actual cup kernel is the transported geometric quadratic relation span.
This is equality of whole submodules, without an assumption that higher OS relations are
generated in degree two.

Blueprint: A04 (`thm:a04`). -/
theorem cupKernel_eq {n : ℕ} (A : Arrangement k (Fin n → k)) :
    LinearMap.ker (cupMap T A) =
      (quadraticRelationSpan R A).map
        (exteriorPower.map 2 (degreeOneEquiv T A).toLinearMap) := by
  have hk := comap_cupKernel_eq T A
  rw [← hk, Submodule.map_comap_eq_of_surjective
    (exteriorPower.map_surjective (degreeOneEquiv T A).surjective)]

/-- The entire exterior square at the actual common target is its cup kernel, using the
existing full two-puncture OS presentation. -/
theorem target_cupKernel_eq_top :
    LinearMap.ker (cupMap T (twoPunctureArrangement k)) = ⊤ := by
  have hz : osExteriorSquareMap R (twoPunctureArrangement k) = 0 := by
    apply LinearMap.ext
    intro q
    obtain ⟨p, rfl⟩ := exteriorPower.map_surjective
      (Finsupp.domLCongr (twoPunctureLabelEquiv k) :
        (Fin 2 →₀ R) ≃ₗ[R] (twoPunctureArrangement k →₀ R)).surjective q
    exact DFunLike.congr_fun (markingTarget_exteriorSquareMap_eq_zero (k := k) R) p
  let e := exteriorPower.map 2 (degreeOneEquiv T (twoPunctureArrangement k)).toLinearMap
  have hs : Function.Surjective e :=
    exteriorPower.map_surjective (degreeOneEquiv T (twoPunctureArrangement k)).surjective
  have hc : (cupMap T (twoPunctureArrangement k)).comp e = 0 := by
    rw [cupMap_comp_coordinates, hz, LinearMap.comp_zero]
    rfl
  have hk : (LinearMap.ker (cupMap T (twoPunctureArrangement k))).comap e = ⊤ := by
    rw [← LinearMap.ker_comp, hc, LinearMap.ker_zero]
  have he := congrArg (Submodule.map e) hk
  rw [Submodule.map_comap_eq_of_surjective hs, Submodule.map_top,
    LinearMap.range_eq_top.mpr hs] at he
  exact he

/-- Every actual target degree-one cup product vanishes. This is a consequence of the full
target presentation, not an extra cohomology assumption. -/
theorem target_cupMap_eq_zero : cupMap T (twoPunctureArrangement k) = 0 :=
  LinearMap.ker_eq_top.mp (target_cupKernel_eq_top T)

/-- The actual cup product commutes with every actual scheme pullback between arrangement
complements, not just the selected inclusion and marking arrows. -/
theorem cupMap_naturality {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (A : Arrangement k V) (A' : Arrangement k W)
    (f : D.complement A ⟶ D.complement A') :
    (cupMap T A).comp (exteriorPower.map 2 (componentPull T f 1)) =
      (componentPull T f 2).comp (cupMap T A') := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply Subtype.ext
  change (cupMap T A (exteriorPower.map 2 (componentPull T f 1)
      (exteriorPower.ιMulti R 2 v)) : T.obj (D.complement A)) =
    T.pull f (cupMap T A' (exteriorPower.ιMulti R 2 v) : T.obj (D.complement A'))
  calc
    _ = (cupMap T A (exteriorPower.ιMulti R 2 ((componentPull T f 1) ∘ v)) :
        T.obj (D.complement A)) :=
      congrArg (fun q : ⋀[R]^2 (degreeOne T A) ↦
        (cupMap T A q : T.obj (D.complement A)))
        (exteriorPower.map_apply_ιMulti (componentPull T f 1) v)
    _ = (T.pull f (v 0)) * T.pull f (v 1) := coe_cupMap_ιMulti T A _
    _ = T.pull f ((v 0 : T.obj _) * (v 1 : T.obj _)) :=
      (map_mul (T.pull f) (v 0 : T.obj _) (v 1 : T.obj _)).symm
    _ = _ := congrArg (T.pull f) (coe_cupMap_ιMulti T A' v).symm

end OrlikSolomon.HyperplaneGT.Cohomology
