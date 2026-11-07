/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import OrlikSolomon.DeRham.Cohomology.Basic
public import OrlikSolomon.DeRham.Cohomology.Degree
public import OrlikSolomon.DeRham.Cohomology.Point

/-!
# De Rham cohomology

This is the module to import for the de Rham cohomology algebra of a commutative algebra `A` over a
commutative ring `k`, with no smoothness hypothesis. It imports the files under `DeRham/Cohomology`,
whose headers list their results, and it compares the degree pieces with Mathlib's homology of the
de Rham complex `complex k A`.

## Summary of the design

The total algebra comes first, because forms and `d` do: `Forms k A` is one type and `d k` is an
operator on it. `cycles k A` is a `k`-subalgebra of forms, `boundaries k A` is a two-sided ideal of
`cycles k A`, and `Cohomology k A` is the quotient. `Cohomology.degree k A n` is then a submodule,
with no casts between degrees, and `Cohomology.degreeEquiv k A n` and `homologyIso k A n` say that
it is what the blueprint calls `H^n`. `Cohomology.grading k A p` is the same grading, indexed by
`ℤ`.

Write a class as `Cohomology.mk x hx`, with `hx : d k x = 0`, and use `Cohomology.mk_eq_zero_iff`,
`Cohomology.mk_eq_mk_iff` and `Cohomology.induction`. Do not unfold the quotient.

## Summary of the blueprint

Blueprint `def:dr-cohomology`:

* `H^n = ker d / im d`: `OrlikSolomon.DeRham.Cohomology.degree`,
  `OrlikSolomon.DeRham.Cohomology.degreeEquiv` and `OrlikSolomon.DeRham.homologyIso`;
* the unital `k`-algebra structure on the direct sum: `OrlikSolomon.DeRham.Cohomology`, with
  `OrlikSolomon.DeRham.Cohomology.mk_mul`, `OrlikSolomon.DeRham.Cohomology.mk_one` and
  `OrlikSolomon.DeRham.Cohomology.gradedAlgebraDegree`;
* graded commutativity: `OrlikSolomon.DeRham.Cohomology.isGradedCommutative_degree`;
* covariant functoriality: `OrlikSolomon.DeRham.Cohomology.map`,
  `OrlikSolomon.DeRham.Cohomology.map_id`, `OrlikSolomon.DeRham.Cohomology.map_comp`,
  `OrlikSolomon.DeRham.Cohomology.map_mem_degree` and `OrlikSolomon.DeRham.cohomologyFunctor`;
* boundaries are an ideal in the cycles: `OrlikSolomon.DeRham.cycles` and
  `OrlikSolomon.DeRham.boundaries`.

For `lem:dr-ordinary-basic`: `OrlikSolomon.DeRham.Cohomology.grading`,
`OrlikSolomon.DeRham.Cohomology.isGradedCommutative_grading`,
`OrlikSolomon.DeRham.Cohomology.isHomogeneousOfShift_map`,
`OrlikSolomon.DeRham.Cohomology.bijective_algebraMap_point` and
`OrlikSolomon.DeRham.Cohomology.eq_zero_of_mem_grading_point`.

For `thm:dr-homotopy`: `OrlikSolomon.DeRham.Cohomology.map_eq_map_of_homotopy`.

## Main definitions of this file

* `OrlikSolomon.DeRham.homologyIso k A n`: `H^n` is the homology in degree `n` of `complex k A`.

## Main results of this file

* `OrlikSolomon.DeRham.coe_homologyIso_hom_homologyπ`: that isomorphism sends the class of a cycle
  of `complex k A` to the class of the corresponding closed form.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace OrlikSolomon.DeRham

universe u v

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

section Homology

/-- The kernel of `d` out of degree `n` in the complex is the kernel of `powerD k A n`. -/
theorem ker_complex_d_hom (n : ℕ) :
    LinearMap.ker ((complex k A).d n (n + 1)).hom = LinearMap.ker (powerD k A n) := by
  rw [complex_d]
  rfl

/-- The image of `d` into degree `n` in the complex is `rangeD k A n`. -/
theorem range_complex_d_hom_prev (n : ℕ) :
    LinearMap.range ((complex k A).d ((ComplexShape.up ℕ).prev n) n).hom =
      Cohomology.rangeD k A n := by
  cases n with
  | zero =>
    rw [CochainComplex.prev_nat_zero, (complex k A).shape 0 0 (by simp)]
    exact LinearMap.range_zero
  | succ n =>
    rw [CochainComplex.prev_nat_succ, complex_d]
    rfl

/-- The short complex of `complex k A` at degree `n`, with the blueprint's zero map from degree `-1`
at `n = 0`. -/
abbrev scDegree (n : ℕ) : ShortComplex (ModuleCat.{v} k) :=
  (complex k A).sc' ((ComplexShape.up ℕ).prev n) n (n + 1)

/-- The homology of the short complex at degree `n` is the piece `H^n`. -/
def scDegreeHomologyEquiv (n : ℕ) :
    (scDegree k A n).moduleCatLeftHomologyData.H ≃ₗ[k] Cohomology.degree k A n :=
  (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (ker_complex_d_hom k A n)) (by
    ext z
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply]
    rw [← range_complex_d_hom_prev]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      refine ⟨(scDegree k A n).moduleCatToCycles y, ⟨y, rfl⟩, Subtype.ext ?_⟩
      exact hy)).trans (Cohomology.degreeEquiv k A n)

/-- The homology in degree `n` of the de Rham complex is the piece `H^n` of the total cohomology.
This says that `Cohomology.degree k A n` is what Mathlib's homology computes.

Blueprint: `def:dr-cohomology`. -/
def homologyIso (n : ℕ) : (complex k A).homology n ≅ ModuleCat.of k (Cohomology.degree k A n) :=
  (complex k A).homologyIsoSc' _ n (n + 1) rfl (CochainComplex.next ℕ n) ≪≫
    (scDegree k A n).moduleCatHomologyIso ≪≫ (scDegreeHomologyEquiv k A n).toModuleIso

/-- The form underlying a cycle of `complex k A`. -/
def formOfCycle (n : ℕ) (z : (complex k A).cycles n) : Forms k A :=
  Subtype.val (p := (· ∈ ⋀[A]^n Ω[A⁄k])) (((complex k A).iCycles n).hom z)

/-- A cycle of `complex k A` is a closed form. -/
theorem d_formOfCycle (n : ℕ) (z : (complex k A).cycles n) : d k (formOfCycle k A n z) = 0 := by
  have h := (complex k A).iCycles_d n (n + 1)
  rw [complex_d] at h
  exact congrArg Subtype.val congr(($h).hom z)

/-- `homologyIso` sends the homology class of a cycle of `complex k A` to the class of that closed
form. So it is the identification of the two descriptions of `H^n`, not merely some isomorphism.

Blueprint: `def:dr-cohomology`. -/
theorem coe_homologyIso_hom_homologyπ (n : ℕ) (z : (complex k A).cycles n) :
    (((homologyIso k A n).hom.hom (((complex k A).homologyπ n).hom z) :
        Cohomology.degree k A n) : Cohomology k A) =
      Cohomology.mk (formOfCycle k A n z) (d_formOfCycle k A n z) := by
  have h₁ : (complex k A).homologyπ n ≫ (homologyIso k A n).hom =
      ((complex k A).cyclesIsoSc' _ n (n + 1) rfl (CochainComplex.next ℕ n)).hom ≫
        (scDegree k A n).moduleCatCyclesIso.hom ≫
          (scDegree k A n).moduleCatLeftHomologyData.π ≫
            (scDegreeHomologyEquiv k A n).toModuleIso.hom := by
    simp only [homologyIso, Iso.trans_hom]
    rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.π_moduleCatCyclesIso_hom_assoc]
  have hi := (scDegree k A n).moduleCatCyclesIso_hom_i
  have hc := (complex k A).cyclesIsoSc'_hom_iCycles _ n (n + 1) rfl (CochainComplex.next ℕ n)
  have h₂ : (((scDegree k A n).moduleCatCyclesIso.hom.hom
      (((complex k A).cyclesIsoSc' _ n (n + 1) rfl (CochainComplex.next ℕ n)).hom.hom z)).1 :
        (complex k A).X n) = ((complex k A).iCycles n).hom z :=
    congr(($hi).hom
      (((complex k A).cyclesIsoSc' _ n (n + 1) rfl (CochainComplex.next ℕ n)).hom.hom z)).trans
      congr(($hc).hom z)
  refine (congrArg Subtype.val congr(($h₁).hom z)).trans ?_
  exact Cohomology.mk_congr (congrArg (Subtype.val (p := (· ∈ ⋀[A]^n Ω[A⁄k]))) h₂) _

end Homology

end OrlikSolomon.DeRham
