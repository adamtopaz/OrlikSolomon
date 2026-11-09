/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Graded
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Faithful restriction from the full graded to the quadratic diagram

Canonical degree-one coordinates turn every full graded diagram automorphism into a
quadratic one. The full degree-two kernel is preserved because the actual exterior quotient
commutes with the algebra automorphism. Faithfulness uses generation of each entire algebra
by its degree-one generators, including the single common target.

Blueprint: A03 (`def:a03`). This restriction does not claim that arbitrary quadratic
automorphisms extend to the full algebras.
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Module OSAlgebra

variable {k : Type v} [Field k] (R : Type r) [CommRing R]

section Arrangement

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (𝒜 : Arrangement k V) (g : OSAlgebra R 𝒜 ≃ₐ[R] OSAlgebra R 𝒜)
  (hg : (degree R 𝒜 1).map g.toLinearMap = degree R 𝒜 1)

/-- A degree-one-preserving presentation automorphism, in the canonical free-module
coordinates. This construction needs no condition on the higher-degree generators. -/
def osDegreeOneAut : (𝒜 →₀ R) ≃ₗ[R] (𝒜 →₀ R) :=
  (osDegreeOneEquiv R 𝒜).trans
    ((g.toLinearEquiv.ofSubmodules _ _ hg).trans (osDegreeOneEquiv R 𝒜).symm)

/-- The canonical degree-one coordinates intertwine the restricted and full automorphisms.
-/
theorem osDegreeOneAut_apply (x : 𝒜 →₀ R) :
    (osDegreeOneEquiv R 𝒜 (osDegreeOneAut R 𝒜 g hg x) : OSAlgebra R 𝒜) =
      g (osDegreeOneEquiv R 𝒜 x) := by
  simp [osDegreeOneAut]

private theorem quotient_ι_eq_degreeOne (x : 𝒜 →₀ R) :
    quotient R 𝒜 (ExteriorAlgebra.ι R x) = (osDegreeOneEquiv R 𝒜 x : OSAlgebra R 𝒜) := by
  have h : (quotient R 𝒜).toLinearMap.comp (ExteriorAlgebra.ι R) =
      (degree R 𝒜 1).subtype.comp (osDegreeOneEquiv R 𝒜).toLinearMap := by
    ext H
    change quotient R 𝒜 (ExteriorAlgebra.ι R (Finsupp.single H 1)) =
      (osDegreeOneEquiv R 𝒜 (Finsupp.single H 1) : OSAlgebra R 𝒜)
    simpa only [exteriorGen, osDegreeOneEquiv_single, Submodule.coe_smul, one_smul] using
      quotient_exteriorGen R 𝒜 H
  exact DFunLike.congr_fun h x

/-- The exterior lift of the restricted map commutes with the actual whole OS quotient. -/
theorem osDegreeOneAut_quotient :
    (quotient R 𝒜).comp (ExteriorAlgebra.map (osDegreeOneAut R 𝒜 g hg).toLinearMap) =
      g.toAlgHom.comp (quotient R 𝒜) := by
  apply exteriorAlgHom_ext
  intro H
  change quotient R 𝒜 (ExteriorAlgebra.map (osDegreeOneAut R 𝒜 g hg).toLinearMap
    (exteriorGen R H)) = g (generator R 𝒜 H)
  rw [show ExteriorAlgebra.map (osDegreeOneAut R 𝒜 g hg).toLinearMap (exteriorGen R H) =
      ExteriorAlgebra.ι R (osDegreeOneAut R 𝒜 g hg (Finsupp.single H 1)) by
    simp [exteriorGen]]
  rw [quotient_ι_eq_degreeOne, osDegreeOneAut_apply]
  simp

end Arrangement

/-- The restricted map preserves the whole explicit quadratic relation submodule by equality.
This follows from A02's actual kernel, rather than an assumption that the algebra is quadratic.
-/
theorem osDegreeOneAut_map_quadraticRelationSpan {n : ℕ}
    (𝒜 : Arrangement k (Fin n → k)) (g : OSAlgebra R 𝒜 ≃ₐ[R] OSAlgebra R 𝒜)
    (hg : (degree R 𝒜 1).map g.toLinearMap = degree R 𝒜 1) :
    (quadraticRelationSpan R 𝒜).map
      (exteriorPower.map 2 (osDegreeOneAut R 𝒜 g hg).toLinearMap) =
        quadraticRelationSpan R 𝒜 := by
  let f := exteriorPower.map 2 (osDegreeOneAut R 𝒜 g hg).toLinearMap
  have hmem (x : ⋀[R]^2 (𝒜 →₀ R)) :
      x ∈ quadraticRelationSpan R 𝒜 ↔ quotient R 𝒜 x.val = 0 := by
    rw [← quadraticKernel_eq_span, LinearMap.mem_ker]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · exact fun h ↦ Subtype.ext h
  have hiff (x : ⋀[R]^2 (𝒜 →₀ R)) :
      f x ∈ quadraticRelationSpan R 𝒜 ↔ x ∈ quadraticRelationSpan R 𝒜 := by
    rw [hmem, hmem]
    have heq := DFunLike.congr_fun (osDegreeOneAut_quotient R 𝒜 g hg) x.val
    change quotient R 𝒜 (ExteriorAlgebra.map (osDegreeOneAut R 𝒜 g hg).toLinearMap x.val) =
      g (quotient R 𝒜 x.val) at heq
    change quotient R 𝒜 (exteriorPower.map 2 (osDegreeOneAut R 𝒜 g hg).toLinearMap x) = 0 ↔ _
    rw [exteriorPower.coe_map, heq]
    constructor
    · exact fun h ↦ g.injective (h.trans (map_zero g).symm)
    · intro h
      simpa only [map_zero] using congrArg g h
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hiff x).mpr hx
  · intro y hy
    obtain ⟨x, rfl⟩ := exteriorPower.map_surjective (n := 2)
      (osDegreeOneAut R 𝒜 g hg).surjective y
    exact ⟨x, (hiff x).mp hy, rfl⟩

variable {k₀ : Type u} [Field k₀] [Algebra k₀ k] {n : ℕ}
  {C : CofinalSystem k₀ k n} {S : Set k₀}

namespace GradedDiagramAut

variable {R}

/-- The free-module equivalence obtained from the degree-one part of a full stage map. -/
def stageLinearEquiv (g : GradedDiagramAut R C S) (𝒜 : C.Stage) :
    (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) :=
  osDegreeOneAut R 𝒜.val.val (g.stageEquiv 𝒜) (g.map_degree 𝒜 1)

/-- The common target equivalence in its ordered two-generator coordinates. -/
def targetLinearEquiv (g : GradedDiagramAut R C S) :
    (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R) :=
  (markingTargetDegreeOneEquiv (k := k) R).trans
    ((g.targetEquiv.toLinearEquiv.ofSubmodules _ _ (g.map_target_degree 1)).trans
      (markingTargetDegreeOneEquiv (k := k) R).symm)

/-- Stage restriction agrees on every degree-one vector with the full algebra action. -/
theorem stageLinearEquiv_apply (g : GradedDiagramAut R C S) (𝒜 : C.Stage)
    (x : 𝒜.val.val →₀ R) :
    (osDegreeOneEquiv R 𝒜.val.val (g.stageLinearEquiv 𝒜 x) : OSAlgebra R 𝒜.val.val) =
      g.stageEquiv 𝒜 (osDegreeOneEquiv R 𝒜.val.val x) := osDegreeOneAut_apply _ _ _ _ _

/-- Target restriction agrees on every ordered degree-one vector with the full target action.
-/
theorem targetLinearEquiv_apply (g : GradedDiagramAut R C S) (x : Fin 2 →₀ R) :
    (markingTargetDegreeOneEquiv (k := k) R (g.targetLinearEquiv x) : OSAlgebra R _) =
      g.targetEquiv (markingTargetDegreeOneEquiv (k := k) R x) := by
  simp [targetLinearEquiv]

/-- The degree-one stage restrictions commute with the literal free-module inclusions. -/
theorem stageLinearEquiv_inclusion_naturality (g : GradedDiagramAut R C S)
    {𝒜 ℬ : C.Stage} (h : 𝒜 ≤ ℬ) :
    (g.stageLinearEquiv ℬ).toLinearMap.comp
        (Finsupp.lmapDomain R R (Arrangement.inclusion h)) =
      (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp
        (g.stageLinearEquiv 𝒜).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (osDegreeOneEquiv R ℬ.val.val).injective
  apply Subtype.ext
  have hi (y : 𝒜.val.val →₀ R) :
      (osDegreeOneEquiv R ℬ.val.val (Finsupp.lmapDomain R R (Arrangement.inclusion h) y) :
        OSAlgebra R ℬ.val.val) = OSAlgebra.map R h (osDegreeOneEquiv R 𝒜.val.val y) := by
    simpa only [coe_osDegreeOneMap_apply] using
      congrArg Subtype.val (osDegreeOneEquiv_naturality R h y)
  change (osDegreeOneEquiv R ℬ.val.val (g.stageLinearEquiv ℬ
    (Finsupp.lmapDomain R R (Arrangement.inclusion h) x)) : OSAlgebra R ℬ.val.val) =
      osDegreeOneEquiv R ℬ.val.val
        (Finsupp.lmapDomain R R (Arrangement.inclusion h) (g.stageLinearEquiv 𝒜 x))
  rw [stageLinearEquiv_apply, hi, hi, stageLinearEquiv_apply]
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
    DFunLike.congr_fun (g.inclusion_naturality h)
      (osDegreeOneEquiv R 𝒜.val.val x : OSAlgebra R 𝒜.val.val)

/-- The restricted marking square uses the same restricted common target at every stage. -/
theorem stageLinearEquiv_marking_naturality (g : GradedDiagramAut R C S) (𝒜 : C.Stage)
    (w : Marking S n) (hw : w.Available 𝒜.val.val) :
    (g.stageLinearEquiv 𝒜).toLinearMap.comp (w.basisMap R hw) =
      (w.basisMap R hw).comp g.targetLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (osDegreeOneEquiv R 𝒜.val.val).injective
  apply Subtype.ext
  change (osDegreeOneEquiv R 𝒜.val.val (g.stageLinearEquiv 𝒜 (w.basisMap R hw x)) :
    OSAlgebra R 𝒜.val.val) = osDegreeOneEquiv R 𝒜.val.val
      (w.basisMap R hw (g.targetLinearEquiv x))
  rw [stageLinearEquiv_apply, w.osMap_degreeOne R hw, w.osMap_degreeOne R hw,
    targetLinearEquiv_apply]
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
    DFunLike.congr_fun (g.marking_naturality 𝒜 w hw)
      (markingTargetDegreeOneEquiv (k := k) R x : OSAlgebra R (twoPunctureArrangement k))

variable (R C S)

/-- Restriction of a full graded diagram automorphism to its canonical degree-one coordinates.
The actual degree-two quotient kernel gives preservation of the whole quadratic relation span.
Blueprint: A03 (`def:a03`). -/
def toQuadratic : GradedDiagramAut R C S →* DiagramAut R C S where
  toFun g := DiagramAut.ofEquivs g.stageLinearEquiv g.targetLinearEquiv
    (fun 𝒜 ↦ osDegreeOneAut_map_quadraticRelationSpan R 𝒜.val.val
      (g.stageEquiv 𝒜) (g.map_degree 𝒜 1))
    (fun _ _ h ↦ g.stageLinearEquiv_inclusion_naturality h)
    (fun 𝒜 w hw ↦ g.stageLinearEquiv_marking_naturality 𝒜 w hw)
  map_one' := by
    apply DiagramAut.ext
    · intro 𝒜
      apply LinearEquiv.ext
      intro x
      apply (osDegreeOneEquiv R 𝒜.val.val).injective
      apply Subtype.ext
      change (osDegreeOneEquiv R 𝒜.val.val
        ((1 : GradedDiagramAut R C S).stageLinearEquiv 𝒜 x) : OSAlgebra R 𝒜.val.val) =
          osDegreeOneEquiv R 𝒜.val.val x
      rw [stageLinearEquiv_apply]
      rfl
    · apply LinearEquiv.ext
      intro x
      apply (markingTargetDegreeOneEquiv (k := k) R).injective
      apply Subtype.ext
      change (markingTargetDegreeOneEquiv (k := k) R
        ((1 : GradedDiagramAut R C S).targetLinearEquiv x) :
          OSAlgebra R (twoPunctureArrangement k)) =
          (markingTargetDegreeOneEquiv (k := k) R x : OSAlgebra R (twoPunctureArrangement k))
      rw [targetLinearEquiv_apply]
      rfl
  map_mul' g h := by
    apply DiagramAut.ext
    · intro 𝒜
      apply LinearEquiv.ext
      intro x
      apply (osDegreeOneEquiv R 𝒜.val.val).injective
      apply Subtype.ext
      change (osDegreeOneEquiv R 𝒜.val.val ((g * h).stageLinearEquiv 𝒜 x) :
          OSAlgebra R 𝒜.val.val) =
        osDegreeOneEquiv R 𝒜.val.val (g.stageLinearEquiv 𝒜 (h.stageLinearEquiv 𝒜 x))
      rw [stageLinearEquiv_apply, stageLinearEquiv_apply, stageLinearEquiv_apply]
      rfl
    · apply LinearEquiv.ext
      intro x
      apply (markingTargetDegreeOneEquiv (k := k) R).injective
      apply Subtype.ext
      change (markingTargetDegreeOneEquiv (k := k) R ((g * h).targetLinearEquiv x) :
          OSAlgebra R (twoPunctureArrangement k)) =
        (markingTargetDegreeOneEquiv (k := k) R (g.targetLinearEquiv (h.targetLinearEquiv x)) :
          OSAlgebra R (twoPunctureArrangement k))
      rw [targetLinearEquiv_apply, targetLinearEquiv_apply, targetLinearEquiv_apply]
      rfl

variable {R C S}

@[simp]
theorem stageEquiv_toQuadratic (g : GradedDiagramAut R C S) (𝒜 : C.Stage) :
    (toQuadratic R C S g).stageEquiv 𝒜 = g.stageLinearEquiv 𝒜 := rfl

@[simp]
theorem targetEquiv_toQuadratic (g : GradedDiagramAut R C S) :
    (toQuadratic R C S g).targetEquiv = g.targetLinearEquiv := rfl

/-- Degree-one restriction loses no full diagram automorphism, since every stage algebra and
the common target are generated in degree one. This is faithfulness, not an extension theorem.
-/
theorem toQuadratic_injective : Function.Injective (toQuadratic R C S) := by
  intro g h heq
  apply GradedDiagramAut.ext
  · intro 𝒜
    apply AlgEquiv.coe_toAlgHom_injective
    apply OSAlgebra.algHom_ext
    intro H
    have hc := congrArg (fun f : DiagramAut R C S ↦ f.stageEquiv 𝒜) heq
    change g.stageLinearEquiv 𝒜 = h.stageLinearEquiv 𝒜 at hc
    have hh := congrArg (fun f : (𝒜.val.val →₀ R) ≃ₗ[R] (𝒜.val.val →₀ R) ↦
      (osDegreeOneEquiv R 𝒜.val.val (f (Finsupp.single H 1)) : OSAlgebra R 𝒜.val.val)) hc
    rw [stageLinearEquiv_apply, stageLinearEquiv_apply] at hh
    simpa using hh
  · apply AlgEquiv.coe_toAlgHom_injective
    apply OSAlgebra.algHom_ext
    intro H
    obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
    have hc := congrArg (fun f : DiagramAut R C S ↦ f.targetEquiv) heq
    change g.targetLinearEquiv = h.targetLinearEquiv at hc
    have hh := congrArg (fun f : (Fin 2 →₀ R) ≃ₗ[R] (Fin 2 →₀ R) ↦
      (markingTargetDegreeOneEquiv (k := k) R (f (Finsupp.single a 1)) :
        OSAlgebra R (twoPunctureArrangement k))) hc
    rw [targetLinearEquiv_apply, targetLinearEquiv_apply] at hh
    simpa using hh

end GradedDiagramAut

end OrlikSolomon.HyperplaneGT
