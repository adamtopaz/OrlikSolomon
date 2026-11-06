/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Grading.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Internal gradings on linear images

The image pieces of an internal grading form an internal grading on a surjective linear
image whenever the kernel is homogeneous. `linearImageDecomposition` constructs the
decomposition, and `decompose_linearImageGrading` computes its components.

This applies in particular to module quotients. The quotient map may be obtained by
restricting scalars from a larger coefficient ring; the construction keeps its actual target
type unchanged. Blueprint: the module cokernel in `def:lift-map`.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon

open DirectSum

variable {R ι M Q : Type*} [Ring R] [AddCommGroup M] [AddCommGroup Q]
  [Module R M] [Module R Q]

/-- The degree pieces on a linear image are the images of the original degree pieces. -/
def linearImageGrading (ℳ : ι → Submodule R M) (f : M →ₗ[R] Q) : ι → Submodule R Q :=
  fun i ↦ (ℳ i).map f

/-- A class in an image piece has a representative in the corresponding original piece. -/
theorem mem_linearImageGrading {ℳ : ι → Submodule R M} {f : M →ₗ[R] Q} {i : ι} {y : Q} :
    y ∈ linearImageGrading ℳ f i ↔ ∃ x ∈ ℳ i, f x = y :=
  Submodule.mem_map

/-- The image map preserves the degree pieces. -/
theorem map_mem_linearImageGrading {ℳ : ι → Submodule R M} {f : M →ₗ[R] Q}
    {i : ι} {x : M} (hx : x ∈ ℳ i) : f x ∈ linearImageGrading ℳ f i :=
  Submodule.mem_map_of_mem hx

/-- A linear map is homogeneous of shift zero for the grading by its image pieces. -/
theorem isHomogeneousOfShift_linearImageGrading [AddZeroClass ι]
    (ℳ : ι → Submodule R M) (f : M →ₗ[R] Q) :
    IsHomogeneousOfShift ℳ (linearImageGrading ℳ f) 0 f := by
  intro i x hx
  simpa only [add_zero] using map_mem_linearImageGrading (f := f) hx

variable [DecidableEq ι] (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : M →ₗ[R] Q)

private def linearImageDecomposeAux : M →ₗ[R] ⨁ i, linearImageGrading ℳ f i :=
  (DirectSum.lmap fun i ↦ (f.comp (ℳ i).subtype).codRestrict
    (linearImageGrading ℳ f i) fun x ↦ map_mem_linearImageGrading x.2).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem linearImageDecomposeAux_apply (x : M) (i : ι) :
    (linearImageDecomposeAux ℳ f x i : Q) = f (decompose ℳ x i) := by
  simp only [linearImageDecomposeAux, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.lmap_apply]
  rfl

private theorem linearImageDecomposeAux_of_mem {i : ι} {x : M} (hx : x ∈ ℳ i) :
    linearImageDecomposeAux ℳ f x =
      DirectSum.lof R ι (fun j ↦ linearImageGrading ℳ f j) i
        ⟨f x, map_mem_linearImageGrading hx⟩ := by
  change DirectSum.lmap _ (DirectSum.decomposeLinearEquiv ℳ x) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe ℳ i ⟨x, hx⟩, DirectSum.lmap_lof]
  rfl

private theorem linearImageDecomposeAux_sum (x : M) :
    DirectSum.coeLinearMap (linearImageGrading ℳ f) (linearImageDecomposeAux ℳ f x) = f x := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous x => simp [linearImageDecomposeAux_of_mem ℳ f x.2]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem linearImageDecomposeAux_ker (hker : (LinearMap.ker f).IsHomogeneous ℳ) :
    LinearMap.ker f ≤ LinearMap.ker (linearImageDecomposeAux ℳ f) := by
  intro x hx
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change (linearImageDecomposeAux ℳ f x i : Q) = 0
  rw [linearImageDecomposeAux_apply]
  exact ((hker.mem_iff ℳ).1 hx i :)

/-- A surjective linear image inherits an internal grading if the kernel is homogeneous.
This construction applies to an actual module quotient, without replacing it by a quotient
with a different scalar ring. -/
@[no_expose, instance_reducible]
def linearImageDecomposition (hf : Function.Surjective f)
    (hker : (LinearMap.ker f).IsHomogeneous ℳ) : Decomposition (linearImageGrading ℳ f) :=
  Decomposition.ofLinearMap _
    ((f.liftOfSurjective hf)
      ⟨linearImageDecomposeAux ℳ f, linearImageDecomposeAux_ker ℳ f hker⟩)
    (by
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := hf y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.equivOfSurjective_apply] using
        linearImageDecomposeAux_sum ℳ f x)
    (by
      apply DirectSum.linearMap_ext R
      intro i
      apply LinearMap.ext
      rintro ⟨y, x, hx, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply, DirectSum.coeLinearMap_lof,
        LinearMap.equivOfSurjective_apply]
      exact linearImageDecomposeAux_of_mem ℳ f hx)

/-- Components on a linear image are images of the components of any representative. The
formula holds for any decomposition of these image pieces, since an internal decomposition
is unique. -/
@[simp]
theorem decompose_linearImageGrading [Decomposition (linearImageGrading ℳ f)] (x : M) (i : ι) :
    (decompose (linearImageGrading ℳ f) (f x) i : Q) = f (decompose ℳ x i) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst i
      rw [DirectSum.decompose_of_mem_same _ (map_mem_linearImageGrading x.2),
        DirectSum.decompose_of_mem_same _ x.2]
    · rw [DirectSum.decompose_of_mem_ne _ (map_mem_linearImageGrading x.2) h,
        DirectSum.decompose_of_mem_ne _ x.2 h, map_zero]
  | add x y hx hy => simp [DirectSum.decompose_add, hx, hy]

variable {ℳ f}

/-- The range of a homogeneous map is closed under taking homogeneous components. -/
theorem IsHomogeneousOfShift.isHomogeneous_range [AddGroup ι]
    {𝒩 : ι → Submodule R Q} [Decomposition 𝒩] {a : ι}
    (hf : IsHomogeneousOfShift ℳ 𝒩 a f) : (LinearMap.range f).IsHomogeneous 𝒩 := by
  intro i y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨(decompose ℳ x (i + -a) : M),
    (hf.decompose_map (neg_add_cancel_right i a) x).symm⟩

end OrlikSolomon
