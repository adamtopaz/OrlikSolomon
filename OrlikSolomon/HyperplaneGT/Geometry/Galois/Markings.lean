/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Galois.System
import Mathlib.Tactic.FinCases

/-!
# Tagged marking functions and their fixed fibers

A marking is tagged as either a coordinate translate `xᵢ - s` for `s ∈ S`, or an ordered
coordinate difference `xᵢ - xⱼ` with `i < j`. Its fibers at base-field values are hyperplanes,
and every base-field automorphism fixes them individually. The zero and one fibers are
strictly parallel, including in characteristic two.

Availability records that a finite arrangement contains both fibers. Ordered fiber labels
commute with inclusions, and cofinality supplies a common stage for any finite collection of
markings and previously selected stages. Neither a generating condition on `S` nor algebraicity
or perfectness of the field extension is needed here.

Blueprint: G06 (`def:g06`). Actual coordinate-algebra maps are in the separate `AlgebraicMaps`
leaf; their single target is independent of the marking.
-/

@[expose] public section

universe u v

namespace OrlikSolomon.HyperplaneGT

variable {k₀ : Type v}

/-- The tagged coordinate translates and ordered coordinate differences in a marking system.
The set `S` is arbitrary at this stage; generation assumptions enter reconstruction later.

Blueprint: G06 (`def:g06`). -/
inductive Marking (S : Set k₀) (n : ℕ) : Type v
  | coordinate (i : Fin n) (s : S)
  | difference (i j : Fin n) (hij : i < j)

namespace Marking

variable {S : Set k₀} {n : ℕ}

/-- There are no markings in dimension zero, regardless of the chosen set of constants. -/
instance : IsEmpty (Marking S 0) := ⟨fun w ↦ by cases w <;> exact Fin.elim0 ‹Fin 0›⟩

variable {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]

/-- The affine function associated with a tagged marking. -/
def function : Marking S n → ((Fin n → k) →ᵃ[k] k)
  | .coordinate i s => (LinearMap.proj i).toAffineMap -
      AffineMap.const k _ (algebraMap k₀ k s.val)
  | .difference i j _ => (LinearMap.proj i).toAffineMap - (LinearMap.proj j).toAffineMap

@[simp]
theorem function_coordinate (i : Fin n) (s : S) (x : Fin n → k) :
    (coordinate i s).function (k := k) x = x i - algebraMap k₀ k s.val := rfl

@[simp]
theorem function_difference (i j : Fin n) (hij : i < j) (x : Fin n → k) :
    (difference (S := S) i j hij).function (k := k) x = x i - x j := rfl

/-- Every marking has nonzero linear part, with no dimension lower bound. -/
theorem function_linear_ne_zero (w : Marking S n) : (w.function (k := k)).linear ≠ 0 := by
  cases w with
  | coordinate i s =>
    intro h
    have hh := congrArg (fun f : (Fin n → k) →ₗ[k] k ↦ f (Pi.single i 1)) h
    simp [function] at hh
  | difference i j hij =>
    intro h
    have hh := congrArg (fun f : (Fin n → k) →ₗ[k] k ↦ f (Pi.single i 1)) h
    simp [function, (ne_of_lt hij).symm] at hh

/-- The fiber of a marking at a base-field value, as an affine hyperplane. -/
def fiber (w : Marking S n) (a : k₀) : Hyperplane k n :=
  ⟨zeroLocus (w.function (k := k) - AffineMap.const k _ (algebraMap k₀ k a)),
    isHyperplane_zeroLocus_iff.mpr (by simpa using w.function_linear_ne_zero (k := k))⟩

/-- The underlying affine subspace is the zero locus of the normalized level equation. -/
theorem fiber_val (w : Marking S n) (a : k₀) :
    (w.fiber (k := k) a).val =
      zeroLocus (w.function (k := k) - AffineMap.const k _ (algebraMap k₀ k a)) := rfl

/-- Membership in a marking fiber is the corresponding level equation. -/
@[simp]
theorem mem_fiber (w : Marking S n) (a : k₀) (x : Fin n → k) :
    x ∈ (w.fiber (k := k) a).val ↔ w.function (k := k) x = algebraMap k₀ k a := by
  simp [fiber, sub_eq_zero]

/-- The normalized level equation is an equation of the fiber hyperplane. -/
theorem isEquation_fiber (w : Marking S n) (a : k₀) :
    IsEquation (w.function (k := k) - AffineMap.const k _ (algebraMap k₀ k a))
      (w.fiber (k := k) a).val :=
  ⟨by simpa using w.function_linear_ne_zero (k := k), rfl⟩

/-- Different base-field levels of a marking give different hyperplanes. -/
theorem fiber_injective (w : Marking S n) : Function.Injective (w.fiber (k := k)) := by
  intro a b hab
  obtain ⟨x, hx⟩ := (w.fiber (k := k) a).property.nonempty
  have ha := (w.mem_fiber (k := k) a x).mp hx
  have hxb : x ∈ (w.fiber (k := k) b).val := by
    rw [← congrArg (fun H : Hyperplane k n ↦ H.val) hab]
    exact hx
  have hb := (w.mem_fiber (k := k) b x).mp hxb
  exact (algebraMap k₀ k).injective (ha.symm.trans hb)

/-- Distinct fibers are strictly parallel, over every field including characteristic two. -/
theorem parallel_fibers (w : Marking S n) {a b : k₀} (hab : a ≠ b) :
    Parallel (w.fiber (k := k) a) (w.fiber (k := k) b) := by
  refine ⟨fun h ↦ hab (w.fiber_injective h), le_bot_iff.mp ?_⟩
  intro x hx
  have ha := (w.mem_fiber (k := k) a x).mp hx.1
  have hb := (w.mem_fiber (k := k) b x).mp hx.2
  exact (hab ((algebraMap k₀ k).injective (ha.symm.trans hb))).elim

/-- The zero and one fibers of every marking are strictly parallel. -/
theorem parallel_zero_one (w : Marking S n) :
    Parallel (w.fiber (k := k) 0) (w.fiber (k := k) 1) :=
  w.parallel_fibers zero_ne_one

/-- A marking function is defined over the base field: applying an automorphism to the point
applies the same automorphism to its value. -/
theorem function_fieldCoordinateAddEquiv (w : Marking S n) (σ : k ≃ₐ[k₀] k)
    (x : Fin n → k) :
    w.function (k := k) (fieldCoordinateAddEquiv σ.toRingEquiv (Fin n) x) =
      σ (w.function (k := k) x) := by
  cases w <;> simp [function, σ.commutes]

/-- Coefficientwise field transformation fixes each marking affine function. -/
theorem fieldAffineForm_function (w : Marking S n) (σ : k ≃ₐ[k₀] k) :
    fieldAffineForm σ.toRingEquiv (w.function (k := k)) = w.function (k := k) := by
  ext x
  obtain ⟨y, rfl⟩ := (fieldCoordinateAddEquiv σ.toRingEquiv (Fin n)).surjective x
  rw [fieldAffineForm_apply, w.function_fieldCoordinateAddEquiv]
  rfl

/-- Every base-field marking fiber is individually fixed by the coefficient Galois action. -/
@[simp]
theorem galois_smul_fiber (w : Marking S n) (σ : k ≃ₐ[k₀] k) (a : k₀) :
    σ • w.fiber (k := k) a = w.fiber a := by
  apply Subtype.ext
  ext x
  rw [galois_smul_val, mem_fieldAffineSubspace, mem_fiber, mem_fiber]
  have hx := w.function_fieldCoordinateAddEquiv σ
    ((fieldCoordinateAddEquiv σ.toRingEquiv (Fin n)).symm x)
  rw [(fieldCoordinateAddEquiv σ.toRingEquiv (Fin n)).apply_symm_apply] at hx
  constructor
  · intro h
    rw [hx, h, σ.commutes]
  · intro h
    apply σ.injective
    rw [← hx, h, σ.commutes]

/-- A marking is available at an arrangement when both its deleted fibers are labels there. -/
def Available (w : Marking S n) (𝒜 : Arrangement k (Fin n → k)) : Prop :=
  (w.fiber (k := k) 0).val ∈ 𝒜 ∧ (w.fiber (k := k) 1).val ∈ 𝒜

/-- Enlarging an arrangement preserves availability of each marking. -/
theorem Available.mono {w : Marking S n} {𝒜 ℬ : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) (h : 𝒜 ≤ ℬ) : w.Available ℬ :=
  ⟨h hw.1, h hw.2⟩

/-- The two ordered fiber labels of an available marking, indexed by zero and one. -/
def fiberLabel (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) (a : Fin 2) : 𝒜 :=
  if a = 0 then ⟨(w.fiber 0).val, hw.1⟩ else ⟨(w.fiber 1).val, hw.2⟩

@[simp]
theorem fiberLabel_zero (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) : (w.fiberLabel hw 0).val = (w.fiber (k := k) 0).val := by
  simp [fiberLabel]

@[simp]
theorem fiberLabel_one (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) : (w.fiberLabel hw 1).val = (w.fiber (k := k) 1).val := by
  simp [fiberLabel]

/-- The ordered label has precisely its indicated zero or one level. -/
theorem fiberLabel_val (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) (a : Fin 2) :
    (w.fiberLabel hw a).val = (w.fiber (k := k) (a.val : k₀)).val := by
  fin_cases a <;> simp

/-- The ordered zero and one fiber labels of an available marking are distinct. -/
theorem fiberLabel_injective (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) : Function.Injective (w.fiberLabel hw) := by
  intro a b hab
  have hfiber : w.fiber (k := k) (a.val : k₀) = w.fiber (b.val : k₀) := by
    apply Subtype.ext
    simpa only [fiberLabel_val] using congrArg (fun H : 𝒜 ↦ H.val) hab
  have hab' := w.fiber_injective hfiber
  fin_cases a <;> fin_cases b <;> simp_all

/-- Ordered marking labels commute with an inclusion of arrangements. -/
@[simp]
theorem inclusion_fiberLabel (w : Marking S n) {𝒜 ℬ : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) (h : 𝒜 ≤ ℬ) (a : Fin 2) :
    Arrangement.inclusion h (w.fiberLabel hw a) = w.fiberLabel (hw.mono h) a := by
  apply Subtype.ext
  simp only [Arrangement.coe_inclusion, fiberLabel_val]

end Marking

variable {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ} {S : Set k₀}

/-- A tagged marking arrow at a finite arrangement. Every such arrow has the same target;
only its source stage, tag, and availability witness vary.

Blueprint: G06 (`def:g06`). -/
structure MarkingArrow (S : Set k₀) (𝒜 : Arrangement k (Fin n → k)) where
  /-- The tagged marking function. -/
  marking : Marking S n
  /-- Both fibers have been deleted at the source arrangement. -/
  available : marking.Available 𝒜

/-- Tagged marking arrows are determined by their marking tag; availability is a proposition.
-/
@[ext]
theorem MarkingArrow.ext {𝒜 : Arrangement k (Fin n → k)} {f g : MarkingArrow S 𝒜}
    (h : f.marking = g.marking) : f = g := by
  cases f
  cases g
  cases h
  rfl

namespace CofinalSystem

variable (C : CofinalSystem k₀ k n)

/-- A finite collection of markings is simultaneously available at some selected stage. -/
theorem exists_stage_markings (s : Finset (Marking S n)) :
    ∃ 𝒜 : C.Stage, ∀ w ∈ s, w.Available 𝒜.val.val := by
  classical
  let fibers := s.biUnion fun w ↦ {w.fiber (k := k) 0, w.fiber 1}
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_containing fibers
  refine ⟨𝒜, fun w hw ↦ ⟨?_, ?_⟩⟩
  · exact h𝒜 _ (Finset.mem_biUnion.mpr ⟨w, hw, by simp⟩)
  · exact h𝒜 _ (Finset.mem_biUnion.mpr ⟨w, hw, by simp⟩)

/-- A marking is available somewhere in every chosen cofinal system. -/
theorem exists_stage_marking (w : Marking S n) :
    ∃ 𝒜 : C.Stage, w.Available 𝒜.val.val := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_markings {w}
  exact ⟨𝒜, h𝒜 w (by simp)⟩

/-- Previously selected stages and finitely many markings may all be moved to one common
stage. No closure of the chosen family under unions is assumed. -/
theorem exists_ge_markings (s : Finset C.Stage) (t : Finset (Marking S n)) :
    ∃ ℬ : C.Stage, (∀ 𝒜 ∈ s, 𝒜 ≤ ℬ) ∧ ∀ w ∈ t, w.Available ℬ.val.val := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_markings t
  obtain ⟨ℬ, hℬ⟩ := C.exists_ge_finset (insert 𝒜 s)
  refine ⟨ℬ, fun 𝒟 h𝒟 ↦ hℬ 𝒟 (by simp [h𝒟]), ?_⟩
  intro w hw
  exact (h𝒜 w hw).mono (show 𝒜.val.val ≤ ℬ.val.val from hℬ 𝒜 (by simp))

end CofinalSystem

end OrlikSolomon.HyperplaneGT
