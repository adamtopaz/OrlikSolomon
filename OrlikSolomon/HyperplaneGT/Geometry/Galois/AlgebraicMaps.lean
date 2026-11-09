/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Complement
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Markings
import Mathlib.Tactic.FinCases

/-!
# Actual algebraic marking maps to one common target

The common two-puncture target is the complement of zero and one in the affine line. An
available marking induces its genuine coordinate-algebra pullback by the existing localization
map `SmoothAlg.complementMap`. These maps commute with arrangement inclusions because they
restrict the same affine marking function. Their formulas on the two ordered target units
prepare the scheme/theory comparison without importing a cohomology theory.

The arrow in `SmoothAlg` runs from the target algebra to the source complement algebra; the
corresponding geometric arrow runs from the stage complement to the common target. Scheme-open
transport is separate from these affine-algebra maps.

Blueprint: G06 (`def:g06`), including its actual inclusion/marking commuting squares.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open CategoryTheory

private theorem affineMap_sub_const_zero {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (f : M →ᵃ[R] R) : f - AffineMap.const R M 0 = f := by
  ext x
  simp

variable (k : Type u) [Field k]

private theorem isHyperplane_line_level (a : k) :
    IsHyperplane (zeroLocus (AffineMap.id k k - AffineMap.const k k a)) := by
  apply isHyperplane_zeroLocus_iff.mpr
  intro h
  have hh := congrArg (fun f : k →ₗ[k] k ↦ f 1) h
  simp at hh

/-- The single target arrangement, consisting of the points zero and one of the affine line.
It is independent of all marking tags, constants, ambient dimensions and chosen cofinal systems.

Blueprint: G06 (`def:g06`). -/
def twoPunctureArrangement : Arrangement k k := by
  classical
  exact Arrangement.ofFinset {zeroLocus (AffineMap.id k k),
    zeroLocus (AffineMap.id k k - AffineMap.const k k 1)}

/-- The target arrangement has exactly its two specified point hyperplanes. -/
@[simp]
theorem mem_twoPunctureArrangement (H : AffineSubspace k k) :
    H ∈ twoPunctureArrangement k ↔ H = zeroLocus (AffineMap.id k k) ∨
      H = zeroLocus (AffineMap.id k k - AffineMap.const k k 1) := by
  classical
  simp only [twoPunctureArrangement, Arrangement.mem_ofFinset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl
    · simpa only [affineMap_sub_const_zero] using isHyperplane_line_level k 0
    · exact isHyperplane_line_level k 1

/-- The zero and one point labels of the common target, in that order. -/
def twoPunctureLabel (a : Fin 2) : twoPunctureArrangement k :=
  if a = 0 then ⟨zeroLocus (AffineMap.id k k), by simp⟩ else
    ⟨zeroLocus (AffineMap.id k k - AffineMap.const k k 1), by simp⟩

/-- The ordered target label is the corresponding level of the affine-line coordinate. -/
@[simp]
theorem twoPunctureLabel_val (a : Fin 2) :
    (twoPunctureLabel k a).val =
      zeroLocus (AffineMap.id k k - AffineMap.const k k (a.val : k)) := by
  fin_cases a <;> simp [twoPunctureLabel, affineMap_sub_const_zero]

/-- The two ordered labels identify `Fin 2` with the common target's hyperplanes. -/
def twoPunctureLabelEquiv : Fin 2 ≃ twoPunctureArrangement k :=
  Equiv.ofBijective (twoPunctureLabel k) ⟨by
    intro a b hab
    have ha : (a.val : k) ∈ (twoPunctureLabel k a).val := by simp
    rw [hab] at ha
    have hab' : (a.val : k) = (b.val : k) := by simpa [sub_eq_zero] using ha
    fin_cases a <;> fin_cases b <;> simp_all,
    by
      intro H
      rcases (mem_twoPunctureArrangement k H.val).mp H.property with h | h
      · exact ⟨0, Subtype.ext (by simpa [affineMap_sub_const_zero] using h.symm)⟩
      · exact ⟨1, Subtype.ext (by simpa [affineMap_sub_const_zero] using h.symm)⟩⟩

/-- The target-label equivalence uses exactly the specified ordered labels. -/
@[simp]
theorem twoPunctureLabelEquiv_apply (a : Fin 2) :
    twoPunctureLabelEquiv k a = twoPunctureLabel k a := rfl

/-- The one shared target, as a smooth coordinate algebra. -/
@[instance_reducible]
def markingTarget : SmoothAlg k := SmoothAlg.complement (twoPunctureArrangement k)

/-- The unit `t-a` on the common target, for the ordered values `a = 0, 1`. -/
def markingTargetUnit (a : Fin 2) : (markingTarget k)ˣ :=
  SmoothAlg.complementUnit (twoPunctureArrangement k)
    (AffineMap.id k k - AffineMap.const k k (a.val : k))
    (.of_mem (twoPunctureLabel_val k a ▸ (twoPunctureLabel k a).property))

variable {k} {k₀ : Type v} [Field k₀] [Algebra k₀ k] {S : Set k₀} {n : ℕ}

namespace Marking

variable (w : Marking S n) {𝒜 ℬ : Arrangement k (Fin n → k)}

variable {w} in
/-- An available marking has every ordered level equation inverted on its source complement. -/
theorem Available.covers_fiber (hw : w.Available 𝒜) (a : Fin 2) :
    𝒜.Covers (zeroLocus
      (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))) := by
  apply Arrangement.Covers.of_mem
  rw [← w.fiber_val, ← w.fiberLabel_val hw a]
  exact (w.fiberLabel hw a).property

variable {w} in
/-- The inverse images of both target hyperplanes are covered by an available source marking.
-/
theorem Available.covers_target (hw : w.Available 𝒜) :
    ∀ K ∈ twoPunctureArrangement k, 𝒜.Covers (K.comap (w.function (k := k))) := by
  intro K hK
  rcases (mem_twoPunctureArrangement k K).mp hK with rfl | rfl
  · rw [← zeroLocus_comp]
    simpa [affineMap_sub_const_zero] using hw.covers_fiber 0
  · rw [← zeroLocus_comp]
    have hcomp : (AffineMap.id k k - AffineMap.const k k 1).comp w.function =
        w.function - AffineMap.const k _ 1 := by ext x; rfl
    simpa only [hcomp, Fin.val_one, Nat.cast_one, map_one] using hw.covers_fiber 1

/-- The actual pullback on smooth coordinate algebras induced by the geometric marking map
from a stage complement to the one common two-puncture target.

Blueprint: G06 (`def:g06`). -/
def algebraicMap (hw : w.Available 𝒜) : markingTarget k ⟶ SmoothAlg.complement 𝒜 :=
  SmoothAlg.complementMap (w.function (k := k)) (twoPunctureArrangement k) 𝒜 hw.covers_target

/-- On unlocalized affine coordinates, the marking map is the original affine pullback. -/
@[simp]
theorem algebraicMap_toComplement (hw : w.Available 𝒜) (x : SmoothAlg.affineSpace k k) :
    w.algebraicMap hw (SmoothAlg.toComplement (twoPunctureArrangement k) x) =
      SmoothAlg.toComplement 𝒜 (SmoothAlg.affinePull (w.function (k := k)) x) :=
  SmoothAlg.complementMap_toComplement _ _ x

/-- The marking pullback restricts the same affine function before and after localization. -/
@[reassoc (attr := simp)]
theorem toComplement_comp_algebraicMap (hw : w.Available 𝒜) :
    SmoothAlg.toComplement (twoPunctureArrangement k) ≫ w.algebraicMap hw =
      SmoothAlg.affinePull (w.function (k := k)) ≫ SmoothAlg.toComplement 𝒜 :=
  SmoothAlg.toComplement_comp_complementMap _ _

/-- Marking maps at two nested arrangements form a genuine commuting square of algebras. -/
@[reassoc (attr := simp)]
theorem algebraicMap_comp_inclusion (hw : w.Available 𝒜) (h : 𝒜 ≤ ℬ) :
    w.algebraicMap hw ≫ SmoothAlg.complementInclusion h = w.algebraicMap (hw.mono h) := by
  apply SmoothAlg.complement_hom_ext
  simp

/-- Pullback sends each ordered target unit `t-a` to the corresponding marking unit `w-a`.
-/
@[simp]
theorem mapUnits_algebraicMap_targetUnit (hw : w.Available 𝒜) (a : Fin 2) :
    SmoothAlg.mapUnits (w.algebraicMap hw) (markingTargetUnit k a) =
      SmoothAlg.complementUnit 𝒜
        (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
        (hw.covers_fiber a) := by
  apply Units.ext
  simp only [markingTargetUnit, SmoothAlg.coe_mapUnits, SmoothAlg.coe_complementUnit,
    algebraicMap_toComplement, SmoothAlg.affinePull_affineCoord]
  congr 2
  ext x
  simp

end Marking

end OrlikSolomon.HyperplaneGT
