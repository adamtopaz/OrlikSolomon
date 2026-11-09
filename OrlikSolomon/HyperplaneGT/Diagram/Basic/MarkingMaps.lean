/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Algebra.LowDegrees
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.AlgebraicMaps
import Mathlib.Tactic.FinCases

/-!
# Presentation maps of the tagged markings

An available marking sends the two ordered free generators of the single common target to
its zero and one fiber labels. This map is injective and carries the entire target exterior
square into the actual quadratic relation span. The same generator formula defines a map of
the full Orlik–Solomon algebras, preserving every degree and commuting with inclusions.

All coefficients are arbitrary commutative rings. No cohomology comparison or quadratic
presentation of the whole Orlik–Solomon algebra is assumed. Blueprint: A03 (`def:a03`).
-/

@[expose] public section

noncomputable section

universe u v r

namespace OrlikSolomon.HyperplaneGT

open Module OSAlgebra

variable {k₀ : Type u} {k : Type v} [Field k₀] [Field k] [Algebra k₀ k]
  {S : Set k₀} {n : ℕ} (R : Type r) [CommRing R]

namespace Marking

variable (w : Marking S n) {𝒜 ℬ : Arrangement k (Fin n → k)}

/-- The linear pullback of the two ordered marking labels. Every marking has the same
source module, independently of its stage and its tag. Blueprint: A03 (`def:a03`). -/
def basisMap (hw : w.Available 𝒜) : (Fin 2 →₀ R) →ₗ[R] (𝒜 →₀ R) :=
  Finsupp.lmapDomain R R (w.fiberLabel hw)

/-- A marking sends each ordered basis vector to its corresponding fiber label. -/
@[simp]
theorem basisMap_single (hw : w.Available 𝒜) (a : Fin 2) (c : R) :
    w.basisMap R hw (Finsupp.single a c) = Finsupp.single (w.fiberLabel hw a) c := by
  simp [basisMap]

/-- Distinct zero and one labels make the marking pullback injective, even over the zero ring.
-/
theorem basisMap_injective (hw : w.Available 𝒜) : Function.Injective (w.basisMap R hw) :=
  Finsupp.mapDomain_injective (w.fiberLabel_injective hw)

/-- Marking pullbacks commute with extending the arrangement labels. -/
@[simp]
theorem basisMap_comp_inclusion (hw : w.Available 𝒜) (h : 𝒜 ≤ ℬ) :
    (Finsupp.lmapDomain R R (Arrangement.inclusion h)).comp (w.basisMap R hw) =
      w.basisMap R (hw.mono h) := by
  ext a
  simp

/-- Different ordered labels of an available marking are disjoint hyperplanes. -/
theorem fiberLabel_inf_eq_bot (hw : w.Available 𝒜) {a b : Fin 2} (hab : a ≠ b) :
    (w.fiberLabel hw a).val ⊓ (w.fiberLabel hw b).val = ⊥ := by
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · simpa [fiberLabel] using (w.parallel_zero_one (k := k)).2
  · simpa [fiberLabel, inf_comm] using
      (w.parallel_zero_one (k := k)).2
  · exact (hab rfl).elim

/-- Every product of two marking generator images vanishes: equal labels square to zero,
and unequal labels are parallel. This includes characteristic two. -/
@[simp]
theorem generator_mul_generator_fiberLabel (hw : w.Available 𝒜) (a b : Fin 2) :
    generator R 𝒜 (w.fiberLabel hw a) * generator R 𝒜 (w.fiberLabel hw b) = 0 := by
  by_cases hab : a = b
  · subst b
    exact generator_mul_self R 𝒜 _
  · exact generator_mul_eq_zero_of_disjoint R 𝒜 _ _ (w.fiberLabel_inf_eq_bot hw hab)

/-- The entire exterior square at the common target maps into the actual quadratic relation
span, since both marking labels are parallel. Blueprint: A03 (`def:a03`). -/
theorem basisMap_quadraticRelationSpan (hw : w.Available 𝒜) :
    (⊤ : Submodule R (⋀[R]^2 (Fin 2 →₀ R))).map
      (exteriorPower.map 2 (w.basisMap R hw)) ≤ quadraticRelationSpan R 𝒜 := by
  have hker : (⋀[R]^2 (Fin 2 →₀ R)) ≤
      LinearMap.ker ((quotient R 𝒜).toLinearMap.comp
        (ExteriorAlgebra.map (w.basisMap R hw)).toLinearMap) := by
    rw [← OrlikSolomon.span_word_length R 2, Submodule.span_le]
    rintro _ ⟨I, hI, rfl⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hI
    have hm (a : Fin 2) : ExteriorAlgebra.map (w.basisMap R hw) (exteriorGen R a) =
        exteriorGen R (w.fiberLabel hw a) := by simp [exteriorGen]
    change quotient R 𝒜 (ExteriorAlgebra.map (w.basisMap R hw)
      (word (exteriorGen R) [a, b])) = 0
    simpa only [word_cons, word_nil, mul_one, map_mul, hm, quotient_exteriorGen] using
      w.generator_mul_generator_fiberLabel R hw a b
  rintro _ ⟨x, _, rfl⟩
  rw [← quadraticKernel_eq_span, LinearMap.mem_ker]
  apply Subtype.ext
  change quotient R 𝒜 (exteriorPower.map 2 (w.basisMap R hw) x) = 0
  simpa only [exteriorPower.coe_map, LinearMap.mem_ker, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] using hker x.2

private theorem target_nodup_length_le_two {I : List (twoPunctureArrangement k)}
    (hI : I.Nodup) : I.length ≤ 2 := by
  have hc := Fintype.card_congr (twoPunctureLabelEquiv k)
  simpa only [← hc, Fintype.card_fin] using hI.length_le_card

/-- The marking labels satisfy all relations of the two-puncture Orlik–Solomon presentation.
The dependent-boundary condition is vacuous because this target has only two labels. -/
theorem isFamily (hw : w.Available 𝒜) :
    IsFamily (twoPunctureArrangement k)
      (fun H ↦ generator R 𝒜 (w.fiberLabel hw ((twoPunctureLabelEquiv k).symm H))) where
  toIsExteriorFamily := (isExteriorFamily_generator R 𝒜).comp _
  word_eq_zero I _ h := by
    cases I with
    | nil => simp at h
    | cons H I =>
      cases I with
      | nil => exact (((twoPunctureArrangement k).isHyperplane H.2).ne_bot
          (by simpa using h)).elim
      | cons K I => simp only [word_cons, ← mul_assoc,
          generator_mul_generator_fiberLabel, zero_mul]
  wordBoundary_eq_zero I hI h := by
    have hlo := dependent_length_ge_three (twoPunctureArrangement k) hI h
    have hhi := target_nodup_length_le_two hI
    omega

/-- Pullback of the full Orlik–Solomon presentation along a marking. Its source is the same
two-puncture algebra for every tag and stage. All target relators are checked in the universal
property; no quadratic-presentation assumption is used. Blueprint: A03 (`def:a03`). -/
def osMap (hw : w.Available 𝒜) :
    OSAlgebra R (twoPunctureArrangement k) →ₐ[R] OSAlgebra R 𝒜 :=
  OSAlgebra.lift _ (w.isFamily R hw)

/-- The full presentation map sends the ordered target generators to the marking fibers. -/
theorem osMap_generator (hw : w.Available 𝒜) (a : Fin 2) :
    w.osMap R hw (generator R _ (twoPunctureLabelEquiv k a)) =
      generator R 𝒜 (w.fiberLabel hw a) := by
  exact (OSAlgebra.lift_generator _ (w.isFamily R hw) _).trans
    (congrArg (fun a ↦ generator R 𝒜 (w.fiberLabel hw a))
      ((twoPunctureLabelEquiv k).symm_apply_apply a))

/-- The ordered generator formula also uses the target's named label constructor. -/
@[simp]
theorem osMap_generator_label (hw : w.Available 𝒜) (a : Fin 2) :
    w.osMap R hw (generator R _ (twoPunctureLabel k a)) =
      generator R 𝒜 (w.fiberLabel hw a) := w.osMap_generator R hw a

/-- Full presentation pullback preserves every homogeneous degree. -/
theorem osMap_mem_degree (hw : w.Available 𝒜) {q : ℕ}
    {x : OSAlgebra R (twoPunctureArrangement k)} (hx : x ∈ degree R _ q) :
    w.osMap R hw x ∈ degree R 𝒜 q := by
  have hspan : degree R (twoPunctureArrangement k) q ≤
      (degree R 𝒜 q).comap (w.osMap R hw).toLinearMap := by
    rw [← OSAlgebra.span_word_length R _ q, Submodule.span_le]
    rintro _ ⟨I, hI, rfl⟩
    change w.osMap R hw (word (generator R _) I) ∈ degree R 𝒜 q
    rw [map_word]
    have heq : (fun H ↦ w.osMap R hw (generator R _ H)) =
        fun H ↦ generator R 𝒜 (w.fiberLabel hw ((twoPunctureLabelEquiv k).symm H)) := by
      funext H
      obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
      rw [osMap_generator, Equiv.symm_apply_apply]
    rw [heq, ← word_map]
    simpa only [List.length_map, hI] using
      word_mem_degree R 𝒜 (I.map fun H ↦ w.fiberLabel hw ((twoPunctureLabelEquiv k).symm H))
  exact hspan hx

/-- The full marking pullback commutes with every arrangement inclusion. -/
@[simp]
theorem osMap_comp_inclusion (hw : w.Available 𝒜) (h : 𝒜 ≤ ℬ) :
    (OSAlgebra.map R h).comp (w.osMap R hw) = w.osMap R (hw.mono h) := by
  apply OSAlgebra.algHom_ext
  intro H
  obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
  simp

end Marking

/-- The two different ordered labels of the common target are disjoint points. -/
theorem twoPunctureLabel_inf_eq_bot {a b : Fin 2} (hab : a ≠ b) :
    (twoPunctureLabel k a).val ⊓ (twoPunctureLabel k b).val = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have ha : x = (a.val : k) := by
    simpa [twoPunctureLabel_val, sub_eq_zero] using hx.1
  have hb : x = (b.val : k) := by
    simpa [twoPunctureLabel_val, sub_eq_zero] using hx.2
  fin_cases a <;> fin_cases b <;> simp_all

/-- All products of two ordered common-target generators vanish, including squares. -/
@[simp]
theorem generator_mul_generator_twoPunctureLabel (a b : Fin 2) :
    generator R (twoPunctureArrangement k) (twoPunctureLabel k a) *
      generator R _ (twoPunctureLabel k b) = 0 := by
  by_cases hab : a = b
  · subst b
    exact generator_mul_self R _ _
  · exact generator_mul_eq_zero_of_disjoint R _ _ _ (twoPunctureLabel_inf_eq_bot hab)

/-- The entire exterior square of the ordered target coordinates is the actual cup kernel.
This identifies A03's target relation submodule with top. -/
theorem markingTarget_exteriorSquareMap_eq_zero :
    (osExteriorSquareMap R (twoPunctureArrangement k)).comp
      (exteriorPower.map 2
        (Finsupp.domLCongr (twoPunctureLabelEquiv k)).toLinearMap) = 0 := by
  let f : (Fin 2 →₀ R) →ₗ[R] ((twoPunctureArrangement k) →₀ R) :=
    (Finsupp.domLCongr (twoPunctureLabelEquiv k)).toLinearMap
  have hker : (⋀[R]^2 (Fin 2 →₀ R)) ≤
      LinearMap.ker ((quotient R (twoPunctureArrangement k)).toLinearMap.comp
        (ExteriorAlgebra.map f).toLinearMap) := by
    rw [← OrlikSolomon.span_word_length R 2, Submodule.span_le]
    rintro _ ⟨I, hI, rfl⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hI
    have hm (a : Fin 2) : ExteriorAlgebra.map f (exteriorGen R a) =
        exteriorGen R (twoPunctureLabel k a) := by simp [f, exteriorGen]
    change quotient R _ (ExteriorAlgebra.map f (word (exteriorGen R) [a, b])) = 0
    simpa only [word_cons, word_nil, mul_one, map_mul, hm, quotient_exteriorGen] using
      generator_mul_generator_twoPunctureLabel (k := k) R a b
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simpa only [f, LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coe_osExteriorSquareMap_apply, exteriorPower.coe_map, LinearMap.zero_apply,
    ZeroMemClass.coe_zero] using hker x.2

/-- The canonical degree-one coordinates of the common target, ordered as zero then one. -/
def markingTargetDegreeOneEquiv :
    (Fin 2 →₀ R) ≃ₗ[R] degree R (twoPunctureArrangement k) 1 :=
  (Finsupp.domLCongr (twoPunctureLabelEquiv k)).trans
    (osDegreeOneEquiv R (twoPunctureArrangement k))

/-- The target coordinate equivalence sends each ordered basis vector to its actual generator.
-/
@[simp]
theorem markingTargetDegreeOneEquiv_single (a : Fin 2) (c : R) :
    (markingTargetDegreeOneEquiv (k := k) R (Finsupp.single a c) : OSAlgebra R _) =
      c • generator R _ (twoPunctureLabelEquiv k a) := by
  simp [markingTargetDegreeOneEquiv]

/-- The linear and full graded marking arrows agree in the canonical degree-one coordinates.
-/
theorem Marking.osMap_degreeOne (w : Marking S n) {𝒜 : Arrangement k (Fin n → k)}
    (hw : w.Available 𝒜) (x : Fin 2 →₀ R) :
    (osDegreeOneEquiv R 𝒜 (w.basisMap R hw x) : OSAlgebra R 𝒜) =
      w.osMap R hw (markingTargetDegreeOneEquiv (k := k) R x) := by
  have h : (degree R 𝒜 1).subtype.comp
      ((osDegreeOneEquiv R 𝒜).toLinearMap.comp (w.basisMap R hw)) =
      (w.osMap R hw).toLinearMap.comp
        ((degree R (twoPunctureArrangement k) 1).subtype.comp
          (markingTargetDegreeOneEquiv (k := k) R).toLinearMap) := by
    ext a
    simp
  exact DFunLike.congr_fun h x

end OrlikSolomon.HyperplaneGT
