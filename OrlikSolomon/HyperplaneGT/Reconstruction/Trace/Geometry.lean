/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates
public import OrlikSolomon.Geometry.Chart

/-!
# Intrinsic hyperplane traces

Hyperplanes inside a fixed affine hyperplane are represented by the existing affine chart
on its direction. Every intrinsic hyperplane lifts to an ambient hyperplane: pull its
equation back along the existing affine retraction. No point of a complement is needed.

The optional trace label discards precisely the strict parallel hyperplanes. Equal retained
traces of two distinct labels are precisely the guarded dependent triples. These geometric
facts supply the labels for the free-module trace map.

## Main results

* `exists_hyperplane_comap_chart` lifts any intrinsic hyperplane to an ambient hyperplane.
* `traceLabel_eq_none_iff` characterizes the discarded labels.
* `traceLabel_eq_some_iff` identifies each retained label with the actual chart comap.
* `traceLabel_surjective` covers every intrinsic hyperplane.
* `exists_common_traceLabel_iff` identifies the merged distinct labels.

Blueprint: the geometric assertions of L01 (`lem:l01`).
-/

@[expose] public section

noncomputable section

universe u

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} [Field k]

/-- Every hyperplane of a nonempty affine subspace is the trace of an ambient hyperplane
other than that subspace. The construction uses the existing affine retraction of its chart.

Blueprint: the trace-label surjectivity in `lem:l01`. -/
theorem exists_hyperplane_comap_chart {V : Type u} [AddCommGroup V] [Module k V]
    (X : AffineSubspace k V) (hX : X ≠ ⊥)
    (J : AffineSubspace k X.direction) (hJ : IsHyperplane J) :
    ∃ K : AffineSubspace k V, IsHyperplane K ∧ K ≠ X ∧ K.comap (chart X) = J := by
  obtain ⟨r, hr⟩ := exists_retraction X
  obtain ⟨f, hf⟩ := hJ.exists_isEquation
  have hcomp : (f.comp r).comp (chart X) = f := by
    rw [AffineMap.comp_assoc, hr, AffineMap.comp_id]
  have hlin : (f.comp r).linear ≠ 0 := by
    intro h
    apply hf.linear_ne_zero
    have heq := congrArg AffineMap.linear hcomp
    change (f.comp r).linear.comp (chart X).linear = f.linear at heq
    rw [h, LinearMap.zero_comp] at heq
    exact heq.symm
  have htrace : (zeroLocus (f.comp r)).comap (chart X) = J := by
    rw [← zeroLocus_comp, hcomp, hf.zeroLocus_eq]
  refine ⟨zeroLocus (f.comp r), isHyperplane_zeroLocus_iff.mpr hlin, ?_, htrace⟩
  intro h
  rw [h, comap_chart_self hX] at htrace
  exact hJ.ne_top htrace.symm

variable {n : ℕ}

/-- The existing hyperplanes in the direction space of a hyperplane, transported to it by
`chart`. This is a subtype synonym, not a new incidence or arrangement structure. -/
@[instance_reducible]
def IntrinsicHyperplane (H : Hyperplane k n) :=
  {J : AffineSubspace k H.val.direction // IsHyperplane J}

/-- The optional intrinsic trace of a hyperplane other than the fixed hyperplane. Strict
parallel hyperplanes are discarded; every other label retains its actual chart comap. -/
def traceLabel (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H}) :
    Option (IntrinsicHyperplane H) := by
  classical
  exact if h : Parallel H K.val then none else
    some ⟨K.val.val.comap (chart H.val),
      (H.property.isHyperplane_comap_chart_iff K.val.property).mpr
        ⟨fun hKH ↦ K.property (Subtype.ext hKH),
          fun hbot ↦ h ⟨K.property.symm, hbot⟩⟩⟩

/-- The discarded labels are exactly the strict parallel hyperplanes. -/
@[simp]
theorem traceLabel_eq_none_iff (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H}) :
    traceLabel H K = none ↔ Parallel H K.val := by
  classical
  unfold traceLabel
  split_ifs <;> simp_all

/-- Retained labels are exactly the actual intrinsic hyperplane traces. -/
theorem traceLabel_eq_some_iff (H : Hyperplane k n) (K : {K : Hyperplane k n // K ≠ H})
    (J : IntrinsicHyperplane H) :
    traceLabel H K = some J ↔ K.val.val.comap (chart H.val) = J.val := by
  classical
  unfold traceLabel
  split_ifs with h
  · have hbot := (comap_chart_eq_bot_iff H.property.ne_bot).mpr h.2
    simp [hbot, eq_comm, J.property.ne_bot]
  · rw [Option.some.injEq]
    exact Subtype.ext_iff

/-- Every intrinsic hyperplane occurs as a retained trace, including the vacuous
zero-dimensional direction case. No positive ambient dimension is assumed. -/
theorem traceLabel_surjective (H : Hyperplane k n) (J : IntrinsicHyperplane H) :
    ∃ K : {K : Hyperplane k n // K ≠ H}, traceLabel H K = some J := by
  obtain ⟨K, hK, hKH, htrace⟩ :=
    exists_hyperplane_comap_chart H.val H.property.ne_bot J.val J.property
  refine ⟨⟨⟨K, hK⟩, fun h ↦ hKH (congrArg Subtype.val h)⟩, ?_⟩
  exact (traceLabel_eq_some_iff H _ J).mpr htrace

/-- Two distinct off-hyperplane labels have a common retained trace exactly when they form
one guarded dependent triple with the fixed hyperplane. The retained-label condition excludes
empty traces from this equivalence. -/
theorem exists_common_traceLabel_iff (H : Hyperplane k n)
    (K L : {K : Hyperplane k n // K ≠ H}) (hKL : K.val ≠ L.val) :
    (∃ J : IntrinsicHyperplane H, traceLabel H K = some J ∧ traceLabel H L = some J) ↔
      DependentTriple H K.val L.val := by
  rw [dependentTriple_iff_trace_eq H K.val L.val K.property.symm L.property.symm hKL]
  constructor
  · rintro ⟨J, hK, hL⟩
    have hK' := (traceLabel_eq_some_iff H K J).mp hK
    have hL' := (traceLabel_eq_some_iff H L J).mp hL
    refine ⟨?_, ?_⟩
    · exact (comap_chart_eq_bot_iff H.property.ne_bot).not.mp (by rw [hK']; exact J.property.ne_bot)
    · exact (comap_chart_eq_comap_chart_iff H.property.ne_bot).mp (hK'.trans hL'.symm)
  · rintro ⟨hbot, heq⟩
    have htrace := (H.property.isHyperplane_comap_chart_iff K.val.property).mpr
      ⟨fun hKH ↦ K.property (Subtype.ext hKH), hbot⟩
    refine ⟨⟨K.val.val.comap (chart H.val), htrace⟩, ?_, ?_⟩
    · exact (traceLabel_eq_some_iff H K _).mpr rfl
    · apply (traceLabel_eq_some_iff H L _).mpr
      exact ((comap_chart_eq_comap_chart_iff H.property.ne_bot).mpr heq).symm

end OrlikSolomon.HyperplaneGT
