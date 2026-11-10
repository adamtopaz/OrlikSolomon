/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Local.Geometry

/-!
# Geometric connectivity of affine hyperplanes

Two distinct intersecting hyperplanes belong to an actual guarded dependent triple: the
sum of their equations has nonzero normal part and contains their intersection.
In dimension at least two, a strict parallel pair has a hyperplane transverse to both.
These witnesses connect all hyperplane labels for the scalar-kernel argument.

The field is arbitrary, including characteristic two. There is no coefficient ring,
cohomology theory, Galois condition or rational point of a complement.
Blueprint: the geometric connectivity in S01 (`lem:s01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- Distinct intersecting hyperplanes extend to a guarded dependent triple, without a
characteristic assumption or a dimension lower bound beyond their actual intersection.
Blueprint: the intersecting case of S01 (`lem:s01`). -/
theorem exists_dependentTriple_of_inf_ne_bot (H K : Hyperplane k n)
    (hne : H ≠ K) (hmeet : H.val ⊓ K.val ≠ ⊥) :
    ∃ L : Hyperplane k n, DependentTriple H K L := by
  let f := equation H.val
  let g := equation K.val
  have hf : IsEquation f H.val := isEquation_equation H.property
  have hg : IsEquation g K.val := isEquation_equation K.property
  have hnot : ¬Parallel H K := fun hp ↦ hmeet hp.2
  have hlin := normals_linearIndependent_of_not_parallel H K hne hnot hf hg
  have hsum : (f + g).linear ≠ 0 := by
    intro hz
    have he : (1 : k) • f.linear + (1 : k) • g.linear = 0 := by simpa using hz
    exact one_ne_zero (hlin.eq_zero_of_pair he).1
  let L : Hyperplane k n := ⟨zeroLocus (f + g), isHyperplane_zeroLocus_iff.mpr hsum⟩
  have hHL : H ≠ L := by
    intro he
    have hfg : IsEquation (f + g) H.val := by
      rw [he]
      exact isEquation_zeroLocus hsum
    obtain ⟨c, hc, -⟩ := hf.existsUnique_smul hfg
    have hl := congrArg AffineMap.linear hc
    change f.linear + g.linear = (c : k) • f.linear at hl
    have hl' : (1 : k) • f.linear + (1 : k) • g.linear =
        (c : k) • f.linear + (0 : k) • g.linear := by simpa using hl
    exact one_ne_zero (hlin.eq_of_pair hl').2
  have hKL : K ≠ L := by
    intro he
    have hfg : IsEquation (f + g) K.val := by
      rw [he]
      exact isEquation_zeroLocus hsum
    obtain ⟨c, hc, -⟩ := hg.existsUnique_smul hfg
    have hl := congrArg AffineMap.linear hc
    change f.linear + g.linear = (c : k) • g.linear at hl
    have hl' : (1 : k) • f.linear + (1 : k) • g.linear =
        (0 : k) • f.linear + (c : k) • g.linear := by simpa using hl
    exact one_ne_zero (hlin.eq_of_pair hl').1
  refine ⟨L, (dependentTriple_iff_inf_le H K L hne hHL hKL hnot).mpr ?_⟩
  intro x hx
  change f x + g x = 0
  rw [hf.apply_eq_zero_iff.mpr hx.1, hg.apply_eq_zero_iff.mpr hx.2, add_zero]

/-- In dimension at least two, one hyperplane meets both members of a strict parallel pair
and is distinct from each. The witness is a transverse graph in a chart of the first member.
Blueprint: the parallel case of S01 (`lem:s01`). -/
theorem exists_hyperplane_meeting_parallel_pair (hn : 2 ≤ n)
    (H K : Hyperplane k n) (hpar : Parallel H K) :
    ∃ L : Hyperplane k n,
      H ≠ L ∧ K ≠ L ∧ H.val ⊓ L.val ≠ ⊥ ∧ K.val ⊓ L.val ≠ ⊥ := by
  have hf := isEquation_equation H.property
  obtain ⟨i, hi⟩ := exists_normal_coefficient_ne_zero_of_isEquation hf
  have hH : ¬IsVertical (omittedCoordinates i) H :=
    (not_isVertical_iff_of_isEquation i H hf).mpr hi
  obtain ⟨L, -, hHL, hmeet⟩ :=
    exists_meeting_graph hn (omittedCoordinates i) i (mem_omittedCoordinates i) H hH
  have hKL : K ≠ L := by
    intro he
    exact hmeet (he ▸ hpar.2)
  refine ⟨L, hHL, hKL, hmeet, ?_⟩
  intro hbot
  have hdHK := (inf_eq_bot_iff_direction_eq H K hpar.1).mp hpar.2
  have hdKL := (inf_eq_bot_iff_direction_eq K L hKL).mp hbot
  exact hmeet ((inf_eq_bot_iff_direction_eq H L hHL).mpr (hdHK.trans hdKL))

/-- A function on hyperplanes taking equal values on the first two members of every guarded
dependent triple is constant in dimension at least two. The target is arbitrary; the proof
uses only the geometric connectivity witnesses. Blueprint: the connectivity step in S01. -/
theorem eq_of_eq_on_dependentTriples (hn : 2 ≤ n) {α : Type*}
    (f : Hyperplane k n → α)
    (h : ∀ H K L : Hyperplane k n, DependentTriple H K L → f H = f K)
    (H K : Hyperplane k n) : f H = f K := by
  classical
  by_cases heq : H = K
  · exact congrArg f heq
  by_cases hmeet : H.val ⊓ K.val ≠ ⊥
  · obtain ⟨L, hL⟩ := exists_dependentTriple_of_inf_ne_bot H K heq hmeet
    exact h H K L hL
  · have hpar : Parallel H K := ⟨heq, not_not.mp hmeet⟩
    obtain ⟨L, hHL, hKL, hHLmeet, hKLmeet⟩ :=
      exists_hyperplane_meeting_parallel_pair hn H K hpar
    obtain ⟨J, hJ⟩ := exists_dependentTriple_of_inf_ne_bot H L hHL hHLmeet
    obtain ⟨J', hJ'⟩ := exists_dependentTriple_of_inf_ne_bot K L hKL hKLmeet
    exact (h H L J hJ).trans (h K L J' hJ').symm

end OrlikSolomon.HyperplaneGT
