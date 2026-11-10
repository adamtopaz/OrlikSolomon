/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Projective
public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Inertia
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Markings
import Mathlib.Tactic.FinCases

/-!
# The marked frame and the obstruction to exchanging all fibers

The coordinate zero fibers and the ordered coordinate-difference zero fiber form a genuine
dependent triple. The corresponding three one fibers have empty common intersection.
These statements hold over arbitrary fields, including characteristic two, and use only
the actual tagged marking functions.

Blueprint: the geometric obstruction in I04 (`lem:i04`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

universe u v r

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} {S : Set k₀}

private theorem marking_coordinate_zero_distinct (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    (Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.coordinate j ⟨0, hS⟩).fiber 0 ∧
      (Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.difference (S := S) i j hij).fiber 0 ∧
      (Marking.coordinate j ⟨0, hS⟩).fiber (k := k) 0 ≠
        (Marking.difference (S := S) i j hij).fiber 0 := by
  have hne := ne_of_lt hij
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single j (1 : k) ∈ H.val) he
    simp [hne] at hm
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single j (1 : k) ∈ H.val) he
    simp [hne] at hm
  · intro he
    have hm := congrArg (fun H : Hyperplane k n ↦ Pi.single i (1 : k) ∈ H.val) he
    simp [hne.symm] at hm

/-- Two distinct coordinate zero fibers and their ordered difference zero fiber have the
same nonempty codimension-two trace. No assumption about the characteristic is needed. -/
theorem dependentTriple_marking_coordinate_zero (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    DependentTriple ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0)
      ((Marking.coordinate j ⟨0, hS⟩).fiber 0)
      ((Marking.difference (S := S) i j hij).fiber 0) := by
  obtain ⟨hij', hi, hj⟩ := marking_coordinate_zero_distinct (k := k) hS i j hij
  apply (dependentTriple_iff_trace_eq _ _ _ hij' hi hj).mpr
  constructor
  · intro hbot
    have hz : (0 : Fin n → k) ∈
        ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 0).val ⊓
          ((Marking.coordinate j ⟨0, hS⟩).fiber 0).val := by
      constructor <;> simp
    rw [hbot] at hz
    exact AffineSubspace.notMem_bot k _ _ hz
  · ext x
    simp only [AffineSubspace.mem_inf_iff, Marking.mem_fiber, Marking.function_coordinate,
      Marking.function_difference, map_zero, sub_zero]
    constructor
    · rintro ⟨hi, hj⟩
      exact ⟨hi, by simp [hi, hj]⟩
    · rintro ⟨hi, hd⟩
      exact ⟨hi, by simpa only [hi, zero_sub, neg_eq_zero] using hd⟩

/-- The corresponding coordinate one fibers and difference one fiber have empty triple
intersection. Thus exchanging every ordered marking pair cannot preserve incidence, even
in characteristic two. -/
theorem not_dependentTriple_marking_coordinate_one (hS : (0 : k₀) ∈ S)
    (i j : Fin n) (hij : i < j) :
    ¬DependentTriple ((Marking.coordinate i ⟨0, hS⟩).fiber (k := k) 1)
      ((Marking.coordinate j ⟨0, hS⟩).fiber 1)
      ((Marking.difference (S := S) i j hij).fiber 1) := by
  intro hd
  apply hd.2.2.2.1
  apply le_bot_iff.mp
  intro x hx
  have hi := (Marking.mem_fiber _ _ x).mp hx.1.1
  have hj := (Marking.mem_fiber _ _ x).mp hx.1.2
  have hd := (Marking.mem_fiber _ _ x).mp hx.2
  simp only [Marking.function_coordinate, map_zero, sub_zero, map_one] at hi hj
  simp only [Marking.function_difference, map_one, hi, hj, sub_self] at hd
  exact (zero_ne_one hd).elim

variable {R : Type r} [CommRing R] {C : CofinalSystem k₀ k n}

/-- The two coefficients of the one common target determine the image of every ordered
marked basis vector. This is the actual marking square in the universal module and needs
neither reconstruction hypotheses nor a new marking-map construction. -/
theorem DiagramAut.universalEquiv_marking_single (g : DiagramAut R C S)
    (w : Marking S n) (a : Fin 2) :
    g.universalEquiv (Finsupp.single (w.fiber (k := k) (a.val : k₀)) 1) =
      (g.targetEquiv (Finsupp.single a 1)) 0 • Finsupp.single (w.fiber 0) 1 +
        (g.targetEquiv (Finsupp.single a 1)) 1 • Finsupp.single (w.fiber 1) 1 := by
  classical
  obtain ⟨A, hw⟩ := C.exists_stage_marking w
  let f := (finiteStageMap R A.val.val).comp (w.basisMap R hw)
  have hf (t : Fin 2) : f (Finsupp.single t 1) =
      Finsupp.single (w.fiber (k := k) (t.val : k₀)) 1 := by
    simp only [f, LinearMap.comp_apply, Marking.basisMap_single, finiteStageMap_single]
    congr 1
    apply Subtype.ext
    exact w.fiberLabel_val hw t
  have he := LinearMap.congr_fun (g.universalEquiv_marking A w hw) (Finsupp.single a 1)
  change g.universalEquiv (f (Finsupp.single a 1)) =
    f (g.targetEquiv (Finsupp.single a 1)) at he
  have hsplit (x : Fin 2 →₀ R) :
      x = x 0 • Finsupp.single 0 1 + x 1 • Finsupp.single 1 1 := by
    ext t
    fin_cases t <;> simp
  rw [hf, hsplit (g.targetEquiv (Finsupp.single a 1)), map_add, map_smul,
    map_smul, hf, hf] at he
  simpa only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] using he

end OrlikSolomon.HyperplaneGT
