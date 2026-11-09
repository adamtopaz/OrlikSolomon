/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Equations
import OrlikSolomon.Geometry.ProjectiveArrangement
public import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Parallel pairs and dependent hyperplane triples

Distinct affine hyperplanes are parallel precisely when their normal forms are proportional.
Otherwise they meet in codimension two. Dependent triples have a nonempty intersection of
codimension two; empty triples are excluded, including in dimension two.

## Main results

* `parallel_iff_normal_proportional` and `normals_linearIndependent_of_not_parallel` give the
  pair dichotomy, with `codim_inf_eq_two_of_not_parallel` in its transverse branch.
* `dependentTriple_iff_equations_dependent` and
  `dependentTriple_iff_coefficientPoints_collinear` identify geometric and linear incidence.
* `dependentTriple_iff_trace_eq` characterizes equal nonempty traces.

Blueprint: `lem:g02`.
-/

@[expose] public section

namespace OrlikSolomon.HyperplaneGT

universe u v

variable {k : Type u} [Field k] {n : ℕ}

/-- Strict parallelism of hyperplanes: the labels are different and their intersection is empty.
In contrast, Mathlib's parallelism relation also relates a nonempty subspace to itself.

Blueprint: `lem:g02`. -/
def Parallel (H K : Hyperplane k n) : Prop := H ≠ K ∧ H.val ⊓ K.val = ⊥

/-- A dependent triple consists of distinct hyperplanes whose intersection is nonempty and has
codimension two. The nonemptiness guard is essential.

Blueprint: `lem:g02`. -/
def DependentTriple (H K L : Hyperplane k n) : Prop :=
  H ≠ K ∧ H ≠ L ∧ K ≠ L ∧ H.val ⊓ K.val ⊓ L.val ≠ ⊥ ∧
    codim (H.val ⊓ K.val ⊓ L.val) = 2

theorem parallel_comm (H K : Hyperplane k n) : Parallel H K ↔ Parallel K H := by
  simp only [Parallel, ne_comm, inf_comm]

@[simp]
theorem not_parallel_self (H : Hyperplane k n) : ¬Parallel H H := by
  simp [Parallel]

theorem dependentTriple_swap (H K L : Hyperplane k n) :
    DependentTriple H K L ↔ DependentTriple K H L := by
  simp [DependentTriple, ne_comm, inf_comm, and_left_comm]

theorem dependentTriple_rotate (H K L : Hyperplane k n) :
    DependentTriple H K L ↔ DependentTriple K L H := by
  simp [DependentTriple, ne_comm, inf_comm, inf_left_comm, and_left_comm]

/-- Distinct hyperplanes are disjoint precisely when their directions agree. -/
theorem inf_eq_bot_iff_direction_eq (H K : Hyperplane k n) (hne : H ≠ K) :
    H.val ⊓ K.val = ⊥ ↔ H.val.direction = K.val.direction := by
  constructor
  · intro hbot
    by_contra hdir
    have hsup : H.val.direction ⊔ K.val.direction = ⊤ := by
      obtain h | h := (le_sup_left : H.val.direction ≤
        H.val.direction ⊔ K.val.direction).eq_or_lt
      · have hKH : K.val.direction ≤ H.val.direction := by
          rw [h]
          exact le_sup_right
        obtain hKH | hKH := hKH.eq_or_lt
        · exact (hdir hKH.symm).elim
        · exact (H.property.isCoatom_direction.1
            (K.property.isCoatom_direction.2 _ hKH)).elim
      · exact H.property.isCoatom_direction.2 _ h
    obtain ⟨p, hpH, hpK⟩ :=
      AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
        H.property.nonempty K.property.nonempty hsup
    have hp : p ∈ H.val ⊓ K.val := ⟨hpH, hpK⟩
    rw [hbot] at hp
    exact AffineSubspace.notMem_bot k _ _ hp
  · intro hdir
    by_contra hbot
    obtain ⟨p, hpH, hpK⟩ := (AffineSubspace.nonempty_iff_ne_bot _).mpr hbot
    exact hne (Subtype.ext ((AffineSubspace.eq_iff_direction_eq_of_mem hpH hpK).mpr hdir))

section LinearForms

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A nonzero scalar-valued linear form has the same kernel as another form precisely when
they differ by a unit. This is the iff form of `exists_eq_smul_of_ker_eq`. -/
theorem ker_eq_ker_iff_unit_smul {f g : V →ₗ[k] k} (hf : f ≠ 0) :
    LinearMap.ker f = LinearMap.ker g ↔ ∃ c : kˣ, g = (c : k) • f := by
  constructor
  · intro hker
    exact exists_eq_smul_of_ker_eq hker.symm hf
  · rintro ⟨c, rfl⟩
    ext x
    simp [c.ne_zero]

/-- A form lies in the span of two affine forms exactly when it vanishes on their nonempty
common zero locus. No finite-dimensionality assumption on the ambient vector space is needed.
-/
theorem affineMap_mem_span_pair_iff {f g h : V →ᵃ[k] k}
    (hfg : ∃ p : V, f p = 0 ∧ g p = 0) :
    h ∈ Submodule.span k {f, g} ↔ ∀ x : V, f x = 0 → g x = 0 → h x = 0 := by
  constructor
  · intro hh x hfx hgx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hh
    simp [hfx, hgx]
  · intro hh
    obtain ⟨p, hfp, hgp⟩ := hfg
    have hhp := hh p hfp hgp
    have hker : LinearMap.ker f.linear ⊓ LinearMap.ker g.linear ≤
        LinearMap.ker h.linear := by
      intro v hv
      have hfv : f.linear v = 0 := hv.1
      have hgv : g.linear v = 0 := hv.2
      have hhv := hh (v +ᵥ p)
        (by simp only [AffineMap.map_vadd, hfv, hfp, zero_vadd])
        (by simp only [AffineMap.map_vadd, hgv, hgp, zero_vadd])
      change h (v +ᵥ p) = 0 at hhv
      rw [AffineMap.map_vadd, hhp] at hhv
      simpa using hhv
    have hspan : h.linear ∈ Submodule.span k {f.linear, g.linear} := by
      have hker' : (⨅ i : Fin 2, LinearMap.ker (![f.linear, g.linear] i)) ≤
          LinearMap.ker h.linear := by
        intro v hv
        exact hker ⟨((Submodule.mem_iInf _).mp hv) 0, ((Submodule.mem_iInf _).mp hv) 1⟩
      simpa only [Matrix.range_cons_cons_empty] using mem_span_of_iInf_ker_le_ker hker'
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, AffineMap.ext_linear (p := p) ?_ ?_⟩
    · simpa using hab
    · change a * f p + b * g p = h p
      simp [hfp, hgp, hhp]

end LinearForms

section ProjectivePoints

variable {W : Type v} [AddCommGroup W] [Module k W]

/-- Three nonzero vectors with independent first pair give collinear projective points exactly
when the third vector belongs to the span of the pair. -/
theorem isCollinear_mk_triple_iff_mem_span_pair {a b c : W}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : LinearIndependent k ![a, b]) :
    Projectivization.IsCollinear
      {Projectivization.mk k a ha, Projectivization.mk k b hb, Projectivization.mk k c hc} ↔
      c ∈ Submodule.span k {a, b} := by
  have : Module.Finite k (Submodule.span k ({a, b} : Set W)) :=
    Module.Finite.span_of_finite _ (Set.toFinite _)
  have hdim : Module.finrank k (Submodule.span k ({a, b} : Set W)) = 2 := by
    rw [← Matrix.range_cons_cons_empty a b ![]]
    simpa using finrank_span_eq_card hab
  constructor
  · rintro ⟨P, hPfinite, hPdim, hP⟩
    let : Module.Finite k P.submodule := hPfinite
    have haP : a ∈ P.submodule :=
      (Projectivization.Subspace.mem_submodule_iff P ha).mpr (hP (by simp))
    have hbP : b ∈ P.submodule :=
      (Projectivization.Subspace.mem_submodule_iff P hb).mpr (hP (by simp))
    have hcP : c ∈ P.submodule :=
      (Projectivization.Subspace.mem_submodule_iff P hc).mpr (hP (by simp))
    have hle : Submodule.span k {a, b} ≤ P.submodule := by
      refine Submodule.span_le.mpr ?_
      rintro x (rfl | rfl) <;> assumption
    have hdimle := Submodule.finrank_mono hle
    have heq : Submodule.span k {a, b} = P.submodule :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    rw [heq]
    exact hcP
  · intro hmem
    refine ⟨(Submodule.span k {a, b}).projectivization, ?_, ?_, ?_⟩
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      infer_instance
    · rw [Projectivization.Subspace.submodule.apply_symm_apply, hdim]
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact (Submodule.mk_mem_projectivization_iff _ ha).mpr
          (Submodule.subset_span (by simp))
      · exact (Submodule.mk_mem_projectivization_iff _ hb).mpr
          (Submodule.subset_span (by simp))
      · exact (Submodule.mk_mem_projectivization_iff _ hc).mpr hmem

end ProjectivePoints

/-- Parallel hyperplanes have proportional normal forms, with no choice of equations.

Blueprint: `lem:g02`. -/
theorem parallel_iff_normal_proportional (H K : Hyperplane k n) (hne : H ≠ K)
    {f g : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H.val) (hg : IsEquation g K.val) :
    Parallel H K ↔ ∃ c : kˣ, g.linear = (c : k) • f.linear := by
  rw [Parallel, and_iff_right hne, inf_eq_bot_iff_direction_eq H K hne,
    hf.direction_eq, hg.direction_eq]
  exact ker_eq_ker_iff_unit_smul hf.linear_ne_zero

/-- The normal forms of distinct nonparallel hyperplanes are linearly independent.

Blueprint: `lem:g02`. -/
theorem normals_linearIndependent_of_not_parallel (H K : Hyperplane k n) (hne : H ≠ K)
    (hnot : ¬Parallel H K) {f g : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H.val) (hg : IsEquation g K.val) :
    LinearIndependent k ![f.linear, g.linear] := by
  rw [LinearIndependent.pair_iff' hf.linear_ne_zero]
  intro c hc
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hg.linear_ne_zero (hc.symm.trans (by simp [hzero]))
  exact hnot ((parallel_iff_normal_proportional H K hne hf hg).mpr
    ⟨Units.mk0 c hc0, hc.symm⟩)

/-- Distinct nonparallel hyperplanes intersect in codimension two. -/
theorem codim_inf_eq_two_of_not_parallel (H K : Hyperplane k n) (hne : H ≠ K)
    (hnot : ¬Parallel H K) : codim (H.val ⊓ K.val) = 2 := by
  apply H.property.codim_inf_eq_two K.property (fun h ↦ hne (Subtype.ext h.symm))
  exact fun h ↦ hnot ⟨hne, h⟩

/-- Nested nonempty affine subspaces of equal codimension coincide. -/
theorem affineSubspace_eq_of_le_of_codim_eq {X Y : AffineSubspace k (Fin n → k)}
    (hX : X ≠ ⊥) (hle : X ≤ Y) (hcodim : codim X = codim Y) : X = Y := by
  obtain h | h := hle.eq_or_lt
  · exact h
  · have := codim_lt_codim hX h
    omega

/-- For a nonparallel pair, a third distinct hyperplane forms a dependent triple exactly when
it contains the intersection of the pair. -/
theorem dependentTriple_iff_inf_le (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) (hnot : ¬Parallel H K) :
    DependentTriple H K L ↔ H.val ⊓ K.val ≤ L.val := by
  have hbot : H.val ⊓ K.val ≠ ⊥ := fun h ↦ hnot ⟨hHK, h⟩
  have hpair := codim_inf_eq_two_of_not_parallel H K hHK hnot
  constructor
  · rintro ⟨-, -, -, htriple, hcodim⟩
    have heq : H.val ⊓ K.val ⊓ L.val = H.val ⊓ K.val :=
      affineSubspace_eq_of_le_of_codim_eq htriple inf_le_left (hcodim.trans hpair.symm)
    exact inf_eq_left.mp heq
  · intro hle
    have heq : H.val ⊓ K.val ⊓ L.val = H.val ⊓ K.val := inf_eq_left.mpr hle
    exact ⟨hHK, hHL, hKL, by simpa only [heq] using hbot,
      by simpa only [heq] using hpair⟩

/-- The geometric dependent-triple criterion is the linear span criterion for any equations.

Blueprint: `lem:g02`. -/
theorem dependentTriple_iff_equation_mem_span (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) (hnot : ¬Parallel H K)
    {f g h : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H.val) (hg : IsEquation g K.val) (hh : IsEquation h L.val) :
    DependentTriple H K L ↔ h ∈ Submodule.span k {f, g} := by
  have hbot : H.val ⊓ K.val ≠ ⊥ := fun h ↦ hnot ⟨hHK, h⟩
  obtain ⟨p, hpH, hpK⟩ := (AffineSubspace.nonempty_iff_ne_bot _).mpr hbot
  rw [dependentTriple_iff_inf_le H K L hHK hHL hKL hnot,
    affineMap_mem_span_pair_iff ⟨p, hf.apply_eq_zero_iff.mpr hpH, hg.apply_eq_zero_iff.mpr hpK⟩]
  constructor
  · intro hle x hfx hgx
    exact hh.apply_eq_zero_iff.mpr (hle ⟨hf.apply_eq_zero_iff.mp hfx,
      hg.apply_eq_zero_iff.mp hgx⟩)
  · intro hvan x hx
    exact hh.apply_eq_zero_iff.mp (hvan x (hf.apply_eq_zero_iff.mpr hx.1)
      (hg.apply_eq_zero_iff.mpr hx.2))

/-- Equations of distinct hyperplanes are linearly independent as a pair of affine forms. -/
theorem equations_linearIndependent_pair (H K : Hyperplane k n) (hne : H ≠ K)
    {f g : (Fin n → k) →ᵃ[k] k} (hf : IsEquation f H.val) (hg : IsEquation g K.val) :
    LinearIndependent k ![f, g] := by
  have hf0 : f ≠ 0 := fun h ↦ hf.linear_ne_zero (by rw [h]; rfl)
  rw [LinearIndependent.pair_iff' hf0]
  intro a ha
  have ha0 : a ≠ 0 := by
    intro hzero
    have hg0 : g = 0 := ha.symm.trans (by simp [hzero])
    exact hg.linear_ne_zero (by rw [hg0]; rfl)
  apply hne
  apply Subtype.ext
  calc
    H.val = zeroLocus f := hf.zeroLocus_eq.symm
    _ = zeroLocus (a • f) := (zeroLocus_smul ha0 f).symm
    _ = zeroLocus g := congrArg zeroLocus ha
    _ = K.val := hg.zeroLocus_eq

/-- For distinct hyperplanes with a nonparallel first pair, dependence of the affine equations
is exactly geometric dependence. The ordering of this family places the third equation first.

Blueprint: `lem:g02`. -/
theorem dependentTriple_iff_equations_dependent (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) (hnot : ¬Parallel H K)
    {f g h : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H.val) (hg : IsEquation g K.val) (hh : IsEquation h L.val) :
    DependentTriple H K L ↔ ¬LinearIndependent k ![h, f, g] := by
  change DependentTriple H K L ↔ ¬LinearIndependent k (Fin.cons h ![f, g])
  rw [linearIndependent_finCons,
    and_iff_right (equations_linearIndependent_pair H K hHK hf hg), not_not,
    Matrix.range_cons_cons_empty]
  exact dependentTriple_iff_equation_mem_span H K L hHK hHL hKL hnot hf hg hh

/-- Coefficient points are collinear exactly when their hyperplanes form a dependent triple,
provided the labels are distinct and the first pair is nonparallel.

Blueprint: `lem:g02`. -/
theorem dependentTriple_iff_coefficientPoints_collinear (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) (hnot : ¬Parallel H K) :
    DependentTriple H K L ↔
      Projectivization.IsCollinear
        {coefficientPoint H, coefficientPoint K, coefficientPoint L} := by
  let f := equation H.val
  let g := equation K.val
  let h := equation L.val
  have hf : IsEquation f H.val := isEquation_equation H.property
  have hg : IsEquation g K.val := isEquation_equation K.property
  have hh : IsEquation h L.val := isEquation_equation L.property
  have hLI := equations_linearIndependent_pair H K hHK hf hg
  have hLIc : LinearIndependent k ![affineCoefficients f, affineCoefficients g] := by
    have heq : (affineCoefficients ∘ ![f, g]) =
        ![affineCoefficients f, affineCoefficients g] := by
      ext i
      fin_cases i <;> rfl
    rw [← heq]
    exact affineCoefficientsEquiv.toLinearMap.linearIndependent_iff_of_injOn
      affineCoefficientsEquiv.injective.injOn |>.mpr hLI
  rw [coefficientPoint_eq_mk H hf, coefficientPoint_eq_mk K hg, coefficientPoint_eq_mk L hh,
    isCollinear_mk_triple_iff_mem_span_pair _ _ _ hLIc,
    dependentTriple_iff_equation_mem_span H K L hHK hHL hKL hnot hf hg hh]
  simp only [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, by simpa only [map_add, map_smul] using congrArg affineCoefficients hab⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, affineCoefficientsEquiv.injective ?_⟩
    simpa only [affineCoefficientsEquiv_apply, map_add, map_smul] using hab

/-- Equal nonempty traces characterize dependent triples of distinct hyperplanes.

Blueprint: `lem:g02`. -/
theorem dependentTriple_iff_trace_eq (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) :
    DependentTriple H K L ↔ H.val ⊓ K.val ≠ ⊥ ∧ H.val ⊓ K.val = H.val ⊓ L.val := by
  constructor
  · intro hdep
    have hbot : H.val ⊓ K.val ≠ ⊥ := by
      intro hb
      exact hdep.2.2.2.1 (by rw [hb, bot_inf_eq])
    have hnot : ¬Parallel H K := fun h ↦ hbot h.2
    have hle := (dependentTriple_iff_inf_le H K L hHK hHL hKL hnot).mp hdep
    refine ⟨hbot, affineSubspace_eq_of_le_of_codim_eq hbot (le_inf inf_le_left hle) ?_⟩
    have hHLbot : H.val ⊓ L.val ≠ ⊥ := by
      intro hb
      exact hbot (le_bot_iff.mp (hb ▸ le_inf inf_le_left hle))
    rw [codim_inf_eq_two_of_not_parallel H K hHK hnot,
      H.property.codim_inf_eq_two L.property
        (fun h ↦ hHL (Subtype.ext h.symm)) hHLbot]
  · rintro ⟨hbot, heq⟩
    apply (dependentTriple_iff_inf_le H K L hHK hHL hKL (fun h ↦ hbot h.2)).mpr
    rw [heq]
    exact inf_le_right

end OrlikSolomon.HyperplaneGT
