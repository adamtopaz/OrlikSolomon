/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Group.End
public import OrlikSolomon.HyperplaneGT.Geometry.Collineation.Span
public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Incidence
import Mathlib.LinearAlgebra.Projectivization.Independence

/-!
# Extending hyperplane permutations to projective coefficient space

The coefficient-point equivalence identifies affine hyperplanes with every projective point
except the constant point. A permutation extends by fixing that point. Strict parallel pairs
describe the lines through the constant point; guarded dependent triples describe the other
lines. Thus preservation of the actual affine incidence relations gives preservation of
projective lines in both directions.

The geometric constructions use an arbitrary field and do not require a coefficient ring,
locality or a dimension bound. Blueprint: the geometric extension in I03 (`lem:i03`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT

open scoped LinearAlgebra.Projectivization

universe u v

variable {k : Type u} [Field k] {n : ℕ}

/-- Extend an actual affine-hyperplane permutation to coefficient projective space by fixing
the constant point. Blueprint: the extension in I03 (`lem:i03`). -/
def projectiveExtension (π : Equiv.Perm (Hyperplane k n)) :
    Equiv.Perm (ℙ k (Fin (n + 1) → k)) := by
  classical
  exact π.extendDomain (coefficientPointEquiv k n)

/-- Extending coefficient permutations by the fixed constant point respects composition. -/
def projectiveExtensionHom :
    Equiv.Perm (Hyperplane k n) →* Equiv.Perm (ℙ k (Fin (n + 1) → k)) := by
  classical
  exact Equiv.Perm.extendDomainHom (coefficientPointEquiv k n)

/-- The extension homomorphism has the prescribed projective extension as its value. -/
@[simp]
theorem projectiveExtensionHom_apply (π : Equiv.Perm (Hyperplane k n)) :
    projectiveExtensionHom π = projectiveExtension π := rfl

/-- The identity hyperplane permutation extends to the identity projective permutation. -/
@[simp]
theorem projectiveExtension_one :
    projectiveExtension (1 : Equiv.Perm (Hyperplane k n)) = 1 :=
  projectiveExtensionHom.map_one

/-- Projective coefficient extensions compose in the same order as the label permutations. -/
theorem projectiveExtension_mul (π ρ : Equiv.Perm (Hyperplane k n)) :
    projectiveExtension (π * ρ) = projectiveExtension π * projectiveExtension ρ :=
  projectiveExtensionHom.map_mul π ρ

/-- Extending an inverse gives the ordinary inverse permutation, retaining cancellation. -/
@[simp]
theorem projectiveExtension_inv (π : Equiv.Perm (Hyperplane k n)) :
    projectiveExtension π⁻¹ = (projectiveExtension π)⁻¹ :=
  projectiveExtensionHom.map_inv π

/-- The projective extension fixes the omitted constant point. -/
@[simp]
theorem projectiveExtension_constantPoint (π : Equiv.Perm (Hyperplane k n)) :
    projectiveExtension π (constantPoint k n) = constantPoint k n := by
  classical
  exact π.extendDomain_apply_not_subtype (coefficientPointEquiv k n) (by simp)

/-- On hyperplane coefficient points the extension is the original label permutation. -/
@[simp]
theorem projectiveExtension_coefficientPoint (π : Equiv.Perm (Hyperplane k n))
    (H : Hyperplane k n) :
    projectiveExtension π (coefficientPoint H) = coefficientPoint (π H) := by
  classical
  exact π.extendDomain_apply_image (coefficientPointEquiv k n) H

section ProjectiveSpans

variable {V : Type v} [AddCommGroup V] [Module k V]

/-- For distinct endpoints, a third point lies on their projective span exactly when the
three points are collinear. No finite-dimensionality of the ambient space is needed. -/
theorem isCollinear_triple_iff_mem_projective_span_pair (p q r : ℙ k V) (hpq : p ≠ q) :
    Projectivization.IsCollinear {p, q, r} ↔
      r ∈ Projectivization.Subspace.span {p, q} := by
  induction p using Projectivization.ind with | h a ha =>
  induction q using Projectivization.ind with | h b hb =>
  induction r using Projectivization.ind with | h c hc =>
  have hab : LinearIndependent k ![a, b] := by
    rwa [← Projectivization.independent_mk_iff_LinearIndependent,
      Projectivization.independent_pair_iff_ne]
  rw [isCollinear_mk_triple_iff_mem_span_pair ha hb hc hab,
    projective_span_pair_eq, Submodule.mk_mem_projectivization_iff]

/-- A different point on a projective line gives another pair of endpoints for the same
line. This is the exchange property for two-point projective spans. -/
theorem projective_span_pair_eq_of_mem (p q r : ℙ k V) (hpq : p ≠ q) (hpr : p ≠ r)
    (hr : r ∈ Projectivization.Subspace.span {p, q}) :
    Projectivization.Subspace.span {p, r} = Projectivization.Subspace.span {p, q} := by
  have hcol := (isCollinear_triple_iff_mem_projective_span_pair p q r hpq).mpr hr
  have hcol' : Projectivization.IsCollinear {p, r, q} := by
    simpa only [Set.pair_comm] using hcol
  have hq := (isCollinear_triple_iff_mem_projective_span_pair p r q hpr).mp hcol'
  apply Projectivization.Subspace.span_eq_span_iff.mpr
  constructor
  · rintro x (rfl | rfl)
    · exact Projectivization.Subspace.subset_span _ (by simp)
    · exact hr
  · rintro x (rfl | rfl)
    · exact Projectivization.Subspace.subset_span _ (by simp)
    · exact hq

end ProjectiveSpans

private theorem const_one_mem_span_equations_iff_parallel (H K : Hyperplane k n)
    (hHK : H ≠ K) {f g : (Fin n → k) →ᵃ[k] k}
    (hf : IsEquation f H.val) (hg : IsEquation g K.val) :
    AffineMap.const k (Fin n → k) (1 : k) ∈ Submodule.span k {f, g} ↔ Parallel H K := by
  constructor
  · intro hm
    refine ⟨hHK, ?_⟩
    by_contra hmeet
    obtain ⟨x, hx⟩ := (AffineSubspace.nonempty_iff_ne_bot _).mpr hmeet
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hm
    have hfx := hf.apply_eq_zero_iff.mpr hx.1
    have hgx := hg.apply_eq_zero_iff.mpr hx.2
    have he := congrArg (fun h : (Fin n → k) →ᵃ[k] k ↦ h x) hab
    simp [hfx, hgx] at he
  · intro hp
    obtain ⟨c, hc⟩ := (parallel_iff_normal_proportional H K hHK hf hg).mp hp
    have hlin : (g - (c : k) • f).linear = 0 := by simp [hc]
    obtain ⟨d, hd⟩ := (AffineMap.linear_eq_zero_iff_exists_const _).mp hlin
    have hdne : d ≠ 0 := by
      intro hd0
      have hgf : g = (c : k) • f := by
        apply sub_eq_zero.mp
        rw [hd, hd0]
        ext x
        simp
      have hKH : K.val = H.val := by
        rw [← hg.zeroLocus_eq, hgf, zeroLocus_smul c.ne_zero, hf.zeroLocus_eq]
      exact hHK (Subtype.ext hKH.symm)
    have hm : AffineMap.const k (Fin n → k) d ∈ Submodule.span k {f, g} := by
      rw [← hd]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hd1 : d⁻¹ • AffineMap.const k (Fin n → k) d = AffineMap.const k _ (1 : k) := by
      ext x
      simp [hdne]
    rw [← hd1]
    exact Submodule.smul_mem _ _ hm

/-- A line through two distinct hyperplane coefficient points contains the constant point
exactly when the hyperplanes are strictly parallel. Blueprint: the parallel pencils in I03. -/
theorem constantPoint_mem_projective_span_pair_iff (H K : Hyperplane k n) (hHK : H ≠ K) :
    constantPoint k n ∈ Projectivization.Subspace.span {coefficientPoint H, coefficientPoint K} ↔
      Parallel H K := by
  let f := equation H.val
  let g := equation K.val
  have hf : IsEquation f H.val := isEquation_equation H.property
  have hg : IsEquation g K.val := isEquation_equation K.property
  have hc : affineCoefficients (AffineMap.const k (Fin n → k) (1 : k)) =
      Fin.cons 1 (fun _ ↦ 0) := by
    ext i
    cases i using Fin.cases <;> simp
  have hcc : coefficientForm (Fin.cons 1 (fun _ : Fin n ↦ (0 : k))) =
      AffineMap.const k (Fin n → k) (1 : k) := by
    rw [← hc, coefficientForm_affineCoefficients]
  rw [coefficientPoint_eq_mk H hf, coefficientPoint_eq_mk K hg,
    projective_span_pair_eq, constantPoint, Submodule.mk_mem_projectivization_iff]
  constructor
  · intro hm
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hm
    apply (const_one_mem_span_equations_iff_parallel H K hHK hf hg).mp
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simpa only [map_add, map_smul, coefficientForm_affineCoefficients, hcc] using
      congrArg coefficientForm hab
  · intro hp
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp
      ((const_one_mem_span_equations_iff_parallel H K hHK hf hg).mpr hp)
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simpa only [map_add, map_smul, hc] using congrArg affineCoefficients hab

/-- A parallel pencil consists of its chosen hyperplane and every hyperplane strictly
parallel to it, when viewed as coefficient points on the line through the constant point. -/
theorem coefficientPoint_mem_constant_span_iff (H K : Hyperplane k n) :
    coefficientPoint K ∈ Projectivization.Subspace.span {constantPoint k n, coefficientPoint H} ↔
      K = H ∨ Parallel H K := by
  by_cases hKH : K = H
  · subst K
    simp only [true_or, iff_true]
    exact Projectivization.Subspace.subset_span _ (by simp)
  have hHK := Ne.symm hKH
  have hoH : constantPoint k n ≠ coefficientPoint H :=
    (coefficientPoint_ne_constantPoint H).symm
  rw [← isCollinear_triple_iff_mem_projective_span_pair _ _ _ hoH]
  have hset : ({constantPoint k n, coefficientPoint H, coefficientPoint K} : Set _) =
      {coefficientPoint H, coefficientPoint K, constantPoint k n} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]
  rw [hset, isCollinear_triple_iff_mem_projective_span_pair _ _ _
    (coefficientPoint_injective.ne hHK), constantPoint_mem_projective_span_pair_iff H K hHK]
  simp only [hKH, false_or]

/-- Three distinct hyperplane coefficient points are collinear exactly when they lie in a
parallel pencil or form a guarded dependent triple. The empty-triangle guard is retained. -/
theorem coefficientPoints_collinear_iff (H K L : Hyperplane k n)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L) :
    Projectivization.IsCollinear {coefficientPoint H, coefficientPoint K, coefficientPoint L} ↔
      (Parallel H K ∧ Parallel H L) ∨ DependentTriple H K L := by
  by_cases hp : Parallel H K
  · have hline := projective_span_pair_eq_of_mem
      (coefficientPoint H) (coefficientPoint K) (constantPoint k n)
      (coefficientPoint_injective.ne hHK) (coefficientPoint_ne_constantPoint H)
      ((constantPoint_mem_projective_span_pair_iff H K hHK).mpr hp)
    have hnot : ¬DependentTriple H K L := by
      intro ht
      exact ht.2.2.2.1 (by simp [hp.2])
    rw [isCollinear_triple_iff_mem_projective_span_pair _ _ _
      (coefficientPoint_injective.ne hHK), ← hline, Set.pair_comm (coefficientPoint H),
      coefficientPoint_mem_constant_span_iff]
    simp only [Ne.symm hHL, false_or, hp, true_and, hnot, or_false]
  · rw [← dependentTriple_iff_coefficientPoints_collinear H K L hHK hHL hKL hp]
    simp only [hp, false_and, false_or]

private theorem isCollinear_constant_iff (H K : Hyperplane k n) (hHK : H ≠ K) :
    Projectivization.IsCollinear {constantPoint k n, coefficientPoint H, coefficientPoint K} ↔
      Parallel H K := by
  rw [isCollinear_triple_iff_mem_projective_span_pair _ _ _
    (coefficientPoint_ne_constantPoint H).symm, coefficientPoint_mem_constant_span_iff]
  simp only [Ne.symm hHK, false_or]

private theorem eq_constant_or_coefficientPoint (p : ℙ k (Fin (n + 1) → k)) :
    p = constantPoint k n ∨ ∃ H : Hyperplane k n, coefficientPoint H = p := by
  by_cases hp : p = constantPoint k n
  · exact Or.inl hp
  · exact Or.inr ⟨hyperplaneOfCoefficientPoint p hp,
      coefficientPoint_hyperplaneOfCoefficientPoint p hp⟩

private theorem projectiveExtension_collinear_iff (π : Equiv.Perm (Hyperplane k n))
    (hp : ∀ H K, Parallel (π H) (π K) ↔ Parallel H K)
    (ht : ∀ H K L, DependentTriple (π H) (π K) (π L) ↔ DependentTriple H K L)
    (p q r : ℙ k (Fin (n + 1) → k)) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Projectivization.IsCollinear {projectiveExtension π p, projectiveExtension π q,
      projectiveExtension π r} ↔ Projectivization.IsCollinear {p, q, r} := by
  rcases eq_constant_or_coefficientPoint p with rfl | ⟨H, rfl⟩
  · rcases eq_constant_or_coefficientPoint q with rfl | ⟨K, rfl⟩
    · exact (hpq rfl).elim
    · rcases eq_constant_or_coefficientPoint r with rfl | ⟨L, rfl⟩
      · exact (hpr rfl).elim
      · have hKL := fun he : K = L ↦ hqr (congrArg coefficientPoint he)
        simpa only [projectiveExtension_constantPoint, projectiveExtension_coefficientPoint,
          isCollinear_constant_iff _ _ (π.injective.ne hKL), isCollinear_constant_iff K L hKL]
          using hp K L
  · rcases eq_constant_or_coefficientPoint q with rfl | ⟨K, rfl⟩
    · rcases eq_constant_or_coefficientPoint r with rfl | ⟨L, rfl⟩
      · exact (hqr rfl).elim
      · have hHL := fun he : H = L ↦ hpr (congrArg coefficientPoint he)
        simp only [projectiveExtension_constantPoint, projectiveExtension_coefficientPoint]
        rw [Set.insert_comm (coefficientPoint (π H)) (constantPoint k n),
          Set.insert_comm (coefficientPoint H) (constantPoint k n),
          isCollinear_constant_iff _ _ (π.injective.ne hHL), isCollinear_constant_iff H L hHL]
        exact hp H L
    · rcases eq_constant_or_coefficientPoint r with rfl | ⟨L, rfl⟩
      · have hHK := fun he : H = K ↦ hpq (congrArg coefficientPoint he)
        simp only [projectiveExtension_constantPoint, projectiveExtension_coefficientPoint]
        rw [Set.pair_comm (coefficientPoint (π K)) (constantPoint k n),
          Set.insert_comm (coefficientPoint (π H)) (constantPoint k n),
          Set.pair_comm (coefficientPoint K) (constantPoint k n),
          Set.insert_comm (coefficientPoint H) (constantPoint k n),
          isCollinear_constant_iff _ _ (π.injective.ne hHK), isCollinear_constant_iff H K hHK]
        exact hp H K
      · have hHK := fun he : H = K ↦ hpq (congrArg coefficientPoint he)
        have hHL := fun he : H = L ↦ hpr (congrArg coefficientPoint he)
        have hKL := fun he : K = L ↦ hqr (congrArg coefficientPoint he)
        simp only [projectiveExtension_coefficientPoint,
          coefficientPoints_collinear_iff _ _ _ (π.injective.ne hHK)
            (π.injective.ne hHL) (π.injective.ne hKL),
          coefficientPoints_collinear_iff H K L hHK hHL hKL, hp, ht]

/-- Preserving strict parallel pairs and guarded dependent triples makes the projective
extension preserve every line as an exact set image. This includes the inverse direction,
over every field and in every ambient dimension. Blueprint: the geometric assertion in I03. -/
theorem preservesProjectiveLines_projectiveExtension (π : Equiv.Perm (Hyperplane k n))
    (hp : ∀ H K, Parallel (π H) (π K) ↔ Parallel H K)
    (ht : ∀ H K L, DependentTriple (π H) (π K) (π L) ↔ DependentTriple H K L) :
    PreservesProjectiveLines (projectiveExtension π) := by
  intro p q hpq
  ext s
  obtain ⟨r, rfl⟩ := (projectiveExtension π).surjective s
  rw [(projectiveExtension π).injective.mem_set_image]
  by_cases hrp : r = p
  · subst r
    exact iff_of_true (Projectivization.Subspace.subset_span _ (by simp))
      (Projectivization.Subspace.subset_span _ (by simp))
  by_cases hrq : r = q
  · subst r
    exact iff_of_true (Projectivization.Subspace.subset_span _ (by simp))
      (Projectivization.Subspace.subset_span _ (by simp))
  change r ∈ Projectivization.Subspace.span {p, q} ↔
    projectiveExtension π r ∈ Projectivization.Subspace.span
      {projectiveExtension π p, projectiveExtension π q}
  rw [← isCollinear_triple_iff_mem_projective_span_pair p q r hpq,
    ← isCollinear_triple_iff_mem_projective_span_pair _ _ _
      ((projectiveExtension π).injective.ne hpq)]
  exact (projectiveExtension_collinear_iff π hp ht p q r hpq (Ne.symm hrp) (Ne.symm hrq)).symm

end OrlikSolomon.HyperplaneGT
