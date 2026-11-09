/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Markings
public import OrlikSolomon.Presentation.Basic

/-!
# The Galois action on each full Orlik–Solomon algebra

A stable finite arrangement inherits the coefficient Galois permutation on its hyperplane
labels. This permutation preserves the intersection and codimension of every list, so it
preserves both complete families of defining relations: empty-intersection words and guarded
dependent boundaries. The presentation universal property gives an algebra automorphism over
any commutative coefficient ring, including the zero ring.

The action preserves every exterior-degree submodule, commutes with arrangement inclusions,
and fixes the ordered labels of every available marking. Its construction uses semilinear
incidence transport, rather than geometric pullback along a linear map.

Blueprint: the finite-stage algebraic construction of S02 (`lem:s02`). Diagram packaging is
separate from this leaf.
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

open OSAlgebra

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {n : ℕ}

/-- The permutation of a stable arrangement's labels induced by a base-field automorphism. -/
def galoisLabelEquiv (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) : 𝒜.val ≃ 𝒜.val where
  toFun H := ⟨fieldAffineSubspace σ.toRingEquiv H.val,
    𝒜.property σ (⟨H.val, 𝒜.val.isHyperplane H.property⟩ : Hyperplane k n) H.property⟩
  invFun H := ⟨fieldAffineSubspace σ⁻¹.toRingEquiv H.val,
    𝒜.property σ⁻¹ (⟨H.val, 𝒜.val.isHyperplane H.property⟩ : Hyperplane k n) H.property⟩
  left_inv H := by
    apply Subtype.ext
    exact fieldAffineSubspace_symm σ.toRingEquiv H.val
  right_inv H := by
    apply Subtype.ext
    exact fieldAffineSubspace_symm σ⁻¹.toRingEquiv H.val

/-- The underlying affine subspace is transported by the coordinate field automorphism. -/
@[simp]
theorem galoisLabelEquiv_val (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) (H : 𝒜.val) :
    (galoisLabelEquiv 𝒜 σ H).val = fieldAffineSubspace σ.toRingEquiv H.val := rfl

@[simp]
theorem galoisLabelEquiv_one (𝒜 : StableArrangement k₀ k n) (H : 𝒜.val) :
    galoisLabelEquiv 𝒜 1 H = H := by
  apply Subtype.ext
  exact fieldAffineSubspace_refl H.val

/-- The covariant label action has the same composition order as the Galois group. -/
@[simp]
theorem galoisLabelEquiv_mul (𝒜 : StableArrangement k₀ k n) (σ τ : k ≃ₐ[k₀] k)
    (H : 𝒜.val) :
    galoisLabelEquiv 𝒜 (σ * τ) H = galoisLabelEquiv 𝒜 σ (galoisLabelEquiv 𝒜 τ H) := by
  apply Subtype.ext
  exact fieldAffineSubspace_trans τ.toRingEquiv σ.toRingEquiv H.val

@[simp]
theorem galoisLabelEquiv_symm (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    (galoisLabelEquiv 𝒜 σ).symm = galoisLabelEquiv 𝒜 σ⁻¹ := by
  ext H
  rfl

/-- Label permutations commute with the inclusion of stable arrangements. -/
@[simp]
theorem inclusion_galoisLabelEquiv {𝒜 ℬ : StableArrangement k₀ k n} (h : 𝒜 ≤ ℬ)
    (σ : k ≃ₐ[k₀] k) (H : 𝒜.val) :
    Arrangement.inclusion h (galoisLabelEquiv 𝒜 σ H) =
      galoisLabelEquiv ℬ σ (Arrangement.inclusion h H) := by
  apply Subtype.ext
  rfl

/-- The intersection of every transformed list is the semilinear image of its intersection.
This includes the empty list and lists with repetitions. -/
theorem inter_map_galoisLabelEquiv (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (I : List 𝒜.val) :
    Arrangement.inter (I.map (galoisLabelEquiv 𝒜 σ)) =
      fieldAffineSubspace σ.toRingEquiv (Arrangement.inter I) := by
  induction I with
  | nil =>
    simp only [List.map_nil, Arrangement.inter_nil]
    ext x
    simp only [mem_fieldAffineSubspace, AffineSubspace.mem_top]
  | cons H I ih =>
    simp only [List.map_cons, Arrangement.inter_cons, galoisLabelEquiv_val, ih,
      fieldAffineSubspace_inf]

/-- Empty-intersection relations are preserved in both directions, in every length. -/
@[simp]
theorem inter_map_galoisLabelEquiv_eq_bot_iff (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (I : List 𝒜.val) :
    Arrangement.inter (I.map (galoisLabelEquiv 𝒜 σ)) = ⊥ ↔ Arrangement.inter I = ⊥ := by
  rw [inter_map_galoisLabelEquiv, fieldAffineSubspace_eq_bot_iff]

/-- Guarded dependent-boundary relations are preserved in both directions, in every length.
The guard remains part of the predicate. -/
@[simp]
theorem isDependent_map_galoisLabelEquiv_iff (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (I : List 𝒜.val) :
    Arrangement.IsDependent (I.map (galoisLabelEquiv 𝒜 σ)) ↔ Arrangement.IsDependent I := by
  simp only [Arrangement.IsDependent, inter_map_galoisLabelEquiv, ne_eq,
    fieldAffineSubspace_eq_bot_iff, codim_fieldAffineSubspace, List.length_map]

variable (R : Type w) [CommRing R]

/-- The permuted generators satisfy all relations of the actual OS presentation. -/
theorem isFamily_galoisLabelEquiv (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    IsFamily 𝒜.val (fun H ↦ generator R 𝒜.val (galoisLabelEquiv 𝒜 σ H)) where
  toIsExteriorFamily := (isExteriorFamily_generator R 𝒜.val).comp _
  word_eq_zero I _ he := by
    rw [← word_map]
    exact word_eq_zero_of_inter_eq_bot R 𝒜.val
      ((inter_map_galoisLabelEquiv_eq_bot_iff 𝒜 σ I).mpr he)
  wordBoundary_eq_zero I _ hd := by
    rw [← wordBoundary_map]
    exact wordBoundary_eq_zero_of_isDependent R 𝒜.val
      ((isDependent_map_galoisLabelEquiv_iff 𝒜 σ I).mpr hd)

/-- The presentation map induced by the Galois permutation of a stable arrangement's labels. -/
def galoisOSAlgebraHom (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    OSAlgebra R 𝒜.val →ₐ[R] OSAlgebra R 𝒜.val :=
  lift _ (isFamily_galoisLabelEquiv R 𝒜 σ)

/-- The Galois presentation map sends a generator to the generator of its transformed label. -/
@[simp]
theorem galoisOSAlgebraHom_generator (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (H : 𝒜.val) :
    galoisOSAlgebraHom R 𝒜 σ (generator R 𝒜.val H) =
      generator R 𝒜.val (galoisLabelEquiv 𝒜 σ H) := lift_generator _ _ H

/-- The full OS algebra automorphism induced by a Galois permutation of hyperplanes.
It is linear over the independent coefficient ring and uses all defining relations.

Blueprint: the finite-stage automorphism of S02 (`lem:s02`). -/
def galoisOSAlgebraEquiv (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    OSAlgebra R 𝒜.val ≃ₐ[R] OSAlgebra R 𝒜.val :=
  AlgEquiv.ofAlgHom (galoisOSAlgebraHom R 𝒜 σ) (galoisOSAlgebraHom R 𝒜 σ⁻¹)
    (by
      apply algHom_ext
      intro H
      simp only [AlgHom.comp_apply, galoisOSAlgebraHom_generator, AlgHom.id_apply]
      exact congrArg (generator R 𝒜.val) ((galoisLabelEquiv 𝒜 σ).apply_symm_apply H))
    (by
      apply algHom_ext
      intro H
      simp only [AlgHom.comp_apply, galoisOSAlgebraHom_generator, AlgHom.id_apply]
      exact congrArg (generator R 𝒜.val) ((galoisLabelEquiv 𝒜 σ).symm_apply_apply H))

/-- The Galois algebra automorphism sends each generator to its transformed label. -/
@[simp]
theorem galoisOSAlgebraEquiv_generator (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (H : 𝒜.val) :
    galoisOSAlgebraEquiv R 𝒜 σ (generator R 𝒜.val H) =
      generator R 𝒜.val (galoisLabelEquiv 𝒜 σ H) :=
  galoisOSAlgebraHom_generator R 𝒜 σ H

/-- The action carries every generator word to the word of the transformed labels. -/
theorem galoisOSAlgebraEquiv_word (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    (I : List 𝒜.val) :
    galoisOSAlgebraEquiv R 𝒜 σ (word (generator R 𝒜.val) I) =
      word (generator R 𝒜.val) (I.map (galoisLabelEquiv 𝒜 σ)) := by
  simp [word_map]

/-- The action carries signed boundaries to signed boundaries of the transformed labels.
There is no restriction on the length of the list. -/
theorem galoisOSAlgebraEquiv_wordBoundary (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (I : List 𝒜.val) :
    galoisOSAlgebraEquiv R 𝒜 σ (wordBoundary (generator R 𝒜.val) I) =
      wordBoundary (generator R 𝒜.val) (I.map (galoisLabelEquiv 𝒜 σ)) := by
  simp [wordBoundary_map]

/-- The identity field automorphism acts identically on the full algebra. -/
@[simp]
theorem galoisOSAlgebraEquiv_one (𝒜 : StableArrangement k₀ k n) :
    galoisOSAlgebraEquiv R 𝒜 1 = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro H
  simp

/-- The algebra automorphisms compose in the same order as the Galois group. -/
theorem galoisOSAlgebraEquiv_mul (𝒜 : StableArrangement k₀ k n) (σ τ : k ≃ₐ[k₀] k) :
    galoisOSAlgebraEquiv R 𝒜 (σ * τ) =
      galoisOSAlgebraEquiv R 𝒜 σ * galoisOSAlgebraEquiv R 𝒜 τ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro H
  simp

/-- The Galois group acts by coefficient-linear automorphisms of each stable-stage algebra.

Blueprint: the finite-stage group action in S02 (`lem:s02`). -/
def galoisOSAlgebraAction (𝒜 : StableArrangement k₀ k n) :
    (k ≃ₐ[k₀] k) →* (OSAlgebra R 𝒜.val ≃ₐ[R] OSAlgebra R 𝒜.val) where
  toFun := galoisOSAlgebraEquiv R 𝒜
  map_one' := galoisOSAlgebraEquiv_one R 𝒜
  map_mul' := galoisOSAlgebraEquiv_mul R 𝒜

@[simp]
theorem galoisOSAlgebraAction_apply (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    galoisOSAlgebraAction R 𝒜 σ = galoisOSAlgebraEquiv R 𝒜 σ := rfl

/-- The inverse algebra automorphism is induced by the inverse field automorphism. -/
@[simp]
theorem galoisOSAlgebraEquiv_symm (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) :
    (galoisOSAlgebraEquiv R 𝒜 σ).symm = galoisOSAlgebraEquiv R 𝒜 σ⁻¹ :=
  (map_inv (galoisOSAlgebraAction R 𝒜) σ).symm

/-- The Galois action preserves every degree, including degree zero and degrees above the
ambient dimension. -/
theorem galoisOSAlgebraEquiv_mem_degree (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k)
    {d : ℕ} {x : OSAlgebra R 𝒜.val} (hx : x ∈ degree R 𝒜.val d) :
    galoisOSAlgebraEquiv R 𝒜 σ x ∈ degree R 𝒜.val d := by
  rw [← OSAlgebra.span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl, rfl⟩ := hx
    rw [galoisOSAlgebraEquiv_word]
    simpa only [List.length_map] using
      word_mem_degree R 𝒜.val (I.map (galoisLabelEquiv 𝒜 σ))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- Degree membership is invariant in both directions under the Galois algebra action. -/
@[simp]
theorem galoisOSAlgebraEquiv_mem_degree_iff (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) {d : ℕ} {x : OSAlgebra R 𝒜.val} :
    galoisOSAlgebraEquiv R 𝒜 σ x ∈ degree R 𝒜.val d ↔ x ∈ degree R 𝒜.val d := by
  constructor
  · intro hx
    have h := galoisOSAlgebraEquiv_mem_degree R 𝒜 σ⁻¹ hx
    rw [← galoisOSAlgebraEquiv_symm, AlgEquiv.symm_apply_apply] at h
    exact h
  · exact galoisOSAlgebraEquiv_mem_degree R 𝒜 σ

/-- The Galois action preserves each full degree submodule by equality. -/
theorem map_degree_galoisOSAlgebraEquiv (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (d : ℕ) :
    (degree R 𝒜.val d).map (galoisOSAlgebraEquiv R 𝒜 σ).toLinearMap = degree R 𝒜.val d := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact galoisOSAlgebraEquiv_mem_degree R 𝒜 σ hx
  · intro x hx
    refine ⟨(galoisOSAlgebraEquiv R 𝒜 σ).symm x, ?_, ?_⟩
    · rw [galoisOSAlgebraEquiv_symm]
      exact galoisOSAlgebraEquiv_mem_degree R 𝒜 σ⁻¹ hx
    · exact (galoisOSAlgebraEquiv R 𝒜 σ).apply_symm_apply x

/-- Stable-stage inclusion maps commute with the full Galois action. -/
theorem galoisOSAlgebraEquiv_naturality {𝒜 ℬ : StableArrangement k₀ k n} (h : 𝒜 ≤ ℬ)
    (σ : k ≃ₐ[k₀] k) :
    (OSAlgebra.map R h).comp (galoisOSAlgebraEquiv R 𝒜 σ).toAlgHom =
      (galoisOSAlgebraEquiv R ℬ σ).toAlgHom.comp (OSAlgebra.map R h) := by
  apply algHom_ext
  intro H
  simp

/-- Every available marking label is fixed by the stage's Galois permutation. -/
@[simp]
theorem galoisLabelEquiv_fiberLabel {S : Set k₀} (𝒜 : StableArrangement k₀ k n)
    (σ : k ≃ₐ[k₀] k) (w : Marking S n) (hw : w.Available 𝒜.val) (a : Fin 2) :
    galoisLabelEquiv 𝒜 σ (w.fiberLabel hw a) = w.fiberLabel hw a := by
  apply Subtype.ext
  rw [galoisLabelEquiv_val, w.fiberLabel_val]
  exact congrArg Subtype.val (w.galois_smul_fiber σ (a.val : k₀))

/-- The full algebra action fixes each of the two ordered generators pulled back by a marking.
-/
theorem galoisOSAlgebraEquiv_generator_fiberLabel {S : Set k₀}
    (𝒜 : StableArrangement k₀ k n) (σ : k ≃ₐ[k₀] k) (w : Marking S n)
    (hw : w.Available 𝒜.val) (a : Fin 2) :
    galoisOSAlgebraEquiv R 𝒜 σ (generator R 𝒜.val (w.fiberLabel hw a)) =
      generator R 𝒜.val (w.fiberLabel hw a) := by
  simp

end OrlikSolomon.HyperplaneGT
