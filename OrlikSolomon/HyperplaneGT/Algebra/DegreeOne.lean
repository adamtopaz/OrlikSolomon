/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Generators

/-!
# Canonical coordinates in degree one

`osDegreeOneEquiv` identifies the free module on a finite arrangement with the degree-one
piece of its Orlik–Solomon algebra. It sends a basis vector to the corresponding generator,
and commutes with inclusions of arrangements. `osDegreeOneBasis` and the inverse equivalence
give the canonical generator basis and its coordinates over any commutative coefficient ring.

`exists_os_word_sum` and `adjoin_range_osGenerator` express generation of the whole algebra.
No nontriviality assumption on the coefficients is used, and the empty arrangement is allowed.

Blueprint: A01 (`lem:a01`) of the cohomological hyperplane reconstruction blueprint.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open Module OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (R : Type v) [CommRing R] (𝒜 : Arrangement k V)

/-- Every Orlik–Solomon element is a finite linear combination of generator words, with no
assumption on the coefficient ring or the dimension of the ambient space.

Blueprint: A01 (`lem:a01`), generation of the full algebra. -/
theorem exists_os_word_sum (x : OSAlgebra R 𝒜) :
    ∃ c : List 𝒜 →₀ R, Finsupp.linearCombination R (word (generator R 𝒜)) c = x :=
  (span_range_eq_top_iff_surjective_finsuppLinearCombination (R := R)).mp
    (OSAlgebra.span_range_word R 𝒜) x

/-- The degree-one generators generate the entire Orlik–Solomon algebra as an algebra over its
coefficient ring. This does not assert that all relations are quadratic.

Blueprint: A01 (`lem:a01`), generation of the full algebra. -/
theorem adjoin_range_osGenerator : Algebra.adjoin R (Set.range (generator R 𝒜)) = ⊤ := by
  apply Subalgebra.toSubmodule_injective
  apply top_unique
  rw [← OSAlgebra.span_range_word R 𝒜]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨I, rfl⟩
  change word (generator R 𝒜) I ∈ Algebra.adjoin R (Set.range (generator R 𝒜))
  induction I with
  | nil => exact one_mem _
  | cons H I hI =>
    rw [word_cons]
    exact mul_mem (Algebra.subset_adjoin (Set.mem_range_self H)) hI

/-- The degree-one piece is exactly the span of the individual hyperplane generators.

Blueprint: A01 (`lem:a01`). -/
theorem span_range_osGenerator_eq_degree_one :
    Submodule.span R (Set.range (generator R 𝒜)) = degree R 𝒜 1 := by
  rw [← OSAlgebra.span_word_length]
  congr 1
  ext x
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨[H], rfl, word_singleton _ _⟩
  · rintro ⟨I, hI, rfl⟩
    cases I with
    | nil => simp at hI
    | cons H I =>
      cases I with
      | nil => exact ⟨H, (word_singleton _ _).symm⟩
      | cons K I => simp at hI

variable [FiniteDimensional k V]

/-- The canonical generator map identifies the free coefficient module on the hyperplanes with
the degree-one part of the Orlik–Solomon algebra. The coefficients may be the zero ring.

Blueprint: A01 (`lem:a01`). -/
def osDegreeOneEquiv : (𝒜 →₀ R) ≃ₗ[R] degree R 𝒜 1 :=
  (linearIndependent_generator R 𝒜).linearCombinationEquiv ≪≫ₗ
    LinearEquiv.ofEq _ _ (span_range_osGenerator_eq_degree_one R 𝒜)

/-- The canonical equivalence is the finite linear combination of the corresponding generators.
-/
@[simp]
theorem coe_osDegreeOneEquiv_apply (c : 𝒜 →₀ R) :
    (osDegreeOneEquiv R 𝒜 c : OSAlgebra R 𝒜) =
      Finsupp.linearCombination R (generator R 𝒜) c :=
  rfl

/-- A single coefficient maps to the same multiple of its hyperplane generator. -/
@[simp]
theorem osDegreeOneEquiv_single (H : 𝒜) (r : R) :
    osDegreeOneEquiv R 𝒜 (Finsupp.single H r) =
      r • (⟨generator R 𝒜 H, generator_mem_degree R 𝒜 H⟩ : degree R 𝒜 1) := by
  apply Subtype.ext
  simp

/-- The coordinate inverse sends a generator to its standard basis vector. -/
@[simp]
theorem osDegreeOneEquiv_symm_generator (H : 𝒜) :
    (osDegreeOneEquiv R 𝒜).symm ⟨generator R 𝒜 H, generator_mem_degree R 𝒜 H⟩ =
      Finsupp.single H 1 := by
  apply (osDegreeOneEquiv R 𝒜).injective
  simp

/-- The coordinates of a degree-one element reconstruct that element by a finite sum. -/
@[simp]
theorem linearCombination_osDegreeOneEquiv_symm (x : degree R 𝒜 1) :
    Finsupp.linearCombination R (generator R 𝒜) ((osDegreeOneEquiv R 𝒜).symm x) = x := by
  rw [← coe_osDegreeOneEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The canonical basis of degree one, indexed by the hyperplanes themselves.

Blueprint: A01 (`lem:a01`). -/
def osDegreeOneBasis : Basis 𝒜 R (degree R 𝒜 1) :=
  (Finsupp.basisSingleOne (R := R) (ι := 𝒜)).map (osDegreeOneEquiv R 𝒜)

/-- A vector of the canonical degree-one basis is its hyperplane generator. -/
@[simp]
theorem osDegreeOneBasis_apply (H : 𝒜) :
    osDegreeOneBasis R 𝒜 H = ⟨generator R 𝒜 H, generator_mem_degree R 𝒜 H⟩ := by
  simp [osDegreeOneBasis]

/-- The representation map of the canonical basis is the inverse generator equivalence. -/
@[simp]
theorem osDegreeOneBasis_repr (x : degree R 𝒜 1) :
    (osDegreeOneBasis R 𝒜).repr x = (osDegreeOneEquiv R 𝒜).symm x :=
  rfl

variable {𝒜} {ℬ 𝒞 : Arrangement k V}

/-- An inclusion of arrangements induces the usual presentation map, restricted to degree one.
-/
def osDegreeOneMap (h : 𝒜 ≤ ℬ) : degree R 𝒜 1 →ₗ[R] degree R ℬ 1 :=
  ((OSAlgebra.map R h).toLinearMap.comp (degree R 𝒜 1).subtype).codRestrict _ fun x ↦
    OSAlgebra.map_mem_degree R 𝒜 h x.2

omit [FiniteDimensional k V] in
/-- The degree-one inclusion map is the restriction of the presentation inclusion. -/
@[simp]
theorem coe_osDegreeOneMap_apply (h : 𝒜 ≤ ℬ) (x : degree R 𝒜 1) :
    (osDegreeOneMap R h x : OSAlgebra R ℬ) = OSAlgebra.map R h x :=
  rfl

omit [FiniteDimensional k V] in
/-- Inclusion preserves the degree-one generator with its underlying hyperplane label. -/
@[simp]
theorem osDegreeOneMap_generator (h : 𝒜 ≤ ℬ) (H : 𝒜) :
    osDegreeOneMap R h ⟨generator R 𝒜 H, generator_mem_degree R 𝒜 H⟩ =
      ⟨generator R ℬ (Arrangement.inclusion h H),
        generator_mem_degree R ℬ (Arrangement.inclusion h H)⟩ :=
  Subtype.ext (OSAlgebra.map_generator R h H)

omit [FiniteDimensional k V] in
/-- Inclusion of an arrangement into itself induces the identity in degree one. -/
@[simp]
theorem osDegreeOneMap_refl : osDegreeOneMap R (le_refl 𝒜) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (OSAlgebra.map_refl R) (x : OSAlgebra R 𝒜)

omit [FiniteDimensional k V] in
/-- Successive degree-one inclusion maps agree with inclusion along the composite. -/
@[simp]
theorem osDegreeOneMap_comp (h : 𝒜 ≤ ℬ) (h' : ℬ ≤ 𝒞) :
    (osDegreeOneMap R h').comp (osDegreeOneMap R h) = osDegreeOneMap R (h.trans h') := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (OSAlgebra.map_comp R h h') (x : OSAlgebra R 𝒜)

/-- The canonical free-module coordinates commute with inclusion of the hyperplane labels.

Blueprint: A01 (`lem:a01`), inclusion naturality. -/
theorem osDegreeOneEquiv_naturality (h : 𝒜 ≤ ℬ) (c : 𝒜 →₀ R) :
    osDegreeOneEquiv R ℬ (Finsupp.lmapDomain R R (Arrangement.inclusion h) c) =
      osDegreeOneMap R h (osDegreeOneEquiv R 𝒜 c) := by
  apply Subtype.ext
  simpa only [coe_osDegreeOneEquiv_apply, coe_osDegreeOneMap_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] using
    DFunLike.congr_fun (Finsupp.lmapDomain_linearCombination R
      (Arrangement.inclusion h) (OSAlgebra.map R h).toLinearMap
      (OSAlgebra.map_generator R h)) c

/-- Applying the coordinate inverse after inclusion extends coefficients by zero on new labels.
-/
@[simp]
theorem osDegreeOneEquiv_symm_map (h : 𝒜 ≤ ℬ) (x : degree R 𝒜 1) :
    (osDegreeOneEquiv R ℬ).symm (osDegreeOneMap R h x) =
      Finsupp.lmapDomain R R (Arrangement.inclusion h) ((osDegreeOneEquiv R 𝒜).symm x) := by
  apply (osDegreeOneEquiv R ℬ).injective
  rw [LinearEquiv.apply_symm_apply, osDegreeOneEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end OrlikSolomon.HyperplaneGT
