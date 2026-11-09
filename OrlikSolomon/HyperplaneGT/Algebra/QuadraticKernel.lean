/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import OrlikSolomon.Algebra.HomogeneousRelations
public import OrlikSolomon.HyperplaneGT.Geometry.Coordinates.Incidence
public import OrlikSolomon.Presentation.Generators

/-!
# The exact quadratic kernel of the Orlik–Solomon quotient

The actual exterior-algebra quotient, restricted to degree two, has kernel spanned by
parallel-pair wedges and dependent-triple difference wedges. This assertion describes only
the degree-two kernel, without claiming that the full presentation is quadratic.

The coefficients are any commutative ring, including the zero ring and characteristic two.
Blueprint: A02 (`thm:a02`).
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.HyperplaneGT

open Module OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (R : Type v) [CommRing R] (𝒜 : Arrangement k V)

/-- The wedge of two standard hyperplane basis vectors, as an element of the exterior square.
-/
def osExteriorPair (H K : 𝒜) : ⋀[R]^2 (𝒜 →₀ R) :=
  ⟨exteriorGen R H * exteriorGen R K, by
    simpa using word_mem_exteriorPower R [H, K]⟩

/-- The exterior-square pair is the product of the corresponding exterior generators. -/
@[simp]
theorem coe_osExteriorPair (H K : 𝒜) :
    (osExteriorPair R 𝒜 H K : ExteriorAlgebra R (𝒜 →₀ R)) =
      exteriorGen R H * exteriorGen R K := rfl

/-- The wedge of the differences from a third hyperplane basis vector. -/
def osExteriorDifferencePair (H K L : 𝒜) : ⋀[R]^2 (𝒜 →₀ R) :=
  osExteriorPair R 𝒜 H K - osExteriorPair R 𝒜 H L + osExteriorPair R 𝒜 K L

/-- The dependent-triple difference wedge is the signed boundary of the triple. -/
theorem coe_osExteriorDifferencePair_eq_boundary (H K L : 𝒜) :
    (osExteriorDifferencePair R 𝒜 H K L : ExteriorAlgebra R (𝒜 →₀ R)) =
      wordBoundary (exteriorGen R) [H, K, L] := by
  simp only [osExteriorDifferencePair, Submodule.coe_add, Submodule.coe_sub,
    coe_osExteriorPair, wordBoundary_triple]
  abel

/-- The difference-pair expression uses actual square-zero exterior products, so is valid also
in characteristic two. -/
@[simp]
theorem coe_osExteriorDifferencePair (H K L : 𝒜) :
    (osExteriorDifferencePair R 𝒜 H K L : ExteriorAlgebra R (𝒜 →₀ R)) =
      (exteriorGen R H - exteriorGen R L) * (exteriorGen R K - exteriorGen R L) := by
  have hswap := (isExteriorFamily_exteriorGen R).mul_eq_neg_mul_swap L K
  simp only [osExteriorDifferencePair, Submodule.coe_add, Submodule.coe_sub,
    coe_osExteriorPair, sub_mul, mul_sub,
    (isExteriorFamily_exteriorGen R).mul_self L, hswap]
  abel

/-- The actual Orlik–Solomon quotient restricted to the exterior square, with its image in
the internal degree-two piece. -/
def osExteriorSquareMap : (⋀[R]^2 (𝒜 →₀ R)) →ₗ[R] degree R 𝒜 2 :=
  ((quotient R 𝒜).toLinearMap.comp (⋀[R]^2 (𝒜 →₀ R)).subtype).codRestrict _ fun x ↦
    RelationQuotient.mk_mem_grading x.2

/-- Forgetting the degree subtype gives the actual exterior-algebra quotient. -/
@[simp]
theorem coe_osExteriorSquareMap_apply (x : ⋀[R]^2 (𝒜 →₀ R)) :
    (osExteriorSquareMap R 𝒜 x : OSAlgebra R 𝒜) = quotient R 𝒜 x := rfl

/-- A standard wedge maps to the product of its Orlik–Solomon generators. -/
theorem coe_osExteriorSquareMap_pair (H K : 𝒜) :
    (osExteriorSquareMap R 𝒜 (osExteriorPair R 𝒜 H K) : OSAlgebra R 𝒜) =
      generator R 𝒜 H * generator R 𝒜 K := by
  simp

/-- A difference wedge maps to the product of the corresponding generator differences. -/
theorem coe_osExteriorSquareMap_differencePair (H K L : 𝒜) :
    (osExteriorSquareMap R 𝒜 (osExteriorDifferencePair R 𝒜 H K L) : OSAlgebra R 𝒜) =
      (generator R 𝒜 H - generator R 𝒜 L) *
        (generator R 𝒜 K - generator R 𝒜 L) := by
  simp

/-- Every degree-two Orlik–Solomon class has a representative in the exterior square. -/
theorem osExteriorSquareMap_surjective : Function.Surjective (osExteriorSquareMap R 𝒜) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := x.2
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

variable {𝒜} {ℬ 𝒞 : Arrangement k V}

/-- An inclusion of arrangements induces the presentation map restricted to degree two. -/
def osDegreeTwoMap (h : 𝒜 ≤ ℬ) : degree R 𝒜 2 →ₗ[R] degree R ℬ 2 :=
  ((OSAlgebra.map R h).toLinearMap.comp (degree R 𝒜 2).subtype).codRestrict _ fun x ↦
    OSAlgebra.map_mem_degree R 𝒜 h x.2

/-- The degree-two inclusion map is the usual inclusion map on the presentation. -/
@[simp]
theorem coe_osDegreeTwoMap_apply (h : 𝒜 ≤ ℬ) (x : degree R 𝒜 2) :
    (osDegreeTwoMap R h x : OSAlgebra R ℬ) = OSAlgebra.map R h x := rfl

/-- The identity inclusion acts identically on degree two. -/
@[simp]
theorem osDegreeTwoMap_refl : osDegreeTwoMap R (le_refl 𝒜) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (OSAlgebra.map_refl R) (x : OSAlgebra R 𝒜)

/-- Successive degree-two inclusion maps compose to the map of the composite inclusion. -/
@[simp]
theorem osDegreeTwoMap_comp (h : 𝒜 ≤ ℬ) (h' : ℬ ≤ 𝒞) :
    (osDegreeTwoMap R h').comp (osDegreeTwoMap R h) = osDegreeTwoMap R (h.trans h') := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (OSAlgebra.map_comp R h h') (x : OSAlgebra R 𝒜)

/-- Exterior-square inclusion preserves each standard wedge and its labels. -/
@[simp]
theorem map_osExteriorPair (h : 𝒜 ≤ ℬ) (H K : 𝒜) :
    exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h))
      (osExteriorPair R 𝒜 H K) =
        osExteriorPair R ℬ (Arrangement.inclusion h H) (Arrangement.inclusion h K) := by
  apply Subtype.ext
  simp [exteriorPower.coe_map, exteriorGen]

/-- Exterior-square inclusion preserves each wedge of generator differences. -/
@[simp]
theorem map_osExteriorDifferencePair (h : 𝒜 ≤ ℬ) (H K L : 𝒜) :
    exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h))
      (osExteriorDifferencePair R 𝒜 H K L) = osExteriorDifferencePair R ℬ
        (Arrangement.inclusion h H) (Arrangement.inclusion h K) (Arrangement.inclusion h L) := by
  simp [osExteriorDifferencePair]

/-- The actual degree-two exterior quotient commutes with inclusions of arrangements. -/
theorem osExteriorSquareMap_naturality (h : 𝒜 ≤ ℬ) (x : ⋀[R]^2 (𝒜 →₀ R)) :
    osExteriorSquareMap R ℬ
      (exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h)) x) =
      osDegreeTwoMap R h (osExteriorSquareMap R 𝒜 x) := by
  have hcomm : (quotient R ℬ).comp
      (ExteriorAlgebra.map (Finsupp.lmapDomain R R (Arrangement.inclusion h))) =
      (OSAlgebra.map R h).comp (quotient R 𝒜) := by
    apply exteriorAlgHom_ext
    intro H
    simp only [AlgHom.comp_apply, quotient_exteriorGen, OSAlgebra.map_generator]
    rw [show ExteriorAlgebra.map (Finsupp.lmapDomain R R (Arrangement.inclusion h))
        (exteriorGen R H) = exteriorGen R (Arrangement.inclusion h H) by simp [exteriorGen]]
    rfl
  apply Subtype.ext
  simpa only [coe_osExteriorSquareMap_apply, coe_osDegreeTwoMap_apply,
    exteriorPower.coe_map, AlgHom.comp_apply] using
    DFunLike.congr_fun hcomm (x : ExteriorAlgebra R (𝒜 →₀ R))

variable (𝒜)

private theorem empty_inter_length_ge_two {I : List 𝒜}
    (hI : Arrangement.inter I = ⊥) : 2 ≤ I.length := by
  cases I with
  | nil => simp at hI
  | cons H I =>
    cases I with
    | nil => exact ((𝒜.isHyperplane H.2).ne_bot (by simpa using hI)).elim
    | cons K I => simp

variable [FiniteDimensional k V]

/-- Every defining affine Orlik–Solomon relator has exterior degree at least two. -/
theorem osRelations_degree_ge_two :
    ∀ r ∈ osRelations R 𝒜, ∃ m, 2 ≤ m ∧ r ∈ ⋀[R]^m (𝒜 →₀ R) := by
  rintro r ⟨I, hI, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
  · exact ⟨I.length, empty_inter_length_ge_two 𝒜 h, word_mem_exteriorPower R I⟩
  · exact ⟨I.length - 1, by have := dependent_length_ge_three 𝒜 hI h; omega,
      wordBoundary_mem_exteriorPower R I⟩

/-- The quadratic relations expressed directly by the guarded affine presentation. -/
def osQuadraticRelationSpan : Submodule R (⋀[R]^2 (𝒜 →₀ R)) :=
  Submodule.span R {x | (∃ H K : 𝒜, (H : AffineSubspace k V) ⊓ K = ⊥ ∧
      x = osExteriorPair R 𝒜 H K) ∨
    ∃ H K L : 𝒜, [H, K, L].Nodup ∧ Arrangement.IsDependent [H, K, L] ∧
      x = osExteriorDifferencePair R 𝒜 H K L}

private theorem span_osRelations_degree_two :
    Submodule.span R (osRelations R 𝒜 ∩ (⋀[R]^2 (𝒜 →₀ R) : Set _)) =
      (osQuadraticRelationSpan R 𝒜).map (⋀[R]^2 (𝒜 →₀ R)).subtype := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro r ⟨⟨I, hI, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩, hr⟩
    · by_cases hlen : I.length = 2
      · obtain ⟨H, K, rfl⟩ := List.length_eq_two.mp hlen
        exact ⟨osExteriorPair R 𝒜 H K,
          Submodule.subset_span (Or.inl ⟨H, K, by simpa using h, rfl⟩), by simp⟩
      · have hz : word (exteriorGen R) I = 0 := by
          by_contra hz
          exact hlen (DirectSum.degree_eq_of_mem_mem (fun m ↦ ⋀[R]^m (𝒜 →₀ R))
            (word_mem_exteriorPower R I) hr hz)
        rw [hz]
        exact Submodule.zero_mem _
    · by_cases hlen : I.length = 3
      · obtain ⟨H, K, L, rfl⟩ := List.length_eq_three.mp hlen
        exact ⟨osExteriorDifferencePair R 𝒜 H K L,
          Submodule.subset_span (Or.inr ⟨H, K, L, hI, h, rfl⟩),
          coe_osExteriorDifferencePair_eq_boundary R 𝒜 H K L⟩
      · have hne : I.length - 1 ≠ 2 := by
          have := dependent_length_ge_three 𝒜 hI h
          omega
        have hz : wordBoundary (exteriorGen R) I = 0 := by
          by_contra hz
          exact hne (DirectSum.degree_eq_of_mem_mem (fun m ↦ ⋀[R]^m (𝒜 →₀ R))
            (wordBoundary_mem_exteriorPower R I) hr hz)
        rw [hz]
        exact Submodule.zero_mem _
  · rw [osQuadraticRelationSpan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, (⟨H, K, h, rfl⟩ | ⟨H, K, L, hI, h, rfl⟩), rfl⟩
    · have hHK : H ≠ K := by
        intro heq
        subst K
        exact (𝒜.isHyperplane H.2).ne_bot (by simpa using h)
      apply Submodule.subset_span
      exact ⟨⟨[H, K], by simp [hHK], Or.inl ⟨by simpa using h, by simp⟩⟩,
        (osExteriorPair R 𝒜 H K).2⟩
    · apply Submodule.subset_span
      exact ⟨⟨[H, K, L], hI, Or.inr ⟨h,
        coe_osExteriorDifferencePair_eq_boundary R 𝒜 H K L⟩⟩,
        (osExteriorDifferencePair R 𝒜 H K L).2⟩

/-- The kernel of the actual degree-two quotient is precisely the span of the length-two empty
products and length-three guarded dependent boundaries. Higher relators contribute nothing
in degree two, even when the coefficient ring is the zero ring.

Blueprint: the homogeneous extraction in A02 (`thm:a02`). -/
theorem osExteriorSquareMap_ker_eq :
    LinearMap.ker (osExteriorSquareMap R 𝒜) = osQuadraticRelationSpan R 𝒜 := by
  ext x
  change osExteriorSquareMap R 𝒜 x = 0 ↔ x ∈ osQuadraticRelationSpan R 𝒜
  rw [← Subtype.val_inj]
  change RelationQuotient.mk (osRelations R 𝒜) (x : ExteriorAlgebra R (𝒜 →₀ R)) = 0 ↔ _
  rw [exteriorAlgebra_quotient_eq_zero_iff (osRelations_degree_ge_two R 𝒜),
    span_osRelations_degree_two]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact Subtype.ext hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

section Coordinates

variable {n : ℕ} (𝒜 : Arrangement k (Fin n → k))

/-- The underlying affine hyperplane of a hyperplane label in an arrangement. -/
def arrangementHyperplane (H : 𝒜) : Hyperplane k n := ⟨H.val, 𝒜.isHyperplane H.2⟩

/-- The hyperplane associated to an arrangement label has the same underlying affine subspace.
-/
@[simp]
theorem arrangementHyperplane_val (H : 𝒜) : (arrangementHyperplane 𝒜 H).val = H.val := rfl

private theorem parallel_iff_empty_pair (H K : 𝒜) :
    Parallel (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K) ↔
      (H : AffineSubspace k (Fin n → k)) ⊓ K = ⊥ := by
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  intro heq
  have hHK : H = K := Subtype.ext (congrArg (fun X : Hyperplane k n ↦ X.val) heq)
  subst K
  exact (𝒜.isHyperplane H.2).ne_bot (by simpa using h)

private theorem dependentTriple_iff_dependent_list (H K L : 𝒜) :
    DependentTriple (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K)
      (arrangementHyperplane 𝒜 L) ↔
      [H, K, L].Nodup ∧ Arrangement.IsDependent [H, K, L] := by
  have hne (H K : 𝒜) : arrangementHyperplane 𝒜 H ≠ arrangementHyperplane 𝒜 K ↔ H ≠ K := by
    constructor
    · exact fun h hHK ↦ h (congrArg _ hHK)
    · exact fun h heq ↦ h (Subtype.ext (congrArg (fun X : Hyperplane k n ↦ X.val) heq))
  simp only [DependentTriple, hne, arrangementHyperplane_val]
  constructor
  · rintro ⟨hHK, hHL, hKL, hbot, hc⟩
    exact ⟨by simp [hHK, hHL, hKL], by
      simpa [Arrangement.IsDependent, Arrangement.inter_cons, ← inf_assoc, hc] using hbot⟩
  · rintro ⟨hI, hdep⟩
    have hdist : H ≠ K ∧ H ≠ L ∧ K ≠ L := by simpa [and_assoc] using hI
    have hbot : (H : AffineSubspace k (Fin n → k)) ⊓ K ⊓ L ≠ ⊥ := by
      simpa [Arrangement.inter_cons, inf_assoc] using hdep.1
    have hpair : (H : AffineSubspace k (Fin n → k)) ⊓ K ≠ ⊥ :=
      ne_bot_of_le_ne_bot hbot inf_le_left
    have hc := (𝒜.isHyperplane H.2).codim_inf_eq_two (𝒜.isHyperplane K.2)
      (fun h ↦ hdist.1 (Subtype.ext h.symm)) hpair
    have hlo := codim_le_codim (show
      (H : AffineSubspace k (Fin n → k)) ⊓ K ⊓ L ≤ (H : AffineSubspace k (Fin n → k)) ⊓ K from
        inf_le_left)
    have hhi : codim ((H : AffineSubspace k (Fin n → k)) ⊓ K ⊓ L) < 3 := by
      simpa [Arrangement.inter_cons, inf_assoc] using hdep.2
    exact ⟨hdist.1, hdist.2.1, hdist.2.2, hbot, by omega⟩

/-- The span of all parallel-pair wedges and all guarded dependent-triple difference wedges
on the arrangement labels. No choice of hyperplane equations enters this definition.

Blueprint: A02 (`thm:a02`). -/
def quadraticRelationSpan : Submodule R (⋀[R]^2 (𝒜 →₀ R)) :=
  Submodule.span R {x |
    (∃ H K : 𝒜, Parallel (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K) ∧
      x = osExteriorPair R 𝒜 H K) ∨
    ∃ H K L : 𝒜, DependentTriple (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K)
      (arrangementHyperplane 𝒜 L) ∧ x = osExteriorDifferencePair R 𝒜 H K L}

/-- Each parallel pair supplies a generator of the quadratic relation span. -/
theorem osExteriorPair_mem_quadraticRelationSpan (H K : 𝒜)
    (h : Parallel (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K)) :
    osExteriorPair R 𝒜 H K ∈ quadraticRelationSpan R 𝒜 :=
  Submodule.subset_span (Or.inl ⟨H, K, h, rfl⟩)

/-- Each guarded dependent triple supplies a generator of the quadratic relation span. -/
theorem osExteriorDifferencePair_mem_quadraticRelationSpan (H K L : 𝒜)
    (h : DependentTriple (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K)
      (arrangementHyperplane 𝒜 L)) :
    osExteriorDifferencePair R 𝒜 H K L ∈ quadraticRelationSpan R 𝒜 :=
  Submodule.subset_span (Or.inr ⟨H, K, L, h, rfl⟩)

/-- The exact degree-two kernel of the actual Orlik–Solomon quotient is the span of all
parallel-pair wedges and all guarded dependent-triple difference wedges. This does not assert
that the higher-degree presentation is generated by these quadratic relations.

Blueprint: A02 (`thm:a02`). -/
theorem quadraticKernel_eq_span :
    LinearMap.ker (osExteriorSquareMap R 𝒜) = quadraticRelationSpan R 𝒜 := by
  rw [osExteriorSquareMap_ker_eq]
  unfold osQuadraticRelationSpan quadraticRelationSpan
  congr 1
  ext x
  simp only [parallel_iff_empty_pair, dependentTriple_iff_dependent_list, and_assoc]

/-- Including hyperplane labels preserves the complete quadratic relation submodule. This is
an immediate consequence of naturality for the actual quotient kernel. -/
theorem quadraticRelationSpan_map_le {ℬ : Arrangement k (Fin n → k)} (h : 𝒜 ≤ ℬ) :
    (quadraticRelationSpan R 𝒜).map
      (exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h))) ≤
        quadraticRelationSpan R ℬ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← quadraticKernel_eq_span] at hx ⊢
  change osExteriorSquareMap R ℬ _ = 0
  rw [osExteriorSquareMap_naturality, show osExteriorSquareMap R 𝒜 x = 0 from hx, map_zero]

end Coordinates

end OrlikSolomon.HyperplaneGT
