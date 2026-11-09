/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Universal.Support

/-!
# The global quadratic relation span

The universal quadratic relations are the span of the parallel-pair wedges and guarded
dependent-triple difference wedges on all affine hyperplanes. Finite-stage relations map
into this explicit span. Conversely, every element of the global span comes from the actual
quadratic relation submodule of some selected finite stage, for any chosen cofinal system.
No injectivity of degree-two restriction maps is asserted or used.

Blueprint: the relation-span part of U01 (`def:u01`, `lem:u01`).
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon.HyperplaneGT

variable {k : Type u} [Field k] {n : ℕ} (R : Type w) [CommRing R]

/-- The exterior product of two standard vectors in the universal hyperplane module. -/
def universalExteriorPair (H K : Hyperplane k n) : ⋀[R]^2 (Hyperplane k n →₀ R) :=
  exteriorPower.ιMulti R 2 ![Finsupp.single H 1, Finsupp.single K 1]

/-- A dependent-triple relation as the exterior product of two differences. -/
def universalExteriorDifferencePair (H K L : Hyperplane k n) :
    ⋀[R]^2 (Hyperplane k n →₀ R) :=
  exteriorPower.ιMulti R 2
    ![Finsupp.single H 1 - Finsupp.single L 1, Finsupp.single K 1 - Finsupp.single L 1]

/-- The pair wedge is the product of the two corresponding exterior generators. -/
@[simp]
theorem coe_universalExteriorPair (H K : Hyperplane k n) :
    (universalExteriorPair R H K : ExteriorAlgebra R (Hyperplane k n →₀ R)) =
      exteriorGen R H * exteriorGen R K := by
  simp [universalExteriorPair, ExteriorAlgebra.ιMulti_apply, exteriorGen]

/-- The difference wedge uses the actual exterior product, including in characteristic two. -/
@[simp]
theorem coe_universalExteriorDifferencePair (H K L : Hyperplane k n) :
    (universalExteriorDifferencePair R H K L : ExteriorAlgebra R (Hyperplane k n →₀ R)) =
      (exteriorGen R H - exteriorGen R L) * (exteriorGen R K - exteriorGen R L) := by
  simp [universalExteriorDifferencePair, ExteriorAlgebra.ιMulti_apply,
    exteriorGen]

/-- Extension by zero preserves the pair wedge and its actual hyperplane labels. -/
@[simp]
theorem map_finiteStageMap_osExteriorPair (𝒜 : Arrangement k (Fin n → k)) (H K : 𝒜) :
    exteriorPower.map 2 (finiteStageMap R 𝒜) (osExteriorPair R 𝒜 H K) =
      universalExteriorPair R (arrangementHyperplane 𝒜 H) (arrangementHyperplane 𝒜 K) := by
  apply Subtype.ext
  simp [exteriorPower.coe_map, exteriorGen, finiteStageMap]

/-- Extension by zero preserves the dependent-triple difference wedge. -/
@[simp]
theorem map_finiteStageMap_osExteriorDifferencePair (𝒜 : Arrangement k (Fin n → k))
    (H K L : 𝒜) :
    exteriorPower.map 2 (finiteStageMap R 𝒜) (osExteriorDifferencePair R 𝒜 H K L) =
      universalExteriorDifferencePair R (arrangementHyperplane 𝒜 H)
        (arrangementHyperplane 𝒜 K) (arrangementHyperplane 𝒜 L) := by
  apply Subtype.ext
  simp [exteriorPower.coe_map, exteriorGen, finiteStageMap]

/-- The explicit span of all parallel-pair and guarded dependent-triple relations on the
universal free hyperplane module. No cohomological colimit is assumed.

Blueprint: U01 (`def:u01`). -/
def universalQuadraticRelationSpan : Submodule R (⋀[R]^2 (Hyperplane k n →₀ R)) :=
  Submodule.span R {q |
    (∃ H K, Parallel H K ∧ q = universalExteriorPair R H K) ∨
    ∃ H K L, DependentTriple H K L ∧ q = universalExteriorDifferencePair R H K L}

/-- A parallel pair supplies a global quadratic relation. -/
theorem universalExteriorPair_mem (H K : Hyperplane k n) (h : Parallel H K) :
    universalExteriorPair R H K ∈ universalQuadraticRelationSpan R :=
  Submodule.subset_span (Or.inl ⟨H, K, h, rfl⟩)

/-- A guarded dependent triple supplies a global quadratic relation. -/
theorem universalExteriorDifferencePair_mem (H K L : Hyperplane k n)
    (h : DependentTriple H K L) :
    universalExteriorDifferencePair R H K L ∈ universalQuadraticRelationSpan R :=
  Submodule.subset_span (Or.inr ⟨H, K, L, h, rfl⟩)

/-- The actual finite-stage quadratic relation span maps into the global span. -/
theorem map_quadraticRelationSpan_finiteStageMap_le (𝒜 : Arrangement k (Fin n → k)) :
    (quadraticRelationSpan R 𝒜).map (exteriorPower.map 2 (finiteStageMap R 𝒜)) ≤
      universalQuadraticRelationSpan R := by
  rw [Submodule.map_le_iff_le_comap, quadraticRelationSpan, Submodule.span_le]
  rintro q (⟨H, K, h, rfl⟩ | ⟨H, K, L, h, rfl⟩)
  · change exteriorPower.map 2 (finiteStageMap R 𝒜) (osExteriorPair R 𝒜 H K) ∈
      universalQuadraticRelationSpan R
    rw [map_finiteStageMap_osExteriorPair]
    exact universalExteriorPair_mem R _ _ h
  · change exteriorPower.map 2 (finiteStageMap R 𝒜) (osExteriorDifferencePair R 𝒜 H K L) ∈
      universalQuadraticRelationSpan R
    rw [map_finiteStageMap_osExteriorDifferencePair]
    exact universalExteriorDifferencePair_mem R _ _ _ h

/-- Exterior-square extension by zero is compatible with finite-stage inclusion. -/
@[simp]
theorem exteriorPower_finiteStageMap_inclusion {𝒜 ℬ : Arrangement k (Fin n → k)}
    (h : 𝒜 ≤ ℬ) (q : ⋀[R]^2 (𝒜 →₀ R)) :
    exteriorPower.map 2 (finiteStageMap R ℬ)
        (exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h)) q) =
      exteriorPower.map 2 (finiteStageMap R 𝒜) q := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, finiteStageMap_comp_inclusion]

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k]

namespace CofinalSystem

variable (C : CofinalSystem k₀ k n)

private theorem exists_stage_parallel_pair (H K : Hyperplane k n) (h : Parallel H K) :
    ∃ 𝒜 : C.Stage, ∃ q ∈ quadraticRelationSpan R 𝒜.val.val,
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) q = universalExteriorPair R H K := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_containing {H, K}
  let H' : 𝒜.val.val := ⟨H.val, h𝒜 H (by simp)⟩
  let K' : 𝒜.val.val := ⟨K.val, h𝒜 K (by simp)⟩
  have hH : arrangementHyperplane 𝒜.val.val H' = H := Subtype.ext rfl
  have hK : arrangementHyperplane 𝒜.val.val K' = K := Subtype.ext rfl
  refine ⟨𝒜, osExteriorPair R 𝒜.val.val H' K', ?_, ?_⟩
  · apply osExteriorPair_mem_quadraticRelationSpan
    rwa [hH, hK]
  · rw [map_finiteStageMap_osExteriorPair, hH, hK]

private theorem exists_stage_dependent_triple (H K L : Hyperplane k n)
    (h : DependentTriple H K L) :
    ∃ 𝒜 : C.Stage, ∃ q ∈ quadraticRelationSpan R 𝒜.val.val,
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) q =
        universalExteriorDifferencePair R H K L := by
  classical
  obtain ⟨𝒜, h𝒜⟩ := C.exists_stage_containing {H, K, L}
  let H' : 𝒜.val.val := ⟨H.val, h𝒜 H (by simp)⟩
  let K' : 𝒜.val.val := ⟨K.val, h𝒜 K (by simp)⟩
  let L' : 𝒜.val.val := ⟨L.val, h𝒜 L (by simp)⟩
  have hH : arrangementHyperplane 𝒜.val.val H' = H := Subtype.ext rfl
  have hK : arrangementHyperplane 𝒜.val.val K' = K := Subtype.ext rfl
  have hL : arrangementHyperplane 𝒜.val.val L' = L := Subtype.ext rfl
  refine ⟨𝒜, osExteriorDifferencePair R 𝒜.val.val H' K' L', ?_, ?_⟩
  · apply osExteriorDifferencePair_mem_quadraticRelationSpan
    rwa [hH, hK, hL]
  · rw [map_finiteStageMap_osExteriorDifferencePair, hH, hK, hL]

/-- Every global relation comes from the actual quadratic relation span of a selected
finite stage, and every such finite-stage image is a global relation.

Blueprint: U01 (`lem:u01`). -/
theorem mem_universalQuadraticRelationSpan_iff (q : ⋀[R]^2 (Hyperplane k n →₀ R)) :
    q ∈ universalQuadraticRelationSpan R ↔
      ∃ 𝒜 : C.Stage, ∃ a ∈ quadraticRelationSpan R 𝒜.val.val,
        exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) a = q := by
  constructor
  · intro hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨H, K, h, rfl⟩ | ⟨H, K, L, h, rfl⟩
      · exact C.exists_stage_parallel_pair R H K h
      · exact C.exists_stage_dependent_triple R H K L h
    | zero =>
      obtain ⟨𝒜⟩ := (inferInstance : Nonempty C.Stage)
      exact ⟨𝒜, 0, Submodule.zero_mem _, map_zero _⟩
    | add q r _ _ hq hr =>
      obtain ⟨𝒜, a, ha, hqa⟩ := hq
      obtain ⟨ℬ, b, hb, hrb⟩ := hr
      obtain ⟨𝒟, h𝒜, hℬ⟩ := exists_ge_ge 𝒜 ℬ
      refine ⟨𝒟,
        exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion h𝒜)) a +
          exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion hℬ)) b,
        Submodule.add_mem _
          (quadraticRelationSpan_map_le R 𝒜.val.val h𝒜 ⟨a, ha, rfl⟩)
          (quadraticRelationSpan_map_le R ℬ.val.val hℬ ⟨b, hb, rfl⟩), ?_⟩
      simp only [map_add, exteriorPower_finiteStageMap_inclusion, hqa, hrb]
    | smul c q _ hq =>
      obtain ⟨𝒜, a, ha, rfl⟩ := hq
      exact ⟨𝒜, c • a, Submodule.smul_mem _ c ha, map_smul _ c a⟩
  · rintro ⟨𝒜, a, ha, rfl⟩
    exact map_quadraticRelationSpan_finiteStageMap_le R 𝒜.val.val ⟨a, ha, rfl⟩

/-- Finitely many global relations have witnesses in one common selected finite stage.
No injectivity of exterior-square inclusions or union closure of stages is used. -/
theorem exists_stage_relations (s : Finset (⋀[R]^2 (Hyperplane k n →₀ R)))
    (hs : ∀ q ∈ s, q ∈ universalQuadraticRelationSpan R) :
    ∃ 𝒜 : C.Stage, ∀ q ∈ s, ∃ a ∈ quadraticRelationSpan R 𝒜.val.val,
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) a = q := by
  classical
  have h : ∀ q : s, ∃ 𝒜 : C.Stage, ∃ a ∈ quadraticRelationSpan R 𝒜.val.val,
      exteriorPower.map 2 (finiteStageMap R 𝒜.val.val) a = q.val :=
    fun q ↦ (C.mem_universalQuadraticRelationSpan_iff R q.val).mp (hs q.val q.property)
  choose 𝒜 a ha hqa using h
  obtain ⟨𝒟, h𝒟⟩ := C.exists_ge_finset (s.attach.image 𝒜)
  refine ⟨𝒟, fun q hq ↦ ?_⟩
  let q' : s := ⟨q, hq⟩
  have hi : 𝒜 q' ≤ 𝒟 := h𝒟 _ (Finset.mem_image.mpr ⟨q', Finset.mem_attach _ _, rfl⟩)
  refine ⟨exteriorPower.map 2 (Finsupp.lmapDomain R R (Arrangement.inclusion hi)) (a q'),
    quadraticRelationSpan_map_le R (𝒜 q').val.val hi ⟨a q', ha q', rfl⟩, ?_⟩
  simpa only [exteriorPower_finiteStageMap_inclusion] using hqa q'

end CofinalSystem

end OrlikSolomon.HyperplaneGT
