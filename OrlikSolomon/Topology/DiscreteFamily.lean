/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Order.Filter.Pi

/-!
# Subgroups of discrete families with a common target

A family of discrete groups and one discrete common target give their existing product
and every subgroup a named topology. The component criterion for continuity and the finite
coordinate neighborhood basis require no topology on the data defining the groups.

These helpers do not install any global topology instances on the factors or the subgroup.
-/

@[expose] public section

namespace OrlikSolomon.DiscreteFamily

open Filter Topology

universe u v w

variable {ι : Type u} (M : ι → Type v) (T : Type w)

/-- The product topology on discrete complete factors and a discrete common target. -/
@[instance_reducible]
def topology : TopologicalSpace ((∀ i, M i) × T) :=
  letI : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  letI : TopologicalSpace T := ⊥
  inferInstance

variable {M T} [∀ i, Group (M i)] [Group T]

/-- The induced topology on an existing subgroup of a discrete family with common target. -/
@[instance_reducible]
def subgroupTopology (G : Subgroup ((∀ i, M i) × T)) : TopologicalSpace G :=
  TopologicalSpace.induced Subtype.val (topology M T)

/-- The projection from a subgroup to one complete factor. -/
def stageHom (G : Subgroup ((∀ i, M i) × T)) (i : ι) : G →* M i where
  toFun g := g.val.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The projection from a subgroup to its common target. -/
def targetHom (G : Subgroup ((∀ i, M i) × T)) : G →* T where
  toFun g := g.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Simultaneous identity at one complete factor and at the common target. -/
def stageKernel (G : Subgroup ((∀ i, M i) × T)) (i : ι) : Subgroup G :=
  ((stageHom G i).prod (targetHom G)).ker

@[simp]
theorem mem_stageKernel (G : Subgroup ((∀ i, M i) × T)) (i : ι) (g : G) :
    g ∈ stageKernel G i ↔ g.val.1 i = 1 ∧ g.val.2 = 1 := by
  change (g.val.1 i, g.val.2) = (1, 1) ↔ _
  simp only [Prod.mk.injEq]

/-- The named subgroup topology makes multiplication and inversion continuous. -/
theorem isTopologicalGroup (G : Subgroup ((∀ i, M i) × T)) :
    @IsTopologicalGroup G (subgroupTopology G) _ := by
  let : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  let : ∀ i, DiscreteTopology (M i) := fun i ↦ discreteTopology_bot (M i)
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := discreteTopology_bot T
  exact isTopologicalGroup_induced G.subtype

/-- Discrete component coordinates separate distinct subgroup elements. -/
theorem t2Space (G : Subgroup ((∀ i, M i) × T)) :
    @T2Space G (subgroupTopology G) := by
  let : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  let : ∀ i, DiscreteTopology (M i) := fun i ↦ discreteTopology_bot (M i)
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := discreteTopology_bot T
  change T2Space G
  infer_instance

/-- Continuity into the subgroup is equivalent to continuity of every complete component,
including the common target, with its discrete topology. -/
theorem continuous_iff (G : Subgroup ((∀ i, M i) × T)) {X : Type*}
    [TopologicalSpace X] (f : X → G) :
    @Continuous X G _ (subgroupTopology G) f ↔
      (∀ i, @Continuous X (M i) _ ⊥ (fun x ↦ (f x).val.1 i)) ∧
        @Continuous X T _ ⊥ (fun x ↦ (f x).val.2) := by
  let : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  let : TopologicalSpace T := ⊥
  change Continuous f ↔ _
  rw [continuous_induced_rng]
  change Continuous (fun x ↦ ((f x).val.1, (f x).val.2)) ↔ _
  rw [continuous_prodMk, continuous_pi_iff]

/-- The projection to a complete factor is continuous for the named subgroup topology. -/
theorem continuous_stageHom (G : Subgroup ((∀ i, M i) × T)) (i : ι) :
    @Continuous G (M i) (subgroupTopology G) ⊥ (stageHom G i) := by
  let : TopologicalSpace G := subgroupTopology G
  exact ((continuous_iff G id).mp continuous_id).1 i

/-- The common-target projection is continuous for the named subgroup topology. -/
theorem continuous_targetHom (G : Subgroup ((∀ i, M i) × T)) :
    @Continuous G T (subgroupTopology G) ⊥ (targetHom G) := by
  let : TopologicalSpace G := subgroupTopology G
  exact ((continuous_iff G id).mp continuous_id).2

/-- Clopen coordinate cylinders separate distinct elements of the subgroup. -/
theorem totallySeparatedSpace (G : Subgroup ((∀ i, M i) × T)) :
    @TotallySeparatedSpace G (subgroupTopology G) := by
  classical
  let : TopologicalSpace G := subgroupTopology G
  let : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  let : ∀ i, DiscreteTopology (M i) := fun i ↦ discreteTopology_bot (M i)
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := discreteTopology_bot T
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro g h hne
  by_cases htarget : g.val.2 = h.val.2
  · have hstage : g.val.1 ≠ h.val.1 := fun hs ↦ hne (Subtype.ext (Prod.ext hs htarget))
    obtain ⟨i, hi⟩ : ∃ i, g.val.1 i ≠ h.val.1 i := by
      by_contra! heq
      exact hstage (funext heq)
    refine ⟨(stageHom G i) ⁻¹' {g.val.1 i},
      (isClopen_discrete _).preimage (continuous_stageHom G i), rfl, ?_⟩
    exact fun heq ↦ hi heq.symm
  · refine ⟨(targetHom G) ⁻¹' {g.val.2},
      (isClopen_discrete _).preimage (continuous_targetHom G), rfl, ?_⟩
    exact fun heq ↦ htarget heq.symm

/-- A stage kernel is normal as the kernel of the paired component homomorphism. -/
instance stageKernel_normal (G : Subgroup ((∀ i, M i) × T)) (i : ι) :
    (stageKernel G i).Normal :=
  inferInstanceAs (((stageHom G i).prod (targetHom G)).ker.Normal)

/-- Simultaneous identity on one complete factor and the target is a clopen condition. -/
theorem isClopen_stageKernel (G : Subgroup ((∀ i, M i) × T)) (i : ι) :
    @IsClopen G (subgroupTopology G) (stageKernel G i : Set G) := by
  let : TopologicalSpace G := subgroupTopology G
  let : TopologicalSpace (M i) := ⊥
  let : DiscreteTopology (M i) := discreteTopology_bot (M i)
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := discreteTopology_bot T
  have hstage := (isClopen_discrete ({1} : Set (M i))).preimage (continuous_stageHom G i)
  have htarget := (isClopen_discrete ({1} : Set T)).preimage (continuous_targetHom G)
  convert hstage.inter htarget using 1
  ext g
  exact mem_stageKernel G i g

/-- Each left coset of a stage kernel is clopen. -/
theorem isClopen_stageKernel_leftCoset (G : Subgroup ((∀ i, M i) × T)) (i : ι) (g : G) :
    @IsClopen G (subgroupTopology G) {h : G | g⁻¹ * h ∈ stageKernel G i} := by
  let : TopologicalSpace G := subgroupTopology G
  have : IsTopologicalGroup G := isTopologicalGroup G
  exact (isClopen_stageKernel G i).preimage (continuous_const.mul continuous_id)

/-- Finite complete-factor agreement and common-target agreement form a neighborhood basis. -/
theorem nhds_one_finiteBasis (G : Subgroup ((∀ i, M i) × T)) :
    (@nhds G (subgroupTopology G) 1).HasBasis Set.Finite
      (fun I : Set ι ↦ {g : G | (∀ i ∈ I, g.val.1 i = 1) ∧ g.val.2 = 1}) := by
  let : ∀ i, TopologicalSpace (M i) := fun _ ↦ ⊥
  let : ∀ i, DiscreteTopology (M i) := fun i ↦ discreteTopology_bot (M i)
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := discreteTopology_bot T
  have hfamily : (𝓝 (1 : (∀ i, M i) × T)).HasBasis Set.Finite
      (fun I : Set ι ↦ {g : (∀ i, M i) × T |
        (∀ i ∈ I, g.1 i = 1) ∧ g.2 = 1}) := by
    change (𝓝 ((fun i ↦ (1 : M i)), (1 : T))).HasBasis _ _
    rw [nhds_prod_eq, nhds_pi]
    simp only [nhds_discrete]
    have h := (Filter.hasBasis_pi_pure (fun i ↦ (1 : M i))).prod_principal ({1} : Set T)
    rw [Filter.principal_singleton] at h
    refine h.congr (fun _ ↦ Iff.rfl) ?_
    intro I _
    ext g
    simp
  change (𝓝 (⟨(1 : (∀ i, M i) × T), G.one_mem⟩ : G)).HasBasis _ _
  rw [nhds_subtype_eq_comap]
  exact hfamily.comap Subtype.val


end OrlikSolomon.DiscreteFamily
