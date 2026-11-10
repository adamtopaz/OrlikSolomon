/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.HyperplaneGT.Topology.RatFunc.Automorphisms
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Quadratic
public import OrlikSolomon.HyperplaneGT.Topology.Basic
public import OrlikSolomon.HyperplaneGT.Topology.Krull
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Rational-function counterexample to the Krull comparison

Over a finite constant field, the actual finite automorphism group of `F(t)` supplies
finite stable saturation and hence a genuine cofinal arrangement system. Its pointwise
and stage permutation topologies are discrete, whereas Mathlib's Krull topology is
indiscrete. With prime constant field and binary coefficients, the actual M8 quadratic
diagram group is nontrivial, finite and discrete. Neither its direct Galois action nor
the forward M8 classification is continuous for the literal Krull source topology.

All topology statements name their choices explicitly; no instance replaces Mathlib's
Krull topology. The classifier source is the literal product of discrete coefficient
units and that actual Krull group. Finiteness and nontriviality are theorems used only
locally. The pointwise and Krull conclusions hold over arbitrary constant fields;
finite constants are needed for finite saturation and the finite actual diagram.

Blueprint: T08 (`prop:t08`).
-/

@[expose] public section

open scoped Topology

namespace OrlikSolomon.HyperplaneGT.RatFuncExamples

universe u

variable (F : Type u) [Field F]

/-- A finite-dimensional intermediate field has the whole rational-function Galois group
as its fixing subgroup. -/
theorem finiteIntermediateField_fixingSubgroup_eq_top
    (E : IntermediateField F (RatFunc F)) [FiniteDimensional F E] :
    E.fixingSubgroup = ⊤ := by
  rw [intermediateField_eq_bot_of_finiteDimensional F E,
    IntermediateField.fixingSubgroup_bot]

/-- Mathlib's actual Krull topology on the rational-function automorphism group is
indiscrete, over every constant field. Blueprint: `prop:t08`. -/
theorem krullTopology_eq_top : krullTopology F (RatFunc F) = ⊤ := by
  apply TopologicalSpace.ext_nhds
  intro σ
  rw [nhds_top]
  apply Filter.ext
  intro s
  rw [((galGroupBasis F (RatFunc F)).nhds_hasBasis σ).mem_iff, Filter.mem_top]
  constructor
  · rintro ⟨U, ⟨G, ⟨E, hE, rfl⟩, rfl⟩, hU⟩
    have : FiniteDimensional F E := hE
    rw [finiteIntermediateField_fixingSubgroup_eq_top F E] at hU
    apply Set.eq_univ_of_forall
    intro τ
    exact hU ⟨σ⁻¹ * τ, by simp, by simp⟩
  · rintro rfl
    refine ⟨Set.univ, ?_, Set.subset_univ _⟩
    exact ⟨⊤, top_fixedByFinite, rfl⟩

/-- The identity singleton is not open in the actual Krull topology: translation by one
is a distinct automorphism. -/
theorem not_krull_isOpen_singleton_one :
    ¬ @IsOpen (RatFunc F ≃ₐ[F] RatFunc F) (krullTopology F (RatFunc F)) {1} := by
  rw [krullTopology_eq_top, TopologicalSpace.isOpen_top_iff]
  rintro (h | h)
  · exact Set.singleton_ne_empty _ h
  · have hx : translation F 1 ∈ ({1} : Set (RatFunc F ≃ₐ[F] RatFunc F)) := by
      rw [h]
      exact Set.mem_univ _
    exact translation_one_ne_one F (Set.mem_singleton_iff.mp hx)

/-- All finite Galois-stable arrangements form a cofinal system over a finite constant
field. Cofinality uses the actual finite saturation of each finite set of hyperplanes.
This construction also works in dimension zero. Blueprint: `prop:t08`. -/
noncomputable def finiteStableCofinalSystem (F : Type u) [Field F] [Finite F] (n : ℕ) :
    CofinalSystem F (RatFunc F) n := by
  classical
  let : Finite (RatFunc F ≃ₐ[F] RatFunc F) := finite_algEquiv F
  let : Fintype (RatFunc F ≃ₐ[F] RatFunc F) := Fintype.ofFinite _
  refine ⟨Set.univ, ?_⟩
  intro s
  let t := Finset.univ.biUnion fun σ : RatFunc F ≃ₐ[F] RatFunc F => s.image (σ • ·)
  let A := Arrangement.ofFinset (t.image Subtype.val)
  have hmem (H : Hyperplane (RatFunc F) n) : H.val ∈ A ↔ H ∈ t := by
    constructor
    · intro h
      obtain ⟨K, hK, hKH⟩ := Finset.mem_image.mp (Arrangement.mem_ofFinset.mp h).1
      have hKH' : K = H := Subtype.ext hKH
      simpa only [hKH'] using hK
    · intro h
      exact Arrangement.mem_ofFinset.mpr
        ⟨Finset.mem_image.mpr ⟨H, h, rfl⟩, H.property⟩
  have hstable : IsGaloisStable (k₀ := F) A := by
    intro σ H hH
    obtain ⟨τ, _, hτ⟩ := Finset.mem_biUnion.mp ((hmem H).mp hH)
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hτ
    apply (hmem _).mpr
    exact Finset.mem_biUnion.mpr ⟨σ * τ, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨K, hK, mul_smul σ τ K⟩⟩
  refine ⟨⟨A, hstable⟩, Set.mem_univ _, ?_⟩
  intro H hH
  apply (hmem H).mpr
  exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨H, hH, one_smul _ H⟩⟩

/-- Every finite stable arrangement belongs to this supplied system. -/
@[simp] theorem mem_finiteStableCofinalSystem
    (F : Type u) [Field F] [Finite F] (n : ℕ)
    (A : StableArrangement F (RatFunc F) n) :
    A ∈ (finiteStableCofinalSystem F n).stages := Set.mem_univ _

/-- Fixing the rational variable determines an automorphism, so pointwise convergence
is discrete over every constant field. Blueprint: `prop:t08`. -/
theorem pointwiseTopology_eq_bot :
    galoisPointwiseTopology F (RatFunc F) = ⊥ := by
  let : TopologicalSpace (RatFunc F ≃ₐ[F] RatFunc F) :=
    galoisPointwiseTopology F (RatFunc F)
  let : IsTopologicalGroup (RatFunc F ≃ₐ[F] RatFunc F) :=
    galoisPointwise_isTopologicalGroup F (RatFunc F)
  have he : (fixingSubgroup (RatFunc F ≃ₐ[F] RatFunc F)
      ({RatFunc.X} : Set (RatFunc F)) : Set (RatFunc F ≃ₐ[F] RatFunc F)) = {1} := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixingSubgroup_iff, Set.mem_singleton_iff,
      AlgEquiv.smul_def, forall_eq]
    constructor
    · intro h
      apply AlgEquiv.coe_toAlgHom_injective
      exact algHom_ext_X F h
    · rintro rfl
      rfl
  have ho := (galoisPointwise_isClopen_fixing F (RatFunc F) {RatFunc.X}).isOpen
  rw [Finset.coe_singleton, he] at ho
  let := discreteTopology_of_isOpen_singleton_one ho
  exact DiscreteTopology.eq_bot

/-- The finite-intermediate-field fixing condition fails for rational functions, even
though finite stable arrangement systems exist over finite constants. -/
theorem not_KrullFixingCondition : ¬ KrullFixingCondition F (RatFunc F) := by
  intro h
  have he := (krull_eq_pointwise_iff F (RatFunc F)).mpr h
  rw [pointwiseTopology_eq_bot] at he
  apply not_krull_isOpen_singleton_one F
  rw [he]
  exact @isOpen_discrete _ ⊥ (discreteTopology_bot _) _

/-- The actual permutation topology of the supplied system is discrete in every positive
dimension. No statement in dimension zero is asserted. -/
theorem stagePermutationTopology_eq_bot [Finite F] (n : ℕ) (hn : 1 ≤ n) :
    (finiteStableCofinalSystem F n).galoisStagePermutationTopology = ⊥ := by
  rw [CofinalSystem.galoisStagePermutationTopology_eq_pointwise _ hn,
    pointwiseTopology_eq_bot]

/-- The singleton zero generates every prime field as a subfield. -/
theorem zero_generates_primeField (p : ℕ) [Fact p.Prime] :
    Subfield.closure ({0} : Set (ZMod p)) = ⊤ := Subsingleton.elim _ _

/-- The actual quadratic diagram group over binary coefficients is finite for the
supplied rational-function system over any prime field. -/
theorem finite_binary_diagramAut (p : ℕ) [Fact p.Prime] :
    Finite (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := by
  let := finite_algEquiv (ZMod p)
  exact Finite.of_equiv _ (quadraticAutEquiv (ZMod 2)
    (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)) (by simp)
    (zero_generates_primeField p) (by decide)).toEquiv

/-- The actual direct Galois action embeds the nontrivial rational-function automorphism
group into the binary-coefficient quadratic diagram group. -/
theorem nontrivial_binary_diagramAut (p : ℕ) [Fact p.Prime] :
    Nontrivial (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := by
  let := nontrivial_algEquiv (ZMod p)
  exact Function.Injective.nontrivial (galoisQuadraticAction_injective (ZMod 2)
    (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)) (by simp)
    (zero_generates_primeField p) (by decide))

/-- The original stage-and-common-target topology on the actual binary quadratic diagram
is discrete, by its Hausdorff separation and finiteness. Blueprint: `prop:t08`. -/
theorem binary_diagramTopology_eq_bot (p : ℕ) [Fact p.Prime] :
    DiagramAut.stageTopology (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p)) = ⊥ := by
  let := finite_binary_diagramAut p
  let : TopologicalSpace (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := DiagramAut.stageTopology _ _ _
  let : T2Space (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := FiniteStageTopology.diagramT2Space _ _ _
  exact DiscreteTopology.eq_bot

/-- The actual M8 direct Galois action is not continuous from Mathlib's Krull topology
to the original binary quadratic diagram topology. Blueprint: `prop:t08`. -/
theorem not_continuous_galoisQuadraticAction (p : ℕ) [Fact p.Prime] :
    ¬ @Continuous (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p))
      (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)))
      (krullTopology (ZMod p) (RatFunc (ZMod p)))
      (DiagramAut.stageTopology (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p)))
      (galoisQuadraticAction (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p))) := by
  let : TopologicalSpace (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := DiagramAut.stageTopology _ _ _
  intro hc
  have he : (galoisQuadraticAction (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) ⁻¹' {1} = {1} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (galoisQuadraticAction_injective (ZMod 2)
      (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)) (by simp)
      (zero_generates_primeField p) (by decide)).eq_iff' (map_one _)
  have ho : @IsOpen _ (DiagramAut.stageTopology (ZMod 2)
      (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p))) {1} := by
    rw [binary_diagramTopology_eq_bot]
    exact @isOpen_discrete _ ⊥ (discreteTopology_bot _) _
  exact not_krull_isOpen_singleton_one (ZMod p) (he ▸ ho.preimage hc)

/-- The forward actual M8 classification fails continuity for the literal product of
discrete binary units and Mathlib's Krull topology. Blueprint: `prop:t08`. -/
theorem not_continuous_quadraticAutEquiv (p : ℕ) [Fact p.Prime] :
    letI : TopologicalSpace (ZMod 2)ˣ := ⊥
    letI : TopologicalSpace (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) :=
      krullTopology (ZMod p) (RatFunc (ZMod p))
    ¬ @Continuous ((ZMod 2)ˣ × (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)))
      (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)))
      inferInstance (DiagramAut.stageTopology (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p)))
      (quadraticAutEquiv (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p)) (by simp) (zero_generates_primeField p) (by decide)) := by
  intro hc
  let : TopologicalSpace (ZMod 2)ˣ := ⊥
  let : TopologicalSpace (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) :=
    krullTopology (ZMod p) (RatFunc (ZMod p))
  have hi : Continuous (fun σ : RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p) ↦
      ((1 : (ZMod 2)ˣ), σ)) := continuous_const.prodMk continuous_id
  apply not_continuous_galoisQuadraticAction p
  convert hc.comp hi using 1
  funext σ
  simp only [Function.comp_apply, quadraticAutEquiv_apply, scalarQuadraticAut_one,
    one_mul, galoisQuadraticAction_apply]

/-- Consequently the actual M8 classification is not a homeomorphism for the literal
Krull product topology, despite all supplied-system classification hypotheses. -/
theorem not_isHomeomorph_quadraticAutEquiv (p : ℕ) [Fact p.Prime] :
    letI : TopologicalSpace (ZMod 2)ˣ := ⊥
    letI : TopologicalSpace (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) :=
      krullTopology (ZMod p) (RatFunc (ZMod p))
    ¬ @IsHomeomorph ((ZMod 2)ˣ × (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)))
      (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2) ({0} : Set (ZMod p)))
      inferInstance (DiagramAut.stageTopology (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p)))
      (quadraticAutEquiv (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
        ({0} : Set (ZMod p)) (by simp) (zero_generates_primeField p) (by decide)) := by
  let : TopologicalSpace (ZMod 2)ˣ := ⊥
  let : TopologicalSpace (RatFunc (ZMod p) ≃ₐ[ZMod p] RatFunc (ZMod p)) :=
    krullTopology (ZMod p) (RatFunc (ZMod p))
  let : TopologicalSpace (DiagramAut (ZMod 2) (finiteStableCofinalSystem (ZMod p) 2)
      ({0} : Set (ZMod p))) := DiagramAut.stageTopology _ _ _
  intro h
  exact not_continuous_quadraticAutEquiv p h.continuous

end OrlikSolomon.HyperplaneGT.RatFuncExamples
