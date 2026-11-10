/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois.Extraction
public import OrlikSolomon.HyperplaneGT.Reconstruction.Galois.Geometry
public import OrlikSolomon.HyperplaneGT.Reconstruction.Incidence.Relations

/-!
# The scalar kernel of Galois extraction

A trivial recovered hyperplane permutation makes the primal generator units agree along
every guarded dependent triple. Connectivity of the actual hyperplane geometry makes the
unit independent of the label. The universal action, every selected stage, and the one
common marking target consequently have that same primal scalar. The unit is inverse to
the dual inertia unit.

Blueprint: S01 (`lem:s01`).
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DiagramAut

universe u v r

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {R : Type r} [CommRing R] [IsLocalRing R] {n : ℕ}
  {C : CofinalSystem k₀ k n} {S : Set k₀}

private theorem primalUnit_eq_of_dependentTriple (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (hperm : g.hyperplanePerm hS hn = 1)
    (H K L : Hyperplane k n) (ht : DependentTriple H K L) :
    (g.hyperplaneUnit hS hn H)⁻¹ = (g.hyperplaneUnit hS hn K)⁻¹ := by
  have hr := (dependentTriple_rotate K L H).mp ((dependentTriple_rotate H K L).mp ht)
  have hp : ¬Parallel L H := by
    intro hp
    exact hr.2.2.2.1 (by rw [hp.2]; simp)
  have hx : Finsupp.single H (1 : R) - Finsupp.single K 1 ∈ traceKernel R L := by
    simpa only [Units.val_one, one_smul] using
      (unit_smul_single_sub_mem_traceKernel_iff R L H K hr.1.symm hr.2.1.symm
        hr.2.2.1 hp 1 1).mpr ⟨hr, rfl⟩
  have hy := (g.universalEquiv_mem_traceKernel_iff hS hn L _).mpr hx
  rw [hperm, Equiv.Perm.one_apply, map_sub, g.universalEquiv_single hS hn H,
    g.universalEquiv_single hS hn K, hperm, Equiv.Perm.one_apply,
    Equiv.Perm.one_apply] at hy
  exact ((unit_smul_single_sub_mem_traceKernel_iff R L H K hr.1.symm hr.2.1.symm
    hr.2.2.1 hp _ _).mp hy).2

omit [IsLocalRing R] in
private theorem scalar_unique_of_target (g : DiagramAut R C S) (u v : Rˣ)
    (hu : ∀ x : Fin 2 →₀ R, g.targetEquiv x = (u : R) • x)
    (hv : ∀ x : Fin 2 →₀ R, g.targetEquiv x = (v : R) • x) : v = u := by
  apply Units.ext
  have he := congrArg (fun x : Fin 2 →₀ R ↦ x 0)
    ((hv (Finsupp.single 0 1)).symm.trans (hu (Finsupp.single 0 1)))
  simpa using he

/-- If the recovered label permutation is trivial, one unique primal unit acts on every
universal generator, every finite stage, and the actual common marking target. The same
unit is inverse to every dual inertia unit. Blueprint: S01 (`lem:s01`). -/
theorem scalar_of_hyperplanePerm_eq_one (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (hperm : g.hyperplanePerm hS hn = 1) :
    ∃! u : Rˣ,
      (∀ H : Hyperplane k n, g.universalEquiv (Finsupp.single H 1) =
        (u : R) • Finsupp.single H 1) ∧
      (∀ (A : C.Stage) (x : A.val.val →₀ R), g.stageEquiv A x = (u : R) • x) ∧
      (∀ x : Fin 2 →₀ R, g.targetEquiv x = (u : R) • x) := by
  classical
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let w : Marking S n := Marking.coordinate i ⟨0, hS⟩
  let H₀ := w.fiber (k := k) 0
  let u : Rˣ := (g.hyperplaneUnit hS hn H₀)⁻¹
  have hconst (H K : Hyperplane k n) :
      (g.hyperplaneUnit hS hn H)⁻¹ = (g.hyperplaneUnit hS hn K)⁻¹ :=
    eq_of_eq_on_dependentTriples hn (fun H ↦ (g.hyperplaneUnit hS hn H)⁻¹)
      (g.primalUnit_eq_of_dependentTriple hS hn hperm) H K
  have hM (H : Hyperplane k n) : g.universalEquiv (Finsupp.single H 1) =
      (u : R) • Finsupp.single H 1 := by
    rw [g.universalEquiv_single hS hn, hperm, Equiv.Perm.one_apply, hconst H H₀]
  have hmap : g.universalEquiv.toLinearMap = (u : R) • LinearMap.id := by
    apply Finsupp.lhom_ext
    intro H c
    have hc : Finsupp.single H c = c • Finsupp.single H (1 : R) := by simp
    change g.universalEquiv (Finsupp.single H c) = (u : R) • Finsupp.single H c
    rw [hc, map_smul, hM]
    exact smul_comm c (u : R) _
  have hstage (A : C.Stage) (x : A.val.val →₀ R) :
      g.stageEquiv A x = (u : R) • x := by
    apply finiteStageMap_injective R A.val.val
    rw [← g.universalEquiv_finiteStageMap A x, map_smul]
    exact LinearMap.congr_fun hmap _
  have htarget (x : Fin 2 →₀ R) : g.targetEquiv x = (u : R) • x := by
    obtain ⟨A, hw⟩ := C.exists_stage_marking w
    apply w.basisMap_injective R hw
    have he := LinearMap.congr_fun (g.marking_naturality A w hw) x
    change g.stageEquiv A (w.basisMap R hw x) = w.basisMap R hw (g.targetEquiv x) at he
    rw [hstage] at he
    rw [← he, map_smul]
  exact ⟨u, ⟨hM, hstage, htarget⟩, fun v hv ↦ g.scalar_unique_of_target u v htarget hv.2.2⟩

/-- The kernel of the extracted Galois homomorphism has one unique common primal scalar
on every stage and the common marking target. Blueprint: S01 (`lem:s01`). -/
theorem scalar_of_toGalois_eq_one (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (hg : toGalois R C S hS hgen hn g = 1) :
    ∃! u : Rˣ,
      (∀ (A : C.Stage) (x : A.val.val →₀ R), g.stageEquiv A x = (u : R) • x) ∧
      (∀ x : Fin 2 →₀ R, g.targetEquiv x = (u : R) • x) := by
  obtain ⟨u, hu, -⟩ := g.scalar_of_hyperplanePerm_eq_one hS hn
    ((g.toGalois_eq_one_iff_hyperplanePerm_eq_one hS hgen hn).mp hg)
  exact ⟨u, hu.2, fun v hv ↦ g.scalar_unique_of_target u v hu.2.2 hv.2⟩

/-- A common scalar at the actual stages forces the recovered label permutation to be
trivial; the unit coefficient prevents any change of support. -/
private theorem hyperplanePerm_eq_one_of_scalar (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hn : 2 ≤ n) (u : Rˣ)
    (hu : ∀ (A : C.Stage) (x : A.val.val →₀ R), g.stageEquiv A x = (u : R) • x) :
    g.hyperplanePerm hS hn = 1 := by
  classical
  ext H
  obtain ⟨A, x, hx⟩ := C.exists_stage_vector R (Finsupp.single H 1)
  have he := g.universalEquiv_finiteStageMap A x
  rw [hx, hu, map_smul, hx, g.universalEquiv_single hS hn H] at he
  by_contra hp
  change g.hyperplanePerm hS hn H ≠ H at hp
  have hv := congrArg (fun x : Hyperplane k n →₀ R ↦ x (g.hyperplanePerm hS hn H)) he
  simp [Ne.symm hp] at hv

/-- Exactly the common primal scalars lie in the kernel of Galois extraction. Both stage
and common-target equalities refer to the original diagram components.
Blueprint: S01 (`lem:s01`). -/
theorem toGalois_eq_one_iff_scalar (g : DiagramAut R C S)
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n) :
    toGalois R C S hS hgen hn g = 1 ↔
      ∃ u : Rˣ,
        (∀ (A : C.Stage) (x : A.val.val →₀ R), g.stageEquiv A x = (u : R) • x) ∧
        (∀ x : Fin 2 →₀ R, g.targetEquiv x = (u : R) • x) := by
  constructor
  · intro hg
    obtain ⟨u, hu, -⟩ := g.scalar_of_toGalois_eq_one hS hgen hn hg
    exact ⟨u, hu⟩
  · rintro ⟨u, hu, -⟩
    exact (g.toGalois_eq_one_iff_hyperplanePerm_eq_one hS hgen hn).mpr
      (g.hyperplanePerm_eq_one_of_scalar hS hn u hu)

end OrlikSolomon.HyperplaneGT.DiagramAut
