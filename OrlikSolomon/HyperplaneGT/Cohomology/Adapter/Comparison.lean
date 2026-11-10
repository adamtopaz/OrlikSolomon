/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Graded
public import OrlikSolomon.HyperplaneGT.Diagram.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Comparison of the actual cohomology and presentation diagrams

The canonical structure theorem identifies the actual inclusion and tagged marking
pullbacks, the full cup kernels, and every diagonal homogeneous component. Conjugation by
these canonical comparisons gives multiplicative equivalences of the actual automorphism
groups with the presentation diagram groups. Both stage and common-target components are
retained, including in dimension zero.

Blueprint: A04 (`thm:a04`). All statements use a supplied full geometric ordinary theory;
no new nonzero cohomology-theory instance is constructed.
-/

@[expose] public section

noncomputable section

universe u v r b h

open CategoryTheory AlgebraicGeometry Module

namespace OrlikSolomon.HyperplaneGT.Cohomology

open Arrangement OSAlgebra

variable {k₀ : Type v} {k : Type u} [Field k₀] [Field k] [Algebra k₀ k]
  {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : Geometric.SmoothDomain k}
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The existing diagonal structure theorem commutes with actual scheme inclusion pullback.
-/
theorem diagonalEquiv_inclusion {A A' : Arrangement k V} (hA : A ≤ A') :
    (diagonalPull T (D.complementInclusion hA)).comp (T.diagonalEquiv A).toAlgHom =
      (T.diagonalEquiv A').toAlgHom.comp (OSAlgebra.map R hA) := by
  apply AlgHom.ext
  intro x
  apply injective_coeAlgHom_diagonalGrading (T.grading (D.complement A'))
  change DirectSum.coeAlgHom _ (diagonalPull T _ (T.diagonalEquiv A x)) =
    DirectSum.coeAlgHom _ (T.diagonalEquiv A' (OSAlgebra.map R hA x))
  rw [coeAlgHom_diagonalPull, T.coeAlgHom_diagonalEquiv, T.coeAlgHom_diagonalEquiv]
  exact (realizationOverR_map T hA x).symm

/-- The full structure theorem identifies the actual tagged scheme marking pullback with
its OS presentation map. The same target is used for every stage and marking. -/
theorem diagonalEquiv_marking {n : ℕ} {S : Set k₀} (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (diagonalPull T (w.schemeMap D hw)).comp
        (T.diagonalEquiv (twoPunctureArrangement k)).toAlgHom =
      (T.diagonalEquiv A).toAlgHom.comp (w.osMap R hw) := by
  apply OSAlgebra.algHom_ext
  intro H
  obtain ⟨a, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
  apply injective_coeAlgHom_diagonalGrading (T.grading (D.complement A))
  change DirectSum.coeAlgHom _ (diagonalPull T _
      (T.diagonalEquiv _ (generator R _ (twoPunctureLabel k a)))) =
    DirectSum.coeAlgHom _ (T.diagonalEquiv A
      (w.osMap R hw (generator R _ (twoPunctureLabel k a))))
  rw [coeAlgHom_diagonalPull, T.coeAlgHom_diagonalEquiv, T.coeAlgHom_diagonalEquiv,
    w.osMap_generator_label R hw a]
  have ht := coe_targetDegreeOneEquiv_single T a 1
  have hs := degreeOneEquiv_fiberLabel T w hw a 1
  simp only [one_smul] at ht hs
  change T.pull _ (T.realizationOverR _ (generator R _ (twoPunctureLabel k a))) =
    T.realizationOverR A (generator R A (w.fiberLabel hw a))
  change T.realizationOverR (twoPunctureArrangement k)
    (markingTargetDegreeOneEquiv (k := k) R (Finsupp.single a 1) : OSAlgebra R _) = _ at ht
  rw [markingTargetDegreeOneEquiv_single, one_smul] at ht
  change T.realizationOverR A
    (osDegreeOneEquiv R A (Finsupp.single (w.fiberLabel hw a) 1) : OSAlgebra R A) = _ at hs
  rw [osDegreeOneEquiv_single, one_smul] at hs
  have ht' : T.realizationOverR (twoPunctureArrangement k)
      (generator R _ (twoPunctureLabel k a)) =
      T.logClass (schemeMarkingTargetUnit D a) := ht
  have hs' : T.realizationOverR A (generator R A (w.fiberLabel hw a)) =
      T.logClass (Geometric.complementUnit A
        (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
        (hw.covers_fiber a)) := hs
  rw [ht', hs']
  exact w.pull_logClass_targetUnit T hw a

/-! Conjugation transports the entire submodule condition and every specified arrow. -/

section Transport

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

private def exteriorCongr (e : M ≃ₗ[R] N) : (⋀[R]^2 M) ≃ₗ[R] (⋀[R]^2 N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map 2 e.toLinearMap)
    (exteriorPower.map 2 e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id])

private theorem map_conjugate_eq_iff (e : M ≃ₗ[R] N) (P : Submodule R M) (P' : Submodule R N)
    (hP : P.map e.toLinearMap = P') (g : N ≃ₗ[R] N) :
    P.map (e.trans (g.trans e.symm)).toLinearMap = P ↔
      P'.map g.toLinearMap = P' := by
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    Submodule.map_comp, Submodule.map_comp, hP, Submodule.map_symm_eq_iff, hP, eq_comm]

private theorem conjugate_arrow_iff {M M' N N' : Type*} (eM : M ≃ M') (eN : N ≃ N')
    (p : M → N) (p' : M' → N') (hp : ∀ x, p' (eM x) = eN (p x))
    (gM : M' → M') (gN : N' → N') :
    (∀ x, eN.symm (gN (eN (p x))) = p (eM.symm (gM (eM x)))) ↔
      ∀ x, gN (p' x) = p' (gM x) := by
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := eM.surjective x
    have hh := congrArg eN (h x)
    simpa only [eN.apply_symm_apply, ← hp, eM.apply_symm_apply] using hh
  · intro h x
    apply eN.injective
    simpa only [eN.apply_symm_apply, ← hp, eM.apply_symm_apply] using h (eM x)

private theorem linear_conjugate_arrow_iff {M M' N N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (p : M →ₗ[R] N) (p' : M' →ₗ[R] N')
    (hp : p'.comp eM.toLinearMap = eN.toLinearMap.comp p)
    (gM : M' ≃ₗ[R] M') (gN : N' ≃ₗ[R] N') :
    gN.toLinearMap.comp p' = p'.comp gM.toLinearMap ↔
      (eN.trans (gN.trans eN.symm)).toLinearMap.comp p =
        p.comp (eM.trans (gM.trans eM.symm)).toLinearMap := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  exact (conjugate_arrow_iff eM.toEquiv eN.toEquiv p p'
    (fun x ↦ DFunLike.congr_fun hp x) gM gN).symm

private theorem exterior_conjugate_iff (e : M ≃ₗ[R] N)
    (P : Submodule R (⋀[R]^2 M)) (P' : Submodule R (⋀[R]^2 N))
    (hP : P.map (exteriorPower.map 2 e.toLinearMap) = P') (g : N ≃ₗ[R] N) :
    P'.map (exteriorPower.map 2 g.toLinearMap) = P' ↔
      P.map (exteriorPower.map 2 (e.trans (g.trans e.symm)).toLinearMap) = P := by
  have hh := (map_conjugate_eq_iff (exteriorCongr e) P P' hP (exteriorCongr g)).symm
  change P'.map (exteriorPower.map 2 g.toLinearMap) = P' ↔
    P.map ((exteriorPower.map 2 e.symm.toLinearMap).comp
      ((exteriorPower.map 2 g.toLinearMap).comp
        (exteriorPower.map 2 e.toLinearMap))) = P at hh
  simpa only [LinearEquiv.coe_trans, exteriorPower.map_comp, LinearMap.comp_assoc] using hh

end Transport

variable {n : ℕ} (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Conjugation by the canonical actual degree-one coordinates, including the single common
ordered target. This uses Mathlib's general-linear-group conjugation equivalence. -/
def quadraticFamilyEquiv : QuadraticAutFamily T C ≃* HyperplaneGT.QuadraticAutFamily R C :=
  MulEquiv.prodCongr
    (MulEquiv.piCongrRight fun 𝒜 ↦
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv R _).symm.trans
        (LinearMap.GeneralLinearGroup.congrLinearEquiv (degreeOneEquiv T 𝒜.val.val).symm)).trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv R _))
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv R _).symm.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv (targetDegreeOneEquiv T).symm)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv R _))

/-- The complete actual cup-kernel conditions and actual arrow squares are equivalent to
all the presentation quadratic-diagram conditions. -/
theorem quadraticFamilyEquiv_mem_iff (g : QuadraticAutFamily T C) :
    g ∈ quadraticDiagramAutSubgroup T C S ↔
      quadraticFamilyEquiv T C g ∈ HyperplaneGT.quadraticDiagramAutSubgroup R C S := by
  refine and_congr (forall_congr' fun 𝒜 ↦ ?_)
    (and_congr (forall_congr' fun 𝒜 ↦ forall_congr' fun ℬ ↦ forall_congr' fun hi ↦ ?_)
      (forall_congr' fun 𝒜 ↦ forall_congr' fun w ↦ forall_congr' fun hw ↦ ?_))
  · exact exterior_conjugate_iff (degreeOneEquiv T 𝒜.val.val) _ _
      (cupKernel_eq T 𝒜.val.val).symm (g.1 𝒜)
  · exact linear_conjugate_arrow_iff
      (degreeOneEquiv T 𝒜.val.val) (degreeOneEquiv T ℬ.val.val)
      (Finsupp.lmapDomain R R (Arrangement.inclusion hi))
      (componentPull T (D.complementInclusion hi) 1)
      (degreeOneEquiv_inclusion T hi) (g.1 𝒜) (g.1 ℬ)
  · exact linear_conjugate_arrow_iff (targetDegreeOneEquiv T)
      (degreeOneEquiv T 𝒜.val.val) (w.basisMap R hw)
      (componentPull T (w.schemeMap D hw) 1)
      (degreeOneEquiv_marking T w hw) g.2 (g.1 𝒜)

/-- **The quadratic diagram comparison.** The actual degree-one/cup-kernel automorphism
group is multiplicatively equivalent to the A03 presentation diagram group, in both
directions and with its common target retained. Blueprint: A04 (`thm:a04`). -/
def degreeOneDiagramEquiv : DiagramAut T C S ≃* HyperplaneGT.DiagramAut R C S where
  __ := (quadraticFamilyEquiv T C).toEquiv.subtypeEquiv
    (quadraticFamilyEquiv_mem_iff T C S)
  map_mul' g h := Subtype.ext ((quadraticFamilyEquiv T C).map_mul g.val h.val)

/-- The forward comparison intertwines each actual stage equivalence with its coordinates.
-/
theorem degreeOneDiagramEquiv_stage (g : DiagramAut T C S) (𝒜 : C.Stage)
    (x : 𝒜.val.val →₀ R) :
    degreeOneEquiv T 𝒜.val.val ((degreeOneDiagramEquiv T C S g).stageEquiv 𝒜 x) =
      g.stageEquiv 𝒜 (degreeOneEquiv T 𝒜.val.val x) := by
  change degreeOneEquiv T 𝒜.val.val ((degreeOneEquiv T 𝒜.val.val).symm
    (g.stageEquiv 𝒜 (degreeOneEquiv T 𝒜.val.val x))) = _
  exact (degreeOneEquiv T 𝒜.val.val).apply_symm_apply _

/-- The forward comparison intertwines the one actual target equivalence with ordered
coordinates. -/
theorem degreeOneDiagramEquiv_target (g : DiagramAut T C S) (x : Fin 2 →₀ R) :
    targetDegreeOneEquiv T ((degreeOneDiagramEquiv T C S g).targetEquiv x) =
      g.targetEquiv (targetDegreeOneEquiv T x) := by
  change targetDegreeOneEquiv T ((targetDegreeOneEquiv T).symm
    (g.targetEquiv (targetDegreeOneEquiv T x))) = _
  exact (targetDegreeOneEquiv T).apply_symm_apply _

/-- The structure theorem sends the entire ordinary degree component onto the corresponding
actual diagonal summand. -/
theorem map_diagonalEquiv_degree (A : Arrangement k V) (q : ℕ) :
    (degree R A q).map (T.diagonalEquiv A).toLinearMap =
      diagonalDegree T (D.complement A) q := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change T.diagonalEquiv A y ∈ diagonalDegree T (D.complement A) q
    rw [T.diagonalEquiv_of_mem_degree hy]
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (T.degreeEquiv A q).surjective x
    refine ⟨y.val, y.property, ?_⟩
    change T.diagonalEquiv A y.val = DirectSum.of _ q x
    rw [T.diagonalEquiv_of_mem_degree y.property]
    exact congrArg (DirectSum.of _ q) hy

private theorem algebra_conjugate_arrow_iff {M M' N N' : Type*}
    [Ring M] [Algebra R M] [Ring M'] [Algebra R M']
    [Ring N] [Algebra R N] [Ring N'] [Algebra R N']
    (eM : M ≃ₐ[R] M') (eN : N ≃ₐ[R] N') (p : M →ₐ[R] N) (p' : M' →ₐ[R] N')
    (hp : p'.comp eM.toAlgHom = eN.toAlgHom.comp p)
    (gM : M' ≃ₐ[R] M') (gN : N' ≃ₐ[R] N') :
    gN.toAlgHom.comp p' = p'.comp gM.toAlgHom ↔
      (eN.trans (gN.trans eN.symm)).toAlgHom.comp p =
        p.comp (eM.trans (gM.trans eM.symm)).toAlgHom := by
  simp only [AlgHom.ext_iff, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.trans_apply]
  exact (conjugate_arrow_iff eM.toEquiv eN.toEquiv p p'
    (fun x ↦ DFunLike.congr_fun hp x) gM gN).symm

/-- Conjugation by the existing full diagonal structure theorem, including its actual
common target, using Mathlib's algebra-automorphism congruence. -/
def gradedFamilyEquiv : GradedAutFamily T C ≃* HyperplaneGT.GradedAutFamily R C :=
  MulEquiv.prodCongr
    (MulEquiv.piCongrRight fun 𝒜 ↦ AlgEquiv.autCongr (T.diagonalEquiv 𝒜.val.val).symm)
    (AlgEquiv.autCongr (T.diagonalEquiv (twoPunctureArrangement k)).symm)

/-- Full preservation of every actual diagonal summand and all actual arrow squares is
equivalent to the full marked graded presentation-diagram conditions. -/
theorem gradedFamilyEquiv_mem_iff (g : GradedAutFamily T C) :
    g ∈ gradedDiagramAutSubgroup T C S ↔
      gradedFamilyEquiv T C g ∈ HyperplaneGT.gradedDiagramAutSubgroup R C S := by
  refine and_congr (forall_congr' fun 𝒜 ↦ forall_congr' fun q ↦ ?_)
    (and_congr (forall_congr' fun q ↦ ?_)
      (and_congr
        (forall_congr' fun 𝒜 ↦ forall_congr' fun ℬ ↦ forall_congr' fun hi ↦ ?_)
        (forall_congr' fun 𝒜 ↦ forall_congr' fun w ↦ forall_congr' fun hw ↦ ?_)))
  · exact (map_conjugate_eq_iff (T.diagonalEquiv 𝒜.val.val).toLinearEquiv _ _
      (map_diagonalEquiv_degree T 𝒜.val.val q) (g.1 𝒜).toLinearEquiv).symm
  · exact (map_conjugate_eq_iff (T.diagonalEquiv (twoPunctureArrangement k)).toLinearEquiv
      _ _ (map_diagonalEquiv_degree T (twoPunctureArrangement k) q)
      g.2.toLinearEquiv).symm
  · exact algebra_conjugate_arrow_iff
      (T.diagonalEquiv 𝒜.val.val) (T.diagonalEquiv ℬ.val.val)
      (OSAlgebra.map R hi) (diagonalPull T (D.complementInclusion hi))
      (diagonalEquiv_inclusion T hi) (g.1 𝒜) (g.1 ℬ)
  · exact algebra_conjugate_arrow_iff (T.diagonalEquiv (twoPunctureArrangement k))
      (T.diagonalEquiv 𝒜.val.val) (w.osMap R hw) (diagonalPull T (w.schemeMap D hw))
      (diagonalEquiv_marking T w hw) g.2 (g.1 𝒜)

/-- **The full graded diagram comparison.** Actual diagonal-cohomology diagram
automorphisms and full marked graded OS-diagram automorphisms are multiplicatively
equivalent in both directions. Blueprint: A04 (`thm:a04`). -/
def gradedDiagramEquiv : GradedDiagramAut T C S ≃* HyperplaneGT.GradedDiagramAut R C S where
  __ := (gradedFamilyEquiv T C).toEquiv.subtypeEquiv (gradedFamilyEquiv_mem_iff T C S)
  map_mul' g h := Subtype.ext ((gradedFamilyEquiv T C).map_mul g.val h.val)

/-- The full forward comparison intertwines the actual algebra automorphism at a stage. -/
theorem gradedDiagramEquiv_stage (g : GradedDiagramAut T C S) (𝒜 : C.Stage)
    (x : OSAlgebra R 𝒜.val.val) :
    T.diagonalEquiv 𝒜.val.val ((gradedDiagramEquiv T C S g).stageEquiv 𝒜 x) =
      g.stageEquiv 𝒜 (T.diagonalEquiv 𝒜.val.val x) := by
  change T.diagonalEquiv 𝒜.val.val ((T.diagonalEquiv 𝒜.val.val).symm
    (g.stageEquiv 𝒜 (T.diagonalEquiv 𝒜.val.val x))) = _
  exact (T.diagonalEquiv 𝒜.val.val).apply_symm_apply _

/-- The full forward comparison intertwines the single actual common-target automorphism.
-/
theorem gradedDiagramEquiv_target (g : GradedDiagramAut T C S)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    T.diagonalEquiv (twoPunctureArrangement k)
        ((gradedDiagramEquiv T C S g).targetEquiv x) =
      g.targetEquiv (T.diagonalEquiv (twoPunctureArrangement k) x) := by
  change T.diagonalEquiv (twoPunctureArrangement k)
    ((T.diagonalEquiv (twoPunctureArrangement k)).symm
      (g.targetEquiv (T.diagonalEquiv (twoPunctureArrangement k) x))) = _
  exact (T.diagonalEquiv (twoPunctureArrangement k)).apply_symm_apply _

/-- The inverse comparison recovers the actual stage action from canonical coordinates. -/
theorem degreeOneDiagramEquiv_symm_stage (g : HyperplaneGT.DiagramAut R C S)
    (𝒜 : C.Stage) (x : 𝒜.val.val →₀ R) :
    ((degreeOneDiagramEquiv T C S).symm g).stageEquiv 𝒜
        (degreeOneEquiv T 𝒜.val.val x) =
      degreeOneEquiv T 𝒜.val.val (g.stageEquiv 𝒜 x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (degreeOneDiagramEquiv_stage T C S ((degreeOneDiagramEquiv T C S).symm g) 𝒜 x).symm

/-- The inverse comparison recovers the actual common-target action from ordered coordinates.
-/
theorem degreeOneDiagramEquiv_symm_target (g : HyperplaneGT.DiagramAut R C S)
    (x : Fin 2 →₀ R) :
    ((degreeOneDiagramEquiv T C S).symm g).targetEquiv (targetDegreeOneEquiv T x) =
      targetDegreeOneEquiv T (g.targetEquiv x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (degreeOneDiagramEquiv_target T C S ((degreeOneDiagramEquiv T C S).symm g) x).symm

/-- The inverse full comparison recovers the actual stage algebra action. -/
theorem gradedDiagramEquiv_symm_stage (g : HyperplaneGT.GradedDiagramAut R C S)
    (𝒜 : C.Stage) (x : OSAlgebra R 𝒜.val.val) :
    ((gradedDiagramEquiv T C S).symm g).stageEquiv 𝒜 (T.diagonalEquiv 𝒜.val.val x) =
      T.diagonalEquiv 𝒜.val.val (g.stageEquiv 𝒜 x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (gradedDiagramEquiv_stage T C S ((gradedDiagramEquiv T C S).symm g) 𝒜 x).symm

/-- The inverse full comparison recovers the actual common-target algebra action. -/
theorem gradedDiagramEquiv_symm_target (g : HyperplaneGT.GradedDiagramAut R C S)
    (x : OSAlgebra R (twoPunctureArrangement k)) :
    ((gradedDiagramEquiv T C S).symm g).targetEquiv
        (T.diagonalEquiv (twoPunctureArrangement k) x) =
      T.diagonalEquiv (twoPunctureArrangement k) (g.targetEquiv x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    (gradedDiagramEquiv_target T C S ((gradedDiagramEquiv T C S).symm g) x).symm

/-- The actual inclusion of degree-one cohomology in its diagonal direct sum. -/
def degreeOneι (A : Arrangement k V) : degreeOne T A →ₗ[R] diagonal T (D.complement A) :=
  DirectSum.lof R ℕ (fun q ↦ ↥(diagonalGrading (T.grading (D.complement A)) q)) 1

/-- The degree-one summand inclusion is injective. -/
theorem degreeOneι_injective (A : Arrangement k V) : Function.Injective (degreeOneι T A) :=
  DirectSum.of_injective (β := fun q ↦ ↥(diagonalGrading (T.grading (D.complement A)) q)) 1

/-- Canonical stage degree-one coordinates agree with the full diagonal structure theorem.
-/
theorem degreeOneι_degreeOneEquiv (A : Arrangement k V) (x : A →₀ R) :
    degreeOneι T A (degreeOneEquiv T A x) =
      T.diagonalEquiv A (osDegreeOneEquiv R A x) :=
  (T.diagonalEquiv_of_mem_degree (osDegreeOneEquiv R A x).property).symm

/-- Ordered common-target degree-one coordinates agree with its full structure theorem. -/
theorem degreeOneι_targetDegreeOneEquiv (x : Fin 2 →₀ R) :
    degreeOneι T (twoPunctureArrangement k) (targetDegreeOneEquiv T x) =
      T.diagonalEquiv (twoPunctureArrangement k) (markingTargetDegreeOneEquiv (k := k) R x) :=
  (T.diagonalEquiv_of_mem_degree (markingTargetDegreeOneEquiv (k := k) R x).property).symm

namespace GradedDiagramAut

/-- Restriction to actual degree-one cohomology. The following summand equations identify
this map with literal restriction of the actual diagonal algebra actions; the two diagram
comparisons provide the whole-kernel and arrow conditions. -/
def toQuadratic : GradedDiagramAut T C S →* DiagramAut T C S :=
  (degreeOneDiagramEquiv T C S).symm.toMonoidHom.comp
    ((HyperplaneGT.GradedDiagramAut.toQuadratic R C S).comp
      (gradedDiagramEquiv T C S).toMonoidHom)

/-- Actual restriction commutes with both canonical diagram comparisons. -/
theorem toQuadratic_comparison (g : GradedDiagramAut T C S) :
    degreeOneDiagramEquiv T C S (toQuadratic T C S g) =
      HyperplaneGT.GradedDiagramAut.toQuadratic R C S (gradedDiagramEquiv T C S g) :=
  (degreeOneDiagramEquiv T C S).apply_symm_apply _

/-- The stage component of restriction is exactly the action on the actual degree-one
summand of diagonal cohomology. -/
theorem toQuadratic_stage (g : GradedDiagramAut T C S) (𝒜 : C.Stage) :
    (g.stageEquiv 𝒜).toLinearMap.comp (degreeOneι T 𝒜.val.val) =
      (degreeOneι T 𝒜.val.val).comp ((toQuadratic T C S g).stageEquiv 𝒜).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (degreeOneEquiv T 𝒜.val.val).surjective x
  change g.stageEquiv 𝒜 (degreeOneι T 𝒜.val.val (degreeOneEquiv T 𝒜.val.val c)) =
    degreeOneι T 𝒜.val.val ((toQuadratic T C S g).stageEquiv 𝒜
      (degreeOneEquiv T 𝒜.val.val c))
  calc
    _ = g.stageEquiv 𝒜 (T.diagonalEquiv 𝒜.val.val (osDegreeOneEquiv R 𝒜.val.val c)) :=
      congrArg (g.stageEquiv 𝒜) (degreeOneι_degreeOneEquiv T 𝒜.val.val c)
    _ = T.diagonalEquiv 𝒜.val.val
        ((gradedDiagramEquiv T C S g).stageEquiv 𝒜 (osDegreeOneEquiv R 𝒜.val.val c)) :=
      (gradedDiagramEquiv_stage T C S g 𝒜 _).symm
    _ = T.diagonalEquiv 𝒜.val.val (osDegreeOneEquiv R 𝒜.val.val
        ((HyperplaneGT.GradedDiagramAut.toQuadratic R C S
          (gradedDiagramEquiv T C S g)).stageEquiv 𝒜 c)) :=
      congrArg (T.diagonalEquiv 𝒜.val.val)
        ((gradedDiagramEquiv T C S g).stageLinearEquiv_apply 𝒜 c).symm
    _ = _ := (degreeOneι_degreeOneEquiv T 𝒜.val.val _).symm
    _ = _ := congrArg (degreeOneι T 𝒜.val.val)
      (degreeOneDiagramEquiv_symm_stage T C S _ 𝒜 c).symm

-- Elaborating the common target traverses its actual scheme carrier and the two nested
-- diagram subgroup comparisons; the default recursion bound is too small for this term.
set_option maxRecDepth 2000 in
/-- The common-target component of restriction is its actual degree-one summand action. -/
theorem toQuadratic_target (g : GradedDiagramAut T C S) :
    g.targetEquiv.toLinearMap.comp (degreeOneι T (twoPunctureArrangement k)) =
      (degreeOneι T (twoPunctureArrangement k)).comp
        (toQuadratic T C S g).targetEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (targetDegreeOneEquiv T).surjective x
  calc
    _ = g.targetEquiv (T.diagonalEquiv (twoPunctureArrangement k)
        (markingTargetDegreeOneEquiv (k := k) R c)) :=
      congrArg g.targetEquiv (degreeOneι_targetDegreeOneEquiv T c)
    _ = T.diagonalEquiv (twoPunctureArrangement k) ((gradedDiagramEquiv T C S g).targetEquiv
        (markingTargetDegreeOneEquiv (k := k) R c)) :=
      (gradedDiagramEquiv_target T C S g _).symm
    _ = T.diagonalEquiv (twoPunctureArrangement k) (markingTargetDegreeOneEquiv (k := k) R
        ((HyperplaneGT.GradedDiagramAut.toQuadratic R C S
          (gradedDiagramEquiv T C S g)).targetEquiv c)) :=
      congrArg (T.diagonalEquiv (twoPunctureArrangement k))
        ((gradedDiagramEquiv T C S g).targetLinearEquiv_apply c).symm
    _ = _ := (degreeOneι_targetDegreeOneEquiv T _).symm
    _ = _ := congrArg (degreeOneι T (twoPunctureArrangement k))
      (degreeOneDiagramEquiv_symm_target T C S _ c).symm

/-- Degree-one restriction is faithful on the full actual marked diagonal diagram. -/
theorem toQuadratic_injective : Function.Injective (toQuadratic T C S) :=
  (degreeOneDiagramEquiv T C S).symm.injective.comp
    ((HyperplaneGT.GradedDiagramAut.toQuadratic_injective (R := R) (C := C) (S := S)).comp
      (gradedDiagramEquiv T C S).injective)

end GradedDiagramAut

private theorem conjugate_scalar_iff {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (g : N ≃ₗ[R] N) (a : R) :
    (∀ y, g y = a • y) ↔ ∀ x, (e.trans (g.trans e.symm)) x = a • x := by
  constructor
  · intro h x
    change e.symm (g (e x)) = _
    rw [h, map_smul, e.symm_apply_apply]
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hh := congrArg e (h x)
    change e (e.symm (g (e x))) = e (a • x) at hh
    simpa only [e.apply_symm_apply, map_smul] using hh

private theorem conjugate_scalar_submodule_iff {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) (P' : Submodule R N)
    (hP : P.map e.toLinearMap = P') (g : N ≃ₗ[R] N) (a : R) :
    (∀ y : P', g (y : N) = a • (y : N)) ↔
      ∀ x : P, (e.trans (g.trans e.symm)) (x : M) = a • (x : M) := by
  constructor
  · intro h x
    have hx : e (x : M) ∈ P' := by
      rw [← hP]
      exact ⟨x, x.property, rfl⟩
    apply e.injective
    change e (e.symm (g (e (x : M)))) = e (a • (x : M))
    rw [e.apply_symm_apply, map_smul]
    exact h ⟨e (x : M), hx⟩
  · intro h y
    have hy : (y : N) ∈ P.map e.toLinearMap := hP.symm ▸ y.property
    obtain ⟨x, hx, hxy⟩ := hy
    have hh := congrArg e (h ⟨x, hx⟩)
    change e (e.symm (g (e x))) = e (a • x) at hh
    rw [e.apply_symm_apply, map_smul] at hh
    exact hxy ▸ hh

/-- The quadratic comparison carries the scalar family of a fixed unit to the same scalar
family, including the common target. This is a characterization, independent of any scalar
classification theorem. Blueprint: A04 (`thm:a04`). -/
theorem degreeOneDiagramEquiv_scalar_iff (g : DiagramAut T C S) (a : Rˣ) :
    ((∀ (𝒜 : C.Stage) (x : degreeOne T 𝒜.val.val), g.stageEquiv 𝒜 x = (a : R) • x) ∧
      ∀ x : degreeOne T (twoPunctureArrangement k), g.targetEquiv x = (a : R) • x) ↔
    ((∀ (𝒜 : C.Stage) (x : 𝒜.val.val →₀ R),
        (degreeOneDiagramEquiv T C S g).stageEquiv 𝒜 x = (a : R) • x) ∧
      ∀ x : Fin 2 →₀ R, (degreeOneDiagramEquiv T C S g).targetEquiv x = (a : R) • x) := by
  refine and_congr (forall_congr' fun 𝒜 ↦ ?_) ?_
  · exact conjugate_scalar_iff (degreeOneEquiv T 𝒜.val.val) (g.stageEquiv 𝒜) a
  · exact conjugate_scalar_iff (targetDegreeOneEquiv T) g.targetEquiv a

/-- The full graded comparison carries multiplication by `a^q` on every degree to precisely
the same scalar family at all stages and the single common target. No scalar-classification
hypothesis is used. Blueprint: A04 (`thm:a04`). -/
theorem gradedDiagramEquiv_scalar_iff (g : GradedDiagramAut T C S) (a : Rˣ) :
    ((∀ (𝒜 : C.Stage) (q : ℕ) (x : diagonalDegree T (D.complement 𝒜.val.val) q),
        g.stageEquiv 𝒜 (x : diagonal T _) = (a : R)^q • (x : diagonal T _)) ∧
      ∀ (q : ℕ) (x : diagonalDegree T (schemeMarkingTarget D) q),
        g.targetEquiv (x : diagonal T _) = (a : R)^q • (x : diagonal T _)) ↔
    ((∀ (𝒜 : C.Stage) (q : ℕ) (x : degree R 𝒜.val.val q),
        (gradedDiagramEquiv T C S g).stageEquiv 𝒜 (x : OSAlgebra R _) =
          (a : R)^q • (x : OSAlgebra R _)) ∧
      ∀ (q : ℕ) (x : degree R (twoPunctureArrangement k) q),
        (gradedDiagramEquiv T C S g).targetEquiv (x : OSAlgebra R _) =
          (a : R)^q • (x : OSAlgebra R _)) := by
  refine and_congr (forall_congr' fun 𝒜 ↦ forall_congr' fun q ↦ ?_)
    (forall_congr' fun q ↦ ?_)
  · exact conjugate_scalar_submodule_iff (T.diagonalEquiv 𝒜.val.val).toLinearEquiv
      _ _ (map_diagonalEquiv_degree T 𝒜.val.val q) (g.stageEquiv 𝒜).toLinearEquiv _
  · exact conjugate_scalar_submodule_iff
      (T.diagonalEquiv (twoPunctureArrangement k)).toLinearEquiv _ _
      (map_diagonalEquiv_degree T (twoPunctureArrangement k) q) g.targetEquiv.toLinearEquiv _

end OrlikSolomon.HyperplaneGT.Cohomology
