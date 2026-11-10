/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Diagram.Basic.Restriction
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.Scalar

/-!
# Central scalar actions on the full graded diagram

Unit scaling preserves every defining Orlik–Solomon relation: words scale by their length,
and their signed boundaries scale by one less than their length. It therefore gives an
automorphism of the full algebra, acting by the corresponding power on each ordinary
homogeneous component. The same action at every stage and at the single common target
commutes with the actual inclusion and marking maps.

These scalar families restrict to the existing quadratic scalar families and form an
injective central subgroup over every commutative coefficient ring. No classification,
locality, dimension or nonzero hypothesis is used. Blueprint: the scalar extension in S04
(`thm:s04`). Extending an arbitrary quadratic automorphism requires the later classification.
-/

@[expose] public section

noncomputable section

universe u v w

namespace OrlikSolomon

private theorem word_uniform_smul {R T I : Type*} [CommSemiring R] [Semiring T]
    [Algebra R T] (a : R) (x : I → T) (l : List I) :
    word (fun i ↦ a • x i) l = a ^ l.length • word x l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [word_cons, List.length_cons, ih, smul_mul_assoc, mul_smul_comm,
      smul_smul, pow_succ]

private theorem wordBoundary_uniform_smul {R T I : Type*} [CommRing R] [Ring T]
    [Algebra R T] (a : R) (x : I → T) (l : List I) :
    wordBoundary (fun i ↦ a • x i) l = a ^ (l.length - 1) • wordBoundary x l := by
  rw [wordBoundary_eq_sum, wordBoundary_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [word_uniform_smul, List.length_eraseIdx_of_lt j.isLt]
  exact smul_comm _ _ _

namespace OSAlgebra

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (R : Type w) [CommRing R] (A : Arrangement k V)

/-- Uniform scaling of all canonical generators satisfies both complete OS relator families.
No invertibility or nonzero assumption on the scalar is needed. -/
theorem isFamily_uniform_smul (a : R) :
    IsFamily A (fun H ↦ a • generator R A H) where
  mul_self H := by
    simp only [smul_mul_assoc, mul_smul_comm, generator_mul_self, smul_zero]
  mul_add_mul_swap_of_ne i j hij := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add,
      (isExteriorFamily_generator R A).mul_add_mul_swap_of_ne hij, smul_zero]
  word_eq_zero I _ h := by
    rw [word_uniform_smul, word_eq_zero_of_inter_eq_bot R A h, smul_zero]
  wordBoundary_eq_zero I _ h := by
    rw [wordBoundary_uniform_smul, wordBoundary_eq_zero_of_isDependent R A h, smul_zero]

/-- Uniform coefficient scaling gives an endomorphism of the full OS algebra, because
both families of defining relations are homogeneous. -/
def scalarHom (a : R) : OSAlgebra R A →ₐ[R] OSAlgebra R A := by
  exact lift _ (isFamily_uniform_smul R A a)

/-- The uniform scaling endomorphism has the prescribed action on every generator. -/
@[simp]
theorem scalarHom_generator (a : R) (H : A) :
    scalarHom R A a (generator R A H) = a • generator R A H :=
  lift_generator _ (isFamily_uniform_smul R A a) H

private theorem scalarHom_apply_of_mem_degree (a : R) (q : ℕ)
    (x : OSAlgebra R A) (hx : x ∈ degree R A q) :
    scalarHom R A a x = a ^ q • x := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    rw [OrlikSolomon.map_word]
    simp only [scalarHom_generator, word_uniform_smul, hI]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul r x hx ih => simp only [map_smul, ih, smul_smul, mul_comm]

/-- A coefficient unit scales every generator of the full OS algebra, preserving both
complete relator families. Blueprint: the full scalar lift in S04 (`thm:s04`). -/
def scalarEquiv (a : Rˣ) : OSAlgebra R A ≃ₐ[R] OSAlgebra R A :=
  AlgEquiv.ofAlgHom (scalarHom R A (a : R)) (scalarHom R A (↑a⁻¹ : R))
    (by
      apply algHom_ext
      intro H
      simp only [AlgHom.comp_apply, scalarHom_generator, map_smul, smul_smul,
        AlgHom.id_apply]
      simp)
    (by
      apply algHom_ext
      intro H
      simp only [AlgHom.comp_apply, scalarHom_generator, map_smul, smul_smul,
        AlgHom.id_apply]
      simp)

/-- The full scalar automorphism multiplies each canonical generator by its unit. -/
@[simp]
theorem scalarEquiv_generator (a : Rˣ) (H : A) :
    scalarEquiv R A a (generator R A H) = (a : R) • generator R A H :=
  scalarHom_generator R A (a : R) H

/-- On the entire ordinary degree-q component, unit scaling acts by the q-th power. -/
theorem scalarEquiv_apply_of_mem_degree (a : Rˣ) (q : ℕ)
    (x : OSAlgebra R A) (hx : x ∈ degree R A q) :
    scalarEquiv R A a x = (a : R) ^ q • x :=
  scalarHom_apply_of_mem_degree R A (a : R) q x hx

/-- Every ordinary homogeneous component is preserved by exact image equality. -/
theorem map_degree_scalarEquiv (a : Rˣ) (q : ℕ) :
    (degree R A q).map (scalarEquiv R A a).toLinearMap = degree R A q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change scalarEquiv R A a x ∈ degree R A q
    rw [scalarEquiv_apply_of_mem_degree R A a q x hx]
    exact Submodule.smul_mem _ _ hx
  · intro y hy
    refine ⟨(scalarEquiv R A a).symm y, ?_, (scalarEquiv R A a).apply_symm_apply y⟩
    change scalarHom R A (↑a⁻¹ : R) y ∈ degree R A q
    rw [scalarHom_apply_of_mem_degree R A _ q y hy]
    exact Submodule.smul_mem _ _ hy

/-- Scaling by one is the identity on the full algebra. -/
@[simp]
theorem scalarEquiv_one : scalarEquiv R A 1 = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro H
  simp

/-- Multiplication of units corresponds to composition of full algebra automorphisms. -/
theorem scalarEquiv_mul (a b : Rˣ) :
    scalarEquiv R A (a * b) = scalarEquiv R A a * scalarEquiv R A b := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro H
  simp [smul_smul, mul_comm]

/-- The full scalar action is a homomorphism on coefficient units. -/
def scalarAction : Rˣ →* (OSAlgebra R A ≃ₐ[R] OSAlgebra R A) where
  toFun := scalarEquiv R A
  map_one' := scalarEquiv_one R A
  map_mul' := scalarEquiv_mul R A

/-- Inverting the scalar automorphism inverts its coefficient unit. -/
@[simp]
theorem scalarEquiv_inv (a : Rˣ) :
    scalarEquiv R A a⁻¹ = (scalarEquiv R A a).symm :=
  (scalarAction R A).map_inv a

end OSAlgebra

namespace HyperplaneGT

open OSAlgebra

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k] {n : ℕ}
variable (R : Type w) [CommRing R] (C : CofinalSystem k₀ k n) (S : Set k₀)

/-- Uniform unit scaling on the full stage algebras and the single common target.
Both complete relator families, every degree and all actual arrows are retained.
Blueprint: the full scalar family in S04 (`thm:s04`). -/
def scalarGradedAut (a : Rˣ) : GradedDiagramAut R C S :=
  GradedDiagramAut.ofEquivs (fun A ↦ scalarEquiv R A.val.val a)
    (scalarEquiv R (twoPunctureArrangement k) a)
    (fun A q ↦ map_degree_scalarEquiv R A.val.val a q)
    (fun q ↦ map_degree_scalarEquiv R (twoPunctureArrangement k) a q)
    (by
      intro A B h
      apply algHom_ext
      intro H
      simp)
    (by
      intro A w hw
      apply algHom_ext
      intro H
      obtain ⟨i, rfl⟩ := (twoPunctureLabelEquiv k).surjective H
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Marking.osMap_generator,
        scalarEquiv_generator, map_smul])

/-- Each scalar stage map is the full OS unit-scaling equivalence. -/
@[simp]
theorem scalarGradedAut_stageEquiv (a : Rˣ) (A : C.Stage) :
    (scalarGradedAut R C S a).stageEquiv A = scalarEquiv R A.val.val a := rfl

/-- The one common target carries the same full unit-scaling equivalence. -/
@[simp]
theorem scalarGradedAut_targetEquiv (a : Rˣ) :
    (scalarGradedAut R C S a).targetEquiv =
      scalarEquiv R (twoPunctureArrangement k) a := rfl

/-- Unit scaling acts by the degree power on every stage's entire homogeneous component. -/
theorem scalarGradedAut_stage_apply_of_mem_degree (a : Rˣ) (A : C.Stage) (q : ℕ)
    (x : OSAlgebra R A.val.val) (hx : x ∈ degree R A.val.val q) :
    (scalarGradedAut R C S a).stageEquiv A x = (a : R) ^ q • x :=
  scalarEquiv_apply_of_mem_degree R A.val.val a q x hx

/-- The same degree power acts on the entire corresponding component of the common target.
-/
theorem scalarGradedAut_target_apply_of_mem_degree (a : Rˣ) (q : ℕ)
    (x : OSAlgebra R (twoPunctureArrangement k))
    (hx : x ∈ degree R (twoPunctureArrangement k) q) :
    (scalarGradedAut R C S a).targetEquiv x = (a : R) ^ q • x :=
  scalarEquiv_apply_of_mem_degree R (twoPunctureArrangement k) a q x hx

/-- Restricting the full scalar family gives the existing quadratic scalar family, including
its common-target component. Blueprint: scalar compatibility in S04 (`thm:s04`). -/
@[simp]
theorem toQuadratic_scalarGradedAut (a : Rˣ) :
    GradedDiagramAut.toQuadratic R C S (scalarGradedAut R C S a) =
      scalarQuadraticAut R C S a := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.ext
    intro x
    apply (osDegreeOneEquiv R A.val.val).injective
    apply Subtype.ext
    change (osDegreeOneEquiv R A.val.val
      ((scalarGradedAut R C S a).stageLinearEquiv A x) : OSAlgebra R A.val.val) =
        osDegreeOneEquiv R A.val.val ((scalarQuadraticAut R C S a).stageEquiv A x)
    rw [GradedDiagramAut.stageLinearEquiv_apply, scalarGradedAut_stageEquiv,
      scalarEquiv_apply_of_mem_degree R A.val.val a 1 _ (osDegreeOneEquiv R A.val.val x).property]
    simp
  · apply LinearEquiv.ext
    intro x
    apply (markingTargetDegreeOneEquiv (k := k) R).injective
    apply Subtype.ext
    change (markingTargetDegreeOneEquiv (k := k) R
      ((scalarGradedAut R C S a).targetLinearEquiv x) :
        OSAlgebra R (twoPunctureArrangement k)) =
      markingTargetDegreeOneEquiv (k := k) R ((scalarQuadraticAut R C S a).targetEquiv x)
    rw [GradedDiagramAut.targetLinearEquiv_apply, scalarGradedAut_targetEquiv,
      scalarEquiv_apply_of_mem_degree R (twoPunctureArrangement k) a 1 _
        (markingTargetDegreeOneEquiv (k := k) R x).property]
    simp

/-- The full scalar family of one is the identity on every stage and the common target. -/
@[simp]
theorem scalarGradedAut_one : scalarGradedAut R C S 1 = 1 := by
  apply GradedDiagramAut.toQuadratic_injective
  simp

/-- Full scalar families compose by multiplication of the coefficient units. -/
theorem scalarGradedAut_mul (a b : Rˣ) :
    scalarGradedAut R C S (a * b) = scalarGradedAut R C S a * scalarGradedAut R C S b := by
  apply GradedDiagramAut.toQuadratic_injective
  simp only [toQuadratic_scalarGradedAut, map_mul, scalarQuadraticAut_mul]

/-- Coefficient units act on the full marked graded diagram. -/
def scalarGradedAction : Rˣ →* GradedDiagramAut R C S where
  toFun := scalarGradedAut R C S
  map_one' := scalarGradedAut_one R C S
  map_mul' := scalarGradedAut_mul R C S

/-- The full scalar action evaluates to the named uniform unit-scaling family. -/
@[simp]
theorem scalarGradedAction_apply (a : Rˣ) :
    scalarGradedAction R C S a = scalarGradedAut R C S a := rfl

/-- Inverting a full scalar family inverts its coefficient unit. -/
@[simp]
theorem scalarGradedAut_inv (a : Rˣ) :
    scalarGradedAut R C S a⁻¹ = (scalarGradedAut R C S a)⁻¹ :=
  (scalarGradedAction R C S).map_inv a

/-- The common target detects the scalar unit even over the zero coefficient ring and in
dimension zero, so the full scalar homomorphism is injective without reconstruction. -/
theorem scalarGradedAction_injective : Function.Injective (scalarGradedAction R C S) := by
  intro a b h
  apply scalarQuadraticAction_injective R C S
  simpa only [scalarGradedAction_apply, toQuadratic_scalarGradedAut,
    scalarQuadraticAction_apply] using congrArg (GradedDiagramAut.toQuadratic R C S) h

/-- The full scalar families commute with all graded diagram automorphisms. -/
theorem scalarGradedAut_commute (a : Rˣ) (g : GradedDiagramAut R C S) :
    Commute (scalarGradedAut R C S a) g := by
  apply GradedDiagramAut.toQuadratic_injective
  simpa only [map_mul, toQuadratic_scalarGradedAut] using
    (scalarQuadraticAut_commute R C S a (GradedDiagramAut.toQuadratic R C S g)).eq

namespace GradedDiagramAut

/-- The literal subgroup of full graded scalar families, defined as the scalar action's range.
Blueprint: the full central scalar subgroup in S04 (`thm:s04`). -/
def scalarSubgroup : Subgroup (GradedDiagramAut R C S) := (scalarGradedAction R C S).range

/-- The uniform full scalar subgroup is central over every commutative coefficient ring. -/
theorem scalarSubgroup_le_center :
    scalarSubgroup R C S ≤ Subgroup.center (GradedDiagramAut R C S) := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun g ↦ (scalarGradedAut_commute R C S a g).eq.symm

/-- Restriction carries the literal full scalar range onto the literal quadratic scalar
range, with no classification or nonzero hypothesis. -/
theorem map_scalarSubgroup_toQuadratic :
    (scalarSubgroup R C S).map (toQuadratic R C S) = DiagramAut.scalarSubgroup R C S := by
  ext g
  constructor
  · rintro ⟨h, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (toQuadratic_scalarGradedAut R C S a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨scalarGradedAut R C S a, ⟨a, rfl⟩, toQuadratic_scalarGradedAut R C S a⟩

end GradedDiagramAut

end HyperplaneGT

end OrlikSolomon
