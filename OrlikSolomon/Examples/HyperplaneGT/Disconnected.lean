/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.HyperplaneGT.Reconstruction.Domain.Descent
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.Orbits
public import OrlikSolomon.HyperplaneGT.Reconstruction.LocalRing.GradedScalar
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The disconnected-coefficient obstruction

Complementary coefficient idempotents combine two existing full Galois actions into an
actual graded diagram over a product ring, retaining the same identity common target.
For distinct Galois factors this family cannot be one scalar times one Galois action.
Thus the classification fails over disconnected coefficients `F × F`: the local-ring
or integral-domain hypotheses cannot be dropped.

All construction helpers are private to this regression. No product comparison or
relation-preservation conclusion is assumed; the construction uses the already proved
full OS algebra equivalences, including every defining relation.

Blueprint: the disconnected-coefficient regression following S03–S05.
-/

@[expose] public section

noncomputable section

namespace OrlikSolomon.HyperplaneGT.DisconnectedExamples

universe u v r a

section Mix

variable {F : Type r} [CommRing F] {A : Type a} [Ring A] [Algebra (F × F) A]

private theorem prod_zero_smul (x : A) : ((0, 0) : F × F) • x = 0 :=
  zero_smul (F × F) x

private theorem prod_split_smul (x : A) :
    ((1, 0) : F × F) • x + ((0, 1) : F × F) • x = x := by
  have hs : ((1, 0) : F × F) + (0, 1) = 1 := by ext <;> simp
  rw [← add_smul, hs, one_smul]

private def mixHom (f g : A →ₐ[F × F] A) : A →ₐ[F × F] A where
  toFun x := ((1, 0) : F × F) • f x + ((0, 1) : F × F) • g x
  map_zero' := by simp
  map_add' x y := by simp [map_add, smul_add, add_assoc, add_comm, add_left_comm]
  map_one' := by
    simp only [map_one]
    exact prod_split_smul _
  map_mul' x y := by
    simp [map_mul, add_mul, mul_add, smul_smul, prod_zero_smul]
  commutes' c := by
    simp only [AlgHom.commutes]
    exact prod_split_smul _

private def mixEquiv (f g : A ≃ₐ[F × F] A) : A ≃ₐ[F × F] A :=
  AlgEquiv.ofAlgHom (mixHom f.toAlgHom g.toAlgHom)
    (mixHom f.symm.toAlgHom g.symm.toAlgHom)
    (by
      ext x
      simp [mixHom, map_add, map_smul, smul_add, smul_smul, prod_zero_smul, prod_split_smul])
    (by
      ext x
      simp [mixHom, map_add, map_smul, smul_add, smul_smul, prod_zero_smul, prod_split_smul])

private theorem mixEquiv_apply (f g : A ≃ₐ[F × F] A) (x : A) :
    mixEquiv f g x = ((1, 0) : F × F) • f x + ((0, 1) : F × F) • g x := rfl

private theorem mixEquiv_map_submodule (f g : A ≃ₐ[F × F] A) (P : Submodule (F × F) A)
    (hf : P.map f.toLinearMap = P) (hg : P.map g.toLinearMap = P) :
    P.map (mixEquiv f g).toLinearMap = P := by
  have hle (f g : A ≃ₐ[F × F] A) (hf : P.map f.toLinearMap = P)
      (hg : P.map g.toLinearMap = P) : P.map (mixEquiv f g).toLinearMap ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact P.add_mem (P.smul_mem _ (hf.le ⟨x, hx, rfl⟩))
      (P.smul_mem _ (hg.le ⟨x, hx, rfl⟩))
  apply le_antisymm (hle f g hf hg)
  intro y hy
  refine ⟨(mixEquiv f g).symm y, ?_, (mixEquiv f g).apply_symm_apply y⟩
  exact hle f.symm g.symm ((Submodule.map_symm_eq_iff f.toLinearEquiv).mpr hf)
    ((Submodule.map_symm_eq_iff g.toLinearEquiv).mpr hg) ⟨y, hy, rfl⟩

private theorem mixEquiv_naturality {B : Type*} [Ring B] [Algebra (F × F) B]
    (f g : A ≃ₐ[F × F] A) (f' g' : B ≃ₐ[F × F] B) (l : A →ₐ[F × F] B)
    (hf : f'.toAlgHom.comp l = l.comp f.toAlgHom)
    (hg : g'.toAlgHom.comp l = l.comp g.toAlgHom) :
    (mixEquiv f' g').toAlgHom.comp l = l.comp (mixEquiv f g).toAlgHom := by
  ext x
  change ((1, 0) : F × F) • f' (l x) + ((0, 1) : F × F) • g' (l x) =
    l (((1, 0) : F × F) • f x + ((0, 1) : F × F) • g x)
  rw [map_add, map_smul, map_smul]
  exact congrArg₂ (fun x y : B ↦ ((1, 0) : F × F) • x + ((0, 1) : F × F) • y)
    (DFunLike.congr_fun hf x) (DFunLike.congr_fun hg x)

end Mix

variable {k : Type u} {k₀ : Type v} [Field k] [Field k₀] [Algebra k₀ k]
  {n : ℕ} (F : Type r) [CommRing F] (C : CofinalSystem k₀ k n) (S : Set k₀)

private def mixDiagrams (f g : GradedDiagramAut (F × F) C S) :
    GradedDiagramAut (F × F) C S :=
  GradedDiagramAut.ofEquivs (fun A ↦ mixEquiv (f.stageEquiv A) (g.stageEquiv A))
    (mixEquiv f.targetEquiv g.targetEquiv)
    (fun A q ↦ mixEquiv_map_submodule _ _ _ (f.map_degree A q) (g.map_degree A q))
    (fun q ↦ mixEquiv_map_submodule _ _ _ (f.map_target_degree q) (g.map_target_degree q))
    (fun _ _ h ↦ mixEquiv_naturality _ _ _ _ _
      (f.inclusion_naturality h) (g.inclusion_naturality h))
    (fun A w hw ↦ mixEquiv_naturality _ _ _ _ _
      (f.marking_naturality A w hw) (g.marking_naturality A w hw))

/-- Complementary coefficient idempotents select two full Galois factors independently.
This is an actual graded diagram, preserving every OS relation and every ordinary degree,
with the original inclusion and tagged marking maps and one shared identity target.
The implementation stays opaque so its generic idempotent helpers remain example-private;
the generator and target equations give the public interface. -/
@[no_expose]
def mixedGaloisAut (σ τ : k ≃ₐ[k₀] k) : GradedDiagramAut (F × F) C S :=
  mixDiagrams F C S (galoisGradedAut (F × F) C S σ) (galoisGradedAut (F × F) C S τ)

/-- The finite-stage action chooses the two Galois labels by complementary coefficients. -/
theorem mixedGaloisAut_generator (σ τ : k ≃ₐ[k₀] k) (A : C.Stage) (H : A.val.val) :
    (mixedGaloisAut F C S σ τ).stageEquiv A (OSAlgebra.generator (F × F) A.val.val H) =
      ((1, 0) : F × F) • OSAlgebra.generator (F × F) A.val.val (galoisLabelEquiv A.val σ H) +
      ((0, 1) : F × F) • OSAlgebra.generator (F × F) A.val.val (galoisLabelEquiv A.val τ H) := by
  change ((1, 0) : F × F) •
      (galoisGradedAut (F × F) C S σ).stageEquiv A (OSAlgebra.generator (F × F) A.val.val H) +
    ((0, 1) : F × F) •
      (galoisGradedAut (F × F) C S τ).stageEquiv A (OSAlgebra.generator (F × F) A.val.val H) = _
  rw [galoisGradedAut_generator, galoisGradedAut_generator]

/-- Every marking still uses the same identity common target. -/
@[simp]
theorem mixedGaloisAut_target (σ τ : k ≃ₐ[k₀] k) :
    (mixedGaloisAut F C S σ τ).targetEquiv = AlgEquiv.refl := by
  ext x
  change ((1, 0) : F × F) • x + ((0, 1) : F × F) • x = x
  exact prod_split_smul x

/-- Degree-one restriction retains the two genuinely independent Galois labels. -/
theorem mixedGaloisAut_toQuadratic_single (σ τ : k ≃ₐ[k₀] k)
    (A : C.Stage) (H : A.val.val) :
    (GradedDiagramAut.toQuadratic (F × F) C S (mixedGaloisAut F C S σ τ)).stageEquiv A
      (Finsupp.single H 1) =
    ((1, 0) : F × F) • Finsupp.single (galoisLabelEquiv A.val σ H) 1 +
      ((0, 1) : F × F) • Finsupp.single (galoisLabelEquiv A.val τ H) 1 := by
  apply (osDegreeOneEquiv (F × F) A.val.val).injective
  apply Subtype.val_injective
  rw [GradedDiagramAut.stageEquiv_toQuadratic,
    GradedDiagramAut.stageLinearEquiv_apply]
  simp only [osDegreeOneEquiv_single, one_smul, map_add, map_smul,
    Submodule.coe_add, Submodule.coe_smul]
  exact mixedGaloisAut_generator F C S σ τ A H

/-- The quadratic common target also remains identically fixed. -/
theorem mixedGaloisAut_toQuadratic_target (σ τ : k ≃ₐ[k₀] k) :
    (GradedDiagramAut.toQuadratic (F × F) C S (mixedGaloisAut F C S σ τ)).targetEquiv =
      LinearEquiv.refl (F × F) _ := by
  apply LinearEquiv.ext
  intro x
  apply (markingTargetDegreeOneEquiv (k := k) (F × F)).injective
  apply Subtype.val_injective
  rw [GradedDiagramAut.targetEquiv_toQuadratic,
    GradedDiagramAut.targetLinearEquiv_apply, mixedGaloisAut_target]
  rfl

private theorem project_mixed [Algebra (F × F) F] (σ τ ρ : k ≃ₐ[k₀] k)
    (hproj : ∀ (A : C.Stage) (H : A.val.val),
      algebraMap (F × F) F (1, 0) • Finsupp.single (galoisLabelEquiv A.val σ H) (1 : F) +
        algebraMap (F × F) F (0, 1) • Finsupp.single (galoisLabelEquiv A.val τ H) (1 : F) =
          Finsupp.single (galoisLabelEquiv A.val ρ H) (1 : F)) :
    DiagramAut.coefficientExtend (F × F) C S F
      (GradedDiagramAut.toQuadratic (F × F) C S (mixedGaloisAut F C S σ τ)) =
    galoisQuadraticAut F C S ρ := by
  apply DiagramAut.ext
  · intro A
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro H a
    change (DiagramAut.coefficientExtend (F × F) C S F
      (GradedDiagramAut.toQuadratic (F × F) C S (mixedGaloisAut F C S σ τ))).stageEquiv A
        (Finsupp.single H a) = (galoisQuadraticAut F C S ρ).stageEquiv A (Finsupp.single H a)
    rw [show Finsupp.single H a = a • Finsupp.single H (1 : F) by simp,
      map_smul, map_smul, DiagramAut.coefficientExtend_stage_single,
      mixedGaloisAut_toQuadratic_single, galoisQuadraticAut_stageEquiv_single]
    congr 1
    rw [map_add]
    convert hproj A H using 1; simp [Algebra.smul_def]
  · rw [DiagramAut.coefficientExtend_targetEquiv, mixedGaloisAut_toQuadratic_target,
      galoisQuadraticAut_targetEquiv]
    exact coefficientExtendLinearEquiv_refl (F × F) F

variable (F : Type r) [Field F]

/-- Distinct Galois choices on the two components cannot be one scalar times one Galois
family. This is a counterexample to extending S03–S05 to disconnected coefficients. -/
theorem mixedGaloisAut_not_scalar_mul_galois
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ τ : k ≃ₐ[k₀] k) (hστ : σ ≠ τ) :
    ¬ ∃ (a : (F × F)ˣ) (ρ : k ≃ₐ[k₀] k),
      GradedDiagramAut.toQuadratic (F × F) C S (mixedGaloisAut F C S σ τ) =
        scalarQuadraticAut (F × F) C S a * galoisQuadraticAut (F × F) C S ρ := by
  rintro ⟨a, ρ, he⟩
  have hfst : σ = ρ := by
    let : Algebra (F × F) F := (RingHom.fst F F).toAlgebra
    have hp := project_mixed F C S σ τ σ (by
      intro A H
      change (1 : F) • _ + (0 : F) • _ = _
      simp)
    have h := congrArg (DiagramAut.coefficientExtend (F × F) C S F) he
    rw [hp, map_mul, coefficientExtend_scalarQuadraticAut,
      coefficientExtend_galoisQuadraticAut] at h
    have hg := congrArg (DiagramAut.toGalois F C S hS hgen hn) h
    simpa using hg
  have hsnd : τ = ρ := by
    let : Algebra (F × F) F := (RingHom.snd F F).toAlgebra
    have hp := project_mixed F C S σ τ τ (by
      intro A H
      change (0 : F) • _ + (1 : F) • _ = _
      simp)
    have h := congrArg (DiagramAut.coefficientExtend (F × F) C S F) he
    rw [hp, map_mul, coefficientExtend_scalarQuadraticAut,
      coefficientExtend_galoisQuadraticAut] at h
    have hg := congrArg (DiagramAut.toGalois F C S hS hgen hn) h
    simpa using hg
  exact hστ (hfst.trans hsnd.symm)

/-- The entire full graded family also has no common scalar/Galois factorization. -/
theorem mixedGaloisAut_not_full_scalar_mul_galois
    (hS : (0 : k₀) ∈ S) (hgen : Subfield.closure S = ⊤) (hn : 2 ≤ n)
    (σ τ : k ≃ₐ[k₀] k) (hστ : σ ≠ τ) :
    ¬ ∃ (a : (F × F)ˣ) (ρ : k ≃ₐ[k₀] k), mixedGaloisAut F C S σ τ =
      scalarGradedAut (F × F) C S a * galoisGradedAut (F × F) C S ρ := by
  rintro ⟨a, ρ, he⟩
  apply mixedGaloisAut_not_scalar_mul_galois (F := F) C S hS hgen hn σ τ hστ
  refine ⟨a, ρ, ?_⟩
  have h := congrArg (GradedDiagramAut.toQuadratic (F × F) C S) he
  simpa only [map_mul, toQuadratic_scalarGradedAut, galoisQuadraticAut] using h

/-- A concrete disconnected counterexample over `𝔽₂ × 𝔽₂`, using the identity and complex
conjugation on the actual full cofinal system in dimension two. The common target remains
identity, but neither full nor quadratic classification by a single Galois factor holds.
Thus the local-ring or integral-domain hypotheses in S03–S05 are necessary. -/
theorem binary_complex_disconnected_counterexample :
    (mixedGaloisAut (ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ 1 Complex.conjAe).targetEquiv =
        AlgEquiv.refl ∧
    (¬∃ (a : (ZMod 2 × ZMod 2)ˣ) (ρ : ℂ ≃ₐ[ℝ] ℂ),
      GradedDiagramAut.toQuadratic (ZMod 2 × ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ
        (mixedGaloisAut (ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ 1 Complex.conjAe) =
      scalarQuadraticAut (ZMod 2 × ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ a *
        galoisQuadraticAut (ZMod 2 × ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ ρ) ∧
    (¬∃ (a : (ZMod 2 × ZMod 2)ˣ) (ρ : ℂ ≃ₐ[ℝ] ℂ),
      mixedGaloisAut (ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ 1 Complex.conjAe =
      scalarGradedAut (ZMod 2 × ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ a *
        galoisGradedAut (ZMod 2 × ZMod 2) (fullCofinalSystem ℝ ℂ 2) Set.univ ρ) := by
  have hconj : (1 : ℂ ≃ₐ[ℝ] ℂ) ≠ Complex.conjAe := by
    intro he
    have him := congrArg Complex.im (AlgEquiv.congr_fun he Complex.I)
    norm_num at him
  exact ⟨mixedGaloisAut_target _ _ _ _ _,
    mixedGaloisAut_not_scalar_mul_galois (F := ZMod 2) _ _
      (by trivial) (by simp) (by decide) _ _ hconj,
    mixedGaloisAut_not_full_scalar_mul_galois (F := ZMod 2) _ _
      (by trivial) (by simp) (by decide) _ _ hconj⟩

end OrlikSolomon.HyperplaneGT.DisconnectedExamples
