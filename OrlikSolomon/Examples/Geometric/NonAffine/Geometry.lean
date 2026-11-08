/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Schemes.Projective
public import OrlikSolomon.Cohomology.Geometric.Logarithms
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The non-affine projective line

The projective line is the actual scheme `Proj Sym((k²)*)`, over `Spec k`. Its structure
map is smooth and proper, and its underlying scheme is not affine, over every field.
It therefore belongs both to the all-smooth domain and to the smooth separated finite-type
domain. The standard product pair and the product-with-`𝔾ₘ` equivalence apply to it.

The non-affineness proof uses homogeneous prime ideals, independently of rational points.
The generic homogeneous prime specializes to `(X₀)`. If the projective line were affine,
properness would make its structure map finite and its topology discrete.

Blueprint: the geometric assertions of `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace

universe u v w z

namespace OrlikSolomon.Geometric.Examples

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The projective line over `k`, as the projectivization of the two-dimensional vector space.
Blueprint: `prop:geo-nonaffine`. -/
@[instance_reducible]
def projectiveLine : Over (Spec (.of k)) := projectiveSpace k (Fin 2 → k)

/-- The projective line is smooth over the base field. -/
instance projectiveLine_smooth : Smooth (projectiveLine k).hom :=
  smooth_projectiveSpace_hom

private instance : IsScalarTower k (symmetricGrading k (Dual k (Fin 2 → k)) 0)
    (CoordinateRing k (Fin 2 → k)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The projective line is proper over the base field. -/
instance projectiveLine_proper : IsProper (projectiveLine k).hom := by
  have : Algebra.FiniteType (symmetricGrading k (Dual k (Fin 2 → k)) 0)
      (CoordinateRing k (Fin 2 → k)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap k (symmetricGrading k (Dual k (Fin 2 → k)) 0)))) := by
    have : IsIso (CommRingCat.ofHom
        (algebraMap k (symmetricGrading k (Dual k (Fin 2 → k)) 0))) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      constructor
      · intro x y h
        exact SymmetricAlgebra.algebraMap_leftInverse (R := k) (Dual k (Fin 2 → k))
          |>.injective (congrArg Subtype.val h)
      · intro x
        have hx := x.property
        change (x : CoordinateRing k (Fin 2 → k)) ∈
          (LinearMap.range (SymmetricAlgebra.ι k (Dual k (Fin 2 → k)))) ^ 0 at hx
        rw [pow_zero, Submodule.mem_one] at hx
        obtain ⟨r, hr⟩ := hx
        exact ⟨r, Subtype.ext hr⟩
    infer_instance
  change IsProper (projToSpec k (Fin 2 → k))
  unfold projToSpec
  infer_instance

private abbrev Index := ULift.{u} (Fin 2)

private abbrev grading := MvPolynomial.homogeneousSubmodule Index k

private lemma x_irrelevant (i : Index) :
    MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (grading k) :=
  HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
    (MvPolynomial.isHomogeneous_X k i)

private def originIdeal : HomogeneousIdeal (grading k) :=
  ⟨Ideal.span (MvPolynomial.X '' ({⟨0⟩} : Set Index)),
    Ideal.homogeneous_span _ _ (by
      rintro _ ⟨i, -, rfl⟩
      exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩)⟩

private lemma x_one_not_origin :
    (MvPolynomial.X (⟨1⟩ : Index) : MvPolynomial Index k) ∉ originIdeal k := by
  intro h
  change MvPolynomial.X (⟨1⟩ : Index) ∈ Ideal.span (MvPolynomial.X '' ({⟨0⟩} : Set Index)) at h
  rw [MvPolynomial.mem_ideal_span_X_image] at h
  have h' := h (Finsupp.single (⟨1⟩ : Index) 1) (by simp [MvPolynomial.X])
  obtain ⟨i, hi, h⟩ := h'
  simp only [Set.mem_singleton_iff] at hi
  subst i
  simp at h

private def genericPoint : ProjectiveSpectrum (grading k) where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (MvPolynomial Index k)).IsPrime; infer_instance
  not_irrelevant_le h := by
    have hx := h (x_irrelevant k ⟨0⟩)
    change MvPolynomial.X (⟨0⟩ : Index) ∈ (⊥ : Ideal (MvPolynomial Index k)) at hx
    exact MvPolynomial.X_ne_zero (R := k) (⟨0⟩ : Index) (by simpa only [Ideal.mem_bot] using hx)

private def originPoint : ProjectiveSpectrum (grading k) where
  asHomogeneousIdeal := originIdeal k
  isPrime := MvPolynomial.span_X_image_isPrime _
  not_irrelevant_le h := x_one_not_origin k (h (x_irrelevant k ⟨1⟩))

private lemma generic_ne_origin : genericPoint k ≠ originPoint k := by
  intro h
  have hx : MvPolynomial.X (⟨0⟩ : Index) ∈ (originPoint k).asHomogeneousIdeal :=
    Ideal.subset_span ⟨⟨0⟩, rfl, rfl⟩
  rw [← h] at hx
  change MvPolynomial.X (⟨0⟩ : Index) ∈ (⊥ : Ideal (MvPolynomial Index k)) at hx
  exact MvPolynomial.X_ne_zero (R := k) (⟨0⟩ : Index) (by simpa only [Ideal.mem_bot] using hx)

private lemma not_t1 : ¬ T1Space (Proj (grading k)) := by
  intro h
  change T1Space (ProjectiveSpectrum (grading k)) at h
  have := h
  have hle : genericPoint k ≤ originPoint k :=
    show (⊥ : HomogeneousIdeal (grading k)) ≤ originIdeal k from bot_le
  have hcl := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  rw [closure_singleton] at hcl
  exact generic_ne_origin k (Set.mem_singleton_iff.mp hcl).symm


/-- The projective line is not affine over any field.
Blueprint: `prop:geo-nonaffine`. -/
theorem projectiveLine_not_isAffine : ¬ IsAffine (projectiveLine k).left := by
  intro h
  have := h
  have : IsProper (projectiveLine k).hom := inferInstance
  have : IsFinite (projectiveLine k).hom :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have : IsLocallyArtinian (projectiveLine k).left :=
    IsLocallyArtinian.of_locallyQuasiFinite (projectiveLine k).hom
  have : DiscreteTopology (Proj (symmetricGrading k (Dual k (Fin 2 → k)))) :=
    inferInstanceAs (DiscreteTopology (projectiveLine k).left)
  have hhomeo := (projIsoMvPolynomial
    ((Pi.basisFun k (Fin 2)).dualBasis.reindex Equiv.ulift.symm)).hom.homeomorph
  exact not_t1 k hhomeo.symm.isEmbedding.t1Space

/-- The projective line as an object of the domain of all smooth schemes. -/
@[instance_reducible]
def projectiveLineAll : (SmoothDomain.all k).Obj :=
  ⟨projectiveLine k, projectiveLine_smooth k⟩

/-- The projective line as an object of the smooth separated finite-type domain. -/
@[instance_reducible]
def projectiveLineSft : (SmoothDomain.sft k).Obj :=
  ⟨projectiveLine k, inferInstance, inferInstance, inferInstance⟩

/-- The projective line is smooth, separated, of finite type, and non-affine.
Blueprint: `prop:geo-nonaffine`. -/
theorem projectiveLineScope :
    Smooth (projectiveLine k).hom ∧ IsSeparated (projectiveLine k).hom ∧
      QuasiCompact (projectiveLine k).hom ∧ ¬ IsAffine (projectiveLine k).left :=
  ⟨inferInstance, inferInstance, inferInstance, projectiveLine_not_isAffine k⟩

/-- The permitted pair `(ℙ¹ × 𝔸¹, ℙ¹ × {0}, ℙ¹ × 𝔾ₘ, z)` in the all-smooth domain.
Blueprint: `prop:geo-nonaffine`. -/
@[instance_reducible]
def projectiveLinePair : DivisorPair (SmoothDomain.all k) :=
  DivisorPair.standardPair _ (projectiveLineAll k)

/-- The same permitted pair in the smooth separated finite-type domain. -/
@[instance_reducible]
def projectiveLineSftPair : DivisorPair (SmoothDomain.sft k) :=
  DivisorPair.standardPair _ (projectiveLineSft k)

variable {k}
variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]

/-- The product-with-`𝔾ₘ` calculation applies to the actual non-affine projective line.
No cohomology calculation of `ℙ¹` is assumed. Blueprint: `prop:geo-nonaffine`. -/
@[no_expose]
def projectiveLineGmProduct (T : OrdinaryTheory.{u, v, w, z} (SmoothDomain.all k) ℬ) :
    (T.obj (projectiveLineAll k) × T.obj (projectiveLineAll k)) ≃ₗ[B]
      T.obj ((SmoothDomain.all k).prodGm (projectiveLineAll k)) :=
  T.gmProductEquiv (projectiveLineAll k)

/-- The product-with-`𝔾ₘ` calculation also applies in the separated finite-type domain. -/
@[no_expose]
def projectiveLineSftGmProduct (T : OrdinaryTheory.{u, v, w, z} (SmoothDomain.sft k) ℬ) :
    (T.obj (projectiveLineSft k) × T.obj (projectiveLineSft k)) ≃ₗ[B]
      T.obj ((SmoothDomain.sft k).prodGm (projectiveLineSft k)) :=
  T.gmProductEquiv (projectiveLineSft k)

/-- The two summands are `π* a` and `[z] π* b`, including for this non-affine base. -/
@[simp]
theorem projectiveLineGmProduct_apply
    (T : OrdinaryTheory.{u, v, w, z} (SmoothDomain.all k) ℬ)
    (a b : T.obj (projectiveLineAll k)) :
    projectiveLineGmProduct T (a, b) =
      T.pull ((SmoothDomain.all k).prodGmFst (projectiveLineAll k)) a +
        T.logClass ((SmoothDomain.all k).prodGmCoord (projectiveLineAll k)) *
          T.pull ((SmoothDomain.all k).prodGmFst (projectiveLineAll k)) b :=
  T.gmProductEquiv_apply a b

/-- The inverse reads off the section `z = 1` and the residue of the permitted pair. -/
theorem projectiveLineGmProduct_symm_apply
    (T : OrdinaryTheory.{u, v, w, z} (SmoothDomain.all k) ℬ)
    (x : T.obj ((SmoothDomain.all k).prodGm (projectiveLineAll k))) :
    (projectiveLineGmProduct T).symm x =
      (T.pull ((SmoothDomain.all k).oneSection (projectiveLineAll k)) x,
        T.residue (projectiveLinePair k) x) :=
  T.gmProductEquiv_symm_apply x

end OrlikSolomon.Geometric.Examples
