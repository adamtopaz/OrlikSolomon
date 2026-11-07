/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Presentation.Geometric

/-!
# Acceptance consumers for the geometric public facade

This file imports only `Presentation.Geometric`. It states both structure theorems for a theory
on all smooth schemes and checks their equation formulas, without any affine comparison supplied
by the user. The deletion consumers also check the ambient, closed and open comparisons and both
cohomology maps across the pair isomorphism.

Blueprint: acceptance tests following `thm:geo-transport-all`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Module
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (T : OrdinaryTheory.{u, v, w, z} (SmoothDomain.all k) ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (𝒜 : Arrangement k V)

/-- A theory on all smooth schemes supplies the affine theorem with its actual open target. -/
example : OSAlgebra B 𝒜 ≃ₐ[B] T.obj ((SmoothDomain.all k).complement 𝒜) :=
  T.affineEquiv 𝒜

/-- Its generator formula accepts any equation, without changing the canonical target. -/
example (H : 𝒜) {f : V →ᵃ[k] k} (hf : IsEquation f H) :
    T.affineEquiv 𝒜 (generator B 𝒜 H) =
      T.logClass (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [T.affineEquiv_generator_of_isEquation H hf]

/-- The point axiom uses the public object algebra without additional scalar transports. -/
example : Function.Bijective (algebraMap B (T.obj (SmoothDomain.all k).point)) :=
  T.bijective_algebraMap_point

/-- The empty smooth affine scheme has zero cohomology even when coefficients are nonzero. -/
example : Subsingleton (T.obj ((SmoothDomain.all k).spec (SmoothAlg.zero k))) := by
  let : IsEmpty (((SmoothDomain.all k).spec (SmoothAlg.zero k)).obj.left) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (SmoothAlg.zero k)))
  exact T.emptySubsingleton _

/-- The geometric theorem also applies in ambient dimension zero. -/
example (𝒜₀ : Arrangement k (Fin 0 → k)) :
    OSAlgebra B 𝒜₀ ≃ₐ[B] T.obj ((SmoothDomain.all k).complement 𝒜₀) :=
  T.affineEquiv 𝒜₀

/-- The first summand in the product with `𝔾ₘ` supports ordinary ring simplification. -/
example (X : (SmoothDomain.all k).Obj) (a : T.obj X) :
    T.gmProductEquiv X (a, 0) = T.pull ((SmoothDomain.all k).prodGmFst X) a := by
  simp only [OrdinaryTheory.gmProductEquiv_apply, map_zero, mul_zero, add_zero]

/-- Its second summand is recovered by the typed standard residue. -/
example (X : (SmoothDomain.all k).Obj) (a b : T.obj X) :
    T.standardResidue X (T.gmProductEquiv X (a, b)) + 0 = b := by
  rw [T.standardResidue_gmProductEquiv, add_zero]

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (P : ProjectiveArrangement k W) [Nonempty P]

/-- Nonemptiness is the only additional hypothesis for the projective theorem. -/
example : projectiveAlgebra B P.cone_isCentral ≃ₐ[B]
    T.obj ((SmoothDomain.all k).projectiveComplement P) :=
  T.projectiveEquiv P

/-- The projective generator formula accepts equations of arbitrary hyperplane labels. -/
example (H K : P) {ℓ ℓ' : Dual k W}
    (hℓ : LinearMap.ker ℓ = (H : Submodule k W))
    (hℓ' : LinearMap.ker ℓ' = (K : Submodule k W)) :
    T.projectiveEquiv P (projectiveDifference B P.cone_isCentral
      (P.coneHyperplaneEquiv H) (P.coneHyperplaneEquiv K)) =
      T.logClass (projectiveRatio (ℓ := ℓ) (ℓ' := ℓ')
        (by rw [hℓ]; exact H.2) (by rw [hℓ']; exact K.2)) := by
  rw [T.projectiveEquiv_difference_of_ker_eq P H K hℓ hℓ']

section Deletion

variable {𝒜} {H : AffineSubspace k V} {f : V →ᵃ[k] k}
  (hH : H ∈ 𝒜) (hf : IsEquation f H)

/-- The pair comparison uses the three canonical complement comparisons simultaneously. -/
example :
    (DivisorPair.deletionPairIsoSpec (SmoothDomain.all k) hH hf).hom.ambient =
        ((SmoothDomain.all k).complementIsoSpec (𝒜.deletion H)).hom ∧
    (DivisorPair.deletionPairIsoSpec (SmoothDomain.all k) hH hf).hom.closed =
        ((SmoothDomain.all k).complementIsoSpec (𝒜.restriction H)).hom ∧
    (DivisorPair.deletionPairIsoSpec (SmoothDomain.all k) hH hf).hom.compl =
        ((SmoothDomain.all k).complementIsoSpec 𝒜).hom := by
  exact ⟨DivisorPair.deletionPairIsoSpec_hom_ambient _ _ _,
    DivisorPair.deletionPairIsoSpec_hom_closed _ _ _,
    DivisorPair.deletionPairIsoSpec_hom_compl _ _ _⟩

/-- The comparison commutes with the closed arrow of deletion. -/
example :
    (SmoothDomain.all k).complementRestriction 𝒜 (𝒜.isHyperplane hH) ≫
        ((SmoothDomain.all k).complementIsoSpec (𝒜.deletion H)).hom =
      ((SmoothDomain.all k).complementIsoSpec (𝒜.restriction H)).hom ≫
        (DivisorPair.spec (SmoothDomain.all k)
          (OrlikSolomon.DivisorPair.deletionPair 𝒜 hH hf)).i := by
  rw [DivisorPair.deletionPair_hi (SmoothDomain.all k) hH hf]

/-- The comparison also commutes with the open arrow of deletion. -/
example :
    (SmoothDomain.all k).complementInclusion (𝒜.deletion_le H) ≫
        ((SmoothDomain.all k).complementIsoSpec (𝒜.deletion H)).hom =
      ((SmoothDomain.all k).complementIsoSpec 𝒜).hom ≫
        (DivisorPair.spec (SmoothDomain.all k)
          (OrlikSolomon.DivisorPair.deletionPair 𝒜 hH hf)).j := by
  rw [DivisorPair.deletionPair_hj (SmoothDomain.all k) hH hf]

/-- Gysin commutes with the closed and ambient comparison maps. -/
example (x : T.toAlgebraic.C.obj (SmoothAlg.complement (𝒜.restriction H))) :
    T.gysin (DivisorPair.deletionPair (SmoothDomain.all k) 𝒜 hH hf)
        (T.pull ((SmoothDomain.all k).complementIsoSpec (𝒜.restriction H)).hom x) =
      T.pull ((SmoothDomain.all k).complementIsoSpec (𝒜.deletion H)).hom
        (T.gysin (DivisorPair.spec (SmoothDomain.all k)
          (OrlikSolomon.DivisorPair.deletionPair 𝒜 hH hf)) x) := by
  have h := T.gysin_pull (DivisorPair.deletionPairIsoSpec (SmoothDomain.all k) hH hf).hom x
  rw [DivisorPair.deletionPairIsoSpec_hom_closed,
    DivisorPair.deletionPairIsoSpec_hom_ambient] at h
  exact h

/-- Residue commutes with the open and closed comparison maps. -/
example (x : T.toAlgebraic.C.obj (SmoothAlg.complement 𝒜)) :
    T.residue (DivisorPair.deletionPair (SmoothDomain.all k) 𝒜 hH hf)
        (T.pull ((SmoothDomain.all k).complementIsoSpec 𝒜).hom x) =
      T.pull ((SmoothDomain.all k).complementIsoSpec (𝒜.restriction H)).hom
        (T.residue (DivisorPair.spec (SmoothDomain.all k)
          (OrlikSolomon.DivisorPair.deletionPair 𝒜 hH hf)) x) := by
  have h := T.residue_pull (DivisorPair.deletionPairIsoSpec (SmoothDomain.all k) hH hf).hom x
  rw [DivisorPair.deletionPairIsoSpec_hom_compl,
    DivisorPair.deletionPairIsoSpec_hom_closed] at h
  exact h

end Deletion

end OrlikSolomon.Geometric.Examples
