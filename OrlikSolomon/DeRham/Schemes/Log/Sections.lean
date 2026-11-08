/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Naturality

/-!
# Logarithmic operations on explicit section carriers

The maps here display complement and divisor sections on inverse-image opens. They avoid
mixing the carrier of a direct-image sheaf with the equal concrete section carrier in one
formula. The underlying sheaf maps and their existing public statements are unchanged.

## Main results

`logToOpenSheafAt_theta`, `logResidueSheafAt_regular_add_theta`, and
`logSheafPullbackAt_id`. These formulas support ordinary `simp` and ring rewriting without
unfolding the image construction or a direct-image functor.

The named target module `logSheafPullbackSections` keeps identity preimages out of implicit
carrier arguments. Consequently the usual linear-equivalence coercion, inverse, addition
and scalar-multiplication simp lemmas apply to `logSheafIdentitySectionsEquiv`.
For inverse reindexing of an arbitrary target section, use the carrier
`logSheafPullbackSections (𝟙 P) n U` in its binder.

Blueprint: the section formulas in `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k] {D : SmoothDomain k} (P : DivisorPair D)

/-- Inclusion on an ambient open, displaying the actual complement section carrier. -/
def logToOpenSheafAt (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logSheaf P n).obj.obj U →ₗ[k]
      (formsSheaf k P.compl.obj n).obj.obj (op (P.j.hom.left ⁻¹ᵁ U.unop)) :=
  ((logToOpenSheaf P n).hom.app U).hom

/-- Residue on an ambient open, displaying the actual divisor section carrier. -/
def logResidueSheafAt (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logSheaf P (n + 1)).obj.obj U →ₗ[k]
      (formsSheaf k P.closed.obj n).obj.obj (op (P.i.hom.left ⁻¹ᵁ U.unop)) :=
  ((logResidueSheaf P n).hom.app U).hom

/-- On explicit section carriers, regular inclusion is ordinary pullback. -/
@[simp] theorem logToOpenSheafAt_regular (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logToOpenSheafAt P n U ((regularToLogSheaf P n).hom.app U a) =
      formsSheafPullbackAt P.j.hom U.unop n a :=
  regularToLogSheaf_logToOpenSheaf P n U a

/-- On explicit section carriers, the theta generator includes as left logarithmic
multiplication. -/
@[simp] theorem logToOpenSheafAt_theta (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logToOpenSheafAt P (n + 1) U ((thetaToLogSheaf P n).hom.app U a) =
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        (formsSheafPullbackAt P.j.hom U.unop n a) :=
  thetaToLogSheaf_logToOpenSheaf P n U a

/-- Regular forms have zero residue on the explicit divisor section carrier. -/
@[simp] theorem logResidueSheafAt_regular (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj (n + 1)).obj.obj U) :
    logResidueSheafAt P n U ((regularToLogSheaf P (n + 1)).hom.app U a) = 0 :=
  logResidueSheaf_regular P n U a

/-- The residue of a theta generator is restriction of its coefficient. -/
@[simp] theorem logResidueSheafAt_theta (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logResidueSheafAt P n U ((thetaToLogSheaf P n).hom.app U a) =
      formsSheafPullbackAt P.i.hom U.unop n a :=
  logResidueSheaf_theta P n U a

/-- Residue reads the theta coefficient of a normal form, using one divisor carrier throughout. -/
@[simp] theorem logResidueSheafAt_regular_add_theta (n : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k P.ambient.obj (n + 1)).obj.obj U)
    (b : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logResidueSheafAt P n U
      ((regularToLogSheaf P (n + 1)).hom.app U a + (thetaToLogSheaf P n).hom.app U b) =
      formsSheafPullbackAt P.i.hom U.unop n b := by
  simp only [map_add, logResidueSheafAt_regular, logResidueSheafAt_theta, zero_add]

/-- The canonical reindexing from an open to its inverse image under the identity pair map.
Its named target module is stable under simplification of identity-morphism projections. -/
def logSheafIdentitySectionsEquiv (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    (logSheaf P n).obj.obj U ≃ₗ[k] logSheafPullbackSections (𝟙 P) n U :=
  (eqToIso (by rfl : (logSheaf P n).obj.obj U =
    logSheafPullbackSections (𝟙 P) n U)).toLinearEquiv

/-- Identity logarithmic pullback is the canonical section reindexing. The inverse-image open
is displayed on both sides, rather than identified through a direct-image object. -/
@[simp] theorem logSheafPullbackAt_id (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ) :
    logSheafPullbackAt (𝟙 P) n U = (logSheafIdentitySectionsEquiv P n U).toLinearMap := by
  ext a
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_id P n)) U) a

/-- Undoing the inverse-image reindexing after identity pullback recovers the original section.
The ordinary identity and linear-equivalence simp lemmas already prove this equality.
Blueprint: the identity compatibility in `thm:geo-log-sheaves`. -/
theorem logSheafPullbackAt_id_cancel (n : ℕ) (U : P.ambient.obj.left.Opensᵒᵖ)
    (x : (logSheaf P n).obj.obj U) :
    (logSheafIdentitySectionsEquiv P n U).symm (logSheafPullbackAt (𝟙 P) n U x) = x := by
  rw [logSheafPullbackAt_id]
  exact (logSheafIdentitySectionsEquiv P n U).symm_apply_apply x

end OrlikSolomon.Geometric.DeRham
