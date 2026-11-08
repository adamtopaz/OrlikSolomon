/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Data.ZMod.Basic
public import OrlikSolomon.DeRham.Schemes.Log

/-!
# Consumers of the logarithmic section API

These examples import the logarithmic umbrella alone. They check simplification on explicit
complement/divisor section carriers, identity reindexing, the signed theta differential,
and affine global comparison and residue lifts. Characteristic two and the zero base ring
exercise global lifts without an ordinary-theory instance.

Blueprint: the public section and affine formulas of `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open OrlikSolomon.Geometric.DeRham

universe u

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [CommRing k] {D : SmoothDomain k} (P : DivisorPair D) (n : ℕ)

/-- Identity pullback simplifies with its canonical inverse-image reindexing. -/
example (U : P.ambient.obj.left.Opensᵒᵖ) (x : (logSheaf P n).obj.obj U) :
    (logSheafIdentitySectionsEquiv P n U).symm (logSheafPullbackAt (𝟙 P) n U x) = x := by
  simp

/-- The pointwise identity law normalizes the linear-map coercion. -/
example (U : P.ambient.obj.left.Opensᵒᵖ) (x : (logSheaf P n).obj.obj U) :
    logSheafPullbackAt (𝟙 P) n U x = logSheafIdentitySectionsEquiv P n U x := by
  simp

/-- The named inverse-image module keeps linear-equivalence coercions stable under simp. -/
example (U : P.ambient.obj.left.Opensᵒᵖ) (x : (logSheaf P n).obj.obj U) :
    (logSheafIdentitySectionsEquiv P n U).toLinearMap x =
      logSheafIdentitySectionsEquiv P n U x := by
  simp

/-- Identity reindexing cancels after addition of separately pulled-back sections. -/
example (U : P.ambient.obj.left.Opensᵒᵖ) (x y : (logSheaf P n).obj.obj U) :
    (logSheafIdentitySectionsEquiv P n U).symm
      (logSheafPullbackAt (𝟙 P) n U x + logSheafPullbackAt (𝟙 P) n U y) = x + y := by
  simp

/-- Identity reindexing cancels through scalar multiplication. -/
example (U : P.ambient.obj.left.Opensᵒᵖ) (c : k) (x : (logSheaf P n).obj.obj U) :
    (logSheafIdentitySectionsEquiv P n U).symm (c • logSheafPullbackAt (𝟙 P) n U x) =
      c • x := by
  simp

/-- Residue of a normal form simplifies through zero addition on one concrete divisor carrier. -/
example (U : P.ambient.obj.left.Opensᵒᵖ)
    (ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj U)
    (η : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logResidueSheafAt P n U
      ((regularToLogSheaf P (n + 1)).hom.app U ω + (thetaToLogSheaf P n).hom.app U η) =
      formsSheafPullbackAt P.i.hom U.unop n η := by
  simp

/-- The named module remains transparent to the original pullback and wedge simp API. -/
example {Q : DivisorPair D} (F : P ⟶ Q) (p q : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ) (c : k)
    (a : (logSheaf Q p).obj.obj U) (b : (logSheaf Q q).obj.obj U) :
    logSheafPullbackAt F (p + q) U (c • logSheafWedge Q p q U a b) =
      c • logSheafWedge P p q (op (F.ambient.hom.left ⁻¹ᵁ U.unop))
        (logSheafPullbackAt F p U a) (logSheafPullbackAt F q U b) := by
  simp

/-- Inclusion of a theta generator simplifies to left logarithmic multiplication. -/
example (U : P.ambient.obj.left.Opensᵒᵖ)
    (η : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logToOpenSheafAt P (n + 1) U ((thetaToLogSheaf P n).hom.app U η) =
      (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op (P.j.hom.left ⁻¹ᵁ U.unop))
        (formsSheafPullbackAt P.j.hom U.unop n η) := by
  simp

/-- The logarithmic differential rewrites to the negative coefficient differential. -/
example : thetaToLogSheaf P n ≫ logSheafD P (n + 1) +
    formsSheafD k P.ambient.obj n ≫ thetaToLogSheaf P (n + 1) = 0 := by
  rw [thetaToLogSheaf_d, neg_add_cancel]

/-- The applied differential formula rewrites directly on sections. -/
example (U : P.ambient.obj.left.Opensᵒᵖ)
    (η : (formsSheaf k P.ambient.obj n).obj.obj U)
    (hη : (formsSheafD k P.ambient.obj n).hom.app U η = 0) :
    (logSheafD P (n + 1)).hom.app U ((thetaToLogSheaf P n).hom.app U η) = 0 := by
  rw [thetaToLogSheaf_d_apply, hη, map_zero, neg_zero]

/-- The global wedge formula uses theta without an identity restriction. -/
example (η : (formsSheaf k P.compl.obj n).obj.obj (op ⊤)) :
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op ⊤) η =
      (formsSheafCast k P.compl.obj (Nat.add_comm 1 n)).hom.app (op ⊤)
        (formsSheafWedge k P.compl.obj 1 n (op ⊤) (thetaSection P) η) := by
  rw [thetaWedgeSheaf_top_eq_wedge]

variable (Q : DivisorPair (SmoothDomain.aff k))

/-- On an affine pair, every divisor section has a global logarithmic lift over any base ring. -/
example (γ : (formsSheaf k Q.closed.obj n).obj.obj (op ⊤)) :
    ∃ l, logResidueSheafTop Q n l = γ := logResidueSheafTop_surjective Q n γ

/-- A lift of a closed divisor section differentiates to a regular global form. -/
example (l : (logSheaf Q (n + 1)).obj.obj (op ⊤))
    (hl : (formsSheafD k Q.closed.obj n).hom.app (op ⊤) (logResidueSheafTop Q n l) = 0) :
    ∃ ω, regularToLogTop Q (n + 1 + 1) ω = (logSheafD Q (n + 1)).hom.app (op ⊤) l :=
  exists_regularToLogTop_eq_logSheafD_of_residue_closed Q n l hl

/-- Affine global logarithmic comparison needs only invertibility of positive integers. -/
example (hUnits : ∀ m : ℕ, IsUnit (m + 1 : k)) :
    QuasiIso (((sheafSectionsFunctor (k := k) Q.ambient.obj.left ⊤).mapHomologicalComplex
      (.up ℕ)).map (logToOpenComplexNat Q)) := affineGlobalLogToOpen_quasiIso Q hUnits

/-- Characteristic two still has every global residue lift for the standard affine pair. -/
example (m : ℕ) : Function.Surjective
    (logResidueSheafTop (DivisorPair.standardPair (SmoothDomain.aff (ZMod 2))
      (SmoothDomain.aff (ZMod 2)).point) m) := logResidueSheafTop_surjective _ _

/-- The same global residue lift API works on the empty smooth scheme over the zero ring. -/
example (m : ℕ) : Function.Surjective
    (logResidueSheafTop (DivisorPair.standardPair (SmoothDomain.aff PUnit)
      (SmoothDomain.aff PUnit).point) m) := logResidueSheafTop_surjective _ _

end OrlikSolomon.Geometric.Examples
