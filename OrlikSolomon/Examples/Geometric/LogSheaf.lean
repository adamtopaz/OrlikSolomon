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
example (U : P.ambient.obj.left.Opensᵒᵖ) :
    logSheafPullbackAt (𝟙 P) n U = (logSheafIdentitySectionsEquiv P n U).toLinearMap := by
  simp

/-- Residue of a normal form simplifies through zero addition on one concrete divisor carrier. -/
example (U : P.ambient.obj.left.Opensᵒᵖ)
    (ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj U)
    (η : (formsSheaf k P.ambient.obj n).obj.obj U) :
    logResidueSheafAt P n U
      ((regularToLogSheaf P (n + 1)).hom.app U ω + (thetaToLogSheaf P n).hom.app U η) =
      formsSheafPullbackAt P.i.hom U.unop n η := by
  simp only [map_add, logResidueSheafAt_regular, logResidueSheafAt_theta, zero_add]

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
