/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Algebra
public import OrlikSolomon.DeRham.Schemes.Log.Residue
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The right projection formula for logarithmic residue

Residue of a logarithmic form multiplied on the right by a regular form is the wedge
of its residue with the restriction of that regular form to the divisor, with no sign.
The formula is checked on local normal forms and glued by sheaf separatedness.
This size split of `Log/Naturality` uses arbitrary commutative base rings and domains.

Blueprint: the right form projection identity in `thm:geo-log-sheaves`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k] {D : SmoothDomain k}

/-- Differentiating a left-theta logarithmic form negates the differential of its coefficient. -/
@[reassoc] theorem thetaToLogSheaf_d (P : DivisorPair D) (n : ℕ) :
    thetaToLogSheaf P n ≫ logSheafD P (n + 1) =
      -(formsSheafD k P.ambient.obj n ≫ thetaToLogSheaf P (n + 1)) := by
  simp only [thetaToLogSheaf, Category.assoc, logMkSheaf_d, biprod.inr_map_assoc,
    Preadditive.neg_comp]

/-- On sections, the differential of a theta generator is minus theta times the
differential of its coefficient. -/
theorem thetaToLogSheaf_d_apply (P : DivisorPair D) (n : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    (logSheafD P (n + 1)).hom.app U ((thetaToLogSheaf P n).hom.app U a) =
      -((thetaToLogSheaf P (n + 1)).hom.app U ((formsSheafD k P.ambient.obj n).hom.app U a)) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (thetaToLogSheaf_d P n)) U) a

/-- The residue of a left logarithmic generator is restriction of its coefficient. -/
@[reassoc (attr := simp)] theorem thetaToLogSheaf_residue (P : DivisorPair D) (n : ℕ) :
    thetaToLogSheaf P n ≫ logResidueSheaf P n = formsSheafPullback P.i.hom n := by
  change (biprod.inr ≫ logMkSheaf P n) ≫ logResidueSheaf P n = _
  rw [Category.assoc, logMkSheaf_residue, biprod.inr_snd_assoc]

private lemma logSheafCast_regular (P : DivisorPair D) {p q : ℕ} (h : p = q)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (formsSheaf k P.ambient.obj p).obj.obj U) :
    (logSheafCast P h).hom.app U ((regularToLogSheaf P p).hom.app U a) =
      (regularToLogSheaf P q).hom.app U ((formsSheafCast k P.ambient.obj h).hom.app U a) := by
  subst q
  rfl
private lemma logSheafCast_cancel (P : DivisorPair D) {p q : ℕ} (h : p = q)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (logSheaf P q).obj.obj U) :
    (logSheafCast P h).hom.app U ((logSheafCast P h.symm).hom.app U a) = a := by
  subst q
  rfl

/-- Residue annihilates regular forms, on every ambient open.
For simplification on the actual divisor carrier, use `logResidueSheafAt_regular`. -/
@[simp] theorem logResidueSheaf_regular (P : DivisorPair D) (n : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (formsSheaf k P.ambient.obj (n + 1)).obj.obj U) :
    (logResidueSheaf P n).hom.app U ((regularToLogSheaf P (n + 1)).hom.app U a) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (regularToLogSheaf_residue P n)) U) a

/-- Residue of a logarithmic generator is the restriction of its coefficient.
For simplification on the actual divisor carrier, use `logResidueSheafAt_theta`. -/
@[simp] theorem logResidueSheaf_theta (P : DivisorPair D) (n : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (formsSheaf k P.ambient.obj n).obj.obj U) :
    (logResidueSheaf P n).hom.app U ((thetaToLogSheaf P n).hom.app U a) =
      (formsSheafPullback P.i.hom n).hom.app U a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f => f.hom) (thetaToLogSheaf_residue P n)) U) a
private lemma right_projection_normal (P : DivisorPair D) (p q : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ)
    (ω : (formsSheaf k P.ambient.obj (p + 1)).obj.obj U)
    (η : (formsSheaf k P.ambient.obj p).obj.obj U)
    (β : (formsSheaf k P.ambient.obj q).obj.obj U) :
    (logResidueSheaf P (p + q)).hom.app U
      ((logSheafCast P (Nat.add_right_comm p 1 q)).hom.app U
        (logSheafWedge P (p + 1) q U
          ((regularToLogSheaf P (p + 1)).hom.app U ω + (thetaToLogSheaf P p).hom.app U η)
          ((regularToLogSheaf P q).hom.app U β))) =
      formsSheafWedge k P.closed.obj p q (op (P.i.hom.left ⁻¹ᵁ U.unop))
        ((logResidueSheaf P p).hom.app U
          ((regularToLogSheaf P (p + 1)).hom.app U ω + (thetaToLogSheaf P p).hom.app U η))
        ((formsSheafPullback P.i.hom q).hom.app U β) := by
  rw [logSheafWedge_add_left, logSheafWedge_regular, logSheafWedge_theta_regular]
  simp only [map_add, logSheafCast_regular, logResidueSheaf_regular,
    logSheafCast_cancel, zero_add, logResidueSheaf_theta]
  exact formsSheafPullback_wedge P.i.hom p q U η β

private lemma logMkSheaf_decomposition (P : DivisorPair D) (p : ℕ) :
    logMkSheaf P p = biprod.fst ≫ regularToLogSheaf P (p + 1) +
      biprod.snd ≫ thetaToLogSheaf P p := by
  calc
    _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ logMkSheaf P p := by
      rw [biprod.total, Category.id_comp]
    _ = _ := by
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, inl_logMkSheaf]
      rfl

/-- Wedge product on divisor forms with their ambient direct-image section carrier. -/
def closedFormsSheafWedge (P : DivisorPair D) (p q : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (closedFormsSheaf P p).obj.obj U)
    (b : (closedFormsSheaf P q).obj.obj U) : (closedFormsSheaf P (p + q)).obj.obj U :=
  formsSheafWedge k P.closed.obj p q (op (P.i.hom.left ⁻¹ᵁ U.unop)) a b

/-- The ambient-carrier wedge is the ordinary wedge on the inverse-image open of the divisor. -/
theorem closedFormsSheafWedge_eq (P : DivisorPair D) (p q : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (a : (closedFormsSheaf P p).obj.obj U)
    (b : (closedFormsSheaf P q).obj.obj U) :
    closedFormsSheafWedge P p q U a b =
      formsSheafWedge k P.closed.obj p q (op (P.i.hom.left ⁻¹ᵁ U.unop)) a b := rfl

/-- Residue satisfies the right projection formula without a sign. The degree cast only
identifies `(p + 1) + q` with `(p + q) + 1`.

Blueprint: the right form projection identity in `thm:geo-log-sheaves`. -/
theorem logResidueSheaf_right_projection (P : DivisorPair D) (p q : ℕ)
    (U : P.ambient.obj.left.Opensᵒᵖ) (α : (logSheaf P (p + 1)).obj.obj U)
    (β : (formsSheaf k P.ambient.obj q).obj.obj U) :
    (logResidueSheaf P (p + q)).hom.app U
      ((logSheafCast P (Nat.add_right_comm p 1 q)).hom.app U
        (logSheafWedge P (p + 1) q U α ((regularToLogSheaf P q).hom.app U β))) =
      closedFormsSheafWedge P p q U
        ((logResidueSheaf P p).hom.app U α)
        ((formsSheafPullback P.i.hom q).hom.app U β) := by
  have : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology P.ambient.obj.left)
      (logMkSheaf P p).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).2 inferInstance
  apply (closedFormsSheaf P (p + q)).isSeparated _ _
    (Presheaf.imageSieve_mem _ (logMkSheaf P p).hom α)
  rintro V f ⟨t, ht⟩
  have hleft : (closedFormsSheaf P (p + q)).obj.map f.op
      ((logResidueSheaf P (p + q)).hom.app U
        ((logSheafCast P (Nat.add_right_comm p 1 q)).hom.app U
          (logSheafWedge P (p + 1) q U α ((regularToLogSheaf P q).hom.app U β)))) =
      (logResidueSheaf P (p + q)).hom.app (op V)
        ((logSheafCast P (Nat.add_right_comm p 1 q)).hom.app (op V)
          (logSheafWedge P (p + 1) q (op V) ((logSheaf P (p + 1)).obj.map f.op α)
            ((regularToLogSheaf P q).hom.app (op V)
              ((formsSheaf k P.ambient.obj q).obj.map f.op β)))) := by
    rw [← (logResidueSheaf P (p + q)).hom.naturality_apply f.op,
      ← (logSheafCast P (Nat.add_right_comm p 1 q)).hom.naturality_apply f.op,
      logSheafWedge_naturality, ← (regularToLogSheaf P q).hom.naturality_apply f.op]
  have hright : (closedFormsSheaf P (p + q)).obj.map f.op
      (formsSheafWedge k P.closed.obj p q (op (P.i.hom.left ⁻¹ᵁ U.unop))
        ((logResidueSheaf P p).hom.app U α) ((formsSheafPullback P.i.hom q).hom.app U β)) =
      formsSheafWedge k P.closed.obj p q (op (P.i.hom.left ⁻¹ᵁ V))
        ((logResidueSheaf P p).hom.app (op V) ((logSheaf P (p + 1)).obj.map f.op α))
        ((formsSheafPullback P.i.hom q).hom.app (op V)
          ((formsSheaf k P.ambient.obj q).obj.map f.op β)) := by
    change (formsSheaf k P.closed.obj (p + q)).obj.map
      ((TopologicalSpace.Opens.map P.i.hom.left.base).map f).op _ = _
    exact (formsSheafWedge_naturality k P.closed.obj p q
      ((TopologicalSpace.Opens.map P.i.hom.left.base).map f).op _ _).trans
        (congrArg₂ (formsSheafWedge k P.closed.obj p q _)
          ((logResidueSheaf P p).hom.naturality_apply f.op α).symm
          ((formsSheafPullback P.i.hom q).hom.naturality_apply f.op β).symm)
  refine hleft.trans (Eq.trans ?_ hright.symm)
  rw [← ht]
  have hdec := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logMkSheaf_decomposition P p)) (op V)) t
  change (logMkSheaf P p).hom.app (op V) t =
    (regularToLogSheaf P (p + 1)).hom.app (op V)
      ((biprod.fst : formsSheaf k P.ambient.obj (p + 1) ⊞ formsSheaf k P.ambient.obj p ⟶ _).hom.app
        (op V) t) +
    (thetaToLogSheaf P p).hom.app (op V)
      ((biprod.snd : formsSheaf k P.ambient.obj (p + 1) ⊞ formsSheaf k P.ambient.obj p ⟶ _).hom.app
        (op V) t) at hdec
  rw [hdec]
  exact right_projection_normal P p q (op V) _ _ _

end OrlikSolomon.Geometric.DeRham
