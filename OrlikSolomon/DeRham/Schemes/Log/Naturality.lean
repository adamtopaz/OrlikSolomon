/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module
public import OrlikSolomon.DeRham.Schemes.Log.Algebra
public import OrlikSolomon.DeRham.Schemes.Log.Projection
public import OrlikSolomon.DeRham.Schemes.Log.Residue
/-!
# Transverse pullback of logarithmic forms

Logarithmic forms pull back along every transverse morphism of geometric principal pairs.
The equation multiplier changes the logarithmic form by a regular logarithmic differential.
The resulting maps preserve regular inclusions, complement inclusions, residue and differential.
No flatness or characteristic assumption is used.

The main maps are `logSheafPullback` and `logComplexNatPullback`; the typed section maps
`logSheafPullbackAt` and `logSheafPullbackTop` preserve wedge products and units.
`logSheafPullbackSections` names the inverse-image module to keep identity reindexing stable
under simplification without changing the underlying section type.
`logSheafWithEqnIso` and `logComplexNatWithEqnIso` express invariance under associated equations.

Blueprint: naturality in `thm:geo-log-sheaves`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable {k : Type u} [CommRing k]

/-- The logarithmic differential of a product is the sum of the logarithmic differentials. -/
theorem thetaWedgeSheaf_mul (X : Over (Spec (CommRingCat.of k)))
    (v w : (sectionAlgebra k X ⊤)ˣ) (n : ℕ) :
    thetaWedgeSheaf X (v * w) n = thetaWedgeSheaf X v n + thetaWedgeSheaf X w n := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (_root_.Opens.grothendieckTopology X.left) _ _
    (formsSheaf k X (n + 1)).property
  ext U a
  change (thetaWedgeSheaf X (v * w) n).hom.app U ((formsSheafUnit k X n).app U a) =
    (thetaWedgeSheaf X v n).hom.app U ((formsSheafUnit k X n).app U a) +
      (thetaWedgeSheaf X w n).hom.app U ((formsSheafUnit k X n).app U a)
  let b (v : (sectionAlgebra k X ⊤)ˣ) : (formsPresheaf k X (n + 1)).obj U :=
    ⟨dlog k (Units.map (sectionRestriction k X U.unop.leTop).toMonoidHom v) * a.val,
      by simpa only [Nat.add_comm 1 n] using
        SetLike.mul_mem_graded (dlog_mem_exteriorPower_one k _) a.property⟩
  have hb : b (v * w) = b v + b w := by
    apply Subtype.ext
    change dlog k (Units.map (sectionRestriction k X U.unop.leTop).toMonoidHom (v * w)) * a.val =
      dlog k (Units.map (sectionRestriction k X U.unop.leTop).toMonoidHom v) * a.val +
        dlog k (Units.map (sectionRestriction k X U.unop.leTop).toMonoidHom w) * a.val
    rw [map_mul, dlog_mul, add_mul]
  rw [thetaWedgeSheaf_unit, thetaWedgeSheaf_unit, thetaWedgeSheaf_unit]
  change ((formsSheafUnit k X (n + 1)).app U).hom (b (v * w)) =
    ((formsSheafUnit k X (n + 1)).app U).hom (b v) +
      ((formsSheafUnit k X (n + 1)).app U).hom (b w)
  exact (congrArg ((formsSheafUnit k X (n + 1)).app U).hom hb).trans
    (((formsSheafUnit k X (n + 1)).app U).hom.map_add _ _)

variable {D : SmoothDomain k} {P Q : DivisorPair D}

/-- Transverse pullback changes the invertible equation by the ambient equation multiplier. -/
lemma pairPullback_eqnUnit (F : P ⟶ Q) (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) :
    Units.map (sectionPullbackTop F.compl.hom).toMonoidHom
        (show (sectionAlgebra k Q.compl.obj ⊤)ˣ from Q.eqnUnit) =
      Units.map (sectionPullbackTop P.j.hom).toMonoidHom
        (show (sectionAlgebra k P.ambient.obj ⊤)ˣ from u) *
      (show (sectionAlgebra k P.compl.obj ⊤)ˣ from P.eqnUnit) := by
  apply Units.ext
  change F.compl.hom.left.appTop (Q.eqnUnit : Γ(Q.compl.obj.left, ⊤)) =
    P.j.hom.left.appTop (u : Γ(P.ambient.obj.left, ⊤)) *
      (P.eqnUnit : Γ(P.compl.obj.left, ⊤))
  rw [Q.coe_eqnUnit, P.coe_eqnUnit, ← map_mul, ← hu]
  have h := congrArg (fun f => f.hom.left.appTop) F.j_comp
  exact (ConcreteCategory.congr_hom h Q.eqn).symm

private def complementThetaWedge (P : DivisorPair D)
    (v : (sectionAlgebra k P.compl.obj ⊤)ˣ) (n : ℕ) :
    openFormsSheaf P n ⟶ openFormsSheaf P (n + 1) :=
  (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (thetaWedgeSheaf P.compl.obj v n)

private lemma complementThetaWedge_pullback (F : P ⟶ Q)
    (v : (sectionAlgebra k Q.compl.obj ⊤)ˣ) (n : ℕ) :
    complementThetaWedge Q v n ≫ openFormsPullback F (n + 1) =
      openFormsPullback F n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (complementThetaWedge P (Units.map
            (sectionPullbackTop F.compl.hom).toMonoidHom v) n) := by
  rw [openFormsPullback_eq, openFormsPullback_eq]
  dsimp only [complementThetaWedge]
  rw [← Category.assoc, ← Functor.map_comp, thetaWedgeSheaf_pullback,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg
    (fun f ↦ (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
      (formsSheafPullback F.compl.hom n) ≫ f)
    ((pairOpenPushforwardIso F).hom.naturality
      (thetaWedgeSheaf P.compl.obj
        (Units.map (sectionPullbackTop F.compl.hom).toMonoidHom v) n))

private lemma thetaNormalFormPullback (F : P ⟶ Q) (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    (formsSheafPullback Q.j.hom n ≫ openThetaWedgeSheaf Q n) ≫
        openFormsPullback F (n + 1) =
      formsSheafPullback F.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          ((show formsSheaf k P.ambient.obj n ⟶ openFormsSheaf P (n + 1) from
            thetaWedgeSheaf P.ambient.obj
              (show (sectionAlgebra k P.ambient.obj ⊤)ˣ from u) n ≫
              formsSheafPullback P.j.hom (n + 1)) +
            formsSheafPullback P.j.hom n ≫ openThetaWedgeSheaf P n) := by
  change (formsSheafPullback Q.j.hom n ≫ complementThetaWedge Q Q.eqnUnit n) ≫ _ = _
  rw [Category.assoc, complementThetaWedge_pullback, ← Category.assoc,
    regularPullback_openFormsPullback, Category.assoc, ← Functor.map_comp]
  congr 1
  congr 1
  rw [pairPullback_eqnUnit F u hu]
  dsimp only [complementThetaWedge]
  rw [thetaWedgeSheaf_mul, Functor.map_add, comp_add,
    ← thetaWedgeSheaf_pullback P.j.hom
      (show (sectionAlgebra k P.ambient.obj ⊤)ˣ from u) n]
  rfl

private def normalFormPullback (F : P ⟶ Q) (u : Γ(P.ambient.obj.left, ⊤)ˣ) (n : ℕ) :
    formsSheaf k Q.ambient.obj (n + 1) ⊞ formsSheaf k Q.ambient.obj n ⟶
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).obj
        (logSheaf P (n + 1)) :=
  biprod.desc
    (formsSheafPullback F.ambient.hom (n + 1) ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
        (regularToLogSheaf P (n + 1)))
    (formsSheafPullback F.ambient.hom n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
        (thetaWedgeSheaf P.ambient.obj
            (show (sectionAlgebra k P.ambient.obj ⊤)ˣ from u) n ≫
            regularToLogSheaf P (n + 1) +
          biprod.inr ≫ logMkSheaf P n))

private lemma normalFormPullback_inclusion (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    normalFormPullback F u n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logToOpenSheaf P (n + 1)) =
      logNormalFormSheaf Q n ≫ openFormsPullback F (n + 1) := by
  apply biprod.hom_ext'
  · simp only [normalFormPullback, biprod.inl_desc_assoc, inl_logNormalFormSheaf_assoc]
    rw [Category.assoc, ← Functor.map_comp, regularToLogSheaf_comp_logToOpenSheaf]
    exact (regularPullback_openFormsPullback F (n + 1)).symm
  · simp only [normalFormPullback, biprod.inr_desc_assoc, inr_logNormalFormSheaf_assoc]
    rw [Category.assoc, ← Functor.map_comp, add_comp, Category.assoc, Category.assoc,
      regularToLogSheaf_comp_logToOpenSheaf, logMkSheaf_comp_logToOpenSheaf,
      inr_logNormalFormSheaf]
    exact (thetaNormalFormPullback F u hu n).symm

private lemma normalFormPullback_kernel (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    kernel.ι (logMkSheaf Q n) ≫ normalFormPullback F u n = 0 := by
  apply (cancel_mono ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
    (logToOpenSheaf P (n + 1)))).1
  rw [zero_comp, Category.assoc, normalFormPullback_inclusion F u hu,
    ← logMkSheaf_comp_logToOpenSheaf, ← Category.assoc, ← Category.assoc,
    kernel.condition, zero_comp, zero_comp]

private def logSheafPullbackAux (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) : (n : ℕ) →
    (logSheaf Q n ⟶ (TopCat.Sheaf.pushforward (ModuleCat k)
      F.ambient.hom.left.base).obj (logSheaf P n))
  | 0 => by
    have : IsIso (regularToLogSheaf Q 0) := isIso_of_mono_of_epi _
    exact inv (regularToLogSheaf Q 0) ≫ formsSheafPullback F.ambient.hom 0 ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
        (regularToLogSheaf P 0)
  | n + 1 => Abelian.epiDesc (logMkSheaf Q n) (normalFormPullback F u n)
      (normalFormPullback_kernel F u hu n)

/-- Pullback of logarithmic forms along an arbitrary transverse morphism of principal pairs.
It is the unique map compatible with ordinary pullback on the complement. -/
@[no_expose] def logSheafPullback (F : P ⟶ Q) (n : ℕ) :
    logSheaf Q n ⟶ (TopCat.Sheaf.pushforward (ModuleCat k)
      F.ambient.hom.left.base).obj (logSheaf P n) :=
  logSheafPullbackAux F F.exists_unit_mul.choose F.exists_unit_mul.choose_spec n

private lemma logSheafPullbackAux_inclusion (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    logSheafPullbackAux F u hu n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logToOpenSheaf P n) =
      logToOpenSheaf Q n ≫ openFormsPullback F n := by
  cases n with
  | zero =>
    have : IsIso (regularToLogSheaf Q 0) := isIso_of_mono_of_epi _
    apply (cancel_epi (regularToLogSheaf Q 0)).1
    dsimp only [logSheafPullbackAux]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp, regularToLogSheaf_comp_logToOpenSheaf,
      ← Category.assoc, regularToLogSheaf_comp_logToOpenSheaf]
    exact (regularPullback_openFormsPullback F 0).symm
  | succ n =>
    apply (cancel_epi (logMkSheaf Q n)).1
    dsimp only [logSheafPullbackAux]
    rw [← Category.assoc, Abelian.comp_epiDesc, ← Category.assoc,
      logMkSheaf_comp_logToOpenSheaf]
    exact normalFormPullback_inclusion F u hu n

/-- Logarithmic pullback is characterized by its ordinary complement inclusion. -/
@[reassoc (attr := simp)] theorem logSheafPullback_inclusion (F : P ⟶ Q) (n : ℕ) :
    logSheafPullback F n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logToOpenSheaf P n) =
      logToOpenSheaf Q n ≫ openFormsPullback F n :=
  logSheafPullbackAux_inclusion F F.exists_unit_mul.choose F.exists_unit_mul.choose_spec n

/-- The complement inclusion uniquely determines logarithmic pullback. -/
theorem logSheafPullback_unique (F : P ⟶ Q) (n : ℕ)
    (f : logSheaf Q n ⟶ (TopCat.Sheaf.pushforward (ModuleCat k)
      F.ambient.hom.left.base).obj (logSheaf P n))
    (hf : f ≫ (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
      (logToOpenSheaf P n) = logToOpenSheaf Q n ≫ openFormsPullback F n) :
    f = logSheafPullback F n :=
  (cancel_mono ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
    (logToOpenSheaf P n))).1 (hf.trans (logSheafPullback_inclusion F n).symm)

/-- Pullback commutes with the regular-form inclusion. -/
@[reassoc (attr := simp)] theorem regularToLogSheaf_pullback (F : P ⟶ Q) (n : ℕ) :
    regularToLogSheaf Q n ≫ logSheafPullback F n =
      formsSheafPullback F.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (regularToLogSheaf P n) := by
  apply (cancel_mono ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
    (logToOpenSheaf P n))).1
  rw [Category.assoc, logSheafPullback_inclusion, ← Category.assoc,
    regularToLogSheaf_comp_logToOpenSheaf, Category.assoc,
    ← Functor.map_comp, regularToLogSheaf_comp_logToOpenSheaf]
  exact regularPullback_openFormsPullback F n

private def pairClosedPushforwardIso (F : P ⟶ Q) :
    TopCat.Sheaf.pushforward (ModuleCat k) F.closed.hom.left.base ⋙
        TopCat.Sheaf.pushforward (ModuleCat k) Q.i.hom.left.base ≅
      TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base ⋙
        TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base := by
  apply eqToIso
  exact congrArg (TopCat.Sheaf.pushforward (ModuleCat k))
    (congrArg (fun f => f.hom.left.base) F.i_comp).symm

/-- Pullback of divisor forms along the closed square of a transverse pair morphism. -/
@[no_expose] def closedFormsPullback (F : P ⟶ Q) (n : ℕ) :
    closedFormsSheaf Q n ⟶
      (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).obj (closedFormsSheaf P n) :=
  (TopCat.Sheaf.pushforward (ModuleCat k) Q.i.hom.left.base).map
    (formsSheafPullback F.closed.hom n) ≫
      (pairClosedPushforwardIso F).hom.app (formsSheaf k P.closed.obj n)

/-- Restriction to the divisor commutes with the closed square of a transverse morphism. -/
@[reassoc] theorem regularPullback_closedFormsPullback (F : P ⟶ Q) (n : ℕ) :
    formsSheafPullback Q.i.hom n ≫ closedFormsPullback F n =
      formsSheafPullback F.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (formsSheafPullback P.i.hom n) := by
  dsimp only [closedFormsPullback]
  rw [← Category.assoc, ← formsSheafPullback_comp]
  have h : F.closed.hom ≫ Q.i.hom = P.i.hom ≫ F.ambient.hom :=
    (congrArg (fun f => f.hom) F.i_comp).symm
  have hc : (pairClosedPushforwardIso F).hom.app (formsSheaf k P.closed.obj n) =
      eqToHom (congrArg
        (fun t : P.closed.obj ⟶ Q.ambient.obj =>
          (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
            (formsSheaf k P.closed.obj n)) h) := by
    dsimp only [pairClosedPushforwardIso, eqToIso]
    exact eqToHom_app _ _
  rw [hc]
  have hcongr (f g : P.closed.obj ⟶ Q.ambient.obj) (hfg : f = g) :
      formsSheafPullback f n ≫ eqToHom (congrArg
        (fun t : P.closed.obj ⟶ Q.ambient.obj =>
          (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
            (formsSheaf k P.closed.obj n)) hfg) = formsSheafPullback g n := by
    subst g
    simp only [eqToHom_refl, Category.comp_id]
  exact (hcongr _ _ h).trans (formsSheafPullback_comp P.i.hom F.ambient.hom n)

private lemma logMkSheaf_pullback_normal (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    logMkSheaf Q n ≫ logSheafPullback F (n + 1) = normalFormPullback F u n := by
  apply (cancel_mono ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
    (logToOpenSheaf P (n + 1)))).1
  rw [Category.assoc, logSheafPullback_inclusion, ← Category.assoc,
    logMkSheaf_comp_logToOpenSheaf]
  exact (normalFormPullback_inclusion F u hu n).symm

/-- Pullback of logarithmic forms commutes with residue for every transverse morphism. -/
@[reassoc (attr := simp)] theorem logSheafPullback_residue (F : P ⟶ Q) (n : ℕ) :
    logSheafPullback F (n + 1) ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logResidueSheaf P n) =
      logResidueSheaf Q n ≫ closedFormsPullback F n := by
  obtain ⟨u, hu⟩ := F.exists_unit_mul
  apply (cancel_epi (logMkSheaf Q n)).1
  rw [← Category.assoc, logMkSheaf_pullback_normal F u hu, ← Category.assoc,
    logMkSheaf_residue]
  apply biprod.hom_ext'
  · simp only [normalFormPullback, biprod.inl_desc_assoc, Category.assoc,
      biprod.inl_snd_assoc, zero_comp]
    rw [← Functor.map_comp, regularToLogSheaf_residue, Functor.map_zero, comp_zero]
  · simp only [normalFormPullback, biprod.inr_desc_assoc, Category.assoc,
      biprod.inr_snd_assoc]
    rw [← Functor.map_comp, add_comp]
    simp only [Category.assoc, regularToLogSheaf_residue, comp_zero, zero_add,
      logMkSheaf_residue, biprod.inr_snd_assoc]
    exact (regularPullback_closedFormsPullback F n).symm

/-- Complement pullback commutes with the ordinary de Rham differential. -/
@[reassoc] theorem openFormsPullback_d (F : P ⟶ Q) (n : ℕ) :
    openFormsPullback F n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          ((TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
            (formsSheafD k P.compl.obj n)) =
      (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
          (formsSheafD k Q.compl.obj n) ≫ openFormsPullback F (n + 1) := by
  rw [openFormsPullback_eq, openFormsPullback_eq]
  symm
  rw [← Category.assoc, ← Functor.map_comp, ← formsSheafPullback_d,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg
    (fun f ↦ (TopCat.Sheaf.pushforward (ModuleCat k) Q.j.hom.left.base).map
      (formsSheafPullback F.compl.hom n) ≫ f)
    ((pairOpenPushforwardIso F).hom.naturality (formsSheafD k P.compl.obj n))

/-- Pullback on logarithmic forms commutes with the base-linear differential. -/
@[reassoc] theorem logSheafPullback_d (F : P ⟶ Q) (n : ℕ) :
    logSheafPullback F n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logSheafD P n) =
      logSheafD Q n ≫ logSheafPullback F (n + 1) := by
  apply (cancel_mono ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
    (logToOpenSheaf P (n + 1)))).1
  rw [Category.assoc, ← Functor.map_comp, logSheafD_comp_logToOpenSheaf,
    Functor.map_comp, ← Category.assoc, logSheafPullback_inclusion, Category.assoc,
    openFormsPullback_d, ← Category.assoc, ← logSheafD_comp_logToOpenSheaf]
  simp only [Category.assoc, logSheafPullback_inclusion]

/-- Pullback of logarithmic complexes along a transverse morphism of geometric pairs. -/
def logComplexNatPullback (F : P ⟶ Q) : logComplexNat Q ⟶
    ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).mapHomologicalComplex
      (.up ℕ)).obj (logComplexNat P) where
  f n := logSheafPullback F n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact logSheafPullback_d F i

/-- The component of logarithmic complex pullback is the corresponding sheaf pullback. -/
@[simp] theorem logComplexNatPullback_f (F : P ⟶ Q) (n : ℕ) :
    (logComplexNatPullback F).f n = logSheafPullback F n := rfl

/-- The identity pair map acts identically on complement forms. -/
@[simp] theorem openFormsPullback_id (P : DivisorPair D) (n : ℕ) :
    openFormsPullback (𝟙 P) n = 𝟙 (openFormsSheaf P n) := by
  rw [openFormsPullback_eq]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (formsSheafPullback (𝟙 P.compl.obj) n) ≫ _ = _
  rw [formsSheafPullback_id]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (𝟙 (formsSheaf k P.compl.obj n)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  change 𝟙 (openFormsSheaf P n) ≫ 𝟙 (openFormsSheaf P n) = 𝟙 (openFormsSheaf P n)
  exact Category.id_comp _

/-- The identity pair map acts identically on logarithmic forms. -/
@[simp] theorem logSheafPullback_id (P : DivisorPair D) (n : ℕ) :
    logSheafPullback (𝟙 P) n = 𝟙 (logSheaf P n) := by
  apply (cancel_mono (logToOpenSheaf P n)).1
  change logSheafPullback (𝟙 P) n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) ((𝟙 P : P ⟶ P).ambient.hom.left.base)).map
        (logToOpenSheaf P n) = _
  rw [logSheafPullback_inclusion, openFormsPullback_id]
  change logToOpenSheaf P n ≫ 𝟙 (openFormsSheaf P n) =
    𝟙 (logSheaf P n) ≫ logToOpenSheaf P n
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {R : DivisorPair D}

-- Composition of direct images and direct image along the composite have the same presheaf.
-- The displayed functor objects must be compared beyond implicit transparency.
set_option backward.isDefEq.respectTransparency false in
private lemma pairOpenPushforwardIso_comp (F : P ⟶ Q) (G : Q ⟶ R) (n : ℕ) :
    (pairOpenPushforwardIso (F ≫ G)).hom.app (formsSheaf k P.compl.obj n) =
      (pairOpenPushforwardIso G).hom.app
          ((TopCat.Sheaf.pushforward (ModuleCat k) F.compl.hom.left.base).obj
            (formsSheaf k P.compl.obj n)) ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
          ((pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)) := by
  dsimp only [pairOpenPushforwardIso, eqToIso]
  rw [eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_map, eqToHom_trans]

-- Normalize the two presentations of the composite direct-image target.
set_option backward.isDefEq.respectTransparency false in
/-- Complement-form pullback is contravariantly compatible with composition of pair maps. -/
theorem openFormsPullback_comp (F : P ⟶ Q) (G : Q ⟶ R) (n : ℕ) :
    openFormsPullback (F ≫ G) n = openFormsPullback G n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
        (openFormsPullback F n) := by
  rw [openFormsPullback_eq, openFormsPullback_eq, openFormsPullback_eq]
  change (TopCat.Sheaf.pushforward (ModuleCat k) R.j.hom.left.base).map
    (formsSheafPullback (F.compl.hom ≫ G.compl.hom) n) ≫ _ = _
  rw [formsSheafPullback_comp, Functor.map_comp, Functor.map_comp,
    pairOpenPushforwardIso_comp]
  simpa only [Category.assoc, CategoryTheory.Functor.comp_map] using congrArg
    (fun h ↦ (TopCat.Sheaf.pushforward (ModuleCat k) R.j.hom.left.base).map
        (formsSheafPullback G.compl.hom n) ≫ h ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
        ((pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)))
    ((pairOpenPushforwardIso G).hom.naturality (formsSheafPullback F.compl.hom n))

-- Normalize the two presentations of the composite direct-image target.
set_option backward.isDefEq.respectTransparency false in
/-- Logarithmic pullback is contravariantly compatible with composition of transverse maps. -/
theorem logSheafPullback_comp (F : P ⟶ Q) (G : Q ⟶ R) (n : ℕ) :
    logSheafPullback (F ≫ G) n = logSheafPullback G n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
        (logSheafPullback F n) := by
  apply (cancel_mono
    ((TopCat.Sheaf.pushforward (ModuleCat k) (F ≫ G).ambient.hom.left.base).map
      (logToOpenSheaf P n))).1
  change logSheafPullback (F ≫ G) n ≫ _ =
    (logSheafPullback G n ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
        (logSheafPullback F n)) ≫
      (TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).map
        ((TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (logToOpenSheaf P n))
  rw [logSheafPullback_inclusion, Category.assoc, ← Functor.map_comp,
    logSheafPullback_inclusion, Functor.map_comp, ← Category.assoc,
    logSheafPullback_inclusion, Category.assoc, openFormsPullback_comp]

/-- The identity pair map acts identically on logarithmic complexes. -/
@[simp] theorem logComplexNatPullback_id (P : DivisorPair D) :
    logComplexNatPullback (𝟙 P) = 𝟙 (logComplexNat P) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact logSheafPullback_id P n

/-- Pullback on logarithmic complexes is contravariantly compatible with composition. -/
theorem logComplexNatPullback_comp (F : P ⟶ Q) (G : Q ⟶ R) :
    logComplexNatPullback (F ≫ G) = logComplexNatPullback G ≫
      ((TopCat.Sheaf.pushforward (ModuleCat k) G.ambient.hom.left.base).mapHomologicalComplex
        (.up ℕ)).map (logComplexNatPullback F) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact logSheafPullback_comp F G n

/-- Logarithmic sections on the inverse image of an ambient open under a pair morphism.
This named module keeps the inverse-image carrier stable under simplification of the
projections of an identity morphism. It is definitionally the usual section module and
is transparent to instance search for arithmetic with ordinary sections on the same open. -/
@[instance_reducible] def logSheafPullbackSections (F : P ⟶ Q) (n : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ) :
    ModuleCat k :=
  (logSheaf P n).obj.obj (op (F.ambient.hom.left ⁻¹ᵁ U.unop))

/-- Pullback on an individual ambient open, with its inverse-image section module named
by `logSheafPullbackSections` so that identity reindexing is stable under simplification. -/
def logSheafPullbackAt (F : P ⟶ Q) (n : ℕ) (U : Q.ambient.obj.left.Opensᵒᵖ) :
    (logSheaf Q n).obj.obj U →ₗ[k] logSheafPullbackSections F n U :=
  ((logSheafPullback F n).hom.app U).hom

/-- On sections, logarithmic pullback includes as ordinary complement pullback. -/
@[simp] theorem logSheafPullbackAt_inclusion (F : P ⟶ Q) (n : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ) (a : (logSheaf Q n).obj.obj U) :
    (logToOpenSheaf P n).hom.app (op (F.ambient.hom.left ⁻¹ᵁ U.unop))
        (logSheafPullbackAt F n U a) =
      (openFormsPullback F n).hom.app U ((logToOpenSheaf Q n).hom.app U a) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_inclusion F n)) U) a

private lemma pairOpenPreimage_eq (F : P ⟶ Q) (U : Q.ambient.obj.left.Opens) :
    P.j.hom.left ⁻¹ᵁ (F.ambient.hom.left ⁻¹ᵁ U) =
      F.compl.hom.left ⁻¹ᵁ (Q.j.hom.left ⁻¹ᵁ U) :=
  congrArg (fun f => f.hom.left ⁻¹ᵁ U) F.j_comp

-- Evaluation identifies the canonical direct-image comparison with transport of an open.
set_option backward.isDefEq.respectTransparency false in
private lemma pairOpenPushforwardIso_app (F : P ⟶ Q) (n : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ) :
    ((pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)).hom.app U =
      (formsSheaf k P.compl.obj n).obj.map (eqToHom (pairOpenPreimage_eq F U.unop)).op := by
  let E := sheafToPresheaf (_root_.Opens.grothendieckTopology Q.ambient.obj.left)
    (ModuleCat.{u} k) ⋙ (evaluation _ _).obj U
  change E.map ((pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)) = _
  dsimp only [pairOpenPushforwardIso, eqToIso]
  rw [eqToHom_app, eqToHom_map, eqToHom_op, eqToHom_map]

private lemma openFormsPullback_apply (F : P ⟶ Q) (n : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k Q.compl.obj n).obj.obj (op (Q.j.hom.left ⁻¹ᵁ U.unop))) :
    (openFormsPullback F n).hom.app U a =
      (formsSheaf k P.compl.obj n).obj.map (eqToHom (pairOpenPreimage_eq F U.unop)).op
        ((formsSheafPullback F.compl.hom n).hom.app (op (Q.j.hom.left ⁻¹ᵁ U.unop)) a) := by
  rw [openFormsPullback_eq]
  change ((pairOpenPushforwardIso F).hom.app (formsSheaf k P.compl.obj n)).hom.app U
    ((formsSheafPullback F.compl.hom n).hom.app (op (Q.j.hom.left ⁻¹ᵁ U.unop)) a) = _
  rw [pairOpenPushforwardIso_app]
  rfl

/-- Complement-form pullback preserves wedge products. -/
theorem openFormsPullback_wedge (F : P ⟶ Q) (p q : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ)
    (a : (formsSheaf k Q.compl.obj p).obj.obj (op (Q.j.hom.left ⁻¹ᵁ U.unop)))
    (b : (formsSheaf k Q.compl.obj q).obj.obj (op (Q.j.hom.left ⁻¹ᵁ U.unop))) :
    (openFormsPullback F (p + q)).hom.app U
        (formsSheafWedge k Q.compl.obj p q (op (Q.j.hom.left ⁻¹ᵁ U.unop)) a b) =
      formsSheafWedge k P.compl.obj p q
        (op (P.j.hom.left ⁻¹ᵁ (F.ambient.hom.left ⁻¹ᵁ U.unop)))
        ((openFormsPullback F p).hom.app U a) ((openFormsPullback F q).hom.app U b) := by
  rw [openFormsPullback_apply, formsSheafPullback_wedge,
    openFormsPullback_apply, openFormsPullback_apply]
  exact formsSheafWedge_naturality k P.compl.obj p q
    (eqToHom (pairOpenPreimage_eq F U.unop)).op _ _

/-- Transverse pullback preserves the wedge product of logarithmic forms. -/
@[simp] theorem logSheafPullbackAt_wedge (F : P ⟶ Q) (p q : ℕ)
    (U : Q.ambient.obj.left.Opensᵒᵖ)
    (a : (logSheaf Q p).obj.obj U) (b : (logSheaf Q q).obj.obj U) :
    logSheafPullbackAt F (p + q) U (logSheafWedge Q p q U a b) =
      logSheafWedge P p q (op (F.ambient.hom.left ⁻¹ᵁ U.unop))
        (logSheafPullbackAt F p U a) (logSheafPullbackAt F q U b) := by
  apply logToOpenSheaf_app_injective
  rw [logSheafPullbackAt_inclusion, logSheafWedge_logToOpenSheaf,
    logSheafWedge_logToOpenSheaf, logSheafPullbackAt_inclusion, logSheafPullbackAt_inclusion]
  exact openFormsPullback_wedge F p q U _ _

/-- Transverse pullback preserves the unit logarithmic form. -/
@[simp] theorem logSheafPullbackAt_one (F : P ⟶ Q)
    (U : Q.ambient.obj.left.Opensᵒᵖ) :
    logSheafPullbackAt F 0 U (logSheafOneSection Q U) =
      logSheafOneSection P (op (F.ambient.hom.left ⁻¹ᵁ U.unop)) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (regularToLogSheaf_pullback F 0)) U)
      (formsSheafOneSection k Q.ambient.obj U)
  change logSheafPullbackAt F 0 U (logSheafOneSection Q U) =
    (regularToLogSheaf P 0).hom.app (op (F.ambient.hom.left ⁻¹ᵁ U.unop))
      ((formsSheafPullback F.ambient.hom 0).hom.app U
        (formsSheafOneSection k Q.ambient.obj U)) at h
  exact h.trans (congrArg
    ((regularToLogSheaf P 0).hom.app (op (F.ambient.hom.left ⁻¹ᵁ U.unop)))
      (formsSheafPullback_one F.ambient.hom U))

/-- The logarithmic generator pulls back with the regular correction from the equation unit. -/
@[reassoc] theorem thetaToLogSheaf_pullback (F : P ⟶ Q)
    (u : Γ(P.ambient.obj.left, ⊤)ˣ)
    (hu : F.ambient.hom.left.appTop Q.eqn = u * P.eqn) (n : ℕ) :
    thetaToLogSheaf Q n ≫ logSheafPullback F (n + 1) =
      formsSheafPullback F.ambient.hom n ≫
        (TopCat.Sheaf.pushforward (ModuleCat k) F.ambient.hom.left.base).map
          (thetaWedgeSheaf P.ambient.obj
              (show (sectionAlgebra k P.ambient.obj ⊤)ˣ from u) n ≫
              regularToLogSheaf P (n + 1) + thetaToLogSheaf P n) := by
  change (biprod.inr ≫ logMkSheaf Q n) ≫ logSheafPullback F (n + 1) = _
  rw [Category.assoc, logMkSheaf_pullback_normal F u hu, normalFormPullback, biprod.inr_desc]
  rfl

private lemma openFormsPullback_withEqn_hom (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    openFormsPullback (P.withEqnIso f hf).hom n = 𝟙 (openFormsSheaf P n) := by
  rw [openFormsPullback_eq]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (formsSheafPullback (𝟙 P.compl.obj) n) ≫ _ = _
  rw [formsSheafPullback_id]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (𝟙 (formsSheaf k P.compl.obj n)) ≫ 𝟙 (openFormsSheaf P n) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

private lemma openFormsPullback_withEqn_inv (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    openFormsPullback (P.withEqnIso f hf).inv n = 𝟙 (openFormsSheaf P n) := by
  rw [openFormsPullback_eq]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (formsSheafPullback (𝟙 P.compl.obj) n) ≫ _ = _
  rw [formsSheafPullback_id]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.j.hom.left.base).map
    (𝟙 (formsSheaf k P.compl.obj n)) ≫ 𝟙 (openFormsSheaf P n) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

private def withEqnLogHom (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    logSheaf P n ⟶ logSheaf (P.withEqn f hf) n :=
  logSheafPullback (P.withEqnIso f hf).hom n

private def withEqnLogInv (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    logSheaf (P.withEqn f hf) n ⟶ logSheaf P n :=
  logSheafPullback (P.withEqnIso f hf).inv n

private lemma withEqn_pullback_hom_inclusion (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    withEqnLogHom P f hf n ≫ logToOpenSheaf (P.withEqn f hf) n =
      logToOpenSheaf P n := by
  have h := logSheafPullback_inclusion (P.withEqnIso f hf).hom n
  change logSheafPullback (P.withEqnIso f hf).hom n ≫
    logToOpenSheaf (P.withEqn f hf) n =
      logToOpenSheaf P n ≫ openFormsPullback (P.withEqnIso f hf).hom n at h
  exact h.trans (by
    rw [openFormsPullback_withEqn_hom]
    exact Category.comp_id _)

private lemma withEqn_pullback_inv_inclusion (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    withEqnLogInv P f hf n ≫ logToOpenSheaf P n =
      logToOpenSheaf (P.withEqn f hf) n := by
  have h := logSheafPullback_inclusion (P.withEqnIso f hf).inv n
  change logSheafPullback (P.withEqnIso f hf).inv n ≫ logToOpenSheaf P n =
    logToOpenSheaf (P.withEqn f hf) n ≫ openFormsPullback (P.withEqnIso f hf).inv n at h
  exact h.trans (by
    rw [openFormsPullback_withEqn_inv]
    exact Category.comp_id _)

/-- Replacing the equation by an associated global equation preserves logarithmic forms. -/
@[no_expose] def logSheafWithEqnIso (P : DivisorPair D) (f : Γ(P.ambient.obj.left, ⊤))
    (hf : Associated f P.eqn) (n : ℕ) : logSheaf (P.withEqn f hf) n ≅ logSheaf P n where
  hom := withEqnLogInv P f hf n
  inv := withEqnLogHom P f hf n
  hom_inv_id := by
    apply (cancel_mono (logToOpenSheaf (P.withEqn f hf) n)).1
    rw [Category.assoc, withEqn_pullback_hom_inclusion,
      withEqn_pullback_inv_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (logToOpenSheaf P n)).1
    rw [Category.assoc, withEqn_pullback_inv_inclusion,
      withEqn_pullback_hom_inclusion, Category.id_comp]

/-- The change-of-equation comparison preserves the actual complement inclusion. -/
@[reassoc (attr := simp)] theorem logSheafWithEqnIso_hom_inclusion (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    (logSheafWithEqnIso P f hf n).hom ≫ logToOpenSheaf P n =
      logToOpenSheaf (P.withEqn f hf) n := withEqn_pullback_inv_inclusion P f hf n

/-- Change of associated equation preserves regular forms. -/
@[reassoc (attr := simp)] theorem logSheafWithEqnIso_hom_regular (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    regularToLogSheaf (P.withEqn f hf) n ≫ (logSheafWithEqnIso P f hf n).hom =
      regularToLogSheaf P n := by
  have h := regularToLogSheaf_pullback (P.withEqnIso f hf).inv n
  change regularToLogSheaf (P.withEqn f hf) n ≫ (logSheafWithEqnIso P f hf n).hom =
    formsSheafPullback (𝟙 P.ambient.obj) n ≫ regularToLogSheaf P n at h
  exact h.trans (by
    rw [formsSheafPullback_id]
    change 𝟙 (formsSheaf k P.ambient.obj n) ≫ regularToLogSheaf P n = _
    exact Category.id_comp _)

private lemma closedFormsPullback_withEqn_inv (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    closedFormsPullback (P.withEqnIso f hf).inv n = 𝟙 (closedFormsSheaf P n) := by
  dsimp only [closedFormsPullback]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
    (formsSheafPullback (𝟙 P.closed.obj) n) ≫ _ = _
  rw [formsSheafPullback_id]
  change (TopCat.Sheaf.pushforward (ModuleCat k) P.i.hom.left.base).map
    (𝟙 (formsSheaf k P.closed.obj n)) ≫ 𝟙 (closedFormsSheaf P n) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- Residue is invariant under replacing the equation by an associated equation. -/
@[reassoc (attr := simp)] theorem logSheafWithEqnIso_hom_residue (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    (logSheafWithEqnIso P f hf (n + 1)).hom ≫ logResidueSheaf P n =
      logResidueSheaf (P.withEqn f hf) n := by
  have h := logSheafPullback_residue (P.withEqnIso f hf).inv n
  change (logSheafWithEqnIso P f hf (n + 1)).hom ≫ logResidueSheaf P n =
    logResidueSheaf (P.withEqn f hf) n ≫ closedFormsPullback (P.withEqnIso f hf).inv n at h
  exact h.trans (by
    rw [closedFormsPullback_withEqn_inv]
    change logResidueSheaf (P.withEqn f hf) n ≫ 𝟙 (closedFormsSheaf P n) = _
    exact Category.comp_id _)

/-- Change of associated equation commutes with the logarithmic differential. -/
@[reassoc] theorem logSheafWithEqnIso_hom_d (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    (logSheafWithEqnIso P f hf n).hom ≫ logSheafD P n =
      logSheafD (P.withEqn f hf) n ≫ (logSheafWithEqnIso P f hf (n + 1)).hom :=
  logSheafPullback_d (P.withEqnIso f hf).inv n

/-- Associated equations give canonically isomorphic logarithmic complexes. -/
@[no_expose] def logComplexNatWithEqnIso (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) :
    logComplexNat (P.withEqn f hf) ≅ logComplexNat P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => logSheafWithEqnIso P f hf n)
    (by
      intro n m hnm
      obtain rfl : n + 1 = m := hnm
      exact logSheafWithEqnIso_hom_d P f hf n)

/-- The complex comparison for associated equations has the corresponding sheaf comparison. -/
@[simp] theorem logComplexNatWithEqnIso_hom_f (P : DivisorPair D)
    (f : Γ(P.ambient.obj.left, ⊤)) (hf : Associated f P.eqn) (n : ℕ) :
    (logComplexNatWithEqnIso P f hf).hom.f n = (logSheafWithEqnIso P f hf n).hom := by rfl

/-- Pullback of global logarithmic forms on the displayed top-open section carriers. -/
def logSheafPullbackTop (F : P ⟶ Q) (n : ℕ) :
    (logSheaf Q n).obj.obj (op ⊤) →ₗ[k] (logSheaf P n).obj.obj (op ⊤) :=
  ((logSheafPullback F n).hom.app (op ⊤)).hom

/-- The typed global pullback is the evaluation of sheaf pullback on the top open. -/
@[simp] theorem logSheafPullback_app_top (F : P ⟶ Q) (n : ℕ)
    (a : (logSheaf Q n).obj.obj (op ⊤)) :
    dsimp% (logSheafPullback F n).hom.app (op ⊤) a = logSheafPullbackTop F n a := rfl

/-- Identity acts identically on global logarithmic forms. -/
@[simp] theorem logSheafPullbackTop_id (P : DivisorPair D) (n : ℕ) :
    logSheafPullbackTop (𝟙 P) n = LinearMap.id := by
  ext a
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_id P n)) (op ⊤)) a

/-- Pullback of global logarithmic forms is contravariantly functorial. -/
theorem logSheafPullbackTop_comp (F : P ⟶ Q) (G : Q ⟶ R) (n : ℕ) :
    logSheafPullbackTop (F ≫ G) n =
      (logSheafPullbackTop F n).comp (logSheafPullbackTop G n) := by
  ext a
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_comp F G n)) (op ⊤)) a

/-- Global logarithmic pullback preserves wedge products. -/
@[simp] theorem logSheafPullbackTop_wedge (F : P ⟶ Q) (p q : ℕ)
    (a : (logSheaf Q p).obj.obj (op ⊤)) (b : (logSheaf Q q).obj.obj (op ⊤)) :
    logSheafPullbackTop F (p + q) (logSheafWedge Q p q (op ⊤) a b) =
      logSheafWedge P p q (op ⊤) (logSheafPullbackTop F p a) (logSheafPullbackTop F q b) :=
  logSheafPullbackAt_wedge F p q (op ⊤) a b

/-- Global logarithmic pullback preserves the unit. -/
@[simp] theorem logSheafPullbackTop_one (F : P ⟶ Q) :
    logSheafPullbackTop F 0 (logSheafOneSection Q (op ⊤)) = logSheafOneSection P (op ⊤) :=
  logSheafPullbackAt_one F (op ⊤)

/-- Global logarithmic pullback commutes with the differential. -/
theorem logSheafPullbackTop_d (F : P ⟶ Q) (n : ℕ)
    (a : (logSheaf Q n).obj.obj (op ⊤)) :
    (logSheafD P n).hom.app (op ⊤) (logSheafPullbackTop F n a) =
      logSheafPullbackTop F (n + 1) ((logSheafD Q n).hom.app (op ⊤) a) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_d F n)) (op ⊤)) a

/-- On global sections, closed-form pullback is ordinary pullback on the divisor. -/
theorem closedFormsPullback_app_top (F : P ⟶ Q) (n : ℕ)
    (a : (formsSheaf k Q.closed.obj n).obj.obj (op ⊤)) :
    dsimp% (closedFormsPullback F n).hom.app (op ⊤) a =
      formsSheafPullbackTop F.closed.hom n a := by
  dsimp only [closedFormsPullback]
  let E := sheafToPresheaf (_root_.Opens.grothendieckTopology Q.ambient.obj.left)
    (ModuleCat.{u} k) ⋙ (evaluation _ _).obj (op ⊤)
  have he : F.closed.hom ≫ Q.i.hom = P.i.hom ≫ F.ambient.hom :=
    (congrArg (fun f => f.hom) F.i_comp).symm
  have hc : (pairClosedPushforwardIso F).hom.app (formsSheaf k P.closed.obj n) =
      eqToHom (congrArg
        (fun t : P.closed.obj ⟶ Q.ambient.obj =>
          (TopCat.Sheaf.pushforward (ModuleCat k) t.left.base).obj
            (formsSheaf k P.closed.obj n)) he) := by
    dsimp only [pairClosedPushforwardIso, eqToIso]
    exact eqToHom_app _ _
  have h : E.map ((pairClosedPushforwardIso F).hom.app (formsSheaf k P.closed.obj n)) =
      𝟙 ((formsSheaf k P.closed.obj n).obj.obj (op ⊤)) := by
    rw [hc]
    exact (eqToHom_map E _).trans (by rfl)
  exact ConcreteCategory.congr_hom h (formsSheafPullbackTop F.closed.hom n a)

/-- Global residue with its divisor section carrier explicit. -/
def logResidueSheafTop (P : DivisorPair D) (n : ℕ) :
    (logSheaf P (n + 1)).obj.obj (op ⊤) →ₗ[k]
      (formsSheaf k P.closed.obj n).obj.obj (op ⊤) :=
  ((logResidueSheaf P n).hom.app (op ⊤)).hom

/-- The typed global residue is residue evaluated on the top open. -/
@[simp] theorem logResidueSheaf_app_top (P : DivisorPair D) (n : ℕ)
    (a : (logSheaf P (n + 1)).obj.obj (op ⊤)) :
    dsimp% (logResidueSheaf P n).hom.app (op ⊤) a = logResidueSheafTop P n a := rfl

/-- Global logarithmic pullback commutes with the typed global residue. -/
theorem logSheafPullbackTop_residue (F : P ⟶ Q) (n : ℕ)
    (a : (logSheaf Q (n + 1)).obj.obj (op ⊤)) :
    logResidueSheafTop P n (logSheafPullbackTop F (n + 1) a) =
      formsSheafPullbackTop F.closed.hom n (logResidueSheafTop Q n a) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafPullback_residue F n)) (op ⊤)) a
  exact h.trans (closedFormsPullback_app_top F n _)

end OrlikSolomon.Geometric.DeRham
