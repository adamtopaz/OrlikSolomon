/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Log.Naturality

/-!
# Affine comparison of the logarithmic residue sequence

For an affine geometric pair, actual global sections of its sheaf residue sequence identify
with the old algebraic logarithmic sequence of its section-ring pair. The divisor comparison
is zero in degree zero and `globalFormsEquiv` in degree `n + 1`, with differential `-d`.
Residue is checked on regular-plus-left-theta representatives. These comparisons supply the
representative equations `ρ(l) = γ` and `regular(ω) = d(l)` for the affine residue and Gysin maps.
All results use a commutative base ring; short exactness of global sections for affine pairs
follows from the algebraic comparison.

## Main results

* `logResidueSheafTop_surjective` and `exact_regularToLogTop_logResidueSheafTop`: global lifts
  and exactness on affine pairs, including the regular differential of a closed-residue lift.
* `affineLogComparison_residue`: compatibility with actual sheaf residue, without another sign.
* `affineShiftedClosedComplexIso`: compatibility with the explicitly signed divisor shift.
* `affineLogResidueShortComplexIso`: comparison with the actual global sheaf short complex.
* `affineLogComparison_global_gysin_representative_iff`: equivalence of the global sheaf and
  old algebraic lift-and-differential data, with the positive `d(l)` convention.

Blueprint: `thm:geo-log-sheaves`, supplying representative comparisons for `thm:geo-dr-instance`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite AlgebraicGeometry
open scoped ZeroObject
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k]

/-- Algebraic pullback preserves left multiplication by the logarithmic form of a unit. -/
lemma leftDlogPower_map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (v : Aˣ) (n : ℕ)
    (a : ⋀[A]^n Ω[A⁄k]) :
    Forms.mapPower φ (n + 1) (leftDlogPower v n a) =
      leftDlogPower (Units.map φ.toMonoidHom v) n (Forms.mapPower φ n a) := by
  apply Subtype.ext
  change Forms.map φ (dlog k v * a.val) =
    dlog k (Units.map φ.toMonoidHom v) * Forms.map φ a.val
  rw [map_mul, Forms.map_dlog]
  rfl

-- The affine comparison passes between exterior-power and sheaf section carriers.
set_option backward.isDefEq.respectTransparency false in
/-- The affine global forms comparison preserves left logarithmic multiplication. -/
lemma globalFormsEquiv_leftDlogPower
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (v : (globalSections X)ˣ) (n : ℕ)
    (a : ⋀[globalSections X]^n Ω[globalSections X⁄k]) :
    (thetaWedgeSheaf X (Units.map (globalSectionsAlgEquiv X).toAlgHom.toMonoidHom v) n).hom.app
        (op ⊤) (globalFormsEquiv X n a) =
      globalFormsEquiv X (n + 1) (leftDlogPower v n a) := by
  rw [globalFormsEquiv_apply, globalFormsEquiv_apply, leftDlogPower_map,
    affineFormsComparison_apply, affineFormsComparison_apply]
  let v' := Units.map (globalSectionsAlgEquiv X).toAlgHom.toMonoidHom v
  have hv : Units.map (sectionRestriction k X (⊤ : X.left.Opens).leTop).toMonoidHom v' = v' := by
    change Units.map (sectionRestriction k X (𝟙 ⊤)).toMonoidHom v' = v'
    rw [sectionRestriction_id]
    rfl
  have h := thetaWedgeSheaf_unit X v' n (op ⊤)
    (Forms.mapPower (globalSectionsAlgEquiv X).toAlgHom n a)
  simpa only [hv, leftDlogPower, v'] using h

variable {D : SmoothDomain k}

/-- Global sections of the divisor direct image, shifted up one degree with differential `-d`. -/
@[implicit_reducible] def globalShiftedClosedComplexNat (P : DivisorPair D) :
    CochainComplex (ModuleCat k) ℕ :=
  ((sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left) (ModuleCat k) ⋙
    (evaluation _ _).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).obj
      (shiftedClosedComplexNat P)

/-- Positive degrees of the global shifted divisor complex are global divisor forms. -/
@[simp] lemma globalShiftedClosedComplexNat_X_succ (P : DivisorPair D) (n : ℕ) :
    (globalShiftedClosedComplexNat P).X (n + 1) =
      (formsSheaf k P.closed.obj n).obj.obj (op ⊤) := rfl

/-- The positive differential of the global shifted divisor complex is the negative
sheaf differential. -/
lemma globalShiftedClosedComplexNat_d_succ (P : DivisorPair D) (n : ℕ) :
    (globalShiftedClosedComplexNat P).d (n + 1) (n + 1 + 1) =
      -(formsSheafD k P.closed.obj n).hom.app (op ⊤) := by
  change ((shiftedClosedComplexNat P).d (n + 1) (n + 1 + 1)).hom.app (op ⊤) = _
  rw [shiftedClosedComplexNat_d]
  rfl

/-- The actual global sections of the logarithmic residue short complex of sheaf complexes. -/
@[implicit_reducible] def globalLogResidueShortComplexNat (P : DivisorPair D) :
    ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  (logResidueShortComplexNat P).map
    ((sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left) (ModuleCat k) ⋙
      (evaluation _ _).obj (op ⊤)).mapHomologicalComplex (.up ℕ))

/-- Degree zero of the global shifted divisor complex is a zero object. -/
lemma globalShiftedClosedComplexNat_isZero_zero (P : DivisorPair D) :
    IsZero ((globalShiftedClosedComplexNat P).X 0) :=
  (sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left) (ModuleCat k) ⋙
    (evaluation _ _).obj (op ⊤)).map_isZero (isZero_zero _)

/-- The actual complement inclusion of a closed logarithmic section is closed. -/
lemma formsSheafD_logToOpenTop_eq_zero (P : DivisorPair D) {n : ℕ}
    {l : (logSheaf P n).obj.obj (op ⊤)}
    (hl : (logSheafD P n).hom.app (op ⊤) l = 0) :
    (formsSheafD k P.compl.obj n).hom.app (op ⊤) (logToOpenTop P n l) = 0 := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom)
      (logSheafD_comp_logToOpenSheaf P n)) (op ⊤)) l
  change logToOpenTop P (n + 1) ((logSheafD P n).hom.app (op ⊤) l) =
    (formsSheafD k P.compl.obj n).hom.app (op ⊤) (logToOpenTop P n l) at h
  exact h.symm.trans (by rw [hl, map_zero])

/-- The residue of a closed global logarithmic section is closed. -/
lemma formsSheafD_logResidueSheafTop_eq_zero (P : DivisorPair D) {n : ℕ}
    {l : (logSheaf P (n + 1)).obj.obj (op ⊤)}
    (hl : (logSheafD P (n + 1)).hom.app (op ⊤) l = 0) :
    (formsSheafD k P.closed.obj n).hom.app (op ⊤) (logResidueSheafTop P n l) = 0 := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logResidueSheaf_d P n)) (op ⊤)) l
  change logResidueSheafTop P (n + 1) ((logSheafD P (n + 1)).hom.app (op ⊤) l) =
    -((formsSheafD k P.closed.obj n).hom.app (op ⊤) (logResidueSheafTop P n l)) at h
  rw [hl, map_zero] at h
  exact neg_eq_zero.mp h.symm

/-- A regular form representing the differential of a global logarithmic section is closed. -/
lemma formsSheafD_eq_zero_of_regularToLogTop_eq_logSheafD (P : DivisorPair D) {n : ℕ}
    {l : (logSheaf P n).obj.obj (op ⊤)}
    {ω : (formsSheaf k P.ambient.obj (n + 1)).obj.obj (op ⊤)}
    (hω : regularToLogTop P (n + 1) ω = (logSheafD P n).hom.app (op ⊤) l) :
    (formsSheafD k P.ambient.obj (n + 1)).hom.app (op ⊤) ω = 0 := by
  have : Mono (regularToLogSheaf P (n + 1 + 1)).hom :=
    (sheafToPresheaf (_root_.Opens.grothendieckTopology P.ambient.obj.left)
      (ModuleCat k)).map_mono _
  have : Mono ((regularToLogSheaf P (n + 1 + 1)).hom.app (op ⊤)) :=
    ((evaluation _ _).obj (op ⊤)).map_mono _
  apply (ModuleCat.mono_iff_injective ((regularToLogSheaf P (n + 1 + 1)).hom.app (op ⊤))).1
    inferInstance
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (regularToLogSheaf_d P (n + 1))) (op ⊤)) ω
  change (logSheafD P (n + 1)).hom.app (op ⊤) (regularToLogTop P (n + 1) ω) =
    (regularToLogSheaf P (n + 1 + 1)).hom.app (op ⊤)
      ((formsSheafD k P.ambient.obj (n + 1)).hom.app (op ⊤) ω) at h
  rw [hω] at h
  have hdd := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logSheafD_comp P n)) (op ⊤)) l
  change (logSheafD P (n + 1)).hom.app (op ⊤)
    ((logSheafD P n).hom.app (op ⊤) l) = 0 at hdd
  simpa only [map_zero] using h.symm.trans hdd

variable (P : DivisorPair (SmoothDomain.aff k))

private def affineShiftedClosedComponentIso : (n : ℕ) →
    (shiftedComplex k P.globalSections.closed).X n ≅ (globalShiftedClosedComplexNat P).X n
  | 0 => (ModuleCat.isZero_of_subsingleton (ModuleCat.of k PUnit)).iso
      (globalShiftedClosedComplexNat_isZero_zero P)
  | n + 1 => (globalFormsEquiv P.closed.obj n).toModuleIso

/-- The algebraic divisor shift and the global shifted divisor sheaf complex are isomorphic.
Both differentials are `-d`, and the positive components are `globalFormsEquiv`. -/
@[no_expose] def affineShiftedClosedComplexIso :
    shiftedComplex k P.globalSections.closed ≅ globalShiftedClosedComplexNat P :=
  HomologicalComplex.Hom.isoOfComponents (affineShiftedClosedComponentIso P) (by
    rintro (_ | n) _ rfl
    · exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of k PUnit)).eq_of_src _ _
    · dsimp only [affineShiftedClosedComponentIso]
      change (globalFormsEquiv P.closed.obj n).toModuleIso.hom ≫
          (globalShiftedClosedComplexNat P).d (n + 1) (n + 1 + 1) =
        (shiftedComplex k P.globalSections.closed).d (n + 1) (n + 1 + 1) ≫
          (globalFormsEquiv P.closed.obj (n + 1)).toModuleIso.hom
      rw [globalShiftedClosedComplexNat_d_succ, shiftedComplex_d_succ]
      ext x
      change -(formsSheafD k P.closed.obj n).hom.app (op ⊤)
          (globalFormsEquiv P.closed.obj n x) =
        globalFormsEquiv P.closed.obj (n + 1) (-powerD k P.globalSections.closed n x)
      rw [globalFormsEquiv_d, map_neg]
      rfl)

private lemma globalSections_eqnUnit :
    Units.map (globalSectionsAlgEquiv P.compl.obj).toAlgHom.toMonoidHom
        P.globalSections.eqnUnit = P.eqnUnit := by
  apply Units.ext
  rfl

-- The top-open direct image and the concrete complement sections agree after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The affine logarithmic comparison preserves a left-theta algebraic representative. -/
lemma affineLogComparison_theta (n : ℕ)
    (η : ⋀[P.globalSections.ambient]^n Ω[P.globalSections.ambient⁄k]) :
    affineLogComparison P (n + 1)
        ⟨theta k P.globalSections.eqn P.globalSections.compl *
            Forms.map (IsScalarTower.toAlgHom k P.globalSections.ambient P.globalSections.compl)
              η.val,
          theta_mul_map_mem_logPower k P.globalSections.eqn P.globalSections.compl η.property⟩ =
      (thetaToLogSheaf P n).hom.app (op ⊤) (globalFormsEquiv P.ambient.obj n η) := by
  apply logToOpenSheaf_app_injective P (n + 1) (op ⊤)
  change logToOpenTop P (n + 1) _ = _
  rw [affineLogComparison_toOpen, thetaToLogSheaf_logToOpenSheaf]
  change globalFormsEquiv P.compl.obj (n + 1) _ =
    (thetaWedgeSheaf P.compl.obj P.eqnUnit n).hom.app (op ⊤)
      (formsSheafPullbackTop P.j.hom n (globalFormsEquiv P.ambient.obj n η))
  rw [globalFormsEquiv_pull, ← globalSections_eqnUnit P, globalFormsEquiv_leftDlogPower]
  congr 1

/-- The affine logarithmic comparison preserves each specified regular-plus-left-theta
normal form. -/
lemma affineLogComparison_normalForm (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl (n + 1))
    (ω : ⋀[P.globalSections.ambient]^(n + 1) Ω[P.globalSections.ambient⁄k])
    (η : ⋀[P.globalSections.ambient]^n Ω[P.globalSections.ambient⁄k])
    (hx : x.val = Forms.map (IsScalarTower.toAlgHom k P.globalSections.ambient
      P.globalSections.compl) ω.val + theta k P.globalSections.eqn P.globalSections.compl *
        Forms.map (IsScalarTower.toAlgHom k P.globalSections.ambient P.globalSections.compl)
          η.val) :
    affineLogComparison P (n + 1) x =
      regularToLogTop P (n + 1) (globalFormsEquiv P.ambient.obj (n + 1) ω) +
        (thetaToLogSheaf P n).hom.app (op ⊤) (globalFormsEquiv P.ambient.obj n η) := by
  have he : x = powerToLog k P.globalSections.eqn P.globalSections.compl (n + 1) ω +
      ⟨theta k P.globalSections.eqn P.globalSections.compl *
        Forms.map (IsScalarTower.toAlgHom k P.globalSections.ambient P.globalSections.compl) η.val,
        theta_mul_map_mem_logPower k P.globalSections.eqn P.globalSections.compl η.property⟩ :=
    Subtype.ext hx
  rw [he, map_add, affineLogComparison_regular, affineLogComparison_theta]

/-- The affine logarithmic comparison intertwines sheaf residue and algebraic residue without
an additional sign. Blueprint: `thm:geo-log-sheaves`. -/
lemma affineLogComparison_residue (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl (n + 1)) :
    logResidueSheafTop P n (affineLogComparison P (n + 1) x) =
      globalFormsEquiv P.closed.obj n
        (logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n x) := by
  obtain ⟨ω, hω, η, hη, hx⟩ := mem_logPower_succ.1 x.property
  let ω' : ⋀[P.globalSections.ambient]^(n + 1) Ω[P.globalSections.ambient⁄k] := ⟨ω, hω⟩
  let η' : ⋀[P.globalSections.ambient]^n Ω[P.globalSections.ambient⁄k] := ⟨η, hη⟩
  rw [affineLogComparison_normalForm P n x ω' η' hx.symm, map_add]
  change (logResidueSheaf P n).hom.app (op ⊤)
      ((regularToLogSheaf P (n + 1)).hom.app (op ⊤)
        (globalFormsEquiv P.ambient.obj (n + 1) ω')) +
    (logResidueSheaf P n).hom.app (op ⊤)
      ((thetaToLogSheaf P n).hom.app (op ⊤) (globalFormsEquiv P.ambient.obj n η')) = _
  rw [logResidueSheaf_regular, zero_add, logResidueSheaf_theta]
  change formsSheafPullbackTop P.i.hom n (globalFormsEquiv P.ambient.obj n η') = _
  rw [globalFormsEquiv_pull]
  have hρ : logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n x =
      Forms.mapPower (SmoothAlg.algHom P.globalSections.i) n η' := by
    apply Subtype.ext
    rw [coe_logPowerResidue, Forms.coe_mapPower]
    exact logResidue_eq_of_coe_eq P.globalSections.isSmoothPrincipalPair hx.symm
  rw [hρ]
  rfl

/-- The positive component of the shifted divisor comparison is the global forms equivalence. -/
@[simp] lemma affineShiftedClosedComplexIso_hom_f_succ (n : ℕ) :
    (affineShiftedClosedComplexIso P).hom.f (n + 1) =
      (globalFormsEquiv P.closed.obj n).toModuleIso.hom := by
  dsimp only [affineShiftedClosedComplexIso]
  rfl

/-- Regular inclusion commutes with the affine comparisons as a map of complexes. -/
lemma affineLogComplexIso_regularToLog :
    (complexIsoGlobalFormsComplex P.ambient.obj).hom ≫ (globalLogResidueShortComplexNat P).f =
      regularToLog k P.globalSections.eqn P.globalSections.compl ≫
        (affineLogComplexIso P).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  ext x
  change regularToLogTop P n (globalFormsEquiv P.ambient.obj n x) =
    affineLogComparison P n (powerToLog k P.globalSections.eqn P.globalSections.compl n x)
  exact (affineLogComparison_regular P n x).symm

-- The shifted divisor comparison identifies the direct-image top sections with divisor forms.
set_option backward.isDefEq.respectTransparency false in
/-- Residue commutes with the affine comparisons as a map of complexes to the signed shift. -/
lemma affineLogComplexIso_residue :
    (affineLogComplexIso P).hom ≫ (globalLogResidueShortComplexNat P).g =
      logResidueHom P.globalSections.compl P.globalSections.isSmoothPrincipalPair ≫
        (affineShiftedClosedComplexIso P).hom := by
  apply HomologicalComplex.hom_ext
  rintro (_ | n)
  · change (affineLogComplexIso P).hom.f 0 ≫ 0 =
      0 ≫ (affineShiftedClosedComplexIso P).hom.f 0
    rw [comp_zero, zero_comp]
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      affineLogComplexIso_hom_f, logResidueHom_f_succ,
      affineShiftedClosedComplexIso_hom_f_succ]
    ext x
    exact affineLogComparison_residue P n x

/-- The old algebraic logarithmic residue sequence is isomorphic to actual global sections of
the sheaf sequence. Blueprint: `thm:geo-log-sheaves`. -/
def affineLogResidueShortComplexIso :
    logResidueShortComplex P.globalSections.compl P.globalSections.isSmoothPrincipalPair ≅
      globalLogResidueShortComplexNat P :=
  ShortComplex.isoMk (complexIsoGlobalFormsComplex P.ambient.obj) (affineLogComplexIso P)
    (affineShiftedClosedComplexIso P)
    (affineLogComplexIso_regularToLog P) (affineLogComplexIso_residue P)

/-- The global logarithmic residue sequence of an affine pair is short exact by comparison
with the old algebraic sequence. -/
lemma globalLogResidueShortComplexNat_shortExact :
    (globalLogResidueShortComplexNat P).ShortExact :=
  ShortComplex.shortExact_of_iso (affineLogResidueShortComplexIso P)
    (logResidueShortExact P.globalSections.compl P.globalSections.isSmoothPrincipalPair)

/-- On an affine pair, every global divisor form has a global logarithmic residue lift.
This uses affine comparison; it asserts no surjectivity on arbitrary non-affine opens. -/
lemma logResidueSheafTop_surjective (n : ℕ) :
    Function.Surjective (logResidueSheafTop P n) := by
  intro γ
  obtain ⟨x, hx⟩ := logPowerResidue_surjective P.globalSections.compl
    P.globalSections.isSmoothPrincipalPair n ((globalFormsEquiv P.closed.obj n).symm γ)
  refine ⟨affineLogComparison P (n + 1) x, ?_⟩
  rw [affineLogComparison_residue, hx, LinearEquiv.apply_symm_apply]

/-- The actual global residue sequence of an affine pair is exact in each positive degree. -/
lemma exact_regularToLogTop_logResidueSheafTop (n : ℕ) :
    Function.Exact (regularToLogTop P (n + 1)) (logResidueSheafTop P n) := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (globalLogResidueShortComplexNat_shortExact P) (n + 1)
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.exact

/-- A logarithmic lift of a closed divisor form has a regular global differential, yielding
the lift-and-differentiate representative for Gysin with the positive `d(l)` convention. -/
lemma exists_regularToLogTop_eq_logSheafD_of_residue_closed (n : ℕ)
    (l : (logSheaf P (n + 1)).obj.obj (op ⊤))
    (hl : (formsSheafD k P.closed.obj n).hom.app (op ⊤)
      (logResidueSheafTop P n l) = 0) :
    ∃ ω : (formsSheaf k P.ambient.obj (n + 1 + 1)).obj.obj (op ⊤),
      regularToLogTop P (n + 1 + 1) ω = (logSheafD P (n + 1)).hom.app (op ⊤) l := by
  apply (exact_regularToLogTop_logResidueSheafTop P (n + 1) _).1
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) (logResidueSheaf_d P n)) (op ⊤)) l
  change logResidueSheafTop P (n + 1) ((logSheafD P (n + 1)).hom.app (op ⊤) l) =
    -((formsSheafD k P.closed.obj n).hom.app (op ⊤) (logResidueSheafTop P n l)) at h
  exact h.trans (by rw [hl, neg_zero])

/-- The regular component of the short-complex comparison is the global forms comparison. -/
@[simp] lemma affineLogResidueShortComplexIso_hom_τ₁ :
    (affineLogResidueShortComplexIso P).hom.τ₁ =
      (complexIsoGlobalFormsComplex P.ambient.obj).hom := rfl

/-- The logarithmic component of the short-complex comparison is the affine logarithmic
comparison. -/
@[simp] lemma affineLogResidueShortComplexIso_hom_τ₂ :
    (affineLogResidueShortComplexIso P).hom.τ₂ = (affineLogComplexIso P).hom := rfl

/-- The divisor component of the short-complex comparison is the signed shifted comparison. -/
@[simp] lemma affineLogResidueShortComplexIso_hom_τ₃ :
    (affineLogResidueShortComplexIso P).hom.τ₃ = (affineShiftedClosedComplexIso P).hom := rfl

/-- A specified residue equation is preserved and reflected by the affine comparisons. -/
lemma affineLogComparison_residue_eq_iff (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl (n + 1))
    (γ : ⋀[P.globalSections.closed]^n Ω[P.globalSections.closed⁄k]) :
    logResidueSheafTop P n (affineLogComparison P (n + 1) x) = globalFormsEquiv P.closed.obj n γ ↔
      logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n x = γ := by
  rw [affineLogComparison_residue]
  exact (globalFormsEquiv P.closed.obj n).injective.eq_iff

/-- Inverse comparison takes global sheaf residue to algebraic residue of the inverse
logarithmic form. -/
lemma affineLogComparison_residue_symm (n : ℕ)
    (l : (logSheaf P (n + 1)).obj.obj (op ⊤)) :
    (globalFormsEquiv P.closed.obj n).symm (logResidueSheafTop P n l) =
      logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n
        ((affineLogComparison P (n + 1)).symm l) := by
  rw [LinearEquiv.symm_apply_eq]
  simpa only [LinearEquiv.apply_symm_apply] using
    affineLogComparison_residue P n ((affineLogComparison P (n + 1)).symm l)

/-- The affine logarithmic comparison preserves and reflects closedness. -/
lemma affineLogComparison_closed_iff (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n) :
    (logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x) = 0 ↔
      logPowerD k P.globalSections.eqn P.globalSections.compl n x = 0 := by
  rw [affineLogComparison_d, LinearEquiv.map_eq_zero_iff]

/-- A global logarithmic section is closed exactly when its algebraic representative is closed. -/
lemma affineLogComparison_global_closed_iff (n : ℕ)
    (l : (logSheaf P n).obj.obj (op ⊤)) :
    (logSheafD P n).hom.app (op ⊤) l = 0 ↔
      logPowerD k P.globalSections.eqn P.globalSections.compl n
        ((affineLogComparison P n).symm l) = 0 := by
  simpa only [LinearEquiv.apply_symm_apply] using
    affineLogComparison_closed_iff P n ((affineLogComparison P n).symm l)

/-- The equation `d(l) = regular(ω)` is preserved and reflected by the affine comparisons. -/
lemma affineLogComparison_d_eq_regular_iff (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n)
    (ω : ⋀[P.globalSections.ambient]^(n + 1) Ω[P.globalSections.ambient⁄k]) :
    (logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x) =
        regularToLogTop P (n + 1) (globalFormsEquiv P.ambient.obj (n + 1) ω) ↔
      logPowerD k P.globalSections.eqn P.globalSections.compl n x =
        powerToLog k P.globalSections.eqn P.globalSections.compl (n + 1) ω := by
  rw [affineLogComparison_d, ← affineLogComparison_regular]
  exact (affineLogComparison P (n + 1)).injective.eq_iff

/-- The equation `regular(ω) = d(l)` is preserved and reflected by the affine comparisons. -/
lemma affineLogComparison_regular_eq_d_iff (n : ℕ)
    (x : logPower k P.globalSections.eqn P.globalSections.compl n)
    (ω : ⋀[P.globalSections.ambient]^(n + 1) Ω[P.globalSections.ambient⁄k]) :
    regularToLogTop P (n + 1) (globalFormsEquiv P.ambient.obj (n + 1) ω) =
        (logSheafD P n).hom.app (op ⊤) (affineLogComparison P n x) ↔
      powerToLog k P.globalSections.eqn P.globalSections.compl (n + 1) ω =
        logPowerD k P.globalSections.eqn P.globalSections.compl n x :=
  eq_comm.trans ((affineLogComparison_d_eq_regular_iff P n x ω).trans eq_comm)

/-- Residue lifts and their regular differentials are preserved and reflected by the affine
comparisons, with the representative convention `G[γ] = [d(l)]`. -/
lemma affineLogComparison_gysin_representative_iff (n : ℕ)
    (l : logPower k P.globalSections.eqn P.globalSections.compl (n + 1))
    (γ : ⋀[P.globalSections.closed]^n Ω[P.globalSections.closed⁄k])
    (ω : ⋀[P.globalSections.ambient]^(n + 1 + 1) Ω[P.globalSections.ambient⁄k]) :
    (logResidueSheafTop P n (affineLogComparison P (n + 1) l) = globalFormsEquiv P.closed.obj n γ ∧
      regularToLogTop P (n + 1 + 1) (globalFormsEquiv P.ambient.obj (n + 1 + 1) ω) =
        (logSheafD P (n + 1)).hom.app (op ⊤) (affineLogComparison P (n + 1) l)) ↔
    (logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n l = γ ∧
      powerToLog k P.globalSections.eqn P.globalSections.compl (n + 1 + 1) ω =
        logPowerD k P.globalSections.eqn P.globalSections.compl (n + 1) l) :=
  and_congr (affineLogComparison_residue_eq_iff P n l γ)
    (affineLogComparison_regular_eq_d_iff P (n + 1) l ω)

/-- For arbitrary global sections, the residue-lift and regular-differential equations are
exactly the old algebraic equations under inverse comparison. The Gysin representative is
`d(l)`, with no additional sign. Blueprint: `thm:geo-dr-instance`. -/
lemma affineLogComparison_global_gysin_representative_iff (n : ℕ)
    (l : (logSheaf P (n + 1)).obj.obj (op ⊤))
    (γ : (formsSheaf k P.closed.obj n).obj.obj (op ⊤))
    (ω : (formsSheaf k P.ambient.obj (n + 1 + 1)).obj.obj (op ⊤)) :
    (logResidueSheafTop P n l = γ ∧ regularToLogTop P (n + 1 + 1) ω =
      (logSheafD P (n + 1)).hom.app (op ⊤) l) ↔
    (logPowerResidue P.globalSections.compl P.globalSections.isSmoothPrincipalPair n
        ((affineLogComparison P (n + 1)).symm l) = (globalFormsEquiv P.closed.obj n).symm γ ∧
      powerToLog k P.globalSections.eqn P.globalSections.compl (n + 1 + 1)
          ((globalFormsEquiv P.ambient.obj (n + 1 + 1)).symm ω) =
        logPowerD k P.globalSections.eqn P.globalSections.compl (n + 1)
          ((affineLogComparison P (n + 1)).symm l)) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    affineLogComparison_gysin_representative_iff P n ((affineLogComparison P (n + 1)).symm l)
      ((globalFormsEquiv P.closed.obj n).symm γ)
      ((globalFormsEquiv P.ambient.obj (n + 1 + 1)).symm ω)

end OrlikSolomon.Geometric.DeRham
