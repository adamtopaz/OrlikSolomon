/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import OrlikSolomon.DeRham.Pole.Degree
public import OrlikSolomon.DeRham.Schemes.Log.Restriction

/-!
# Logarithmic comparisons on affine schemes and stalks

The ordinary module stalk functors preserve homology and jointly detect isomorphisms of
sheaves. Consequently they detect quasi-isomorphisms of sheaf complexes of any shape.
The criteria in `Geometry/Schemes/ModuleGluing` give the sheaf-theoretic step in the logarithmic
comparison of `thm:geo-log-sheaves`; they make no assertion about applying global sections to a
quasi-isomorphism.

The algebraic logarithmic quasi-isomorphism is imported from `DeRham/Pole/Degree`. It gives
global comparison on affine pairs and local comparison on affine neighborhoods for the
stalkwise theorem.

## Main results

* `affineGlobalLogToOpen_quasiIso`: global comparison on an affine pair, from the algebraic theorem.
* `logSheafComparison_of_units` and `logSheafComparison`: the actual logarithmic inclusion
  is a quasi-isomorphism of sheaf complexes, proved on affine neighborhoods and then stalks.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace OrlikSolomon.Geometric.DeRham

@[deprecated (since := "2026-11-07")]
alias algebraicLogToLocalization_quasiIso := OrlikSolomon.DeRham.logToLocalization_quasiIso

@[deprecated (since := "2026-11-07")]
alias sheafComplex_quasiIso_iff_stalk := OrlikSolomon.Geometric.sheafComplex_quasiIso_iff_stalk

@[deprecated (since := "2026-11-07")]
alias presheafComplex_stalk_quasiIso_of_basis :=
  OrlikSolomon.Geometric.presheafComplex_stalk_quasiIso_of_basis

@[deprecated (since := "2026-11-07")]
alias sheafComplex_quasiIso_of_basis := OrlikSolomon.Geometric.sheafComplex_quasiIso_of_basis

section AffineComparison

variable {k : Type u} [CommRing k] (P : DivisorPair (SmoothDomain.aff k))

/-- Global logarithmic forms compute the complement's global de Rham complex for an affine
pair, when positive integers are units. This follows from the algebraic pole theorem and the
affine comparison square, rather than exactness of global sections on arbitrary schemes. -/
theorem affineGlobalLogToOpen_quasiIso (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    QuasiIso
      (((sheafSectionsFunctor (k := k) P.ambient.obj.left ⊤).mapHomologicalComplex
        (.up ℕ)).map (logToOpenComplexNat P)) := by
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (affineLogComplexIso P) (complexIsoGlobalFormsComplex P.compl.obj)
      (affineLogComplexIso_toOpen P))).1
    (OrlikSolomon.DeRham.logToLocalization_quasiIso k P.globalSections.eqn
      P.globalSections.compl hUnits P.globalSections.isSmoothPrincipalPair)

end AffineComparison

section GeometricComparison

variable {k : Type u} [CommRing k] {D : SmoothDomain k} (P : DivisorPair D)

/-- The inclusion of logarithmic forms in the ordinary direct-image de Rham complex is a
quasi-isomorphism when positive integers are units in the base ring. The proof compares sections
on every affine neighborhood with the existing pole theorem, then passes to stalks.
It does not apply underived global sections to a quasi-isomorphism.

Blueprint: `thm:geo-log-sheaves`. -/
theorem logSheafComparison_of_units (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    QuasiIso (logToOpenComplexNat P) := by
  apply Geometric.sheafComplex_quasiIso_of_basis k P.ambient.obj.left (logToOpenComplexNat P)
    (B := P.ambient.obj.left.affineOpens)
    (by simpa only [Opens.IsBasis] using P.ambient.obj.left.isBasis_affineOpens)
  intro U hU
  let V : P.ambient.obj.left.affineOpens := ⟨U, hU⟩
  change QuasiIso
    (((sheafSectionsFunctor (k := k) P.ambient.obj.left V.1).mapHomologicalComplex
      (.up ℕ)).map (logToOpenComplexNat P))
  let Q := affineNeighborhoodAlgebraicPair P V
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (affineNeighborhoodLogComplexIso P V) (affineNeighborhoodOpenComplexIso P V)
      (affineNeighborhoodLogComplexIso_toOpen P V))).1
        (OrlikSolomon.DeRham.logToLocalization_quasiIso k Q.eqn Q.compl hUnits
          Q.isSmoothPrincipalPair)

end GeometricComparison

/-- Over a characteristic-zero field, logarithmic forms are quasi-isomorphic to the ordinary
direct image of forms on the complement, as complexes of sheaves. This is a stalkwise statement;
it makes no comparison with derived direct image or non-affine global cohomology.

Blueprint: `thm:geo-log-sheaves`. -/
theorem logSheafComparison {k : Type u} [Field k] [CharZero k] {D : SmoothDomain k}
    (P : DivisorPair D) : QuasiIso (logToOpenComplexNat P) :=
  logSheafComparison_of_units P fun n => isUnit_iff_ne_zero.2 (Nat.cast_add_one_ne_zero n)

end OrlikSolomon.Geometric.DeRham
