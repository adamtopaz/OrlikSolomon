/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.Geometric.NonAffine.Fiber

/-!
# Concrete sums of chart complexes and their restriction differences

A pair of nonnegative cochain complexes of modules has a concrete sum with product terms
and componentwise differential. Two restriction maps to an overlap complex induce the
Čech difference, with the second chart minus the first. The constructions are natural in
chain maps and compatible with componentwise chain isomorphisms.

The main definitions are `chartSumComplex`, `chartSumDifference`, and `chartSumIso`.
`chartSumDifference_naturality` supplies the diagram comparison used to transport the
associated two-chart homotopy fibers.

Blueprint: the routine chart-comparison constructions in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [CommRing k]
  (A0 A1 : CochainComplex (ModuleCat.{v} k) ℕ)

/-- The concrete product of the two chart modules in degree `n`. -/
@[implicit_reducible]
def chartSumTerm (n : ℕ) : ModuleCat.{v} k := ModuleCat.of k (A0.X n × A1.X n)

/-- The componentwise differential on the two chart modules. -/
def chartSumDifferential (n : ℕ) : chartSumTerm A0 A1 n →ₗ[k] chartSumTerm A0 A1 (n + 1) :=
  (A0.d n (n + 1)).hom.prodMap (A1.d n (n + 1)).hom

/-- The sum of two possibly different nonnegative cochain complexes, realized by products. -/
-- Keep the concrete product carriers available to rewriting after the component formulas.
@[implicit_reducible]
def chartSumComplex : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (chartSumTerm A0 A1)
    (fun n => ModuleCat.ofHom (chartSumDifferential A0 A1 n)) (fun n => by
      ext x
      apply Prod.ext
      · change (A0.d n (n + 1) ≫ A0.d (n + 1) (n + 2)) x.1 = 0
        rw [A0.d_comp_d]
        rfl
      · change (A1.d n (n + 1) ≫ A1.d (n + 1) (n + 2)) x.2 = 0
        rw [A1.d_comp_d]
        rfl)

/-- The terms of the sum are the concrete products of the chart modules. -/
lemma chartSumComplex_X (n : ℕ) : (chartSumComplex A0 A1).X n = chartSumTerm A0 A1 n := rfl

/-- The differential of the sum is the componentwise chart differential. -/
@[simp]
lemma chartSumComplex_d (n : ℕ) : (chartSumComplex A0 A1).d n (n + 1) =
    ModuleCat.ofHom (chartSumDifferential A0 A1 n) := by
  simp only [chartSumComplex, CochainComplex.of_d]

/-- The canonical identification of a sum term with its concrete product of chart modules. -/
def chartSumTermIso (n : ℕ) : (chartSumComplex A0 A1).X n ≅
    ModuleCat.of k (A0.X n × A1.X n) := Iso.refl _

/-- The term-to-product isomorphism has the identity underlying function. -/
@[simp]
lemma chartSumTermIso_hom_apply (n : ℕ) (x : (chartSumComplex A0 A1).X n) :
    (chartSumTermIso A0 A1 n).hom x = x := rfl

/-- The inverse product-to-term isomorphism has the identity underlying function. -/
@[simp]
lemma chartSumTermIso_inv_apply (n : ℕ) (x : A0.X n × A1.X n) :
    (chartSumTermIso A0 A1 n).inv x = x := rfl

/-- The sum differential acts componentwise. -/
@[simp]
lemma chartSumDifferential_apply (n : ℕ) (x : chartSumTerm A0 A1 n) :
    chartSumDifferential A0 A1 n x = (A0.d n (n + 1) x.1, A1.d n (n + 1) x.2) := rfl

variable {A0 A1} {A0' A1' A0'' A1'' B B' : CochainComplex (ModuleCat.{v} k) ℕ}

/-- A pair of chain maps induces the componentwise map of chart sums. -/
def chartSumMap (f0 : A0 ⟶ A0') (f1 : A1 ⟶ A1') :
    chartSumComplex A0 A1 ⟶ chartSumComplex A0' A1' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom ((f0.f n).hom.prodMap (f1.f n).hom))
    (fun n => by
      rw [chartSumComplex_d, chartSumComplex_d]
      ext x
      apply Prod.ext
      · exact congr($(f0.comm n (n + 1)) x.1)
      · exact congr($(f1.comm n (n + 1)) x.2))

/-- The induced map of chart sums applies the two maps to their respective components. -/
@[simp]
lemma chartSumMap_f_apply (f0 : A0 ⟶ A0') (f1 : A1 ⟶ A1') (n : ℕ)
    (x : chartSumTerm A0 A1 n) :
    (chartSumMap f0 f1).f n x = (f0.f n x.1, f1.f n x.2) := rfl

/-- Identity maps induce the identity on the chart sum. -/
@[simp]
lemma chartSumMap_id : chartSumMap (𝟙 A0) (𝟙 A1) = 𝟙 (chartSumComplex A0 A1) := by
  ext n x
  rfl

/-- The componentwise construction preserves composition of chain maps. -/
@[simp]
lemma chartSumMap_comp (f0 : A0 ⟶ A0') (f1 : A1 ⟶ A1')
    (g0 : A0' ⟶ A0'') (g1 : A1' ⟶ A1'') :
    chartSumMap (f0 ≫ g0) (f1 ≫ g1) = chartSumMap f0 f1 ≫ chartSumMap g0 g1 := by
  ext n x
  rfl

/-- A pair of chain isomorphisms induces the corresponding isomorphism of chart sums. -/
def chartSumIso (e0 : A0 ≅ A0') (e1 : A1 ≅ A1') :
    chartSumComplex A0 A1 ≅ chartSumComplex A0' A1' where
  hom := chartSumMap e0.hom e1.hom
  inv := chartSumMap e0.inv e1.inv
  hom_inv_id := by rw [← chartSumMap_comp, e0.hom_inv_id, e1.hom_inv_id, chartSumMap_id]
  inv_hom_id := by rw [← chartSumMap_comp, e0.inv_hom_id, e1.inv_hom_id, chartSumMap_id]

/-- The forward chart-sum isomorphism acts componentwise. -/
@[simp]
lemma chartSumIso_hom_f_apply (e0 : A0 ≅ A0') (e1 : A1 ≅ A1') (n : ℕ)
    (x : chartSumTerm A0 A1 n) :
    (chartSumIso e0 e1).hom.f n x = (e0.hom.f n x.1, e1.hom.f n x.2) := rfl

/-- The inverse chart-sum isomorphism acts componentwise. -/
@[simp]
lemma chartSumIso_inv_f_apply (e0 : A0 ≅ A0') (e1 : A1 ≅ A1') (n : ℕ)
    (x : chartSumTerm A0' A1' n) :
    (chartSumIso e0 e1).inv.f n x = (e0.inv.f n x.1, e1.inv.f n x.2) := rfl

/-- The difference of the two restrictions, with the second chart minus the first chart. -/
def chartSumDifference (f0 : A0 ⟶ B) (f1 : A1 ⟶ B) : chartSumComplex A0 A1 ⟶ B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((f1.f n).hom.comp (LinearMap.snd k _ _) - (f0.f n).hom.comp (LinearMap.fst k _ _)))
    (fun n => by
      rw [chartSumComplex_d]
      ext x
      change B.d n (n + 1) (f1.f n x.2 - f0.f n x.1) =
        f1.f (n + 1) (A1.d n (n + 1) x.2) - f0.f (n + 1) (A0.d n (n + 1) x.1)
      rw [map_sub]
      exact congrArg₂ (· - ·) congr($(f1.comm n (n + 1)) x.2)
        congr($(f0.comm n (n + 1)) x.1))

/-- The restriction difference sends a chart pair to the second image minus the first. -/
@[simp]
lemma chartSumDifference_f_apply (f0 : A0 ⟶ B) (f1 : A1 ⟶ B) (n : ℕ)
    (x : chartSumTerm A0 A1 n) :
    (chartSumDifference f0 f1).f n x = f1.f n x.2 - f0.f n x.1 := rfl

/-- Two commuting restriction squares give a commuting square for their difference maps. -/
lemma chartSumDifference_naturality (f0 : A0 ⟶ B) (f1 : A1 ⟶ B)
    (f0' : A0' ⟶ B') (f1' : A1' ⟶ B') (g0 : A0 ⟶ A0') (g1 : A1 ⟶ A1') (gB : B ⟶ B')
    (h0 : g0 ≫ f0' = f0 ≫ gB) (h1 : g1 ≫ f1' = f1 ≫ gB) :
    chartSumMap g0 g1 ≫ chartSumDifference f0' f1' = chartSumDifference f0 f1 ≫ gB := by
  ext n x
  change f1'.f n (g1.f n x.2) - f0'.f n (g0.f n x.1) =
    gB.f n (f1.f n x.2 - f0.f n x.1)
  rw [map_sub]
  exact congrArg₂ (· - ·) congr($(congrArg (fun f : A1 ⟶ B' => f.f n) h1) x.2)
    congr($(congrArg (fun f : A0 ⟶ B' => f.f n) h0) x.1)

/-- Transporting the chart and overlap complexes by compatible isomorphisms preserves
the restriction-difference diagram. -/
lemma chartSumIso_difference (f0 : A0 ⟶ B) (f1 : A1 ⟶ B)
    (f0' : A0' ⟶ B') (f1' : A1' ⟶ B')
    (e0 : A0 ≅ A0') (e1 : A1 ≅ A1') (eB : B ≅ B')
    (h0 : e0.hom ≫ f0' = f0 ≫ eB.hom) (h1 : e1.hom ≫ f1' = f1 ≫ eB.hom) :
    (chartSumIso e0 e1).hom ≫ chartSumDifference f0' f1' =
      chartSumDifference f0 f1 ≫ eB.hom :=
  chartSumDifference_naturality f0 f1 f0' f1' e0.hom e1.hom eB.hom h0 h1

end OrlikSolomon.Geometric.Examples
