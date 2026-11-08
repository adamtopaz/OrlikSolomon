/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A concrete nonnegative homotopy fiber for the two-chart example

The total complex for two opens is the homotopy fiber of the difference of restrictions. This
module gives its terms and differentials as modules, so that the projective-line computation
can use the old algebraic de Rham complexes and the ordinary long exact homology sequence.

Blueprint: the two-chart computation in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [CommRing k]
  {A B : CochainComplex (ModuleCat.{v} k) ℕ} (φ : A ⟶ B)

/-- The modules of the homotopy fiber, with no overlap term in degree zero. -/
@[implicit_reducible]
def twoChartFiberTerm (_φ : A ⟶ B) : ℕ → ModuleCat.{v} k
  | 0 => A.X 0
  | n + 1 => ModuleCat.of k (A.X (n + 1) × B.X n)

/-- The total differential, with a minus sign on the overlap differential. -/
def twoChartFiberDifferential :
    (n : ℕ) → twoChartFiberTerm φ n →ₗ[k] twoChartFiberTerm φ (n + 1)
  | 0 => (A.d 0 1).hom.prod (φ.f 0).hom
  | n + 1 =>
    ((A.d (n + 1) (n + 2)).hom.comp (LinearMap.fst k _ _)).prod
      (((φ.f (n + 1)).hom.comp (LinearMap.fst k _ _)) -
        (B.d n (n + 1)).hom.comp (LinearMap.snd k _ _))

private lemma differential_square (K : CochainComplex (ModuleCat.{v} k) ℕ) (n : ℕ)
    (x : K.X n) : K.d (n + 1) (n + 2) (K.d n (n + 1) x) = 0 := by
  change (K.d n (n + 1) ≫ K.d (n + 1) (n + 2)) x = 0
  rw [K.d_comp_d]
  rfl

private lemma differential_natural (n : ℕ) (x : A.X n) :
    φ.f (n + 1) (A.d n (n + 1) x) = B.d n (n + 1) (φ.f n x) := by
  exact congr($(φ.comm n (n + 1)) x).symm

/-- The total differential squares to zero by compatibility with the restriction map. -/
lemma twoChartFiberDifferential_square (n : ℕ) :
    (twoChartFiberDifferential φ (n + 1)).comp (twoChartFiberDifferential φ n) = 0 := by
  ext x
  cases n with
  | zero =>
    apply Prod.ext
    · exact differential_square A 0 x
    · exact sub_eq_zero.mpr (differential_natural φ 0 x)
  | succ n =>
    apply Prod.ext
    · exact differential_square A (n + 1) x.1
    · change φ.f (n + 2) (A.d (n + 1) (n + 2) x.1) -
        B.d (n + 1) (n + 2) (φ.f (n + 1) x.1 - B.d n (n + 1) x.2) = 0
      rw [map_sub, differential_square B, sub_zero, differential_natural φ, sub_self]

/-- The homotopy fiber in nonnegative degrees: degree zero is `A⁰`, and degree `n+1` is
`Aⁿ⁺¹ × Bⁿ`, with differential `(a,b) ↦ (da, φ(a) - db)`. -/
def twoChartFiber : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (twoChartFiberTerm φ)
    (fun n => ModuleCat.ofHom (twoChartFiberDifferential φ n))
    (fun n => ModuleCat.hom_ext (twoChartFiberDifferential_square φ n))

@[simp]
lemma twoChartFiber_X (n : ℕ) : (twoChartFiber φ).X n = twoChartFiberTerm φ n := rfl

@[simp]
lemma twoChartFiber_d (n : ℕ) :
    (twoChartFiber φ).d n (n + 1) = ModuleCat.ofHom (twoChartFiberDifferential φ n) := by
  simp only [twoChartFiber, CochainComplex.of_d]

/-- The overlap shifted up by one, with the sign from totalization. -/
@[implicit_reducible]
def twoChartOverlapTerm (B : CochainComplex (ModuleCat.{v} k) ℕ) : ℕ → ModuleCat.{v} k
  | 0 => ModuleCat.of k PUnit.{v + 1}
  | n + 1 => B.X n

/-- The differential of the shifted overlap complex. -/
def twoChartOverlapDifferential (B : CochainComplex (ModuleCat.{v} k) ℕ) :
    (n : ℕ) → twoChartOverlapTerm B n →ₗ[k] twoChartOverlapTerm B (n + 1)
  | 0 => 0
  | n + 1 => -(B.d n (n + 1)).hom

/-- The overlap complex placed in total Čech degrees at least one. -/
def twoChartOverlap (B : CochainComplex (ModuleCat.{v} k) ℕ) :
    CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (twoChartOverlapTerm B)
    (fun n => ModuleCat.ofHom (twoChartOverlapDifferential B n)) (fun n => by
      cases n with
      | zero => simp [twoChartOverlapDifferential]
      | succ n =>
        ext x
        change -B.d (n + 1) (n + 2) (-B.d n (n + 1) x) = 0
        rw [map_neg, neg_neg, differential_square B])

@[simp]
lemma twoChartOverlap_d (n : ℕ) :
    (twoChartOverlap B).d n (n + 1) = ModuleCat.ofHom (twoChartOverlapDifferential B n) := by
  simp only [twoChartOverlap, CochainComplex.of_d]

private def fiberProjection (n : ℕ) : twoChartFiberTerm φ n →ₗ[k] A.X n :=
  match n with
  | 0 => LinearMap.id
  | _ + 1 => LinearMap.fst k _ _

private def fiberInclusion (n : ℕ) : twoChartOverlapTerm B n →ₗ[k] twoChartFiberTerm φ n :=
  match n with
  | 0 => 0
  | _ + 1 => LinearMap.inr k _ _

/-- Projection from the two-chart total complex to its two regular charts. -/
@[no_expose]
def twoChartFiberProjection : twoChartFiber φ ⟶ A :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (fiberProjection φ n)) (fun n => by
    rw [twoChartFiber_d]
    ext x
    cases n <;> rfl)

/-- Inclusion of the overlap column in the total complex. -/
@[no_expose]
def twoChartFiberInclusion : twoChartOverlap B ⟶ twoChartFiber φ :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (fiberInclusion φ n)) (fun n => by
    rw [twoChartOverlap_d, twoChartFiber_d]
    ext x
    change twoChartFiberDifferential φ n (fiberInclusion φ n x) =
      fiberInclusion φ (n + 1) (twoChartOverlapDifferential B n x)
    cases n with
    | zero =>
      change (A.d 0 1 0, φ.f 0 0) = (0, 0)
      simp
    | succ n =>
      change (A.d (n + 1) (n + 2) 0, φ.f (n + 1) 0 - B.d n (n + 1) x) =
        (0, -B.d n (n + 1) x)
      simp)

/-- The overlap inclusion has zero composite with projection onto the charts. -/
lemma twoChartFiberInclusion_projection :
    twoChartFiberInclusion φ ≫ twoChartFiberProjection φ = 0 := by
  ext n x
  cases n <;> rfl

/-- The short complex of the two Čech columns and their total complex. -/
@[implicit_reducible]
def twoChartFiberSequence : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk (twoChartFiberInclusion φ) (twoChartFiberProjection φ)
    (twoChartFiberInclusion_projection φ)

/-- This sequence is degreewise split short exact; no exactness of global sections is used. -/
theorem twoChartFiberSequence_shortExact : (twoChartFiberSequence φ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    cases n with
    | zero => exact ⟨0, hx.symm⟩
    | succ n =>
      refine ⟨x.2, ?_⟩
      exact Prod.ext hx.symm rfl
  · apply (ModuleCat.mono_iff_injective _).mpr
    cases n with
    | zero => exact fun _ _ _ => Subsingleton.elim (α := PUnit.{v + 1}) _ _
    | succ n => exact fun _ _ h => congrArg Prod.snd h
  · apply (ModuleCat.epi_iff_surjective _).mpr
    cases n with
    | zero => exact fun x => ⟨x, rfl⟩
    | succ n => exact fun x => ⟨(x, 0), rfl⟩

/-- Away from the bottom degree, changing both differential signs preserves homology. -/
def twoChartOverlapShortComplexIso (n : ℕ) :
    (twoChartOverlap B).sc' (n + 1) (n + 2) (n + 3) ≅ B.sc' n (n + 1) (n + 2) :=
  ShortComplex.isoMk (LinearEquiv.neg k (M := B.X n)).toModuleIso (Iso.refl (B.X (n + 1)))
    (LinearEquiv.neg k (M := B.X (n + 2))).toModuleIso
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      rw [twoChartOverlap_d]
      ext x
      change B.d n (n + 1) (-x) = -(B.d n (n + 1) x)
      exact map_neg _ x)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      rw [twoChartOverlap_d]
      ext x
      change B.d (n + 1) (n + 2) x = -(-(B.d (n + 1) (n + 2) x))
      exact (neg_neg _).symm)

/-- Positive-degree homology of the overlap is shifted up by one in the total complex. -/
def twoChartOverlapHomologySuccIso (n : ℕ) :
    (twoChartOverlap B).homology (n + 2) ≅ B.homology (n + 1) :=
  (twoChartOverlap B).homologyIsoSc' (n + 1) (n + 2) (n + 3)
      ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))
      (CochainComplex.next ℕ (n + 2)) ≪≫
    ShortComplex.homologyMapIso (twoChartOverlapShortComplexIso (B := B) n) ≪≫
      (B.homologyIsoSc' n (n + 1) (n + 2)
        ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
        (CochainComplex.next ℕ (n + 1))).symm

/-- Degree-one exactness of the two-chart total complex follows from exactness on the charts
and surjectivity of the difference map on closed functions. -/
theorem twoChartFiber_exactAt_one (hA : A.ExactAt 1)
    (hφ : ∀ b : B.X 0, B.d 0 1 b = 0 →
      ∃ a : A.X 0, A.d 0 1 a = 0 ∧ φ.f 0 a = b) :
    (twoChartFiber φ).ExactAt 1 := by
  have hp := (ComplexShape.up ℕ).prev_eq'
    (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
  have hn := CochainComplex.next ℕ 1
  rw [A.exactAt_iff' 0 1 2 hp hn, ShortComplex.moduleCat_exact_iff] at hA
  change ∀ x : A.X 1, A.d 1 2 x = 0 → ∃ a : A.X 0, A.d 0 1 a = x at hA
  rw [(twoChartFiber φ).exactAt_iff' 0 1 2 hp hn, ShortComplex.moduleCat_exact_iff]
  change ∀ x : A.X 1 × B.X 0, (twoChartFiber φ).d 1 2 x = 0 →
    ∃ a : A.X 0, (twoChartFiber φ).d 0 1 a = x
  intro x hx
  change (twoChartFiber φ).d 1 2 x = 0 at hx
  rw [twoChartFiber_d] at hx
  have hx₁ : A.d 1 2 x.1 = 0 := congrArg Prod.fst hx
  have hx₂ : φ.f 1 x.1 = B.d 0 1 x.2 := sub_eq_zero.mp (congrArg Prod.snd hx)
  obtain ⟨a, ha⟩ := hA x.1 hx₁
  have hb : B.d 0 1 (x.2 - φ.f 0 a) = 0 := by
    rw [map_sub, ← differential_natural φ 0 a]
    change B.d 0 1 x.2 - φ.f 1 (A.d 0 1 a) = 0
    rw [ha, hx₂, sub_self]
  obtain ⟨c, hc₀, hc₁⟩ := hφ _ hb
  refine ⟨a + c, ?_⟩
  rw [twoChartFiber_d]
  apply Prod.ext
  · change A.d 0 1 (a + c) = x.1
    rw [map_add, ha, hc₀, add_zero]
  · change φ.f 0 (a + c) = x.2
    rw [map_add, hc₁, add_sub_cancel]

section Isomorphism

variable {A' B' : CochainComplex (ModuleCat.{v} k) ℕ} (ψ : A' ⟶ B')
  (eA : A ≅ A') (eB : B ≅ B')

/-- A commuting isomorphism of restriction diagrams identifies the total-complex terms. -/
def twoChartFiberTermIso : (n : ℕ) → twoChartFiberTerm φ n ≅ twoChartFiberTerm ψ n
  | 0 => (HomologicalComplex.eval _ _ 0).mapIso eA
  | n + 1 =>
    (LinearEquiv.prodCongr
      ((HomologicalComplex.eval _ _ (n + 1)).mapIso eA).toLinearEquiv
      ((HomologicalComplex.eval _ _ n).mapIso eB).toLinearEquiv).toModuleIso

/-- An isomorphism of the chart/overlap diagram induces an isomorphism of its total complex. -/
def twoChartFiberIso (h : eA.hom ≫ ψ = φ ≫ eB.hom) : twoChartFiber φ ≅ twoChartFiber ψ :=
  HomologicalComplex.Hom.isoOfComponents (twoChartFiberTermIso φ ψ eA eB) (by
    rintro n _ rfl
    rw [twoChartFiber_d, twoChartFiber_d]
    ext x
    cases n with
    | zero =>
      change (A'.d 0 1 (eA.hom.f 0 x), ψ.f 0 (eA.hom.f 0 x)) =
        (eA.hom.f 1 (A.d 0 1 x), eB.hom.f 0 (φ.f 0 x))
      apply Prod.ext
      · exact congr($(eA.hom.comm 0 1) x)
      · exact congr($(congrArg (fun f : A ⟶ B' => f.f 0) h) x)
    | succ n =>
      change (A'.d (n + 1) (n + 2) (eA.hom.f (n + 1) x.1),
        ψ.f (n + 1) (eA.hom.f (n + 1) x.1) - B'.d n (n + 1) (eB.hom.f n x.2)) =
        (eA.hom.f (n + 2) (A.d (n + 1) (n + 2) x.1),
          eB.hom.f (n + 1) (φ.f (n + 1) x.1 - B.d n (n + 1) x.2))
      apply Prod.ext
      · exact congr($(eA.hom.comm (n + 1) (n + 2)) x.1)
      · have hf := congr($(congrArg (fun f : A ⟶ B' => f.f (n + 1)) h) x.1)
        have hd := congr($(eB.hom.comm n (n + 1)) x.2)
        rw [map_sub]
        exact congrArg₂ (· - ·) hf hd)

end Isomorphism

end OrlikSolomon.Geometric.Examples
