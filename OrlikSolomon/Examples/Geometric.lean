/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Bridge
public import OrlikSolomon.Examples.Bridge
public import OrlikSolomon.Examples.Geometric.Acceptance
public import OrlikSolomon.Examples.Geometric.AffineDeRham
public import OrlikSolomon.Examples.Geometric.DeRhamAcceptance
public import OrlikSolomon.Examples.Geometric.Degenerate
public import OrlikSolomon.Examples.Geometric.Exclusions
public import OrlikSolomon.Examples.Geometric.Morphisms
public import OrlikSolomon.Examples.Geometric.NonAffine
public import OrlikSolomon.Presentation.Geometric

/-!
# Regressions for geometric cohomology

These consumers check that the public geometric cohomology notation works with ordinary ring
rewriting. In particular, a normalized residue and the projection formula give restriction to the
divisor using either `rw` or `simp`, and products involving Gysin and residue values use the same
ring operations as `OrdinaryTheory.obj`.

The remaining examples check the pullback notation and the algebraic standard-residue
simplification after transport. They apply to every admissible domain and geometric ordinary
theory, without nonzero-coefficient assumptions.

A zero-coefficient supports-and-purity model also exercises the geometric bridge and its
component maps. This checks that the degreewise inputs can be instantiated without strengthening
the coefficient hypotheses. The actual open complement of the two points over `F₂` has a scheme
point and no rational points; its logarithmic basis retains the integer word count.

Blueprint: acceptance consumers for `def:geo-theory`, `thm:geo-to-algebraic`, `thm:geo-bridge`,
and `prop:geo-finite-field`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w z t

namespace OrlikSolomon.Geometric.Examples

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-- The normalized residue projection formula supports subsequent ring rewrites. -/
example (P : DivisorPair D) {α : T.obj P.compl}
    (hα : α ∈ T.grading P.compl (1, 1)) (h1 : T.residue P α = 1)
    (β : T.obj P.ambient) : T.residue P (α * T.pull P.j β) = T.pull P.i β := by
  rw [T.residue_mul_pull P hα β, h1, one_mul]

/-- The normalized residue projection formula also simplifies with ordinary ring lemmas. -/
example (P : DivisorPair D) {α : T.obj P.compl}
    (hα : α ∈ T.grading P.compl (1, 1)) (h1 : T.residue P α = 1)
    (β : T.obj P.ambient) : T.residue P (α * T.pull P.j β) = T.pull P.i β := by
  simp [T.residue_mul_pull P hα β, h1]

/-- Gysin values and classes in the public ambient algebra use the same multiplication. -/
example (P : DivisorPair D) (x : T.obj P.closed) (y : T.obj P.ambient) :
    T.gysin P x * (1 * y) = T.gysin P x * y := by
  rw [one_mul]

/-- Residue values and restricted classes use the same multiplication on the divisor. -/
example (P : DivisorPair D) (α : T.obj P.compl) (β : T.obj P.ambient) :
    (T.residue P α : T.obj P.closed) * (1 * T.pull P.i β) =
      T.residue P α * T.pull P.i β := by
  rw [one_mul]

/-- Functor evaluation simplifies to the public pullback notation. -/
example {X Y : D.Obj} (f : X ⟶ Y) (x : T.obj Y) : T.C.map f.op x = T.pull f x := by
  simp

/-- Affine transport preserves the algebraic standard-residue simplification. -/
example (A : SmoothAlg k) (x : T.toAlgebraic.C.obj (SmoothAlg.polynomial A)) :
    T.toAlgebraic.stdResidue A
      (T.toAlgebraic.C.map (SmoothAlg.polynomialToLaurent A) x) = 0 := by
  simp

/-! ### A zero-coefficient supports-and-purity model -/

open OrlikSolomon.Sanity
/-- A geometric degreewise input with zero coefficients and zero groups in every degree. -/
def zeroDegreewiseTheory {k : Type u} [CommRing k] (D : SmoothDomain k) :
    DegreewiseTheory.{u, v, w, z} D zeroWeight.{v, w} where
  H _ _ := PUnit.{z + 1}
  coeff _ _ := 0
  coeff_one _ := Subsingleton.elim _ _
  coeff_mul _ _ _ _ _ := Subsingleton.elim _ _
  bijective_algebraMap_gradeZero :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  graded_comm _ _ _ _ _ := Sigma.ext (add_comm _ _) (heq_of_eq (Subsingleton.elim _ _))
  pull _ _ := 0
  pull_id _ _ _ := Subsingleton.elim _ _
  pull_comp _ _ _ _ := Subsingleton.elim _ _
  pull_one _ := Subsingleton.elim _ _
  pull_mul _ _ _ _ _ := Subsingleton.elim _ _
  pull_coeff _ _ _ := Subsingleton.elim _ _
  bijective_coeff_point _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  eq_zero_point _ _ := Subsingleton.elim _ _
  bijective_pullback_affineLine _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

instance {k : Type u} [CommRing k] (D : SmoothDomain k) (X : D.Obj) (i : ℤ × ℤ) :
    Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} D).H X i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- Zero supported cohomology, with localization and oriented purity on every geometric pair. -/
def zeroSupportsAndPurity {k : Type u} [CommRing k] (D : SmoothDomain k) :
    SupportsAndPurity.{u, v, w, z, t} (zeroDegreewiseTheory.{u, v, w, z} D) where
  support _ _ := PUnit.{t + 1}
  forget _ _ := 0
  boundary _ _ := 0
  purity _ _ :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _
      map_add' _ _ := Subsingleton.elim _ _
      map_smul' _ _ := Subsingleton.elim _ _ }
  exact_forget_pull _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_pull_boundary _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_boundary_forget _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  supportPull _ _ := 0
  forget_natural _ _ _ := Subsingleton.elim _ _
  boundary_natural _ _ _ := Subsingleton.elim _ _
  purity_natural _ _ _ := Subsingleton.elim _ _
  supportMul _ _ _ := 0
  forget_mul _ _ _ _ _ := Subsingleton.elim _ _
  purity_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))
  boundary_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))

/-- Restricting the geometric zero model commutes with forming the ordinary theory. -/
example {k : Type u} [CommRing k] {D₁ D₂ : SmoothDomain k} (h : D₁ ≤ D₂) :
    (ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} D₂)
      (zeroSupportsAndPurity.{u, v, w, z, t} D₂)).restrict h =
        ofSupportsAndPurity ((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h)
          ((zeroSupportsAndPurity.{u, v, w, z, t} D₂).restrict h) := by
  rw [ofSupportsAndPurity_restrict]

/-- The restricted model's pullback formula closes with the public simp lemma alone. -/
example {k : Type u} [CommRing k] {D₁ D₂ : SmoothDomain k} (h : D₁ ≤ D₂)
    {X Y : D₁.Obj} (f : X ⟶ Y) (i : ℤ × ℤ)
    (x : ((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h).H Y i) :
    (ofSupportsAndPurity ((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h)
      ((zeroSupportsAndPurity.{u, v, w, z, t} D₂).restrict h)).pull f
        (((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h).incl Y i x) =
      ((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h).incl X i
        (((zeroDegreewiseTheory.{u, v, w, z} D₂).restrict h).pull f i x) := by
  simp only [ofSupportsAndPurity_pull_incl]

/-- Evaluation on spectra commutes with the bridge for the same realizable zero model. -/
example {k : Type u} [CommRing k] (D : SmoothDomain k) :
    (ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} D)
      (zeroSupportsAndPurity.{u, v, w, z, t} D)).toAlgebraic =
        OrlikSolomon.ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic
          (zeroSupportsAndPurity.{u, v, w, z, t} D).toAlgebraic := by
  rw [ofSupportsAndPurity_toAlgebraic]

/-- Affine evaluation retains the algebraic bridge's homogeneous pullback simplification. -/
example {k : Type u} [CommRing k] (D : SmoothDomain k) {A A' : SmoothAlg k}
    (f : A ⟶ A') (i : ℤ × ℤ)
    (x : (zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic.H A i) :
    (OrlikSolomon.ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic
      (zeroSupportsAndPurity.{u, v, w, z, t} D).toAlgebraic).C.map f
        ((zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic.incl A i x) =
      (zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic.incl A' i
        ((zeroDegreewiseTheory.{u, v, w, z} D).toAlgebraic.map f i x) := by
  simp only [OrlikSolomon.ofSupportsAndPurity_map_incl]

private def frozenPullComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) :
    T.grading Y i →ₗ[R] T.grading X i :=
  (T.isHomogeneousOfShift_mapOverR f).component (add_zero i)

private def frozenGysinComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) (P : DivisorPair D) (i : ℤ × ℤ) :
    T.grading P.closed i →ₗ[R] T.grading P.ambient (i + (2, 1)) :=
  (T.isHomogeneousOfShift_gysinOverR P).component rfl

private def frozenResidueComponent {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : OrdinaryTheory.{u, v, w, z} D ℬ) (P : DivisorPair D) (i : ℤ × ℤ) :
    T.grading P.compl i →ₗ[R] T.grading P.closed (i + (-1, -1)) :=
  (T.isHomogeneousOfShift_residueOverR P).component rfl

/-- The bridge preserves the component maps of a realizable zero-coefficient input. -/
example {k : Type u} [CommRing k] (D : SmoothDomain k) {X Y : D.Obj} (f : X ⟶ Y)
    (P : DivisorPair D) (i : ℤ × ℤ) :
    let T := ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, v, v} D)
      (zeroSupportsAndPurity.{u, v, v, v, v} D)
    (∀ x : T.grading Y i, (frozenPullComponent T f i x : T.obj X) = T.pull f x) ∧
    (∀ x : T.grading P.closed i,
      (frozenGysinComponent T P i x : T.obj P.ambient) = T.gysin P x) ∧
    (∀ x : T.grading P.compl i,
      (frozenResidueComponent T P i x : T.obj P.closed) = T.residue P x) := by
  intro T
  exact ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-! ### A nonempty scheme without rational points -/

/-- The actual open complement of the two rational points of the affine line over `F₂`.
Blueprint: `prop:geo-finite-field`. -/
@[implicit_reducible]
def twoPointsOverF2 : Over (Spec (.of (ZMod 2))) := complement twoPoints

/-- This complement has a scheme point, even though it has no rational point. -/
instance nonempty_twoPointsOverF2 : Nonempty twoPointsOverF2.left := by
  have : Nontrivial twoPoints.ComplementRing := nontrivial_complementRing_twoPoints
  let x : PrimeSpectrum twoPoints.ComplementRing := Classical.choice inferInstance
  exact ⟨(complementIsoSpec twoPoints).inv.left.base x⟩

/-- The complement has no `F₂`-point, expressed by the scheme hom-set over `F₂`. -/
theorem isEmpty_hom_twoPointsOverF2 :
    IsEmpty (spec (CommAlgCat.of (ZMod 2) (ZMod 2)) ⟶ twoPointsOverF2) := by
  refine ⟨fun g ↦ ?_⟩
  let φ := specHomEquiv (spec (CommAlgCat.of (ZMod 2) (ZMod 2)))
    (SmoothAlg.complement twoPoints).obj (g ≫ (complementIsoSpec twoPoints).hom)
  let ψ : twoPoints.ComplementRing →ₐ[ZMod 2] ZMod 2 :=
    (globalSectionsSpecIso (CommAlgCat.of (ZMod 2) (ZMod 2))).hom.hom.comp φ.hom
  exact isEmpty_algHom_twoPoints.false ψ

/-- The integer combinatorial polynomial of the two-point arrangement is `1 + 2 X`. -/
theorem twoPointsOverF2_poincarePolynomial :
    twoPoints.poincarePolynomial = 1 + 2 * Polynomial.X := by
  classical
  have hne : zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)) ≠
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1) := fun h ↦
    (Arrangement.mem_deletion.1 zeroLocus_id_sub_one_mem_deletion).1 h.symm
  have h𝒜 : twoPoints.hyperplanes = {zeroLocus (AffineMap.id (ZMod 2) (ZMod 2)),
      zeroLocus (AffineMap.id (ZMod 2) (ZMod 2) - AffineMap.const _ _ 1)} := by
    ext K
    simp only [Arrangement.mem_hyperplanes, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hK ↦ ?_, ?_⟩
    · simpa using (Arrangement.mem_ofFinset.1 hK).1
    · rintro (rfl | rfl)
      exacts [zeroLocus_id_mem_twoPoints, zeroLocus_id_sub_one_mem_twoPoints]
  exact Arrangement.poincarePolynomial_pair_disjoint twoPoints hne h𝒜 inf_zeroLocus_id_twoPoints

/-- Every supplied geometric theory has a logarithmic basis with two words of length one.
The count is retained from the recursion; it is not inferred from rank over the zero ring. -/
theorem exists_basis_twoPointsOverF2 (D : SmoothDomain (ZMod 2))
    (T : OrdinaryTheory.{0, v, w, z} D ℬ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → List twoPoints)
      (b : Module.Basis ι B (T.obj (D.complement twoPoints))),
      (∀ i, b i = T.logMonomial twoPoints (I i)) ∧
      (∀ i, (I i).length ≤ 1) ∧ Fintype.card {i // (I i).length = 1} = 2 := by
  obtain ⟨ι, inst, I, b, hb, hlen, hcount⟩ := T.exists_basis_logMonomial twoPoints
  let := inst
  refine ⟨ι, inst, I, b, hb, ?_, (hcount 1).trans bettiNumber_one_twoPoints⟩
  simpa only [Module.finrank_self] using hlen


end OrlikSolomon.Geometric.Examples
