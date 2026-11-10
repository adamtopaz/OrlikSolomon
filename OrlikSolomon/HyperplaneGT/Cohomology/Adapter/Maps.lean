/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Geometric.Logarithms
public import OrlikSolomon.Geometry.Schemes.Complement.Basic
public import OrlikSolomon.Grading.Diagonal
public import OrlikSolomon.Grading.DirectSum
public import OrlikSolomon.HyperplaneGT.Geometry.Galois.AlgebraicMaps

/-!
# Actual scheme marking maps and diagonal pullbacks

Every available tagged marking maps its actual open scheme complement to the same
two-puncture open scheme. The maps agree with the existing localization pullbacks and
commute with complement inclusions. Their ordered unit formulas give logarithmic naturality.

For a supplied full geometric ordinary theory, component and diagonal pullbacks are the
restrictions and direct sums of the actual scheme pullback. No OS comparison is used to
define them, and no additional cohomological hypothesis is imposed.

Blueprint: the actual map and pullback part of A04 (`thm:a04`).
-/

@[expose] public section

noncomputable section

universe u v r b h

open CategoryTheory AlgebraicGeometry DirectSum

namespace OrlikSolomon.HyperplaneGT.Cohomology

variable {k : Type u} [Field k] (D : Geometric.SmoothDomain k)

/-- The one common two-puncture target, as an actual open scheme in the supplied domain.
It is independent of every marking, ambient dimension and cofinal system. -/
@[instance_reducible]
def schemeMarkingTarget : D.Obj := D.complement (twoPunctureArrangement k)

/-- The ordered units `t` and `t-1` on the actual common target. -/
def schemeMarkingTargetUnit (a : Fin 2) :
    Γ((schemeMarkingTarget D).obj.left, ⊤)ˣ :=
  Geometric.complementUnit (twoPunctureArrangement k)
    (AffineMap.id k k - AffineMap.const k k (a.val : k))
    (.of_mem (twoPunctureLabel_val k a ▸ (twoPunctureLabel k a).property))

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k] {S : Set k₀} {n : ℕ}

namespace Marking

variable (w : HyperplaneGT.Marking S n) {A A' : Arrangement k (Fin n → k)}

/-- The actual geometric marking map from an open complement to the single common target.
Its coordinate-algebra pullback is the existing `HyperplaneGT.Marking.algebraicMap`.

Blueprint: A04 (`thm:a04`). -/
def _root_.OrlikSolomon.HyperplaneGT.Marking.schemeMap
    (hw : w.Available A) : D.complement A ⟶ schemeMarkingTarget D :=
  D.complementMap w.function (twoPunctureArrangement k) A hw.covers_target

/-- The actual marking map agrees with its localization map under the canonical affine
comparisons. -/
@[reassoc (attr := simp)]
theorem _root_.OrlikSolomon.HyperplaneGT.Marking.schemeMap_comp_complementIsoSpec
    (hw : w.Available A) :
    w.schemeMap D hw ≫ (D.complementIsoSpec (twoPunctureArrangement k)).hom =
      (D.complementIsoSpec A).hom ≫ (D.specFunctor.map (w.algebraicMap hw)).unop :=
  D.complementMap_comp_complementIsoSpec_hom _ _

/-- The marking map restricts its original affine coordinate function. -/
@[reassoc (attr := simp)]
theorem _root_.OrlikSolomon.HyperplaneGT.Marking.schemeMap_comp_complementι (hw : w.Available A) :
    (w.schemeMap D hw).hom ≫ Geometric.complementι (twoPunctureArrangement k) =
      Geometric.complementι A ≫ Geometric.affineSpaceMap k w.function :=
  Geometric.complementMap_comp_complementι _ _

/-- Actual marking maps commute with inclusions of open complements. -/
@[reassoc (attr := simp)]
theorem _root_.OrlikSolomon.HyperplaneGT.Marking.inclusion_comp_schemeMap
    (hw : w.Available A) (hA : A ≤ A') :
    D.complementInclusion hA ≫ w.schemeMap D hw = w.schemeMap D (hw.mono hA) := by
  apply ObjectProperty.hom_ext
  apply Geometric.hom_ext_complement
  change (Geometric.complementInclusion hA ≫
      Geometric.complementMap w.function _ _ hw.covers_target) ≫ _ =
      Geometric.complementMap w.function _ _ (hw.mono hA).covers_target ≫ _
  simp only [Category.assoc, Geometric.complementMap_comp_complementι,
    Geometric.complementInclusion_comp_complementι_assoc]

/-- Each ordered target unit pulls back to the corresponding marking equation on the
actual open source complement. -/
theorem _root_.OrlikSolomon.HyperplaneGT.Marking.schemeMap_targetUnit
    (hw : w.Available A) (a : Fin 2) :
    Units.map (w.schemeMap D hw).hom.left.appTop.hom (schemeMarkingTargetUnit D a) =
      Geometric.complementUnit A
        (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
        (hw.covers_fiber a) := by
  apply Units.ext
  have he : (AffineMap.id k k - AffineMap.const k k (a.val : k)).comp w.function =
      w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)) := by
    ext x
    simp
  change (Geometric.complementMap w.function (twoPunctureArrangement k) A
      hw.covers_target).left.appTop
      (Geometric.complementUnit (twoPunctureArrangement k)
        (AffineMap.id k k - AffineMap.const k k (a.val : k)) _) = _
  rw [Geometric.complementMap_appTop_complementUnit]
  simp only [Geometric.coe_complementUnit, he]

end Marking

variable {D}

variable {R : Type r} [CommRing R] {B : Type b} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (T : Geometric.OrdinaryTheory.{u, r, b, h} D ℬ)

/-- The actual external direct sum of the diagonal cohomology components.
This transparent carrier synonym inherits the existing direct-sum instances without
transport instances. The attempted `instance_reducible` carrier does not synthesize even
its inherited additive monoid or ring; exposing the literal type head is necessary. -/
@[reducible]
def diagonal (X : D.Obj) : Type h :=
  ⨁ q : ℕ, OrlikSolomon.diagonalGrading (T.grading X) q

/-- The canonical internal grading of the actual diagonal direct sum, given by its summand
inclusions. -/
def diagonalDegree (X : D.Obj) (q : ℕ) : Submodule R (diagonal T X) :=
  directSumGrading (fun q ↦ ↥(OrlikSolomon.diagonalGrading (T.grading X) q)) q

/-- Restriction of the actual scheme pullback to a diagonal component. -/
def componentPull {X Y : D.Obj} (f : X ⟶ Y) (q : ℕ) :
    OrlikSolomon.diagonalGrading (T.grading Y) q →ₗ[R]
      OrlikSolomon.diagonalGrading (T.grading X) q :=
  (T.mapOverR f).restrict fun _ hx ↦ T.pull_mem_grading f hx

/-- Component pullback has exactly the original scheme pullback as its underlying value. -/
@[simp]
theorem coe_componentPull {X Y : D.Obj} (f : X ⟶ Y) (q : ℕ)
    (x : OrlikSolomon.diagonalGrading (T.grading Y) q) :
    (componentPull T f q x : T.obj X) = T.pull f x := rfl

/-- Pullback by the identity is the identity on every component. -/
@[simp]
theorem componentPull_id (X : D.Obj) (q : ℕ) :
    componentPull T (𝟙 X) q = LinearMap.id := by
  ext x
  exact T.pull_id X x

/-- Component pullbacks compose in the contravariant order. -/
@[simp]
theorem componentPull_comp {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    componentPull T (f ≫ g) q = (componentPull T f q).comp (componentPull T g q) := by
  ext x
  exact T.pull_comp f g x

/-- Actual scheme pullback on the diagonal algebra, assembled from its component maps.
The definition uses the existing direct-sum algebra universal property. -/
def diagonalPull {X Y : D.Obj} (f : X ⟶ Y) : diagonal T Y →ₐ[R] diagonal T X :=
  DirectSum.toAlgebra R (fun q ↦ ↥(OrlikSolomon.diagonalGrading (T.grading Y) q))
    (fun q ↦ (DirectSum.lof R ℕ _ q).comp (componentPull T f q))
    (by
      change DirectSum.of _ 0 _ = 1
      rw [DirectSum.one_def]
      congr 1
      apply Subtype.ext
      exact map_one (T.pull f))
    (by
      intro i j x y
      change DirectSum.of _ (i + j) _ = DirectSum.of _ i _ * DirectSum.of _ j _
      rw [DirectSum.of_mul_of]
      congr 1
      apply Subtype.ext
      exact map_mul (T.pull f) (x : T.obj Y) (y : T.obj Y))

/-- On a homogeneous summand the diagonal pullback is the original component pullback. -/
@[simp]
theorem diagonalPull_of {X Y : D.Obj} (f : X ⟶ Y) (q : ℕ)
    (x : OrlikSolomon.diagonalGrading (T.grading Y) q) :
    diagonalPull T f (DirectSum.of _ q x) =
      DirectSum.of _ q (componentPull T f q x) := by
  change DirectSum.toModule R ℕ _
    (fun q ↦ (DirectSum.lof R ℕ _ q).comp (componentPull T f q))
    (DirectSum.lof R ℕ _ q x) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- Pullback by the identity is the identity on the actual diagonal algebra. -/
@[simp]
theorem diagonalPull_id (X : D.Obj) : diagonalPull T (𝟙 X) = AlgHom.id R _ := by
  apply DirectSum.algHom_ext
  intro q x
  simp

/-- Actual diagonal pullbacks compose in the contravariant order. -/
@[simp]
theorem diagonalPull_comp {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    diagonalPull T (f ≫ g) = (diagonalPull T f).comp (diagonalPull T g) := by
  apply DirectSum.algHom_ext
  intro q x
  simp

/-- Summing the diagonal classes into total cohomology commutes with actual pullback. -/
theorem coeAlgHom_diagonalPull {X Y : D.Obj} (f : X ⟶ Y) (x : diagonal T Y) :
    DirectSum.coeAlgHom (OrlikSolomon.diagonalGrading (T.grading X))
        (diagonalPull T f x) =
      T.pull f (DirectSum.coeAlgHom (OrlikSolomon.diagonalGrading (T.grading Y)) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of q x => simp
  | add x y hx hy => simp [hx, hy]

/-- Logarithmic naturality for both ordered marking generators on the actual open schemes.
-/
theorem _root_.OrlikSolomon.HyperplaneGT.Marking.pull_logClass_targetUnit
    (w : HyperplaneGT.Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) (a : Fin 2) :
    T.pull (w.schemeMap D hw) (T.logClass (schemeMarkingTargetUnit D a)) =
      T.logClass (Geometric.complementUnit A
        (w.function - AffineMap.const k _ (algebraMap k₀ k (a.val : k₀)))
        (hw.covers_fiber a)) := by
  rw [T.pull_logClass, w.schemeMap_targetUnit]

end OrlikSolomon.HyperplaneGT.Cohomology
