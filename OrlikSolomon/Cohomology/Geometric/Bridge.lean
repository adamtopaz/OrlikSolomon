/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Bridge
public import OrlikSolomon.Cohomology.Geometric.Transport

/-!
# The geometric supports-and-purity bridge

`Geometric.DegreewiseTheory` and `Geometric.SupportsAndPurity` give the degreewise inputs on
any admissible domain, including non-affine schemes. `ofSupportsAndPurity` forms all bidegrees'
external direct sum. Its Gysin map is purity followed by forgetting supports; its residue is the
localization boundary followed by inverse purity. The shared category-independent bridge proves
all total exactness, shifts, coefficient linearity, naturality and the right projection formula.
Restriction and affine transport commute with the construction.

## Hand check against Betti cohomology

For a field embedded in `ℂ`, use the separated finite-type domain and any commutative ring `R`,
including `ZMod 2` and the zero ring. Take `B = R[t,t⁻¹]`, with `ℬ w = R t^w`, and
`H^{p,w}(X) = H^p(X(ℂ); R) t^w`. Cup product and ordinary pullback supply `GRing`, `GAlgebra`,
graded commutativity, coefficients and functoriality. A point has only degree-zero cohomology.
The homotopy `(x,z,s) ↦ (x,sz)` supplies affine-line invariance.

For a pair, relative cohomology `H^p(X(ℂ), U(ℂ); R) t^w` supplies supported groups, forgetting,
the connecting homomorphism and the three degreewise exactness statements. The Thom class of the
complex normal line, times `t`, supplies purity of shift `(2,1)`. A transverse pair map identifies
the normal lines and preserves this orientation, with no ambient flatness assumption. Relative
cup product on the right gives `forget_mul` and `purity_mul`; the Thom degree is even. On closed
ambient cochains, `d(ã ∪ b) = dã ∪ b`, giving `boundary_mul` with no sign. These are interpretations
of every input field, not a formal construction of singular cohomology in Lean.

Blueprint: `def:geo-supports`, `thm:geo-bridge`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite DirectSum

universe u v w z t

namespace OrlikSolomon.Geometric

/-- Degreewise cohomology on an admissible scheme domain, with indexed cup products,
contravariant pullback, coefficients, and the degreewise point and affine-line conditions.
Localization and purity are separate inputs. Blueprint: `def:geo-supports`. -/
structure DegreewiseTheory {k : Type u} [CommRing k] (D : SmoothDomain k) {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B] (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] where
  /-- The group `H^{p,w}(X)`. -/
  H (X : D.Obj) : ℤ × ℤ → Type z
  /-- Cohomology groups are additive abelian groups. -/
  [addCommGroup : ∀ X i, AddCommGroup (H X i)]
  /-- Each cohomology group is an `R`-module. -/
  [module : ∀ X i, Module R (H X i)]
  /-- The cup products, with their associative unital graded ring laws. -/
  [gRing : ∀ X, GRing (H X)]
  /-- Cup products are compatible with the `R`-module structures. -/
  [gAlgebra : ∀ X, GAlgebra R (H X)]
  /-- The structural coefficient map in each weight. -/
  coeff (X : D.Obj) (w : ℤ) : ℬ w →ₗ[R] H X (0, w)
  /-- The coefficient maps preserve the unit. -/
  coeff_one (X : D.Obj) :
    coeff X 0 (GradedMonoid.GOne.one (A := fun w ↦ ℬ w)) = GradedMonoid.GOne.one
  /-- The coefficient maps preserve products. -/
  coeff_mul (X : D.Obj) {w v : ℤ} (b : ℬ w) (c : ℬ v) :
    coeff X (w + v) (GradedMonoid.GMul.mul (A := fun w ↦ ℬ w) b c) =
      GradedMonoid.GMul.mul (coeff X w b) (coeff X v c)
  /-- The structural map identifies `R` with `ℬ 0`. -/
  bijective_algebraMap_gradeZero : Function.Bijective (algebraMap R (ℬ 0))
  /-- Cup products supercommute; a sigma equality records the change from `i+j` to `j+i`. -/
  graded_comm (X : D.Obj) {i j : ℤ × ℤ} (x : H X i) (y : H X j) :
    GradedMonoid.mk (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.mk (j + i) ((i.1 * j.1).negOnePow • GradedMonoid.GMul.mul y x)
  /-- Pullback in each bidegree, contravariantly along a scheme morphism. -/
  pull {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) : H Y i →ₗ[R] H X i
  /-- Pullback along an identity is the identity. -/
  pull_id (X : D.Obj) (i : ℤ × ℤ) (x : H X i) : pull (𝟙 X) i x = x
  /-- Pullback respects composition. -/
  pull_comp {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ × ℤ) (x : H Z i) :
    pull (f ≫ g) i x = pull f i (pull g i x)
  /-- Pullback preserves the unit. -/
  pull_one {X Y : D.Obj} (f : X ⟶ Y) :
    pull f 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one
  /-- Pullback preserves cup products. -/
  pull_mul {X Y : D.Obj} (f : X ⟶ Y) {i j : ℤ × ℤ} (x : H Y i) (y : H Y j) :
    pull f (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (pull f i x) (pull f j y)
  /-- Pullback preserves homogeneous coefficients. -/
  pull_coeff {X Y : D.Obj} (f : X ⟶ Y) (w : ℤ) (b : ℬ w) :
    pull f (0, w) (coeff Y w b) = coeff X w b
  /-- At the point, the coefficient map is bijective in every weight. -/
  bijective_coeff_point (w : ℤ) : Function.Bijective (coeff D.point w)
  /-- The point has no cohomology in nonzero cohomological degrees. -/
  eq_zero_point {p w : ℤ} (hp : p ≠ 0) (x : H D.point (p, w)) : x = 0
  /-- Affine-line invariance in every bidegree. -/
  bijective_pullback_affineLine (X : D.Obj) (i : ℤ × ℤ) :
    Function.Bijective (pull (D.prodAffineLineFst X) i)

namespace DegreewiseTheory

attribute [instance] addCommGroup module gRing gAlgebra

variable {k : Type u} [CommRing k] {D : SmoothDomain k} {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (E : DegreewiseTheory.{u, v, w, z} D ℬ)

/-- The covariant core on the opposite of the scheme domain. -/
@[implicit_reducible]
def toCore : CategoricalDegreewiseTheory D.Objᵒᵖ (op D.point)
    (fun X ↦ op (D.prodAffineLine X.unop))
    (fun X ↦ (D.prodAffineLineFst X.unop).op) ℬ where
  H X := E.H X.unop
  addCommGroup X := E.addCommGroup X.unop
  module X := E.module X.unop
  gRing X := E.gRing X.unop
  gAlgebra X := E.gAlgebra X.unop
  coeff X := E.coeff X.unop
  coeff_one X := E.coeff_one X.unop
  coeff_mul X := E.coeff_mul X.unop
  bijective_algebraMap_gradeZero := E.bijective_algebraMap_gradeZero
  graded_comm X := E.graded_comm X.unop
  map f := E.pull f.unop
  map_id X := E.pull_id X.unop
  map_comp f g := E.pull_comp g.unop f.unop
  map_one f := E.pull_one f.unop
  map_mul f := E.pull_mul f.unop
  map_coeff f := E.pull_coeff f.unop
  bijective_coeff_point := E.bijective_coeff_point
  eq_zero_point := E.eq_zero_point
  bijective_map_line X := E.bijective_pullback_affineLine X.unop

/-- Total cohomology, summed over all integer bidegrees. -/
abbrev Total (X : D.Obj) := ⨁ i, E.H X i

/-- Inclusion of a degreewise cohomology group in the total algebra. -/
abbrev incl (X : D.Obj) (i : ℤ × ℤ) : E.H X i →ₗ[R] E.Total X :=
  DirectSum.lof R _ (E.H X) i

instance algebra (X : D.Obj) : Algebra B (E.Total X) := E.toCore.algebra (op X)
instance isScalarTower (X : D.Obj) : IsScalarTower R B (E.Total X) :=
  E.toCore.isScalarTower (op X)

/-- The image grading on the total algebra. -/
def grading (X : D.Obj) : ℤ × ℤ → Submodule R (E.Total X) := E.toCore.grading (op X)

instance gradedAlgebra (X : D.Obj) : GradedAlgebra (E.grading X) :=
  E.toCore.gradedAlgebra (op X)

/-- Multiplication of summands is the original indexed cup product. -/
@[simp]
lemma incl_mul_incl (X : D.Obj) {i j : ℤ × ℤ} (x : E.H X i) (y : E.H X j) :
    E.incl X i x * E.incl X j y = E.incl X (i + j) (GradedMonoid.GMul.mul x y) :=
  E.toCore.incl_mul_incl (op X) x y

/-- A homogeneous coefficient maps to its degreewise coefficient class. -/
@[simp]
lemma algebraMap_coe (X : D.Obj) {w : ℤ} (b : ℬ w) :
    algebraMap B (E.Total X) (b : B) = E.incl X (0, w) (E.coeff X w b) :=
  E.toCore.algebraMap_coe (op X) b

/-- The degreewise pullback of an isomorphism is a linear equivalence. -/
def pullIso {X Y : D.Obj} (e : X ≅ Y) (i : ℤ × ℤ) : E.H Y i ≃ₗ[R] E.H X i :=
  E.toCore.mapIso e.op i

@[simp] lemma pullIso_apply {X Y : D.Obj} (e : X ≅ Y) (i : ℤ × ℤ) (x : E.H Y i) :
    E.pullIso e i x = E.pull e.hom i x := rfl

/-- Restriction of all degreewise data along an inclusion of admissible domains. -/
def restrict {D₁ : SmoothDomain k} (h : D₁ ≤ D) : DegreewiseTheory D₁ ℬ where
  H X := E.H ((ObjectProperty.ιOfLE h).obj X)
  addCommGroup X := E.addCommGroup _
  module X := E.module _
  gRing X := E.gRing _
  gAlgebra X := E.gAlgebra _
  coeff X := E.coeff _
  coeff_one X := E.coeff_one _
  coeff_mul X := E.coeff_mul _
  bijective_algebraMap_gradeZero := E.bijective_algebraMap_gradeZero
  graded_comm X := E.graded_comm _
  pull f := E.pull ((ObjectProperty.ιOfLE h).map f)
  pull_id X i x := by rw [CategoryTheory.Functor.map_id]; exact E.pull_id _ _ _
  pull_comp f g i x := by rw [CategoryTheory.Functor.map_comp]; exact E.pull_comp _ _ _ _
  pull_one f := E.pull_one _
  pull_mul f := E.pull_mul _
  pull_coeff f := E.pull_coeff _
  bijective_coeff_point := E.bijective_coeff_point
  eq_zero_point := E.eq_zero_point
  bijective_pullback_affineLine X := E.bijective_pullback_affineLine _

@[simp]
lemma restrict_H {D₁ : SmoothDomain k} (h : D₁ ≤ D) (X : D₁.Obj) (i : ℤ × ℤ) :
    (E.restrict h).H X i = E.H ((ObjectProperty.ιOfLE h).obj X) i := rfl

@[simp]
lemma restrict_pull {D₁ : SmoothDomain k} (h : D₁ ≤ D) {X Y : D₁.Obj}
    (f : X ⟶ Y) (i : ℤ × ℤ) (x : (E.restrict h).H Y i) :
    dsimp% (E.restrict h).pull f i x = E.pull ((ObjectProperty.ιOfLE h).map f) i x := rfl

/-- Evaluation on spectra supplies the old degreewise algebraic inputs. The point and line
conditions use the canonical scheme isomorphisms, with no user-supplied affine comparison. -/
def toAlgebraic : OrlikSolomon.DegreewiseTheory k ℬ where
  H A := E.H (D.spec A)
  addCommGroup A := E.addCommGroup _
  module A := E.module _
  gRing A := E.gRing _
  gAlgebra A := E.gAlgebra _
  coeff A := E.coeff _
  coeff_one A := E.coeff_one _
  coeff_mul A := E.coeff_mul _
  bijective_algebraMap_gradeZero := E.bijective_algebraMap_gradeZero
  graded_comm A := E.graded_comm _
  map f := E.pull (D.specFunctor.map f).unop
  map_id A i x := by rw [CategoryTheory.Functor.map_id]; exact E.pull_id _ _ _
  map_comp f g i x := by rw [CategoryTheory.Functor.map_comp]; exact E.pull_comp _ _ _ _
  map_one f := E.pull_one _
  map_mul f := E.pull_mul _
  map_coeff f := E.pull_coeff _
  bijective_coeff_point w := by
    have h := (E.pullIso D.specPointIso (0, w)).bijective.comp (E.bijective_coeff_point w)
    change Function.Bijective (fun b ↦ E.pull D.specPointIso.hom (0, w)
      (E.coeff D.point w b)) at h
    simpa only [E.pull_coeff] using h
  eq_zero_point hp x := by
    apply (E.pullIso D.specPointIso.symm _).injective
    rw [map_zero]
    exact E.eq_zero_point hp _
  bijective_map_polynomialC A i := by
    have h := (E.pullIso (D.specPolynomialIso A) i).bijective.comp
      (E.bijective_pullback_affineLine (D.spec A) i)
    change Function.Bijective (fun x ↦ E.pull (D.specPolynomialIso A).hom i
      (E.pull (D.prodAffineLineFst (D.spec A)) i x)) at h
    simpa only [← E.pull_comp, D.specPolynomialIso_hom_prodAffineLineFst] using h

@[simp]
lemma toAlgebraic_H (A : SmoothAlg k) (i : ℤ × ℤ) :
    E.toAlgebraic.H A i = E.H (D.spec A) i := rfl

@[simp]
lemma toAlgebraic_map {A A' : SmoothAlg k} (f : A ⟶ A') (i : ℤ × ℤ)
    (x : E.toAlgebraic.H A i) :
    dsimp% E.toAlgebraic.map f i x = E.pull (D.specFunctor.map f).unop i x := rfl

end DegreewiseTheory

/-- The covariant pair diagram on the opposite geometric pair category. -/
def geometricPairDiagram {k : Type u} [CommRing k] (D : SmoothDomain k) :
    CovariantPairDiagram D.Objᵒᵖ (DivisorPair D)ᵒᵖ where
  ambient := { obj P := op P.unop.ambient, map f := f.unop.ambient.op }
  closed := { obj P := op P.unop.closed, map f := f.unop.closed.op }
  compl := { obj P := op P.unop.compl, map f := f.unop.compl.op }
  i := { app P := P.unop.i.op, naturality _ _ f := congrArg Quiver.Hom.op f.unop.i_comp }
  j := { app P := P.unop.j.op, naturality _ _ f := congrArg Quiver.Hom.op f.unop.j_comp }

/-- Degreewise localization with supports, oriented purity, transverse contravariant pullback
and right mixed products on geometric divisor pairs. Only the degreewise localization sequence
is input; total exactness, Gysin and residue are conclusions. Blueprint: `def:geo-supports`. -/
structure SupportsAndPurity {k : Type u} [CommRing k] {D : SmoothDomain k}
    {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (E : DegreewiseTheory.{u, v, w, z} D ℬ) where
  /-- Supported cohomology `H_D^{p,w}(X)`. -/
  support (P : DivisorPair D) : ℤ × ℤ → Type t
  /-- Supported cohomology groups are additive abelian groups. -/
  [addCommGroup : ∀ P i, AddCommGroup (support P i)]
  /-- Supported cohomology groups are `R`-modules. -/
  [module : ∀ P i, Module R (support P i)]
  /-- The support-forgetting map. -/
  forget (P : DivisorPair D) (i : ℤ × ℤ) : support P i →ₗ[R] E.H P.ambient i
  /-- The localization boundary, raising cohomological degree by one. -/
  boundary (P : DivisorPair D) (i : ℤ × ℤ) :
    E.H P.compl i →ₗ[R] support P (i + (1, 0))
  /-- Oriented purity of bidegree `(2,1)`. -/
  purity (P : DivisorPair D) (i : ℤ × ℤ) : E.H P.closed i ≃ₗ[R] support P (i + (2, 1))
  /-- Exactness at ambient cohomology. -/
  exact_forget_pull (P : DivisorPair D) (i : ℤ × ℤ) :
    Function.Exact (forget P i) (E.pull P.j i)
  /-- Exactness at open cohomology. -/
  exact_pull_boundary (P : DivisorPair D) (i : ℤ × ℤ) :
    Function.Exact (E.pull P.j i) (boundary P i)
  /-- Exactness at supported cohomology. -/
  exact_boundary_forget (P : DivisorPair D) (i : ℤ × ℤ) :
    Function.Exact (boundary P i) (forget P (i + (1, 0)))
  /-- Contravariant transverse pullback of supported classes. -/
  supportPull {P Q : DivisorPair D} (f : P ⟶ Q) (i : ℤ × ℤ) :
    support Q i →ₗ[R] support P i
  /-- Forgetting supports commutes with transverse pullback. -/
  forget_natural {P Q : DivisorPair D} (f : P ⟶ Q) (i : ℤ × ℤ) (x : support Q i) :
    forget P i (supportPull f i x) = E.pull f.ambient i (forget Q i x)
  /-- The boundary commutes with transverse pullback. -/
  boundary_natural {P Q : DivisorPair D} (f : P ⟶ Q) (i : ℤ × ℤ) (x : E.H Q.compl i) :
    boundary P i (E.pull f.compl i x) = supportPull f (i + (1, 0)) (boundary Q i x)
  /-- Purity commutes with transverse pullback. -/
  purity_natural {P Q : DivisorPair D} (f : P ⟶ Q) (i : ℤ × ℤ) (x : E.H Q.closed i) :
    purity P i (E.pull f.closed i x) = supportPull f (i + (2, 1)) (purity Q i x)
  /-- The right mixed supported/ambient cup product. -/
  supportMul (P : DivisorPair D) (i j : ℤ × ℤ) :
    support P i →ₗ[R] E.H P.ambient j →ₗ[R] support P (i + j)
  /-- Forgetting supports preserves mixed products. -/
  forget_mul (P : DivisorPair D) {i j : ℤ × ℤ}
      (x : support P i) (y : E.H P.ambient j) :
    forget P (i + j) (supportMul P i j x y) = GradedMonoid.GMul.mul (forget P i x) y
  /-- Purity preserves right products with ambient classes, with no sign. -/
  purity_mul (P : DivisorPair D) {i j : ℤ × ℤ} (x : E.H P.closed i) (y : E.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (2, 1))
        (purity P (i + j) (GradedMonoid.GMul.mul x (E.pull P.i j y))) =
      GradedMonoid.mk ((i + (2, 1)) + j) (supportMul P (i + (2, 1)) j (purity P i x) y)
  /-- The boundary projection formula, with the open factor first and no sign. -/
  boundary_mul (P : DivisorPair D) {i j : ℤ × ℤ} (x : E.H P.compl i) (y : E.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (1, 0))
        (boundary P (i + j) (GradedMonoid.GMul.mul x (E.pull P.j j y))) =
      GradedMonoid.mk ((i + (1, 0)) + j)
        (supportMul P (i + (1, 0)) j (boundary P i x) y)

namespace SupportsAndPurity

attribute [instance] addCommGroup module

variable {k : Type u} [CommRing k] {D : SmoothDomain k} {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {E : DegreewiseTheory.{u, v, w, z} D ℬ} (S : SupportsAndPurity.{u, v, w, z, t} E)

/-- The covariant supports-and-purity core on opposite geometric pairs. -/
def toCore : CategoricalSupportsAndPurity E.toCore (geometricPairDiagram D) where
  support P := S.support P.unop
  addCommGroup P := S.addCommGroup P.unop
  module P := S.module P.unop
  forget P := S.forget P.unop
  boundary P := S.boundary P.unop
  purity P := S.purity P.unop
  exact_forget_map P := S.exact_forget_pull P.unop
  exact_map_boundary P := S.exact_pull_boundary P.unop
  exact_boundary_forget P := S.exact_boundary_forget P.unop
  supportMap f := S.supportPull f.unop
  forget_natural f := S.forget_natural f.unop
  boundary_natural f := S.boundary_natural f.unop
  purity_natural f := S.purity_natural f.unop
  supportMul P := S.supportMul P.unop
  forget_mul P := S.forget_mul P.unop
  purity_mul P := S.purity_mul P.unop
  boundary_mul P := S.boundary_mul P.unop

/-- Total supported cohomology, summed over all bidegrees. -/
abbrev Total (P : DivisorPair D) := ⨁ i, S.support P i

/-- Inclusion of a supported bidegree into its total direct sum. -/
abbrev incl (P : DivisorPair D) (i : ℤ × ℤ) : S.support P i →ₗ[R] S.Total P :=
  DirectSum.lof R _ (S.support P) i

/-- Total support-forgetting. -/
def forgetTotal (P : DivisorPair D) : S.Total P →ₗ[R] E.Total P.ambient :=
  S.toCore.forgetTotal (op P)

/-- The total localization boundary. -/
def boundaryTotal (P : DivisorPair D) : E.Total P.compl →ₗ[R] S.Total P :=
  S.toCore.boundaryTotal (op P)

/-- The shifted direct sum of the oriented purity equivalences. -/
def purityTotal (P : DivisorPair D) : E.Total P.closed ≃ₗ[R] S.Total P :=
  S.toCore.purityTotal (op P)

/-- Gysin is purity followed by support-forgetting, with derived `B`-linearity. -/
def gysin (P : DivisorPair D) : E.Total P.closed →ₗ[B] E.Total P.ambient :=
  S.toCore.gysin (op P)

/-- Residue is the boundary followed by inverse purity, with derived `B`-linearity. -/
def residue (P : DivisorPair D) : E.Total P.compl →ₗ[B] E.Total P.closed :=
  S.toCore.residue (op P)

/-- Restriction of all support data and purity along an inclusion of admissible domains. -/
def restrict {D₁ : SmoothDomain k} (h : D₁ ≤ D) : SupportsAndPurity (E.restrict h) where
  support P := S.support (DivisorPair.ofLE h P)
  addCommGroup P := S.addCommGroup (DivisorPair.ofLE h P)
  module P := S.module (DivisorPair.ofLE h P)
  forget P := S.forget (DivisorPair.ofLE h P)
  boundary P := S.boundary (DivisorPair.ofLE h P)
  purity P := S.purity (DivisorPair.ofLE h P)
  exact_forget_pull P := S.exact_forget_pull (DivisorPair.ofLE h P)
  exact_pull_boundary P := S.exact_pull_boundary (DivisorPair.ofLE h P)
  exact_boundary_forget P := S.exact_boundary_forget (DivisorPair.ofLE h P)
  supportPull f := S.supportPull ((DivisorPair.functorOfLE h).map f)
  forget_natural f := S.forget_natural ((DivisorPair.functorOfLE h).map f)
  boundary_natural f := S.boundary_natural ((DivisorPair.functorOfLE h).map f)
  purity_natural f := S.purity_natural ((DivisorPair.functorOfLE h).map f)
  supportMul P := S.supportMul (DivisorPair.ofLE h P)
  forget_mul P := S.forget_mul (DivisorPair.ofLE h P)
  purity_mul P := S.purity_mul (DivisorPair.ofLE h P)
  boundary_mul P := S.boundary_mul (DivisorPair.ofLE h P)

/-- Evaluation on spectrum pairs supplies the old supports-and-purity package. -/
def toAlgebraic : OrlikSolomon.SupportsAndPurity E.toAlgebraic where
  support P := S.support (DivisorPair.spec D P)
  addCommGroup P := S.addCommGroup (DivisorPair.spec D P)
  module P := S.module (DivisorPair.spec D P)
  forget P := S.forget (DivisorPair.spec D P)
  boundary P := S.boundary (DivisorPair.spec D P)
  purity P := S.purity (DivisorPair.spec D P)
  exact_forget_map P := S.exact_forget_pull (DivisorPair.spec D P)
  exact_map_boundary P := S.exact_pull_boundary (DivisorPair.spec D P)
  exact_boundary_forget P := S.exact_boundary_forget (DivisorPair.spec D P)
  supportMap f := S.supportPull (DivisorPair.specMap D f)
  forget_natural f := S.forget_natural (DivisorPair.specMap D f)
  boundary_natural f := S.boundary_natural (DivisorPair.specMap D f)
  purity_natural f := S.purity_natural (DivisorPair.specMap D f)
  supportMul P := S.supportMul (DivisorPair.spec D P)
  forget_mul P := S.forget_mul (DivisorPair.spec D P)
  purity_mul P := S.purity_mul (DivisorPair.spec D P)
  boundary_mul P := S.boundary_mul (DivisorPair.spec D P)

@[simp]
lemma restrict_support {D₁ : SmoothDomain k} (h : D₁ ≤ D) (P : DivisorPair D₁) (i : ℤ × ℤ) :
    (S.restrict h).support P i = S.support (DivisorPair.ofLE h P) i := rfl

@[simp]
lemma toAlgebraic_support (P : OrlikSolomon.DivisorPair k) (i : ℤ × ℤ) :
    S.toAlgebraic.support P i = S.support (DivisorPair.spec D P) i := rfl

@[simp]
lemma forgetTotal_incl (P : DivisorPair D) (i : ℤ × ℤ) (x : S.support P i) :
    S.forgetTotal P (S.incl P i x) = E.incl P.ambient i (S.forget P i x) :=
  S.toCore.forgetTotal_incl (op P) i x

@[simp]
lemma boundaryTotal_incl (P : DivisorPair D) (i : ℤ × ℤ) (x : E.H P.compl i) :
    S.boundaryTotal P (E.incl P.compl i x) = S.incl P (i + (1, 0)) (S.boundary P i x) :=
  S.toCore.boundaryTotal_incl (op P) i x

@[simp]
lemma purityTotal_incl (P : DivisorPair D) (i : ℤ × ℤ) (x : E.H P.closed i) :
    S.purityTotal P (E.incl P.closed i x) = S.incl P (i + (2, 1)) (S.purity P i x) :=
  S.toCore.purityTotal_incl (op P) i x

end SupportsAndPurity

variable {k : Type u} [CommRing k] {D : SmoothDomain k} {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  (E : DegreewiseTheory.{u, v, w, z} D ℬ) (S : SupportsAndPurity.{u, v, w, z, t} E)

/-- Degreewise products, localization and oriented purity give an ordinary theory on the entire
admissible domain, by the common direct-sum construction. Blueprint: `thm:geo-bridge`. -/
@[implicit_reducible]
def ofSupportsAndPurity : OrdinaryTheory D ℬ where
  bijective_algebraMap_gradeZero := E.bijective_algebraMap_gradeZero
  C := E.toCore.functor
  algebra X := inferInstanceAs (Algebra R (E.Total X))
  isScalarTower X := E.isScalarTower X
  grading := E.grading
  gradedAlgebra X := E.gradedAlgebra X
  algebraMap_mem_grading X := E.toCore.algebraMap_mem_grading (op X)
  isHomogeneousOfShift_map f := E.toCore.isHomogeneousOfShift_mapTotal f.op
  isGradedCommutative X := E.toCore.isGradedCommutative (op X)
  bijective_algebraMap_point := E.toCore.bijective_coeffMap_point
  eq_zero_of_mem_grading_point := E.toCore.eq_zero_of_mem_grading_point
  bijective_pullback_affineLine X := E.toCore.bijective_mapTotal_line (op X)
  gysin := S.gysin
  residue := S.residue
  isHomogeneousOfShift_gysin P := S.toCore.isHomogeneousOfShift_gysinR (op P)
  isHomogeneousOfShift_residue P := S.toCore.isHomogeneousOfShift_residueR (op P)
  exact_gysin_map P := S.toCore.exact_gysinR_map (op P)
  exact_map_residue P := S.toCore.exact_map_residueR (op P)
  exact_residue_gysin P := S.toCore.exact_residueR_gysinR (op P)
  gysin_map f := S.toCore.gysinR_natural f.op
  residue_map f := S.toCore.residueR_natural f.op
  residue_mul_map P α _ β := S.toCore.residueR_mul_map (op P) α β

/-- Total pullback restricts to the supplied degreewise pullback. -/
@[simp]
lemma ofSupportsAndPurity_pull_incl {X Y : D.Obj} (f : X ⟶ Y) (i : ℤ × ℤ) (x : E.H Y i) :
    (ofSupportsAndPurity E S).pull f (E.incl Y i x) = E.incl X i (E.pull f i x) :=
  E.toCore.mapTotal_incl f.op i x

/-- The Gysin formula in terms of total oriented purity and support-forgetting. -/
lemma ofSupportsAndPurity_gysin_apply (P : DivisorPair D) (x : E.Total P.closed) :
    (ofSupportsAndPurity E S).gysin P x = S.forgetTotal P (S.purityTotal P x) := rfl

/-- The residue formula in terms of total boundary and inverse purity. -/
lemma ofSupportsAndPurity_residue_apply (P : DivisorPair D) (x : E.Total P.compl) :
    (ofSupportsAndPurity E S).residue P x = (S.purityTotal P).symm (S.boundaryTotal P x) := rfl

/-- The constructed grading is the image grading on the original direct sum. -/
@[simp]
lemma ofSupportsAndPurity_grading (X : D.Obj) (i : ℤ × ℤ) :
    (ofSupportsAndPurity E S).grading X i = E.grading X i := rfl

/-- On one summand, Gysin is the supplied degreewise purity followed by support-forgetting. -/
@[simp]
lemma ofSupportsAndPurity_gysin_incl (P : DivisorPair D) (i : ℤ × ℤ) (x : E.H P.closed i) :
    (ofSupportsAndPurity E S).gysin P (E.incl P.closed i x) =
      E.incl P.ambient (i + (2, 1)) (S.forget P (i + (2, 1)) (S.purity P i x)) :=
  S.toCore.gysin_incl (op P) i x

/-- Purity identifies the constructed residue with the original localization boundary. -/
@[simp]
lemma ofSupportsAndPurity_purity_residue (P : DivisorPair D) (x : E.Total P.compl) :
    S.purityTotal P ((ofSupportsAndPurity E S).residue P x) = S.boundaryTotal P x :=
  (S.purityTotal P).apply_symm_apply _

/-- The degreewise Gysin map obtained by taking the indicated total component. -/
def gysinDegreewiseOfSupportsAndPurity (P : DivisorPair D) (i j : ℤ × ℤ) :
    E.H P.closed i →ₗ[R] E.H P.ambient j := S.toCore.gysinDegreewise (op P) i j

/-- The degreewise residue obtained by taking the indicated total component. -/
def residueDegreewiseOfSupportsAndPurity (P : DivisorPair D) (i j : ℤ × ℤ) :
    E.H P.compl i →ₗ[R] E.H P.closed j := S.toCore.residueDegreewise (op P) i j

/-- The constructed Gysin map agrees with its original degreewise component. -/
lemma gysinDegreewiseOfSupportsAndPurity_incl (P : DivisorPair D) {i j : ℤ × ℤ}
    (hij : i + (2, 1) = j) (x : E.H P.closed i) :
    (ofSupportsAndPurity E S).gysin P (E.incl P.closed i x) =
      E.incl P.ambient j (gysinDegreewiseOfSupportsAndPurity E S P i j x) :=
  S.toCore.gysinDegreewise_incl (op P) hij x

/-- The constructed residue agrees with its original degreewise component. -/
lemma residueDegreewiseOfSupportsAndPurity_incl (P : DivisorPair D) {i j : ℤ × ℤ}
    (hij : i + (-1, -1) = j) (x : E.H P.compl i) :
    (ofSupportsAndPurity E S).residue P (E.incl P.compl i x) =
      E.incl P.closed j (residueDegreewiseOfSupportsAndPurity E S P i j x) :=
  S.toCore.residueDegreewise_incl (op P) hij x

/-- Degreewise localization is exact at ambient cohomology on every domain object.
Blueprint: `thm:geo-bridge`. -/
theorem ofSupportsAndPurity_exact_gysin_pull (P : DivisorPair D) {i j : ℤ × ℤ}
    (hij : i + (2, 1) = j) :
    Function.Exact (gysinDegreewiseOfSupportsAndPurity E S P i j) (E.pull P.j j) :=
  S.toCore.exact_gysinDegreewise_map (op P) hij

/-- Degreewise localization is exact at open cohomology on every domain object.
Blueprint: `thm:geo-bridge`. -/
theorem ofSupportsAndPurity_exact_pull_residue (P : DivisorPair D) {i j : ℤ × ℤ}
    (hij : i + (-1, -1) = j) :
    Function.Exact (E.pull P.j i) (residueDegreewiseOfSupportsAndPurity E S P i j) :=
  S.toCore.exact_map_residueDegreewise (op P) hij

/-- Degreewise localization is exact at divisor cohomology on every domain object.
Blueprint: `thm:geo-bridge`. -/
theorem ofSupportsAndPurity_exact_residue_gysin (P : DivisorPair D) {i j l : ℤ × ℤ}
    (hij : i + (-1, -1) = j) (hjl : j + (2, 1) = l) :
    Function.Exact (residueDegreewiseOfSupportsAndPurity E S P i j)
      (gysinDegreewiseOfSupportsAndPurity E S P j l) :=
  S.toCore.exact_residueDegreewise_gysinDegreewise (op P) hij hjl

/-- Restricting the constructed theory agrees with constructing from the restricted inputs. -/
theorem ofSupportsAndPurity_restrict {D₁ : SmoothDomain k} (h : D₁ ≤ D) :
    (ofSupportsAndPurity E S).restrict h = ofSupportsAndPurity (E.restrict h) (S.restrict h) := rfl

/-- Affine duality commutes with the bridge, including Gysin and residue. -/
theorem ofSupportsAndPurity_toAlgebraic :
    (ofSupportsAndPurity E S).toAlgebraic =
      OrlikSolomon.ofSupportsAndPurity E.toAlgebraic S.toAlgebraic := rfl

end OrlikSolomon.Geometric
