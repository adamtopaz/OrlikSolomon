/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.RingQuot
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OrlikSolomon.DeRham.Schemes.Instance
import OrlikSolomon.Geometry.Schemes.PrincipalPair.Certificates
import OrlikSolomon.Interface.Logarithms
import OrlikSolomon.Interface.OSAlgebra
import OrlikSolomon.Interface.ProjectiveComplement
import OrlikSolomon.Presentation.Geometric.Projective

/-!
# The Orlik–Solomon theorem for projective hyperplane arrangements

This file states the main theorem of the project. Let `k` be a field, `𝒜` a nonempty arrangement of
hyperplanes in `ℙⁿ_k`, and `U = ℙⁿ ∖ ⋃ 𝒜` its complement, an open subscheme of `ℙⁿ`. For every
cohomology theory `T` of smooth `k`-schemes satisfying the axioms C1–C5 below, with coefficients in
a commutative ring `B` graded by weight, the cohomology `T(U)` is the projective Orlik–Solomon
algebra of `𝒜` over `B`, through the isomorphism that sends `e_H - e_K` to the logarithmic class of
the function `ℓ_H / ℓ_K`, and which respects the bigradings (`orlikSolomon`). The file is the
interface of the whole library.

## Trust model

The file is arranged in the following order.

* **Part I: definitions** uses only Mathlib, Lean core and earlier declarations of this file.
* The **Proof region**, in `OrlikSolomon.MainTheorem.Proof`, implements the proofs with the
  library. Clear opening and closing comments mark this region **skip this**. Lean requires these
  helpers before the statements that use them.
* **Part II: statements** again uses only Mathlib, Lean core and earlier interface declarations.
* The final **`#print axioms`** commands check each Part II theorem. Only `propext`,
  `Classical.choice` and `Quot.sound` may appear.

To know what the project proves, read Part I, skip the marked Proof region, read Part II and inspect
these axiom reports. Lean's kernel checks the skipped proofs.

Two independent mechanisms enforce the first point.

* The library is imported privately (`import`, not `public import`). Lean's module system rejects
  any public signature or exposed definition body that refers to a privately imported declaration,
  so only the proofs of theorems can use the library. A few theorems of Part I, such as
  `smooth_affineLine_hom` and the certificates of `standardDivisor`, exist for this reason: they
  discharge proof obligations of definitions, and their statements are again Mathlib only.
* `lake exe audit` checks, on the compiled file, that every constant in the type of a declaration of
  Parts I and II, and in the value of such a definition, comes from Mathlib, from Lean core or from
  this file outside the Proof region. A theorem may be cited anywhere, since a proof carries
  no data.
  `lake exe audit --interface` runs this check alone.

## How to audit

Read Part I and check that `CohomologyTheory` asks for the axioms C1–C5 and for nothing that
resembles a conclusion, and that its objects are the intended ones. Skip the Proof region between
its opening and closing marker comments. Read Part II and check its statements. Finally run
`lake exe audit` and inspect the concluding `#print axioms` output, in that order.

## Design decisions

* **Any class of smooth schemes.** A cohomology theory is defined on a class `𝒟` of smooth
  `k`-schemes (`SmoothSchemeClass`) that contains every smooth affine scheme and is closed under
  isomorphisms and under `X ↦ X × 𝔸¹`. The standard reading is `𝒟 = allSmooth k`: a cohomology
  theory on all smooth `k`-schemes. Every theorem holds for every `𝒟`. A theory on a class restricts
  to any smaller class still satisfying the four conditions; `smoothAffine k` asks the least of a
  theory. The complement of a nonempty arrangement is affine, so it belongs to every class.
* **Principal divisors.** The Gysin sequence is asked only for divisors with a global equation; see
  `PrincipalSmoothDivisor`.
* **Hyperplanes are subsets of `ℙⁿ`.** `ℙⁿ` is Mathlib's `Proj k[x₀, …, xₙ]`. A hyperplane is the
  zero locus `V₊(ℓ)` of a nonzero linear form `ℓ`, as a set of points of this scheme, and `ℓ` is
  unique up to a nonzero scalar. Dependence of hyperplanes is linear dependence of equations, which
  does not depend on their choice. The complement is the open subscheme on `ℙⁿ ∖ ⋃ H`.
* **Characterizations, not constructions.** The logarithmic class `[ℓ/ℓ']` appears as `g^* τ`,
  where the class `τ` on `𝔾ₘ` is characterized by its degree and residue (`IsFundamentalClass`) and
  `g : U → 𝔾ₘ` by pulling the coordinate back to `ℓ/ℓ'`. Part II proves that both exist and are
  unique (`existsUnique_fundamentalClass`, `existsUnique_hom_ratio`), so the main theorem is not
  vacuous and no choice is hidden in a definition.
* **Nonempty arrangements only.** For the empty arrangement the complement is `ℙⁿ` itself, whose
  cohomology needs a projective bundle formula, which the axioms do not provide.
* **Edge cases.** `n = 0` is allowed: `ℙ⁰` is a point, its only hyperplane is `V₊(x₀) = ∅`, and the
  theorem says that `T(ℙ⁰) = B`. The coefficients may be the zero ring, and `2` need not be
  invertible: the generators square to zero because the Orlik–Solomon algebra is a quotient of an
  exterior algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w z

namespace OrlikSolomon.MainTheorem

/-! ## Part I: definitions -/

variable {k : Type u} [Field k]

/-! ### Smooth schemes over `k` -/

variable (k) in
/-- The affine line `𝔸¹_k = Spec k[X]`, as a scheme over `Spec k`. -/
def affineLine : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))

variable (k) in
/-- The multiplicative group `𝔾ₘ = Spec k[T, T⁻¹]`, as a scheme over `Spec k`. -/
def multiplicativeGroup : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k[T;T⁻¹])))

variable (k) in
/-- The coordinate `T` of `𝔾ₘ = Spec k[T, T⁻¹]`, as a global function on `𝔾ₘ`. -/
def gmCoordinate : Γ((multiplicativeGroup k).left, ⊤) :=
  (Scheme.ΓSpecIso (.of k[T;T⁻¹])).inv (LaurentPolynomial.T 1)

variable (k) in
/-- `𝔸¹_k` is smooth over `k`. A proof obligation of the definitions below. -/
theorem smooth_affineLine_hom : Smooth (affineLine k).hom :=
  inferInstanceAs (Smooth (Geometric.affineLine k).hom)

variable (k) in
/-- `𝔾ₘ` is smooth over `k`. A proof obligation of the definitions below. -/
theorem smooth_multiplicativeGroup_hom : Smooth (multiplicativeGroup k).hom :=
  inferInstanceAs (Smooth (Geometric.gm k).hom)

variable (k) in
/-- A class of smooth `k`-schemes, on which a cohomology theory is defined. It contains every
smooth affine `k`-scheme, and it is closed under isomorphisms and under `X ↦ X × 𝔸¹`, which is what
the axioms need. The standard example is `allSmooth k`, and the smallest is `smoothAffine k`.
Morphisms between members are all morphisms of `k`-schemes (`Obj`). -/
structure SmoothSchemeClass where
  /-- Membership in the class, a property of schemes over `Spec k`. -/
  property : ObjectProperty (Over (Spec (.of k)))
  /-- (a) The class is closed under isomorphisms of `k`-schemes. -/
  isClosedUnderIsomorphisms : property.IsClosedUnderIsomorphisms
  /-- (b) Every member is smooth over `k`. -/
  smooth_hom : ∀ ⦃X : Over (Spec (.of k))⦄, property X → Smooth X.hom
  /-- (c) Every smooth affine `k`-scheme is a member. -/
  of_isAffine : ∀ X : Over (Spec (.of k)), IsAffine X.left → Smooth X.hom → property X
  /-- (d) The class is closed under `X ↦ X × 𝔸¹`, the fiber product over `Spec k`. -/
  tensor_affineLine : ∀ ⦃X : Over (Spec (.of k))⦄, property X → property (X ⊗ affineLine k)

namespace SmoothSchemeClass

variable (k) in
/-- The class of all smooth `k`-schemes: the standard domain of a cohomology theory. -/
def allSmooth : SmoothSchemeClass k where
  property X := Smooth X.hom
  isClosedUnderIsomorphisms := ⟨fun e (_ : Smooth _) ↦ by
    rw [← Over.w e.inv]
    infer_instance⟩
  smooth_hom _ h := h
  of_isAffine _ _ h := h
  tensor_affineLine X (_ : Smooth X.hom) := by
    have := smooth_affineLine_hom k
    change Smooth (Limits.pullback.fst _ _ ≫ X.hom)
    infer_instance

variable (k) in
/-- The class of smooth affine `k`-schemes, the smallest class. -/
def smoothAffine : SmoothSchemeClass k where
  property X := IsAffine X.left ∧ Smooth X.hom
  isClosedUnderIsomorphisms := ⟨fun e ⟨_, _⟩ ↦ by
    refine ⟨.of_isIso e.inv.left, ?_⟩
    rw [← Over.w e.inv]
    infer_instance⟩
  smooth_hom _ h := h.2
  of_isAffine _ h₁ h₂ := ⟨h₁, h₂⟩
  tensor_affineLine X := fun ⟨_, _⟩ ↦ by
    have := smooth_affineLine_hom k
    have : IsAffine (affineLine k).left := inferInstanceAs (IsAffine (Spec _))
    exact ⟨inferInstanceAs (IsAffine (Limits.pullback _ _)), by
      change Smooth (Limits.pullback.fst _ _ ≫ X.hom)
      infer_instance⟩

variable (𝒟 : SmoothSchemeClass k)

/-- The members of `𝒟`, as a full subcategory of the schemes over `Spec k`: a morphism is any
morphism of `k`-schemes. -/
abbrev Obj : Type (u + 1) := 𝒟.property.FullSubcategory

/-- The point `Spec k`, as a member of `𝒟`. -/
def point : 𝒟.Obj :=
  ⟨𝟙_ (Over (Spec (.of k))), 𝒟.of_isAffine _ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (Smooth (𝟙 _)))⟩

/-- The affine line `𝔸¹_k`, as a member of `𝒟`. -/
def affineLine : 𝒟.Obj :=
  ⟨MainTheorem.affineLine k, 𝒟.of_isAffine _ (inferInstanceAs (IsAffine (Spec _)))
    (smooth_affineLine_hom k)⟩

/-- The multiplicative group `𝔾ₘ`, as a member of `𝒟`. -/
def multiplicativeGroup : 𝒟.Obj :=
  ⟨MainTheorem.multiplicativeGroup k, 𝒟.of_isAffine _ (inferInstanceAs (IsAffine (Spec _)))
    (smooth_multiplicativeGroup_hom k)⟩

/-- The product `X × 𝔸¹` over `Spec k`, as a member of `𝒟`. -/
def prodAffineLine (X : 𝒟.Obj) : 𝒟.Obj :=
  ⟨X.obj ⊗ MainTheorem.affineLine k, 𝒟.tensor_affineLine X.property⟩

/-- The projection `X × 𝔸¹ → X`. -/
def prodAffineLineFst (X : 𝒟.Obj) : 𝒟.prodAffineLine X ⟶ X :=
  ObjectProperty.homMk (CartesianMonoidalCategory.fst _ _)

end SmoothSchemeClass

/-! ### Principal smooth divisors -/

/-- A **principal smooth divisor** in `𝒟`: a smooth divisor `D` of a member `X`, together with a
chosen global equation `eqn` that cuts it out scheme-theoretically, and its complement `U = X ∖ D`.
In other words, a principal effective Cartier divisor with smooth support. `D` and `U` are given as
members of `𝒟` with maps `i : D → X` and `j : U → X`, certified to be the zero scheme and the
non-vanishing locus of `eqn`; `eqn` may be a unit, in which case `D` is empty. General smooth
divisors, which are only locally principal, are not included.

This is the right hypothesis for the axioms C4 and C5.

* The axioms ask for Gysin sequences only for these divisors, which asks *less* of a theory: a
  theory with Gysin sequences for all smooth divisors restricts to these.
* A global equation trivializes the normal bundle of `D`, which is why the Gysin map needs no twist
  and has shift `(2, 1)`. For a general divisor it would need a twist by the normal bundle, and so
  more structure.
* The proof applies the axioms only to such divisors: hyperplanes in affine spaces, and the zero
  section of `X × 𝔸¹` with complement `X × 𝔾ₘ`. It never uses a hyperplane of `ℙⁿ`, which has no
  global equation.
* The Gysin and residue maps do not depend on the choice of equation: two equations differ by a
  unit, and the naturality axioms of C5, applied to the identity maps, which form a
  `PrincipalSmoothDivisor.Hom` between the two choices, show this. -/
structure PrincipalSmoothDivisor (𝒟 : SmoothSchemeClass k) where
  /-- The ambient scheme `X`. -/
  ambient : 𝒟.Obj
  /-- The divisor `D`. -/
  closed : 𝒟.Obj
  /-- The complement `U = X ∖ D`. -/
  compl : 𝒟.Obj
  /-- The inclusion `i : D → X`. -/
  i : closed ⟶ ambient
  /-- The inclusion `j : U → X`. -/
  j : compl ⟶ ambient
  /-- The equation of `D`, a global function on `X`. -/
  eqn : Γ(ambient.obj.left, ⊤)
  /-- The equation is a non-zero-divisor on every open subset of `X`, so `D` is a Cartier
  divisor. On an affine `X` it suffices that `eqn` be a non-zero-divisor of `Γ(X, 𝒪_X)`. -/
  eqn_mem_nonZeroDivisors (V : ambient.obj.left.Opens) :
    ambient.obj.left.presheaf.map (homOfLE le_top).op eqn ∈ nonZeroDivisors Γ(ambient.obj.left, V)
  /-- `i` is a closed immersion. -/
  [isClosedImmersion_i : IsClosedImmersion i.hom.left]
  /-- The ideal sheaf of `D` in `X` is generated by `eqn`: `D` is the zero scheme of `eqn`. -/
  ker_i : i.hom.left.ker = Scheme.IdealSheafData.ofIdealTop (Ideal.span {eqn})
  /-- `j` is an open immersion. -/
  [isOpenImmersion_j : IsOpenImmersion j.hom.left]
  /-- The image of `j` is the open subset of `X` where `eqn` does not vanish. -/
  opensRange_j : j.hom.left.opensRange = ambient.obj.left.basicOpen eqn

/-- A transverse morphism `P → Q` of principal smooth divisors: maps of the ambient schemes, the
divisors and the complements, compatible with `i` and `j`, such that the ambient map pulls the
equation of `Q` back to a unit multiple of the equation of `P`. So `D_P` is the scheme-theoretic
preimage of `D_Q`. This excludes `z ↦ z²` on `𝔸¹`, which pulls the reduced origin back to a double
point. Naturality of the Gysin and residue maps (C5) is asked along these. -/
structure PrincipalSmoothDivisor.Hom {𝒟 : SmoothSchemeClass k}
    (P Q : PrincipalSmoothDivisor 𝒟) where
  /-- The map of ambient schemes. -/
  ambient : P.ambient ⟶ Q.ambient
  /-- The map of divisors. -/
  closed : P.closed ⟶ Q.closed
  /-- The map of complements. -/
  compl : P.compl ⟶ Q.compl
  /-- The square with `i` commutes. -/
  i_comp : P.i ≫ ambient = closed ≫ Q.i
  /-- The square with `j` commutes. -/
  j_comp : P.j ≫ ambient = compl ≫ Q.j
  /-- The ambient map pulls the equation of `Q` back to a unit multiple of that of `P`. -/
  associated_eqn : Associated (ambient.hom.left.appTop Q.eqn) P.eqn

/-! ### Cohomology theories -/

/-- A **cohomology theory** on a class `𝒟` of smooth `k`-schemes, with coefficients in a
commutative `R`-algebra `B` graded by weight, `B = ⨁ ℬ w`. The standard case is
`𝒟 = SmoothSchemeClass.allSmooth k`, a theory on all smooth `k`-schemes; any other class, such as
`SmoothSchemeClass.smoothAffine k`, is allowed too. A theory satisfies the axioms C1–C5 and nothing
else: no field asserts generation by logarithmic classes, a vanishing, a short exact sequence or any
form of the structure theorem.

* C1: each `C(X)` is a `B`-algebra and an internally bigraded ring, `C(X) = ⨁ H^{p,w}(X)`, with
  `ℬ w` in bidegree `(0, w)`, and `R = ℬ 0`. It need not be commutative.
* C2: pullback `f^* = C.map f.op` is a map of `B`-algebras preserving bidegrees, and homogeneous
  classes supercommute, with the sign given by the cohomological degrees.
* C3: `C(Spec k) = B`, in cohomological degree `0`, and pullback along `X × 𝔸¹ → X` is bijective.
* C4: each principal smooth divisor `D ⊆ X` with complement `U` has a Gysin map `C(D) → C(X)` of
  shift `(2, 1)` and a residue `C(U) → C(D)` of shift `(-1, -1)`, forming with `j^*` a long exact
  sequence `⋯ → C(D) → C(X) → C(U) → C(D) → ⋯`. It is not assumed to be short exact.
* C5: these maps commute with transverse pullback, and the residue satisfies the projection formula
  `r(α j^*β) = r(α) i^*β` for `α` of bidegree `(1, 1)`.

These axioms are standard properties of, for example, singular cohomology of smooth complex
varieties with coefficients `R[T, T⁻¹]`, with `T` of weight `1` for the Tate twist. They have
not been verified for singular cohomology in Lean. The verified nonzero example is the affine
de Rham theory of `nonempty_cohomologyTheory`. -/
structure CohomologyTheory (𝒟 : SmoothSchemeClass k) {R : Type v} [CommRing R] {B : Type w}
    [CommRing B] [Algebra R B] (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] where
  /-- C1: the structure map identifies `R` with the weight-zero part `ℬ 0` of `B`. -/
  bijective_algebraMap_gradeZero : Function.Bijective (algebraMap R (ℬ 0))
  /-- C1, C2: the cohomology `C(X)`, contravariant in `X`, as a `B`-algebra. Pullback along
  `f : X → Y` is `C.map f.op : C(Y) → C(X)`. The `B`-action is central, as Mathlib's `Algebra`
  requires. -/
  C : 𝒟.Objᵒᵖ ⥤ AlgCat.{z} B
  /-- C1: each `C(X)` is an `R`-algebra, ... -/
  [algebra (X : 𝒟.Obj) : Algebra R (C.obj (op X))]
  /-- C1: ... through `R → B`. -/
  [isScalarTower (X : 𝒟.Obj) : IsScalarTower R B (C.obj (op X))]
  /-- C1: the piece `H^{p, w}(X)` of `C(X)` in cohomological degree `p` and weight `w`. It is an
  `R`-submodule; multiplication by `ℬ v` changes the weight. -/
  grading (X : 𝒟.Obj) : ℤ × ℤ → Submodule R (C.obj (op X))
  /-- C1: `C(X)` is the internal direct sum of its pieces, compatibly with products. -/
  [gradedAlgebra (X : 𝒟.Obj) : GradedAlgebra (grading X)]
  /-- C1: `B → C(X)` sends `ℬ w` into bidegree `(0, w)`. -/
  algebraMap_mem_grading (X : 𝒟.Obj) {w : ℤ} {b : B} (hb : b ∈ ℬ w) :
    algebraMap B (C.obj (op X)) b ∈ grading X (0, w)
  /-- C2: pullbacks preserve bidegrees. -/
  map_mem_grading {X Y : 𝒟.Obj} (f : X ⟶ Y) {p w : ℤ} {x : C.obj (op Y)}
    (hx : x ∈ grading Y (p, w)) : C.map f.op x ∈ grading X (p, w)
  /-- C2: classes of bidegrees `(p, w)` and `(q, v)` commute up to the sign `(-1)^{pq}`. -/
  mul_comm_of_mem_grading (X : 𝒟.Obj) {p w q v : ℤ} {x y : C.obj (op X)}
    (hx : x ∈ grading X (p, w)) (hy : y ∈ grading X (q, v)) :
    x * y = (p * q).negOnePow • (y * x)
  /-- C3: `B → C(Spec k)` is bijective. -/
  bijective_algebraMap_point : Function.Bijective (algebraMap B (C.obj (op 𝒟.point)))
  /-- C3: `C(Spec k)` is concentrated in cohomological degree `0`. -/
  eq_zero_of_mem_grading_point {p w : ℤ} (hp : p ≠ 0) {x : C.obj (op 𝒟.point)}
    (hx : x ∈ grading 𝒟.point (p, w)) : x = 0
  /-- C3: homotopy invariance, pullback along `X × 𝔸¹ → X` is bijective. -/
  bijective_map_prodAffineLineFst (X : 𝒟.Obj) :
    Function.Bijective (C.map (𝒟.prodAffineLineFst X).op)
  /-- C4: the Gysin map `C(D) → C(X)` of a principal smooth divisor. -/
  gysin (P : PrincipalSmoothDivisor 𝒟) : C.obj (op P.closed) →ₗ[B] C.obj (op P.ambient)
  /-- C4: the residue `C(U) → C(D)` of a principal smooth divisor. -/
  residue (P : PrincipalSmoothDivisor 𝒟) : C.obj (op P.compl) →ₗ[B] C.obj (op P.closed)
  /-- C4: the Gysin map has shift `(2, 1)`. -/
  gysin_mem_grading (P : PrincipalSmoothDivisor 𝒟) {p w : ℤ} {x : C.obj (op P.closed)}
    (hx : x ∈ grading P.closed (p, w)) : gysin P x ∈ grading P.ambient (p + 2, w + 1)
  /-- C4: the residue has shift `(-1, -1)`. -/
  residue_mem_grading (P : PrincipalSmoothDivisor 𝒟) {p w : ℤ} {x : C.obj (op P.compl)}
    (hx : x ∈ grading P.compl (p, w)) : residue P x ∈ grading P.closed (p - 1, w - 1)
  /-- C4: exactness at `C(X)`, `im g = ker j^*`. -/
  exact_gysin_map (P : PrincipalSmoothDivisor 𝒟) : Function.Exact (gysin P) (C.map P.j.op)
  /-- C4: exactness at `C(U)`, `im j^* = ker r`. -/
  exact_map_residue (P : PrincipalSmoothDivisor 𝒟) : Function.Exact (C.map P.j.op) (residue P)
  /-- C4: exactness at `C(D)`, `im r = ker g`. With the two previous fields, a long exact
  sequence, not a short exact one. -/
  exact_residue_gysin (P : PrincipalSmoothDivisor 𝒟) : Function.Exact (residue P) (gysin P)
  /-- C5: the Gysin map commutes with transverse pullback. -/
  gysin_map {P Q : PrincipalSmoothDivisor 𝒟} (f : P.Hom Q) (x : C.obj (op Q.closed)) :
    gysin P (C.map f.closed.op x) = C.map f.ambient.op (gysin Q x)
  /-- C5: the residue commutes with transverse pullback. -/
  residue_map {P Q : PrincipalSmoothDivisor 𝒟} (f : P.Hom Q) (x : C.obj (op Q.compl)) :
    residue P (C.map f.compl.op x) = C.map f.closed.op (residue Q x)
  /-- C5: the projection formula `r(α j^*β) = r(α) i^*β` for `α` of bidegree `(1, 1)`. -/
  residue_mul_map (P : PrincipalSmoothDivisor 𝒟) {α : C.obj (op P.compl)}
    (hα : α ∈ grading P.compl (1, 1)) (β : C.obj (op P.ambient)) :
    residue P (α * C.map P.j.op β) = residue P α * C.map P.i.op β

attribute [instance] CohomologyTheory.algebra CohomologyTheory.isScalarTower
  CohomologyTheory.gradedAlgebra

/-! ### The standard divisor and the fundamental class -/

variable (k) in
/-- A certificate of `standardDivisor`: `X` is a non-zero-divisor on every open of `𝔸¹_k`. -/
theorem standardDivisor_eqn_mem_nonZeroDivisors (V : (Spec (.of k[X])).Opens) :
    (Spec (.of k[X])).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) ∈ nonZeroDivisors Γ(Spec (.of k[X]), V) :=
  (Geometric.isRegularSection_ΓSpecIso_inv_iff _).2 Polynomial.X_mem_nonZeroDivisors V

variable (k) in
/-- A certificate of `standardDivisor`: the origin of `𝔸¹_k`, the image of `X ↦ 0`, is the zero
scheme of `X`. -/
theorem standardDivisor_ker_i :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))).ker =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X}) := by
  refine Geometric.ker_specMap_of_ker_eq _ ?_
  rw [CommRingCat.hom_ofHom, Polynomial.ker_evalRingHom, map_zero, sub_zero]

variable (k) in
/-- A certificate of `standardDivisor`: the image of `𝔾ₘ → 𝔸¹_k` is the locus `X ≠ 0`. -/
theorem standardDivisor_opensRange_j :
    letI := IsOpenImmersion.of_isLocalization (S := k[T;T⁻¹]) (Polynomial.X : k[X])
    (Spec.map (CommRingCat.ofHom (algebraMap k[X] k[T;T⁻¹]))).opensRange =
      (Spec (.of k[X])).basicOpen ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) :=
  Geometric.opensRange_specMap_of_isLocalization _ _ inferInstance

/-- The **standard divisor** `{0} ⊆ 𝔸¹_k`, with complement `𝔾ₘ` and equation the coordinate `X`.
`i : Spec k → 𝔸¹_k` is `Spec` of evaluation at `0`, and `j : 𝔾ₘ → 𝔸¹_k` is `Spec` of the inclusion
`k[X] → k[T, T⁻¹]`, `X ↦ T`. -/
def standardDivisor (𝒟 : SmoothSchemeClass k) : PrincipalSmoothDivisor 𝒟 where
  ambient := 𝒟.affineLine
  closed := 𝒟.point
  compl := 𝒟.multiplicativeGroup
  i := ObjectProperty.homMk <| Over.homMk
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) <| by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext c
      simp
  j := ObjectProperty.homMk <| Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap k[X] k[T;T⁻¹]))) <| by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  eqn := (Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X
  eqn_mem_nonZeroDivisors := standardDivisor_eqn_mem_nonZeroDivisors k
  isClosedImmersion_i := IsClosedImmersion.spec_of_surjective _ fun c ↦ ⟨Polynomial.C c, by simp⟩
  ker_i := standardDivisor_ker_i k
  isOpenImmersion_j := IsOpenImmersion.of_isLocalization (Polynomial.X : k[X])
  opensRange_j := standardDivisor_opensRange_j k

/-- `τ` is a **fundamental class** of `T`: a class on `𝔾ₘ` of bidegree `(1, 1)` whose residue at
the origin is `1`. It is the logarithmic class `[T]` of the coordinate, and it exists and is unique
(`existsUnique_fundamentalClass`). -/
def CohomologyTheory.IsFundamentalClass {𝒟 : SmoothSchemeClass k} {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ) (τ : T.C.obj (op 𝒟.multiplicativeGroup)) : Prop :=
  τ ∈ T.grading 𝒟.multiplicativeGroup (1, 1) ∧ T.residue (standardDivisor 𝒟) τ = 1

/-! ### Projective space and hyperplanes -/

variable (k) in
/-- The grading of `k[x₀, …, xₙ]` by total degree. -/
abbrev degreeGrading (n : ℕ) : ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

variable (k) in
/-- Projective space `ℙⁿ_k = Proj k[x₀, …, xₙ]`, as a scheme over `Spec k` through the degree-zero
part `k` of `k[x₀, …, xₙ]`. -/
def projectiveSpace (n : ℕ) : Over (Spec (.of k)) :=
  Over.mk (Proj.toSpecZero (degreeGrading k n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (degreeGrading k n 0))))

variable {n : ℕ}

/-- `ℓ` is an **equation** of the set `H` of points of `ℙⁿ`: a nonzero linear form whose zero locus
`V₊(ℓ)` is `H`. An equation of `H` is unique up to a nonzero scalar. -/
structure IsEquation (H : Set (projectiveSpace k n).left) (ℓ : MvPolynomial (Fin (n + 1)) k) :
    Prop where
  /-- `ℓ` is a linear form. -/
  isHomogeneous : ℓ.IsHomogeneous 1
  /-- `ℓ` is not zero. -/
  ne_zero : ℓ ≠ 0
  /-- `H` is the zero locus of `ℓ`, the points whose homogeneous prime contains `ℓ`. -/
  zeroLocus_eq : ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ} = H

variable (k n) in
/-- A **hyperplane** of `ℙⁿ`: a set of points of `ℙⁿ` that has an equation. -/
abbrev Hyperplane : Type u := {H : Set (projectiveSpace k n).left // ∃ ℓ, IsEquation H ℓ}

variable (k n) in
/-- A **projective hyperplane arrangement**: a finite set of hyperplanes of `ℙⁿ`. -/
abbrev HyperplaneArrangement : Type u := Finset (Hyperplane k n)

/-- A list of hyperplanes of `𝒜` is **dependent** if some choice of equations of its members is
linearly dependent over `k`. Since equations are unique up to nonzero scalars, every choice is then
dependent. For a list without repetitions, this says that the intersection has codimension less
than the length of the list. -/
def IsDependent {𝒜 : HyperplaneArrangement k n} (S : List 𝒜) : Prop :=
  ∃ ℓ : Fin S.length → MvPolynomial (Fin (n + 1)) k,
    (∀ j, IsEquation ((S[j] : 𝒜) : Hyperplane k n) (ℓ j)) ∧ ¬ LinearIndependent k ℓ

/-! ### The Orlik–Solomon algebra -/

variable (B : Type w) [CommRing B] (𝒜 : HyperplaneArrangement k n)

/-- The generator `e_H` of the exterior algebra `⋀ B^𝒜`, for a hyperplane `H` of `𝒜`. -/
def exteriorGenerator (H : 𝒜) : ExteriorAlgebra B (𝒜 →₀ B) :=
  ExteriorAlgebra.ι B (Finsupp.single H 1)

/-- The word `e_S = e_{H₁} ⋯ e_{Hₚ}` of a list `S = [H₁, …, Hₚ]`, which is `1` for `S = []`. -/
def exteriorWord (S : List 𝒜) : ExteriorAlgebra B (𝒜 →₀ B) :=
  (S.map (exteriorGenerator B 𝒜)).prod

/-- The boundary `∂ e_S = ∑ⱼ (-1)ʲ e_{S ∖ Sⱼ}` of a word, where `S ∖ Sⱼ` omits the letter of index
`j`, counted from `0`. -/
def exteriorWordBoundary (S : List 𝒜) : ExteriorAlgebra B (𝒜 →₀ B) :=
  ∑ j : Fin S.length, (-1 : ℤ) ^ (j : ℕ) • exteriorWord B 𝒜 (S.eraseIdx j)

/-- The relations of the Orlik–Solomon algebra: `∂ e_S = 0` for every dependent list `S` of
hyperplanes without repetitions. -/
def orlikSolomonRel (a b : ExteriorAlgebra B (𝒜 →₀ B)) : Prop :=
  b = 0 ∧ ∃ S : List 𝒜, S.Nodup ∧ IsDependent S ∧ a = exteriorWordBoundary B 𝒜 S

/-- The **Orlik–Solomon algebra** of `𝒜` over `B`: the exterior algebra on generators `e_H`, for
`H ∈ 𝒜`, modulo the two-sided ideal generated by the boundaries of dependent words. It is the
Orlik–Solomon algebra of the central arrangement in `k^{n+1}` of which `𝒜` is the
projectivization. -/
abbrev OrlikSolomonAlgebra : Type (max u w) := RingQuot (orlikSolomonRel B 𝒜)

/-- The generator `e_H` of the Orlik–Solomon algebra. -/
def generator (H : 𝒜) : OrlikSolomonAlgebra B 𝒜 :=
  RingQuot.mkAlgHom B (orlikSolomonRel B 𝒜) (exteriorGenerator B 𝒜 H)

/-- The word `e_S = e_{H₁} ⋯ e_{Hₚ}` in the Orlik–Solomon algebra. -/
def word (S : List 𝒜) : OrlikSolomonAlgebra B 𝒜 :=
  (S.map (generator B 𝒜)).prod

/-- The **projective Orlik–Solomon algebra**: the `B`-subalgebra of the Orlik–Solomon algebra
generated by the differences `e_H - e_K`. For nonempty `𝒜` it is the kernel of `∂`. -/
def projectiveOrlikSolomonAlgebra : Subalgebra B (OrlikSolomonAlgebra B 𝒜) :=
  Algebra.adjoin B (Set.range fun HK : 𝒜 × 𝒜 ↦ generator B 𝒜 HK.1 - generator B 𝒜 HK.2)

/-- The generator `e_H - e_K` of the projective Orlik–Solomon algebra. -/
def projectiveGenerator (H K : 𝒜) : projectiveOrlikSolomonAlgebra B 𝒜 :=
  ⟨generator B 𝒜 H - generator B 𝒜 K, Algebra.subset_adjoin ⟨(H, K), rfl⟩⟩

variable {R : Type v} [CommRing R] [Algebra R B] (ℬ : ℤ → Submodule R B)

/-- The piece of bidegree `i = (p, w)` of the Orlik–Solomon algebra: the `R`-span of the `b e_S`
with `S` of length `p` and `b ∈ ℬ (w - p)`. So `e_H` has bidegree `(1, 1)`, like a logarithmic
class, and `ℬ w` has bidegree `(0, w)`. -/
def orlikSolomonGrading (i : ℤ × ℤ) : Submodule R (OrlikSolomonAlgebra B 𝒜) :=
  Submodule.span R {x | ∃ (S : List 𝒜) (b : B), (S.length : ℤ) = i.1 ∧ b ∈ ℬ (i.2 - i.1) ∧
    x = algebraMap B (OrlikSolomonAlgebra B 𝒜) b * word B 𝒜 S}

/-- The piece of bidegree `i` of the projective Orlik–Solomon algebra: its elements that lie in the
piece of bidegree `i` of the Orlik–Solomon algebra. -/
def projectiveOrlikSolomonGrading (i : ℤ × ℤ) :
    Submodule R (projectiveOrlikSolomonAlgebra B 𝒜) :=
  (orlikSolomonGrading B 𝒜 ℬ i).comap
    ((projectiveOrlikSolomonAlgebra B 𝒜).val.toLinearMap.restrictScalars R)

/-! ### The complement and the ratios of equations -/

variable {B}

/-- The complement `ℙⁿ ∖ ⋃_{H ∈ 𝒜} H`, an open subset of `ℙⁿ`. -/
def complementOpens : (projectiveSpace k n).left.Opens where
  carrier := (⋃ H ∈ 𝒜, (H : Set (projectiveSpace k n).left))ᶜ
  is_open' := by
    rw [isOpen_compl_iff]
    refine 𝒜.finite_toSet.isClosed_biUnion fun H _ ↦ ?_
    obtain ⟨ℓ, hℓ⟩ := H.2
    rw [← hℓ.zeroLocus_eq]
    exact ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The **complement** `U = ℙⁿ ∖ ⋃_{H ∈ 𝒜} H`, the open subscheme of `ℙⁿ` on `complementOpens 𝒜`,
as a scheme over `Spec k`. -/
def complement : Over (Spec (.of k)) :=
  Over.mk ((complementOpens 𝒜).ι ≫ (projectiveSpace k n).hom)

/-- The function `ℓ / ℓ'` on the complement, for a linear form `ℓ` and an equation `ℓ'` of a
hyperplane of `𝒜`. It is the degree-zero fraction `ℓ / ℓ'`, a function on the chart `D₊(ℓ')` of
`ℙⁿ` where `ℓ'` does not vanish, restricted to the complement, which lies in that chart. If `ℓ` is
an equation of a hyperplane of `𝒜` too, it is a unit. -/
def ratio {𝒜 : HyperplaneArrangement k n} {K : Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : ℓ.IsHomogeneous 1) (hℓ' : IsEquation K ℓ') :
    Γ((complement 𝒜).left, ⊤) :=
  (complementOpens 𝒜).ι.appLE (Proj.basicOpen (degreeGrading k n) ℓ') ⊤ (fun x _ h ↦ by
    have hx : x.1 ∉ ⋃ H ∈ 𝒜, (H : Set (projectiveSpace k n).left) := x.2
    have hℓx : x.1 ∈ ProjectiveSpectrum.zeroLocus (degreeGrading k n) {ℓ'} :=
      (ProjectiveSpectrum.mem_zeroLocus _ _ _).2 (Set.singleton_subset_iff.2 h)
    exact hx (Set.mem_biUnion hK (hℓ'.zeroLocus_eq ▸ hℓx)))
    (Proj.awayToSection (degreeGrading k n) ℓ'
      (HomogeneousLocalization.Away.mk (degreeGrading k n) hℓ'.isHomogeneous 1 ℓ
        (by simpa using hℓ)))

/-! ## Proof region — skip this

This private implementation precedes Part II because Lean declarations cannot refer forward.
-/

/- BEGIN PROOF REGION — SKIP THIS; resume at END PROOF REGION below.
Nothing in this region is part of the public statement.
`lake exe audit --interface` enforces the boundary.
-/

namespace Proof

variable {ℬ} {𝒟 : SmoothSchemeClass k} [GradedAlgebra ℬ]

private def affineObject (𝒟 : SmoothSchemeClass k) (X : (Geometric.SmoothDomain.aff k).Obj) :
    𝒟.Obj := ⟨X.obj, 𝒟.of_isAffine _ X.property.1 X.property.2⟩

private def affineInclusion (𝒟 : SmoothSchemeClass k) :
    (Geometric.SmoothDomain.aff k).Obj ⥤ 𝒟.Obj where
  obj := affineObject 𝒟
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def toPrincipal (𝒟 : SmoothSchemeClass k)
    (P : Geometric.DivisorPair (Geometric.SmoothDomain.aff k)) : PrincipalSmoothDivisor 𝒟 where
  ambient := affineObject 𝒟 P.ambient
  closed := affineObject 𝒟 P.closed
  compl := affineObject 𝒟 P.compl
  i := (affineInclusion 𝒟).map P.i
  j := (affineInclusion 𝒟).map P.j
  eqn := P.eqn
  eqn_mem_nonZeroDivisors := P.isRegularSection_eqn
  isClosedImmersion_i := P.isClosedImmersion_i
  ker_i := P.ker_i
  isOpenImmersion_j := P.isOpenImmersion_j
  opensRange_j := P.opensRange_j

private def toPrincipalHom {P Q : Geometric.DivisorPair (Geometric.SmoothDomain.aff k)}
    (f : P ⟶ Q) : (toPrincipal 𝒟 P).Hom (toPrincipal 𝒟 Q) where
  ambient := (affineInclusion 𝒟).map f.ambient
  closed := (affineInclusion 𝒟).map f.closed
  compl := (affineInclusion 𝒟).map f.compl
  i_comp := by
    change (affineInclusion 𝒟).map P.i ≫ (affineInclusion 𝒟).map f.ambient =
      (affineInclusion 𝒟).map f.closed ≫ (affineInclusion 𝒟).map Q.i
    simpa only [Functor.map_comp] using congrArg (affineInclusion 𝒟).map f.i_comp
  j_comp := by
    change (affineInclusion 𝒟).map P.j ≫ (affineInclusion 𝒟).map f.ambient =
      (affineInclusion 𝒟).map f.compl ≫ (affineInclusion 𝒟).map Q.j
    simpa only [Functor.map_comp] using congrArg (affineInclusion 𝒟).map f.j_comp
  associated_eqn := f.associated_eqn

private def affineTheory (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ) :
    Geometric.OrdinaryTheory.{u, v, w, z} (Geometric.SmoothDomain.aff k) ℬ where
  bijective_algebraMap_gradeZero := T.bijective_algebraMap_gradeZero
  C := (affineInclusion 𝒟).op ⋙ T.C
  algebra X := T.algebra ((affineInclusion 𝒟).obj X)
  isScalarTower X := T.isScalarTower ((affineInclusion 𝒟).obj X)
  grading X := T.grading ((affineInclusion 𝒟).obj X)
  gradedAlgebra X := T.gradedAlgebra ((affineInclusion 𝒟).obj X)
  algebraMap_mem_grading X {w} {b} hb :=
    T.algebraMap_mem_grading ((affineInclusion 𝒟).obj X) hb
  isHomogeneousOfShift_map f := by
    intro ⟨p, w⟩ x hx
    change T.C.map ((affineInclusion 𝒟).map f).op x ∈
      T.grading ((affineInclusion 𝒟).obj _) ((p, w) + 0)
    simpa only [add_zero] using T.map_mem_grading ((affineInclusion 𝒟).map f) hx
  isGradedCommutative X := by
    intro ⟨p, w⟩ ⟨q, v⟩ x y hx hy
    exact T.mul_comm_of_mem_grading (affineObject 𝒟 X) hx hy
  bijective_algebraMap_point := T.bijective_algebraMap_point
  eq_zero_of_mem_grading_point {p} {w} hp {x} hx := T.eq_zero_of_mem_grading_point hp hx
  bijective_pullback_affineLine X := T.bijective_map_prodAffineLineFst (affineObject 𝒟 X)
  gysin P := T.gysin (toPrincipal 𝒟 P)
  residue P := T.residue (toPrincipal 𝒟 P)
  isHomogeneousOfShift_gysin P := by
    intro ⟨p, w⟩ x hx
    exact T.gysin_mem_grading (toPrincipal 𝒟 P) hx
  isHomogeneousOfShift_residue P := by
    intro ⟨p, w⟩ x hx
    change T.residue (toPrincipal 𝒟 P) x ∈ T.grading (toPrincipal 𝒟 P).closed
      ((p, w) + (-1, -1))
    simpa only [sub_eq_add_neg, Prod.mk_add_mk] using T.residue_mem_grading (toPrincipal 𝒟 P) hx
  exact_gysin_map P := T.exact_gysin_map (toPrincipal 𝒟 P)
  exact_map_residue P := T.exact_map_residue (toPrincipal 𝒟 P)
  exact_residue_gysin P := T.exact_residue_gysin (toPrincipal 𝒟 P)
  gysin_map f x := T.gysin_map (toPrincipalHom f) x
  residue_map f x := T.residue_map (toPrincipalHom f) x
  residue_mul_map P {α} hα β := T.residue_mul_map (toPrincipal 𝒟 P) hα β

private def toPair (P : PrincipalSmoothDivisor (SmoothSchemeClass.smoothAffine k)) :
    Geometric.DivisorPair (Geometric.SmoothDomain.aff k) where
  ambient := P.ambient
  closed := P.closed
  compl := P.compl
  i := P.i
  j := P.j
  eqn := P.eqn
  isRegularSection_eqn := P.eqn_mem_nonZeroDivisors
  isClosedImmersion_i := P.isClosedImmersion_i
  ker_i := P.ker_i
  isOpenImmersion_j := P.isOpenImmersion_j
  opensRange_j := P.opensRange_j

private def toPairHom {P Q : PrincipalSmoothDivisor (SmoothSchemeClass.smoothAffine k)}
    (f : P.Hom Q) : toPair P ⟶ toPair Q where
  ambient := f.ambient
  closed := f.closed
  compl := f.compl
  i_comp := f.i_comp
  j_comp := f.j_comp
  associated_eqn := f.associated_eqn

private def fromGeometric
    (T : Geometric.OrdinaryTheory.{u, v, w, z} (Geometric.SmoothDomain.aff k) ℬ) :
    CohomologyTheory.{u, v, w, z} (SmoothSchemeClass.smoothAffine k) ℬ where
  bijective_algebraMap_gradeZero := T.bijective_algebraMap_gradeZero
  C := T.C
  algebra X := T.algebra X
  isScalarTower X := T.isScalarTower X
  grading := T.grading
  gradedAlgebra X := T.gradedAlgebra X
  algebraMap_mem_grading := T.algebraMap_mem_grading
  map_mem_grading {X} {Y} f {p} {w} {x} hx := by
    change T.C.map f.op x ∈ T.grading X (p, w)
    have hm := T.isHomogeneousOfShift_map f hx
    change T.C.map f.op x ∈ T.grading X ((p, w) + 0) at hm
    simpa only [add_zero] using hm
  mul_comm_of_mem_grading X {p} {w} {q} {v} {x} {y} hx hy := T.isGradedCommutative X hx hy
  bijective_algebraMap_point := T.bijective_algebraMap_point
  eq_zero_of_mem_grading_point := T.eq_zero_of_mem_grading_point
  bijective_map_prodAffineLineFst := T.bijective_pullback_affineLine
  gysin P := T.gysin (toPair P)
  residue P := T.residue (toPair P)
  gysin_mem_grading P {p} {w} {x} hx := T.isHomogeneousOfShift_gysin (toPair P) hx
  residue_mem_grading P {p} {w} {x} hx := by
    change T.residue (toPair P) x ∈ T.grading (toPair P).closed (p - 1, w - 1)
    simpa only [sub_eq_add_neg, Prod.mk_add_mk] using
      T.isHomogeneousOfShift_residue (toPair P) hx
  exact_gysin_map P := T.exact_gysin_map (toPair P)
  exact_map_residue P := T.exact_map_residue (toPair P)
  exact_residue_gysin P := T.exact_residue_gysin (toPair P)
  gysin_map f x := T.gysin_map (toPairHom f) x
  residue_map f x := T.residue_map (toPairHom f) x
  residue_mul_map P {α} hα β := T.residue_mul_map (toPair P) hα β

private theorem toPrincipal_standardPair :
    toPrincipal 𝒟 (Interface.standardPair (Geometric.SmoothDomain.aff k)) = standardDivisor 𝒟 := rfl

private theorem fundamentalClass_iff (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    (τ : T.C.obj (op 𝒟.multiplicativeGroup)) :
    T.IsFundamentalClass τ ↔ τ = (affineTheory T).tau :=
  Interface.mem_grading_and_residue_eq_one_iff (affineTheory T)

private theorem fundamentalClass_existsUnique (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ) :
    ∃! τ, T.IsFundamentalClass τ :=
  Interface.existsUnique_mem_grading_and_residue_eq_one (affineTheory T)

private theorem equation_iff {H : Set (MainTheorem.projectiveSpace k n).left}
    {ℓ : MvPolynomial (Fin (n + 1)) k} :
    MainTheorem.IsEquation H ℓ ↔ Interface.IsEquation H ℓ :=
  ⟨fun h ↦ ⟨h.isHomogeneous, h.ne_zero, h.zeroLocus_eq⟩,
    fun h ↦ ⟨h.isHomogeneous, h.ne_zero, h.zeroLocus_eq⟩⟩

private def hyperplaneEquiv : MainTheorem.Hyperplane k n ≃ Interface.Hyperplane k n :=
  Equiv.subtypeEquivRight fun H ↦ exists_congr fun ℓ ↦ equation_iff (H := H) (ℓ := ℓ)

@[simp] private theorem coe_hyperplaneEquiv (H : MainTheorem.Hyperplane k n) :
    (hyperplaneEquiv H).1 = H.1 := rfl

private def arrangement (𝒜 : MainTheorem.HyperplaneArrangement k n) :
    Interface.HyperplaneArrangement k n := 𝒜.map hyperplaneEquiv.toEmbedding

@[simp] private theorem mem_arrangement {𝒜 : MainTheorem.HyperplaneArrangement k n}
    {H : Interface.Hyperplane k n} : H ∈ arrangement 𝒜 ↔ hyperplaneEquiv.symm H ∈ 𝒜 := by
  simp [arrangement]

private def arrangementEquiv (𝒜 : MainTheorem.HyperplaneArrangement k n) : 𝒜 ≃ arrangement 𝒜 :=
  .ofBijective (fun H ↦ ⟨hyperplaneEquiv H, by simp [H.2]⟩)
    ⟨fun H K h ↦ Subtype.ext (hyperplaneEquiv.injective (congrArg Subtype.val h)),
      fun K ↦ by
        refine ⟨⟨hyperplaneEquiv.symm K, mem_arrangement.1 K.2⟩, ?_⟩
        apply Subtype.ext
        exact hyperplaneEquiv.apply_symm_apply (K : Interface.Hyperplane k n)⟩

@[simp] private theorem coe_arrangementEquiv {𝒜 : MainTheorem.HyperplaneArrangement k n} (H : 𝒜) :
    (arrangementEquiv 𝒜 H).1.1 = H.1.1 := rfl

private theorem union_arrangement (𝒜 : MainTheorem.HyperplaneArrangement k n) :
    (⋃ H ∈ arrangement 𝒜, (H : Set (Interface.projectiveSpace k n).left)) =
      ⋃ H ∈ 𝒜, (H : Set (MainTheorem.projectiveSpace k n).left) := by
  ext x
  constructor
  · intro hx
    obtain ⟨H, hH, hx⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨K, hK, rfl⟩ := Finset.mem_map.1 hH
    exact Set.mem_iUnion₂.2 ⟨K, hK, hx⟩
  · intro hx
    obtain ⟨H, hH, hx⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨hyperplaneEquiv H, Finset.mem_map.2 ⟨H, hH, rfl⟩, hx⟩

private theorem dependent_iff {𝒜 : MainTheorem.HyperplaneArrangement k n} (S : List 𝒜) :
    MainTheorem.IsDependent S ↔ Interface.IsDependent (S.map (arrangementEquiv 𝒜)) := by
  let e := arrangementEquiv 𝒜
  let ef : Fin (S.map e).length ≃ Fin S.length := finCongr (List.length_map (as := S) e)
  have hget (j : Fin (S.map e).length) : (S.map e).get j = e (S.get (ef j)) := by
    simp [ef, List.get_eq_getElem]
  constructor
  · rintro ⟨ℓ, hℓ, hdep⟩
    refine ⟨ℓ ∘ ef, ?_, ?_⟩
    · intro j
      change Interface.IsEquation (((S.map e).get j).1.1) (ℓ (ef j))
      rw [hget]
      exact equation_iff.1 (hℓ (ef j))
    · exact fun hli ↦ hdep ((linearIndependent_equiv ef).1 hli)
  · rintro ⟨ℓ, hℓ, hdep⟩
    refine ⟨ℓ ∘ ef.symm, ?_, ?_⟩
    · intro j
      apply equation_iff.2
      have ht := hℓ (ef.symm j)
      change Interface.IsEquation (((S.map e).get (ef.symm j)).1.1) (ℓ (ef.symm j)) at ht
      rw [hget, ef.apply_symm_apply] at ht
      exact ht
    · exact fun hli ↦ hdep ((linearIndependent_equiv ef.symm).1 hli)

private theorem complementOpens_eq (𝒜 : MainTheorem.HyperplaneArrangement k n) :
    MainTheorem.complementOpens 𝒜 = Interface.complementOpens (arrangement 𝒜) := by
  apply TopologicalSpace.Opens.ext
  exact congrArg (fun Z ↦ Zᶜ) (union_arrangement 𝒜).symm

private def complementReindexIso (𝒜 : MainTheorem.HyperplaneArrangement k n) :
    MainTheorem.complement 𝒜 ≅ Interface.complement (arrangement 𝒜) :=
  Over.isoMk ((MainTheorem.projectiveSpace k n).left.isoOfEq (complementOpens_eq 𝒜)) (by
    change (((MainTheorem.projectiveSpace k n).left.isoOfEq (complementOpens_eq 𝒜)).hom ≫
      (Interface.complementOpens (arrangement 𝒜)).ι) ≫ (MainTheorem.projectiveSpace k n).hom =
        (MainTheorem.complementOpens 𝒜).ι ≫ (MainTheorem.projectiveSpace k n).hom
    exact congrArg (fun f ↦ f ≫ (MainTheorem.projectiveSpace k n).hom)
      (Scheme.isoOfEq_hom_ι _ (complementOpens_eq 𝒜)))

private theorem isoOfEq_appTop_appLE {X : Scheme.{u}} {U V : X.Opens} (h : U = V)
    {W : X.Opens} (hu : ⊤ ≤ U.ι ⁻¹ᵁ W) (hv : ⊤ ≤ V.ι ⁻¹ᵁ W) (s : Γ(X, W)) :
    (X.isoOfEq h).hom.appTop (V.ι.appLE W ⊤ hv s) = U.ι.appLE W ⊤ hu s := by
  subst V
  simp

private theorem complementReindexIso_hom_appTop_ratio {𝒜 : MainTheorem.HyperplaneArrangement k n}
    {K : MainTheorem.Hyperplane k n} (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : ℓ.IsHomogeneous 1)
    (hℓ' : MainTheorem.IsEquation K ℓ') :
    (complementReindexIso 𝒜).hom.left.appTop
        (Interface.ratio (𝒜 := arrangement 𝒜) (K := hyperplaneEquiv K)
          (by simpa using hK) hℓ (equation_iff.1 hℓ')) =
      MainTheorem.ratio hK hℓ hℓ' := by
  exact isoOfEq_appTop_appLE (complementOpens_eq 𝒜) _ _ _

private theorem actual_complement_isAffine_smooth (𝒜 : MainTheorem.HyperplaneArrangement k n)
    (h𝒜 : 𝒜.Nonempty) : IsAffine (MainTheorem.complement 𝒜).left ∧
      Smooth (MainTheorem.complement 𝒜).hom := by
  have hne : (arrangement 𝒜).Nonempty := by
    obtain ⟨H, hH⟩ := h𝒜
    exact ⟨hyperplaneEquiv H, by simpa using hH⟩
  have h := Interface.complement_isAffine_smooth (arrangement 𝒜) hne
  have := h.1
  have := h.2
  refine ⟨.of_isIso (complementReindexIso 𝒜).hom.left, ?_⟩
  have hcomp : Smooth ((complementReindexIso 𝒜).hom.left ≫
      (Interface.complement (arrangement 𝒜)).hom) := inferInstance
  exact (Over.w (complementReindexIso 𝒜).hom) ▸ hcomp

private theorem actual_isUnit_ratio {𝒜 : MainTheorem.HyperplaneArrangement k n}
    {H K : MainTheorem.Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
    (hℓ : MainTheorem.IsEquation H ℓ) (hℓ' : MainTheorem.IsEquation K ℓ') :
    IsUnit (MainTheorem.ratio hK hℓ.isHomogeneous hℓ') := by
  let : Nonempty (arrangement 𝒜) := ⟨⟨hyperplaneEquiv H, by simpa using hH⟩⟩
  have hu := Interface.isUnit_ratio (arrangement 𝒜)
    (H := hyperplaneEquiv H) (K := hyperplaneEquiv K)
    (by simpa using hH) (by simpa using hK) (equation_iff.1 hℓ) (equation_iff.1 hℓ')
  have hm := hu.map ((complementReindexIso 𝒜).hom.left.appTop.hom)
  exact (complementReindexIso_hom_appTop_ratio hK hℓ.isHomogeneous hℓ') ▸ hm

private instance arrangement_nonempty (𝒜 : MainTheorem.HyperplaneArrangement k n) [Nonempty 𝒜] :
    Nonempty (arrangement 𝒜) := (arrangementEquiv 𝒜).symm.nonempty

private def actualComplementIso (𝒜 : MainTheorem.HyperplaneArrangement k n) :
    MainTheorem.complement 𝒜 ≅
      Geometric.projectiveComplement (Interface.toProjectiveArrangement (arrangement 𝒜)) :=
  complementReindexIso 𝒜 ≪≫ Interface.complementIso (arrangement 𝒜)

private theorem actualComplementIso_hom_appTop_projectiveRatio
    {𝒜 : MainTheorem.HyperplaneArrangement k n} [Nonempty 𝒜]
    {H K : MainTheorem.Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
    (hℓ : MainTheorem.IsEquation H ℓ) (hℓ' : MainTheorem.IsEquation K ℓ') :
    (actualComplementIso 𝒜).hom.left.appTop
        (Geometric.projectiveRatio
          (Interface.ker_toDual_mem_toProjectiveArrangement (𝒜 := arrangement 𝒜)
            (H := hyperplaneEquiv H) (by simpa using hH) (equation_iff.1 hℓ))
          (Interface.ker_toDual_mem_toProjectiveArrangement (𝒜 := arrangement 𝒜)
            (H := hyperplaneEquiv K) (by simpa using hK) (equation_iff.1 hℓ')) :
          Γ((Geometric.projectiveComplement
            (Interface.toProjectiveArrangement (arrangement 𝒜))).left, ⊤)) =
      MainTheorem.ratio hK hℓ.isHomogeneous hℓ' := by
  change ((complementReindexIso 𝒜).hom.left ≫
    (Interface.complementIso (arrangement 𝒜)).hom.left).appTop _ = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Interface.complementIso_hom_appTop_projectiveRatio (arrangement 𝒜)
      (H := hyperplaneEquiv H) (K := hyperplaneEquiv K) (by simpa using hH)
      (by simpa using hK) (equation_iff.1 hℓ) (equation_iff.1 hℓ')]
  exact complementReindexIso_hom_appTop_ratio hK hℓ.isHomogeneous hℓ'


private theorem affineComplement_property (𝒜 : HyperplaneArrangement k n)
    (h𝒜 : 𝒜.Nonempty) : (Geometric.SmoothDomain.aff k).property (complement 𝒜) :=
  actual_complement_isAffine_smooth 𝒜 h𝒜

private def affineComplement (𝒜 : HyperplaneArrangement k n) (h𝒜 : 𝒜.Nonempty) :
    (Geometric.SmoothDomain.aff k).Obj :=
  ⟨complement 𝒜, affineComplement_property 𝒜 h𝒜⟩

private def classComplement (𝒟 : SmoothSchemeClass k) (𝒜 : HyperplaneArrangement k n)
    (h𝒜 : 𝒜.Nonempty) : 𝒟.Obj := affineObject 𝒟 (affineComplement 𝒜 h𝒜)

private theorem hom_ratio_existsUnique (𝒟 : SmoothSchemeClass k)
    {𝒜 : HyperplaneArrangement k n} (h𝒜 : 𝒜.Nonempty)
    {H K : Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation H ℓ) (hℓ' : IsEquation K ℓ') :
    ∃! g : classComplement 𝒟 𝒜 h𝒜 ⟶ 𝒟.multiplicativeGroup,
      g.hom.left.appTop (gmCoordinate k) = ratio hK hℓ.isHomogeneous hℓ' := by
  obtain ⟨g, hg, hu⟩ := (Interface.existsUnique_hom_gm_iff (complement 𝒜)
    (ratio hK hℓ.isHomogeneous hℓ')).2 (actual_isUnit_ratio hH hK hℓ hℓ')
  refine ⟨ObjectProperty.homMk g, hg, fun g' hg' ↦ ?_⟩
  exact ObjectProperty.hom_ext _ (hu g'.hom hg')

private def geometricComplementIso (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜]
    (h𝒜 : 𝒜.Nonempty) :
    affineComplement 𝒜 h𝒜 ≅ (Geometric.SmoothDomain.aff k).projectiveComplement
      (Interface.toProjectiveArrangement (arrangement 𝒜)) :=
  ObjectProperty.isoMk _ (actualComplementIso 𝒜)

private theorem ratioClass_pull (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    {𝒜 : HyperplaneArrangement k n} [Nonempty 𝒜] (h𝒜 : 𝒜.Nonempty)
    {H K : Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation H ℓ) (hℓ' : IsEquation K ℓ')
    (τ : T.C.obj (op 𝒟.multiplicativeGroup)) (hτ : T.IsFundamentalClass τ)
    (g : classComplement 𝒟 𝒜 h𝒜 ⟶ 𝒟.multiplicativeGroup)
    (hg : g.hom.left.appTop (gmCoordinate k) = ratio hK hℓ.isHomogeneous hℓ') :
    (affineTheory T).pullIso (geometricComplementIso 𝒜 h𝒜)
      ((affineTheory T).logClass
        (Geometric.projectiveRatio
          (Interface.ker_toDual_mem_toProjectiveArrangement (𝒜 := arrangement 𝒜)
            (H := hyperplaneEquiv H) (by simpa using hH) (equation_iff.1 hℓ))
          (Interface.ker_toDual_mem_toProjectiveArrangement (𝒜 := arrangement 𝒜)
            (H := hyperplaneEquiv K) (by simpa using hK) (equation_iff.1 hℓ')))) =
      T.C.map g.op τ := by
  rw [Geometric.OrdinaryTheory.pullIso_apply, Geometric.OrdinaryTheory.pull_logClass]
  symm
  change (affineTheory T).pull
    (ObjectProperty.homMk g.hom : affineComplement 𝒜 h𝒜 ⟶ (Geometric.SmoothDomain.aff k).gm)
    τ = _
  rw [(fundamentalClass_iff T τ).1 hτ]
  apply Interface.pull_tau_eq_logClass
  exact hg.trans (actualComplementIso_hom_appTop_projectiveRatio hH hK hℓ hℓ').symm

namespace SourceAlgebra

variable (𝒜 : MainTheorem.HyperplaneArrangement k n)

private def coneIndexEquiv : 𝒜 ≃ (Interface.toProjectiveArrangement (arrangement 𝒜)).cone :=
  (arrangementEquiv 𝒜).trans (Interface.coneHyperplaneEquiv (arrangement 𝒜))

private theorem coneIndexEquiv_apply (H : 𝒜) :
    coneIndexEquiv 𝒜 H = (Interface.toProjectiveArrangement (arrangement 𝒜)).coneHyperplaneEquiv
      (Interface.projectiveHyperplaneEquiv (arrangement 𝒜) (arrangementEquiv 𝒜 H)) := rfl

private theorem dependence_iff (S : List 𝒜) :
    MainTheorem.IsDependent S ↔ Arrangement.IsDependent (S.map (coneIndexEquiv 𝒜)) := by
  have h := (dependent_iff S).trans
    (Interface.isDependent_iff_cone (S.map (arrangementEquiv 𝒜)))
  simpa only [List.map_map, coneIndexEquiv, Equiv.coe_trans] using h

variable (B) [Nonempty 𝒜]

private def projectiveSourceEquiv :
    MainTheorem.projectiveOrlikSolomonAlgebra B 𝒜 ≃ₐ[B]
      OSAlgebra.projectiveAlgebra B
        (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral :=
  Interface.projectiveAlgebraEquiv B 𝒜 (MainTheorem.IsDependent (𝒜 := 𝒜))
    (coneIndexEquiv 𝒜) (fun S _ ↦ dependence_iff 𝒜 S)
      (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral

private theorem projectiveSourceEquiv_generator (H K : 𝒜) :
    projectiveSourceEquiv (B := B) 𝒜 (MainTheorem.projectiveGenerator B 𝒜 H K) =
      OSAlgebra.projectiveDifference B
        (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral
        (coneIndexEquiv 𝒜 H) (coneIndexEquiv 𝒜 K) := by
  apply Subtype.ext
  exact Interface.coe_projectiveAlgebraEquiv_projectiveGenerator B 𝒜
    (MainTheorem.IsDependent (𝒜 := 𝒜)) (coneIndexEquiv 𝒜)
    (fun S _ ↦ dependence_iff 𝒜 S)
    (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral H K

variable (ℬ)

omit [GradedAlgebra ℬ] in
private theorem projectiveSourceEquiv_mem_grading_iff (i : ℤ × ℤ)
    (x : MainTheorem.projectiveOrlikSolomonAlgebra B 𝒜) :
    projectiveSourceEquiv (B := B) 𝒜 x ∈ OSAlgebra.projectiveBigrading B ℬ
      (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral i ↔
        x ∈ MainTheorem.projectiveOrlikSolomonGrading B 𝒜 ℬ i :=
  Interface.projectiveAlgebraEquiv_mem_projectiveBigrading_iff B 𝒜
    (MainTheorem.IsDependent (𝒜 := 𝒜)) ℬ (coneIndexEquiv 𝒜)
    (fun S _ ↦ dependence_iff 𝒜 S)
    (Interface.toProjectiveArrangement (arrangement 𝒜)).cone_isCentral i x

end SourceAlgebra

private def canonicalEquiv (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜] (h𝒜 : 𝒜.Nonempty) :
    projectiveOrlikSolomonAlgebra B 𝒜 ≃ₐ[B] T.C.obj (op (classComplement 𝒟 𝒜 h𝒜)) :=
  ((SourceAlgebra.projectiveSourceEquiv (B := B) 𝒜).trans
    ((affineTheory T).projectiveEquiv (Interface.toProjectiveArrangement (arrangement 𝒜)))).trans
      ((affineTheory T).pullIso (geometricComplementIso 𝒜 h𝒜))

private theorem canonicalEquiv_mem_grading_iff (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜] (h𝒜 : 𝒜.Nonempty)
    (i : ℤ × ℤ) (x : projectiveOrlikSolomonAlgebra B 𝒜) :
    canonicalEquiv T 𝒜 h𝒜 x ∈ T.grading (classComplement 𝒟 𝒜 h𝒜) i ↔
      x ∈ projectiveOrlikSolomonGrading B 𝒜 ℬ i := by
  change (affineTheory T).pullIso (geometricComplementIso 𝒜 h𝒜)
    ((affineTheory T).projectiveEquiv _ (SourceAlgebra.projectiveSourceEquiv (B := B) 𝒜 x)) ∈
      (affineTheory T).grading (affineComplement 𝒜 h𝒜) i ↔ _
  rw [Geometric.OrdinaryTheory.pullIso_mem_grading_iff,
    Geometric.OrdinaryTheory.projectiveEquiv_mem_grading_iff]
  exact SourceAlgebra.projectiveSourceEquiv_mem_grading_iff (B := B) (ℬ := ℬ) 𝒜 i x

private theorem canonicalEquiv_image_grading (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜] (h𝒜 : 𝒜.Nonempty) (i : ℤ × ℤ) :
    canonicalEquiv T 𝒜 h𝒜 '' (projectiveOrlikSolomonGrading B 𝒜 ℬ i : Set _) =
      T.grading (classComplement 𝒟 𝒜 h𝒜) i := by
  ext y
  obtain ⟨x, rfl⟩ := (canonicalEquiv T 𝒜 h𝒜).surjective y
  rw [(canonicalEquiv T 𝒜 h𝒜).injective.mem_set_image]
  exact (canonicalEquiv_mem_grading_iff T 𝒜 h𝒜 i x).symm

private theorem canonicalEquiv_generator (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ)
    (𝒜 : HyperplaneArrangement k n) [Nonempty 𝒜] (h𝒜 : 𝒜.Nonempty) (H K : 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
    (hℓ : IsEquation (H : Hyperplane k n) ℓ) (hℓ' : IsEquation (K : Hyperplane k n) ℓ')
    (τ : T.C.obj (op 𝒟.multiplicativeGroup)) (hτ : T.IsFundamentalClass τ)
    (g : classComplement 𝒟 𝒜 h𝒜 ⟶ 𝒟.multiplicativeGroup)
    (hg : g.hom.left.appTop (gmCoordinate k) = ratio K.2 hℓ.isHomogeneous hℓ') :
    canonicalEquiv T 𝒜 h𝒜 (projectiveGenerator B 𝒜 H K) = T.C.map g.op τ := by
  change (affineTheory T).pullIso _ ((affineTheory T).projectiveEquiv _
    (SourceAlgebra.projectiveSourceEquiv (B := B) 𝒜 (projectiveGenerator B 𝒜 H K))) = _
  rw [SourceAlgebra.projectiveSourceEquiv_generator]
  have hker := Interface.hyperplaneSubmodule_eq_ker (H := hyperplaneEquiv (H : Hyperplane k n))
    (equation_iff.1 hℓ)
  have hker' := Interface.hyperplaneSubmodule_eq_ker (H := hyperplaneEquiv (K : Hyperplane k n))
    (equation_iff.1 hℓ')
  rw [SourceAlgebra.coneIndexEquiv_apply, SourceAlgebra.coneIndexEquiv_apply]
  rw [Geometric.OrdinaryTheory.projectiveEquiv_difference_of_ker_eq _ _ _ _
    (ℓ := Interface.toDual ℓ) (ℓ' := Interface.toDual ℓ') hker.symm hker'.symm]
  exact ratioClass_pull T h𝒜 H.2 K.2 hℓ hℓ' τ hτ g hg

end Proof

/- END PROOF REGION — resume reading the public statement here.
The skipped region is excluded from the statement by `lake exe audit --interface`.
-/

/-! ## Part II: statements -/

/-- The complement of a nonempty arrangement is affine and smooth over `k`. -/
theorem complement_isAffine_smooth (h𝒜 : 𝒜.Nonempty) :
    IsAffine (complement 𝒜).left ∧ Smooth (complement 𝒜).hom :=
  Proof.actual_complement_isAffine_smooth 𝒜 h𝒜

/-- The complement of a nonempty arrangement, as a member of `𝒟`. It is one by
`complement_isAffine_smooth`, since every class contains the smooth affine schemes. This definition
is in Part II because it uses that theorem. -/
def complementObj (𝒟 : SmoothSchemeClass k) {𝒜 : HyperplaneArrangement k n}
    (h𝒜 : 𝒜.Nonempty) : 𝒟.Obj :=
  ⟨complement 𝒜, 𝒟.of_isAffine _ (complement_isAffine_smooth 𝒜 h𝒜).1
    (complement_isAffine_smooth 𝒜 h𝒜).2⟩

variable {𝒟 : SmoothSchemeClass k} {ℬ} [GradedAlgebra ℬ]

/-- Every cohomology theory, on any class `𝒟`, has exactly one fundamental class. -/
theorem existsUnique_fundamentalClass (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ) :
    ∃! τ, T.IsFundamentalClass τ :=
  Proof.fundamentalClass_existsUnique T

/-- For equations `ℓ` and `ℓ'` of hyperplanes of `𝒜`, there is exactly one morphism of `k`-schemes
`g : U → 𝔾ₘ` that pulls the coordinate back to `ℓ / ℓ'`. In particular `ℓ / ℓ'` is a unit. The
class `𝒟` plays no role: its morphisms are all morphisms of `k`-schemes. -/
theorem existsUnique_hom_ratio (𝒟 : SmoothSchemeClass k) {𝒜 : HyperplaneArrangement k n}
    (h𝒜 : 𝒜.Nonempty) {H K : Hyperplane k n} (hH : H ∈ 𝒜) (hK : K ∈ 𝒜)
    {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k} (hℓ : IsEquation H ℓ) (hℓ' : IsEquation K ℓ') :
    ∃! g : complementObj 𝒟 h𝒜 ⟶ 𝒟.multiplicativeGroup,
      g.hom.left.appTop (gmCoordinate k) = ratio hK hℓ.isHomogeneous hℓ' :=
  Proof.hom_ratio_existsUnique 𝒟 h𝒜 hH hK hℓ hℓ'

/-- **The Orlik–Solomon theorem.** Let `T` be a cohomology theory on a class `𝒟` of smooth
`k`-schemes, and let `𝒜` be a nonempty arrangement of hyperplanes in `ℙⁿ_k`, with complement `U`.
The standard case is `𝒟 = SmoothSchemeClass.allSmooth k`, a theory on all smooth `k`-schemes, but
any class is allowed, such as `SmoothSchemeClass.smoothAffine k`, which makes the theorem apply to
theories defined only on smooth affine schemes.

There is an isomorphism of `B`-algebras `Φ` from the projective Orlik–Solomon algebra of `𝒜` to
`T(U)` such that

1. `Φ (e_H - e_K) = g^* τ` for all hyperplanes `H` and `K` of `𝒜`, all equations `ℓ` of `H` and
   `ℓ'` of `K`, the fundamental class `τ`, and the map `g : U → 𝔾ₘ` given by `ℓ / ℓ'`. That is,
   `e_H - e_K` goes to the logarithmic class `[ℓ / ℓ']`. Since the `e_H - e_K` generate, this
   determines `Φ`;
2. `Φ` maps the piece of bidegree `(p, w)` of the projective Orlik–Solomon algebra onto
   `H^{p, w}(U)`, for all `p` and `w`. -/
theorem orlikSolomon (T : CohomologyTheory.{u, v, w, z} 𝒟 ℬ) (𝒜 : HyperplaneArrangement k n)
    (h𝒜 : 𝒜.Nonempty) :
    ∃ Φ : projectiveOrlikSolomonAlgebra B 𝒜 ≃ₐ[B] T.C.obj (op (complementObj 𝒟 h𝒜)),
      (∀ (H K : 𝒜) {ℓ ℓ' : MvPolynomial (Fin (n + 1)) k}
        (hℓ : IsEquation (H : Hyperplane k n) ℓ) (hℓ' : IsEquation (K : Hyperplane k n) ℓ')
        (τ : T.C.obj (op 𝒟.multiplicativeGroup)), T.IsFundamentalClass τ →
        ∀ g : complementObj 𝒟 h𝒜 ⟶ 𝒟.multiplicativeGroup,
          g.hom.left.appTop (gmCoordinate k) = ratio K.2 hℓ.isHomogeneous hℓ' →
          Φ (projectiveGenerator B 𝒜 H K) = T.C.map g.op τ) ∧
      ∀ p w : ℤ, Φ '' (projectiveOrlikSolomonGrading B 𝒜 ℬ (p, w) : Set _) =
        T.grading (complementObj 𝒟 h𝒜) (p, w) := by
  let : Nonempty 𝒜 := 𝒜.nonempty_coe_sort.mpr h𝒜
  exact ⟨Proof.canonicalEquiv T 𝒜 h𝒜, Proof.canonicalEquiv_generator T 𝒜 h𝒜,
    fun p w ↦ Proof.canonicalEquiv_image_grading T 𝒜 h𝒜 (p, w)⟩

/-- **The axioms are consistent.** For a field `k` of characteristic zero, algebraic de Rham
cohomology with coefficients `B = k[T, T⁻¹]`, graded by `ℬ w = k T^w`, is a cohomology theory on
smooth affine `k`-schemes. Since `B ≠ 0` and the axioms identify `B` with the cohomology of the
point, it is not the zero theory, so the main theorem is not vacuous.

It is stated for `smoothAffine k`, because the library constructs de Rham cohomology only for affine
schemes. A nonzero theory on `allSmooth k` would need de Rham cohomology of schemes that are not
affine, through hypercohomology, which is not formalized. -/
theorem nonempty_cohomologyTheory (k : Type u) [Field k] [CharZero k] :
    Nonempty (CohomologyTheory.{u, u, u, u} (SmoothSchemeClass.smoothAffine k)
      (AddMonoidAlgebra.grade k : ℤ → Submodule k k[T;T⁻¹])) :=
  ⟨Proof.fromGeometric (Geometric.DeRham.ordinaryTheory k)⟩

/-! ## Axiom reports -/

#print axioms complement_isAffine_smooth
#print axioms existsUnique_fundamentalClass
#print axioms existsUnique_hom_ratio
#print axioms orlikSolomon
#print axioms nonempty_cohomologyTheory

end OrlikSolomon.MainTheorem
