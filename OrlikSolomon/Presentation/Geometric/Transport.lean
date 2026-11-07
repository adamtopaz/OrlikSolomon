/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Geometric.Logarithms

/-!
# The transport of the affine development

This file gives the Lean form of `thm:geo-transport-all` of the geometric refactor blueprint: the
comparison through which every statement of the algebraic development about a named smooth object
is restated for the corresponding scheme.

Let `T` be a geometric ordinary theory on an admissible domain `D`, and let `e : X ≅ Spec A` be the
comparison of an object `X` of `D` with the spectrum of a smooth algebra `A`, such as the comparison
`s_𝒜` of an arrangement complement with the spectrum of its coordinate ring. The old theory
`T.toAlgebraic` has the value `C(Spec A)` at `A`, and `transportAffineDevelopment T e` identifies it
with `C(X)` by pullback along `e`. The blueprint's induction on expressions is the list of laws of
this comparison: it is an equivalence of `B`-algebras, so it preserves constants, sums, products and
scalars; it preserves and reflects every bidegree; it sends the old logarithmic class of a unit `u`
of `A` to the logarithmic class of the corresponding global unit of `X`; and it commutes with
pullback along every morphism whose square with the comparisons commutes. The residue and Gysin
maps of a pair isomorphic to the spectrum of an old pair are compared by pair naturality,
`OrdinaryTheory.residue_pull` and `OrdinaryTheory.gysin_pull`, as `Presentation/Geometric/Affine`
does for the deletion pair.

A single Lean statement cannot quantify over all statements of the old development. So the rule
`𝖦` is realized by this comparison and its laws, together with their application to the public
theorems: `Presentation/Geometric/Affine`, `Presentation/Geometric/Ordinary` and
`Presentation/Geometric/Projective` restate every public result of `thm:affine`, `cor:ordinary`,
`thm:betti`, `lem:comparison-residue`, `thm:projective` and `cor:projective-betti` by composing the
old theorem for `T.toAlgebraic` with this comparison.

## Main definitions

* `transportAffineDevelopment T e : T.toAlgebraic.C.obj A ≃ₐ[B] T.obj X`, for `e : X ≅ Spec A`.

## Main results

* `transportAffineDevelopment_mem_grading_iff`: bidegrees are preserved and reflected.
* `transportAffineDevelopment_logClass`, `transportAffineDevelopment_logClass_eq`: old logarithmic
  classes go to geometric ones.
* `transportAffineDevelopment_map`: naturality for compatible morphisms.
* `bijOn_transportAffineDevelopment`: each graded piece of `C(Spec A)` corresponds to that of
  `C(X)`, and `transportAffineDevelopmentComponentEquiv` is the resulting `R`-linear equivalence.

## Blueprint

`thm:geo-transport-all`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w z

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ) {X Y : D.Obj} {A A' : SmoothAlg.{u} k}

/-- **The transport rule.** For a comparison `e : X ≅ Spec A` of an object of the domain with the
spectrum of a smooth algebra, the value `C(Spec A)` of the old theory `T.toAlgebraic` at `A` is
`C(X)`, by pullback along `e`. Composing an old conclusion about `T.toAlgebraic` at `A` with this
equivalence gives its geometric restatement at `X`: the laws below say that the comparison
commutes with every operation of the old statements, namely the algebra operations, bidegrees,
logarithmic classes and compatible pullbacks.

Blueprint: `thm:geo-transport-all`. -/
def transportAffineDevelopment (e : X ≅ D.spec A) : T.toAlgebraic.C.obj A ≃ₐ[B] T.obj X :=
  T.pullIso e

@[simp]
lemma transportAffineDevelopment_apply (e : X ≅ D.spec A) (x : T.toAlgebraic.C.obj A) :
    transportAffineDevelopment T e x = T.pull e.hom x :=
  rfl

@[simp]
lemma transportAffineDevelopment_symm_apply (e : X ≅ D.spec A) (y : T.obj X) :
    (transportAffineDevelopment T e).symm y = T.pull e.inv y :=
  rfl

/-- The transport preserves and reflects every bidegree.

Blueprint: `thm:geo-transport-all`. -/
lemma transportAffineDevelopment_mem_grading_iff (e : X ≅ D.spec A) {i : ℤ × ℤ}
    {x : T.toAlgebraic.C.obj A} :
    transportAffineDevelopment T e x ∈ T.grading X i ↔ x ∈ T.toAlgebraic.grading A i :=
  T.pullIso_mem_grading_iff e

/-- The inverse transport preserves and reflects every bidegree. -/
lemma transportAffineDevelopment_symm_mem_grading_iff (e : X ≅ D.spec A) {i : ℤ × ℤ}
    {y : T.obj X} :
    (transportAffineDevelopment T e).symm y ∈ T.toAlgebraic.grading A i ↔ y ∈ T.grading X i := by
  rw [← transportAffineDevelopment_mem_grading_iff, AlgEquiv.apply_symm_apply]

/-- The transport preserves the bigrading. -/
lemma isHomogeneousOfShift_transportAffineDevelopment (e : X ≅ D.spec A) :
    IsHomogeneousOfShift (T.toAlgebraic.grading A) (T.grading X) 0
      (transportAffineDevelopment T e) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hx ↦
    (transportAffineDevelopment_mem_grading_iff T e).2 hx

/-- The transport restricts to a bijection between the pieces of bidegree `i`. -/
lemma bijOn_transportAffineDevelopment (e : X ≅ D.spec A) (i : ℤ × ℤ) :
    Set.BijOn (transportAffineDevelopment T e) (T.toAlgebraic.grading A i) (T.grading X i) :=
  ⟨fun _ hx ↦ (transportAffineDevelopment_mem_grading_iff T e).2 hx,
    (transportAffineDevelopment T e).injective.injOn,
    fun y hy ↦ ⟨_, (transportAffineDevelopment_symm_mem_grading_iff T e).2 hy,
      AlgEquiv.apply_symm_apply _ y⟩⟩

/-- The transport on the pieces of bidegree `i`, as an `R`-linear equivalence. Its source is
written `T.grading (D.spec A) i`, the `simp` normal form of `T.toAlgebraic.grading A i`. -/
def transportAffineDevelopmentComponentEquiv (e : X ≅ D.spec A) (i : ℤ × ℤ) :
    T.grading (D.spec A) i ≃ₗ[R] T.grading X i :=
  (isHomogeneousOfShift_transportAffineDevelopment T e).componentEquiv
    (e := (transportAffineDevelopment T e).toLinearEquiv) (add_zero i)

@[simp]
lemma coe_transportAffineDevelopmentComponentEquiv_apply (e : X ≅ D.spec A) (i : ℤ × ℤ)
    (x : T.grading (D.spec A) i) :
    (transportAffineDevelopmentComponentEquiv T e i x : T.obj X) = T.pull e.hom x :=
  rfl

@[simp]
lemma coe_transportAffineDevelopmentComponentEquiv_symm_apply (e : X ≅ D.spec A) (i : ℤ × ℤ)
    (y : T.grading X i) :
    ((transportAffineDevelopmentComponentEquiv T e i).symm y : T.obj (D.spec A)) =
      T.pull e.inv y :=
  rfl

/-- The transport sends the old logarithmic class of a unit `u` of `A` to the logarithmic class
of the global unit `v` of `X` that corresponds to `u` under `e`, given by an equation of global
sections. `transportAffineDevelopment_logClass_eq` is the form with the unit itself.

Blueprint: `thm:geo-transport-all`. -/
lemma transportAffineDevelopment_logClass (e : X ≅ D.spec A) (u : Aˣ) {v : Γ(X.obj.left, ⊤)ˣ}
    (hv : (v : Γ(X.obj.left, ⊤)) = e.hom.hom.left.appTop ((Scheme.ΓSpecIso (.of A)).inv u)) :
    transportAffineDevelopment T e (T.toAlgebraic.logClass u) = T.logClass v :=
  T.pull_toAlgebraic_logClass e.hom u hv

/-- The transport sends the old logarithmic class of a unit `u` of `A` to the logarithmic class of
the pullback along `e` of the global unit `specUnit u` of `Spec A`.

Blueprint: `thm:geo-transport-all`. -/
lemma transportAffineDevelopment_logClass_eq (e : X ≅ D.spec A) (u : Aˣ) :
    transportAffineDevelopment T e (T.toAlgebraic.logClass u) =
      T.logClass (Units.map e.hom.hom.left.appTop.hom (specUnit (A := A.obj) u)) :=
  T.pull_toAlgebraic_logClass_eq e.hom u

/-- The transport commutes with pullback: if a morphism `g : X ⟶ Y` corresponds under the
comparisons to the algebra map `φ : A' ⟶ A`, then pulling back along `g` is the old map induced by
`φ`.

Blueprint: `thm:geo-transport-all`. -/
lemma transportAffineDevelopment_map (e : X ≅ D.spec A) (e' : Y ≅ D.spec A') (g : X ⟶ Y)
    (φ : A' ⟶ A) (h : g ≫ e'.hom = e.hom ≫ (D.specFunctor.map φ).unop)
    (x : T.toAlgebraic.C.obj A') :
    transportAffineDevelopment T e (T.toAlgebraic.C.map φ x) =
      T.pull g (transportAffineDevelopment T e' x) := by
  rw [transportAffineDevelopment_apply, transportAffineDevelopment_apply,
    OrdinaryTheory.toAlgebraic_map, ← OrdinaryTheory.pull_comp, ← OrdinaryTheory.pull_comp, h]

end OrlikSolomon.Geometric
